module

public import ShrincsSecurity.Slhdsa.PostPrf
public import ShrincsSecurity.Shrincs.PrfBound
public import ShrincsSecurity.Shrincs.Claim411
public import ShrincsSecurity.Shrincs.Claim412

/-!
# Theorem 4.3: Standalone EU-CMA security of SLH-DSA (`[HK22]`)

`SHRINCS-Security-Analysis.pdf`, **Theorem 4.3** (Section 4.6, quoted from `[HK22]`, restated under
the collection accounting of Section 4.3): for any `q_s`-query EU-CMA adversary `A` (Definition 4.14)
against pure-mode hedged SLH-DSA at validated parameters `vp.sl`,

```
Succ^{EU-CMA}_{SLH-DSA, q_s}(A)
  ≤ Adv^{prf}_{PRF, q₁}(B_sl_prfAdv A)
  + Adv^{prf}_{PRF_msg^sl, q_s}(B_sl_prfmsgAdv A)
  + Succ^{ITSR}_{H_msg^sl, q_s}(B_itsr)
  + ∑_{γ < w - 2} Adv^{SM-UD}_{F ∈ Th_λ, q₂}(B_ud γ)
  + Adv^{SM-PRE}_{F ∈ Th_λ, q₂}(B_pre)
  + Adv^{SM-TCR}_{F ∈ Th_λ, q₃}(B_tcrF_wots)
  + Adv^{SM-TCR}_{H ∈ Th_λ, q₄}(B_tcrH_xmss)
  + Adv^{SM-TCR}_{Th_k ∈ Th_λ, q₅}(B_tcrThK)
  + Adv^{SM-TCR}_{Th_lsl ∈ Th_λ, q₆}(B_tcrThLsl)
  + Adv^{SM-TCR}_{H ∈ Th_λ, q₇}(B_tcrH_fors)
  + 3 · Adv^{SM-TCR}_{F ∈ Th_λ, q₈}(B_tcrF_fors)
  + Adv^{SM-DSPR}_{F ∈ Th_λ, q₈}(B_dsprF_fors),
```

where `q₁ = slSecretCount vp.sl = wotsInstanceCount · len + 2^h · k · 2^a` is the exact number of
secret-key elements of the hypertree, `q₂ = wotsInstanceCount · len`, `q₃ = q₂ · (w - 1)`,
`q₄ = xmssTreeCount · (2^{h'} - 1)` (with `q₅ = 2^h`, `q₆ = wotsInstanceCount`,
`q₇ = 2^h · k · (2^a - 1)`, `q₈ = 2^h · k · 2^a`, exact VCVio reachable-target counts of
`PostPrf.lean`), and the bound holds in the standard model for `Th_λ` and `H_msg^sl` (`ITSR`) under
`hinj : Function.Injective pr.yToBytes` and `henc : enc.Injective`.

**Note on the 10 post-PRF summands vs. the paper's restatement of `[HK22]`:** The paper's Theorem 4.3
lists `5 · SM-TCR(F) + 1 · SM-TCR(H)` (including an extra FORS-leaf `SM-TCR(F)` hop from `[HK22]`
and a single combined XMSS+FORS `SM-TCR(H)` term), whereas `postPrf_bound` proves the cleaner
`4 · SM-TCR(F) + 2 · SM-TCR(H)` form (`B_tcrF_wots` + `3 · B_tcrF_fors`, omitting the redundant
FORS-leaf `F` hop, and keeping XMSS `H` and FORS `H` as separate `SM-TCR(H)` terms `B_tcrH_xmss`
and `B_tcrH_fors`; see `DEVIATIONS.md` §4.6).

## Proof architecture

1. **Scheme instantiation (`slhdsaScheme`)**: instantiates VCVio's `SignatureAlg ProbComp`
   (Definition 4.13/4.14, `Notions.EUCMAAdversary`, `Notions.euCmaSucc`) with pure-mode hedged
   FIPS 205 SLH-DSA (`Scheme.Stateless`, `SLHDSA.External.encodePureMessage`).
2. **Secret-ledger congruence (`slRootDet_prf`, `slSignDet_prf`)**: using VCVio's ledger theorems
   (`keygenInternalWithSecretM_pred_of_ledger`, `signInternalWithSecretRandomizerM_pred_of_ledger`)
   and `Shrincs.mem_slSecretList`, proves that the real PRF outputs restricted to `SlSecAdrs vp`
   compute the exact `Stateless.root` and `SLHDSA.GeneralScheme.signInternal`.
3. **Hop 1 (`PRF`, budget `q₁ = slSecretCount vp.sl`)**: `B_sl_prfAdv` queries `PRF` once at every
   `(pk, a)` for `a : SlSecAdrs vp` via `tableM` (at most `slSecretCount vp.sl` pairwise distinct
   queries, zero queries after setup). Its real world equals `slGame0` (`euCmaSucc`), and its ideal
   world samples `u ← $ᵗ (SlSecAdrs vp → pr.Y)` directly (`slGame1`).
4. **Hop 2 (`PRF_msg^sl`, budget `q_s`)**: `B_sl_prfmsgAdv` samples `u ← $ᵗ (SlSecAdrs vp → pr.Y)`
   itself and forwards each signing query's `(optRand, M')` to its `PRF_msg^sl` oracle (`≤ q_s`
   queries). Its real world is distributed as `slGame1`, and its ideal world is `slGame2` (lazy
   uniform randomizer cache `SlRndCache pr`).
5. **Post-PRF bridge (`slGame2 → postPrfExp`)**: couples `slGame2` in lockstep with
   `Slhdsa.postPrfExp pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)` (using `pureMsg_injective`
   for freshness and `SLHDSA.External.encodePureMessage_eq_ok` for verification), and applies
   `Slhdsa.postPrf_bound` to obtain all 10 remaining terms.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Slhdsa

open Scheme Shrincs SLHDSA.Security
open SLHDSA (Adrs Byte)

/-! ## 1. Pure-mode message encoding & standalone SLH-DSA `SignatureAlg` -/

section SchemeDef

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)

/-- FIPS 205 pure-mode encoded message `M' = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ body` (Algorithm 22). -/
def pureMsg (m : Msg) : List Byte :=
  [0, UInt8.ofNat (enc.ctx m).length] ++ enc.ctx m ++ enc.body m

/-- Under `enc.Injective`, the FIPS 205 pure-mode encoding `pureMsg` is injective on `Msg`. -/
theorem pureMsg_injective (henc : enc.Injective) : Function.Injective (pureMsg Msg enc) := by
  intro m₁ m₂ h
  unfold pureMsg at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
  obtain ⟨hlen, hrest⟩ := h
  have hctx1 := enc.ctx_le m₁
  have hctx2 := enc.ctx_le m₂
  have hlen' : (enc.ctx m₁).length = (enc.ctx m₂).length := by
    have hnat := congrArg UInt8.toNat hlen
    simp only [UInt8.toNat_ofNat'] at hnat
    omega
  obtain ⟨hctx, hbody⟩ := List.append_inj hrest hlen'
  exact henc (Prod.ext hctx hbody)

/-- `Stateless.verify` on `(enc.body m, enc.ctx m)` is literally `verifyInternal` on `pureMsg m`. -/
theorem statelessVerify_eq_verifyInternal [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (m : Msg) (σ : Stateless.Sig pr) :
    Stateless.verify pr (enc.body m) (enc.ctx m) σ pk pkSl =
      SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA (pureMsg Msg enc m) σ ⟨pk, pkSl⟩ := by
  unfold Stateless.verify SLHDSA.External.verifyPure Stateless.publicKey pureMsg
  rw [SLHDSA.External.encodePureMessage_eq_ok _ _ (enc.ctx_le m)]

/-- `Stateless.sign` on `(enc.body m, enc.ctx m)` returns `some (signInternal (pureMsg m) ...)`. -/
theorem statelessSign_eq_signInternal (sk : SLHDSA.SecretKeyCore pr.toSLHDSA.core)
    (m : Msg) (optRand : pr.Y) :
    Stateless.sign pr (enc.body m) (enc.ctx m) sk.skSeed sk.skPrf sk.pkSeed sk.pkRoot optRand =
      some (SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA (pureMsg Msg enc m) sk optRand) := by
  unfold Stateless.sign SLHDSA.External.signPureWithRandomizer Stateless.secretKey pureMsg
  rw [SLHDSA.External.encodePureMessage_eq_ok _ _ (enc.ctx_le m)]
  rfl

/-- **Standalone SLH-DSA** (FIPS 205 pure-mode hedged) as a VCVio `SignatureAlg ProbComp`
(Definition 4.13/4.14). -/
def slhdsaScheme [DecidableEq pr.Y] [SampleableType pr.Y]
    [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] :
    SignatureAlg ProbComp Msg (pr.PkSeed × pr.Y) (SLHDSA.SecretKeyCore pr.toSLHDSA.core)
      (Stateless.Sig pr) where
  keygen := do
    let skSeed ← $ᵗ pr.SkSeed
    let skPrf ← $ᵗ pr.SkPrf
    let pkSeed ← $ᵗ pr.PkSeed
    let pkSl := Stateless.root pr skSeed pkSeed
    return ((pkSeed, pkSl), Stateless.secretKey pr skSeed skPrf pkSeed pkSl)
  sign _ sk m := do
    let optRand ← $ᵗ pr.Y
    return SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA (pureMsg Msg enc m) sk optRand
  verify pk m σ :=
    pure (Stateless.verify pr (enc.body m) (enc.ctx m) σ pk.1 pk.2)

/-- Standalone SLH-DSA is perfectly complete. -/
theorem slhdsaScheme_perfectlyComplete [DecidableEq pr.Y] [SampleableType pr.Y]
    [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] :
    (slhdsaScheme pr Msg enc).PerfectlyComplete ProbCompRuntime.probComp := by
  intro m
  change 𝒟[do
    let (pk, sk) ← (slhdsaScheme pr Msg enc).keygen
    let sig ← (slhdsaScheme pr Msg enc).sign pk sk m
    (slhdsaScheme pr Msg enc).verify pk m sig] {true} = 1
  simp only [slhdsaScheme, bind_assoc, pure_bind]
  have hok : ∀ (skSeed : pr.SkSeed) (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) (optRand : pr.Y),
      Stateless.verify pr (enc.body m) (enc.ctx m)
        (SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA (pureMsg Msg enc m)
          (Stateless.secretKey pr skSeed skPrf pkSeed (Stateless.root pr skSeed pkSeed)) optRand)
        pkSeed (Stateless.root pr skSeed pkSeed) = true := by
    intro skSeed skPrf pkSeed optRand
    exact Stateless.verify_sign pr (enc.ctx_le m)
      (statelessSign_eq_signInternal pr Msg enc
        (Stateless.secretKey pr skSeed skPrf pkSeed (Stateless.root pr skSeed pkSeed)) m optRand)
  have hcomp :
      (do
        let skSeed ← $ᵗ pr.SkSeed
        let skPrf ← $ᵗ pr.SkPrf
        let pkSeed ← $ᵗ pr.PkSeed
        let optRand ← $ᵗ pr.Y
        pure (Stateless.verify pr (enc.body m) (enc.ctx m)
          (SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA (pureMsg Msg enc m)
            (Stateless.secretKey pr skSeed skPrf pkSeed (Stateless.root pr skSeed pkSeed)) optRand)
          pkSeed (Stateless.root pr skSeed pkSeed))) =ᵈ (pure true : ProbComp Bool) := by
    simp_rw [hok]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
        EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_const _ _)
          (EvalDistEq.bind_const _ _)) (EvalDistEq.bind_const _ _)) (EvalDistEq.bind_const _ _)
  rw [hcomp.evalDist_eq]
  simp

end SchemeDef

/-! ## 2. Secret-ledger congruence for pure PRF vs `SlSecAdrs` table -/

section LedgerCongr

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

private theorem simulateQ_id_congr_of_aqs {D R α : Type} {P : D → Prop}
    (s₁ s₂ : D → R) (hagree : ∀ a, P a → s₁ a = s₂ a) :
    ∀ (oa : OracleComp (D →ₒ R) α), oa.AllQueriesSatisfy P →
      simulateQ (fun a => (pure (s₁ a) : Id R) : QueryImpl (D →ₒ R) Id) oa =
        simulateQ (fun a => (pure (s₂ a) : Id R) : QueryImpl (D →ₒ R) Id) oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; rfl
  | query_bind t k ih =>
    intro h
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query]
    change simulateQ (fun a => (pure (s₁ a) : Id R) : QueryImpl (D →ₒ R) Id) (k (s₁ t)) =
      simulateQ (fun a => (pure (s₂ a) : Id R) : QueryImpl (D →ₒ R) Id) (k (s₂ t))
    rw [hagree t h.1]
    exact ih (s₂ t) (h.2 (s₂ t))

/-- Real `Stateless.root` equals `slRootDet` on the `SlSecAdrs` restriction of `pr.PRF pk skSeed`. -/
theorem slRootDet_prf (skSeed : pr.SkSeed) (pk : pr.PkSeed) :
    slRootDet pr pk (fun a => pr.PRF pk skSeed a.1) = Stateless.root pr skSeed pk := by
  let prog : OracleComp (Adrs →ₒ pr.Y) pr.Y :=
    let _ := pubQ pr (OracleComp (Adrs →ₒ pr.Y))
    SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
      (fun a => (Adrs →ₒ pr.Y).query a) pk
  have haqs : prog.AllQueriesSatisfy (fun a => a ∈ slSecretList vp.sl) := by
    let _ := pubQ pr (OracleComp (Adrs →ₒ pr.Y))
    exact @keygenInternalWithSecretM_pred_of_ledger _ _ _
      (fun {_} (oa : OracleComp (Adrs →ₒ pr.Y) _) =>
        oa.AllQueriesSatisfy (fun a => a ∈ slSecretList vp.sl))
      (fun x => allQueriesSatisfy_pure x _)
      (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
      vp.sl pr.toSLHDSA.core (fun a => (Adrs →ₒ pr.Y).query a)
      (fun a b hb hab => by
        rw [allQueriesSatisfy_query_iff]
        exact mem_slSecretList hb hab)
      (pubQ pr (OracleComp (Adrs →ₒ pr.Y))) pk
      (fun _ _ _ => allQueriesSatisfy_pure _ _)
  let s₁ : Adrs → pr.Y := slSecOf pr (fun a => pr.PRF pk skSeed a.1)
  let s₂ : Adrs → pr.Y := fun a => pr.PRF pk skSeed a
  have hagree : ∀ a ∈ slSecretList vp.sl, s₁ a = s₂ a := fun a ha => by
    have hm : a ∈ (slSecretList vp.sl).toFinset := List.mem_toFinset.2 ha
    simp [s₁, s₂, slSecOf, hm]
  have hsim := simulateQ_id_congr_of_aqs s₁ s₂ hagree prog haqs
  have hnat : ∀ (s : Adrs → pr.Y),
      simulateQ (fun a => (pure (s a) : Id pr.Y) : QueryImpl (Adrs →ₒ pr.Y) Id) prog =
        (let _ := pubQ pr Id
         SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
           (fun a => (pure (s a) : Id pr.Y)) pk) := fun s => by
    let _ := pubQ pr (OracleComp (Adrs →ₒ pr.Y))
    let _ := pubQ pr Id
    exact SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core
      (pubHom pr (simulateQ' (fun a => (pure (s a) : Id pr.Y) : QueryImpl (Adrs →ₒ pr.Y) Id)))
      (fun a => (Adrs →ₒ pr.Y).query a) (fun a => (pure (s a) : Id pr.Y))
      (fun a _ => simulateQ_spec_query (fun a => (pure (s a) : Id pr.Y) : QueryImpl (Adrs →ₒ pr.Y) Id) a) pk
  rw [hnat s₁, hnat s₂] at hsim
  have hL : slRootDet pr pk (fun a => pr.PRF pk skSeed a.1) =
      (let _ := pubQ pr Id
       SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
         (fun a => (pure (s₁ a) : Id pr.Y)) pk) := rfl
  have hR : Stateless.root pr skSeed pk =
      (let _ := pubQ pr Id
       SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
         (fun a => (pure (s₂ a) : Id pr.Y)) pk) := by
    let _ := pubQ pr Id
    have hprf := slRootM_prf (m := Id) pr skSeed pk
    have hgd : (let _ := pubQ pr Id
        SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
          (fun a => (pure (s₂ a) : Id pr.Y)) pk) =
        slRootM (m := Id) pr (fun x => pure (pr.PRF x.1 skSeed x.2.1)) pk := by
      exact SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core
        (HasQuery.QueryHom.id _ Id) _ _ (fun a ha => by simp [s₂, guardSec, ha]) pk
    exact (hgd.trans hprf).symm
  rw [hL, hR]
  exact hsim

/-- Real `SLHDSA.GeneralScheme.signInternal` equals `slSignDet` on the `SlSecAdrs` restriction of
`pr.PRF pk skSeed` with randomizer `pr.PRFmsgSl skPrf optRand M`. -/
theorem slSignDet_prf (skSeed : pr.SkSeed) (skPrf : pr.SkPrf) (pk : pr.PkSeed) (pkSl : pr.Y)
    (M : List Byte) (optRand : pr.Y) :
    slSignDet pr pk pkSl (fun a => pr.PRF pk skSeed a.1) M (pr.PRFmsgSl skPrf optRand M) =
      SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA M
        (Stateless.secretKey pr skSeed skPrf pk pkSl) optRand := by
  set R := pr.PRFmsgSl skPrf optRand M
  let prog : OracleComp (Adrs →ₒ pr.Y) (Stateless.Sig pr) :=
    let _ := pubQ pr (OracleComp (Adrs →ₒ pr.Y))
    SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
      (fun a => (Adrs →ₒ pr.Y).query a) M pk pkSl R
  have haqs : prog.AllQueriesSatisfy (fun a => a ∈ slSecretList vp.sl) := by
    let _ := pubQ pr (OracleComp (Adrs →ₒ pr.Y))
    exact @signInternalWithSecretRandomizerM_pred_of_ledger _ _ _
      (fun {_} (oa : OracleComp (Adrs →ₒ pr.Y) _) =>
        oa.AllQueriesSatisfy (fun a => a ∈ slSecretList vp.sl))
      (fun x => allQueriesSatisfy_pure x _)
      (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
      vp.sl pr.toSLHDSA.core (fun a => (Adrs →ₒ pr.Y).query a)
      (fun a b hb hab => by
        rw [allQueriesSatisfy_query_iff]
        exact mem_slSecretList hb hab)
      (pubQ pr (OracleComp (Adrs →ₒ pr.Y))) M pk pkSl R
      (fun _ _ _ => allQueriesSatisfy_pure _ _) (allQueriesSatisfy_pure _ _)
  let s₁ : Adrs → pr.Y := slSecOf pr (fun a => pr.PRF pk skSeed a.1)
  let s₂ : Adrs → pr.Y := fun a => pr.PRF pk skSeed a
  have hagree : ∀ a ∈ slSecretList vp.sl, s₁ a = s₂ a := fun a ha => by
    have hm : a ∈ (slSecretList vp.sl).toFinset := List.mem_toFinset.2 ha
    simp [s₁, s₂, slSecOf, hm]
  have hsim := simulateQ_id_congr_of_aqs s₁ s₂ hagree prog haqs
  have hnat : ∀ (s : Adrs → pr.Y),
      simulateQ (fun a => (pure (s a) : Id pr.Y) : QueryImpl (Adrs →ₒ pr.Y) Id) prog =
        (let _ := pubQ pr Id
         SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
           (fun a => (pure (s a) : Id pr.Y)) M pk pkSl R) := fun s => by
    let _ := pubQ pr (OracleComp (Adrs →ₒ pr.Y))
    let _ := pubQ pr Id
    exact SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
      pr.toSLHDSA.core (pubHom pr (simulateQ' (fun a => (pure (s a) : Id pr.Y) : QueryImpl (Adrs →ₒ pr.Y) Id)))
      (fun a => (Adrs →ₒ pr.Y).query a) (fun a => (pure (s a) : Id pr.Y))
      (fun a _ => simulateQ_spec_query (fun a => (pure (s a) : Id pr.Y) : QueryImpl (Adrs →ₒ pr.Y) Id) a) M pk pkSl R
  rw [hnat s₁, hnat s₂] at hsim
  have hL : slSignDet pr pk pkSl (fun a => pr.PRF pk skSeed a.1) M R =
      (let _ := pubQ pr Id
       SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
         (fun a => (pure (s₁ a) : Id pr.Y)) M pk pkSl R) := rfl
  have hR : SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA M
        (Stateless.secretKey pr skSeed skPrf pk pkSl) optRand =
      (let _ := pubQ pr Id
       SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
         (fun a => (pure (s₂ a) : Id pr.Y)) M pk pkSl R) := by
    let _ := pubQ pr Id
    have h1 : SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
        (fun a => (pure (s₂ a) : Id pr.Y)) M pk pkSl R =
        SLHDSA.GeneralScheme.signInternalWithRandomizerM vp.sl pr.toSLHDSA.core M skSeed pk pkSl R := by
      rw [SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM]
    have h2 : (SLHDSA.GeneralScheme.signInternalM vp.sl pr.toSLHDSA.core M
        (Stateless.secretKey pr skSeed skPrf pk pkSl) optRand : Id _) =
        SLHDSA.GeneralScheme.signInternalWithRandomizerM vp.sl pr.toSLHDSA.core M skSeed pk pkSl
          R := rfl
    have h3 := (SLHDSA.GeneralScheme.signInternalM_natural vp.sl pr.toSLHDSA.core
      (HasQuery.QueryHom.ofSimulateQ (m := Id)) M
      (Stateless.secretKey pr skSeed skPrf pk pkSl) optRand).symm
    have h4 := ofSimulateQ_pubQ (m := Id) pr
      (SLHDSA.GeneralScheme.signInternalM vp.sl pr.toSLHDSA.core M
        (Stateless.secretKey pr skSeed skPrf pk pkSl) optRand)
    exact ((h1.trans h2.symm).trans (h3.trans h4)).symm
  rw [hL, hR]
  exact hsim

end LedgerCongr

/-! ## 3. Standalone games `slGame0`, `slGame1`, `slGame2` and PRF reductions -/

section GamesAndPrf

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]

/-- The stateless randomizer function `PRF_msg^sl(SK.prf, opt_rand, M')` as a keyed hash
(Theorem 4.3). -/
def prfMsgSlF : Notions.KeyedHash pr.SkPrf (pr.Y × List Byte) pr.Y :=
  fun k x => pr.PRFmsgSl k x.1 x.2

/-- The oracle specification of a `PRF_msg^sl` distinguisher. -/
abbrev PrfMsgSlSpec := PRFScheme.PRFOracleSpec (pr.Y × List Byte) pr.Y

/-- The oracle specification of a standalone SLH-DSA EU-CMA adversary. -/
abbrev SlStandaloneSpec := unifSpec + (Msg →ₒ Stateless.Sig pr)

/-- Parameterized signing-phase handler for standalone SLH-DSA given an eager secret table `u`
and a monadic randomizer source `rnd : pr.Y × List Byte → m pr.Y`. -/
def slPhaseImpl {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (pk : pr.PkSeed) (pkSl : pr.Y) (u : SlSecAdrs vp → pr.Y)
    (rnd : pr.Y × List Byte → m pr.Y) :
    QueryImpl (SlStandaloneSpec pr Msg) (StateT (List Msg) m) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List Msg) m) +
  (fun msg => do
    let optRand ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : StateT (List Msg) m pr.Y)
    let R ← (liftM (rnd (optRand, pureMsg Msg enc msg)) : StateT (List Msg) m pr.Y)
    modify fun log => log ++ [msg]
    return slSignDet pr pk pkSl u (pureMsg Msg enc msg) R)

/-- Parameterized signing + verification phase for standalone SLH-DSA. -/
noncomputable def slPhaseM {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (rnd : pr.Y × List Byte → m pr.Y) : m Bool := do
  let pkSl := slRootDet pr pk u
  let ((m, σ), log) ←
    (simulateQ (slPhaseImpl pr Msg enc pk pkSl u rnd) (A.adv.main (pk, pkSl))).run []
  return (!decide (m ∈ log) && Stateless.verify pr (enc.body m) (enc.ctx m) σ pk pkSl)

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
private theorem slPhaseM_natural {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
    (Φ : m →ᵐ n) (hΦ : LiftPres Φ) {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (rnd : pr.Y × List Byte → m pr.Y) :
    Φ (slPhaseM pr Msg enc A pk u rnd) =
      slPhaseM pr Msg enc A pk u (fun x => Φ (rnd x)) := by
  unfold slPhaseM
  let pkSl := slRootDet pr pk u
  have hstep : ∀ t,
      MonadHom.stateT (List Msg) Φ (slPhaseImpl pr Msg enc pk pkSl u rnd t) =
        slPhaseImpl pr Msg enc pk pkSl u (fun x => Φ (rnd x)) t := by
    rintro (k | msg)
    · exact MonadHom.stateT_liftPres Φ hΦ _
    · dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add]
      ext log
      simp only [MonadHom.stateT_run, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind]
      change Φ ((liftM ($ᵗ pr.Y : ProbComp pr.Y) : m pr.Y) >>= fun optRand =>
        rnd (optRand, pureMsg Msg enc msg) >>= fun R =>
          pure (slSignDet pr pk pkSl u (pureMsg Msg enc msg) R, log ++ [msg])) = _
      rw [MonadHom.mmap_bind, hΦ]
      refine bind_congr fun optRand => ?_
      rw [MonadHom.mmap_bind]
      exact bind_congr fun R => MonadHom.mmap_pure _ _
  have hsim : Φ ((simulateQ (slPhaseImpl pr Msg enc pk pkSl u rnd) (A.adv.main (pk, pkSl))).run []) =
      (simulateQ (slPhaseImpl pr Msg enc pk pkSl u (fun x => Φ (rnd x)))
        (A.adv.main (pk, pkSl))).run [] := by
    rw [← MonadHom.stateT_run (List Msg) Φ, MonadHom.mmap_simulateQ _ _ _ hstep]
  rw [MonadHom.mmap_bind, hsim]
  refine bind_congr fun z => MonadHom.mmap_pure _ _

/-- **`GAME.0` (standalone SLH-DSA)**: real `PRF` secrets and real `PRF_msg^sl` randomizers. -/
noncomputable def slGame0 {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    ProbComp Bool := do
  let skSeed ← $ᵗ pr.SkSeed
  let pk ← $ᵗ pr.PkSeed
  let skPrf ← $ᵗ pr.SkPrf
  slPhaseM pr Msg enc A pk (fun a => pr.PRF pk skSeed a.1)
    (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))

/-- **`GAME.1` (standalone SLH-DSA)**: uniform secret table `u ← $ᵗ (SlSecAdrs vp → pr.Y)`,
real `PRF_msg^sl` randomizers. -/
noncomputable def slGame1 {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    ProbComp Bool := do
  let pk ← $ᵗ pr.PkSeed
  let skPrf ← $ᵗ pr.SkPrf
  let u ← $ᵗ (SlSecAdrs vp → pr.Y)
  slPhaseM pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))

/-- **`GAME.2` (standalone SLH-DSA)**: uniform secret table `u` and lazily sampled uniform
randomizers `SlRndCache pr`. -/
noncomputable def slGame2 {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    ProbComp Bool := do
  let pk ← $ᵗ pr.PkSeed
  let u ← $ᵗ (SlSecAdrs vp → pr.Y)
  (slPhaseM pr Msg enc A pk u
    (lazyRO : pr.Y × List Byte → StateT (SlRndCache pr) ProbComp pr.Y)).run' ∅

/-- **Standalone `PRF` reduction `B_sl_prf`**: queries `PRF` once at every `(pk, a)` for
`a : SlSecAdrs vp` (`≤ slSecretCount vp.sl` pairwise distinct queries), then simulates `slPhaseM`
with zero further PRF queries. -/
noncomputable def B_sl_prf {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    OracleComp (PrfSpec pr) Bool := do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (PrfSpec pr) _)
  let skPrf ← (liftM ($ᵗ pr.SkPrf : ProbComp pr.SkPrf) : OracleComp (PrfSpec pr) _)
  let u ← tableM (fun a : SlSecAdrs vp =>
    (PRFScheme.functionQuery (pk, a.1) : OracleComp (PrfSpec pr) pr.Y))
  (liftM (slPhaseM (m := ProbComp) pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))) :
    OracleComp (PrfSpec pr) Bool)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] in
private theorem tableList_prf_bound {T : Type} [DecidableEq T] [Inhabited pr.Y]
    (f : T → pr.PkSeed × Adrs) :
    ∀ l : List T,
      (tableList (fun t => (PRFScheme.functionQuery (f t) : OracleComp (PrfSpec pr) pr.Y))
        l).IsQueryBoundP Notions.IsPRFQuery l.length
  | [] => by simp [tableList]
  | t :: ts => by
    unfold tableList
    refine (isQueryBoundP_query_bind_iff _ _ _ (ts.length + 1)).2 ⟨Or.inr (Nat.succ_pos _), fun _ => ?_⟩
    simp only [Notions.IsPRFQuery, ite_true, Nat.add_sub_cancel]
    exact (isQueryBoundP_bind (n := ts.length) (m := 0)
      (tableList_prf_bound f ts) (fun _ _ => by simp)).mono (by omega)

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- `B_sl_prf` makes at most `slSecretCount vp.sl` queries to its `PRF` oracle. -/
theorem B_sl_prf_bound {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    (B_sl_prf pr Msg enc A).IsQueryBoundP Notions.IsPRFQuery (slSecretCount vp.sl) := by
  have hzero : ∀ {α : Type} (p : ProbComp α),
      (liftM p : OracleComp (PrfSpec pr) α).IsQueryBoundP Notions.IsPRFQuery 0 := fun p =>
    (isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
      rcases t with n | x
      · exact absurd ht (by simp [Notions.IsPRFQuery])
      · rfl
  unfold B_sl_prf tableM
  refine (isQueryBoundP_bind (n := 0) (m := slSecretCount vp.sl) (hzero _) fun pk _ => ?_).mono
    (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := slSecretCount vp.sl) (hzero _) fun skPrf _ => ?_).mono
    (by omega)
  have hlen : (Finset.univ : Finset (SlSecAdrs vp)).toList.length ≤ slSecretCount vp.sl := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_coe, ← length_slSecretList]
    exact List.toFinset_card_le _
  refine (isQueryBoundP_bind (n := (Finset.univ : Finset (SlSecAdrs vp)).toList.length) (m := 0)
    (tableList_prf_bound pr (fun a : SlSecAdrs vp => (pk, a.1)) _)
    (fun u _ => hzero _)).mono (by omega)

/-- **`B_sl_prf` as a PRF adversary** (Definition 4.3) with budget `q₁ = slSecretCount vp.sl`. -/
noncomputable def B_sl_prfAdv {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Notions.PRFAdversary (pr.PkSeed × Adrs) pr.Y (slSecretCount vp.sl) where
  run := B_sl_prf pr Msg enc A
  queryBound := B_sl_prf_bound pr Msg enc A

/-- **Standalone `PRF_msg^sl` reduction `B_sl_prfmsg`**: samples `u ← $ᵗ (SlSecAdrs vp → pr.Y)`
and forwards every signing query's randomizer `(optRand, M')` to its `PRF_msg^sl` oracle. -/
noncomputable def B_sl_prfmsg {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    OracleComp (PrfMsgSlSpec pr) Bool := do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (PrfMsgSlSpec pr) _)
  let u ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) : OracleComp (PrfMsgSlSpec pr) _)
  slPhaseM pr Msg enc A pk u (fun x => (PRFScheme.functionQuery x : OracleComp (PrfMsgSlSpec pr) pr.Y))

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- `B_sl_prfmsg` makes at most `qs` queries to its `PRF_msg^sl` oracle. -/
theorem B_sl_prfmsg_bound {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    (B_sl_prfmsg pr Msg enc A).IsQueryBoundP Notions.IsPRFQuery qs := by
  have hzero : ∀ {α : Type} (p : ProbComp α),
      (liftM p : OracleComp (PrfMsgSlSpec pr) α).IsQueryBoundP Notions.IsPRFQuery 0 := fun p =>
    (isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
      rcases t with n | x
      · exact absurd ht (by simp [Notions.IsPRFQuery])
      · rfl
  unfold B_sl_prfmsg slPhaseM
  refine (isQueryBoundP_bind (n := 0) (m := qs) (hzero _) fun pk _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := qs) (hzero _) fun u _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := qs) (m := 0) ?_ fun _ _ => by simp).mono (by omega)
  refine IsQueryBoundP.simulateQ_run_StateT_of_step (A.signBound (pk, slRootDet pr pk u))
    (fun t log => ?_) []
  rcases t with n | msg
  · dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.ofLift,
      Notions.IsSignQuery, ite_false]
    change ((StateT.lift (liftM (liftM (unifSpec.query n) : ProbComp _) :
      OracleComp (PrfMsgSlSpec pr) _) :
      StateT (List Msg) (OracleComp (PrfMsgSlSpec pr)) _).run log).IsQueryBoundP _ 0
    rw [StateT.run_lift]
    exact (isQueryBoundP_bind (n := 0) (m := 0) (hzero _) fun _ _ => by simp).mono (by omega)
  · dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add]
    simp only [Notions.IsSignQuery, ite_true, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind]
    refine (isQueryBoundP_bind (n := 0) (m := 1) (hzero _) fun optRand _ => ?_).mono (by omega)
    exact (isQueryBoundP_query_bind_iff _ _ _ 1).2 ⟨Or.inr Nat.one_pos, fun _ => by simp⟩

/-- **`B_sl_prfmsg` as a `PRF_msg^sl` adversary** (Definition 4.3) with budget `p = q_s`. -/
noncomputable def B_sl_prfmsgAdv {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Notions.PRFAdversary (pr.Y × List Byte) pr.Y qs where
  run := B_sl_prfmsg pr Msg enc A
  queryBound := B_sl_prfmsg_bound pr Msg enc A

/-! ## 4. Bridge `euCmaSucc → slGame0 → slGame1 → slGame2` -/

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
private theorem runWithSigningOracle_eq_slPhaseImpl (skSeed : pr.SkSeed) (skPrf : pr.SkPrf)
    (pk : pr.PkSeed) :
    let pkSl := Stateless.root pr skSeed pk
    let sk := Stateless.secretKey pr skSeed skPrf pk pkSl
    ∀ {α : Type} (oa : OracleComp (SlStandaloneSpec pr Msg) α) (l : List Msg),
      (fun z => (z.1, l ++ z.2.map fun e => e.fst)) <$>
          (slhdsaScheme pr Msg enc).runWithSigningOracle (pk, pkSl) sk oa =
        (simulateQ (slPhaseImpl pr Msg enc pk pkSl (fun a => pr.PRF pk skSeed a.1)
          (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))) oa).run l := by
  intro pkSl sk α oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp [SignatureAlg.runWithSigningOracle]
  | query_bind t k ih =>
    intro l
    simp only [SignatureAlg.runWithSigningOracle, simulateQ_bind, simulateQ_spec_query,
      WriterT.run_bind, StateT.run_bind, map_bind]
    rcases t with n | msg
    · have hL : ((unifSpec.passthrough + (slhdsaScheme pr Msg enc).signingOracle (pk, pkSl) sk)
          (Sum.inl n)).run =
          (fun u => (u, ([] : (Msg →ₒ Stateless.Sig pr).QueryLog))) <$>
            (liftM (unifSpec.query n) : ProbComp _) := by
        dsimp only [HAdd.hAdd, QueryImpl.add, OracleSpec.passthrough, QueryImpl.liftTarget,
          QueryImpl.ofLift]
        simp [map_eq_bind_pure_comp]
      have hR : ((slPhaseImpl pr Msg enc pk pkSl (fun a => pr.PRF pk skSeed a.1)
          (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))) (Sum.inl n)).run l =
          (fun u => (u, l)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.ofLift]
        simp [map_eq_bind_pure_comp]
      rw [hL, hR, bind_map_left, bind_map_left]
      refine bind_congr fun u => ?_
      have h := ih u l
      simpa [SignatureAlg.runWithSigningOracle, map_eq_bind_pure_comp, bind_assoc] using h
    · have hL : ((unifSpec.passthrough + (slhdsaScheme pr Msg enc).signingOracle (pk, pkSl) sk)
          (Sum.inr msg)).run =
          (fun optRand => (SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA
              (pureMsg Msg enc msg) sk optRand,
            ([⟨msg, SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA
              (pureMsg Msg enc msg) sk optRand⟩] : (Msg →ₒ Stateless.Sig pr).QueryLog))) <$>
            ($ᵗ pr.Y : ProbComp pr.Y) := by
        dsimp only [SignatureAlg.signingOracle, slhdsaScheme, HAdd.hAdd, QueryImpl.add,
          QueryImpl.withLogging]
        simp [WriterT.run_bind, WriterT.run_tell, map_eq_bind_pure_comp]
      have hR : ((slPhaseImpl pr Msg enc pk pkSl (fun a => pr.PRF pk skSeed a.1)
          (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))) (Sum.inr msg)).run l =
          (fun optRand => (slSignDet pr pk pkSl (fun a => pr.PRF pk skSeed a.1)
              (pureMsg Msg enc msg) (pr.PRFmsgSl skPrf optRand (pureMsg Msg enc msg)),
            l ++ [msg])) <$> ($ᵗ pr.Y : ProbComp pr.Y) := by
        dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add]
        simp [StateT.run_bind, StateT.run_monadLift, StateT.run_modify, StateT.run_pure,
          map_eq_bind_pure_comp]
      rw [hL, hR, bind_map_left, bind_map_left]
      refine bind_congr fun optRand => ?_
      have hsign := slSignDet_prf pr skSeed skPrf pk pkSl (pureMsg Msg enc msg) optRand
      rw [hsign]
      have h := ih (SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA (pureMsg Msg enc msg)
        sk optRand) (l ++ [msg])
      simpa [SignatureAlg.runWithSigningOracle, map_eq_bind_pure_comp, List.append_assoc] using h

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **EU-CMA success equals `GAME.0`**. -/
theorem euCmaSucc_eq_slGame0 {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Notions.euCmaSucc ProbCompRuntime.probComp A =
      Pr{let b ← slGame0 pr Msg enc A}[b = true] := by
  change 𝒟[SignatureAlg.unforgeableExperiment A.adv] {true} = _
  rw [prEvent_eq_evalDist_singleton]
  have hdist : SignatureAlg.unforgeableExperiment A.adv =ᵈ slGame0 pr Msg enc A := by
    unfold SignatureAlg.unforgeableExperiment slGame0 slhdsaScheme slPhaseM
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun skSeed => ?_
    refine (EvalDistEq.bind_bind_swap ($ᵗ pr.SkPrf) ($ᵗ pr.PkSeed) _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => EvalDistEq.bind_right _ fun skPrf => ?_
    have hroot := slRootDet_prf pr skSeed pk
    rw [hroot]
    have hrun := runWithSigningOracle_eq_slPhaseImpl pr Msg enc skSeed skPrf pk
      (A.adv.main (pk, Stateless.root pr skSeed pk)) []
    simp only [List.nil_append] at hrun
    rw [← hrun, bind_map_left]
    have hcongr : (do
        let z ← (slhdsaScheme pr Msg enc).runWithSigningOracle (pk, Stateless.root pr skSeed pk)
          (Stateless.secretKey pr skSeed skPrf pk (Stateless.root pr skSeed pk))
          (A.adv.main (pk, Stateless.root pr skSeed pk))
        pure (!z.2.wasQueried z.1.1 &&
          Stateless.verify pr (enc.body z.1.1) (enc.ctx z.1.1) z.1.2 pk
            (Stateless.root pr skSeed pk))) =
        (do
        let z ← (slhdsaScheme pr Msg enc).runWithSigningOracle (pk, Stateless.root pr skSeed pk)
          (Stateless.secretKey pr skSeed skPrf pk (Stateless.root pr skSeed pk))
          (A.adv.main (pk, Stateless.root pr skSeed pk))
        pure (!decide (z.1.1 ∈ List.map (fun e => e.fst) z.2) &&
          Stateless.verify pr (enc.body z.1.1) (enc.ctx z.1.1) z.1.2 pk
            (Stateless.root pr skSeed pk))) :=
      bind_congr fun z => by rw [QueryLog.wasQueried_eq_decide_mem_map_fst]
    exact EvalDistEq.of_evalDist_eq (congrArg evalDist hcongr)
  exact congrArg (fun μ => μ {true}) hdist.evalDist_eq

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Real world of `B_sl_prf` equals `slGame0`**. -/
theorem prfReal_B_sl_prf {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    (Notions.KeyedHash.toPRF (prfF pr)).prfRealExperiment (B_sl_prf pr Msg enc A) =
      slGame0 pr Msg enc A := by
  unfold PRFScheme.prfRealExperiment slGame0 B_sl_prf
  refine bind_congr fun skSeed => ?_
  set Φ := simulateQ' ((Notions.KeyedHash.toPRF (prfF pr)).prfRealQueryImpl skSeed)
  have hL : LiftPres Φ := Claim411.liftPres_real pr skSeed
  change Φ _ = _
  rw [MonadHom.mmap_bind, hL]
  refine bind_congr fun pk => ?_
  rw [MonadHom.mmap_bind, hL]
  refine bind_congr fun skPrf => ?_
  rw [MonadHom.mmap_bind, tableM, Claim411.tableList_natural]
  have hq : (fun a : SlSecAdrs vp => Φ (PRFScheme.functionQuery (pk, a.1))) =
      fun a => pure (pr.PRF pk skSeed a.1) :=
    funext fun a => PRFScheme.simulateQ_prfRealQueryImpl_functionQuery _ _ _
  rw [hq, ← tableM, Claim411.tableM_pure, pure_bind, hL]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] in
private theorem table_run_sl (pk : pr.PkSeed) (l : List (SlSecAdrs vp)) (hl : l.Nodup)
    (c : Claim411.PrfCache pr) (hc : ∀ a ∈ l, c (pk, a.1) = none) :
    Prod.fst <$>
        (tableList (fun a : SlSecAdrs vp => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, a.1))
          l).run c =
      tableList (fun _ => ($ᵗ pr.Y : ProbComp pr.Y)) l := by
  induction l generalizing c with
  | nil => simp [tableList]
  | cons t ts ih =>
    rw [List.nodup_cons] at hl
    simp only [tableList, StateT.run_bind, randomOracle.run_eq, hc t List.mem_cons_self, map_bind,
      bind_assoc, pure_bind]
    refine bind_congr fun u => ?_
    have hc' : ∀ a ∈ ts, (c.cacheQuery (pk, t.1) u) (pk, a.1) = none := by
      intro a ha
      have hne : a ≠ t := fun e => hl.1 (e ▸ ha)
      rw [QueryCache.cacheQuery_of_ne _ _ fun e => hne (Subtype.ext (congrArg Prod.snd e))]
      exact hc a (List.mem_cons_of_mem _ ha)
    have h2 := congrArg (fun x => (fun g => Function.update g t u) <$> x) (ih hl.2 _ hc')
    simp only [Functor.map_map] at h2
    simpa [map_eq_bind_pure_comp] using h2

omit [Fintype pr.Y] in
/-- **Ideal world of `B_sl_prf` is distributed as `slGame1`**. -/
theorem prfIdeal_B_sl_prf {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    PRFScheme.prfIdealExperiment (B_sl_prf pr Msg enc A) =ᵈ slGame1 pr Msg enc A := by
  unfold PRFScheme.prfIdealExperiment slGame1 B_sl_prf
  set Ψ := simulateQ' (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y))
  have hL : LiftPres Ψ := Claim411.liftPres_unifFwd _
  change (Ψ _).run' ∅ =ᵈ _
  rw [MonadHom.mmap_bind, hL, Claim411.run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun pk => ?_
  rw [MonadHom.mmap_bind, hL, Claim411.run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun skPrf => ?_
  rw [MonadHom.mmap_bind, tableM, Claim411.tableList_natural]
  have hq : (fun a : SlSecAdrs vp => Ψ (PRFScheme.functionQuery (pk, a.1))) =
      fun a => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, a.1) :=
    funext fun a => PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery _
  simp only [hq, StateT.run'_eq, StateT.run_bind, map_bind]
  have hrun : ∀ (u : SlSecAdrs vp → pr.Y) (c : Claim411.PrfCache pr),
      Prod.fst <$> ((Ψ (liftM (slPhaseM (m := ProbComp) pr Msg enc A pk u
        (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2)))) :
          StateT (Claim411.PrfCache pr) ProbComp Bool).run c) =
        slPhaseM (m := ProbComp) pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2)) := by
    intro u c
    rw [hL]
    simp [StateT.run_monadLift]
  simp_rw [hrun]
  have htbl := table_run_sl pr pk (Finset.univ : Finset (SlSecAdrs vp)).toList
    (Finset.nodup_toList _) ∅ (fun _ _ => rfl)
  rw [← bind_map_left (f := Prod.fst) (g := fun u =>
    slPhaseM (m := ProbComp) pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))), htbl]
  exact EvalDistEq.bind_left Claim411.tableM_uniform _

omit [Fintype pr.Y] in
/-- **Hop 1 (`GAME.0 → GAME.1`, `PRF`, budget `q₁ = slSecretCount vp.sl`)**. -/
theorem hop1_prf {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Pr{let b ← slGame0 pr Msg enc A}[b = true] ≤
      Pr{let b ← slGame1 pr Msg enc A}[b = true] +
        Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfAdv pr Msg enc A) := by
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, ← prfReal_B_sl_prf,
    ← (prfIdeal_B_sl_prf pr Msg enc A).evalDist_eq]
  exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Real world of `B_sl_prfmsg` is distributed as `slGame1`**. -/
theorem prfReal_B_sl_prfmsg {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    (Notions.KeyedHash.toPRF (prfMsgSlF pr)).prfRealExperiment (B_sl_prfmsg pr Msg enc A) =ᵈ
      slGame1 pr Msg enc A := by
  have heq : (Notions.KeyedHash.toPRF (prfMsgSlF pr)).prfRealExperiment (B_sl_prfmsg pr Msg enc A) =
      (do
        let skPrf ← $ᵗ pr.SkPrf
        let pk ← $ᵗ pr.PkSeed
        let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        slPhaseM pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2))) := by
    unfold PRFScheme.prfRealExperiment B_sl_prfmsg
    refine bind_congr fun skPrf => ?_
    set Φ := simulateQ' ((Notions.KeyedHash.toPRF (prfMsgSlF pr)).prfRealQueryImpl skPrf)
    have hL : LiftPres Φ := fun p => by
      rw [simulateQ'_apply, ← liftComp_eq_liftM, PRFScheme.simulateQ_prfRealQueryImpl_liftComp]; rfl
    change Φ _ = _
    rw [MonadHom.mmap_bind, hL]
    refine bind_congr fun pk => ?_
    rw [MonadHom.mmap_bind, hL]
    refine bind_congr fun u => ?_
    rw [slPhaseM_natural pr Msg enc Φ hL]
    rfl
  rw [heq]
  exact EvalDistEq.bind_bind_swap ($ᵗ pr.SkPrf) ($ᵗ pr.PkSeed) _

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Ideal world of `B_sl_prfmsg` equals `slGame2`**. -/
theorem prfIdeal_B_sl_prfmsg {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    PRFScheme.prfIdealExperiment (B_sl_prfmsg pr Msg enc A) = slGame2 pr Msg enc A := by
  unfold PRFScheme.prfIdealExperiment slGame2 B_sl_prfmsg
  set Ψ := simulateQ' (PRFScheme.prfIdealQueryImpl (D := pr.Y × List Byte) (R := pr.Y))
  have hL : LiftPres Ψ := Claim411.liftPres_unifFwd _
  change (Ψ _).run' ∅ = _
  rw [MonadHom.mmap_bind, hL, Claim411.run'_liftM_bind]
  refine bind_congr fun pk => ?_
  rw [MonadHom.mmap_bind, hL, Claim411.run'_liftM_bind]
  refine bind_congr fun u => ?_
  rw [slPhaseM_natural pr Msg enc Ψ hL]
  congr 2
  funext x
  have h1 : Ψ (PRFScheme.functionQuery x) = (pr.Y × List Byte →ₒ pr.Y).randomOracle x :=
    PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery _
  rw [h1]
  ext c
  rw [randomOracle.run_eq]
  unfold lazyRO
  rw [StateT.run_mk]
  cases c x
  · simp [map_eq_bind_pure_comp]
  · rfl

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Hop 2 (`GAME.1 → GAME.2`, `PRF_msg^sl`, budget `q_s`)**. -/
theorem hop2_prfmsg {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Pr{let b ← slGame1 pr Msg enc A}[b = true] ≤
      Pr{let b ← slGame2 pr Msg enc A}[b = true] +
        Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr)) (B_sl_prfmsgAdv pr Msg enc A) := by
  rw [← (prfReal_B_sl_prfmsg pr Msg enc A).prEvent_eq _, ← prfIdeal_B_sl_prfmsg pr Msg enc A,
    prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
  exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _

/-! ## 5. Bridge `slGame2 → Slhdsa.postPrfExp (SfStage1.unit pr)` -/

/-- Wrapper handler converting a standalone SLH-DSA adversary's `Msg` signing queries into
encoded `List Byte` queries to `SlAdvSpec pr` while tracking `log : List Msg`. -/
def slAdvWrapImpl : QueryImpl (SlStandaloneSpec pr Msg) (StateT (List Msg) (OracleComp (SlAdvSpec pr))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (SlAdvSpec pr))).liftTarget
      (StateT (List Msg) (OracleComp (SlAdvSpec pr))) +
  (fun msg => do
    let σ ← (liftM ((SlAdvSpec pr).query (.inr (pureMsg Msg enc msg))) :
      StateT (List Msg) (OracleComp (SlAdvSpec pr)) (Stateless.Sig pr))
    modify fun log => log ++ [msg]
    return σ)

/-- Standalone SLH-DSA EU-CMA adversary packaged as a `PostPrfAdv pr Unit Unit qs`. -/
noncomputable def slPostPrfAdv {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    PostPrfAdv pr Unit Unit qs where
  run _ _ pk pkSl := do
    let ((m, σ), log) ← (simulateQ (slAdvWrapImpl pr Msg enc) (A.adv.main (pk, pkSl))).run []
    return (if m ∉ log then some (pureMsg Msg enc m, σ) else none)
  signBound _ _ pk pkSl := by
    refine (isQueryBoundP_bind (n := qs) (m := 0) ?_ fun _ _ => by simp).mono (by omega)
    refine IsQueryBoundP.simulateQ_run_StateT_of_step (A.signBound (pk, pkSl))
      (fun t log => ?_) []
    rcases t with n | msg
    · dsimp only [slAdvWrapImpl, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.ofLift,
        Notions.IsSignQuery, ite_false]
      change ((StateT.lift (liftM (unifSpec.query n) : OracleComp (SlAdvSpec pr) _) :
        StateT (List Msg) (OracleComp (SlAdvSpec pr)) _).run log).IsQueryBoundP IsSlSignQuery 0
      rw [StateT.run_lift]
      exact (isQueryBoundP_query_bind_iff _ _ _ 0).2 ⟨Or.inl (by simp [IsSlSignQuery]), fun _ => by simp⟩
    · dsimp only [slAdvWrapImpl, HAdd.hAdd, QueryImpl.add]
      simp only [Notions.IsSignQuery, ite_true, StateT.run_bind, StateT.run_monadLift,
        StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind]
      exact (isQueryBoundP_query_bind_iff _ _ _ 1).2 ⟨Or.inr Nat.one_pos, fun _ => by simp⟩

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] in
private theorem lockstep_slGame2 (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    let pkSl := slRootDet pr pk u
    ∀ {α : Type} (oa : OracleComp (SlStandaloneSpec pr Msg) α)
      (log : List Msg) (slSt : SlSignSt pr)
      (k₁ : α → List Msg → SlRndCache pr → ProbComp Bool)
      (k₂ : α → List Msg → SlSignSt pr → ProbComp Bool),
      slSt.log = log.map (pureMsg Msg enc) →
      slSt.rnd = slSt.rnd →
      (∀ a log' slSt', slSt'.log = log'.map (pureMsg Msg enc) →
        𝒟[k₁ a log' slSt'.rnd] {true} ≤ 𝒟[k₂ a log' slSt'] {true}) →
      𝒟[((simulateQ (slPhaseImpl pr Msg enc pk pkSl u
            (lazyRO : pr.Y × List Byte → StateT (SlRndCache pr) ProbComp pr.Y)) oa).run log).run
            slSt.rnd >>= fun z => k₁ z.1.1 z.1.2 z.2] {true} ≤
      𝒟[(simulateQ (slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
            ((simulateQ (slAdvWrapImpl pr Msg enc) oa).run log)).run slSt >>=
            fun z => k₂ z.1.1 z.1.2 z.2] {true} := by
  intro pkSl α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log slSt k₁ k₂ hlog _ hk
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a log slSt hlog
  | query_bind t k ih =>
    intro log slSt k₁ k₂ hlog _ hk
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases t with n | msg
    · have hL : (((slPhaseImpl pr Msg enc pk pkSl u
          (lazyRO : pr.Y × List Byte → StateT (SlRndCache pr) ProbComp pr.Y))
          (.inl n)).run log).run slSt.rnd =
          (fun x => ((x, log), slSt.rnd)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.ofLift]
        simp [StateT.run_monadLift, map_eq_bind_pure_comp]
      have hR : (simulateQ (slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((slAdvWrapImpl pr Msg enc (.inl n)).run log)).run slSt =
          (fun x => ((x, log), slSt)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        change (simulateQ (slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((StateT.lift (liftM (unifSpec.query n) : OracleComp (SlAdvSpec pr) _)).run log)).run slSt = _
        rw [StateT.run_lift, simulateQ_bind, StateT.run_bind]
        change (((slSignImpl pr pk pkSl (slSignDet pr pk pkSl u) (.inl n)).run slSt) >>=
          fun z => pure ((z.1, log), z.2)) = _
        dsimp only [slSignImpl, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.ofLift]
        simp [map_eq_bind_pure_comp]
      rw [hL, hR, bind_map_left, bind_map_left]
      exact evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun u _ =>
        ih u log slSt k₁ k₂ hlog rfl hk
    · have hL : (((slPhaseImpl pr Msg enc pk pkSl u
          (lazyRO : pr.Y × List Byte → StateT (SlRndCache pr) ProbComp pr.Y))
          (.inr msg)).run log).run slSt.rnd = (do
            let optRand ← $ᵗ pr.Y
            match slSt.rnd (optRand, pureMsg Msg enc msg) with
            | some R =>
                pure ((slSignDet pr pk pkSl u (pureMsg Msg enc msg) R, log ++ [msg]), slSt.rnd)
            | none =>
                let R ← $ᵗ pr.Y
                pure ((slSignDet pr pk pkSl u (pureMsg Msg enc msg) R, log ++ [msg]),
                  slSt.rnd.cacheQuery (optRand, pureMsg Msg enc msg) R)) := by
        dsimp only [slPhaseImpl, HAdd.hAdd, QueryImpl.add]
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_modify,
          StateT.run_pure, bind_assoc, pure_bind, lazyRO, StateT.run_mk]
        refine bind_congr fun optRand => ?_
        cases slSt.rnd (optRand, pureMsg Msg enc msg) with
        | some R => simp
        | none => simp [map_eq_bind_pure_comp]
      have hsl_inr : (slSignImpl pr pk pkSl (slSignDet pr pk pkSl u)
          (.inr (pureMsg Msg enc msg))).run slSt = (do
            let optRand ← $ᵗ pr.Y
            match slSt.rnd (optRand, pureMsg Msg enc msg) with
            | some R =>
                pure (slSignDet pr pk pkSl u (pureMsg Msg enc msg) R,
                  { slSt with log := slSt.log ++ [pureMsg Msg enc msg] })
            | none =>
                let R ← $ᵗ pr.Y
                pure (slSignDet pr pk pkSl u (pureMsg Msg enc msg) R,
                  { log := slSt.log ++ [pureMsg Msg enc msg]
                    rnd := slSt.rnd.cacheQuery (optRand, pureMsg Msg enc msg) R
                    itLog := slSt.itLog ++ [(R, (pk, pkSl, pureMsg Msg enc msg))] })) := by
        dsimp only [slSignImpl, HAdd.hAdd, QueryImpl.add]
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_get,
          bind_assoc, pure_bind]
        refine bind_congr fun optRand => ?_
        cases slSt.rnd (optRand, pureMsg Msg enc msg) with
        | some R => simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        | none => simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind]
      have hR : (simulateQ (slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((slAdvWrapImpl pr Msg enc (.inr msg)).run log)).run slSt = (do
            let optRand ← $ᵗ pr.Y
            match slSt.rnd (optRand, pureMsg Msg enc msg) with
            | some R =>
                pure ((slSignDet pr pk pkSl u (pureMsg Msg enc msg) R, log ++ [msg]),
                  { slSt with log := slSt.log ++ [pureMsg Msg enc msg] })
            | none =>
                let R ← $ᵗ pr.Y
                pure ((slSignDet pr pk pkSl u (pureMsg Msg enc msg) R, log ++ [msg]),
                  { log := slSt.log ++ [pureMsg Msg enc msg]
                    rnd := slSt.rnd.cacheQuery (optRand, pureMsg Msg enc msg) R
                    itLog := slSt.itLog ++ [(R, (pk, pkSl, pureMsg Msg enc msg))] })) := by
        dsimp only [slAdvWrapImpl, HAdd.hAdd, QueryImpl.add]
        simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_modify,
          StateT.run_pure, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_assoc,
          pure_bind]
        rw [hsl_inr, bind_assoc]
        refine bind_congr fun optRand => ?_
        cases slSt.rnd (optRand, pureMsg Msg enc msg) with
        | some R => simp
        | none => simp
      rw [hL, hR, bind_assoc, bind_assoc]
      refine evalDist_bind_apply_mono_of_support ($ᵗ pr.Y) _ _ (measurableSet_singleton true)
        fun optRand _ => ?_
      have hlog' : slSt.log ++ [pureMsg Msg enc msg] = (log ++ [msg]).map (pureMsg Msg enc) := by
        simp [hlog]
      cases slSt.rnd (optRand, pureMsg Msg enc msg) with
      | some R =>
        simp only [pure_bind]
        exact ih _ (log ++ [msg]) { slSt with log := slSt.log ++ [pureMsg Msg enc msg] }
          k₁ k₂ hlog' rfl hk
      | none =>
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_apply_mono_of_support ($ᵗ pr.Y) _ _ (measurableSet_singleton true)
          fun R _ => ?_
        exact ih _ (log ++ [msg])
          { log := slSt.log ++ [pureMsg Msg enc msg]
            rnd := slSt.rnd.cacheQuery (optRand, pureMsg Msg enc msg) R
            itLog := slSt.itLog ++ [(R, (pk, pkSl, pureMsg Msg enc msg))] }
          k₁ k₂ hlog' rfl hk

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Bridge from `slGame2` to `Slhdsa.postPrfExp` under `enc.Injective`**. -/
theorem pr_slGame2_le_postPrf (henc : enc.Injective)
    {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Pr{let b ← slGame2 pr Msg enc A}[b = true] ≤
      Pr{let z ← postPrfExp pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)}[
        PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1] := by
  have hpr : ∀ {α : Type} (mx : ProbComp α) (P : α → Prop),
      Pr{let x ← mx}[P x] = 𝒟[mx >>= fun x => pure (decide (P x))] {true} := by
    intro α mx P
    rw [prEvent_def, map_eq_bind_pure_comp]
    let : MeasurableSpace Prop := ⊤
    let : MeasurableSpace Bool := ⊤
    have h1 := lintegral_evalDist_bind_mono_of_support mx (fun x => pure (P x))
      (fun x => pure (decide (P x))) (v := Set.indicator {True} 1) (w := Set.indicator {true} 1)
      (measurable_of_countable _) (measurable_of_countable _)
      (fun x _ => by by_cases hx : P x <;> simp [hx])
    have h2 := lintegral_evalDist_bind_mono_of_support mx (fun x => pure (decide (P x)))
      (fun x => pure (P x)) (v := Set.indicator {true} 1) (w := Set.indicator {True} 1)
      (measurable_of_countable _) (measurable_of_countable _)
      (fun x _ => by by_cases hx : P x <;> simp [hx])
    rw [MeasureTheory.lintegral_indicator_one (by trivial),
        MeasureTheory.lintegral_indicator_one (by trivial)] at h1 h2
    exact le_antisymm h1 h2
  rw [prEvent_eq_evalDist_singleton, hpr]
  unfold slGame2 postPrfExp SfStage1.unit runPostPrf slPostPrfAdv slPhaseM
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  refine evalDist_bind_apply_mono_of_support ($ᵗ pr.PkSeed) _ _ (measurableSet_singleton true)
    fun pk _ => ?_
  refine evalDist_bind_apply_mono_of_support ($ᵗ (SlSecAdrs vp → pr.Y)) _ _
    (measurableSet_singleton true) fun u _ => ?_
  let pkSl := slRootDet pr pk u
  refine lockstep_slGame2 pr Msg enc pk u (A.adv.main (pk, pkSl)) [] (SlSignSt.init pr)
    (fun a log' _ => pure (!decide (a.1 ∈ log') &&
      Stateless.verify pr (enc.body a.1) (enc.ctx a.1) a.2 pk pkSl))
    (fun a log' slSt' => pure (decide (PostPrfWin pr pk pkSl slSt'.log
      (if a.1 ∉ log' then some (pureMsg Msg enc a.1, a.2) else none))))
    rfl rfl fun ⟨mf, σf⟩ log' slSt' hlog => ?_
  by_cases hL : (!decide (mf ∈ log') &&
      Stateless.verify pr (enc.body mf) (enc.ctx mf) σf pk pkSl) = true
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hL
    obtain ⟨hfr, hver⟩ := hL
    have hnotSl : pureMsg Msg enc mf ∉ slSt'.log := by
      rw [hlog, List.mem_map]
      rintro ⟨m0, hm0, heq⟩
      exact hfr (pureMsg_injective Msg enc henc heq ▸ hm0)
    have hver' : SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA
        (pureMsg Msg enc mf) σf ⟨pk, pkSl⟩ = true := by
      rw [← statelessVerify_eq_verifyInternal pr Msg enc pk pkSl mf σf]
      exact hver
    have hR : PostPrfWin pr pk pkSl slSt'.log
        (if mf ∉ log' then some (pureMsg Msg enc mf, σf) else none) := by
      rw [ite_eq_left_iff.2 (fun h => (h hfr).elim)]
      exact ⟨hnotSl, hver'⟩
    rw [decide_eq_true hR]
    cases (!decide (mf ∈ log') &&
      Stateless.verify pr (enc.body mf) (enc.ctx mf) σf pk pkSl) <;> simp
  · have hfalse : (!decide (mf ∈ log') &&
        Stateless.verify pr (enc.body mf) (enc.ctx mf) σf pk pkSl) = false :=
      Bool.eq_false_iff.2 hL
    rw [hfalse]
    simp

/-! ## 6. Main Paper Theorem 4.3 (`theorem_4_3`, `theorem_4_3_of_ud_le`) -/

/-- **Main Paper Theorem 4.3 (`[HK22]`, standalone EU-CMA security of SLH-DSA)**:
under `hinj : Function.Injective pr.yToBytes` and `henc : enc.Injective`, for every `q_s`-query
EU-CMA adversary `A` against pure-mode hedged SLH-DSA, `Succ^{EU-CMA}(A)` is bounded by all twelve
explicit terms of Theorem 4.3 (`PRF` with `q₁ = slSecretCount vp.sl`, `PRF_msg^sl` with `q_s`,
`ITSR` for `H_msg^sl`, `w - 2` WOTS-TW `SM-UD` terms, WOTS-TW `SM-PRE`, WOTS-TW `F` `SM-TCR`,
XMSS `H` `SM-TCR`, `Th_k` `SM-TCR`, `Th_lsl` `SM-TCR`, FORS `H` `SM-TCR`, `3 ·` FORS `F` `SM-TCR`,
and FORS `F` `SM-DSPR`). -/
theorem theorem_4_3 (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Notions.euCmaSucc ProbCompRuntime.probComp A ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr)) (B_sl_prfmsgAdv pr Msg enc A) +
      Notions.itsrSucc (slHmsg pr) (slMap vp)
        (B_itsr pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (B_ud pr (SfStage1.unit pr)
          (wotsStage2 pr (slPostPrfAdv pr Msg enc A)) γ) +
      SM_DT_PRE_Advantage (B_pre pr (SfStage1.unit pr)
        (wotsStage2 pr (slPostPrfAdv pr Msg enc A))) +
      SM_DT_TCR_Advantage (B_tcrF_wots pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrH_xmss pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrThK pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrThLsl pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrH_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      3 * SM_DT_TCR_Advantage (B_tcrF_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_DSPR_Advantage (B_dsprF_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) := by
  rw [euCmaSucc_eq_slGame0 pr Msg enc A]
  have h1 := hop1_prf pr Msg enc A
  have h2 := hop2_prfmsg pr Msg enc A
  have h3 := (pr_slGame2_le_postPrf pr Msg enc henc A).trans
    (postPrf_bound pr hinj (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A))
  calc Pr{let b ← slGame0 pr Msg enc A}[b = true]
      ≤ Pr{let b ← slGame1 pr Msg enc A}[b = true] +
          Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfAdv pr Msg enc A) := h1
    _ ≤ (Pr{let b ← slGame2 pr Msg enc A}[b = true] +
          Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr)) (B_sl_prfmsgAdv pr Msg enc A)) +
          Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfAdv pr Msg enc A) :=
        add_le_add h2 le_rfl
    _ ≤ _ := by
        have hstep := add_le_add (add_le_add h3
          (le_refl (Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr))
            (B_sl_prfmsgAdv pr Msg enc A))))
          (le_refl (Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr))
            (B_sl_prfAdv pr Msg enc A)))
        refine hstep.trans (le_of_eq ?_)
        ring

/-- **Main Paper Theorem 4.3 (`w · InSec^{sm-ud}` form)**: with a common bound `ε_ud` on the
`w - 2` WOTS-TW SM-UD hybrid advantages, the SM-UD sum is at most `w · ε_ud` (and in fact at most
`(w - 2) · ε_ud`). -/
theorem theorem_4_3_of_ud_le (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) {εud : ℝ≥0∞}
    (hud : ∀ γ < vp.params.w - 2,
      SM_DT_UD_Advantage (B_ud pr (SfStage1.unit pr)
        (wotsStage2 pr (slPostPrfAdv pr Msg enc A)) γ) ≤ εud) :
    Notions.euCmaSucc ProbCompRuntime.probComp A ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr)) (B_sl_prfmsgAdv pr Msg enc A) +
      Notions.itsrSucc (slHmsg pr) (slMap vp)
        (B_itsr pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      vp.params.w * εud +
      SM_DT_PRE_Advantage (B_pre pr (SfStage1.unit pr)
        (wotsStage2 pr (slPostPrfAdv pr Msg enc A))) +
      SM_DT_TCR_Advantage (B_tcrF_wots pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrH_xmss pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrThK pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrThLsl pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrH_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      3 * SM_DT_TCR_Advantage (B_tcrF_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_DSPR_Advantage (B_dsprF_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) := by
  refine (theorem_4_3 pr Msg enc hinj henc A).trans ?_
  gcongr
  calc ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (B_ud pr (SfStage1.unit pr)
          (wotsStage2 pr (slPostPrfAdv pr Msg enc A)) γ)
      ≤ ∑ _γ ∈ Finset.range (vp.params.w - 2), εud :=
        Finset.sum_le_sum fun γ hγ => hud γ (Finset.mem_range.mp hγ)
    _ = ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * εud := by simp
    _ ≤ vp.params.w * εud := by gcongr; exact_mod_cast Nat.sub_le _ _

end GamesAndPrf

end ShrincsSecurity.Slhdsa

end
