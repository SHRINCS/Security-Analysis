module

public import ShrincsSecurity.Slhdsa.WotsHybrid
public import ShrincsSecurity.Notions.ITSR
public import ShrincsSecurity.Repro.Lazy

/-!
# Post-PRF standard-model security of SLH-DSA (Main Paper Theorem 4.3 & Claim 4.16 core)

This module proves the **complete post-PRF security bound** for the stateless SLH-DSA path
(`H_msg^sl` + `Th_λ`), parameterized by an arbitrary Stage-1 stateful `O_coll` precomputation
hook `sfStage : SfStage1 pr D E` (`WotsHybrid.lean`):

* For **Main Paper Claim 4.16** (`Shrincs/Claim416.lean`), `sfStage` is `SfStage1.shrincs`
  (precomputing `PK.sf` and all stateful FXMSS signatures via `O_coll` at `Scheme.IsStateful`
  tweaks).
* For **Main Paper Theorem 4.3** (`Slhdsa/Theorem43.lean`), `sfStage` is `SfStage1.unit` (no-op).

## Main Theorem (`postPrf_bound`)

For any `qs`-signing-query post-PRF adversary `adv : PostPrfAdv pr D E qs`, under
`hinj : Function.Injective pr.yToBytes`:

`Pr[PostPrfWin] ≤`
1. `Succ^{ITSR}_{H_msg^sl, qs}(B_itsr)` (exact zero-loss ITSR reduction with local randomizer cache)
2. `+ ∑ γ < w - 2, Adv^{SM-UD}_{F ∈ Th_λ, q₂}(B_ud γ)` (`q₂ = wotsInstanceCount · len`)
3. `+ Adv^{SM-PRE}_{F ∈ Th_λ, q₂}(B_pre)`
4. `+ Adv^{SM-TCR}_{F ∈ Th_λ, q₃}(B_tcrF_wots)` (`q₃ = wotsStepAddresses.length`)
5. `+ Adv^{SM-TCR}_{H ∈ Th_λ, q₄}(B_tcrH_xmss)` (`q₄ = xmssNodeAddresses.length`)
6. `+ Adv^{SM-TCR}_{Th_k ∈ Th_λ, q₅}(B_tcrThK)` (`q₅ = forsRootAddresses.length`)
7. `+ Adv^{SM-TCR}_{Th_lsl ∈ Th_λ, q₆}(B_tcrThLsl)` (`q₆ = wotsPkAddresses.length`)
8. `+ Adv^{SM-TCR}_{H ∈ Th_λ, q₇}(B_tcrH_fors)` (`q₇ = forsTreeAddresses.length`)
9. `+ 3 · Adv^{SM-TCR}_{F ∈ Th_λ, q₈}(B_tcrF_fors)` (`q₈ = forsLeafAddresses.length`)
10. `+ Adv^{SM-DSPR}_{F ∈ Th_λ, q₈}(B_dsprF_fors)`.

Every collection reduction precomputes the entire virtual SLH-DSA hypertree (and any stateful
precomputation from `sfStage`) in Stage 1 via `O_coll` and its challenge oracle, and makes
**zero** `Th_λ` evaluations in Stage 2 (`slSignTable` / `hybSign`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Slhdsa

open Scheme Shrincs SLHDSA.Security
open SLHDSA (Adrs AddrType Byte wotsSkAdrs wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsSkAdrs forsNodeAdrs forsPkAdrs chainStepsCore chainStepsCore_le
  chain chain_zero chain_compose wotsSign wotsSign_eq_ofFn wotsPkGenTops wotsPkGenTops_eq_ofFn
  forsPkGen forsPkFromSig forsLeaf forsNodeHash forsIdx forsIdx_lt
  LayerPosition DigestParts splitDigest)

private theorem evalDistEq_apply_true {mx my : ProbComp Bool} (h : mx =ᵈ my) :
    𝒟[mx] {true} = 𝒟[my] {true} := by
  have htop : (⊤ : MeasurableSpace Bool) = (inferInstance : MeasurableSpace Bool) :=
    MeasurableSpace.ext fun s => ⟨fun _ => MeasurableSet.of_discrete, fun _ => trivial⟩
  have h1 := congrArg (fun μ => μ {true}) h.evalDist_eq
  simpa only [htop] using h1

private theorem prEvent_eq_evalDist_bind {α : Type} (mx : ProbComp α) (P : α → Prop) :
    Pr{let x ← mx}[P x] = 𝒟[mx >>= fun x => pure (decide (P x))] {true} := by
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

private theorem prEvent_biUnion_finset {α ι : Type} (mx : ProbComp α) (s : Finset ι)
    (P : ι → α → Prop) (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, ¬ (P i a ∧ P j a)) :
    Pr{let a ← mx}[∃ i ∈ s, P i a] = ∑ i ∈ s, Pr{let a ← mx}[P i a] := by
  let : MeasurableSpace α := ⊤
  have h1 : ∀ Q : α → Prop, Pr{let a ← mx}[Q a] = 𝒟[mx] {a | Q a} := fun Q => by
    rw [prEvent_eq_evalDist_bind]
    have h2 := (MeasureTheory.lintegral_indicator_one (μ := 𝒟[mx >>= fun a => pure (decide (Q a))])
      (measurableSet_singleton true)).symm
    rw [h2, lintegral_evalDist_bind_of_discrete _ _ (measurable_of_countable _)]
    have hcongr : (fun a => ∫⁻ y, Set.indicator {true} 1 y ∂𝒟[(pure (decide (Q a)) : ProbComp Bool)]) =
        Set.indicator {a | Q a} 1 := by
      funext a; by_cases ha : Q a <;> simp [ha]
    rw [hcongr, MeasureTheory.lintegral_indicator_one (by trivial)]
  simp_rw [h1]
  have hset : {a | ∃ i ∈ s, P i a} = ⋃ i ∈ s, {a | P i a} := by ext a; simp
  rw [hset, MeasureTheory.measure_biUnion_finset]
  · intro i hi j hj hne
    rw [Function.onFun, Set.disjoint_left]
    intro a hia hja; exact hdisj i hi j hj hne a ⟨hia, hja⟩
  · intro i _; trivial

private theorem bottomPosition_ext_of_forsAdrs {vp : SLHDSA.ValidatedParams}
    {p₁ p₂ : BottomPosition vp}
    (htr : p₁.forsAdrs.tree = p₂.forsAdrs.tree)
    (hkp : p₁.forsAdrs.getKeyPairAddress = p₂.forsAdrs.getKeyPairAddress) : p₁ = p₂ := by
  cases p₁; cases p₂
  congr 1
  · exact Fin.ext htr
  · exact Fin.ext hkp

instance {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y] :
    Inhabited (pr.MemberMsg .F) := ‹Inhabited pr.Y›

instance {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y] :
    Inhabited (pr.MemberMsg .H) := inferInstanceAs (Inhabited (pr.Y × pr.Y))

instance {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y] :
    Inhabited (pr.MemberMsg .thK) := inferInstanceAs (Inhabited (Vector pr.Y vp.params.k))

instance {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y] :
    Inhabited (pr.MemberMsg .thLsl) := inferInstanceAs (Inhabited (Vector pr.Y vp.params.lsl))

instance {vp : ValidatedParams} (pr : Primitives vp.params) [Fintype pr.Y] :
    Fintype (pr.MemberMsg .F) := ‹Fintype pr.Y›

/-! ## 1. Post-PRF Stateless Signing Game -/

section PostPrfGame

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- Stateless signing oracle specification: input is the FIPS 205 encoded message `M' : List Byte`,
output is an SLH-DSA signature `Stateless.Sig pr`. -/
abbrev SlSignSpec : OracleSpec (List Byte) :=
  List Byte →ₒ Stateless.Sig pr

/-- Oracle specification for a post-PRF stateless adversary: private coins plus stateless signing. -/
abbrev SlAdvSpec : OracleSpec (ℕ ⊕ List Byte) :=
  unifSpec + SlSignSpec pr

/-- Predicate selecting stateless signing queries in `SlAdvSpec`. -/
def IsSlSignQuery : ℕ ⊕ List Byte → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsSlSignQuery := fun x => by
  rcases x with _ | _ <;> simp only [IsSlSignQuery] <;> infer_instance

/-- Lazy uniform randomizer cache `(optRand, M') ↦ R` (post-`PRF_msg` hop). -/
abbrev SlRndCache : Type := (pr.Y × List Byte →ₒ pr.Y).QueryCache

/-- State threaded through the post-PRF stateless signing oracle:
* `log`: all queried encoded messages `M'`
* `rnd`: lazy uniform cache `(optRand, M') ↦ R`
* `itLog`: all `(R, (pk, pkSl, M'))` triples issued on cache misses (matching the ITSR challenge log). -/
structure SlSignSt where
  log : List (List Byte)
  rnd : SlRndCache pr
  itLog : List (pr.Y × (pr.PkSeed × pr.Y × List Byte))

/-- Initial state of the post-PRF stateless signing oracle. -/
def SlSignSt.init : SlSignSt pr := ⟨[], ∅, []⟩

/-- A `qs`-query post-PRF stateless adversary receiving Stage-1 data `(d, sf)` and `(pk, pkSl)`,
with access to private coins and at most `qs` stateless signing queries. -/
structure PostPrfAdv (D E : Type) (qs : ℕ) where
  run : D → E → pr.PkSeed → pr.Y → OracleComp (SlAdvSpec pr) (Option (List Byte × Stateless.Sig pr))
  signBound : ∀ d sf pk pkSl, (run d sf pk pkSl).IsQueryBoundP IsSlSignQuery qs

/-- Parameterized post-PRF stateless signing handler: on query `m`, samples `optRand ← $ᵗ pr.Y`,
lazily draws uniform `R` cached per `(optRand, m)` (appending `(R, (pk, pkSl, m))` to `itLog` on
cache miss), signs `(m, R)` via `signFn`, and records `m` in `log`. -/
noncomputable def slSignImpl [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr) :
    QueryImpl (SlAdvSpec pr) (StateT (SlSignSt pr) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SlSignSt pr) ProbComp) +
  (fun m => do
    let optRand ← (monadLift ($ᵗ pr.Y) : StateT (SlSignSt pr) ProbComp pr.Y)
    let s ← get
    match s.rnd (optRand, m) with
    | some R =>
      set { s with log := s.log ++ [m] }
      return signFn m R
    | none =>
      let R ← (monadLift ($ᵗ pr.Y) : StateT (SlSignSt pr) ProbComp pr.Y)
      set ({
        log := s.log ++ [m]
        rnd := s.rnd.cacheQuery (optRand, m) R
        itLog := s.itLog ++ [(R, (pk, pkSl, m))]
      } : SlSignSt pr)
      return signFn m R)

private theorem slSignImpl_inl [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    (n : ℕ) (s : SlSignSt pr) :
    (slSignImpl pr pk pkSl signFn (.inl n)).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  change (StateT.lift (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))).run s = _
  rw [StateT.run_lift]
  rfl

private theorem slSignImpl_inr [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    (m : List Byte) (s : SlSignSt pr) :
    (slSignImpl pr pk pkSl signFn (.inr m)).run s = (do
      let optRand ← $ᵗ pr.Y
      match s.rnd (optRand, m) with
      | some R => pure (signFn m R, { s with log := s.log ++ [m] })
      | none =>
          let R ← $ᵗ pr.Y
          pure (signFn m R, {
            log := s.log ++ [m]
            rnd := s.rnd.cacheQuery (optRand, m) R
            itLog := s.itLog ++ [(R, (pk, pkSl, m))]
          })) := by
  change (StateT.lift ($ᵗ pr.Y) >>= fun optRand =>
    get >>= fun s' =>
      (match s'.rnd (optRand, m) with
       | some R => set { s' with log := s'.log ++ [m] } >>= fun _ => pure (signFn m R)
       | none => StateT.lift ($ᵗ pr.Y) >>= fun R =>
           set ({ log := s'.log ++ [m], rnd := s'.rnd.cacheQuery (optRand, m) R,
                  itLog := s'.itLog ++ [(R, (pk, pkSl, m))] } : SlSignSt pr) >>= fun _ =>
             pure (signFn m R))).run s = _
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind]
  refine bind_congr fun optRand => ?_
  cases s.rnd (optRand, m) with
  | some R => simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
  | none => simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind]

/-- Run `adv` against `slSignImpl` with signing callback `signFn`. -/
noncomputable def runPostPrf [DecidableEq pr.Y] [SampleableType pr.Y]
    {D E : Type} {qs : ℕ} (adv : PostPrfAdv pr D E qs)
    (d : D) (sf : E) (pk : pr.PkSeed) (pkSl : pr.Y)
    (signFn : List Byte → pr.Y → Stateless.Sig pr) :
    ProbComp (Option (List Byte × Stateless.Sig pr) × SlSignSt pr) :=
  (simulateQ (slSignImpl pr pk pkSl signFn) (adv.run d sf pk pkSl)).run (SlSignSt.init pr)

/-- **Post-PRF winning condition**: `adv` outputs `some (msg, sig)` with `msg ∉ log` and
`verifyInternal vp.sl pr.toSLHDSA msg sig ⟨pk, pkSl⟩ = true`. -/
def PostPrfWin [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (log : List (List Byte)) (out : Option (List Byte × Stateless.Sig pr)) : Prop :=
  match out with
  | none => False
  | some (msg, sig) =>
      msg ∉ log ∧
      SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA msg sig ⟨pk, pkSl⟩ = true

/-- **Post-PRF experiment** with Stage-1 hook `sfStage` and `qs`-query adversary `adv`. -/
noncomputable def postPrfExp [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [SampleableType pr.PkSeed] {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    ProbComp (pr.PkSeed × (SlSecAdrs vp → pr.Y) × Option (List Byte × Stateless.Sig pr) × SlSignSt pr) := do
  let pk ← $ᵗ pr.PkSeed
  let d ← sfStage.g₁
  let u ← $ᵗ (SlSecAdrs vp → pr.Y)
  let pkSl := slRootDet pr pk u
  let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl (slSignDet pr pk pkSl u)
  return (pk, u, res.1, res.2)

/-- Support invariant of `slSignImpl`: every entry `(R, (pk', pkSl', m))` in `itLog` (and every
cached key `(optRand, m)` in `rnd`) has `m ∈ log`, `pk' = pk`, `pkSl' = pkSl`, and every cached
entry `(optRand, m) ↦ R` already appears in `itLog`. -/
def SlSignInv (pk : pr.PkSeed) (pkSl : pr.Y) (s : SlSignSt pr) : Prop :=
  (∀ e ∈ s.itLog, e.2.1 = pk ∧ e.2.2.1 = pkSl ∧ e.2.2.2 ∈ s.log) ∧
  (∀ optRand m R, s.rnd (optRand, m) = some R → (R, (pk, pkSl, m)) ∈ s.itLog)

theorem slSignInv_init (pk : pr.PkSeed) (pkSl : pr.Y) : SlSignInv pr pk pkSl (SlSignSt.init pr) := by
  refine ⟨fun _ h => by simp [SlSignSt.init] at h, fun _ _ _ h => by simp [SlSignSt.init] at h⟩

theorem slSignInv_of_mem_support [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    {α : Type} (oa : OracleComp (SlAdvSpec pr) α) :
    ∀ s, SlSignInv pr pk pkSl s →
      ∀ r ∈ support ((simulateQ (slSignImpl pr pk pkSl signFn) oa).run s),
        SlSignInv pr pk pkSl r.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hs
  | query_bind t k ih =>
    intro s hs r hr
    rcases t with n | m
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slSignImpl_inl,
        bind_map_left, mem_support_bind_iff] at hr
      obtain ⟨u, _, hr⟩ := hr
      exact ih u s hs r hr
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slSignImpl_inr,
        bind_assoc, mem_support_bind_iff] at hr
      obtain ⟨optRand, _, hr⟩ := hr
      cases hlook : s.rnd (optRand, m) with
      | some R =>
        rw [hlook] at hr
        simp only [support_pure, Set.mem_singleton_iff, exists_eq_left] at hr
        refine ih (signFn m R) { s with log := s.log ++ [m] } ?_ r hr
        refine ⟨fun e he => ?_, fun o' m' R' h' => hs.2 o' m' R' h'⟩
        obtain ⟨h1, h2, h3⟩ := hs.1 e he
        exact ⟨h1, h2, List.mem_append_left _ h3⟩
      | none =>
        rw [hlook] at hr
        obtain ⟨⟨σ, s'⟩, h1, hr⟩ := hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h1
        obtain ⟨R, _, rfl, rfl⟩ := h1
        refine ih (signFn m R) _ ?_ r hr
        refine ⟨fun e he => ?_, fun o' m' R' h' => ?_⟩
        · rcases List.mem_append.1 he with he1 | he2
          · obtain ⟨h1, h2, h3⟩ := hs.1 e he1
            exact ⟨h1, h2, List.mem_append_left _ h3⟩
          · simp only [List.mem_singleton] at he2; subst he2
            exact ⟨rfl, rfl, List.mem_append_right _ (by simp)⟩
        · by_cases heq : (o', m') = (optRand, m)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            simp only [OracleSpec.QueryCache.cacheQuery_self, Option.some.injEq] at h'
            subst h'
            exact List.mem_append_right _ (by simp)
          · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ heq] at h'
            exact List.mem_append_left _ (hs.2 o' m' R' h')

end PostPrfGame

/-! ## 2. Exact Zero-Loss ITSR Reduction (`B_itsr`) -/

section ITSRReduction

/-- Deterministic digest map `MAP_{h,k,t}` mapping `SLHDSA.Bytes vp.sl.params.m` to a
`(BottomPosition, Fin k → Fin 2^a)` ITSR digest (`ShrincsSecurity.ITSR.Digest`). -/
def slMap (vp : ValidatedParams) :
    SLHDSA.Bytes vp.sl.params.m →
      ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a) :=
  fun dg =>
    let parts := splitDigest vp.sl.params dg
    (BottomPosition.ofDigestParts vp.sl parts,
      fun i => ⟨forsIdx vp.sl.params parts.md.toList i.val,
        by simpa [SLHDSA.Params.t] using forsIdx_lt vp.sl.params parts.md.toList i.val⟩)

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- The keyed hash `H_msg^sl : Y × (PkSeed × Y × List Byte) → Bytes m` for Definition 4.11 (ITSR). -/
def slHmsg : Notions.KeyedHash pr.Y (pr.PkSeed × pr.Y × List Byte) (SLHDSA.Bytes vp.sl.params.m) :=
  fun R x => pr.HmsgSl R x.1 x.2.1 x.2.2

/-- ITSR oracle specification matching `slHmsg` and `slMap`. -/
abbrev SlItsrSpec (pr : Primitives vp.params) :=
  unifSpec + Notions.ITSRChalSpec pr.Y (pr.PkSeed × pr.Y × List Byte)
    (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)

/-- Forward `SlAdvSpec pr` to `SlItsrSpec pr` with a local `SlRndCache`:
* private coins forward directly to `unifSpec` (0 ITSR queries);
* signing query `m` samples `optRand ← $ᵗ pr.Y`, reuses cached `R` on hit (0 ITSR queries),
  or queries the ITSR challenge oracle on `(pk, pkSl, m)` on miss (1 ITSR query) and caches `R`. -/
noncomputable def slToItsrImpl [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr) :
    QueryImpl (SlAdvSpec pr) (StateT (SlRndCache pr) (OracleComp (SlItsrSpec pr))) :=
  (fun n => StateT.lift (liftM ((SlItsrSpec pr).query (.inl n)) :
      OracleComp (SlItsrSpec pr) (unifSpec.Range n))) +
  (fun m => do
    let optRand ← StateT.lift (liftM ($ᵗ pr.Y) : OracleComp (SlItsrSpec pr) pr.Y)
    let rc ← (get : StateT (SlRndCache pr) (OracleComp (SlItsrSpec pr)) (SlRndCache pr))
    match rc (optRand, m) with
    | some R => return signFn m R
    | none =>
      let res ← StateT.lift (liftM ((SlItsrSpec pr).query (.inr (pk, pkSl, m))) :
        OracleComp (SlItsrSpec pr) (pr.Y × ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)))
      set (rc.cacheQuery (optRand, m) res.1)
      return signFn m res.1)

private theorem slToItsrImpl_inl [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    (n : ℕ) (rc : SlRndCache pr) :
    (slToItsrImpl pr pk pkSl signFn (.inl n)).run rc =
      (fun u => (u, rc)) <$> (liftM ((SlItsrSpec pr).query (.inl n)) :
        OracleComp (SlItsrSpec pr) (unifSpec.Range n)) := by
  change (StateT.lift (liftM ((SlItsrSpec pr).query (.inl n)) :
    OracleComp (SlItsrSpec pr) (unifSpec.Range n))).run rc = _
  rw [StateT.run_lift]
  rfl

private theorem slToItsrImpl_inr [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    (m : List Byte) (rc : SlRndCache pr) :
    (slToItsrImpl pr pk pkSl signFn (.inr m)).run rc = (do
      let optRand ← (liftM ($ᵗ pr.Y) : OracleComp (SlItsrSpec pr) pr.Y)
      match rc (optRand, m) with
      | some R => pure (signFn m R, rc)
      | none =>
          let res ← (liftM ((SlItsrSpec pr).query (.inr (pk, pkSl, m))) :
            OracleComp (SlItsrSpec pr)
              (pr.Y × ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)))
          pure (signFn m res.1, rc.cacheQuery (optRand, m) res.1)) := by
  change (StateT.lift (liftM ($ᵗ pr.Y) : OracleComp (SlItsrSpec pr) pr.Y) >>= fun optRand =>
    (get : StateT (SlRndCache pr) (OracleComp (SlItsrSpec pr)) (SlRndCache pr)) >>= fun rc' =>
      (match rc' (optRand, m) with
       | some R => pure (signFn m R)
       | none =>
           StateT.lift (liftM ((SlItsrSpec pr).query (.inr (pk, pkSl, m))) :
             OracleComp (SlItsrSpec pr)
               (pr.Y × ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a))) >>= fun res =>
             set (rc'.cacheQuery (optRand, m) res.1) >>= fun _ => pure (signFn m res.1))).run rc = _
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind]
  refine bind_congr fun optRand => ?_
  cases rc (optRand, m) with
  | some R => simp only [StateT.run_pure]
  | none => simp only [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind]

private theorem liftM_prob_itsr_bound {α : Type} (p : ProbComp α) :
    (liftM p : OracleComp (SlItsrSpec pr) α).IsQueryBoundP Notions.IsITSRChal 0 :=
  (isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
    rcases t with _ | _
    · exact absurd ht (by simp [Notions.IsITSRChal])
    · rfl

/-- Query-bound preservation: simulating a `q`-signing-query computation via `slToItsrImpl` makes
at most `q` ITSR challenge queries on every path. -/
theorem isQueryBoundP_slToItsr [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    {α : Type} (oa : OracleComp (SlAdvSpec pr) α) :
    ∀ (q : ℕ) (rc : SlRndCache pr),
      oa.IsQueryBoundP IsSlSignQuery q →
      ((simulateQ (slToItsrImpl pr pk pkSl signFn) oa).run rc).IsQueryBoundP Notions.IsITSRChal q := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q rc _
    simp only [simulateQ_pure, StateT.run_pure]
    trivial
  | query_bind t k ih =>
    intro q rc hq
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases t with n | m
    · have hstep : ∀ u, (k u).IsQueryBoundP IsSlSignQuery q := by
        simpa [IsSlSignQuery] using hq.2
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slToItsrImpl_inl,
        bind_map_left]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2
        ⟨Or.inl (by simp [Notions.IsITSRChal]), fun u => by
          simpa [Notions.IsITSRChal] using ih u q rc (hstep u)⟩
    · rcases q with _ | q
      · rcases hq.1 with h1 | h2
        · exact absurd trivial h1
        · omega
      · have hstep : ∀ σ, (k σ).IsQueryBoundP IsSlSignQuery q := by
          simpa [IsSlSignQuery] using hq.2
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slToItsrImpl_inr,
          bind_assoc]
        have hcont : ∀ optRand : pr.Y,
            ((match rc (optRand, m) with
              | some R => pure (signFn m R, rc)
              | none => do
                  let res ← (liftM ((SlItsrSpec pr).query (.inr (pk, pkSl, m))) :
                    OracleComp (SlItsrSpec pr)
                      (pr.Y × ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)))
                  pure (signFn m res.1, rc.cacheQuery (optRand, m) res.1)) >>=
              fun x => (simulateQ (slToItsrImpl pr pk pkSl signFn) (k x.1)).run x.2).IsQueryBoundP
              Notions.IsITSRChal (q + 1) := by
          intro optRand
          cases hlook : rc (optRand, m) with
          | some R =>
            simp only [pure_bind]
            exact (ih (signFn m R) q rc (hstep (signFn m R))).mono (Nat.le_succ q)
          | none =>
            simp only [bind_assoc, pure_bind]
            refine (isQueryBoundP_query_bind_iff _ _ _ (q + 1)).2
              ⟨Or.inr (Nat.succ_pos q), fun res => ?_⟩
            simpa [Notions.IsITSRChal] using
              ih (signFn m res.1) q (rc.cacheQuery (optRand, m) res.1) (hstep (signFn m res.1))
        exact (isQueryBoundP_bind (liftM_prob_itsr_bound pr ($ᵗ pr.Y))
          (fun optRand _ => hcont optRand)).mono (by omega)

/-- **The exact ITSR adversary `B_itsr`** (Main Paper Theorem 4.3 & Claim 4.16): samples
`(pk, d, u)`, simulates `adv` answering stateless signing queries via `slToItsrImpl` with
`slSignDet`, and outputs `(sig.randomness, (pk, pkSl, msg))` when `adv` outputs `some (msg, sig)`. -/
noncomputable def B_itsr [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [SampleableType pr.PkSeed] {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Notions.ITSRAdversary pr.Y (pr.PkSeed × pr.Y × List Byte)
      (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a) qs where
  run := do
    let pk ← (liftM ($ᵗ pr.PkSeed) : OracleComp (SlItsrSpec pr) pr.PkSeed)
    let d ← (liftM sfStage.g₁ : OracleComp (SlItsrSpec pr) D)
    let u ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y)) : OracleComp (SlItsrSpec pr) (SlSecAdrs vp → pr.Y))
    let pkSl := slRootDet pr pk u
    let (out, _) ← (simulateQ (slToItsrImpl pr pk pkSl (slSignDet pr pk pkSl u))
      (adv.run d (sfStage.sfDet d pk) pk pkSl)).run ∅
    match out with
    | none => return (default, (pk, pkSl, []))
    | some (msg, sig) => return (sig.randomness, (pk, pkSl, msg))
  chalBound := by
    refine (isQueryBoundP_bind (n := 0) (m := qs) (liftM_prob_itsr_bound pr _) fun pk _ =>
      (isQueryBoundP_bind (n := 0) (m := qs) (liftM_prob_itsr_bound pr _) fun d _ =>
        (isQueryBoundP_bind (n := 0) (m := qs) (liftM_prob_itsr_bound pr _) fun u _ =>
          (isQueryBoundP_bind (n := qs) (m := 0)
            (isQueryBoundP_slToItsr pr pk (slRootDet pr pk u) (slSignDet pr pk (slRootDet pr pk u) u)
              (adv.run d (sfStage.sfDet d pk) pk (slRootDet pr pk u)) qs ∅ (adv.signBound _ _ _ _))
            fun ⟨out, _⟩ _ => by
              rcases out with _ | ⟨msg, sig⟩ <;> exact isQueryBoundP_pure Notions.IsITSRChal _ 0).mono
            (by omega)).mono (by omega)).mono (by omega)).mono (by omega)

/-- Exact simulation equivalence between `itsrOracles` running `slToItsrImpl` and `slSignImpl`:
both produce the exact same `(out, itLog)` distribution! -/
theorem simulateQ_itsrOracles_slToItsr [DecidableEq pr.Y] [SampleableType pr.Y]
    (pk : pr.PkSeed) (pkSl : pr.Y) (signFn : List Byte → pr.Y → Stateless.Sig pr)
    {α : Type} (oa : OracleComp (SlAdvSpec pr) α) :
    ∀ (s : SlSignSt pr),
      (fun r => (r.1.1, r.2)) <$>
        (simulateQ (Notions.itsrOracles (slHmsg pr) (slMap vp))
          ((simulateQ (slToItsrImpl pr pk pkSl signFn) oa).run s.rnd)).run s.itLog =
      (fun r => (r.1, r.2.itLog)) <$>
        (simulateQ (slSignImpl pr pk pkSl signFn) oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s; simp
  | query_bind t k ih =>
    intro s
    rcases t with n | m
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slToItsrImpl_inl,
        slSignImpl_inl, bind_map_left, map_bind]
      have hcoin : (Notions.itsrOracles (slHmsg pr) (slMap vp) (.inl n)).run s.itLog =
          (fun u => (u, s.itLog)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp [Notions.itsrOracles, StateT.run_monadLift]
      rw [hcoin, bind_map_left]
      exact bind_congr fun u => ih u s
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slToItsrImpl_inr,
        slSignImpl_inr, bind_assoc, map_bind]
      have hunif : (simulateQ (Notions.itsrOracles (slHmsg pr) (slMap vp))
          (liftM ($ᵗ pr.Y) : OracleComp (SlItsrSpec pr) pr.Y)).run s.itLog =
          (fun x => (x, s.itLog)) <$> ($ᵗ pr.Y) :=
        Fxmss.simulateQ_add_liftM_run _ ($ᵗ pr.Y) s.itLog
      rw [hunif, bind_map_left]
      refine bind_congr fun optRand => ?_
      cases hlook : s.rnd (optRand, m) with
      | some R =>
        simp only [pure_bind, simulateQ_pure, StateT.run_pure]
        exact ih (signFn m R) { s with log := s.log ++ [m] }
      | none =>
        simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        have hch : (Notions.itsrOracles (slHmsg pr) (slMap vp) (.inr (pk, pkSl, m))).run s.itLog =
            (fun R => ((R, Notions.itsrG (slHmsg pr) (slMap vp) (R, (pk, pkSl, m))),
              s.itLog ++ [(R, (pk, pkSl, m))])) <$> ($ᵗ pr.Y) := by
          simp [Notions.itsrOracles, Notions.itsrOracle, StateT.run_monadLift, map_eq_bind_pure_comp]
        rw [hch, bind_map_left]
        refine bind_congr fun R => ?_
        exact ih (signFn m R) {
          log := s.log ++ [m]
          rnd := s.rnd.cacheQuery (optRand, m) R
          itLog := s.itLog ++ [(R, (pk, pkSl, m))]
        }

/-- **ITSR event**: `PostPrfWin` holds AND the forgery's FORS digest is covered by the signing queries. -/
def EvItsr [DecidableEq pr.Y] [Inhabited pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  let pkSl := slRootDet pr pk u
  PostPrfWin pr pk pkSl st.log out ∧
  match out with
  | none => False
  | some (msg, sig) =>
      ITSR.Covered (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
        (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, pkSl, msg)))

/-- **ITSR bound (zero birthday loss)**: `Pr[EvItsr] ≤ Succ^{ITSR}_{H_msg^sl, qs}(B_itsr)`. -/
theorem pr_EvItsr_le [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvItsr pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      Notions.itsrSucc (slHmsg pr) (slMap vp) (B_itsr pr sfStage adv) := by
  unfold Notions.itsrSucc Notions.itsrExperiment postPrfExp
  rw [prEvent_eq_evalDist_bind]
  -- Unpack `B_itsr`'s three `liftM` draws via `Fxmss.simulateQ_add_liftM_bind_run`
  have hrun_b : (do
      let x ← (simulateQ (Notions.itsrOracles (slHmsg pr) (slMap vp)) (B_itsr pr sfStage adv).run).run []
      return decide (Notions.ITSRWins (slHmsg pr) (slMap vp) x.2 x.1)) =
      (do
        let pk ← $ᵗ pr.PkSeed
        let d ← sfStage.g₁
        let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        let pkSl := slRootDet pr pk u
        let r ← runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl (slSignDet pr pk pkSl u)
        let x := match r.1 with
          | none => (default, (pk, pkSl, []))
          | some (msg, sig) => (sig.randomness, (pk, pkSl, msg))
        return decide (Notions.ITSRWins (slHmsg pr) (slMap vp) r.2.itLog x)) := by
    simp only [B_itsr]
    rw [show Notions.itsrOracles (slHmsg pr) (slMap vp) =
        Fxmss.unifFwd _ + Notions.itsrOracle (slHmsg pr) (slMap vp) from rfl]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine bind_congr fun pk => ?_
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine bind_congr fun d => ?_
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine bind_congr fun u => ?_
    rw [← show Notions.itsrOracles (slHmsg pr) (slMap vp) =
        Fxmss.unifFwd _ + Notions.itsrOracle (slHmsg pr) (slMap vp) from rfl]
    have hsim := simulateQ_itsrOracles_slToItsr pr pk (slRootDet pr pk u)
      (slSignDet pr pk (slRootDet pr pk u) u) (adv.run d (sfStage.sfDet d pk) pk (slRootDet pr pk u))
      (SlSignSt.init pr)
    simp only [SlSignSt.init] at hsim
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hconv : ∀ (m : ProbComp ((Option (List Byte × Stateless.Sig pr) × SlRndCache pr) ×
        List (pr.Y × pr.PkSeed × pr.Y × List Byte))),
        (m >>= fun z => (simulateQ (Notions.itsrOracles (slHmsg pr) (slMap vp))
          (match z.1.1 with
           | none => pure (default, (pk, slRootDet pr pk u, []))
           | some (msg, sig) => pure (sig.randomness, (pk, slRootDet pr pk u, msg)))).run z.2 >>=
          fun x => pure (decide (Notions.ITSRWins (slHmsg pr) (slMap vp) x.2 x.1))) =
        ((fun r => (r.1.1, r.2)) <$> m) >>= fun y =>
          pure (decide (Notions.ITSRWins (slHmsg pr) (slMap vp) y.2
            (match y.1 with
             | none => (default, (pk, slRootDet pr pk u, []))
             | some (msg, sig) => (sig.randomness, (pk, slRootDet pr pk u, msg))))) := by
      intro m
      simp only [bind_map_left]
      refine bind_congr fun z => ?_
      rcases z.1.1 with _ | ⟨msg, sig⟩ <;> simp
    rw [hconv, hsim]
    simp only [runPostPrf, SlSignSt.init, bind_map_left]
  -- Apply `hrun_b` to RHS and compare pointwise on support of `runPostPrf`!
  have hlhs : 𝒟[(do
      let pk ← $ᵗ pr.PkSeed
      let d ← sfStage.g₁
      let u ← $ᵗ (SlSecAdrs vp → pr.Y)
      let pkSl := slRootDet pr pk u
      let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl (slSignDet pr pk pkSl u)
      pure (pk, u, res.1, res.2)) >>= fun z => pure (decide (EvItsr pr z.1 z.2.1 z.2.2.1 z.2.2.2))] {true} =
      𝒟[do
        let pk ← $ᵗ pr.PkSeed
        let d ← sfStage.g₁
        let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk (slRootDet pr pk u)
          (slSignDet pr pk (slRootDet pr pk u) u)
        return decide (EvItsr pr pk u res.1 res.2)] {true} := by
    simp only [bind_assoc, pure_bind]
  rw [hlhs, hrun_b]
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun pk _ => ?_
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun d _ => ?_
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun u _ => ?_
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun res hres => ?_
  have hinv := slSignInv_of_mem_support pr pk (slRootDet pr pk u)
    (slSignDet pr pk (slRootDet pr pk u) u) _ (SlSignSt.init pr) (slSignInv_init pr _ _) res hres
  by_cases hev : EvItsr pr pk u res.1 res.2
  · rcases res with ⟨out, st⟩
    rcases out with _ | ⟨msg, sig⟩
    · exact hev.2.elim
    · have hev' := hev
      dsimp only [EvItsr] at hev'
      obtain ⟨⟨hfresh, _⟩, hcov⟩ := hev'
      have hnotmem : (sig.randomness, (pk, slRootDet pr pk u, msg)) ∉ st.itLog := fun hm =>
        hfresh (hinv.1 _ hm).2.2
      have hcov' : ITSR.Covered (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
          (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg))) := by
        convert hcov
      have hwin : Notions.ITSRWins (slHmsg pr) (slMap vp) st.itLog
          (sig.randomness, (pk, slRootDet pr pk u, msg)) := by
        refine ⟨hnotmem, ?_⟩
        have hsub := (Notions.digestSet_subset_iff_covered
          (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
          (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg)))).2 hcov'
        intro x hx
        obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.1 (hsub hx)
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
        exact Finset.mem_biUnion.2 ⟨y, hy, hxd⟩
      simp [hwin, hev]
  · simp [hev]

end ITSRReduction

/-! ## 3. Role Target Predicates, Honest Inputs, and 8-Way Witness Dispatch -/

section WitnessDispatch

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- XMSS internal hash addresses (`type = 2`, `word2 ≠ 0`), member `.H`, count `q₄`. -/
def isXmssH (a : Adrs) : Bool := a.type == 2 && a.word2 != 0

/-- FORS internal hash addresses (`type = 3`, `word2 ≠ 0`), member `.H`, count `q₇`. -/
def isForsH (a : Adrs) : Bool := a.type == 3 && a.word2 != 0

theorem countP_slTreeAddresses_isXmssH :
    (slTreeAddresses vp).countP isXmssH = (xmssNodeAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isXmssH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isXmssH a = false := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isXmssH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isXmssH a = false := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isXmssH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isXmssH a = true := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha
    obtain ⟨⟨_, zi⟩, hmem, rfl⟩ := ha
    have hz := perfectInternalCoords_height_pos (List.mem_product.1 hmem).2
    simp only [isXmssH, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    exact ⟨rfl, by change zi.1 ≠ 0; omega⟩
  rw [slTreeAddresses]; simp only [List.countP_append]
  rw [List.countP_eq_zero.2 (fun a ha => by rw [h1 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h2 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h3 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h4 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h5 a ha]; decide),
    List.countP_eq_length.2 h6]; omega

theorem countP_slTreeAddresses_isForsH :
    (slTreeAddresses vp).countP isForsH = (forsTreeAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isForsH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isForsH a = true := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha
    obtain ⟨⟨_, zi⟩, hmem, rfl⟩ := ha
    have hz := perfectInternalCoords_height_pos (List.mem_product.1 hmem).2
    simp only [isForsH, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    exact ⟨rfl, by change zi.1 ≠ 0; omega⟩
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isForsH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isForsH a = false := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isForsH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isForsH a = false := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  rw [slTreeAddresses]; simp only [List.countP_append]
  rw [List.countP_eq_zero.2 (fun a ha => by rw [h1 a ha]; decide),
    List.countP_eq_length.2 h2,
    List.countP_eq_zero.2 (fun a ha => by rw [h3 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h4 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h5 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h6 a ha]; decide)]; omega

theorem evalNodeInput_isXmssH [Inhabited pr.Y] {a : Adrs} (ht : isXmssH a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.H, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isXmssH, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at ht
  obtain ⟨rfl, h2⟩ := ht
  by_cases h2' : w2 = 1
  · subst h2'; exact ⟨_, rfl⟩
  · simp only [evalNodeInput, h2, h2', ↓reduceIte]; exact ⟨_, rfl⟩

theorem evalNodeInput_isForsH [Inhabited pr.Y] {a : Adrs} (ht : isForsH a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.H, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isForsH, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at ht
  obtain ⟨rfl, h2⟩ := ht
  simp only [evalNodeInput, h2, ↓reduceIte]; exact ⟨_, rfl⟩

/-! ### Exact `honestInput` identification for all 6 witness roles -/

variable [Inhabited pr.Y]

theorem honestInput_forsRoot (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestInput pr pk u (forsPkAdrs b) =
      some ⟨.thK, forsHonestRoots (prEager pr) u pk b⟩ := by
  unfold honestInput evalNodeInput
  have hty : (forsPkAdrs b).type = 4 := rfl
  simp only [hty]
  refine congrArg (fun v => some (⟨.thK, v⟩ : Σ i, pr.MemberMsg i)) ?_
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn, Option.getD_some]
  have heq : forsNodeAdrs (forsPkAdrs b) vp.params.a i = forsNodeAdrs b vp.sl.params.a i := rfl
  have hroot : (forsHonestRoots (prEager pr) u pk b)[i] =
      SLHDSA.forsRoot (prEager pr) u pk b i :=
    forsHonestRoots_getElem (prims := prEager pr) u pk b (i := i) hi
  rw [heq, honestVal_eq_forsNode]
  exact (hroot.trans (SLHDSA.forsRoot_eq_merkleRoot (prEager pr) u pk b i)).symm

theorem honestInput_forsH (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs)
    {z : ℕ} (hz : 0 < z) (t : ℕ) :
    honestInput pr pk u (forsNodeAdrs b z t) =
      some ⟨.H, forsHonestChildren (prEager pr) u pk b z t⟩ := by
  unfold honestInput evalNodeInput
  have hty : (forsNodeAdrs b z t).type = 3 := rfl
  have hw2 : (forsNodeAdrs b z t).word2 = z := rfl
  have hw3 : (forsNodeAdrs b z t).word3 = t := rfl
  have hz0 : z ≠ 0 := Nat.ne_of_gt hz
  simp only [hty, hw2, hw3, hz0, ↓reduceIte, Option.getD_some, Option.some.injEq]
  rw [forsHonestChildren_eq_honestVal]
  rfl

theorem honestInput_forsLeaf (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (t : ℕ) :
    honestInput pr pk u (forsNodeAdrs b 0 t) =
      some ⟨.F, slSecOf pr u (forsSkAdrs b t)⟩ := rfl

theorem honestInput_xmssH (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs)
    {z : ℕ} (hz : 0 < z) (t : ℕ) :
    honestInput pr pk u (xmssNodeAdrs b z t) =
      some ⟨.H, xmssHonestChildren (prEager pr) u pk b z t⟩ := by
  unfold honestInput evalNodeInput
  have hty : (xmssNodeAdrs b z t).type = 2 := rfl
  have hw2 : (xmssNodeAdrs b z t).word2 = z := rfl
  have hw3 : (xmssNodeAdrs b z t).word3 = t := rfl
  have hz0 : z ≠ 0 := Nat.ne_of_gt hz
  simp only [hty, hw2, hw3, hz0, ↓reduceIte, Option.getD_some]
  rw [xmssHonestChildren_eq_honestVal]
  by_cases hz1 : z = 1
  · subst hz1; simp only [↓reduceIte, Nat.sub_self]; rfl
  · simp only [hz1, ↓reduceIte]
    have hzm : z - 1 ≠ 0 := by omega
    rcases hk : z - 1 with _ | k
    · exact absurd hk hzm
    · rfl

theorem honestInput_wotsPk (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestInput pr pk u (wotsPkAdrs b) =
      some ⟨.thLsl, (wotsPkGenTops (prEager pr) u pk b).cast (Params.lsl_eq_len vp.valid).symm⟩ := by
  unfold honestInput evalNodeInput
  have hty : (wotsPkAdrs b).type = 1 := rfl
  simp only [hty]
  refine congrArg (fun v => some (⟨.thLsl, v⟩ : Σ i, pr.MemberMsg i)) ?_
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn, Vector.getElem_cast, Option.getD_some, wotsPkGenTops_eq_ofFn]
  have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
  have hsub : vp.params.w - 2 + 1 = vp.sl.params.w - 1 := by
    change vp.params.w - 2 + 1 = vp.params.w - 1; omega
  have heq : (wotsChainAdrs (wotsPkAdrs b) i).setHashAddress (vp.params.w - 2) =
      (wotsChainAdrs b i).setHashAddress (vp.params.w - 2) := rfl
  rw [heq, honestVal_eq_wotsChain, hsub]

theorem honestInput_wotsStep (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs)
    (c : Fin vp.sl.params.len) (hMsg : pr.Y) (step : ℕ)
    (hge : chainStepsCore (prEager pr).core hMsg c.val ≤ step) :
    honestInput pr pk u ((wotsChainAdrs b c.val).setHashAddress step) =
      some ⟨.F, chain (prEager pr) pk (wotsChainAdrs b c.val)
        (wotsSign (prEager pr) hMsg u pk b)[c.val]
        (chainStepsCore (prEager pr).core hMsg c.val)
        (step - chainStepsCore (prEager pr).core hMsg c.val)⟩ := by
  have hcomp : chain (prEager pr) pk (wotsChainAdrs b c.val)
        (wotsSign (prEager pr) hMsg u pk b)[c.val]
        (chainStepsCore (prEager pr).core hMsg c.val)
        (step - chainStepsCore (prEager pr).core hMsg c.val) =
      chain (prEager pr) pk (wotsChainAdrs b c.val)
        (slSecOf pr u (wotsSkAdrs b c.val)) 0 step := by
    rw [wotsSign_eq_ofFn, Vector.getElem_ofFn]
    have hch := chain_compose (prEager pr) pk (wotsChainAdrs b c.val)
      (slSecOf pr u (wotsSkAdrs b c.val)) 0 (chainStepsCore (prEager pr).core hMsg c.val)
      (step - chainStepsCore (prEager pr).core hMsg c.val)
    simpa [Nat.zero_add, Nat.add_sub_of_le hge] using hch
  rw [hcomp]
  unfold honestInput evalNodeInput
  have hty : ((wotsChainAdrs b c.val).setHashAddress step).type = 0 := rfl
  have hw2 : ((wotsChainAdrs b c.val).setHashAddress step).word2 = c.val := rfl
  have hw3 : ((wotsChainAdrs b c.val).setHashAddress step).word3 = step := rfl
  simp only [hty, hw2, hw3, Option.some.injEq]
  rcases step with _ | k
  · simp only [↓reduceIte, chain_zero]; rfl
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      Option.getD_some]
    have hset : ((wotsChainAdrs b c.val).setHashAddress (k + 1)).setHashAddress k =
        (wotsChainAdrs b c.val).setHashAddress k := rfl
    rw [hset, honestVal_eq_wotsChain]

/-! ### Canonical uncovered FORS tree selection and 8-way dispatch -/

/-- Canonical first uncovered FORS tree index (or `⟨0, k_pos⟩` when covered). -/
noncomputable def findUncoveredTree (G : Finset (ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)))
    (u : ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)) :
    Fin vp.sl.params.k :=
  match (List.finRange vp.sl.params.k).find? (fun i =>
      !decide (∃ v ∈ G, v.1 = u.1 ∧ v.2 i = u.2 i)) with
  | some i => i
  | none => ⟨0, vp.valid.k_pos⟩

/-- Whenever `¬ ITSR.Covered G u`, `findUncoveredTree G u` is genuinely uncovered by `G`. -/
theorem findUncoveredTree_uncovered
    (G : Finset (ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a)))
    (u : ITSR.Digest (BottomPosition vp.sl) vp.sl.params.k (2 ^ vp.sl.params.a))
    (hnc : ¬ ITSR.Covered G u) :
    ∀ v ∈ G, v.1 = u.1 → v.2 (findUncoveredTree G u) ≠ u.2 (findUncoveredTree G u) := by
  unfold findUncoveredTree
  cases hf : (List.finRange vp.sl.params.k).find? (fun i =>
      !decide (∃ v ∈ G, v.1 = u.1 ∧ v.2 i = u.2 i)) with
  | some i =>
    have hsat := List.find?_some hf
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and] at hsat
    intro v hv h1 h2
    exact hsat v hv h1 h2
  | none =>
    exfalso; apply hnc; intro i
    have hnone := List.find?_eq_none.1 hf i (List.mem_finRange i)
    simp only [Bool.not_eq_true', Bool.not_eq_false, decide_eq_true_eq] at hnone
    obtain ⟨v, hv, h1, h2⟩ := hnone
    exact Finset.mem_image.2 ⟨v, Finset.mem_filter.2 ⟨hv, h1⟩, h2⟩

/-- Target FORS tree chosen for a given `(pk, pkSl, msg, sig, itLog)`. -/
noncomputable def chosenForsTree (pk : pr.PkSeed) (pkSl : pr.Y)
    (itLog : List (pr.Y × (pr.PkSeed × pr.Y × List Byte)))
    (msg : List Byte) (sig : Stateless.Sig pr) : Fin vp.sl.params.k :=
  findUncoveredTree
    (itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
    (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, pkSl, msg)))

/-- Exposed FORS per-tree collision finder (mirroring `SLHDSA.Security.findForsTreeCollision`). -/
noncomputable def slFindForsTreeCollision [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (i : Fin vp.sl.params.k) :
    Option (ForsWitness vp.sl.params (prEager pr)) :=
  let idx := forsSigLeafIndex vp.sl.params md i.val
  let y := (prEager pr).F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
  if forsLeaf (prEager pr) u pk adrs idx = y then none
  else
    (PerfectMerkleTree.findCollision (forsLeaf (prEager pr) u pk adrs)
      (forsNodeHash (prEager pr) pk adrs) idx y (sig[i.val]).auth.toList).map
      fun w => .hCollision i w.1 w.2.2

/-- Exposed FORS witness extractor (mirroring `SLHDSA.Security.findForsWitness`): depends on `u`
only through `forsHonestRoots` and `forsLeaf`, and honors `target` on the `.fPreimage` arm. -/
noncomputable def slFindForsWitness [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (target : Fin vp.sl.params.k) :
    ForsWitness vp.sl.params (prEager pr) :=
  if forsRecoveredRoots (prEager pr) sig md pk adrs = forsHonestRoots (prEager pr) u pk adrs then
    ((List.finRange vp.sl.params.k).findSome?
      (slFindForsTreeCollision pr sig md u pk adrs)).getD
      (.fPreimage target (sig[target.val]).sk)
  else .tlCollision (forsRecoveredRoots (prEager pr) sig md pk adrs)

private theorem slForsRecoveredRoot_climb
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (i : Fin vp.sl.params.k)
    (hroot : (forsRecoveredRoots (prEager pr) sig md pk adrs)[i.val] =
      (forsHonestRoots (prEager pr) u pk adrs)[i.val]) :
    PerfectMerkleTree.climb (forsNodeHash (prEager pr) pk adrs)
        (forsSigLeafIndex vp.sl.params md i.val)
        ((prEager pr).F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex vp.sl.params md i.val)) (sig[i.val]).sk)
        (sig[i.val]).auth.toList =
      PerfectMerkleTree.merkleRoot (forsLeaf (prEager pr) u pk adrs)
        (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
        (forsSigLeafIndex vp.sl.params md i.val / 2 ^ vp.sl.params.a) := by
  rw [forsSigLeafIndex_div_pow_a vp.sl.params md i.val]
  rw [forsRecoveredRoots_getElem, forsHonestRoots_getElem, SLHDSA.forsRoot_eq_merkleRoot] at hroot
  exact hroot

private theorem slFindForsTreeCollision_sound [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (i : Fin vp.sl.params.k)
    (hroot : (forsRecoveredRoots (prEager pr) sig md pk adrs)[i.val] =
      (forsHonestRoots (prEager pr) u pk adrs)[i.val])
    {w : ForsWitness vp.sl.params (prEager pr)}
    (hw : slFindForsTreeCollision pr sig md u pk adrs i = some w) :
    w.Valid u pk adrs md := by
  unfold slFindForsTreeCollision at hw
  dsimp only at hw
  split at hw
  · exact absurd hw (by simp)
  · rename_i hleaf
    rw [Option.map_eq_some_iff] at hw
    obtain ⟨u', hu', rfl⟩ := hw
    have hlen : (sig[i.val]).auth.toList.length = vp.sl.params.a := by simp
    have hclimb := slForsRecoveredRoot_climb pr sig md u pk adrs i hroot
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (forsLeaf (prEager pr) u pk adrs) (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
      (forsSigLeafIndex vp.sl.params md i.val) _ _ hlen hclimb hleaf
    rw [hor, Option.some.injEq] at hu'
    subst hu'
    obtain ⟨hzpos, hzle, hne, hcoll⟩ := PerfectMerkleTree.findCollision_sound
      (forsLeaf (prEager pr) u pk adrs) (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
      (forsSigLeafIndex vp.sl.params md i.val) _ _ hlen z _ c hor
    rw [ForsWitness.valid_hCollision]
    refine ⟨hzpos, hzle, ?_, ?_⟩
    · rw [forsHonestChildren_eq]; exact hne
    · rw [forsHonestChildren_eq]
      simpa only [SLHDSA.forsNodeHash_eq_h, PerfectMerkleTree.honestChildren] using hcoll

private theorem slFindForsWitness_sound [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (target : Fin vp.sl.params.k)
    (hpk : forsPkFromSig (prEager pr) sig md pk adrs = forsPkGen (prEager pr) u pk adrs) :
    (slFindForsWitness pr sig md u pk adrs target).Valid u pk adrs md := by
  unfold slFindForsWitness
  split
  · rename_i hroots
    rcases hfind : (List.finRange vp.sl.params.k).findSome?
        (slFindForsTreeCollision pr sig md u pk adrs) with _ | w
    · rw [Option.getD_none, ForsWitness.valid_fPreimage]
      rw [List.findSome?_eq_none_iff] at hfind
      have hnone := hfind target (List.mem_finRange target)
      have hleaf : forsLeaf (prEager pr) u pk adrs (forsSigLeafIndex vp.sl.params md target.val) =
          (prEager pr).F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex vp.sl.params md target.val))
            (sig[target.val]).sk := by
        by_contra hne
        have hlen : (sig[target.val]).auth.toList.length = vp.sl.params.a := by simp
        have hclimb := slForsRecoveredRoot_climb pr sig md u pk adrs target (by rw [hroots])
        obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
          (forsLeaf (prEager pr) u pk adrs) (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
          (forsSigLeafIndex vp.sl.params md target.val) _ _ hlen hclimb hne
        unfold slFindForsTreeCollision at hnone
        simp only [hne, ite_false, hor, Option.map_some] at hnone
        cases hnone
      exact forsLeafPreimage (prEager pr) u pk adrs _ _ hleaf
    · rw [Option.getD_some]
      obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hfind
      exact slFindForsTreeCollision_sound pr sig md u pk adrs i (by rw [hroots]) hi
  · rename_i hroots
    rw [ForsWitness.valid_tlCollision]
    exact ⟨hroots, forsRootsBinding (prEager pr) sig md u pk adrs hpk⟩

/-- Witness extracted from `(pk, u, out, st)` when `out = some (msg, sig)`:
uses `slFindForsWitness` on the FORS arm and VCVio's `findWitness` on the hypertree arm. -/
noncomputable def extractedWitness [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Witness vp.sl (prEager pr)) :=
  match out with
  | none => none
  | some (msg, sig) =>
      let pkSl := slRootDet pr pk u
      let parts := schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, pkSl⟩
      let target := chosenForsTree pr pk pkSl st.itLog msg sig
      if forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
          forsPkGen (prEager pr) u pk parts.forsAdrs then
        some (.fors (slFindForsWitness pr (toEagerSig pr sig).fors parts.md.toList u pk
          parts.forsAdrs target))
      else
        findWitness (vp := vp.sl) (prims := prEager pr) u ⟨pk, pkSl⟩ msg (toEagerSig pr sig) target

private theorem extractedWitness_sound [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (sig : Stateless.Sig pr) (st : SlSignSt pr)
    {w : Witness vp.sl (prEager pr)}
    (hw : extractedWitness pr pk u (some (msg, sig)) st = some w) :
    w.Valid u ⟨pk, slRootDet pr pk u⟩ msg (toEagerSig pr sig) := by
  unfold extractedWitness at hw
  dsimp only at hw
  split at hw
  · rename_i hfp
    simp only [Option.some.injEq] at hw
    subst hw
    rw [Witness.valid_fors]
    exact slFindForsWitness_sound pr _ _ u pk _ _ hfp
  · exact findWitness_sound (vp := vp.sl) (prims := prEager pr) u ⟨pk, slRootDet pr pk u⟩
      msg (toEagerSig pr sig) (chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig) hw

private theorem extractedWitness_eq_hypertree_iff [DecidableEq pr.Y] (pk : pr.PkSeed)
    (u : SlSecAdrs vp → pr.Y) (msg : List Byte) (sig : Stateless.Sig pr) (st : SlSignSt pr)
    (hw' : HypertreeWitness vp.sl (prEager pr) vp.sl.params.d) :
    extractedWitness pr pk u (some (msg, sig)) st = some (.hypertree hw') ↔
      findWitness (vp := vp.sl) (prims := prEager pr) u ⟨pk, slRootDet pr pk u⟩ msg
        (toEagerSig pr sig) (chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig) =
        some (.hypertree hw') := by
  unfold extractedWitness; dsimp only
  split_ifs with hfp
  · rw [findWitness_eq_fors_of_pk u ⟨pk, slRootDet pr pk u⟩ msg (toEagerSig pr sig) _ hfp]
    simp
  · rfl

/-- The 7 non-ITSR witness events on `(pk, u, out, st)`:
1. `EvTcrThK`: FORS `Th_k` collision (`q₅`)
2. `EvTcrHFors`: FORS internal `H` collision (`q₇`)
3. `EvForsPre`: FORS leaf `F` preimage (`q₈`, with `¬ Covered`)
4. `EvTcrHXmss`: XMSS internal `H` collision (`q₄`)
5. `EvTcrThLsl`: WOTS+ `Th_lsl` collision (`q₆`)
6. `EvTcrFWots`: WOTS+ chain `F` collision (`q₃`)
7. `EvPreFWots`: WOTS+ chain `F` preimage (`q₂`). -/
def EvTcrThK [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ∃ rec, extractedWitness pr pk u out st = some (.fors (.tlCollision rec))

def EvTcrHFors [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ∃ i z c, extractedWitness pr pk u out st = some (.fors (.hCollision i z c))

def EvForsPre [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ¬ EvItsr pr pk u out st ∧
  ∃ i val, extractedWitness pr pk u out st = some (.fors (.fPreimage i val))

def EvTcrHXmss [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ∃ ℓ z c, extractedWitness pr pk u out st = some (.hypertree ⟨ℓ, .hCollision z c⟩)

def EvTcrThLsl [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ∃ ℓ rec, extractedWitness pr pk u out st = some (.hypertree ⟨ℓ, .wots (.tlCollision rec)⟩)

def EvTcrFWots [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ∃ ℓ c step val, extractedWitness pr pk u out st = some (.hypertree ⟨ℓ, .wots (.fCollision c step val)⟩)

def EvPreFWots [DecidableEq pr.Y] (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  PostPrfWin pr pk (slRootDet pr pk u) st.log out ∧
  ∃ ℓ c step val, extractedWitness pr pk u out st = some (.hypertree ⟨ℓ, .wots (.fPreimage c step val)⟩)

/-- **Deterministic 8-way completeness**: under `hinj : Function.Injective pr.yToBytes`, every
post-PRF winning forgery falls into at least one of the 8 events (`EvItsr`, `EvTcrThK`,
`EvTcrHFors`, `EvForsPre`, `EvTcrHXmss`, `EvTcrThLsl`, `EvTcrFWots`, `EvPreFWots`). -/
theorem postPrfWin_cases [DecidableEq pr.Y] (hinj : Function.Injective pr.yToBytes)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr)
    (hwin : PostPrfWin pr pk (slRootDet pr pk u) st.log out) :
    EvItsr pr pk u out st ∨
    EvTcrThK pr pk u out st ∨
    EvTcrHFors pr pk u out st ∨
    EvForsPre pr pk u out st ∨
    EvTcrHXmss pr pk u out st ∨
    EvTcrThLsl pr pk u out st ∨
    EvTcrFWots pr pk u out st ∨
    EvPreFWots pr pk u out st := by
  by_cases hitsr : EvItsr pr pk u out st
  · exact Or.inl hitsr
  · rcases out with _ | ⟨msg, sig⟩
    · exact hwin.elim
    · have hver : SLHDSA.GeneralScheme.verifyInternal vp.sl (prEager pr) msg (toEagerSig pr sig)
          ⟨pk, SLHDSA.GeneralHypertree.root vp.sl (prEager pr) u pk⟩ = true := by
        rw [← slRootDet_eq_prEager_root, verifyInternal_prEager_eq]
        exact hwin.2
      have hisSome := findWitness_isSome (vp := vp.sl) (prims := prEager pr)
        (prEager_byteLaws pr hinj) u pk msg (toEagerSig pr sig)
        (chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig) hver
      rw [← slRootDet_eq_prEager_root] at hisSome
      have hexSome : (extractedWitness pr pk u (some (msg, sig)) st).isSome = true := by
        unfold extractedWitness; dsimp only
        split_ifs
        · rfl
        · exact hisSome
      obtain ⟨w, hex⟩ := Option.isSome_iff_exists.1 hexSome
      cases w with
      | fors fw =>
        cases fw with
        | tlCollision rec => exact Or.inr (Or.inl ⟨hwin, rec, hex⟩)
        | hCollision i z c => exact Or.inr (Or.inr (Or.inl ⟨hwin, i, z, c, hex⟩))
        | fPreimage i val => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, hitsr, i, val, hex⟩)))
      | hypertree hw' =>
        rcases hw' with ⟨ℓ, xw⟩
        cases xw with
        | hCollision z c => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, ℓ, z, c, hex⟩))))
        | wots ww =>
          cases ww with
          | tlCollision rec =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, ℓ, rec, hex⟩)))))
          | fCollision c step val =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hwin, ℓ, c, step, val, hex⟩))))))
          | fPreimage c step val =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hwin, ℓ, c, step, val, hex⟩))))))

end WitnessDispatch

/-! ## 4. Generic Routed Stage-1 Collection Reductions (`SM-TCR` and `SM-DSPR`) -/

section RoutedReductions

variable {vp : ValidatedParams} (pr : Primitives vp.params)
  [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed]

/-- Routed Stage-1 `SM-TCR` callback: routes `isTarget` tweaks of member `mem` to the `SM-TCR`
challenge oracle and all other tweaks to `O_coll`. -/
def routedTcrCall (mem : Primitives.Member) (isTarget : Adrs → Bool) (p : ℕ) :
    (i : Primitives.Member) → Adrs → pr.MemberMsg i →
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p)) pr.Y :=
  fun i a msg =>
    let spec := Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p)
    if h : isTarget a = true ∧ i = mem then do
      let y ← (liftM (spec.query (.inr (.inl (a, h.2 ▸ msg)))) : OracleComp spec (Option pr.Y))
      return y.getD default
    else do
      let y ← (liftM (spec.query (.inr (.inr ⟨some i, a, msg⟩))) : OracleComp spec (Option pr.Y))
      return y.getD default

/-- Pure `O_coll` callback for Stage-1 stateful precomputation in `SM-TCR`. -/
def sfTcrCall (mem : Primitives.Member) (p : ℕ) :
    (i : Primitives.Member) → Adrs → pr.MemberMsg i →
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p)) pr.Y :=
  fun i a msg =>
    let spec := Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p)
    do
      let y ← (liftM (spec.query (.inr (.inr ⟨some i, a, msg⟩))) : OracleComp spec (Option pr.Y))
      return y.getD default

/-- **Generic routed `SM-TCR` reduction** for a stateless role `(mem, isTarget, p)`:
* **Stage 1:** samples `d ← sfStage.g₁`, runs `sfStage.sfRun` via `O_coll`, samples `u ← $ᵗ _`,
  and runs `slVirtualTreeM` with `routedTcrCall` wrapped in `recordTcrImpl` (precomputing `(pkSl, tbl)`
  and recording every accepted challenge `(a, msg)` in `savedQ`).
* **Stage 2:** simulates `adv` with `slSignTable` (ZERO `Th_λ` evaluations!), then calls `extract`
  to pick a `(targetIdx, collidingMsg)` pair. -/
noncomputable def routedTcrAdv {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs)
    (mem : Primitives.Member) [DecidableEq (pr.MemberMsg mem)]
    (isTarget : Adrs → Bool) (p : ℕ)
    (extract : pr.PkSeed → (SlSecAdrs vp → pr.Y) → List (Adrs × pr.MemberMsg mem) →
      Option (List Byte × Stateless.Sig pr) → SlSignSt pr → ℕ × pr.MemberMsg mem) :
    SM_DT_TCR_Adversary (Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p) where
  State := D × E × (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y)) ×
    List (Adrs × pr.MemberMsg mem)
  choose := do
    let prob := Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p
    let spec := Fxmss.TcrOracleSpec prob
    let d ← (liftM sfStage.g₁ : OracleComp spec D)
    let sf ← sfStage.sfRun (sfTcrCall pr mem p) d
    let u ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y)) : OracleComp spec (SlSecAdrs vp → pr.Y))
    let (vt, savedQ) ← (simulateQ (Fxmss.recordTcrImpl prob)
      (slVirtualTreeM pr (routedTcrCall pr mem isTarget p) u)).run []
    return (d, sf, u, vt, savedQ)
  forge st pk := do
    let (d, sf, u, vt, savedQ) := st
    let res ← runPostPrf pr adv d sf pk vt.1 (slSignTable pr vt.2 pk vt.1 u)
    return extract pk u savedQ res.1 res.2

/-- **Exact SM-TCR advantage of `routedTcrAdv`** (in terms of `postPrfExp` and `routedTargets`). -/
theorem routedTcrAdv_advantage {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs)
    (mem : Primitives.Member) [DecidableEq (pr.MemberMsg mem)]
    (isTarget : Adrs → Bool) (p : ℕ)
    (hmem : ∀ a ∈ constructionAddresses vp.sl, isTarget a = true →
      ∀ u tbl, ∃ msg, evalNodeInput pr u tbl a = some ⟨mem, msg⟩)
    (hp : (slTreeAddresses vp).countP isTarget ≤ p)
    (extract : pr.PkSeed → (SlSecAdrs vp → pr.Y) → List (Adrs × pr.MemberMsg mem) →
      Option (List Byte × Stateless.Sig pr) → SlSignSt pr → ℕ × pr.MemberMsg mem) :
    SM_DT_TCR_Advantage (routedTcrAdv pr sfStage adv mem isTarget p extract) =
      Pr{let z ← postPrfExp pr sfStage adv}[
        Fxmss.tcrWin (Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p)
          z.1 (routedTargets pr z.1 z.2.1 mem isTarget)
          (extract z.1 z.2.1 (routedTargets pr z.1 z.2.1 mem isTarget) z.2.2.1 z.2.2.2) = true] := by
  set prob := Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p
  unfold SM_DT_TCR_Advantage postPrfExp
  rw [prEvent_eq_evalDist_bind]
  have hexp :
      SM_DT_TCR_Experiment (routedTcrAdv pr sfStage adv mem isTarget p extract) =ᵈ
      (do
        let pk ← $ᵗ pr.PkSeed
        let d ← sfStage.g₁
        let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        let pkSl := slRootDet pr pk u
        let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl (slSignDet pr pk pkSl u)
        return Fxmss.tcrWin prob pk (routedTargets pr pk u mem isTarget)
          (extract pk u (routedTargets pr pk u mem isTarget) res.1 res.2)) := by
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [routedTcrAdv]
    rw [show SM_DT_TCR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_TCR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    rw [← show SM_DT_TCR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_TCR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    obtain ⟨⟨qs₀, tws₀⟩, ⟨hqs₀, htws₀⟩, hsf⟩ := sfStage.sfRun_spec
      (SM_DT_TCR_oracles prob pk) (sfTcrCall pr mem p) pk
      (fun s => s.1 = [] ∧ ∀ t ∈ s.2, Scheme.IsStateful t)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg s hsf ⟨hqs, _⟩ => by
        rcases s with ⟨qs, tws⟩; dsimp only at hqs; subst hqs
        unfold sfTcrCall
        simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_TCR_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          collectionOracle, StateT.run_get, pure_bind, TweakReserved, List.not_mem_nil,
          false_and, exists_false, ↓reduceIte, StateT.run_set, Option.getD_some]
        rfl)
      (fun s a ⟨hqs, htws⟩ hsf => ⟨hqs, fun t ht => by
        rcases List.mem_append.1 ht with ht1 | ht2
        · exact htws t ht1
        · simp only [List.mem_singleton] at ht2; subst ht2; exact hsf⟩)
      d hd ([], []) ⟨rfl, fun _ h => by simp at h⟩
    dsimp only at hqs₀; subst hqs₀
    simp only [simulateQ_bind, StateT.run_bind, hsf, pure_bind, bind_assoc]
    rw [show SM_DT_TCR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_TCR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    rw [Fxmss.simulateQ_add_liftM_run, bind_map_left]
    refine EvalDistEq.bind_right _ fun u => ?_
    rw [← show SM_DT_TCR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_TCR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    obtain ⟨tws', _, hvt⟩ := simulateQ_slVirtualTreeM_routed_tcr pr mem isTarget p hmem hp pk u tws₀ htws₀
    have hrec := Fxmss.simulateQ_recordTcr_run prob pk
      (slVirtualTreeM pr (routedTcrCall pr mem isTarget p) u) [] tws₀
    unfold routedTcrCall at hrec
    rw [hvt, map_pure] at hrec
    change ((simulateQ (SM_DT_TCR_oracles prob pk)
      ((simulateQ (Fxmss.recordTcrImpl prob)
        (slVirtualTreeM pr (routedTcrCall pr mem isTarget p) u)).run [])).run ([], tws₀) >>= _) =ᵈ _
    have hrec' : (simulateQ (SM_DT_TCR_oracles prob pk)
      ((simulateQ (Fxmss.recordTcrImpl prob)
        (slVirtualTreeM pr (routedTcrCall pr mem isTarget p) u)).run [])).run ([], tws₀) =
      pure ((slVirtualTreeDet pr pk u, routedTargets pr pk u mem isTarget),
        (routedTargets pr pk u mem isTarget, tws')) := hrec
    rw [hrec']
    simp only [pure_bind, simulateQ_pure, StateT.run_pure]
    have hvt_spec := slVirtualTreeDet_spec pr pk u
    have hpkSl : (slVirtualTreeDet pr pk u).1 = slRootDet pr pk u :=
      hvt_spec.1.trans (slRootDet_eq_honestVal pr pk u).symm
    have hsign_eq : slSignTable pr (slVirtualTreeDet pr pk u).2 pk (slVirtualTreeDet pr pk u).1 u =
        slSignDet pr pk (slRootDet pr pk u) u := by
      funext msg R; rw [hpkSl]
      exact slSignTable_eq_slSignDet pr pk (slRootDet pr pk u) u hvt_spec.2.2 msg R
    rw [hsign_eq, hpkSl]
    refine EvalDistEq.bind_right _ fun res => ?_
    simp only [Fxmss.tcrWin]
    cases (routedTargets pr pk u mem isTarget)[(extract pk u (routedTargets pr pk u mem isTarget) res.1 res.2).1]? with
    | none => rfl
    | some tm => rfl
  have hmeas := evalDistEq_apply_true hexp
  rw [hmeas]
  simp only [bind_assoc, pure_bind]
  refine congrArg (fun m => 𝒟[m] {true}) ?_
  refine bind_congr fun pk => bind_congr fun d => bind_congr fun u => bind_congr fun res => ?_
  congr 1
  cases Fxmss.tcrWin prob pk (routedTargets pr pk u mem isTarget)
    (extract pk u (routedTargets pr pk u mem isTarget) res.1 res.2) <;> simp

/-- Helper: index-lookup extractor from a candidate function `cand`. -/
noncomputable def idxExtract {M : Type} [Inhabited M]
    (cand : pr.PkSeed → (SlSecAdrs vp → pr.Y) → Option (List Byte × Stateless.Sig pr) → SlSignSt pr →
      Option (Adrs × M)) :
    pr.PkSeed → (SlSecAdrs vp → pr.Y) → List (Adrs × M) →
      Option (List Byte × Stateless.Sig pr) → SlSignSt pr → ℕ × M :=
  fun pk u savedQ out st =>
    match cand pk u out st with
    | none => (savedQ.length, default)
    | some (a, msg') => ((savedQ.map Prod.fst).idxOf a, msg')

/-- Reusable `SM-TCR` reduction bound: if event `Ev` implies the existence of a valid collision
`(a, msg')` at a target address `a ∈ constructionAddresses vp.sl` with `isTarget a = true` and
`honestInput = some ⟨mem, honestMsg⟩`, then `Pr[Ev] ≤ SM_DT_TCR_Advantage (routedTcrAdv ...)`. -/
theorem routedTcr_bound_of_witness {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs)
    (mem : Primitives.Member) [DecidableEq (pr.MemberMsg mem)] [Inhabited (pr.MemberMsg mem)]
    (isTarget : Adrs → Bool) (p : ℕ)
    (hmem : ∀ a ∈ constructionAddresses vp.sl, isTarget a = true →
      ∀ u tbl, ∃ msg, evalNodeInput pr u tbl a = some ⟨mem, msg⟩)
    (hp : (slTreeAddresses vp).countP isTarget ≤ p)
    (Ev : pr.PkSeed → (SlSecAdrs vp → pr.Y) → Option (List Byte × Stateless.Sig pr) → SlSignSt pr → Prop)
    (cand : pr.PkSeed → (SlSecAdrs vp → pr.Y) → Option (List Byte × Stateless.Sig pr) → SlSignSt pr →
      Option (Adrs × pr.MemberMsg mem))
    (hsound : ∀ pk u out st, Ev pk u out st →
      ∃ a msg' honestMsg,
        cand pk u out st = some (a, msg') ∧
        a ∈ constructionAddresses vp.sl ∧
        isTarget a = true ∧
        honestInput pr pk u a = some ⟨mem, honestMsg⟩ ∧
        msg' ≠ honestMsg ∧
        pr.memberEval mem pk a msg' = pr.memberEval mem pk a honestMsg) :
    Pr{let z ← postPrfExp pr sfStage adv}[Ev z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (routedTcrAdv pr sfStage adv mem isTarget p (idxExtract pr cand)) := by
  rw [routedTcrAdv_advantage pr sfStage adv mem isTarget p hmem hp (idxExtract pr cand)]
  refine prEvent_mono _ _ _ fun ⟨pk, u, out, st⟩ hev => ?_
  obtain ⟨a, msg', honestMsg, hcand, hca, ht, hhi, hne, hcoll⟩ := hsound pk u out st hev
  set Q := routedTargets pr pk u mem isTarget
  have hQmem : (a, honestMsg) ∈ Q := mem_routedTargets_of_honestInput pr pk u mem isTarget hca ht hhi
  have hnd : (Q.map Prod.fst).Nodup := nodup_map_fst_routedTargets pr pk u mem isTarget
  have ha_mem : a ∈ Q.map Prod.fst := List.mem_map.2 ⟨(a, honestMsg), hQmem, rfl⟩
  have hidx_lt : (Q.map Prod.fst).idxOf a < Q.length := by
    have := List.idxOf_lt_length_of_mem ha_mem; simpa [List.length_map] using this
  have hget_fst : (Q[(Q.map Prod.fst).idxOf a]'hidx_lt).1 = a := by
    have h := List.getElem_idxOf (List.idxOf_lt_length_of_mem ha_mem)
    rw [List.getElem_map] at h
    exact h
  have hget_snd : (Q[(Q.map Prod.fst).idxOf a]'hidx_lt).2 = honestMsg := by
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.1 hQmem
    have hk_fst : (Q.map Prod.fst)[k]'(by simpa using hk) = a := by simp [hkeq]
    have hkeq_idx : k = (Q.map Prod.fst).idxOf a := by
      have hinj := List.nodup_iff_injective_getElem.1 hnd
      have heq : (⟨k, by simpa using hk⟩ : Fin (Q.map Prod.fst).length) =
          ⟨(Q.map Prod.fst).idxOf a, List.idxOf_lt_length_of_mem ha_mem⟩ :=
        hinj (hk_fst.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem ha_mem)).symm)
      exact congrArg Fin.val heq
    subst hkeq_idx; exact congrArg Prod.snd hkeq
  have hget : Q[(Q.map Prod.fst).idxOf a]? = some (a, honestMsg) := by
    rw [List.getElem?_eq_getElem hidx_lt]
    exact congrArg some (Prod.ext hget_fst hget_snd)
  simp only [Fxmss.tcrWin, idxExtract, hcand, hget]
  change decide (msg' ≠ honestMsg ∧ pr.memberEval mem pk a msg' = pr.memberEval mem pk a honestMsg) = true
  simp [hne, hcoll]

/-! ### Instantiation of the 5 direct `SM-TCR` reductions (`q₅, q₇, q₄, q₆, q₃`) -/

/-- Exact target counts matching Main Paper Theorem 4.3 (`[HK22]`). -/
def qWotsStep (vp : ValidatedParams) : ℕ := (wotsStepAddresses vp.sl).length
def qXmssH (vp : ValidatedParams) : ℕ := (xmssNodeAddresses vp.sl).length
def qForsRoot (vp : ValidatedParams) : ℕ := (forsRootAddresses vp.sl).length
def qWotsPk (vp : ValidatedParams) : ℕ := (wotsPkAddresses vp.sl).length
def qForsH (vp : ValidatedParams) : ℕ := (forsTreeAddresses vp.sl).length
def qForsLeaf (vp : ValidatedParams) : ℕ := (forsLeafAddresses vp.sl).length

/-- Helper: candidate extractor for `Th_k` (`EvTcrThK`). -/
noncomputable def candThK (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Adrs × pr.MemberMsg .thK) :=
  match out with
  | none => none
  | some (msg, sig) =>
      match extractedWitness pr pk u (some (msg, sig)) st with
      | some (.fors (.tlCollision rec)) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
          some (forsPkAdrs parts.forsAdrs, rec)
      | _ => none

/-- Helper: candidate extractor for FORS internal `H` (`EvTcrHFors`). -/
noncomputable def candHFors (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Adrs × pr.MemberMsg .H) :=
  match out with
  | none => none
  | some (msg, sig) =>
      match extractedWitness pr pk u (some (msg, sig)) st with
      | some (.fors (.hCollision i z c)) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
          some (forsNodeAdrs parts.forsAdrs z (forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ z), c)
      | _ => none

/-- Helper: candidate extractor for XMSS internal `H` (`EvTcrHXmss`). -/
noncomputable def candHXmss (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Adrs × pr.MemberMsg .H) :=
  match out with
  | none => none
  | some (msg, sig) =>
      match extractedWitness pr pk u (some (msg, sig)) st with
      | some (.hypertree ⟨ℓ, .hCollision z c⟩) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
          let pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
          some (xmssNodeAdrs pos.toAdrs z (pos.leaf.val / 2 ^ z), c)
      | _ => none

/-- Helper: candidate extractor for WOTS+ `Th_lsl` (`EvTcrThLsl`). -/
noncomputable def candThLsl (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Adrs × pr.MemberMsg .thLsl) :=
  match out with
  | none => none
  | some (msg, sig) =>
      match extractedWitness pr pk u (some (msg, sig)) st with
      | some (.hypertree ⟨ℓ, .wots (.tlCollision rec)⟩) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
          let pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
          some (wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val),
            rec.cast (Params.lsl_eq_len vp.valid).symm)
      | _ => none

/-- Helper: candidate extractor for WOTS+ chain `F` collision (`EvTcrFWots`). -/
noncomputable def candFWots (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Adrs × pr.MemberMsg .F) :=
  match out with
  | none => none
  | some (msg, sig) =>
      match extractedWitness pr pk u (some (msg, sig)) st with
      | some (.hypertree ⟨ℓ, .wots (.fCollision c step val)⟩) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
          let pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
          some ((wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val).setHashAddress step, val)
      | _ => none

/-- `B_tcrThK`: Stage-1 routed `SM-TCR` reduction against `Th_k ∈ Th_λ` (`q₅ = qForsRoot vp`). -/
noncomputable def B_tcrThK {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :=
  routedTcrAdv pr sfStage adv .thK isForsRoot (qForsRoot vp) (idxExtract pr (candThK pr))

/-- `B_tcrH_fors`: Stage-1 routed `SM-TCR` reduction against `H ∈ Th_λ` (`q₇ = qForsH vp`). -/
noncomputable def B_tcrH_fors {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :=
  routedTcrAdv pr sfStage adv .H isForsH (qForsH vp) (idxExtract pr (candHFors pr))

/-- `B_tcrH_xmss`: Stage-1 routed `SM-TCR` reduction against `H ∈ Th_λ` (`q₄ = qXmssH vp`). -/
noncomputable def B_tcrH_xmss {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :=
  routedTcrAdv pr sfStage adv .H isXmssH (qXmssH vp) (idxExtract pr (candHXmss pr))

/-- `B_tcrThLsl`: Stage-1 routed `SM-TCR` reduction against `Th_lsl ∈ Th_λ` (`q₆ = qWotsPk vp`). -/
noncomputable def B_tcrThLsl {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :=
  routedTcrAdv pr sfStage adv .thLsl isWotsPk (qWotsPk vp) (idxExtract pr (candThLsl pr))

/-- `B_tcrF_wots`: Stage-1 routed `SM-TCR` reduction against `F ∈ Th_λ` (`q₃ = qWotsStep vp`). -/
noncomputable def B_tcrF_wots {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :=
  routedTcrAdv pr sfStage adv .F isWotsStep (qWotsStep vp) (idxExtract pr (candFWots pr))

theorem pr_EvTcrThK_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvTcrThK pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (B_tcrThK pr sfStage adv) := by
  refine routedTcr_bound_of_witness pr sfStage adv .thK isForsRoot (qForsRoot vp)
    (fun _ _ ht u tbl => evalNodeInput_isForsRoot pr ht u tbl)
    (by rw [countP_slTreeAddresses_isForsRoot]; exact le_rfl)
    (EvTcrThK pr) (candThK pr) fun pk u out st ⟨hwin, rec, hw⟩ => ?_
  rcases out with _ | ⟨msg, sig⟩
  · exact hwin.elim
  · have hval := extractedWitness_sound pr pk u msg sig st hw
    rw [Witness.valid_fors, ForsWitness.valid_tlCollision] at hval
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hp_eq : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩ = parts :=
      schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩
    rw [hp_eq] at hval
    refine ⟨forsPkAdrs parts.forsAdrs, rec, forsHonestRoots (prEager pr) u pk parts.forsAdrs,
      by simp [candThK, hw, parts],
      (mem_constructionAddresses_iff _).2 (Or.inr (Or.inr (Or.inl (mem_forsRootAddresses_of_parts parts)))),
      rfl, honestInput_forsRoot pr pk u parts.forsAdrs, hval.1, hval.2⟩

theorem pr_EvTcrHFors_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvTcrHFors pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (B_tcrH_fors pr sfStage adv) := by
  refine routedTcr_bound_of_witness pr sfStage adv .H isForsH (qForsH vp)
    (fun _ _ ht u tbl => evalNodeInput_isForsH pr ht u tbl)
    (by rw [countP_slTreeAddresses_isForsH]; exact le_rfl)
    (EvTcrHFors pr) (candHFors pr) fun pk u out st ⟨hwin, i, z, c, hw⟩ => ?_
  rcases out with _ | ⟨msg, sig⟩
  · exact hwin.elim
  · have hval := extractedWitness_sound pr pk u msg sig st hw
    rw [Witness.valid_fors, ForsWitness.valid_hCollision] at hval
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hp_eq : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩ = parts :=
      schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩
    rw [hp_eq] at hval
    obtain ⟨hz0, hza, hne, hcoll⟩ := hval
    refine ⟨forsNodeAdrs parts.forsAdrs z (forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ z),
      c, forsHonestChildren (prEager pr) u pk parts.forsAdrs z (forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ z),
      by simp [candHFors, hw, parts],
      (mem_constructionAddresses_iff _).2 (Or.inr (Or.inl (mem_forsTreeAddresses_of_parts parts parts.md.toList i hz0 hza))),
      by simp only [isForsH, forsNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight,
           Adrs.setTypeAndClear, AddrType.toCode, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
         exact ⟨rfl, Nat.ne_of_gt hz0⟩,
      honestInput_forsH pr pk u parts.forsAdrs hz0 _,
      hne.symm, hcoll.symm⟩

theorem pr_EvTcrHXmss_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvTcrHXmss pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (B_tcrH_xmss pr sfStage adv) := by
  refine routedTcr_bound_of_witness pr sfStage adv .H isXmssH (qXmssH vp)
    (fun _ _ ht u tbl => evalNodeInput_isXmssH pr ht u tbl)
    (by rw [countP_slTreeAddresses_isXmssH]; exact le_rfl)
    (EvTcrHXmss pr) (candHXmss pr) fun pk u out st ⟨hwin, ℓ, z, c, hw⟩ => ?_
  rcases out with _ | ⟨msg, sig⟩
  · exact hwin.elim
  · have hval := extractedWitness_sound pr pk u msg sig st hw
    rw [Witness.valid_hypertree, HypertreeWitness.valid_iff, XmssWitness.valid_hCollision] at hval
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hp_eq : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩ = parts :=
      schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩
    rw [hp_eq] at hval
    obtain ⟨hz0, hzh, hne, hcoll⟩ := hval
    set pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
    have hlt_idx : pos.leaf.val / 2 ^ z < 2 ^ (vp.sl.params.hp - z) := by
      have hdiv : pos.leaf.val / 2 ^ z < 2 ^ vp.sl.params.hp / 2 ^ z :=
        Nat.div_lt_div_of_lt_of_dvd (Nat.pow_dvd_pow 2 hzh) pos.leaf.isLt
      simpa [Nat.pow_div hzh (by decide : 0 < 2)] using hdiv
    have hmem_xmss : xmssNodeAdrs pos.toAdrs z (pos.leaf.val / 2 ^ z) ∈ xmssNodeAddresses vp.sl := by
      rw [← LayerTreeCoord.ofPosition_toAdrs pos]
      exact mem_xmssNodeAddresses vp.sl (LayerTreeCoord.ofPosition pos) hz0 hzh hlt_idx
    refine ⟨xmssNodeAdrs pos.toAdrs z (pos.leaf.val / 2 ^ z), c,
      xmssHonestChildren (prEager pr) u pk pos.toAdrs z (pos.leaf.val / 2 ^ z),
      by simp [candHXmss, hw, parts, pos],
      (mem_constructionAddresses_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmem_xmss))))),
      by simp [isXmssH, xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode, Nat.ne_of_gt hz0],
      honestInput_xmssH pr pk u pos.toAdrs hz0 _,
      hne.symm, hcoll.symm⟩

theorem pr_EvTcrThLsl_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvTcrThLsl pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (B_tcrThLsl pr sfStage adv) := by
  refine routedTcr_bound_of_witness pr sfStage adv .thLsl isWotsPk (qWotsPk vp)
    (fun _ _ ht u tbl => evalNodeInput_isWotsPk pr ht u tbl)
    (by rw [countP_slTreeAddresses_isWotsPk]; exact le_rfl)
    (EvTcrThLsl pr) (candThLsl pr) fun pk u out st ⟨hwin, ℓ, rec, hw⟩ => ?_
  rcases out with _ | ⟨msg, sig⟩
  · exact hwin.elim
  · have hval := extractedWitness_sound pr pk u msg sig st hw
    rw [Witness.valid_hypertree, HypertreeWitness.valid_iff, XmssWitness.valid_wots,
      WotsWitness.valid_tlCollision] at hval
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hp_eq : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩ = parts :=
      schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩
    rw [hp_eq] at hval
    set pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
    have hmem_wpk : wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) ∈ wotsPkAddresses vp.sl := by
      rw [wotsLeafAdrs_eq_wotsInstanceAdrs' pos]
      exact mem_wotsPkAddresses vp.sl pos
    refine ⟨wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val),
      rec.cast (Params.lsl_eq_len vp.valid).symm,
      (wotsPkGenTops (prEager pr) u pk (wotsLeafAdrs pos.toAdrs pos.leaf.val)).cast (Params.lsl_eq_len vp.valid).symm,
      by simp [candThLsl, hw, parts, pos],
      (mem_constructionAddresses_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmem_wpk))))),
      rfl, honestInput_wotsPk pr pk u _,
      fun h => hval.1 (by have := congrArg (Vector.cast (Params.lsl_eq_len vp.valid)) h; simpa using this),
      ?_⟩
    change (prEager pr).Tl pk (wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val))
        (rec.cast (Params.lsl_eq_len vp.valid).symm).toList =
      (prEager pr).Tl pk (wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val))
        ((wotsPkGenTops (prEager pr) u pk (wotsLeafAdrs pos.toAdrs pos.leaf.val)).cast
          (Params.lsl_eq_len vp.valid).symm).toList
    simpa only [Vector.toList_cast] using hval.2

theorem pr_EvTcrFWots_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvTcrFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (B_tcrF_wots pr sfStage adv) := by
  refine routedTcr_bound_of_witness pr sfStage adv .F isWotsStep (qWotsStep vp)
    (fun _ _ ht u tbl => evalNodeInput_isWotsStep pr ht u tbl)
    (by rw [countP_slTreeAddresses_isWotsStep]; exact le_rfl)
    (EvTcrFWots pr) (candFWots pr) fun pk u out st ⟨hwin, ℓ, c, step, val, hw⟩ => ?_
  rcases out with _ | ⟨msg, sig⟩
  · exact hwin.elim
  · have hval := extractedWitness_sound pr pk u msg sig st hw
    rw [Witness.valid_hypertree, HypertreeWitness.valid_iff, XmssWitness.valid_wots,
      WotsWitness.valid_fCollision] at hval
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hp_eq : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩ = parts :=
      schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩
    rw [hp_eq] at hval
    obtain ⟨hstep_lt, hstep_ge, hne, hcoll⟩ := hval
    set pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
    have hmem_ws : (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val).setHashAddress step ∈
        wotsStepAddresses vp.sl := by
      rw [wotsLeafAdrs_eq_wotsInstanceAdrs' pos]
      exact mem_wotsStepAddresses vp.sl (pos, c) ⟨step, hstep_lt⟩
    refine ⟨(wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val).setHashAddress step,
      val, _,
      by simp [candFWots, hw, parts, pos],
      (mem_constructionAddresses_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inl hmem_ws)))),
      rfl, honestInput_wotsStep pr pk u _ c _ step hstep_ge,
      hne, hcoll⟩

end RoutedReductions

/-! ## 5. WOTS-TW Preimage Bound (`EvPreFWots`, via `WotsHybrid.wotsPre_bound`) -/

section WotsPreBound

variable {vp : ValidatedParams} (pr : Primitives vp.params)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]

/-- Keyless Stage-2 runner for `WotsHybrid`: runs `adv` with `hybSign pr pk hyb u`, returning
`some (msg, sig)` if `PostPrfWin` holds (under `hyb.pkSl`) and `none` otherwise. -/
noncomputable def wotsStage2 {D E : Type} {qs : ℕ}
    (adv : PostPrfAdv pr D E qs) :
    D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr)) :=
  fun d sf pk u hyb => do
    let res ← runPostPrf pr adv d sf pk hyb.pkSl (hybSign pr pk hyb u)
    return if PostPrfWin pr pk hyb.pkSl res.2.log res.1 then res.1 else none

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] in
/-- `wotsStage2` does not depend on `u` at `WOTS_PRF` addresses (`type = 5`). -/
theorem wotsStage2_indep_wotsSk {D E : Type} {qs : ℕ}
    (adv : PostPrfAdv pr D E qs)
    (u₁ u₂ : SlSecAdrs vp → pr.Y)
    (h : ∀ a : SlSecAdrs vp, a.1.type ≠ 5 → u₁ a = u₂ a)
    (d : D) (sf : E) (pk : pr.PkSeed) (hyb : HybTree pr) :
    wotsStage2 pr adv d sf pk u₁ hyb = wotsStage2 pr adv d sf pk u₂ hyb := by
  unfold wotsStage2
  have hs : hybSign pr pk hyb u₁ = hybSign pr pk hyb u₂ := by
    funext msg R; exact hybSign_indep_wotsSk pr pk hyb u₁ u₂ h msg R
  rw [hs]

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **`EvPreFWots` bound (`q₂ = qWots vp`)**:
`Pr[EvPreFWots] ≤ ∑ γ < w - 2, SM_DT_UD_Advantage (B_ud ...) + SM_DT_PRE_Advantage (B_pre ...)`. -/
theorem pr_EvPreFWots_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvPreFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (B_ud pr sfStage (wotsStage2 pr adv) γ) +
      SM_DT_PRE_Advantage (B_pre pr sfStage (wotsStage2 pr adv)) := by
  refine le_trans ?_ (wotsPre_bound pr sfStage (wotsStage2 pr adv) (wotsStage2_indep_wotsSk pr adv))
  unfold postPrfExp wotsStage2
  rw [prEvent_eq_evalDist_bind]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun pk _ => ?_
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun d _ => ?_
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun u _ => ?_
  have hpk_eq : (hybTreeDet pr 0 pk u).pkSl = slRootDet pr pk u := (hybTreeDet_zero_spec pr pk u).1
  have hsign_eq : hybSign pr pk (hybTreeDet pr 0 pk u) u = slSignDet pr pk (slRootDet pr pk u) u := by
    funext msg R; exact hybSign_zero_eq_slSignDet pr pk u msg R
  rw [hpk_eq, hsign_eq]
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun res _ => ?_
  by_cases hev : EvPreFWots pr pk u res.1 res.2
  · have ⟨hwin, ℓ, c, step, val, hw⟩ := hev
    rcases res with ⟨out, st⟩
    rcases out with _ | ⟨msg, sig⟩
    · exact hwin.elim
    · have hver : SLHDSA.GeneralScheme.verifyInternal vp.sl (prEager pr) msg (toEagerSig pr sig)
          ⟨pk, slRootDet pr pk u⟩ = true := by
        rw [verifyInternal_prEager_eq]; exact hwin.2
      have hfw : findWitness (vp := vp.sl) (prims := prEager pr) u ⟨pk, slRootDet pr pk u⟩ msg
          (toEagerSig pr sig) (chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig) =
          some (.hypertree ⟨ℓ, .wots (.fPreimage c step val)⟩) :=
        (extractedWitness_eq_hypertree_iff pr pk u msg sig st _).1 hw
      have hpre : (findHybWotsPre pr pk (hybTreeDet pr 0 pk u) msg sig).isSome = true :=
        (findHybWotsPre_zero_iff pr pk u msg sig
          (chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig) hver).2
          ⟨ℓ, c, step, val, hfw⟩
      simp [hwin, isHybWotsPre, hpre, hev]
  · simp [hev]

end WotsPreBound

/-! ## 6. FORS Leaf Preimage Bound (`EvForsPre`, [BHK+19, Claim 23]: `3 * TCR + DSPR`) -/

section ForsPreBound

variable {vp : ValidatedParams} (pr : Primitives vp.params)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]

/-! ### Generic Stage-1 routed `SM-DSPR` adversary (`routedDsprAdv`) -/

/-- First-stage oracle specification for `SM-DSPR`. -/
abbrev DsprOracleSpec {ι P T M N : Type} (prob : SM_DT_DSPR_Problem ι P T M N) :=
  unifSpec + (SM_DT_DSPR_challengeSpec T M N + collectionSpec prob.thColl)

/-- First-stage query recorder for `SM-DSPR` (exact mirror of `Fxmss.recordTcrImpl`). -/
def recordDsprImpl {ι P T M N : Type} (prob : SM_DT_DSPR_Problem ι P T M N) :
    QueryImpl (DsprOracleSpec prob) (StateT (List (T × M)) (OracleComp (DsprOracleSpec prob)))
  | .inl n => StateT.mk fun acc => (fun u => (u, acc)) <$>
      (liftM ((DsprOracleSpec prob).query (.inl n)) :
        OracleComp (DsprOracleSpec prob) (unifSpec.Range n))
  | .inr (.inl tm) => StateT.mk fun acc => do
      let r ← (liftM ((DsprOracleSpec prob).query (.inr (.inl tm))) :
        OracleComp (DsprOracleSpec prob) (Option N))
      return (r, if r.isSome then acc ++ [tm] else acc)
  | .inr (.inr q) => StateT.mk fun acc => (fun r => (r, acc)) <$>
      (liftM ((DsprOracleSpec prob).query (.inr (.inr q))) :
        OracleComp (DsprOracleSpec prob) (Option N))

theorem simulateQ_recordDspr_run {ι P T M N : Type} [DecidableEq T]
    (prob : SM_DT_DSPR_Problem ι P T M N) (pk : P) {α : Type}
    (oa : OracleComp (DsprOracleSpec prob) α) (qs : List (T × M)) (tws : List T) :
    (simulateQ (SM_DT_DSPR_oracles prob pk) ((simulateQ (recordDsprImpl prob) oa).run qs)).run
        (qs, tws) =
      (fun z => ((z.1, z.2.1), z.2)) <$> (simulateQ (SM_DT_DSPR_oracles prob pk) oa).run (qs, tws) := by
  induction oa using OracleComp.inductionOn generalizing qs tws with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | tm | q
    · simp only [simulateQ_bind, simulateQ_spec_query, recordDsprImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hcoin : (SM_DT_DSPR_oracles prob pk (.inl n)).run (qs, tws) =
          (fun u => (u, (qs, tws))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp [SM_DT_DSPR_oracles, StateT.run_monadLift]
      rw [hcoin, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u qs tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordDsprImpl, StateT.run_bind, StateT.run_mk,
        bind_assoc, map_bind]
      have hch : (SM_DT_DSPR_oracles prob pk (.inr (.inl tm))).run (qs, tws) =
          (SM_DT_DSPR_challengeOracle prob pk tm).run (qs, tws) := rfl
      rw [hch]; unfold SM_DT_DSPR_challengeOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind, simulateQ_pure, Option.isSome_none,
          Bool.false_eq_true, ↓reduceIte]
        exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
          Option.isSome_some, ↓reduceIte]
        exact ih (some (prob.th.eval pk tm.1 tm.2)) (qs ++ [tm]) tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordDsprImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hco : (SM_DT_DSPR_oracles prob pk (.inr (.inr q))).run (qs, tws) =
          (collectionOracle (Q := T × M) Prod.fst prob.thColl pk q).run (qs, tws) := rfl
      rw [hco]; unfold collectionOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind]; exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact ih (some (prob.thColl.eval q.1 pk q.2.1 q.2.2)) qs (tws ++ [q.2.1])

/-- Routed Stage-1 `SM-DSPR` callback for `F ∈ Th_λ` at `isForsLeaf` tweaks (`q₈ = qForsLeaf vp`). -/
def routedDsprCall :
    (i : Primitives.Member) → Adrs → pr.MemberMsg i →
      OracleComp (DsprOracleSpec (Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp))) pr.Y :=
  fun i a msg =>
    let spec := DsprOracleSpec (Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp))
    if h : isForsLeaf a = true ∧ i = .F then do
      let y ← (liftM (spec.query (.inr (.inl (a, h.2 ▸ msg)))) : OracleComp spec (Option pr.Y))
      return y.getD default
    else do
      let y ← (liftM (spec.query (.inr (.inr ⟨some i, a, msg⟩))) : OracleComp spec (Option pr.Y))
      return y.getD default

/-- Pure `O_coll` callback for Stage-1 stateful precomputation in `SM-DSPR`. -/
def sfDsprCall :
    (i : Primitives.Member) → Adrs → pr.MemberMsg i →
      OracleComp (DsprOracleSpec (Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp))) pr.Y :=
  fun i a msg =>
    let spec := DsprOracleSpec (Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp))
    do
      let y ← (liftM (spec.query (.inr (.inr ⟨some i, a, msg⟩))) : OracleComp spec (Option pr.Y))
      return y.getD default

/-- Extract the FORS leaf `(aLeaf*, aSk*, val)` witness when `EvForsPre` holds. -/
noncomputable def candForsPre (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    Option (Adrs × pr.Y) :=
  if EvForsPre pr pk u out st then
    match out with
    | none => none
    | some (msg, sig) =>
        match extractedWitness pr pk u (some (msg, sig)) st with
        | some (.fors (.fPreimage i val)) =>
            let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
            some (forsNodeAdrs parts.forsAdrs 0 (forsSigLeafIndex vp.sl.params parts.md.toList i.val), val)
        | _ => none
  else none

/-- `B_tcrF_fors`: Stage-1 routed `SM-TCR` reduction against `F ∈ Th_λ` (`q₈ = qForsLeaf vp`). -/
noncomputable def B_tcrF_fors {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :=
  routedTcrAdv pr sfStage adv .F isForsLeaf (qForsLeaf vp) (idxExtract pr (candForsPre pr))

/-- `B_dsprF_fors`: Stage-1 routed `SM-DSPR` reduction against `F ∈ Th_λ` (`q₈ = qForsLeaf vp`).
When `EvForsPre` holds with witness `(aLeaf*, val)` AND `val = honestX` (the preimage at `aLeaf*`),
it guesses `(idxOf aLeaf*, false)` (predicting NO second preimage); otherwise it outputs the
out-of-range index `savedQ.length`, which loses both `SM_DT_DSPR_Experiment` and
`SM_DT_DSPR_SPExperiment`. -/
noncomputable def B_dsprF_fors {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    SM_DT_DSPR_Adversary (Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp)) where
  State := D × E × (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y)) × List (Adrs × pr.MemberMsg .F)
  choose := do
    let prob := Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp)
    let spec := DsprOracleSpec prob
    let d ← (liftM sfStage.g₁ : OracleComp spec D)
    let sf ← sfStage.sfRun (sfDsprCall pr) d
    let u ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y)) : OracleComp spec (SlSecAdrs vp → pr.Y))
    let (vt, savedQ) ← (simulateQ (recordDsprImpl prob)
      (slVirtualTreeM pr (routedDsprCall pr) u)).run []
    return (d, sf, u, vt, savedQ)
  guess st pk := do
    let (d, sf, u, vt, savedQ) := st
    let res ← runPostPrf pr adv d sf pk vt.1 (slSignTable pr vt.2 pk vt.1 u)
    return match candForsPre pr pk u res.1 res.2 with
      | none => (savedQ.length, false)
      | some (aLeaf, val) =>
          let j := (savedQ.map Prod.fst).idxOf aLeaf
          match savedQ[j]? with
          | some (_, x) => if val = x then (j, false) else (savedQ.length, false)
          | none => (savedQ.length, false)

omit [Fintype pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] in
/-- Soundness of `candForsPre`: whenever `EvForsPre` holds, `candForsPre` returns `some (aLeaf, val)`
with `aLeaf ∈ forsLeafAddresses`, `honestInput = some ⟨.F, x*⟩`, and `pr.F pk aLeaf val = pr.F pk aLeaf x*`. -/
theorem candForsPre_sound (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr)
    (hev : EvForsPre pr pk u out st) :
    ∃ (msg : List Byte) (sig : Stateless.Sig pr) (i : Fin vp.sl.params.k) (val : pr.Y),
      out = some (msg, sig) ∧
      extractedWitness pr pk u out st = some (.fors (.fPreimage i val)) ∧
      let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
      let idx := forsSigLeafIndex vp.sl.params parts.md.toList i.val
      let aLeaf := forsNodeAdrs parts.forsAdrs 0 idx
      let x := slSecOf pr u (forsSkAdrs parts.forsAdrs idx)
      candForsPre pr pk u out st = some (aLeaf, val) ∧
      aLeaf ∈ constructionAddresses vp.sl ∧
      isForsLeaf aLeaf = true ∧
      honestInput pr pk u aLeaf = some ⟨.F, x⟩ ∧
      pr.F pk aLeaf val = pr.F pk aLeaf x ∧
      i = chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig := by
  obtain ⟨hwin, hnotItsr, i, val, hw⟩ := hev
  rcases out with _ | ⟨msg, sig⟩
  · exact hwin.elim
  · have hval := extractedWitness_sound pr pk u msg sig st hw
    rw [Witness.valid_fors, ForsWitness.valid_fPreimage] at hval
    have hi_eq : i = chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig := by
      have hw' := hw
      unfold extractedWitness at hw'
      dsimp only at hw'
      split at hw'
      · simp only [Option.some.injEq, Witness.fors.injEq] at hw'
        unfold slFindForsWitness at hw'
        split at hw'
        · rcases hfind : (List.finRange vp.sl.params.k).findSome?
              (slFindForsTreeCollision pr (toEagerSig pr sig).fors _ u pk _) with _ | w
          · rw [hfind, Option.getD_none] at hw'
            exact (ForsWitness.fPreimage.inj hw').1.symm
          · rw [hfind, Option.getD_some] at hw'
            obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some hfind
            unfold slFindForsTreeCollision at hj
            dsimp only at hj
            split at hj
            · cases hj
            · rw [Option.map_eq_some_iff] at hj
              obtain ⟨_, _, rfl⟩ := hj; cases hw'
        · cases hw'
      · rename_i hfp
        rw [findWitness_eq_hypertree_of_ne u ⟨pk, slRootDet pr pk u⟩ msg (toEagerSig pr sig) _ hfp,
            Option.map_eq_some_iff] at hw'
        obtain ⟨_, _, hcontra⟩ := hw'; cases hcontra
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hp_eq : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩ = parts :=
      schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, slRootDet pr pk u⟩
    rw [hp_eq] at hval
    refine ⟨msg, sig, i, val, rfl, hw,
      by simp [candForsPre, EvForsPre, hwin, hnotItsr, hw],
      (mem_constructionAddresses_iff _).2 (Or.inl (mem_forsLeafAddresses_of_parts parts parts.md.toList i)),
      rfl, honestInput_forsLeaf pr pk u parts.forsAdrs _, hval, hi_eq⟩

/-- Sub-events of `EvForsPre`:
* `EvForsPreNe`: `EvForsPre` with `val ≠ x*` (a genuine second preimage — directly wins `SM-TCR`)
* `EvForsPreEqSP`: `EvForsPre` with `val = x*` AND `SecondPreimageExists`
* `EvForsPreNoSP`: `EvForsPre` with `¬ SecondPreimageExists` (which forces `val = x*`). -/
def EvForsPreNe (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  ∃ aLeaf val x,
    candForsPre pr pk u out st = some (aLeaf, val) ∧
    honestInput pr pk u aLeaf = some ⟨.F, x⟩ ∧
    val ≠ x

def EvForsPreEqSP (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  ∃ aLeaf val x,
    candForsPre pr pk u out st = some (aLeaf, val) ∧
    honestInput pr pk u aLeaf = some ⟨.F, x⟩ ∧
    val = x ∧
    SecondPreimageExists (pr.member ($ᵗ pr.PkSeed) .F) pk aLeaf x

def EvForsPreNoSP (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) : Prop :=
  ∃ aLeaf val x,
    candForsPre pr pk u out st = some (aLeaf, val) ∧
    honestInput pr pk u aLeaf = some ⟨.F, x⟩ ∧
    ¬ SecondPreimageExists (pr.member ($ᵗ pr.PkSeed) .F) pk aLeaf x

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- `EvForsPreNe` is bounded directly by `SM_DT_TCR_Advantage (B_tcrF_fors ...)`. -/
theorem pr_EvForsPreNe_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      SM_DT_TCR_Advantage (B_tcrF_fors pr sfStage adv) := by
  refine routedTcr_bound_of_witness pr sfStage adv .F isForsLeaf (qForsLeaf vp)
    (fun _ _ ht u tbl => evalNodeInput_isForsLeaf pr ht u tbl)
    (by rw [countP_slTreeAddresses_isForsLeaf]; exact le_rfl)
    (EvForsPreNe pr) (candForsPre pr) fun pk u out st ⟨aLeaf, val, x, hcand, hhi, hne⟩ => ?_
  have hev : EvForsPre pr pk u out st := by
    by_contra hnot; simp [candForsPre, hnot] at hcand
  obtain ⟨msg, sig, i, val', _, _, hcand', hca, ht, hhi', hF, _⟩ := candForsPre_sound pr pk u out st hev
  rw [hcand] at hcand'; obtain ⟨ha_eq, hv_eq⟩ := Prod.mk.inj (Option.some.inj hcand')
  subst hv_eq
  rw [← ha_eq] at hca ht hhi' hF
  rw [hhi] at hhi'
  have hx : x = slSecOf pr u (forsSkAdrs (splitDigest vp.sl.params
      (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)).forsAdrs
      (forsSigLeafIndex vp.sl.params (splitDigest vp.sl.params
        (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)).md.toList i.val)) := by
    have h := Option.some.inj hhi'
    cases h
    rfl
  rw [← hx] at hF
  exact ⟨aLeaf, val, x, hcand, hca, ht, hhi, hne, hF⟩

omit [DecidableEq pr.PkSeed] in
/-- **Exact `SM-DSPR` advantage of `B_dsprF_fors`**:
`Pr[EvForsPreNoSP] - Pr[EvForsPreEqSP] = SM_DT_DSPR_Advantage (B_dsprF_fors ...)`. -/
theorem dspr_B_dsprF_fors_eq {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    SM_DT_DSPR_Success (B_dsprF_fors pr sfStage adv) =
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNoSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] ∧
    SM_DT_DSPR_SPProbability (B_dsprF_fors pr sfStage adv) =
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] := by
  set prob := Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) .F) pr.collection (qForsLeaf vp)
  -- Shared Stage-1 + Stage-2 distribution evaluation for both `Experiment` and `SPExperiment`!
  have hboth : ∀ (check : pr.PkSeed → List (Adrs × pr.MemberMsg .F) → ℕ × Bool → Bool),
      (do
        let pk ← prob.th.seedGen
        let r ← (simulateQ (SM_DT_DSPR_oracles prob pk)
          (B_dsprF_fors pr sfStage adv).choose).run ([], [])
        let jb ← (B_dsprF_fors pr sfStage adv).guess r.1 pk
        return check pk r.2.1 jb) =ᵈ
      (do
        let pk ← $ᵗ pr.PkSeed
        let d ← sfStage.g₁
        let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        let pkSl := slRootDet pr pk u
        let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl (slSignDet pr pk pkSl u)
        let Q := routedTargets pr pk u .F isForsLeaf
        let jb : ℕ × Bool :=
          match candForsPre pr pk u res.1 res.2 with
          | none => (Q.length, false)
          | some (aLeaf, val) =>
              let j := (Q.map Prod.fst).idxOf aLeaf
              match Q[j]? with
              | some (_, x) => if val = x then (j, false) else (Q.length, false)
              | none => (Q.length, false)
        return check pk Q jb) := by
    intro check
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B_dsprF_fors]
    rw [show SM_DT_DSPR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_DSPR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    rw [← show SM_DT_DSPR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_DSPR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    obtain ⟨⟨qs₀, tws₀⟩, ⟨hqs₀, htws₀⟩, hsf⟩ := sfStage.sfRun_spec
      (SM_DT_DSPR_oracles prob pk) (sfDsprCall pr) pk
      (fun s => s.1 = [] ∧ ∀ t ∈ s.2, Scheme.IsStateful t)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg s hsf ⟨hqs, _⟩ => by
        rcases s with ⟨qs, tws⟩; dsimp only at hqs; subst hqs
        unfold sfDsprCall
        simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_DSPR_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          collectionOracle, StateT.run_get, pure_bind, TweakReserved, List.not_mem_nil,
          false_and, exists_false, ↓reduceIte, StateT.run_set, Option.getD_some]
        rfl)
      (fun s a ⟨hqs, htws⟩ hsf => ⟨hqs, fun t ht => by
        rcases List.mem_append.1 ht with ht1 | ht2
        · exact htws t ht1
        · simp only [List.mem_singleton] at ht2; subst ht2; exact hsf⟩)
      d hd ([], []) ⟨rfl, fun _ h => by simp at h⟩
    dsimp only at hqs₀; subst hqs₀
    have hsf' : (simulateQ (SM_DT_DSPR_oracles prob pk)
        (sfStage.sfRun (sfDsprCall pr) d)).run ([], []) = pure (sfStage.sfDet d pk, ([], tws₀)) := hsf
    simp only [simulateQ_bind, StateT.run_bind, hsf', pure_bind, bind_assoc]
    rw [show SM_DT_DSPR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_DSPR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    rw [Fxmss.simulateQ_add_liftM_run, bind_map_left]
    refine EvalDistEq.bind_right _ fun u => ?_
    rw [← show SM_DT_DSPR_oracles prob pk =
        Fxmss.unifFwd _ + (SM_DT_DSPR_challengeOracle prob pk +
          collectionOracle Prod.fst prob.thColl pk) from rfl]
    obtain ⟨tws', _, hvt⟩ := simulateQ_slVirtualTreeM_routed_dspr pr .F isForsLeaf (qForsLeaf vp)
      (fun _ _ ht u tbl => evalNodeInput_isForsLeaf pr ht u tbl)
      (by rw [countP_slTreeAddresses_isForsLeaf]; exact le_rfl) pk u tws₀ htws₀
    have hrec := simulateQ_recordDspr_run prob pk (slVirtualTreeM pr (routedDsprCall pr) u) [] tws₀
    unfold routedDsprCall at hrec
    rw [hvt, map_pure] at hrec
    change ((simulateQ (SM_DT_DSPR_oracles prob pk)
      ((simulateQ (recordDsprImpl prob)
        (slVirtualTreeM pr (routedDsprCall pr) u)).run [])).run ([], tws₀) >>= _) =ᵈ _
    have hrec' : (simulateQ (SM_DT_DSPR_oracles prob pk)
      ((simulateQ (recordDsprImpl prob)
        (slVirtualTreeM pr (routedDsprCall pr) u)).run [])).run ([], tws₀) =
      pure ((slVirtualTreeDet pr pk u, routedTargets pr pk u .F isForsLeaf),
        (routedTargets pr pk u .F isForsLeaf, tws')) := hrec
    rw [hrec']
    simp only [pure_bind, simulateQ_pure, StateT.run_pure]
    have hvt_spec := slVirtualTreeDet_spec pr pk u
    have hpkSl : (slVirtualTreeDet pr pk u).1 = slRootDet pr pk u :=
      hvt_spec.1.trans (slRootDet_eq_honestVal pr pk u).symm
    have hsign_eq : slSignTable pr (slVirtualTreeDet pr pk u).2 pk (slVirtualTreeDet pr pk u).1 u =
        slSignDet pr pk (slRootDet pr pk u) u := by
      funext msg R; rw [hpkSl]
      exact slSignTable_eq_slSignDet pr pk (slRootDet pr pk u) u hvt_spec.2.2 msg R
    rw [hsign_eq, hpkSl]
  -- Helper: lookup `Q[(Q.map Prod.fst).idxOf aLeaf]? = some (aLeaf, x)` whenever `candForsPre` succeeds
  have hQ_lookup : ∀ pk u out st aLeaf val,
      candForsPre pr pk u out st = some (aLeaf, val) →
      ∃ x, honestInput pr pk u aLeaf = some ⟨.F, x⟩ ∧
        pr.F pk aLeaf val = pr.F pk aLeaf x ∧
        (routedTargets pr pk u .F isForsLeaf)[((routedTargets pr pk u .F isForsLeaf).map Prod.fst).idxOf aLeaf]? =
          some (aLeaf, x) := by
    intro pk u out st aLeaf val hcand
    have hev : EvForsPre pr pk u out st := by
      by_contra hnot; simp [candForsPre, hnot] at hcand
    obtain ⟨_, _, _, _, _, _, hcand', hca, ht, hhi, hF, _⟩ := candForsPre_sound pr pk u out st hev
    rw [hcand] at hcand'; obtain ⟨ha_eq, hval_eq⟩ := Prod.mk.inj (Option.some.inj hcand')
    subst hval_eq
    rw [← ha_eq] at hca ht hhi hF
    set Q := routedTargets pr pk u .F isForsLeaf
    have hQmem := mem_routedTargets_of_honestInput pr pk u .F isForsLeaf hca ht hhi
    have hnd := nodup_map_fst_routedTargets pr pk u .F isForsLeaf
    have ha_mem : aLeaf ∈ Q.map Prod.fst := List.mem_map.2 ⟨(_, _), hQmem, rfl⟩
    have hidx_lt : (Q.map Prod.fst).idxOf aLeaf < Q.length := by
      have := List.idxOf_lt_length_of_mem ha_mem; simpa [List.length_map] using this
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.1 hQmem
    have hk_fst : (Q.map Prod.fst)[k]'(by simpa using hk) = aLeaf := by
      simpa [Q] using congrArg Prod.fst hkeq
    have hkeq_idx : k = (Q.map Prod.fst).idxOf aLeaf := by
      have hinj := List.nodup_iff_injective_getElem.1 hnd
      have heq : (⟨k, by simpa using hk⟩ : Fin (Q.map Prod.fst).length) =
          ⟨(Q.map Prod.fst).idxOf aLeaf, List.idxOf_lt_length_of_mem ha_mem⟩ :=
        hinj (hk_fst.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem ha_mem)).symm)
      exact congrArg Fin.val heq
    refine ⟨_, hhi, hF, ?_⟩
    rw [List.getElem?_eq_getElem hidx_lt]
    subst hkeq_idx
    exact congrArg some hkeq
  constructor
  · -- Part 1: `SM_DT_DSPR_Success = Pr[EvForsPreNoSP]`
    unfold SM_DT_DSPR_Success SM_DT_DSPR_Experiment postPrfExp
    rw [prEvent_eq_evalDist_bind]
    let check1 : pr.PkSeed → List (Adrs × pr.MemberMsg .F) → ℕ × Bool → Bool := fun pk Q jb =>
      match Q[jb.1]? with
      | none => false
      | some (t, m) =>
          @decide (SecondPreimageExists prob.th pk t m ↔ jb.2 = true)
            (@instDecidableIff _ _ (Classical.propDecidable _) _)
    have h1 := evalDistEq_apply_true (hboth check1)
    have hexp_eq : SM_DT_DSPR_Experiment (B_dsprF_fors pr sfStage adv) =
        (do
          let pk ← prob.th.seedGen
          let r ← (simulateQ (SM_DT_DSPR_oracles prob pk)
            (B_dsprF_fors pr sfStage adv).choose).run ([], [])
          let jb ← (B_dsprF_fors pr sfStage adv).guess r.1 pk
          return check1 pk r.2.1 jb) := by
      unfold SM_DT_DSPR_Experiment
      refine bind_congr fun pk => bind_congr fun r => bind_congr fun jb => ?_
      rcases jb with ⟨j, b⟩
      dsimp only [check1]
      cases r.2.1[j]? with
      | none => rfl
      | some tm =>
        rcases tm with ⟨t, m⟩
        dsimp only
        exact congrArg pure (decide_eq_decide.2 Iff.rfl)
    change 𝒟[SM_DT_DSPR_Experiment (B_dsprF_fors pr sfStage adv)] {true} = _
    rw [hexp_eq]
    refine h1.trans ?_
    simp only [check1, bind_assoc, pure_bind]
    refine congrArg (fun m => 𝒟[m] {true}) ?_
    refine bind_congr fun pk => bind_congr fun d => bind_congr fun u => bind_congr fun res => ?_
    congr 1
    cases hcand : candForsPre pr pk u res.1 res.2 with
    | none =>
      simp only [List.getElem?_eq_none le_rfl]
      symm; rw [decide_eq_false_iff_not]
      rintro ⟨_, _, _, hc, _⟩; rw [hcand] at hc; cases hc
    | some av =>
      rcases av with ⟨aLeaf, val⟩
      obtain ⟨x, hhi, hF, hget⟩ := hQ_lookup pk u res.1 res.2 aLeaf val hcand
      simp only [hget]
      by_cases hveq : val = x
      · subst hveq
        simp only [↓reduceIte, hget]
        by_cases hsp : SecondPreimageExists prob.th pk aLeaf val
        · rw [decide_eq_false (by simp [hsp])]
          symm; rw [decide_eq_false_iff_not]
          rintro ⟨a', v', x', hc, hhi', hsp'⟩
          rw [hcand] at hc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
          rw [hhi] at hhi'; have hx : val = x' := by cases Option.some.inj hhi'; rfl
          subst hx; exact hsp' hsp
        · rw [decide_eq_true (by simp [hsp])]
          symm; rw [decide_eq_true_eq]
          exact ⟨aLeaf, val, val, hcand, hhi, hsp⟩
      · simp only [hveq, ↓reduceIte, List.getElem?_eq_none le_rfl]
        symm; rw [decide_eq_false_iff_not]
        rintro ⟨a', v', x', hc, hhi', hsp'⟩
        rw [hcand] at hc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
        rw [hhi] at hhi'; have hx : x = x' := by cases Option.some.inj hhi'; rfl
        subst hx
        exact hsp' ⟨val, Ne.symm hveq, hF.symm⟩
  · -- Part 2: `SM_DT_DSPR_SPProbability = Pr[EvForsPreEqSP]`
    unfold SM_DT_DSPR_SPProbability SM_DT_DSPR_SPExperiment postPrfExp
    rw [prEvent_eq_evalDist_bind]
    let check2 : pr.PkSeed → List (Adrs × pr.MemberMsg .F) → ℕ × Bool → Bool := fun pk Q jb =>
      match Q[jb.1]? with
      | none => false
      | some (t, m) => @decide (SecondPreimageExists prob.th pk t m) (Classical.propDecidable _)
    have h2 := evalDistEq_apply_true (hboth check2)
    have hexp_eq : SM_DT_DSPR_SPExperiment (B_dsprF_fors pr sfStage adv) =
        (do
          let pk ← prob.th.seedGen
          let r ← (simulateQ (SM_DT_DSPR_oracles prob pk)
            (B_dsprF_fors pr sfStage adv).choose).run ([], [])
          let jb ← (B_dsprF_fors pr sfStage adv).guess r.1 pk
          return check2 pk r.2.1 jb) := by
      unfold SM_DT_DSPR_SPExperiment
      refine bind_congr fun pk => bind_congr fun r => bind_congr fun jb => ?_
      rcases jb with ⟨j, b⟩
      dsimp only [check2]
      cases r.2.1[j]? with
      | none => rfl
      | some tm =>
        rcases tm with ⟨t, m⟩
        dsimp only
        exact congrArg pure (decide_eq_decide.2 Iff.rfl)
    change 𝒟[SM_DT_DSPR_SPExperiment (B_dsprF_fors pr sfStage adv)] {true} = _
    rw [hexp_eq]
    refine h2.trans ?_
    simp only [check2, bind_assoc, pure_bind]
    refine congrArg (fun m => 𝒟[m] {true}) ?_
    refine bind_congr fun pk => bind_congr fun d => bind_congr fun u => bind_congr fun res => ?_
    congr 1
    cases hcand : candForsPre pr pk u res.1 res.2 with
    | none =>
      simp only [List.getElem?_eq_none le_rfl]
      symm; rw [decide_eq_false_iff_not]
      rintro ⟨_, _, _, hc, _⟩; rw [hcand] at hc; cases hc
    | some av =>
      rcases av with ⟨aLeaf, val⟩
      obtain ⟨x, hhi, hF, hget⟩ := hQ_lookup pk u res.1 res.2 aLeaf val hcand
      simp only [hget]
      by_cases hveq : val = x
      · subst hveq
        simp only [↓reduceIte, hget]
        by_cases hsp : SecondPreimageExists prob.th pk aLeaf val
        · rw [decide_eq_true hsp]
          symm; rw [decide_eq_true_eq]
          exact ⟨aLeaf, val, val, hcand, hhi, rfl, hsp⟩
        · rw [decide_eq_false hsp]
          symm; rw [decide_eq_false_iff_not]
          rintro ⟨a', v', x', hc, hhi', _, hsp'⟩
          rw [hcand] at hc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
          rw [hhi] at hhi'; have hx : val = x' := by cases Option.some.inj hhi'; rfl
          subst hx; exact hsp hsp'
      · simp only [hveq, ↓reduceIte, List.getElem?_eq_none le_rfl]
        symm; rw [decide_eq_false_iff_not]
        rintro ⟨a', v', x', hc, hhi', hveq', _⟩
        rw [hcand] at hc; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
        rw [hhi] at hhi'; have hx : x = x' := by cases Option.some.inj hhi'; rfl
        subst hx; exact hveq hveq'

/-! ### Fiber-symmetry proof (`Pr[EvForsPreEqSP] ≤ Pr[EvForsPreNe]`) -/

/-- A FORS leaf coordinate `(pos, tree, leaf)` uniquely naming a FORS secret address `aSk` and
its FORS leaf address `aLeaf`. -/
abbrev ForsLeafCoord (vp : ValidatedParams) :=
  BottomPosition vp.sl × Fin vp.sl.params.k × Fin (2 ^ vp.sl.params.a)

def forsCoordLeafAdrs (c : ForsLeafCoord vp) : Adrs :=
  forsNodeAdrs c.1.forsAdrs 0 (c.2.1.val * 2 ^ vp.sl.params.a + c.2.2.val)

def forsCoordSkAdrs (c : ForsLeafCoord vp) : SlSecAdrs vp :=
  ⟨forsSkAdrs c.1.forsAdrs (c.2.1.val * 2 ^ vp.sl.params.a + c.2.2.val),
    List.mem_toFinset.2 (mem_slSecretList (b := forsCoordLeafAdrs c)
      ((mem_constructionAddresses_iff _).2 (Or.inl (by
        simpa [forsCoordLeafAdrs, SLHDSA.Params.t] using
          mem_forsLeafAddresses vp.sl c.1 c.2.1 ⟨c.2.2.val, by simp [SLHDSA.Params.t]⟩)))
      (by rw [forsCoordLeafAdrs, childAdrs_forsNodeAdrs_zero]; simp))⟩

/-- Does a signing query `(R, (pk, pkSl, m))` open the FORS leaf coordinate `c`? -/
def queryOpensCoord (pk : pr.PkSeed) (pkSl : pr.Y) (c : ForsLeafCoord vp)
    (m : List Byte) (R : pr.Y) : Bool :=
  let d := Notions.itsrG (slHmsg pr) (slMap vp) (R, (pk, pkSl, m))
  decide (d.1 = c.1 ∧ d.2 c.2.1 = c.2.2)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.PkSeed] in
/-- If `u₁, u₂` agree everywhere except possibly at `forsCoordSkAdrs c`, AND have the same
`pr.F pk (forsCoordLeafAdrs c)` image, then `honestVal pr pk u₁ a = honestVal pr pk u₂ a` for
EVERY address `a : Adrs`! -/
theorem honestVal_eq_of_same_fiber (pk : pr.PkSeed) (c : ForsLeafCoord vp)
    (u₁ u₂ : SlSecAdrs vp → pr.Y)
    (hother : ∀ a : SlSecAdrs vp, a ≠ forsCoordSkAdrs c → u₁ a = u₂ a)
    (hfiber : pr.F pk (forsCoordLeafAdrs c) (u₁ (forsCoordSkAdrs c)) =
      pr.F pk (forsCoordLeafAdrs c) (u₂ (forsCoordSkAdrs c))) :
    ∀ a : Adrs, honestVal pr pk u₁ a = honestVal pr pk u₂ a := by
  have haux : ∀ fuel a, honestValAux pr pk u₁ fuel a = honestValAux pr pk u₂ fuel a := by
    intro fuel; induction fuel with
    | zero => intro _; rfl
    | succ fuel ih =>
      intro a
      rcases a with ⟨l, tr, ty, w1, w2, w3⟩
      rcases ty with _ | _ | _ | _ | _ | ty'
      · simp only [honestValAux]
        split_ifs with hw3
        · congr 1; unfold slSecOf
          split_ifs with hm
          · exact hother ⟨_, hm⟩ (fun h => by
              have hty := congrArg (fun x : SlSecAdrs vp => x.1.type) h
              have h1 : (wotsSkAdrs ⟨l, tr, 0, w1, w2, w3⟩ w2).type = 5 := rfl
              have h2 : (forsCoordSkAdrs c).1.type = 6 := rfl
              rw [h1, h2] at hty; omega)
          · rfl
        · congr 1; exact ih _
      · simp only [honestValAux]
        congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]; exact ih _
      · simp only [honestValAux]
        split_ifs with h0 h1
        · rfl
        · congr 1 <;> exact ih _
        · congr 1 <;> exact ih _
      · simp only [honestValAux]
        split_ifs with hw2
        · subst hw2
          by_cases hleaf : (⟨l, tr, 3, w1, 0, w3⟩ : Adrs) = forsCoordLeafAdrs c
          · have hw3 : w3 = (forsCoordLeafAdrs c).word3 := congrArg Adrs.word3 hleaf
            rw [hleaf, hw3]
            have hsk : forsSkAdrs (forsCoordLeafAdrs c) (forsCoordLeafAdrs c).word3 =
                (forsCoordSkAdrs c).1 := by
              simp [forsCoordLeafAdrs, forsCoordSkAdrs, forsNodeAdrs, forsSkAdrs,
                Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setKeyPairAddress,
                Adrs.setTypeAndClear, Adrs.getKeyPairAddress]
            rw [hsk]
            simp only [slSecOf, (forsCoordSkAdrs c).2, ↓reduceDIte]
            exact hfiber
          · congr 1; unfold slSecOf
            split_ifs with hm
            · refine hother ⟨_, hm⟩ fun heq => hleaf ?_
              have hval := congrArg Subtype.val heq
              have hl := congrArg Adrs.layer hval
              have htr := congrArg Adrs.tree hval
              have hw1 := congrArg Adrs.word1 hval
              have hw3 := congrArg Adrs.word3 hval
              simp only [forsCoordSkAdrs, forsSkAdrs, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
                Adrs.setTypeAndClear, Adrs.getKeyPairAddress] at hl htr hw1 hw3
              unfold forsCoordLeafAdrs forsNodeAdrs
              rcases c with ⟨pos, ti, li⟩
              simp only [Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode]
              cases hfa : pos.forsAdrs with
              | mk fl ft fty fw1 fw2 fw3 =>
                simp only [hfa] at hl htr hw1 hw3
                subst hl; subst htr; subst hw1; subst hw3; rfl
            · rfl
        · congr 1 <;> exact ih _
      · simp only [honestValAux]
        congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]; exact ih _
      · rfl
  intro a; exact haux _ a

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.PkSeed] in
/-- If `u₁, u₂` agree everywhere except possibly at `forsCoordSkAdrs c`, have the same `F` image at
`forsCoordLeafAdrs c`, AND `(m, R)` does NOT open `c`, then `slSignDet` produces the EXACT same
signature! -/
theorem slSignDet_eq_of_same_fiber_not_opened (pk : pr.PkSeed) (c : ForsLeafCoord vp)
    (u₁ u₂ : SlSecAdrs vp → pr.Y)
    (hother : ∀ a : SlSecAdrs vp, a ≠ forsCoordSkAdrs c → u₁ a = u₂ a)
    (hfiber : pr.F pk (forsCoordLeafAdrs c) (u₁ (forsCoordSkAdrs c)) =
      pr.F pk (forsCoordLeafAdrs c) (u₂ (forsCoordSkAdrs c)))
    (m : List Byte) (R : pr.Y)
    (hno : queryOpensCoord pr pk (slRootDet pr pk u₁) c m R = false) :
    slSignDet pr pk (slRootDet pr pk u₁) u₁ m R =
      slSignDet pr pk (slRootDet pr pk u₂) u₂ m R := by
  have hhon := honestVal_eq_of_same_fiber pr pk c u₁ u₂ hother hfiber
  have hpk : slRootDet pr pk u₁ = slRootDet pr pk u₂ := by
    rw [slRootDet_eq_honestVal, slRootDet_eq_honestVal, hhon]
  rw [← hpk]
  -- Compare via `slSignTable` on `fun a => some (honestVal pr pk u₁ a)`!
  have htbl₁ : TblComplete pr pk u₁ (fun a => some (honestVal pr pk u₁ a)) := fun _ _ => rfl
  have htbl₂ : TblComplete pr pk u₂ (fun a => some (honestVal pr pk u₁ a)) := fun a _ => by
    dsimp only; rw [hhon]
  rw [← slSignTable_eq_slSignDet pr pk _ u₁ htbl₁, ← slSignTable_eq_slSignDet pr pk _ u₂ htbl₂]
  unfold slSignTable
  -- In `slSignTable`, the ONLY secrets read are:
  -- (a) `WOTS_PRF` (`type = 5 ≠ 6`) — identical by `hother`
  -- (b) `forsSkAdrs parts.forsAdrs (i * 2^a + forsIdx ... i)` — all `≠ (forsCoordSkAdrs c).1` by `hno`!
  set parts := splitDigest vp.sl.params (pr.HmsgSl R pk (slRootDet pr pk u₁) m)
  have hsk_wots : ∀ (a : Adrs), a.type = 5 → slSecOf pr u₁ a = slSecOf pr u₂ a := by
    intro a ha; unfold slSecOf; split_ifs with hm
    · exact hother ⟨a, hm⟩ (fun h => by
        have hty := congrArg (fun x : SlSecAdrs vp => x.1.type) h
        have h2 : (forsCoordSkAdrs c).1.type = 6 := rfl
        rw [ha, h2] at hty; omega)
    · rfl
  have hsk_fors : ∀ (i : Fin vp.sl.params.k),
      slSecOf pr u₁ (forsSkAdrs parts.forsAdrs (forsSigLeafIndex vp.sl.params parts.md.toList i.val)) =
      slSecOf pr u₂ (forsSkAdrs parts.forsAdrs (forsSigLeafIndex vp.sl.params parts.md.toList i.val)) := by
    intro i; unfold slSecOf; split_ifs with hm
    · refine hother ⟨_, hm⟩ fun heq => ?_
      have hval := congrArg Subtype.val heq
      have htr := congrArg Adrs.tree hval
      have hkp := congrArg Adrs.getKeyPairAddress hval
      have hw3 := congrArg Adrs.word3 hval
      simp only [forsCoordSkAdrs, forsSkAdrs, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.getKeyPairAddress] at htr hkp hw3
      rw [forsSigLeafIndex_eq] at hw3
      have hpos_eq : BottomPosition.ofDigestParts vp.sl parts = c.1 := by
        have h1 : (BottomPosition.ofDigestParts vp.sl parts).forsAdrs.tree = c.1.forsAdrs.tree := by
          rw [BottomPosition.forsAdrs_ofDigestParts]; exact htr
        have h2 : (BottomPosition.ofDigestParts vp.sl parts).forsAdrs.getKeyPairAddress =
            c.1.forsAdrs.getKeyPairAddress := by
          rw [BottomPosition.forsAdrs_ofDigestParts]; exact hkp
        exact bottomPosition_ext_of_forsAdrs h1 h2
      have hlt₁ : forsIdx vp.sl.params parts.md.toList i.val < 2 ^ vp.sl.params.a := by
        simpa [SLHDSA.Params.t] using forsIdx_lt vp.sl.params parts.md.toList i.val
      have hlt₂ : c.2.2.val < 2 ^ vp.sl.params.a := c.2.2.isLt
      have h2pos : 0 < 2 ^ vp.sl.params.a := Nat.two_pow_pos _
      have hi_eq : i.val = c.2.1.val := by
        have hdiv := congrArg (· / 2 ^ vp.sl.params.a) hw3
        simp only [Nat.mul_comm _ (2 ^ vp.sl.params.a), Nat.mul_add_div h2pos,
          Nat.div_eq_of_lt hlt₁, Nat.div_eq_of_lt hlt₂, Nat.add_zero] at hdiv
        exact hdiv
      have hidx_eq : forsIdx vp.sl.params parts.md.toList i.val = c.2.2.val := by
        have hmod := congrArg (· % 2 ^ vp.sl.params.a) hw3
        simp only [Nat.mul_comm _ (2 ^ vp.sl.params.a), Nat.mul_add_mod,
          Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hmod
        exact hmod
      have hi_fin : i = c.2.1 := Fin.ext hi_eq
      subst hi_fin
      simp only [queryOpensCoord, Notions.itsrG, slHmsg, slMap] at hno
      exact (of_decide_eq_false hno) ⟨hpos_eq, Fin.ext hidx_eq⟩
    · rfl
  -- Now compare `slSignTable` outputs componentwise: `fors` uses `hsk_fors` (and `tablePubQ` ignores `u`),
  -- and `hypertree` uses `hsk_wots` (and `tablePubQ` ignores `u`)!
  simp only [SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM, SLHDSA.PublicHash.hmsg,
    HasQuery.query, Id.run_bind, Id.run_pure]
  have hfors_sig :
      Id.run (letI := tablePubQ pr (fun a => some (honestVal pr pk u₁ a)) Id
        SLHDSA.forsSignWithSecretM pr.toSLHDSA.core (fun a => pure (slSecOf pr u₁ a))
          parts.md.toList pk parts.forsAdrs) =
      Id.run (letI := tablePubQ pr (fun a => some (honestVal pr pk u₁ a)) Id
        SLHDSA.forsSignWithSecretM pr.toSLHDSA.core (fun a => pure (slSecOf pr u₂ a))
          parts.md.toList pk parts.forsAdrs) := by
    simp only [SLHDSA.forsSignWithSecretM, SLHDSA.forsSignWithSecret, idRun_ofFnM]
    apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn, Id.run_bind, Id.run_pure]
    have hsk_i : slSecOf pr u₁ (forsSkAdrs parts.forsAdrs (i * 2 ^ vp.sl.params.a + forsIdx vp.sl.params parts.md.toList i)) =
        slSecOf pr u₂ (forsSkAdrs parts.forsAdrs (i * 2 ^ vp.sl.params.a + forsIdx vp.sl.params parts.md.toList i)) := by
      have h := hsk_fors ⟨i, hi⟩
      rwa [forsSigLeafIndex_eq] at h
    have hauth_indep : ∀ (z t : ℕ),
        Id.run (PerfectMerkleTree.merkleRootM
          (fun j => SLHDSA.forsLeafWithSecret pr.toSLHDSA.core
            (fun a _ => (pure ((some (honestVal pr pk u₁ a)).getD default) : Id pr.Y))
            (fun a => pure (slSecOf pr u₁ a)) parts.forsAdrs j)
          (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (forsNodeAdrs parts.forsAdrs z t))).getD default) : Id pr.Y))
          z t) =
        Id.run (PerfectMerkleTree.merkleRootM
          (fun j => SLHDSA.forsLeafWithSecret pr.toSLHDSA.core
            (fun a _ => (pure ((some (honestVal pr pk u₁ a)).getD default) : Id pr.Y))
            (fun a => pure (slSecOf pr u₂ a)) parts.forsAdrs j)
          (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (forsNodeAdrs parts.forsAdrs z t))).getD default) : Id pr.Y))
          z t) := by
      intro z; induction z with
      | zero => intro t; rfl
      | succ z _ => intro t; simp only [PerfectMerkleTree.merkleRootM, Id.run_bind]
    have hia : ∀ (idx k : ℕ),
        Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (fun j => SLHDSA.forsLeafWithSecret pr.toSLHDSA.core
            (fun a _ => (pure ((some (honestVal pr pk u₁ a)).getD default) : Id pr.Y))
            (fun a => pure (slSecOf pr u₁ a)) parts.forsAdrs j)
          (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (forsNodeAdrs parts.forsAdrs z t))).getD default) : Id pr.Y))
          idx k) =
        Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (fun j => SLHDSA.forsLeafWithSecret pr.toSLHDSA.core
            (fun a _ => (pure ((some (honestVal pr pk u₁ a)).getD default) : Id pr.Y))
            (fun a => pure (slSecOf pr u₂ a)) parts.forsAdrs j)
          (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (forsNodeAdrs parts.forsAdrs z t))).getD default) : Id pr.Y))
          idx k) := by
      intro idx k; induction k with
      | zero => rfl
      | succ k ihk =>
        simp only [PerfectMerkleTree.intrinsicAuthPathM, Id.run_bind, Id.run_pure, ihk, hauth_indep]
    exact congrArg₂ SLHDSA.ForsTreeSigCore.mk hsk_i (hia _ _)
  have hht_sig : ∀ (layers : ℕ) (p0 : LayerPosition vp.sl) (hrem : p0.layer.val + layers = vp.sl.params.d)
      (rf : Bool) (m0 : pr.Y),
      Id.run (letI := tablePubQ pr (fun a => some (honestVal pr pk u₁ a)) Id
        SLHDSA.GeneralHypertree.signFromPositionWithSecret (vp := vp.sl) pr.toSLHDSA.core
          (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
          (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
          (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
          (fun a => pure (slSecOf pr u₁ a)) rf p0 layers hrem m0) =
      Id.run (letI := tablePubQ pr (fun a => some (honestVal pr pk u₁ a)) Id
        SLHDSA.GeneralHypertree.signFromPositionWithSecret (vp := vp.sl) pr.toSLHDSA.core
          (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
          (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
          (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
          (fun a => pure (slSecOf pr u₂ a)) rf p0 layers hrem m0) := by
    have hxmss : ∀ (m0 : pr.Y) (a : Adrs) (idx : ℕ),
        Id.run (letI := tablePubQ pr (fun a => some (honestVal pr pk u₁ a)) Id
          SLHDSA.xmssSignWithSecret pr.toSLHDSA.core
            (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
            (fun b => pure (slSecOf pr u₁ b)) m0 a idx) =
        Id.run (letI := tablePubQ pr (fun a => some (honestVal pr pk u₁ a)) Id
          SLHDSA.xmssSignWithSecret pr.toSLHDSA.core
            (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
            (fun b => pure (slSecOf pr u₂ b)) m0 a idx) := by
      intro m0 a idx
      simp only [SLHDSA.xmssSignWithSecret, SLHDSA.wotsSignWithSecret, Id.run_bind, Id.run_pure,
        idRun_ofFnM]
      have hmr : ∀ z t,
          Id.run (PerfectMerkleTree.merkleRootM
            (fun j => SLHDSA.xmssLeafWithSecret pr.toSLHDSA.core
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b => pure (slSecOf pr u₁ b)) a j)
            (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (xmssNodeAdrs a z t))).getD default) : Id pr.Y)) z t) =
          Id.run (PerfectMerkleTree.merkleRootM
            (fun j => SLHDSA.xmssLeafWithSecret pr.toSLHDSA.core
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b => pure (slSecOf pr u₂ b)) a j)
            (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (xmssNodeAdrs a z t))).getD default) : Id pr.Y)) z t) := by
        intro z; induction z with
        | zero =>
          intro t
          simp only [PerfectMerkleTree.merkleRootM, SLHDSA.xmssLeafWithSecret,
            SLHDSA.wotsPkGenWithSecret, SLHDSA.wotsPkGenTopsWithSecret, Id.run_bind, Id.run_pure]
        | succ z _ => intro t; simp only [PerfectMerkleTree.merkleRootM, Id.run_bind]
      have hia : ∀ k,
          Id.run (PerfectMerkleTree.intrinsicAuthPathM
            (fun j => SLHDSA.xmssLeafWithSecret pr.toSLHDSA.core
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b => pure (slSecOf pr u₁ b)) a j)
            (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (xmssNodeAdrs a z t))).getD default) : Id pr.Y)) idx k) =
          Id.run (PerfectMerkleTree.intrinsicAuthPathM
            (fun j => SLHDSA.xmssLeafWithSecret pr.toSLHDSA.core
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b _ => (pure ((some (honestVal pr pk u₁ b)).getD default) : Id pr.Y))
              (fun b => pure (slSecOf pr u₂ b)) a j)
            (fun z t _ _ => (pure ((some (honestVal pr pk u₁ (xmssNodeAdrs a z t))).getD default) : Id pr.Y)) idx k) := by
        intro k; induction k with
        | zero => rfl
        | succ k ihk =>
          simp only [PerfectMerkleTree.intrinsicAuthPathM, Id.run_bind, Id.run_pure, ihk, hmr]
      congr 1
      · apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
        rw [hsk_wots _ rfl]
    intro layers; induction layers using Nat.twoStepInduction with
    | zero => intro _ _ _ _; rfl
    | one =>
      intro p0 hrem rf m0
      simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret]
      cases rf <;> simp only [↓reduceIte, Bool.false_eq_true, Id.run_bind, Id.run_pure, hxmss]
    | more layers _ ih =>
      intro p0 hrem rf m0
      simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret, Id.run_bind, hxmss]
      rw [ih]
  exact congrArg₂ (fun f h => (⟨R, f, h⟩ : Stateless.Sig pr)) hfors_sig
    (hht_sig vp.sl.params.d (LayerPosition.initial vp.sl parts) (by simp) (vp.sl.params.d == 1) _)

/-- Truncated signing function at coordinate `c`: if `(m, R)` opens `c`, signs with `u[aSk := default]`
(never reading `u aSk`); otherwise signs with `u`. -/
def truncSign (pk : pr.PkSeed) (c : ForsLeafCoord vp) (u : SlSecAdrs vp → pr.Y)
    (m : List Byte) (R : pr.Y) : Stateless.Sig pr :=
  if queryOpensCoord pr pk (slRootDet pr pk u) c m R then
    slSignDet pr pk (slRootDet pr pk u) (Function.update u (forsCoordSkAdrs c) default) m R
  else
    slSignDet pr pk (slRootDet pr pk u) u m R

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.PkSeed] in
/-- `truncSign` depends on `u` at `forsCoordSkAdrs c` ONLY through `pr.F pk (forsCoordLeafAdrs c) (u aSk)`! -/
theorem truncSign_eq_of_same_fiber (pk : pr.PkSeed) (c : ForsLeafCoord vp)
    (u₁ u₂ : SlSecAdrs vp → pr.Y)
    (hother : ∀ a : SlSecAdrs vp, a ≠ forsCoordSkAdrs c → u₁ a = u₂ a)
    (hfiber : pr.F pk (forsCoordLeafAdrs c) (u₁ (forsCoordSkAdrs c)) =
      pr.F pk (forsCoordLeafAdrs c) (u₂ (forsCoordSkAdrs c))) :
    truncSign pr pk c u₁ = truncSign pr pk c u₂ := by
  have hhon := honestVal_eq_of_same_fiber pr pk c u₁ u₂ hother hfiber
  have hpk : slRootDet pr pk u₁ = slRootDet pr pk u₂ := by
    rw [slRootDet_eq_honestVal, slRootDet_eq_honestVal, hhon]
  funext m R
  unfold truncSign
  rw [← hpk]
  by_cases hop : queryOpensCoord pr pk (slRootDet pr pk u₁) c m R = true
  · simp only [hop, ↓reduceIte]
    have hupd : Function.update u₁ (forsCoordSkAdrs c) default =
        Function.update u₂ (forsCoordSkAdrs c) default := by
      funext a
      by_cases ha : a = forsCoordSkAdrs c
      · subst ha; simp
      · simp [Function.update_of_ne ha, hother a ha]
    rw [hupd]
  · simp only [Bool.not_eq_true] at hop
    simp only [hop, Bool.false_eq_true, ↓reduceIte]
    have h := slSignDet_eq_of_same_fiber_not_opened pr pk c u₁ u₂ hother hfiber m R hop
    rwa [← hpk] at h

omit [Fintype pr.Y] [Inhabited pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] in
/-- Monotonicity of `itLog` across `slSignImpl`: any entry already in `s.itLog` remains in `r.2.itLog`. -/
theorem itLog_subset_of_mem_support (pk : pr.PkSeed) (pkSl : pr.Y)
    (signFn : List Byte → pr.Y → Stateless.Sig pr)
    {α : Type} (oa : OracleComp (SlAdvSpec pr) α) :
    ∀ s, ∀ r ∈ support ((simulateQ (slSignImpl pr pk pkSl signFn) oa).run s),
      ∀ e ∈ s.itLog, e ∈ r.2.itLog := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s r hr e he
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact he
  | query_bind t k ih =>
    intro s r hr e he
    rcases t with n | m
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slSignImpl_inl,
        bind_map_left, mem_support_bind_iff] at hr
      obtain ⟨u, _, hr⟩ := hr
      exact ih u s r hr e he
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slSignImpl_inr,
        bind_assoc, mem_support_bind_iff] at hr
      obtain ⟨optRand, _, hr⟩ := hr
      cases hlook : s.rnd (optRand, m) with
      | some R =>
        rw [hlook] at hr
        simp only [support_pure, Set.mem_singleton_iff, exists_eq_left] at hr
        exact ih (signFn m R) { s with log := s.log ++ [m] } r hr e he
      | none =>
        rw [hlook] at hr
        obtain ⟨⟨σ, s'⟩, h1, hr⟩ := hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h1
        obtain ⟨R, _, rfl, rfl⟩ := h1
        exact ih (signFn m R) _ r hr e (List.mem_append_left _ he)

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] in
/-- On any event `P (out, st)` that (on states satisfying `SlSignInv`) implies NO entry of `st.itLog`
opens `c`, running `adv` with `slSignDet` has the EXACT same probability as running `adv` with
`truncSign`! -/
theorem runPostPrf_truncSign_eq {D E : Type} {qs : ℕ} (adv : PostPrfAdv pr D E qs)
    (d : D) (sf : E) (pk : pr.PkSeed) (c : ForsLeafCoord vp) (u : SlSecAdrs vp → pr.Y)
    (P : Option (List Byte × Stateless.Sig pr) × SlSignSt pr → Prop)
    (hP : ∀ res, SlSignInv pr pk (slRootDet pr pk u) res.2 → P res → ∀ e ∈ res.2.itLog,
      queryOpensCoord pr pk (slRootDet pr pk u) c e.2.2.2 e.1 = false) :
    Pr{let res ← runPostPrf pr adv d sf pk (slRootDet pr pk u) (slSignDet pr pk (slRootDet pr pk u) u)}[P res] =
      Pr{let res ← runPostPrf pr adv d sf pk (slRootDet pr pk u) (truncSign pr pk c u)}[P res] := by
  set pkSl := slRootDet pr pk u
  have hbind_eq : ∀ {α : Type} (m : ProbComp α) (f g : α → ProbComp Bool),
      (∀ a ∈ support m, 𝒟[f a] {true} = 𝒟[g a] {true}) →
      𝒟[m >>= f] {true} = 𝒟[m >>= g] {true} := fun m f g hfg =>
    le_antisymm
      (evalDist_bind_apply_mono_of_support m f g (measurableSet_singleton true) fun a ha => (hfg a ha).le)
      (evalDist_bind_apply_mono_of_support m g f (measurableSet_singleton true) fun a ha => (hfg a ha).ge)
  have hzero_of_open : ∀ {α : Type} (oa : OracleComp (SlAdvSpec pr) α) (signFn : List Byte → pr.Y → Stateless.Sig pr)
      (s : SlSignSt pr) (Q : α × SlSignSt pr → Prop),
      SlSignInv pr pk pkSl s →
      (∃ e ∈ s.itLog, queryOpensCoord pr pk pkSl c e.2.2.2 e.1 = true) →
      (∀ r, SlSignInv pr pk pkSl r.2 → Q r → ∀ e ∈ r.2.itLog, queryOpensCoord pr pk pkSl c e.2.2.2 e.1 = false) →
      𝒟[(simulateQ (slSignImpl pr pk pkSl signFn) oa).run s >>= fun r => pure (decide (Q r))] {true} = 0 := by
    intro α oa signFn s Q hinv ⟨e, he, hop⟩ hQ
    refine le_antisymm ?_ bot_le
    have h0 : 𝒟[(simulateQ (slSignImpl pr pk pkSl signFn) oa).run s >>= fun _ => (pure false : ProbComp Bool)] {true} = 0 := by
      simp
    rw [← h0]
    refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun r hr => ?_
    have hinv_r := slSignInv_of_mem_support pr pk pkSl signFn oa s hinv r hr
    have hnotQ : ¬ Q r := fun hqr => by
      have hf := hQ r hinv_r hqr e (itLog_subset_of_mem_support pr pk pkSl signFn oa s r hr e he)
      rw [hop] at hf; cases hf
    simp [hnotQ]
  have haux : ∀ {α : Type} (oa : OracleComp (SlAdvSpec pr) α) (s : SlSignSt pr)
      (Q : α × SlSignSt pr → Prop),
      SlSignInv pr pk pkSl s →
      (∀ e ∈ s.itLog, queryOpensCoord pr pk pkSl c e.2.2.2 e.1 = false) →
      (∀ r, SlSignInv pr pk pkSl r.2 → Q r → ∀ e ∈ r.2.itLog, queryOpensCoord pr pk pkSl c e.2.2.2 e.1 = false) →
      𝒟[(simulateQ (slSignImpl pr pk pkSl (slSignDet pr pk pkSl u)) oa).run s >>=
          fun r => pure (decide (Q r))] {true} =
      𝒟[(simulateQ (slSignImpl pr pk pkSl (truncSign pr pk c u)) oa).run s >>=
          fun r => pure (decide (Q r))] {true} := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s Q _ _ _; simp
    | query_bind t k ih =>
      intro s Q hinv hsno hQ
      rcases t with n | m
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slSignImpl_inl,
          bind_map_left, bind_assoc]
        exact hbind_eq _ _ _ fun x _ => ih x s Q hinv hsno hQ
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, slSignImpl_inr,
          bind_assoc]
        refine hbind_eq ($ᵗ pr.Y) _ _ fun optRand _ => ?_
        cases hlook : s.rnd (optRand, m) with
        | some R =>
          simp only [pure_bind]
          have hnoR : queryOpensCoord pr pk pkSl c m R = false :=
            hsno (R, (pk, pkSl, m)) (hinv.2 optRand m R hlook)
          have hsig_eq : truncSign pr pk c u m R = slSignDet pr pk pkSl u m R := by
            simp [truncSign, pkSl, hnoR]
          rw [hsig_eq]
          have hinv' : SlSignInv pr pk pkSl { s with log := s.log ++ [m] } :=
            ⟨fun e he => ⟨(hinv.1 e he).1, (hinv.1 e he).2.1, List.mem_append_left _ (hinv.1 e he).2.2⟩,
              hinv.2⟩
          exact ih (slSignDet pr pk pkSl u m R) { s with log := s.log ++ [m] } Q hinv' hsno hQ
        | none =>
          simp only [bind_assoc, pure_bind]
          refine hbind_eq ($ᵗ pr.Y) _ _ fun R _ => ?_
          set s' : SlSignSt pr := {
            log := s.log ++ [m]
            rnd := s.rnd.cacheQuery (optRand, m) R
            itLog := s.itLog ++ [(R, (pk, pkSl, m))]
          }
          have hinv' : SlSignInv pr pk pkSl s' := by
            refine ⟨fun e he => ?_, fun o' m' R' h' => ?_⟩
            · rcases List.mem_append.1 he with he1 | he2
              · exact ⟨(hinv.1 e he1).1, (hinv.1 e he1).2.1, List.mem_append_left _ (hinv.1 e he1).2.2⟩
              · simp only [List.mem_singleton] at he2; subst he2
                exact ⟨rfl, rfl, List.mem_append_right _ (by simp)⟩
            · by_cases heq : (o', m') = (optRand, m)
              · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
                simp only [s', OracleSpec.QueryCache.cacheQuery_self, Option.some.injEq] at h'
                subst h'
                exact List.mem_append_right _ (by simp)
              · simp only [s'] at h'
                rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ heq] at h'
                exact List.mem_append_left _ (hinv.2 o' m' R' h')
          by_cases hop : queryOpensCoord pr pk pkSl c m R = true
          · rw [hzero_of_open _ _ s' Q hinv' ⟨(R, (pk, pkSl, m)), List.mem_append_right _ (by simp), hop⟩ hQ,
                hzero_of_open _ _ s' Q hinv' ⟨(R, (pk, pkSl, m)), List.mem_append_right _ (by simp), hop⟩ hQ]
          · simp only [Bool.not_eq_true] at hop
            have hsig_eq : truncSign pr pk c u m R = slSignDet pr pk pkSl u m R := by
              simp [truncSign, pkSl, hop]
            rw [hsig_eq]
            have hsno' : ∀ e ∈ s'.itLog, queryOpensCoord pr pk pkSl c e.2.2.2 e.1 = false := by
              intro e he; rcases List.mem_append.1 he with he1 | he2
              · exact hsno e he1
              · simp only [List.mem_singleton] at he2; subst he2; exact hop
            exact ih (slSignDet pr pk pkSl u m R) s' Q hinv' hsno' hQ
  rw [prEvent_eq_evalDist_bind, prEvent_eq_evalDist_bind]
  exact haux (adv.run d sf pk pkSl) (SlSignSt.init pr) P
    (slSignInv_init pr pk pkSl) (fun _ h => by simp [SlSignSt.init] at h) hP

/-- `forsCoordLeafAdrs` is injective on `ForsLeafCoord vp`. -/
theorem forsCoordLeafAdrs_injective : Function.Injective (forsCoordLeafAdrs (vp := vp)) := by
  rintro ⟨p₁, t₁, l₁⟩ ⟨p₂, t₂, l₂⟩ h
  have htr := congrArg Adrs.tree h
  have hkp := congrArg Adrs.getKeyPairAddress h
  have hw3 := congrArg Adrs.word3 h
  simp only [forsCoordLeafAdrs, forsNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight,
    Adrs.setTypeAndClear, Adrs.getKeyPairAddress] at htr hkp hw3
  have hp : p₁ = p₂ := bottomPosition_ext_of_forsAdrs htr hkp
  subst hp
  have h2pos : 0 < 2 ^ vp.sl.params.a := Nat.two_pow_pos _
  have ht : t₁ = t₂ := Fin.ext (by
    have hdiv := congrArg (· / 2 ^ vp.sl.params.a) hw3
    simp only [Nat.mul_comm _ (2 ^ vp.sl.params.a), Nat.mul_add_div h2pos,
      Nat.div_eq_of_lt l₁.isLt, Nat.div_eq_of_lt l₂.isLt, Nat.add_zero] at hdiv
    exact hdiv)
  subst ht
  have hl : l₁ = l₂ := Fin.ext (by
    have hmod := congrArg (· % 2 ^ vp.sl.params.a) hw3
    simp only [Nat.mul_comm _ (2 ^ vp.sl.params.a), Nat.mul_add_mod,
      Nat.mod_eq_of_lt l₁.isLt, Nat.mod_eq_of_lt l₂.isLt] at hmod
    exact hmod)
  subst hl; rfl

omit [Fintype pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] in
/-- `candForsPre` depends on `u` at `forsCoordSkAdrs c` ONLY through `pr.F pk (forsCoordLeafAdrs c) (u aSk)`! -/
theorem candForsPre_eq_of_same_fiber (pk : pr.PkSeed) (c : ForsLeafCoord vp)
    (u₁ u₂ : SlSecAdrs vp → pr.Y)
    (hother : ∀ a : SlSecAdrs vp, a ≠ forsCoordSkAdrs c → u₁ a = u₂ a)
    (hfiber : pr.F pk (forsCoordLeafAdrs c) (u₁ (forsCoordSkAdrs c)) =
      pr.F pk (forsCoordLeafAdrs c) (u₂ (forsCoordSkAdrs c)))
    (out : Option (List Byte × Stateless.Sig pr)) (st : SlSignSt pr) :
    candForsPre pr pk u₁ out st = candForsPre pr pk u₂ out st := by
  have hhon := honestVal_eq_of_same_fiber pr pk c u₁ u₂ hother hfiber
  have hpk : slRootDet pr pk u₁ = slRootDet pr pk u₂ := by
    rw [slRootDet_eq_honestVal, slRootDet_eq_honestVal, hhon]
  -- Show `forsPkGen`, `forsHonestRoots`, and `forsHonestChildren` are identical for `u₁` and `u₂`!
  have hfors_pk : ∀ b, forsPkGen (prEager pr) u₁ pk b = forsPkGen (prEager pr) u₂ pk b := fun b => by
    rw [← honestVal_eq_forsPkGen, ← honestVal_eq_forsPkGen, hhon]
  have hfors_roots : ∀ b, forsHonestRoots (prEager pr) u₁ pk b = forsHonestRoots (prEager pr) u₂ pk b := fun b => by
    apply Vector.ext; intro i hi
    rw [forsHonestRoots_getElem, forsHonestRoots_getElem, SLHDSA.forsRoot_eq_merkleRoot,
      SLHDSA.forsRoot_eq_merkleRoot, ← honestVal_eq_forsNode, ← honestVal_eq_forsNode, hhon]
  have hfind_fors : ∀ sig md b target,
      slFindForsWitness pr sig md u₁ pk b target =
      slFindForsWitness pr sig md u₂ pk b target := by
    intro sig md b target
    unfold slFindForsWitness slFindForsTreeCollision
    have hleaf : (forsLeaf (prEager pr) u₁ pk b) = (forsLeaf (prEager pr) u₂ pk b) := by
      funext i; rw [← honestVal_eq_forsLeaf, ← honestVal_eq_forsLeaf, hhon]
    rw [hfors_roots b, hleaf]
  -- Now compare `candForsPre`!
  rcases out with _ | ⟨msg, sig⟩
  · simp [candForsPre, EvForsPre, PostPrfWin]
  · have hev_iff : EvForsPre pr pk u₁ (some (msg, sig)) st ↔ EvForsPre pr pk u₂ (some (msg, sig)) st := by
      have hff_iff : ∀ i val,
          extractedWitness pr pk u₁ (some (msg, sig)) st = some (.fors (.fPreimage i val)) ↔
          extractedWitness pr pk u₂ (some (msg, sig)) st = some (.fors (.fPreimage i val)) := by
        intro i val
        unfold extractedWitness; dsimp only
        rw [← hpk]
        set pkSl := slRootDet pr pk u₁
        set target := chosenForsTree pr pk pkSl st.itLog msg sig
        set parts := schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, pkSl⟩
        by_cases hfp : forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
            forsPkGen (prEager pr) u₁ pk parts.forsAdrs
        · have hfp2 : forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
              forsPkGen (prEager pr) u₂ pk parts.forsAdrs := hfp.trans (hfors_pk _)
          dsimp only [pkSl, parts, target] at hfp hfp2 ⊢
          rw [ite_eq_left hfp, ite_eq_left hfp2, hfind_fors]
        · have hfp2 : forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs ≠
              forsPkGen (prEager pr) u₂ pk parts.forsAdrs := fun h => hfp (h.trans (hfors_pk _).symm)
          dsimp only [pkSl, parts, target] at hfp hfp2 ⊢
          rw [ite_eq_right hfp, ite_eq_right hfp2,
              findWitness_eq_hypertree_of_ne u₁ ⟨pk, slRootDet pr pk u₁⟩ msg (toEagerSig pr sig) _ hfp,
              findWitness_eq_hypertree_of_ne u₂ ⟨pk, slRootDet pr pk u₁⟩ msg (toEagerSig pr sig) _ hfp2]
          simp [Option.map_eq_some_iff]
      simp only [EvForsPre, EvItsr, hpk, hff_iff]
    unfold candForsPre
    by_cases h1 : EvForsPre pr pk u₁ (some (msg, sig)) st
    · have h2 : EvForsPre pr pk u₂ (some (msg, sig)) st := hev_iff.1 h1
      simp only [h1, h2, ↓reduceIte, ← hpk]
      obtain ⟨_, _, i, val, _, hw1, _, _, _, _, _, _⟩ := candForsPre_sound pr pk u₁ (some (msg, sig)) st h1
      have hw2 : extractedWitness pr pk u₂ (some (msg, sig)) st = some (.fors (.fPreimage i val)) := by
        unfold extractedWitness at hw1 ⊢; dsimp only at hw1 ⊢
        rw [← hpk]
        set pkSl := slRootDet pr pk u₁
        set target := chosenForsTree pr pk pkSl st.itLog msg sig
        set parts := schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, pkSl⟩
        by_cases hfp : forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
            forsPkGen (prEager pr) u₁ pk parts.forsAdrs
        · have hfp2 := hfp.trans (hfors_pk parts.forsAdrs)
          simp only [hfp, ↓reduceIte] at hw1
          simp only [hfp2, ↓reduceIte, ← hfind_fors]
          exact hw1
        · simp only [hfp, ↓reduceIte] at hw1
          rw [findWitness_eq_hypertree_of_ne u₁ ⟨pk, pkSl⟩ msg (toEagerSig pr sig) target hfp,
              Option.map_eq_some_iff] at hw1
          obtain ⟨_, _, hc⟩ := hw1; cases hc
      rw [hw1, hw2]
    · have h2 : ¬ EvForsPre pr pk u₂ (some (msg, sig)) st := fun h => h1 (hev_iff.2 h)
      simp only [h1, h2, ↓reduceIte]

/-- **Fiber-symmetry inequality ([BHK+19, Claim 23])**:
`Pr[EvForsPreEqSP] ≤ Pr[EvForsPreNe]`. -/
theorem pr_EvForsPreEqSP_le_Ne {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2] := by
  -- Step 1: Partition both events across all FORS leaf coordinates `c : ForsLeafCoord vp`
  let HitC (c : ForsLeafCoord vp) (z : pr.PkSeed × (SlSecAdrs vp → pr.Y) ×
      Option (List Byte × Stateless.Sig pr) × SlSignSt pr) : Prop :=
    ∃ val, candForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2 = some (forsCoordLeafAdrs c, val)
  have hcover : ∀ z, (∃ aLeaf val, candForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2 = some (aLeaf, val)) →
      ∃ c : ForsLeafCoord vp, HitC c z := by
    rintro ⟨pk, u, out, st⟩ ⟨aLeaf, val, hcand⟩
    have hev : EvForsPre pr pk u out st := by
      by_contra hnot; simp [candForsPre, hnot] at hcand
    obtain ⟨msg, sig, i, val', rfl, _, hcand', _, _, _, _, _⟩ := candForsPre_sound pr pk u out st hev
    rw [hcand] at hcand'; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcand')
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    refine ⟨(BottomPosition.ofDigestParts vp.sl parts, i,
      ⟨forsIdx vp.sl.params parts.md.toList i.val, by simpa [SLHDSA.Params.t] using forsIdx_lt vp.sl.params parts.md.toList i.val⟩),
      val, ?_⟩
    rw [hcand]
    congr 1; congr 1
    simp only [forsCoordLeafAdrs, BottomPosition.forsAdrs_ofDigestParts, forsSigLeafIndex_eq]
  have hdisj : ∀ c₁ c₂ : ForsLeafCoord vp, c₁ ≠ c₂ →
      ∀ z, ¬ (HitC c₁ z ∧ HitC c₂ z) := by
    rintro c₁ c₂ hne z ⟨⟨v₁, h1⟩, ⟨v₂, h2⟩⟩
    rw [h1] at h2
    exact hne (forsCoordLeafAdrs_injective (Prod.mk.inj (Option.some.inj h2)).1)
  have hsum_part : ∀ (E : pr.PkSeed × (SlSecAdrs vp → pr.Y) ×
        Option (List Byte × Stateless.Sig pr) × SlSignSt pr → Prop),
      (∀ z, E z → ∃ c : ForsLeafCoord vp, HitC c z) →
      Pr{let z ← postPrfExp pr sfStage adv}[E z] =
        ∑ c : ForsLeafCoord vp, Pr{let z ← postPrfExp pr sfStage adv}[E z ∧ HitC c z] := by
    intro E hcov
    have heq : (fun z => E z) = (fun z => ∃ c ∈ (Finset.univ : Finset (ForsLeafCoord vp)), E z ∧ HitC c z) := by
      funext z; apply propext
      exact ⟨fun hz => let ⟨c, hc⟩ := hcov z hz; ⟨c, Finset.mem_univ c, hz, hc⟩,
        fun ⟨_, _, hz, _⟩ => hz⟩
    rw [show Pr{let z ← postPrfExp pr sfStage adv}[E z] =
        Pr{let z ← postPrfExp pr sfStage adv}[∃ c ∈ (Finset.univ : Finset (ForsLeafCoord vp)), E z ∧ HitC c z]
      from congrArg (fun P => Pr{let z ← postPrfExp pr sfStage adv}[P z]) heq]
    exact prEvent_biUnion_finset (postPrfExp pr sfStage adv) Finset.univ
      (fun c z => E z ∧ HitC c z) (fun c₁ _ c₂ _ hne z ⟨h1, h2⟩ => hdisj c₁ c₂ hne z ⟨h1.2, h2.2⟩)
  rw [hsum_part (fun z => EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2)
        (fun z ⟨aLeaf, val, _, hc, _⟩ => hcover z ⟨aLeaf, val, hc⟩),
      hsum_part (fun z => EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2)
        (fun z ⟨aLeaf, val, _, hc, _⟩ => hcover z ⟨aLeaf, val, hc⟩)]
  -- Step 2: Prove coordinatewise `Pr[EvForsPreEqSP ∧ HitC c] ≤ Pr[EvForsPreNe ∧ HitC c]` for each `c`!
  refine Finset.sum_le_sum fun c _ => ?_
  set aSk := forsCoordSkAdrs c
  set aLeaf := forsCoordLeafAdrs c
  -- Notice: `HitC c z` implies `honestInput pr pk u aLeaf = some ⟨.F, u aSk⟩`, AND no `e ∈ st.itLog` opens `c`!
  have hhi_c : ∀ pk u, honestInput pr pk u aLeaf = some ⟨.F, u aSk⟩ := by
    intro pk u
    rw [show aLeaf = forsNodeAdrs c.1.forsAdrs 0 (c.2.1.val * 2 ^ vp.sl.params.a + c.2.2.val) from rfl,
      honestInput_forsLeaf]
    have hmem_sk : forsSkAdrs c.1.forsAdrs (c.2.1.val * 2 ^ vp.sl.params.a + c.2.2.val) ∈
        (slSecretList vp.sl).toFinset := aSk.2
    simp only [slSecOf, hmem_sk, ↓reduceDIte]
    rfl
  have hnot_open_c : ∀ pk u out st,
      SlSignInv pr pk (slRootDet pr pk u) st →
      (∃ val, candForsPre pr pk u out st = some (aLeaf, val)) →
      ∀ e ∈ st.itLog, queryOpensCoord pr pk (slRootDet pr pk u) c e.2.2.2 e.1 = false := by
    intro pk u out st hinv ⟨val, hcand⟩ e he
    have hev : EvForsPre pr pk u out st := by
      by_contra hnot; simp [candForsPre, hnot] at hcand
    obtain ⟨msg, sig, i, val', rfl, _, hcand', _, _, _, _, hi_eq⟩ := candForsPre_sound pr pk u out st hev
    rw [hcand] at hcand'; obtain ⟨hleaf_eq, _⟩ := Prod.mk.inj (Option.some.inj hcand')
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    have hc_eq : c = (BottomPosition.ofDigestParts vp.sl parts, i,
        ⟨forsIdx vp.sl.params parts.md.toList i.val, by simpa [SLHDSA.Params.t] using forsIdx_lt vp.sl.params parts.md.toList i.val⟩) := by
      apply forsCoordLeafAdrs_injective
      change aLeaf = _
      rw [hleaf_eq]
      simp only [forsCoordLeafAdrs, BottomPosition.forsAdrs_ofDigestParts, forsSigLeafIndex_eq]
    have hnc : ¬ ITSR.Covered (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
        (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg))) := by
      intro hcov
      refine hev.2.1 ⟨hev.1, ?_⟩
      convert hcov
    have hunc := findUncoveredTree_uncovered _ _ hnc
    have he_mem : Notions.itsrG (slHmsg pr) (slMap vp) e ∈
        st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)) :=
      Finset.mem_image.2 ⟨e, List.mem_toFinset.2 he, rfl⟩
    have he_eq : (e.1, (pk, slRootDet pr pk u, e.2.2.2)) = e := by
      rcases e with ⟨eR, epk, epkSl, em⟩
      obtain ⟨h1, h2, _⟩ := hinv.1 _ he
      dsimp only at h1 h2; subst h1; subst h2; rfl
    simp only [queryOpensCoord, decide_eq_false_iff_not, not_and]
    intro h1 h2
    rw [he_eq] at h1 h2
    have hc1 : c.1 = (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg))).1 := by
      rw [hc_eq]; rfl
    have hc2 : c.2.1 = chosenForsTree pr pk (slRootDet pr pk u) st.itLog msg sig := by
      rw [hc_eq]; exact hi_eq
    have hc3 : c.2.2 = (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg))).2 c.2.1 := by
      rw [hc_eq]; rfl
    rw [hc1] at h1
    rw [hc3, hc2] at h2
    have h2' : (Notions.itsrG (slHmsg pr) (slMap vp) e).2
        (findUncoveredTree (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
          (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg)))) =
        (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg))).2
        (findUncoveredTree (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
          (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, slRootDet pr pk u, msg)))) := by
      convert h2 using 2
      · congr 1; ext x; simp
      · congr 1; ext x; simp
    exact hunc _ he_mem h1 h2'
  -- Step 3: Pull out `(pk, d, u)` and resample `x ← $ᵗ pr.Y` at `aSk` via `Repro.resample`!
  let PEq (z : pr.PkSeed × (SlSecAdrs vp → pr.Y) × Option (List Byte × Stateless.Sig pr) × SlSignSt pr) : Prop :=
    EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∧ HitC c z
  let PNe (z : pr.PkSeed × (SlSecAdrs vp → pr.Y) × Option (List Byte × Stateless.Sig pr) × SlSignSt pr) : Prop :=
    EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∧ HitC c z
  change Pr{let z ← postPrfExp pr sfStage adv}[PEq z] ≤ Pr{let z ← postPrfExp pr sfStage adv}[PNe z]
  unfold postPrfExp
  rw [prEvent_eq_evalDist_bind, prEvent_eq_evalDist_bind]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_apply_mono_of_support ($ᵗ pr.PkSeed) _ _ (measurableSet_singleton true) fun pk _ => ?_
  refine evalDist_bind_apply_mono_of_support sfStage.g₁ _ _ (measurableSet_singleton true) fun d _ => ?_
  -- Apply `Repro.resample aSk` on both sides to isolate `x ← $ᵗ pr.Y`!
  have hresL := evalDistEq_apply_true (Repro.resample aSk fun u =>
      runPostPrf pr adv d (sfStage.sfDet d pk) pk (slRootDet pr pk u) (slSignDet pr pk (slRootDet pr pk u) u) >>=
        fun res => pure (@decide (PEq (pk, u, res.1, res.2)) (Classical.propDecidable _)))
  have hresR := evalDistEq_apply_true (Repro.resample aSk fun u =>
      runPostPrf pr adv d (sfStage.sfDet d pk) pk (slRootDet pr pk u) (slSignDet pr pk (slRootDet pr pk u) u) >>=
        fun res => pure (@decide (PNe (pk, u, res.1, res.2)) (Classical.propDecidable _)))
  refine le_trans hresL.symm.le (le_trans ?_ hresR.le)
  -- Swap `x ← $ᵗ pr.Y` and `u ← $ᵗ (SlSecAdrs vp → pr.Y)` so `u` is fixed first, then sum over `x`!
  refine le_trans (evalDistEq_apply_true (EvalDistEq.bind_bind_swap ($ᵗ pr.Y) ($ᵗ (SlSecAdrs vp → pr.Y)) _)).le
    (le_trans ?_ (evalDistEq_apply_true (EvalDistEq.bind_bind_swap ($ᵗ pr.Y) ($ᵗ (SlSecAdrs vp → pr.Y)) _)).symm.le)
  refine evalDist_bind_apply_mono_of_support ($ᵗ (SlSecAdrs vp → pr.Y)) _ _ (measurableSet_singleton true) fun u _ => ?_
  -- Expand `𝒟[($ᵗ pr.Y) >>= f] {true} = (Fintype.card pr.Y : ℝ≥0∞)⁻¹ * ∑ x, 𝒟[f x] {true}`
  have hunif_sum : ∀ (f : pr.Y → ProbComp Bool),
      𝒟[($ᵗ pr.Y) >>= f] {true} = (Fintype.card pr.Y : ℝ≥0∞)⁻¹ * ∑ x : pr.Y, 𝒟[f x] {true} := by
    intro f
    have hEq : ∀ (m : ProbComp Bool), 𝒟[m] {true} = Pr{let b ← m}[b = true] := fun m => by
      rw [prEvent_eq_evalDist_bind]
      congr 1
      simp
    rw [hEq, prEvent_bind_eq_tsum, tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton, hEq]
  rw [hunif_sum, hunif_sum]
  refine mul_le_mul' le_rfl ?_
  -- For fixed `(pk, d, u)`, group the sum over `x : pr.Y` by fibers `y = pr.F pk aLeaf x`!
  let fiberOf (y : pr.Y) : Finset pr.Y := @Finset.filter pr.Y (fun x => pr.F pk aLeaf x = y)
    (fun x => inferInstanceAs (Decidable (pr.F pk aLeaf x = y))) Finset.univ
  have hfibSum : ∀ (F : pr.Y → ℝ≥0∞),
      ∑ x : pr.Y, F x = ∑ y : pr.Y, ∑ x ∈ fiberOf y, F x := fun F =>
    (Finset.sum_fiberwise_of_maps_to (g := fun x : pr.Y => pr.F pk aLeaf x) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) F).symm
  conv_lhs => rw [hfibSum]
  conv_rhs => rw [hfibSum]
  refine Finset.sum_le_sum fun y _ => ?_
  set S_y : Finset pr.Y := fiberOf y
  by_cases hcard : S_y.card ≤ 1
  · -- Fiber has size ≤ 1: NO `x ∈ S_y` has a second preimage, so LHS sum is `0`!
    have hzero : ∀ x ∈ S_y,
        𝒟[do
            let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk
              (slRootDet pr pk (Function.update u aSk x))
              (slSignDet pr pk (slRootDet pr pk (Function.update u aSk x)) (Function.update u aSk x))
            return @decide (PEq (pk, Function.update u aSk x, res.1, res.2)) (Classical.propDecidable _)] {true} = 0 := by
      intro x hx
      have hFx : pr.F pk aLeaf x = y := (Finset.mem_filter.1 hx).2
      have hnoSP : ¬ SecondPreimageExists (pr.member ($ᵗ pr.PkSeed) .F) pk aLeaf x := by
        rintro ⟨x', hne, heq⟩
        have hFx' : pr.F pk aLeaf x' = y := (show pr.F pk aLeaf x' = pr.F pk aLeaf x from heq.symm).trans hFx
        let x'' : pr.Y := x'
        have hx' : x'' ∈ S_y := by
          dsimp only [S_y, fiberOf]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hFx'⟩
        have h2 : 2 ≤ S_y.card := Finset.one_lt_card.2 ⟨x, hx, x'', hx', hne⟩
        omega
      refine le_antisymm ?_ bot_le
      have h0 : 𝒟[runPostPrf pr adv d (sfStage.sfDet d pk) pk (slRootDet pr pk (Function.update u aSk x))
          (slSignDet pr pk (slRootDet pr pk (Function.update u aSk x)) (Function.update u aSk x)) >>=
          fun _ => (pure false : ProbComp Bool)] {true} = 0 := by simp
      rw [← h0]
      refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun res _ => ?_
      have hfalse : ¬ PEq (pk, Function.update u aSk x, res.1, res.2) := by
        rintro ⟨⟨a', v', x', hcand, hhi, _, hsp⟩, ⟨v, hcand_c⟩⟩
        rw [hcand_c] at hcand; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hcand)
        have hhi' := hhi_c pk (Function.update u aSk x)
        rw [hhi] at hhi'
        have hx_eq : x' = x := by
          have h := Sigma.mk.inj_iff.1 (Option.some.inj hhi')
          simpa using eq_of_heq h.2
        subst hx_eq; exact hnoSP hsp
      simp [hfalse]
    rw [Finset.sum_eq_zero hzero]
    exact bot_le
  · -- Fiber has size ≥ 2: pick an arbitrary representative `x₀ ∈ S_y`!
    have hcard2 : 2 ≤ S_y.card := by omega
    obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 (by omega : 0 < S_y.card)
    have hFx₀ : pr.F pk aLeaf x₀ = y := (Finset.mem_filter.1 hx₀).2
    set u₀ := Function.update u aSk x₀
    set pkSl₀ := slRootDet pr pk u₀
    -- Define fiber-invariant probability `p(v)` under `truncSign pr pk c u₀`!
    let pVal (v : pr.Y) : ℝ≥0∞ :=
      Pr{let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl₀ (truncSign pr pk c u₀)}[
        candForsPre pr pk u₀ res.1 res.2 = some (aLeaf, v)]
    -- For every `x ∈ S_y`:
    -- (1) LHS(x) = pVal x
    -- (2) RHS(x) ≥ ∑ v ∈ S_y.erase x, pVal v
    have hL_eq : ∀ x ∈ S_y,
        𝒟[do
            let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk
              (slRootDet pr pk (Function.update u aSk x))
              (slSignDet pr pk (slRootDet pr pk (Function.update u aSk x)) (Function.update u aSk x))
            return @decide (PEq (pk, Function.update u aSk x, res.1, res.2)) (Classical.propDecidable _)] {true} ≤ pVal x := by
      intro x hx
      have hFx : pr.F pk aLeaf x = y := (Finset.mem_filter.1 hx).2
      have hother : ∀ a : SlSecAdrs vp, a ≠ aSk → Function.update u aSk x a = u₀ a := fun a ha => by
        simp [u₀, Function.update_of_ne ha]
      have hfib : pr.F pk aLeaf (Function.update u aSk x aSk) = pr.F pk aLeaf (u₀ aSk) := by
        simp [u₀, hFx, hFx₀]
      have hpk_eq : slRootDet pr pk (Function.update u aSk x) = pkSl₀ := by
        dsimp only [pkSl₀]
        rw [slRootDet_eq_honestVal, slRootDet_eq_honestVal,
          honestVal_eq_of_same_fiber pr pk c _ _ hother hfib]
      have htr_eq : truncSign pr pk c (Function.update u aSk x) = truncSign pr pk c u₀ :=
        truncSign_eq_of_same_fiber pr pk c _ _ hother hfib
      -- First switch `slSignDet` → `truncSign` via `runPostPrf_truncSign_eq`!
      rw [← prEvent_eq_evalDist_bind]
      rw [runPostPrf_truncSign_eq pr adv d (sfStage.sfDet d pk) pk c (Function.update u aSk x)
        (fun res => PEq (pk, Function.update u aSk x, res.1, res.2))
        (fun res hinv ⟨_, hhit⟩ => hnot_open_c pk _ res.1 res.2 hinv hhit)]
      rw [hpk_eq, htr_eq]
      refine prEvent_mono _ _ _ fun res ⟨⟨a', v', x', hcand, hhi, hveq, _⟩, ⟨v, hcand_c⟩⟩ => ?_
      rw [hcand_c] at hcand; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcand)
      have hhi' := hhi_c pk (Function.update u aSk x)
      rw [hhi] at hhi'
      have hx_eq : x' = x := by
        have h := Sigma.mk.inj_iff.1 (Option.some.inj hhi')
        simpa using eq_of_heq h.2
      subst hx_eq; subst hveq
      rw [← candForsPre_eq_of_same_fiber pr pk c _ _ hother hfib]
      exact hcand_c
    have hR_ge : ∀ x ∈ S_y,
        ∑ v ∈ S_y.erase x, pVal v ≤
        𝒟[do
            let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk
              (slRootDet pr pk (Function.update u aSk x))
              (slSignDet pr pk (slRootDet pr pk (Function.update u aSk x)) (Function.update u aSk x))
            return @decide (PNe (pk, Function.update u aSk x, res.1, res.2)) (Classical.propDecidable _)] {true} := by
      intro x hx
      have hFx : pr.F pk aLeaf x = y := (Finset.mem_filter.1 hx).2
      have hother : ∀ a : SlSecAdrs vp, a ≠ aSk → Function.update u aSk x a = u₀ a := fun a ha => by
        simp [u₀, Function.update_of_ne ha]
      have hfib : pr.F pk aLeaf (Function.update u aSk x aSk) = pr.F pk aLeaf (u₀ aSk) := by
        simp [u₀, hFx, hFx₀]
      have hpk_eq : slRootDet pr pk (Function.update u aSk x) = pkSl₀ := by
        dsimp only [pkSl₀]
        rw [slRootDet_eq_honestVal, slRootDet_eq_honestVal,
          honestVal_eq_of_same_fiber pr pk c _ _ hother hfib]
      have htr_eq : truncSign pr pk c (Function.update u aSk x) = truncSign pr pk c u₀ :=
        truncSign_eq_of_same_fiber pr pk c _ _ hother hfib
      rw [← prEvent_eq_evalDist_bind]
      rw [runPostPrf_truncSign_eq pr adv d (sfStage.sfDet d pk) pk c (Function.update u aSk x)
        (fun res => PNe (pk, Function.update u aSk x, res.1, res.2))
        (fun res hinv ⟨_, hhit⟩ => hnot_open_c pk _ res.1 res.2 hinv hhit)]
      rw [hpk_eq, htr_eq]
      -- Disjoint union over `v ∈ S_y.erase x`: `candForsPre u₀ = some (aLeaf, v)` implies `EvForsPreNe ∧ HitC c`!
      set mx0 := runPostPrf pr adv d (sfStage.sfDet d pk) pk pkSl₀ (truncSign pr pk c u₀)
      have hsum_eq : ∑ v ∈ S_y.erase x, pVal v =
          Pr{let res ← mx0}[∃ v ∈ S_y.erase x, candForsPre pr pk u₀ res.1 res.2 = some (aLeaf, v)] := by
        dsimp only [pVal]
        exact (prEvent_biUnion_finset mx0 (S_y.erase x)
          (fun v res => candForsPre pr pk u₀ res.1 res.2 = some (aLeaf, v))
          (fun v₁ _ v₂ _ hne res ⟨h1, h2⟩ => by
            rw [h1] at h2; exact hne (Prod.mk.inj (Option.some.inj h2)).2)).symm
      rw [hsum_eq]
      refine prEvent_mono _ _ _ fun res ⟨v, hv, hcand₀⟩ => ?_
      have hv_ne : v ≠ x := (Finset.mem_erase.1 hv).1
      have hcand_x : candForsPre pr pk (Function.update u aSk x) res.1 res.2 = some (aLeaf, v) := by
        rw [candForsPre_eq_of_same_fiber pr pk c _ _ hother hfib]; exact hcand₀
      refine ⟨⟨aLeaf, v, x, hcand_x, ?_, hv_ne⟩, ⟨v, hcand_x⟩⟩
      simpa using hhi_c pk (Function.update u aSk x)
    -- Now conclude by elementary double-sum counting on the fiber `S_y` (`2 ≤ S_y.card`)!
    calc ∑ x ∈ S_y,
            𝒟[do
                let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk
                  (slRootDet pr pk (Function.update u aSk x))
                  (slSignDet pr pk (slRootDet pr pk (Function.update u aSk x)) (Function.update u aSk x))
                return @decide (PEq (pk, Function.update u aSk x, res.1, res.2)) (Classical.propDecidable _)] {true}
        ≤ ∑ x ∈ S_y, pVal x := Finset.sum_le_sum hL_eq
      _ ≤ ∑ x ∈ S_y, ∑ v ∈ S_y.erase x, pVal v := by
          have hcomm : ∑ x ∈ S_y, ∑ v ∈ S_y.erase x, pVal v =
              ∑ v ∈ S_y, ((S_y.card - 1 : ℕ) : ℝ≥0∞) * pVal v := by
            have hite : ∀ x ∈ S_y, ∑ v ∈ S_y.erase x, pVal v =
                ∑ v ∈ S_y, if v = x then 0 else pVal v := fun x _ => by
              rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
              congr 1; ext v; simp [Finset.mem_erase, and_comm]
            rw [Finset.sum_congr rfl hite, Finset.sum_comm]
            refine Finset.sum_congr rfl fun v hv => ?_
            have hsum_v : ∑ x ∈ S_y, (if v = x then (0 : ℝ≥0∞) else pVal v) =
                ∑ x ∈ S_y.erase v, pVal v := by
              rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
              congr 1; ext x; simp [Finset.mem_erase, eq_comm, and_comm]
            rw [hsum_v, Finset.sum_const, Finset.card_erase_of_mem hv, nsmul_eq_mul]
          rw [hcomm]
          refine Finset.sum_le_sum fun v _ => ?_
          have h1 : (1 : ℝ≥0∞) ≤ ((S_y.card - 1 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast (by omega : 1 ≤ S_y.card - 1)
          simpa using mul_le_mul' h1 (le_refl (pVal v))
      _ ≤ ∑ x ∈ S_y,
            𝒟[do
                let res ← runPostPrf pr adv d (sfStage.sfDet d pk) pk
                  (slRootDet pr pk (Function.update u aSk x))
                  (slSignDet pr pk (slRootDet pr pk (Function.update u aSk x)) (Function.update u aSk x))
                return @decide (PNe (pk, Function.update u aSk x, res.1, res.2)) (Classical.propDecidable _)] {true} :=
          Finset.sum_le_sum hR_ge

/-- **Complete FORS leaf preimage bound ([BHK+19, Claim 23])**:
`Pr[EvForsPre] ≤ 3 * SM_DT_TCR_Advantage (B_tcrF_fors ...) + SM_DT_DSPR_Advantage (B_dsprF_fors ...)`. -/
theorem pr_EvForsPre_le {D E : Type} {qs : ℕ}
    (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[EvForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      3 * SM_DT_TCR_Advantage (B_tcrF_fors pr sfStage adv) +
      SM_DT_DSPR_Advantage (B_dsprF_fors pr sfStage adv) := by
  -- Every `EvForsPre` falls into `EvForsPreNe ∨ EvForsPreEqSP ∨ EvForsPreNoSP`
  have hsplit : Pr{let z ← postPrfExp pr sfStage adv}[EvForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNoSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] := by
    refine le_trans (prEvent_mono _ _
      (fun z => (EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
          EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2) ∨
        EvForsPreNoSP pr z.1 z.2.1 z.2.2.1 z.2.2.2) ?_)
      ((prEvent_or_le _ _ _).trans (add_le_add (prEvent_or_le _ _ _) le_rfl))
    rintro ⟨pk, u, out, st⟩ hev
    obtain ⟨msg, sig, i, val, _, _, hcand, _, _, hhi, _, _⟩ := candForsPre_sound pr pk u out st hev
    set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk (slRootDet pr pk u) msg)
    set idx := forsSigLeafIndex vp.sl.params parts.md.toList i.val
    set aLeaf := forsNodeAdrs parts.forsAdrs 0 idx
    set x : pr.Y := slSecOf pr u (forsSkAdrs parts.forsAdrs idx)
    by_cases hsp : SecondPreimageExists (pr.member ($ᵗ pr.PkSeed) .F) pk aLeaf x
    · by_cases hveq : val = x
      · exact Or.inl (Or.inr ⟨aLeaf, val, x, hcand, hhi, hveq, hsp⟩)
      · exact Or.inl (Or.inl ⟨aLeaf, val, x, hcand, hhi, hveq⟩)
    · exact Or.inr ⟨aLeaf, val, x, hcand, hhi, hsp⟩
  have ⟨hdspr_succ, hdspr_sp⟩ := dspr_B_dsprF_fors_eq pr sfStage adv
  have hdspr_le : Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNoSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] ≤
      Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        SM_DT_DSPR_Advantage (B_dsprF_fors pr sfStage adv) := by
    rw [SM_DT_DSPR_Advantage, hdspr_succ, hdspr_sp]
    exact le_add_tsub
  have hsym := pr_EvForsPreEqSP_le_Ne pr sfStage adv
  have htcr := pr_EvForsPreNe_le pr sfStage adv
  set pNe := Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNe pr z.1 z.2.1 z.2.2.1 z.2.2.2]
  set pEq := Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreEqSP pr z.1 z.2.1 z.2.2.1 z.2.2.2]
  set pNo := Pr{let z ← postPrfExp pr sfStage adv}[EvForsPreNoSP pr z.1 z.2.1 z.2.2.1 z.2.2.2]
  set tcr := SM_DT_TCR_Advantage (B_tcrF_fors pr sfStage adv)
  set dspr := SM_DT_DSPR_Advantage (B_dsprF_fors pr sfStage adv)
  calc Pr{let z ← postPrfExp pr sfStage adv}[EvForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2]
      ≤ pNe + pEq + pNo := hsplit
    _ ≤ pNe + pEq + (pEq + dspr) := add_le_add le_rfl hdspr_le
    _ ≤ tcr + tcr + (tcr + dspr) := add_le_add (add_le_add htcr (hsym.trans htcr))
        (add_le_add (hsym.trans htcr) le_rfl)
    _ = 3 * tcr + dspr := by ring

end ForsPreBound

/-! ## 7. Master Post-PRF Security Theorem (`postPrf_bound`) -/

section MasterTheorem

variable {vp : ValidatedParams} (pr : Primitives vp.params)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]

/-- **Master Post-PRF Security Bound for SLH-DSA (`postPrf_bound`)**:
under `hinj : Function.Injective pr.yToBytes`, for any Stage-1 stateful hook `sfStage` and any
`qs`-query post-PRF adversary `adv`, `Pr[PostPrfWin]` is bounded by the exact 10 post-PRF summands
of Main Paper Theorem 4.3 (`[HK22]`) and Claim 4.16. -/
theorem postPrf_bound (hinj : Function.Injective pr.yToBytes)
    {D E : Type} {qs : ℕ} (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs) :
    Pr{let z ← postPrfExp pr sfStage adv}[PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1] ≤
      Notions.itsrSucc (slHmsg pr) (slMap vp) (B_itsr pr sfStage adv) +
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (B_ud pr sfStage (wotsStage2 pr adv) γ) +
      SM_DT_PRE_Advantage (B_pre pr sfStage (wotsStage2 pr adv)) +
      SM_DT_TCR_Advantage (B_tcrF_wots pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrH_xmss pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrThK pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrThLsl pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrH_fors pr sfStage adv) +
      3 * SM_DT_TCR_Advantage (B_tcrF_fors pr sfStage adv) +
      SM_DT_DSPR_Advantage (B_dsprF_fors pr sfStage adv) := by
  have hunion :
      Pr{let z ← postPrfExp pr sfStage adv}[PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1] ≤
        Pr{let z ← postPrfExp pr sfStage adv}[EvItsr pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvTcrThK pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvTcrHFors pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvTcrHXmss pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvTcrThLsl pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvTcrFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
        Pr{let z ← postPrfExp pr sfStage adv}[EvPreFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2] := by
    have hmono := prEvent_mono (postPrfExp pr sfStage adv)
      (fun z => PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1)
      (fun z =>
        EvItsr pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvTcrThK pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvTcrHFors pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvTcrHXmss pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvTcrThLsl pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvTcrFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2 ∨
        EvPreFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2)
      (fun ⟨pk, u, out, st⟩ hwin => postPrfWin_cases pr hinj pk u out st hwin)
    calc Pr{let z ← postPrfExp pr sfStage adv}[PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1]
        ≤ _ := hmono
      _ ≤ Pr{let z ← postPrfExp pr sfStage adv}[EvItsr pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          (Pr{let z ← postPrfExp pr sfStage adv}[EvTcrThK pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          (Pr{let z ← postPrfExp pr sfStage adv}[EvTcrHFors pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          (Pr{let z ← postPrfExp pr sfStage adv}[EvForsPre pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          (Pr{let z ← postPrfExp pr sfStage adv}[EvTcrHXmss pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          (Pr{let z ← postPrfExp pr sfStage adv}[EvTcrThLsl pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          (Pr{let z ← postPrfExp pr sfStage adv}[EvTcrFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2] +
          Pr{let z ← postPrfExp pr sfStage adv}[EvPreFWots pr z.1 z.2.1 z.2.2.1 z.2.2.2])))))) := by
          refine (prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_)
          refine (prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_)
          refine (prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_)
          refine (prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_)
          refine (prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_)
          refine (prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_)
          exact prEvent_or_le _ _ _
      _ = _ := by ring
  have h1 := pr_EvItsr_le pr sfStage adv
  have h2 := pr_EvTcrThK_le pr sfStage adv
  have h3 := pr_EvTcrHFors_le pr sfStage adv
  have h4 := pr_EvForsPre_le pr sfStage adv
  have h5 := pr_EvTcrHXmss_le pr sfStage adv
  have h6 := pr_EvTcrThLsl_le pr sfStage adv
  have h7 := pr_EvTcrFWots_le pr sfStage adv
  have h8 := pr_EvPreFWots_le pr sfStage adv
  calc Pr{let z ← postPrfExp pr sfStage adv}[PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1]
      ≤ _ := hunion
    _ ≤ Notions.itsrSucc (slHmsg pr) (slMap vp) (B_itsr pr sfStage adv) +
        SM_DT_TCR_Advantage (B_tcrThK pr sfStage adv) +
        SM_DT_TCR_Advantage (B_tcrH_fors pr sfStage adv) +
        (3 * SM_DT_TCR_Advantage (B_tcrF_fors pr sfStage adv) +
          SM_DT_DSPR_Advantage (B_dsprF_fors pr sfStage adv)) +
        SM_DT_TCR_Advantage (B_tcrH_xmss pr sfStage adv) +
        SM_DT_TCR_Advantage (B_tcrThLsl pr sfStage adv) +
        SM_DT_TCR_Advantage (B_tcrF_wots pr sfStage adv) +
        (∑ γ ∈ Finset.range (vp.params.w - 2),
          SM_DT_UD_Advantage (B_ud pr sfStage (wotsStage2 pr adv) γ) +
          SM_DT_PRE_Advantage (B_pre pr sfStage (wotsStage2 pr adv))) := by
        gcongr
    _ = _ := by ring

/-- Paper-style `(w - 2) * ε_ud` corollary of `postPrf_bound`. -/
theorem postPrf_bound_of_ud_le (hinj : Function.Injective pr.yToBytes)
    {D E : Type} {qs : ℕ} (sfStage : SfStage1 pr D E) (adv : PostPrfAdv pr D E qs)
    {εud : ℝ≥0∞}
    (hud : ∀ γ < vp.params.w - 2,
      SM_DT_UD_Advantage (B_ud pr sfStage (wotsStage2 pr adv) γ) ≤ εud) :
    Pr{let z ← postPrfExp pr sfStage adv}[PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1] ≤
      Notions.itsrSucc (slHmsg pr) (slMap vp) (B_itsr pr sfStage adv) +
      (vp.params.w - 2 : ℕ) * εud +
      SM_DT_PRE_Advantage (B_pre pr sfStage (wotsStage2 pr adv)) +
      SM_DT_TCR_Advantage (B_tcrF_wots pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrH_xmss pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrThK pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrThLsl pr sfStage adv) +
      SM_DT_TCR_Advantage (B_tcrH_fors pr sfStage adv) +
      3 * SM_DT_TCR_Advantage (B_tcrF_fors pr sfStage adv) +
      SM_DT_DSPR_Advantage (B_dsprF_fors pr sfStage adv) := by
  have hsum : ∑ γ ∈ Finset.range (vp.params.w - 2),
      SM_DT_UD_Advantage (B_ud pr sfStage (wotsStage2 pr adv) γ) ≤ (vp.params.w - 2 : ℕ) * εud := by
    calc ∑ γ ∈ Finset.range (vp.params.w - 2),
            SM_DT_UD_Advantage (B_ud pr sfStage (wotsStage2 pr adv) γ)
        ≤ ∑ _γ ∈ Finset.range (vp.params.w - 2), εud :=
          Finset.sum_le_sum fun γ hγ => hud γ (Finset.mem_range.1 hγ)
      _ = (vp.params.w - 2 : ℕ) * εud := by simp
  exact (postPrf_bound pr hinj sfStage adv).trans (by gcongr)

end MasterTheorem

end ShrincsSecurity.Slhdsa

