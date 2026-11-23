module

public import ShrincsSecurity.Fxmss.TcrCommon

/-!
# Claim 4.5: the hop `F.4 → F.5` (SM-TCR of `F`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.5** (txt lines 3565–3677) and
**Algorithm 8** (the reduction `B₄`, lines 7967–8038).

`B₄` is built with `mkTcrAdv`:
* **first stage**: the setup of the block games (`setupHyb`), then, for every anchor `j` (in the
  canonical order `anchorList`) and chain `ch < lsf`, the whole chain from the uniform value
  `u_{j,ch}` through the challenge oracle: `v_{p+1} ← O(ADRS^{p}_{j,ch}, v_p)` for `p < w − 1`,
  each answer being the next message (`iterChal`); the targets are the chain values
  `(ADRS^p_{j,ch}, c_{0,p}(u_{j,ch}))`, at most `L · lsf · (w − 1) ≤ L · lsf · w` of them, at
  pairwise distinct `SF_WOTS_C_HASH` tweaks;
* **second stage**: with `PK.seed` revealed, it runs the signing phase of the block game
  (`stageHyb`) itself and searches the forged chain values `(ADRS^p_{(z*,i*),ch}, c*_p)`,
  `ch < lsf`, `p < w − 1`, against its targets (`tcrFind`).

The event `E5` (a forged chain value at a signed anchor, at or above both digits, different from
the honest one with the same `F`-image) is then an SM-TCR collision, because under
Conjecture 3.1 the honest chain value at `p ≥ a_{j,ch}` is `c_{0,p}(u_{j,ch})`
(`hon0_chainValue`).

## Deviations from the paper
* The event is measured in the block game `F.3_0` (secret key `u`, blocks `c_{0,a}(u)`), as fixed
  by the hybrid structure of the formalisation (`gameHyb 0`), rather than in `F.4`. In `F.3_0`
  every chain value at or above the digit is `c_{0,p}(u)`, so `B₄` queries each chain from
  position `0` (`w − 1` queries per chain) instead of from `max(a − 1, 0)` (Algorithm 8, line 8);
  it therefore needs no grinding in its first stage and no collection query.
* The forger's public key, `PK.sl` and the signatures are computed in the second stage from
  `PK.seed` (Assumption 4.1) instead of through the collection oracle before the parameter is
  revealed (Algorithm 8, lines 13–14); time accounting is replaced by this explicit
  construction.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions
open ShrincsSecurity.Scheme.Structure (leafIds)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-! ## The reduction `B₄` (Algorithm 8) -/

/-- The chains of `B₄`: one per anchor (canonical order) and chain index. -/
noncomputable def B4jobs (P : Params) (S : Structure) : List (LeafId × ℕ) :=
  anchorList P S ×ˢ List.range P.lsf

/-- The targets of the chain `(id, ch)` started at `x`: `(ADRS^p_{id,ch}, c_{0,p}(x))`,
`p < w − 1`. -/
noncomputable def B4chainTargets (pk : pr.PkSeed) (a : LeafId × ℕ) (x : pr.Y) :
    List (SLHDSA.Adrs × pr.Y) :=
  iterTargets ((thF pr).eval pk) (chainTw a.1 a.2) 0 x (P.w - 1)

open scoped Classical in
/-- The first-stage queries of `B₄`: every chain of a valid structure through the challenge
oracle. -/
noncomputable def B4queries (L : ℕ) {State : Type} (d : Setup pr Msg State) :
    OracleComp (TcrSpec (probTcrF pr (L * P.lsf * P.w))) Unit :=
  if d.S.TreeValid P.hsf then
    (B4jobs P d.S).forM fun a =>
      iterChal (probTcrF pr (L * P.lsf * P.w)) (chainTw a.1 a.2) 0 (skOf pr d.S d.u a.1 a.2)
        (P.w - 1)
  else pure ()

open scoped Classical in
/-- The targets recorded by `B₄`'s first stage. -/
noncomputable def B4targets {State : Type} (d : Setup pr Msg State) (pk : pr.PkSeed) :
    List (SLHDSA.Adrs × pr.Y) :=
  if d.S.TreeValid P.hsf then
    (B4jobs P d.S).flatMap fun a => B4chainTargets pr pk a (skOf pr d.S d.u a.1 a.2)
  else []

/-- The candidates read off a forgery: the forged chain values `(ADRS^p_{(z*,i*),ch}, c*_p)`,
`ch < lsf`, `p < w − 1`. -/
def B4cands (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr) :
    List (SLHDSA.Adrs × pr.Y) :=
  (List.finRange P.lsf).flatMap fun ch =>
    (List.range (P.w - 1)).map fun p => (chainTw idf ch.val p, H.fChain idf yf w ch p)

/-- The extraction of `B₄`. -/
noncomputable def B4extract {State : Type} (d : Setup pr Msg State) (pk : pr.PkSeed)
    (o : Option (Transcript pr Msg × Honest pr)) : ℕ × pr.Y :=
  tcrFind ((thF pr).eval pk) (B4targets pr Msg d pk) (forgeryCands pr Msg (B4cands pr) o)

/-- **The reduction `B₄` of Claim 4.5** (Algorithm 8) against SM-TCR of `F ∈ Th_λ` with
`L · lsf · w` targets. -/
noncomputable def B4 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrF pr (L * P.lsf * P.w)) :=
  mkTcrAdv (probTcrF pr (L * P.lsf * P.w)) (setupHyb pr Msg slKeygen A.toFxmssAdversary)
    (B4queries pr Msg L) fun d pk => B4extract pr Msg d pk <$>
      stageHyb pr Msg slKeygen A.toFxmssAdversary (betaOf pr 0 pk d.u) d pk

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg]
  [Inhabited pr.Digest] [Nontrivial Msg] in
/-- The first stage of `B₄` records `B4targets`: the chain tweaks are pairwise distinct and there
are at most `L · lsf · (w − 1)` of them. -/
theorem B4queries_run {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (pk : pr.PkSeed) (d : Setup pr Msg A.State)
    (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary)) :
    (simulateQ (SM_DT_TCR_oracles (probTcrF pr (L * P.lsf * P.w)) pk)
      (B4queries pr Msg L d)).run ([], []) = pure ((), (B4targets pr Msg d pk, [])) := by
  classical
  unfold B4queries B4targets
  split_ifs with hS
  · have hlen : ((B4jobs P d.S).flatMap fun a =>
        B4chainTargets pr pk a (skOf pr d.S d.u a.1 a.2)).length ≤ L * P.lsf * P.w := by
      simp only [List.length_flatMap, B4chainTargets, iterTargets_length, List.map_const',
        List.sum_replicate, smul_eq_mul, B4jobs, List.length_product, List.length_range]
      have := setupHyb_length_anchorList_le pr Msg slKeygen A hd hS
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ this) (Nat.sub_le _ _)
    have h := tcr_forM_run (probTcrF pr (L * P.lsf * P.w)) pk (B4jobs P d.S)
      (fun a => iterChal (probTcrF pr (L * P.lsf * P.w)) (chainTw a.1 a.2) 0
        (skOf pr d.S d.u a.1 a.2) (P.w - 1))
      (fun a => B4chainTargets pr pk a (skOf pr d.S d.u a.1 a.2)) (fun _ => [])
      (fun a _ qs' tws hcap hnd hdis => by
        rw [List.append_nil]
        exact iterChal_run (probTcrF pr (L * P.lsf * P.w)) pk (chainTw a.1 a.2) 0 _ (P.w - 1) qs'
          tws (by simpa [B4chainTargets, iterTargets_length] using hcap) hnd
          (fun t ht => by
            have h := hdis t (by rw [List.map_append]; exact List.mem_append_right _ ht)
            simpa using h))
      [] [] (by simpa using hlen)
      (by
        simp only [List.nil_append, List.map_flatMap, B4chainTargets, iterTargets_map_fst]
        exact nodup_flatMap_chainTw ((nodup_anchorList d.S).product List.nodup_range) _)
      (by simp)
    have h0 : ((B4jobs P d.S).flatMap fun _ => ([] : List SLHDSA.Adrs)) = [] :=
      List.flatMap_eq_nil_iff.2 fun _ _ => rfl
    rw [h0] at h
    simpa using h
  · simp

/-! ## Claim 4.5 -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Claim 4.5** (`F.4 → F.5`): the abort event `E5` (at a signed anchor, a forged chain value at
or above both digits, different from the honest one, with the same `F`-image) in the block game
`F.3_0` is bounded by the SM-TCR advantage of `B₄` against `F ∈ Th_λ` with `L · lsf · w`
targets. -/
theorem claim_4_5 (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEvent Honest.E5 o] ≤
      SM_DT_TCR_Advantage (B4 pr Msg slKeygen A) := by
  classical
  rw [B4, mkTcrAdv_advantage (probTcrF pr (L * P.lsf * P.w)) _ _ _
    (fun d pk => B4targets pr Msg d pk) (fun _ _ => [])
    fun pk d hd => B4queries_run pr Msg slKeygen A pk d hd]
  refine (prEvent_gameHyb_le pr Msg slKeygen 0 A.toFxmssAdversary Honest.E5
    (B4extract pr Msg) (fun d pk out => tcrWin (probTcrF pr (L * P.lsf * P.w)) pk
      (B4targets pr Msg d pk) out = true) ?_).trans le_rfl
  intro pk d hd hS tr w hw hE
  obtain ⟨hid, ch, p, hp, hd1, -, hne, heq⟩ := hE
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  rw [hon_encoded pr hg] at hd1
  have hcv := hon0_chainValue pr (u := d.u) hg ch hd1
  unfold B4extract
  rw [forgeryCands_some pr Msg _ hw]
  refine tcrWin_tcrFind (probTcrF pr (L * P.lsf * P.w)) pk _ _
    ⟨(chainTw tr.idf ch.val p, _), List.mem_flatMap.2 ⟨ch, List.mem_finRange _,
      List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩⟩,
      (chainTw tr.idf ch.val p,
        WotsC.chain pr pk tr.idf ch.val (skOf pr d.S d.u tr.idf ch.val) 0 p),
      ?_, rfl, by rw [← hcv]; exact hne, by rw [← hcv]; exact heq⟩
  simp only [B4targets, hS, ↓reduceIte]
  refine List.mem_flatMap.2 ⟨(tr.idf, ch.val), List.mem_product.2 ⟨mem_anchorList.2 hid,
    List.mem_range.2 ch.isLt⟩, ?_⟩
  rw [B4chainTargets, iterTargets_eq]
  refine List.mem_map.2 ⟨p, List.mem_range.2 hp, ?_⟩
  show (chainTw tr.idf ch.val (0 + p), _) = _
  rw [Nat.zero_add]
  exact congrArg _ (iterVal_chain pr pk tr.idf ch.val _ (fun _ _ => rfl) 0 _ p)

end ShrincsSecurity.Fxmss.Rom

end
