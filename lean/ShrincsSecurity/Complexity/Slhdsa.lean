module

public import ShrincsSecurity.Complexity.Defs

/-!
# Stateless reduction complexity (`ξ̃_sl ≤ ξ + V_sl`), Stage-1 `O_coll` bounds, and lazy `B_sl_prfLazyAdv`

This module proves three complexity results for the stateless SLH-DSA reductions shared by
**Main Paper Theorem 4.3** (`Slhdsa/Theorem43.lean`) and **Main Paper Theorem 4.1 / Claim 4.16**
(`Shrincs/Claim416.lean`, `Shrincs/Theorem41.lean`):

1. **Stage-2 `Th_λ`-evaluation complexity `ξ̃_sl ≤ ξ + V_sl` (`V_sl = 2741` at SHRINCS):**
   For any `ξ`-`Th_λ`-query `BudgetedPostPrfAdv pr D E qs ξ`, every single one of the **9 stateless
   collection reductions** (`B_ud γ`, `B_pre`, `B_tcrF_wots`, `B_tcrH_xmss`, `B_tcrThK`,
   `B_tcrThLsl`, `B_tcrH_fors`, `B_tcrF_fors`, `B_dsprF_fors`) satisfies `Stage2ThBound` with
   budget **`ξ + Vsl vp.params`**:
   * `B_ud_stage2Bound`, `B_pre_stage2Bound`, `B_tcrF_wots_stage2Bound`, `B_tcrH_xmss_stage2Bound`,
     `B_tcrThK_stage2Bound`, `B_tcrThLsl_stage2Bound`, `B_tcrH_fors_stage2Bound`,
     `B_tcrF_fors_stage2Bound`, `B_dsprF_fors_stage2Bound`.
   * Instantiated directly for both standalone SLH-DSA (**`theorem_4_3_stage2Bounds`**) and
     SHRINCS (**`theorem_4_1_stateless_stage2Bounds`**).
2. **Stage-1 `O_coll` + challenge query bounds:**
   * `slVirtualTreeM_totalQueryBound`: `≤ (slTreeAddresses vp).length` oracle calls (at most 1 per
     virtual-hypertree node).
   * `buildHybTreeM_totalQueryBound`: explicit worst-case query bound for `buildHybTreeM` (hence
     `udBuildM` and `preBuildM`).
   * `sfPrecompM_totalQueryBound`: explicit worst-case `O_coll` query bound for Stage-1 stateful
     FXMSS precomputation (`sfPrecompM`).
3. **Lazy-cached standalone `PRF` reduction (`B_sl_prfLazyAdv`, `theorem_4_3_lazy`):**
   Replaces the eager `tableM`-based `B_sl_prfAdv` in standalone Theorem 4.3 with a lazily-queried
   `CachedPRF.cacheAdv` reduction matching `Shrincs/PrfBound.lean`'s `BprfAdv`: it queries `PRF`
   only at secret-key addresses actually accessed by `keygen` and the `q_s` signing queries, still
   within the exact budget `q₁ = slSecretCount vp.sl`, and achieves the identical Theorem 4.3 bound
   (`theorem_4_3_lazy`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Complexity

open Scheme Slhdsa Shrincs SLHDSA.Security
open SLHDSA (Adrs Byte wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsNodeAdrs forsPkAdrs splitDigest LayerPosition)

/-! ## 1. Stage-2 `Th_λ`-evaluation complexity `ξ̃_sl ≤ ξ + V_sl` for all 9 stateless reductions -/

section StatelessStage2

variable {vp : ValidatedParams} (pr : Primitives vp.params)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]

/-- Running `runPostPrf` on a `BudgetedPostPrfAdv` with any pure (`Th_λ`-free) signing function
`signFn` (such as `slSignTable` or `hybSign`) makes at most `ξ` Stage-2 `Th_λ` evaluations. -/
noncomputable def runPostPrf_stage2Bound {D E St : Type} {qs ξ : ℕ}
    (adv : BudgetedPostPrfAdv pr D E qs ξ)
    (getD : St → D) (getE : St → E) (getPkSl : St → pr.Y)
    (signFn : St → pr.PkSeed → List Byte → pr.Y → Stateless.Sig pr) :
    Stage2ThBound pr
      (fun st pk => runPostPrf pr adv.toPostPrfAdv (getD st) (getE st) pk (getPkSl st)
        (signFn st pk))
      ξ where
  progM st pk :=
    (simulateQ (liftStateThImpl pr (slSignImpl pr pk (getPkSl st) (signFn st pk)))
      (adv.runM (getD st) (getE st) pk (getPkSl st))).run (SlSignSt.init pr)
  simulate_eq st pk := by
    unfold runPostPrf
    rw [simulateQ_stage2ThImpl_runStateTh, adv.runM_eq]
  queryBound st pk :=
    isQueryBoundP_runStateTh pr (slSignImpl pr pk (getPkSl st) (signFn st pk))
      (adv.thBound (getD st) (getE st) pk (getPkSl st)) (SlSignSt.init pr)

/-- **`B_ud γ` Stage-2 complexity (`≤ ξ + V_sl`)**: `hybSign` uses 0 `Th_λ` queries and
`findHybWotsPreM` performs verification + WOTS-preimage extraction in one pass of `≤ Vsl` queries. -/
noncomputable def B_ud_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) (γ : ℕ) :
    UdStage2Bound pr (B_ud pr sfStage (wotsStage2 pr adv.toPostPrfAdv) γ) (ξ + Vsl vp.params) := by
  let hsim := runPostPrf_stage2Bound pr adv
    (fun st : (B_ud pr sfStage (wotsStage2 pr adv.toPostPrfAdv) γ).State => st.1)
    (fun st => st.2.1) (fun st => st.2.2.2.pkSl) (fun st pk => hybSign pr pk st.2.2.2 st.2.2.1)
  let extM : (B_ud pr sfStage (wotsStage2 pr adv.toPostPrfAdv) γ).State → pr.PkSeed →
      Option (List Byte × Stateless.Sig pr) × SlSignSt pr → OracleComp (thSpec pr) Bool :=
    fun st pk res =>
      match res.1 with
      | some (msg, sig) =>
        if msg ∉ res.2.log then Option.isSome <$> findHybWotsPreM pr pk st.2.2.2 msg sig
        else pure false
      | none => pure false
  have hext : ∀ st pk res, IsTotalQueryBound (extM st pk res) (Vsl vp.params) := by
    intro st pk res
    dsimp only [extM]
    cases res.1 with
    | none => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
    | some ms =>
      dsimp only
      by_cases hm : ms.1 ∈ res.2.log
      · simp only [hm, not_true_eq_false, ↓reduceIte]
        exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
      · simp only [hm, not_false_eq_true, ↓reduceIte]
        rw [← isQueryBoundP_true_iff, isQueryBoundP_map_iff, isQueryBoundP_true_iff]
        exact findHybWotsPreM_queryBound pr pk st.2.2.2 ms.1 ms.2
  let hb := hsim.bindTh pr extM hext
  refine ⟨hb.progM, fun st pk => (hb.simulate_eq st pk).trans ?_, hb.queryBound⟩
  simp only [B_ud, wotsStage2, bind_assoc, pure_bind, map_eq_bind_pure_comp]
  refine bind_congr fun res => ?_
  rcases res with ⟨out, s⟩
  cases out with
  | none => rfl
  | some ms =>
    rcases ms with ⟨msg, sig⟩
    refine congrArg pure ?_
    dsimp only [extM]
    by_cases hm : msg ∈ s.log
    · simp only [hm, not_true_eq_false, ↓reduceIte, isHybWotsPre, simulateQ_pure, Id.run_pure]
    · simp only [hm, not_false_eq_true, ↓reduceIte, isHybWotsPre, findHybWotsPre,
        map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind, Id.run_bind,
        simulateQ_pure, Id.run_pure]

/-- **`B_pre` Stage-2 complexity (`≤ ξ + V_sl`)**: `hybSign` uses 0 `Th_λ` queries and
`findHybWotsPreM` performs verification + WOTS-preimage extraction in one pass of `≤ Vsl` queries. -/
noncomputable def B_pre_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    PreStage2Bound pr (B_pre pr sfStage (wotsStage2 pr adv.toPostPrfAdv)) (ξ + Vsl vp.params) := by
  let hsim := runPostPrf_stage2Bound pr adv
    (fun st : (B_pre pr sfStage (wotsStage2 pr adv.toPostPrfAdv)).State => st.1)
    (fun st => st.2.1) (fun st => st.2.2.2.1.pkSl) (fun st pk => hybSign pr pk st.2.2.2.1 st.2.2.1)
  let extM : (B_pre pr sfStage (wotsStage2 pr adv.toPostPrfAdv)).State → pr.PkSeed →
      Option (List Byte × Stateless.Sig pr) × SlSignSt pr → OracleComp (thSpec pr) (ℕ × pr.Y) :=
    fun st pk res =>
      match res.1 with
      | some (msg, sig) =>
        if msg ∉ res.2.log then
          (fun opt => match opt with
            | some ((pos, c), step, val) =>
              (st.2.2.2.2.idxOf ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step), val)
            | none => (0, default)) <$> findHybWotsPreM pr pk st.2.2.2.1 msg sig
        else pure (0, default)
      | none => pure (0, default)
  have hext : ∀ st pk res, IsTotalQueryBound (extM st pk res) (Vsl vp.params) := by
    intro st pk res
    dsimp only [extM]
    cases res.1 with
    | none => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
    | some ms =>
      dsimp only
      by_cases hm : ms.1 ∈ res.2.log
      · simp only [hm, not_true_eq_false, ↓reduceIte]
        exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
      · simp only [hm, not_false_eq_true, ↓reduceIte]
        rw [← isQueryBoundP_true_iff, isQueryBoundP_map_iff, isQueryBoundP_true_iff]
        exact findHybWotsPreM_queryBound pr pk st.2.2.2.1 ms.1 ms.2
  let hb := hsim.bindTh pr extM hext
  refine ⟨hb.progM, fun st pk => (hb.simulate_eq st pk).trans ?_, hb.queryBound⟩
  simp only [B_pre, wotsStage2, bind_assoc, pure_bind, map_eq_bind_pure_comp]
  refine bind_congr fun res => ?_
  rcases res with ⟨out, s⟩
  cases out with
  | none => rfl
  | some ms =>
    rcases ms with ⟨msg, sig⟩
    refine congrArg pure ?_
    dsimp only [extM]
    by_cases hm : msg ∈ s.log
    · simp only [hm, not_true_eq_false, ↓reduceIte, extractPre, simulateQ_pure, Id.run_pure]
    · simp only [hm, not_false_eq_true, ↓reduceIte, extractPre, findHybWotsPre,
        map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind, Id.run_bind,
        simulateQ_pure, Id.run_pure]
      cases Id.run (simulateQ (thRealImpl pr pk)
        (findHybWotsPreM pr pk st.2.2.2.1 msg sig)) <;> rfl

/-- Generic `≤ ξ + V_sl` Stage-2 bound for any `routedTcrAdv` whose candidate extractor evaluates
`verifyAndExtractTable` at most once on `(msg, sig)` and post-processes its `(ver, wit)` purely. -/
noncomputable def routedTcr_tableExtract_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ)
    (mem : Primitives.Member) [DecidableEq (pr.MemberMsg mem)] [Inhabited (pr.MemberMsg mem)]
    (isTarget : Adrs → Bool) (p : ℕ)
    (cand : pr.PkSeed → (SlSecAdrs vp → pr.Y) → (pr.Y × (Adrs → Option pr.Y)) →
      Option (List Byte × Stateless.Sig pr) → SlSignSt pr → Option (Adrs × pr.MemberMsg mem))
    (post : pr.PkSeed → (pr.Y × (Adrs → Option pr.Y)) → List Byte → Stateless.Sig pr → SlSignSt pr →
      Bool × Option (Witness vp.sl (prEager pr)) → Option (Adrs × pr.MemberMsg mem))
    (hpost : ∀ pk u vt out st,
      cand pk u vt out st =
        match out with
        | none => none
        | some (msg, sig) =>
            let target := chosenForsTree pr pk vt.1 st.itLog msg sig
            post pk vt msg sig st (verifyAndExtractTable pr pk vt.1 vt.2 u msg sig target)) :
    TcrStage2Bound pr
      (routedTcrAdv pr sfStage adv.toPostPrfAdv mem isTarget p (idxExtract pr cand))
      (ξ + Vsl vp.params) := by
  let hsim := runPostPrf_stage2Bound pr adv
    (fun st : (routedTcrAdv pr sfStage adv.toPostPrfAdv mem isTarget p (idxExtract pr cand)).State => st.1)
    (fun st => st.2.1) (fun st => st.2.2.2.1.1)
    (fun st pk => slSignTable pr st.2.2.2.1.2 pk st.2.2.2.1.1 st.2.2.1)
  let pickFromCand : List (Adrs × pr.MemberMsg mem) → Option (Adrs × pr.MemberMsg mem) →
      ℕ × pr.MemberMsg mem := fun savedQ opt =>
    match opt with
    | some (a, msg') => ((savedQ.map Prod.fst).idxOf a, msg')
    | none => (savedQ.length, default)
  let extM : (routedTcrAdv pr sfStage adv.toPostPrfAdv mem isTarget p (idxExtract pr cand)).State →
      pr.PkSeed → Option (List Byte × Stateless.Sig pr) × SlSignSt pr →
      OracleComp (thSpec pr) (ℕ × pr.MemberMsg mem) :=
    fun st pk res =>
      let (_, _, u, vt, savedQ) := st
      match res.1 with
      | none => pure (savedQ.length, default)
      | some (msg, sig) =>
          let target := chosenForsTree pr pk vt.1 res.2.itLog msg sig
          (fun r => pickFromCand savedQ (post pk vt msg sig res.2 r)) <$>
            verifyAndExtractTableM pr pk vt.1 vt.2 u msg sig target
  have hext : ∀ st pk res, IsTotalQueryBound (extM st pk res) (Vsl vp.params) := by
    intro ⟨d, sf, u, vt, savedQ⟩ pk res
    dsimp only [extM]
    cases res.1 with
    | none => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
    | some ms =>
      rw [← isQueryBoundP_true_iff, isQueryBoundP_map_iff, isQueryBoundP_true_iff]
      exact verifyAndExtractTableM_queryBound pr pk vt.1 vt.2 u ms.1 ms.2 _
  let hb := hsim.bindTh pr extM hext
  refine ⟨hb.progM, fun ⟨d, sf, u, vt, savedQ⟩ pk => (hb.simulate_eq (d, sf, u, vt, savedQ) pk).trans ?_,
    hb.queryBound⟩
  simp only [routedTcrAdv, map_eq_bind_pure_comp]
  refine bind_congr fun res => ?_
  refine congrArg pure ?_
  rcases res with ⟨out, s⟩
  cases out with
  | none =>
    simp only [extM, idxExtract, hpost pk u vt none s, simulateQ_pure, Id.run_pure]
  | some ms =>
    rcases ms with ⟨msg, sig⟩
    dsimp only [extM, pickFromCand, idxExtract]
    rw [hpost pk u vt (some (msg, sig)) s]
    dsimp only [verifyAndExtractTable]
    simp only [map_eq_bind_pure_comp, Function.comp_apply, simulateQ_bind, Id.run_bind,
      simulateQ_pure, Id.run_pure]
    cases post pk vt msg sig s (Id.run (simulateQ (thRealImpl pr pk)
      (verifyAndExtractTableM pr pk vt.1 vt.2 u msg sig
        (chosenForsTree pr pk vt.1 s.itLog msg sig)))) <;> rfl

/-- **`B_tcrThK` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_tcrThK_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    TcrStage2Bound pr (B_tcrThK pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) :=
  routedTcr_tableExtract_stage2Bound pr sfStage adv .thK isForsRoot (qForsRoot vp) (candThK pr)
    (fun pk vt msg sig _ r =>
      match r.2 with
      | some (.fors (.tlCollision rec)) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
          some (forsPkAdrs parts.forsAdrs, rec)
      | _ => none)
    (fun _ _ _ out _ => by cases out <;> rfl)

/-- **`B_tcrH_fors` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_tcrH_fors_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    TcrStage2Bound pr (B_tcrH_fors pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) :=
  routedTcr_tableExtract_stage2Bound pr sfStage adv .H isForsH (qForsH vp) (candHFors pr)
    (fun pk vt msg sig _ r =>
      match r.2 with
      | some (.fors (.hCollision i z c)) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
          some (forsNodeAdrs parts.forsAdrs z
            (forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ z), c)
      | _ => none)
    (fun _ _ _ out _ => by cases out <;> rfl)

/-- **`B_tcrH_xmss` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_tcrH_xmss_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    TcrStage2Bound pr (B_tcrH_xmss pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) :=
  routedTcr_tableExtract_stage2Bound pr sfStage adv .H isXmssH (qXmssH vp) (candHXmss pr)
    (fun pk vt msg sig _ r =>
      match r.2 with
      | some (.hypertree ⟨ℓ, .hCollision z c⟩) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
          let pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
          some (xmssNodeAdrs pos.toAdrs z (pos.leaf.val / 2 ^ z), c)
      | _ => none)
    (fun _ _ _ out _ => by cases out <;> rfl)

/-- **`B_tcrThLsl` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_tcrThLsl_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    TcrStage2Bound pr (B_tcrThLsl pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) :=
  routedTcr_tableExtract_stage2Bound pr sfStage adv .thLsl isWotsPk (qWotsPk vp) (candThLsl pr)
    (fun pk vt msg sig _ r =>
      match r.2 with
      | some (.hypertree ⟨ℓ, .wots (.tlCollision rec)⟩) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
          let pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
          some (wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val),
            rec.cast (Params.lsl_eq_len vp.valid).symm)
      | _ => none)
    (fun _ _ _ out _ => by cases out <;> rfl)

/-- **`B_tcrF_wots` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_tcrF_wots_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    TcrStage2Bound pr (B_tcrF_wots pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) :=
  routedTcr_tableExtract_stage2Bound pr sfStage adv .F isWotsStep (qWotsStep vp) (candFWots pr)
    (fun pk vt msg sig _ r =>
      match r.2 with
      | some (.hypertree ⟨ℓ, .wots (.fCollision c step val)⟩) =>
          let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
          let pos := (LayerPosition.initial vp.sl parts).advance ℓ.val (by simp)
          some ((wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val).setHashAddress step, val)
      | _ => none)
    (fun _ _ _ out _ => by cases out <;> rfl)

/-- **`B_tcrF_fors` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_tcrF_fors_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    TcrStage2Bound pr (B_tcrF_fors pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) :=
  routedTcr_tableExtract_stage2Bound pr sfStage adv .F isForsLeaf (qForsLeaf vp)
    (candForsPreTable pr)
    (fun pk vt msg sig st r =>
      if msg ∉ st.log then
        if r.1 = true ∧ ¬ ITSR.Covered
            (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
            (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, vt.1, msg))) then
          match r.2 with
          | some (.fors (.fPreimage i val)) =>
              let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
              some (forsNodeAdrs parts.forsAdrs 0
                (forsSigLeafIndex vp.sl.params parts.md.toList i.val), val)
          | _ => none
        else none
      else none)
    (fun pk u vt out st => by
      cases out with
      | none => rfl
      | some ms =>
        rcases ms with ⟨msg, sig⟩
        unfold candForsPreTable
        dsimp only
        by_cases hm : msg ∈ st.log
        · simp only [hm, not_true_eq_false, ↓reduceIte]
          rfl
        · simp only [hm, not_false_eq_true, ↓reduceIte]
          exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by convert h2⟩) rfl rfl)

/-- **`B_dsprF_fors` Stage-2 complexity (`≤ ξ + V_sl`)**. -/
noncomputable def B_dsprF_fors_stage2Bound {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    DsprStage2Bound pr (B_dsprF_fors pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params) := by
  let hsim := runPostPrf_stage2Bound pr adv
    (fun st : (B_dsprF_fors pr sfStage adv.toPostPrfAdv).State => st.1)
    (fun st => st.2.1) (fun st => st.2.2.2.1.1)
    (fun st pk => slSignTable pr st.2.2.2.1.2 pk st.2.2.2.1.1 st.2.2.1)
  let postFors : pr.PkSeed → (pr.Y × (Adrs → Option pr.Y)) → List Byte → Stateless.Sig pr →
      SlSignSt pr → Bool × Option (Witness vp.sl (prEager pr)) → Option (Adrs × pr.Y) :=
    fun pk vt msg sig st r =>
      if r.1 = true ∧ ¬ ITSR.Covered
          (st.itLog.toFinset.image (Notions.itsrG (slHmsg pr) (slMap vp)))
          (Notions.itsrG (slHmsg pr) (slMap vp) (sig.randomness, (pk, vt.1, msg))) then
        match r.2 with
        | some (.fors (.fPreimage i val)) =>
            let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk vt.1 msg)
            some (forsNodeAdrs parts.forsAdrs 0
              (forsSigLeafIndex vp.sl.params parts.md.toList i.val), val)
        | _ => none
      else none
  let decideGuess : List (Adrs × pr.MemberMsg .F) → Option (Adrs × pr.Y) → ℕ × Bool :=
    fun savedQ opt =>
      match opt with
      | none => (0, true)
      | some (aLeaf, val) =>
          let j := (savedQ.map Prod.fst).idxOf aLeaf
          match savedQ[j]? with
          | some (_, x) => if val = x then (j, false) else (0, true)
          | none => (0, true)
  let extM : (B_dsprF_fors pr sfStage adv.toPostPrfAdv).State → pr.PkSeed →
      Option (List Byte × Stateless.Sig pr) × SlSignSt pr → OracleComp (thSpec pr) (ℕ × Bool) :=
    fun st pk res =>
      let (_, _, u, vt, savedQ) := st
      match res.1 with
      | none => pure (0, true)
      | some (msg, sig) =>
          if msg ∉ res.2.log then
            let target := chosenForsTree pr pk vt.1 res.2.itLog msg sig
            (fun r => decideGuess savedQ (postFors pk vt msg sig res.2 r)) <$>
              verifyAndExtractTableM pr pk vt.1 vt.2 u msg sig target
          else pure (0, true)
  have hext : ∀ st pk res, IsTotalQueryBound (extM st pk res) (Vsl vp.params) := by
    intro ⟨d, sf, u, vt, savedQ⟩ pk res
    dsimp only [extM]
    cases res.1 with
    | none => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
    | some ms =>
      dsimp only
      by_cases hm : ms.1 ∈ res.2.log
      · simp only [hm, not_true_eq_false, ↓reduceIte]
        exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ _)
      · simp only [hm, not_false_eq_true, ↓reduceIte]
        rw [← isQueryBoundP_true_iff, isQueryBoundP_map_iff, isQueryBoundP_true_iff]
        exact verifyAndExtractTableM_queryBound pr pk vt.1 vt.2 u ms.1 ms.2 _
  let hb := hsim.bindTh pr extM hext
  refine ⟨hb.progM, fun ⟨d, sf, u, vt, savedQ⟩ pk => (hb.simulate_eq (d, sf, u, vt, savedQ) pk).trans ?_,
    hb.queryBound⟩
  simp only [B_dsprF_fors, map_eq_bind_pure_comp]
  refine bind_congr fun res => ?_
  refine congrArg pure ?_
  rcases res with ⟨out, s⟩
  cases out with
  | none => simp only [extM, candForsPreTable, simulateQ_pure, Id.run_pure]
  | some ms =>
    rcases ms with ⟨msg, sig⟩
    dsimp only [extM, candForsPreTable]
    by_cases hm : msg ∈ s.log
    · simp only [hm, not_true_eq_false, ↓reduceIte, simulateQ_pure, Id.run_pure]
    · simp only [hm, not_false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_apply,
        simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure, decideGuess, postFors,
        verifyAndExtractTable]
      congr 1

/-- Bundle of `≤ ξ + V_sl` Stage-2 `Th_λ`-evaluation bounds for all 9 stateless collection
reductions of `postPrf_bound`. -/
structure PostPrfStage2Bounds {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) where
  ud : ∀ γ, UdStage2Bound pr (B_ud pr sfStage (wotsStage2 pr adv.toPostPrfAdv) γ) (ξ + Vsl vp.params)
  pre : PreStage2Bound pr (B_pre pr sfStage (wotsStage2 pr adv.toPostPrfAdv)) (ξ + Vsl vp.params)
  tcrF_wots : TcrStage2Bound pr (B_tcrF_wots pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)
  tcrH_xmss : TcrStage2Bound pr (B_tcrH_xmss pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)
  tcrThK : TcrStage2Bound pr (B_tcrThK pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)
  tcrThLsl : TcrStage2Bound pr (B_tcrThLsl pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)
  tcrH_fors : TcrStage2Bound pr (B_tcrH_fors pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)
  tcrF_fors : TcrStage2Bound pr (B_tcrF_fors pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)
  dsprF_fors : DsprStage2Bound pr (B_dsprF_fors pr sfStage adv.toPostPrfAdv) (ξ + Vsl vp.params)

/-- **Master stateless Stage-2 complexity theorem (`ξ̃_sl ≤ ξ + V_sl`)**: every stateless
collection reduction in `postPrf_bound` makes at most `ξ + Vsl vp.params` (`= ξ + 2741` at SHRINCS)
Stage-2 `Th_λ` evaluations. -/
noncomputable def postPrf_stage2Bounds {D E : Type} {qs ξ : ℕ}
    (sfStage : SfStage1 pr D E) (adv : BudgetedPostPrfAdv pr D E qs ξ) :
    PostPrfStage2Bounds pr sfStage adv where
  ud γ := B_ud_stage2Bound pr sfStage adv γ
  pre := B_pre_stage2Bound pr sfStage adv
  tcrF_wots := B_tcrF_wots_stage2Bound pr sfStage adv
  tcrH_xmss := B_tcrH_xmss_stage2Bound pr sfStage adv
  tcrThK := B_tcrThK_stage2Bound pr sfStage adv
  tcrThLsl := B_tcrThLsl_stage2Bound pr sfStage adv
  tcrH_fors := B_tcrH_fors_stage2Bound pr sfStage adv
  tcrF_fors := B_tcrF_fors_stage2Bound pr sfStage adv
  dsprF_fors := B_dsprF_fors_stage2Bound pr sfStage adv

/-- **Theorem 4.3 Stage-2 complexity (`ξ̃_sl ≤ ξ + V_sl`)**: all 9 stateless collection reductions
of `Slhdsa.theorem_4_3` make at most `ξ + Vsl vp.params` Stage-2 `Th_λ` evaluations. -/
noncomputable def theorem_4_3_stage2Bounds {Msg : Type} {enc : MsgEnc Msg}
    [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq Msg] {qs ξ : ℕ}
    (A : BudgetedSlhdsaAdv pr Msg enc qs ξ) :
    PostPrfStage2Bounds pr (SfStage1.unit pr) A.toPostPrf :=
  postPrf_stage2Bounds pr (SfStage1.unit pr) A.toPostPrf

/-- **Theorem 4.1 (Claim 4.16) stateless Stage-2 complexity (`ξ̃_sl ≤ ξ + V_sl`)**: all 9 stateless
collection reductions of `Shrincs.claim_4_16` / `Shrincs.theorem_4_1_full` make at most
`ξ + Vsl vp.params` Stage-2 `Th_λ` evaluations. -/
noncomputable def theorem_4_1_stateless_stage2Bounds {Msg : Type} {enc : MsgEnc Msg}
    [Fintype pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
    [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
    [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedShrincsForger pr Msg enc qs qh₁ qh₂ L ξ) :
    PostPrfStage2Bounds pr (Shrincs.sfStageShrincs pr Msg enc A.toShrincsAdversary) A.toPostPrf :=
  postPrf_stage2Bounds pr (Shrincs.sfStageShrincs pr Msg enc A.toShrincsAdversary) A.toPostPrf

end StatelessStage2

/-! ## 2. Stage-1 `O_coll` and challenge query bounds -/

section Stage1Bounds

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

private theorem isTotalQueryBound_foldlM {ι α β : Type} {spec : OracleSpec ι}
    (f : α → β → OracleComp spec α) (b : ℕ)
    (hf : ∀ a x, IsTotalQueryBound (f a x) b) :
    ∀ (l : List β) (init : α), IsTotalQueryBound (l.foldlM f init) (l.length * b)
  | [], init => by
    simp only [List.foldlM_nil, List.length_nil, Nat.zero_mul]
    exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | x :: xs, init => by
    simp only [List.foldlM_cons, List.length_cons, Nat.succ_mul]
    exact (isTotalQueryBound_bind (hf init x) fun a' =>
      isTotalQueryBound_foldlM f b hf xs a').mono (by omega)

private theorem evalNodeM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) (a : Adrs) :
    IsTotalQueryBound (evalNodeM pr collCall u tbl a) 1 := by
  unfold evalNodeM
  split
  · split_ifs <;> exact hcall _ _ _
  · exact hcall _ _ _
  · split_ifs
    · exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 1)
    · exact hcall _ _ _
    · exact hcall _ _ _
  · split_ifs <;> exact hcall _ _ _
  · exact hcall _ _ _
  · exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 1)

/-- **Stage-1 virtual-hypertree query bound**: `slVirtualTreeM` issues at most
`(slTreeAddresses vp).length` oracle calls (at most `1` per virtual-hypertree address) whenever
`collCall` issues at most `1` query per evaluation. -/
theorem slVirtualTreeM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (u : SlSecAdrs vp → pr.Y) :
    IsTotalQueryBound (slVirtualTreeM pr collCall u) (slTreeAddresses vp).length := by
  unfold slVirtualTreeM
  have hstep : ∀ (tbl : Adrs → Option pr.Y) (a : Adrs),
      IsTotalQueryBound (do let v ← evalNodeM pr collCall u tbl a; pure (Function.update tbl a (some v))) 1 :=
    fun tbl a => (isTotalQueryBound_bind (n₂ := 0) (evalNodeM_totalQueryBound pr collCall hcall u tbl a)
      fun _ => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
      (by omega)
  have hfold := isTotalQueryBound_foldlM _ 1 hstep (slTreeAddresses vp) (fun _ => none)
  exact (isTotalQueryBound_bind (n₂ := 0) hfold fun _ =>
    (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (by simp)

omit [Inhabited pr.Y] in
/-- Per-step query bound for `slChainM`. -/
theorem slChainM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (chAdrs : Adrs) (x : pr.Y) (start : ℕ) :
    ∀ steps, IsTotalQueryBound (slChainM pr collCall chAdrs x start steps) steps
  | 0 => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | steps + 1 =>
    isTotalQueryBound_bind (slChainM_totalQueryBound collCall hcall chAdrs x start steps)
      fun _ => hcall .F _ _

/-- **Stage-1 hybrid-tree query bound**: explicit worst-case oracle-query bound for `buildHybTreeM`
(covering both `udBuildM` and `preBuildM`). -/
theorem buildHybTreeM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (chainStart : LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → OracleComp spec pr.Y)
    (hcs : ∀ pos c b, IsTotalQueryBound (chainStart pos c b) (vp.sl.params.w - 1))
    (u : SlSecAdrs vp → pr.Y) :
    IsTotalQueryBound (buildHybTreeM pr collCall chainStart u)
      ((forsAddresses vp).length +
        xmssTreeCount vp.sl.params *
          (2 ^ vp.sl.params.hp * (vp.sl.params.len * (2 * (vp.sl.params.w - 1)) + 1) +
            (perfectInternalCoords vp.sl.params.hp).length)) := by
  unfold buildHybTreeM
  have hfors_step : ∀ (tbl : Adrs → Option pr.Y) (a : Adrs),
      IsTotalQueryBound (do let v ← evalNodeM pr collCall u tbl a; pure (Function.update tbl a (some v))) 1 :=
    fun tbl a => (isTotalQueryBound_bind (n₂ := 0) (evalNodeM_totalQueryBound pr collCall hcall u tbl a)
      fun _ => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
      (by omega)
  have hleaf : ∀ acc pos,
      IsTotalQueryBound (buildLeafM pr collCall chainStart acc pos)
        (vp.sl.params.len * (2 * (vp.sl.params.w - 1)) + 1) := by
    intro acc pos
    unfold buildLeafM
    have hvec : IsTotalQueryBound (Vector.ofFnM fun c : Fin vp.sl.params.len => do
        let b := SLHDSA.chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val
        let sigBlk ← chainStart pos c b
        let top ← slChainM pr collCall (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b
          (vp.sl.params.w - 1 - b)
        return (sigBlk, top))
        (∑ _c : Fin vp.sl.params.len, 2 * (vp.sl.params.w - 1)) :=
      isTotalQueryBound_ofFnM _ _ fun c =>
        (isTotalQueryBound_bind (hcs pos c _) fun sigBlk =>
          isTotalQueryBound_bind (n₂ := 0)
            (slChainM_totalQueryBound pr collCall hcall _ sigBlk _ _) fun _ =>
            (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
          (by omega)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hvec
    exact (isTotalQueryBound_bind hvec fun _ =>
      isTotalQueryBound_bind (n₂ := 0) (hcall .thLsl _ _) fun _ =>
        (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (by omega)
  have htree : ∀ acc coord,
      IsTotalQueryBound (buildTreeM pr collCall chainStart acc coord)
        (2 ^ vp.sl.params.hp * (vp.sl.params.len * (2 * (vp.sl.params.w - 1)) + 1) +
          (perfectInternalCoords vp.sl.params.hp).length) := by
    intro acc coord
    unfold buildTreeM
    have hl := isTotalQueryBound_foldlM
      (fun a lf => buildLeafM pr collCall chainStart a ⟨coord.layer, coord.tree, lf⟩)
      (vp.sl.params.len * (2 * (vp.sl.params.w - 1)) + 1)
      (fun a lf => hleaf a ⟨coord.layer, coord.tree, lf⟩) (List.finRange (2 ^ vp.sl.params.hp)) acc
    rw [List.length_finRange] at hl
    have hi := fun tbl₁ => isTotalQueryBound_foldlM
      (fun (tbl : Adrs → Option pr.Y) (zi : ℕ × ℕ) => do
        let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
        let l := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
        let r := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
        let v ← collCall .H a (l, r)
        return Function.update tbl a (some v))
      1
      (fun tbl zi => (isTotalQueryBound_bind (n₂ := 0) (hcall .H _ _) fun _ =>
        (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (by omega))
      (perfectInternalCoords vp.sl.params.hp) tbl₁
    exact (isTotalQueryBound_bind hl fun acc₁ =>
      isTotalQueryBound_bind (n₂ := 0) (hi acc₁.tbl) fun _ =>
        (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (by simp)
  have h1 := isTotalQueryBound_foldlM _ 1 hfors_step (forsAddresses vp) (fun _ => none)
  have h2 := fun init => isTotalQueryBound_foldlM (buildTreeM pr collCall chainStart) _
    htree (allXmssTreesList vp) init
  refine (isTotalQueryBound_bind h1 fun _ =>
    isTotalQueryBound_bind (n₂ := 0) (h2 _) fun _ =>
      (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono ?_
  rw [allXmssTreesList_length]
  simp

omit [Inhabited pr.Y] in
private theorem sfGrindAuxM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (id : LeafId) (md : pr.Digest) :
    ∀ k, IsTotalQueryBound (sfGrindAuxM pr collCall id md k) k
  | 0 => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | k + 1 => by
    unfold sfGrindAuxM
    refine isTotalQueryBound_bind (sfGrindAuxM_totalQueryBound collCall hcall id md k) fun prev => ?_
    cases prev with
    | some v => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 1)
    | none =>
      split_ifs
      · exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hcall .grind _ _) fun _ => by
          split_ifs <;> exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
          (by omega)
      · exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 1)

omit [Inhabited pr.Y] in
private theorem sfChainM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (id : LeafId) (ch : ℕ) (x : pr.Y) (j : ℕ) :
    ∀ k, IsTotalQueryBound (sfChainM pr collCall id ch x j k) k
  | 0 => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | k + 1 =>
    isTotalQueryBound_bind (sfChainM_totalQueryBound collCall hcall id ch x j k) fun _ =>
      hcall .F _ _

private theorem sfAnchorM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (S : Structure) (dig : LeafId → pr.Digest)
    (u : Fxmss.Rom.SkIdx vp.params S → pr.Y) (id : LeafId) :
    IsTotalQueryBound (sfAnchorM pr collCall S dig u id)
      (2 ^ vp.params.c + vp.params.lsf * (vp.params.w - 1) + 1) := by
  unfold sfAnchorM
  refine (isTotalQueryBound_bind (n₁ := 2 ^ vp.params.c) (n₂ := vp.params.lsf * (vp.params.w - 1) + 1)
    (sfGrindAuxM_totalQueryBound pr collCall hcall id (dig id) (2 ^ vp.params.c))
    fun gOpt => ?_).mono (by omega)
  cases gOpt with
  | some dc =>
    have hsig : IsTotalQueryBound (Vector.ofFnM fun ch : Fin vp.params.lsf =>
        sfChainM pr collCall id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0
          (WotsC.digit pr dc.1 ch.val))
        (∑ ch : Fin vp.params.lsf, WotsC.digit pr dc.1 ch.val) :=
      isTotalQueryBound_ofFnM _ _ fun ch => sfChainM_totalQueryBound pr collCall hcall _ _ _ _ _
    have htops : ∀ sigVec : Vector pr.Y vp.params.lsf,
        IsTotalQueryBound (Vector.ofFnM fun ch : Fin vp.params.lsf =>
          sfChainM pr collCall id ch.val sigVec[ch.val]
            (WotsC.digit pr dc.1 ch.val) (vp.params.w - 1 - WotsC.digit pr dc.1 ch.val))
          (∑ ch : Fin vp.params.lsf, (vp.params.w - 1 - WotsC.digit pr dc.1 ch.val)) :=
      fun _ => isTotalQueryBound_ofFnM _ _ fun ch => sfChainM_totalQueryBound pr collCall hcall _ _ _ _ _
    have hsum : (∑ ch : Fin vp.params.lsf, WotsC.digit pr dc.1 ch.val) +
        (∑ ch : Fin vp.params.lsf, (vp.params.w - 1 - WotsC.digit pr dc.1 ch.val)) =
        vp.params.lsf * (vp.params.w - 1) := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ ch : Fin vp.params.lsf,
          WotsC.digit pr dc.1 ch.val + (vp.params.w - 1 - WotsC.digit pr dc.1 ch.val) = vp.params.w - 1 := by
        intro ch; have hlt := WotsC.digit_lt pr dc.1 ch.val; omega
      simp [hterm]
    exact (isTotalQueryBound_bind hsig fun sigVec =>
      isTotalQueryBound_bind (htops sigVec) fun tops =>
        isTotalQueryBound_bind (n₂ := 0) (hcall .thLsf _ tops) fun _ =>
          (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
      (by omega)
  | none =>
    have htops : IsTotalQueryBound (Vector.ofFnM fun ch : Fin vp.params.lsf =>
        sfChainM pr collCall id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (vp.params.w - 1))
        (∑ _ch : Fin vp.params.lsf, (vp.params.w - 1)) :=
      isTotalQueryBound_ofFnM _ _ fun _ => sfChainM_totalQueryBound pr collCall hcall _ _ _ _ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htops
    exact (isTotalQueryBound_bind htops fun tops =>
      isTotalQueryBound_bind (n₂ := 0) (hcall .thLsf _ tops) fun _ =>
        (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
      (by omega)

/-- Number of internal nodes in `S` within the subtree rooted at `(z, i)` (for `z ≤ hsf`). -/
def subtreeInternalBound (S : Structure) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | z + 1, i =>
    if z + 1 ≤ vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∈ S.anchors then 0
    else if z + 1 ≤ vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∈ S.internal then
      subtreeInternalBound S z (2 * i) + subtreeInternalBound S z (2 * i + 1) + 1
    else 0

omit [Inhabited pr.Y] in
private theorem sfTreeNodeM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (S : Structure) (leafTbl : LeafId → pr.Y) :
    ∀ z i tbl, IsTotalQueryBound (sfTreeNodeM pr collCall S leafTbl z i tbl)
      (subtreeInternalBound (vp := vp) S z i)
  | 0, i, tbl => by
    unfold sfTreeNodeM subtreeInternalBound
    split_ifs <;> exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | z + 1, i, tbl => by
    unfold sfTreeNodeM subtreeInternalBound
    split_ifs
    · exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
    · refine (isTotalQueryBound_bind
          (n₁ := subtreeInternalBound (vp := vp) S z (2 * i))
          (n₂ := subtreeInternalBound (vp := vp) S z (2 * i + 1) + 1)
          (sfTreeNodeM_totalQueryBound collCall hcall S leafTbl z (2 * i) tbl)
        fun ⟨lOpt, tbl₁⟩ =>
          isTotalQueryBound_bind
            (n₁ := subtreeInternalBound (vp := vp) S z (2 * i + 1))
            (n₂ := 1)
            (sfTreeNodeM_totalQueryBound collCall hcall S leafTbl z (2 * i + 1) tbl₁)
            fun ⟨rOpt, tbl₂⟩ => ?_).mono (by omega)
      cases lOpt with
      | none => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 1)
      | some l =>
        cases rOpt with
        | none => exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 1)
        | some r =>
          exact (isTotalQueryBound_bind (n₂ := 0) (hcall .H _ (l, r)) fun _ =>
            (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
            (by omega)
    · exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)

/-- **Stage-1 stateful FXMSS precomputation `O_coll` query bound** (`sfPrecompM`):
every anchor takes at most `2^c + lsf * (w - 1) + 1` `O_coll` queries, plus at most
`subtreeInternalBound S hsf 0` internal-node `H` queries. -/
theorem sfPrecompM_totalQueryBound {ι : Type} {spec : OracleSpec ι}
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (hcall : ∀ i a msg, IsTotalQueryBound (collCall i a msg) 1)
    (S : Structure) (ys : Fxmss.Rom.Anchor vp.params S → pr.Digest)
    (u : Fxmss.Rom.SkIdx vp.params S → pr.Y) [Inhabited pr.Digest] :
    IsTotalQueryBound (sfPrecompM pr collCall S ys u)
      ((Fxmss.Rom.anchorList vp.params S).length *
          (2 ^ vp.params.c + vp.params.lsf * (vp.params.w - 1) + 1) +
        subtreeInternalBound (vp := vp) S vp.params.hsf 0) := by
  unfold sfPrecompM
  have hfold := isTotalQueryBound_foldlM
    (fun (acc : (LeafId → Option (WotsC.Sig pr)) × (LeafId → pr.Y)) id => do
      let (wOpt, lv) ← sfAnchorM pr collCall S (Fxmss.Rom.digOf pr ys) u id
      pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv))
    (2 ^ vp.params.c + vp.params.lsf * (vp.params.w - 1) + 1)
    (fun acc id => (isTotalQueryBound_bind (n₂ := 0)
      (sfAnchorM_totalQueryBound pr collCall hcall S _ u id) fun _ =>
        (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (by omega))
    (Fxmss.Rom.anchorList vp.params S) (fun _ => none, fun _ => default)
  exact (isTotalQueryBound_bind hfold fun ⟨wotsTbl, leafTbl⟩ =>
    isTotalQueryBound_bind (n₂ := 0)
      (sfTreeNodeM_totalQueryBound pr collCall hcall S leafTbl vp.params.hsf 0 (fun _ => none))
      fun _ => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
    (by omega)

end Stage1Bounds

/-! ## 3. Lazy-cached standalone `PRF` reduction (`B_sl_prfLazyAdv`, `theorem_4_3_lazy`) -/

section LazySlPrf

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq Msg]

/-- Helper: lazy stateless signing via a monadic secret provider `sec`. -/
def slSignLazyM {m : Type → Type} [Monad m]
    (pk : pr.PkSeed) (pkSl : pr.Y) (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (msg : List Byte) (R : pr.Y) : m (Stateless.Sig pr) :=
  letI := pubQ pr m
  SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
    (guardSec pr sec pk) msg pk pkSl R

/-- Lazy standalone SLH-DSA signing handler over a monadic secret provider `sec` (queries `sec`
only at secret-key addresses actually touched by `signInternalWithSecretRandomizerM`). -/
noncomputable def slLazyPhaseImpl {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (pk : pr.PkSeed) (pkSl : pr.Y) (skPrf : pr.SkPrf)
    (sec : pr.PkSeed × SecAdrs → m pr.Y) :
    QueryImpl (SlStandaloneSpec pr Msg) (StateT (List Msg) m) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List Msg) m) +
  (fun msg => do
    let optRand ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : StateT (List Msg) m pr.Y)
    let R := pr.PRFmsgSl skPrf optRand (pureMsg Msg enc msg)
    let σ ← (liftM (slSignLazyM pr pk pkSl sec (pureMsg Msg enc msg) R) :
      StateT (List Msg) m (Stateless.Sig pr))
    modify fun log => log ++ [msg]
    return σ)

/-- Lazy standalone SLH-DSA phase over a secret provider `sec`: computes `pkSl ← slRootM sec pk`
and runs `A.adv.main (pk, pkSl)` through `slLazyPhaseImpl`, then checks freshness and verifies. -/
noncomputable def slLazyPhaseM {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs)
    (pk : pr.PkSeed) (skPrf : pr.SkPrf) (sec : pr.PkSeed × SecAdrs → m pr.Y) : m Bool := do
  let pkSl ← slRootM pr sec pk
  let ((m, σ), log) ← (simulateQ (slLazyPhaseImpl pr Msg enc pk pkSl skPrf sec)
    (A.adv.main (pk, pkSl))).run []
  return (!decide (m ∈ log) &&
    SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA (pureMsg Msg enc m) σ ⟨pk, pkSl⟩)

/-- **Uncached lazy standalone `PRF` reduction (`B_sl_prfLazy`)**: queries `PRF` on demand via
`secQ pr` (never enumerates the full virtual hypertree). -/
noncomputable def B_sl_prfLazy {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    OracleComp (PrfSpec pr) Bool := do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (PrfSpec pr) _)
  let skPrf ← (liftM ($ᵗ pr.SkPrf : ProbComp pr.SkPrf) : OracleComp (PrfSpec pr) _)
  slLazyPhaseM pr Msg enc A pk skPrf (secQ pr)

/-- Secret-key input domain of `B_sl_prfLazy` at `pk`: the `slSecretList vp.sl` addresses. -/
noncomputable def slPrfInputs (pk : pr.PkSeed) : Finset (pr.PkSeed × Adrs) :=
  (slSecretList vp.sl).toFinset.image fun a => (pk, a)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq Msg] in
private theorem card_slPrfInputs (pk : pr.PkSeed) :
    (slPrfInputs pr pk).card ≤ slSecretCount vp.sl := by
  refine Finset.card_image_le.trans ?_
  rw [← length_slSecretList]
  exact List.toFinset_card_le _

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq Msg] in
private theorem aqs_liftP_sl {α : Type} (p : ProbComp α) (pk : pr.PkSeed) :
    (liftM p : OracleComp (PrfSpec pr) α).AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) :=
  (isQueryBoundP_zero_iff _ _).1 ((isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
    rcases t with _ | _
    · exact absurd trivial ht
    · rfl)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq Msg] in
private theorem aqs_guardSec_sl (pk : pr.PkSeed) (a b : Adrs)
    (hb : b ∈ constructionAddresses vp.sl) (hab : .inl a ∈ childAdrs vp.sl b) :
    (guardSec pr (secQ pr) pk a).AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) := by
  unfold guardSec
  split
  · rw [secQ, PRFScheme.functionQuery, allQueriesSatisfy_query_iff]
    exact Finset.mem_image.2 ⟨a, List.mem_toFinset.2 (mem_slSecretList hb hab), rfl⟩
  · exact allQueriesSatisfy_pure _ _

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq Msg] in
private theorem aqs_slRootM_sl (pk : pr.PkSeed) :
    (slRootM pr (secQ pr) pk).AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) := by
  unfold slRootM
  exact @keygenInternalWithSecretM_pred_of_ledger _ _ _
    (fun {_} (oa : OracleComp (PrfSpec pr) _) =>
      oa.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)))
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
    _ pr.toSLHDSA.core _ (fun a b hb hab => aqs_guardSec_sl pr pk a b hb hab) (pubQ pr _) pk
    (fun _ _ _ => allQueriesSatisfy_pure _ _)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq Msg] in
private theorem aqs_slLazyPhaseImpl (pk : pr.PkSeed) (pkSl : pr.Y) (skPrf : pr.SkPrf)
    (t : (SlStandaloneSpec pr Msg).Domain) (log : List Msg) :
    ((slLazyPhaseImpl pr Msg enc pk pkSl skPrf (secQ pr) t).run log).AllQueriesSatisfy
      (CachedPRF.InSet (slPrfInputs pr pk)) := by
  rcases t with n | msg
  · dsimp only [slLazyPhaseImpl, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget, QueryImpl.ofLift]
    change ((StateT.lift (liftM (liftM (unifSpec.query n) : ProbComp _) :
      OracleComp (PrfSpec pr) _) :
      StateT (List Msg) (OracleComp (PrfSpec pr)) _).run log).AllQueriesSatisfy _
    rw [StateT.run_lift]
    exact allQueriesSatisfy_bind (aqs_liftP_sl pr _ pk) fun _ => allQueriesSatisfy_pure _ _
  · dsimp only [slLazyPhaseImpl, HAdd.hAdd, QueryImpl.add]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_modify,
      StateT.run_pure, bind_assoc, pure_bind]
    refine allQueriesSatisfy_bind (aqs_liftP_sl pr ($ᵗ pr.Y) pk) fun optRand => ?_
    refine allQueriesSatisfy_bind ?_ fun _ => allQueriesSatisfy_pure _ _
    exact @signInternalWithSecretRandomizerM_pred_of_ledger _ _ _
      (fun {_} (oa : OracleComp (PrfSpec pr) _) =>
        oa.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)))
      (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
      _ pr.toSLHDSA.core _ (fun a b hb hab => aqs_guardSec_sl pr pk a b hb hab) (pubQ pr _) _ pk
      pkSl _ (fun _ _ _ => allQueriesSatisfy_pure _ _) (allQueriesSatisfy_pure _ _)

omit [Fintype pr.Y] in
/-- **`cacheAdv (B_sl_prfLazy A)` makes at most `q₁ = slSecretCount vp.sl` distinct PRF queries**,
issuing queries lazily only at secret-key addresses accessed during keygen and the `q_s` signing
queries. -/
theorem cacheAdv_B_sl_prfLazy_bound {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    (CachedPRF.cacheAdv (B_sl_prfLazy pr Msg enc A)).IsQueryBoundP Notions.IsPRFQuery
      (slSecretCount vp.sl) := by
  have hlift : ∀ {α : Type} (p : ProbComp α) (k : α → OracleComp (PrfSpec pr) Bool),
      (simulateQ CachedPRF.cacheImpl ((liftM p : OracleComp (PrfSpec pr) α) >>= k)).run ∅ =
        (liftM p : OracleComp (PrfSpec pr) α) >>= fun x =>
          (simulateQ CachedPRF.cacheImpl (k x)).run ∅ := fun p k => by
    rw [simulateQ_bind, StateT.run_bind, CachedPRF.cacheImpl_liftM_run, bind_map_left]
  have hzero : ∀ {α : Type} (p : ProbComp α),
      (liftM p : OracleComp (PrfSpec pr) α).IsQueryBoundP Notions.IsPRFQuery 0 := fun p =>
    (isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
      rcases t with _ | _
      · exact absurd ht (by simp [Notions.IsPRFQuery])
      · rfl
  rw [CachedPRF.cacheAdv, StateT.run'_eq, isQueryBoundP_map_iff, B_sl_prfLazy, hlift]
  refine (isQueryBoundP_bind (n := 0) (m := slSecretCount vp.sl) (hzero _) fun pk _ => ?_).mono
    (by omega)
  rw [hlift]
  refine (isQueryBoundP_bind (n := 0) (m := slSecretCount vp.sl) (hzero _) fun skPrf _ => ?_).mono
    (by omega)
  refine (CachedPRF.cache_run_bound (slPrfInputs pr pk) _ ∅ ?_).mono ?_
  · unfold slLazyPhaseM
    refine allQueriesSatisfy_bind (aqs_slRootM_sl pr pk) fun pkSl => ?_
    refine allQueriesSatisfy_bind
      (aqs_simulateQ_run _ (aqs_slLazyPhaseImpl pr Msg enc pk pkSl skPrf) _ []) fun _ =>
      allQueriesSatisfy_pure _ _
  · have h1 : CachedPRF.fresh (slPrfInputs pr pk)
        (∅ : CachedPRF.Cache (pr.PkSeed × Adrs) pr.Y) = slPrfInputs pr pk := by
      ext; simp [CachedPRF.fresh]
    rw [h1]
    exact card_slPrfInputs pr pk

/-- **Lazy-cached standalone `PRF` adversary (`B_sl_prfLazyAdv`)** (Definition 4.3, budget
`q₁ = slSecretCount vp.sl`). -/
noncomputable def B_sl_prfLazyAdv {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Notions.PRFAdversary (pr.PkSeed × Adrs) pr.Y (slSecretCount vp.sl) where
  run := CachedPRF.cacheAdv (B_sl_prfLazy pr Msg enc A)
  queryBound := cacheAdv_B_sl_prfLazy_bound pr Msg enc A

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
private theorem slLazyPhaseM_natural {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂]
    [LawfulMonad m₁] [LawfulMonad m₂] [MonadLiftT ProbComp m₁] [MonadLiftT ProbComp m₂]
    (Φ : m₁ →ᵐ m₂) (hΦ : LiftPres Φ)
    {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs)
    (pk : pr.PkSeed) (skPrf : pr.SkPrf) (sec : pr.PkSeed × SecAdrs → m₁ pr.Y) :
    Φ (slLazyPhaseM pr Msg enc A pk skPrf sec) =
      slLazyPhaseM pr Msg enc A pk skPrf (fun x => Φ (sec x)) := by
  have hguard : ∀ a, Φ (guardSec pr sec pk a) = guardSec pr (fun x => Φ (sec x)) pk a := by
    intro a; unfold guardSec; split <;> simp
  have hroot : Φ (slRootM pr sec pk) = slRootM pr (fun x => Φ (sec x)) pk :=
    slRootM_natural pr Φ sec pk
  have hsign : ∀ pkSl msg R,
      Φ (slSignLazyM pr pk pkSl sec msg R) =
      slSignLazyM pr pk pkSl (fun x => Φ (sec x)) msg R := by
    intro pkSl msg R
    unfold slSignLazyM
    let _ := pubQ pr m₁
    let _ := pubQ pr m₂
    let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core) m₁ m₂ :=
      { toMonadHom := Φ
        map_query' := fun _ => MonadHom.mmap_pure Φ _ }
    exact SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
      pr.toSLHDSA.core G (guardSec pr sec pk) (guardSec pr (fun x => Φ (sec x)) pk)
      (fun a _ => hguard a) msg pk pkSl R
  unfold slLazyPhaseM
  rw [MonadHom.mmap_bind, hroot]
  refine bind_congr fun pkSl => ?_
  have hstep : ∀ t,
      MonadHom.stateT (List Msg) Φ (slLazyPhaseImpl pr Msg enc pk pkSl skPrf sec t) =
        slLazyPhaseImpl pr Msg enc pk pkSl skPrf (fun x => Φ (sec x)) t := by
    rintro (k | msg)
    · exact MonadHom.stateT_liftPres Φ hΦ _
    · dsimp only [slLazyPhaseImpl, HAdd.hAdd, QueryImpl.add]
      ext log
      simp only [MonadHom.stateT_run, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind]
      change Φ ((liftM ($ᵗ pr.Y : ProbComp pr.Y) : m₁ pr.Y) >>= fun optRand =>
        (slSignLazyM pr pk pkSl sec (pureMsg Msg enc msg)
          (pr.PRFmsgSl skPrf optRand (pureMsg Msg enc msg))) >>= fun σ =>
            pure (σ, log ++ [msg])) = _
      rw [MonadHom.mmap_bind, hΦ]
      refine bind_congr fun optRand => ?_
      rw [MonadHom.mmap_bind, hsign]
      exact bind_congr fun σ => MonadHom.mmap_pure _ _
  have hsim : Φ ((simulateQ (slLazyPhaseImpl pr Msg enc pk pkSl skPrf sec)
        (A.adv.main (pk, pkSl))).run []) =
      (simulateQ (slLazyPhaseImpl pr Msg enc pk pkSl skPrf (fun x => Φ (sec x)))
        (A.adv.main (pk, pkSl))).run [] := by
    rw [← MonadHom.stateT_run (List Msg) Φ, MonadHom.mmap_simulateQ _ _ _ hstep]
  rw [MonadHom.mmap_bind, hsim]
  exact bind_congr fun _ => MonadHom.mmap_pure _ _

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
private theorem slLazyPhaseM_pure_eq_slPhaseM {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs)
    (pk : pr.PkSeed) (skPrf : pr.SkPrf) (u : SlSecAdrs vp → pr.Y) :
    slLazyPhaseM (m := ProbComp) pr Msg enc A pk skPrf
      (fun x => pure (slSecOf pr u x.2.1)) =
    slPhaseM (m := ProbComp) pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2)) := by
  have hroot : slRootM (m := ProbComp) pr (fun x => pure (slSecOf pr u x.2.1)) pk =
      pure (slRootDet pr pk u) := by
    let Φpure : Id →ᵐ ProbComp :=
      { toFun := fun {_} x => pure (Id.run x)
        toFun_pure' := fun _ => rfl
        toFun_bind' := fun _ _ => by rw [pure_bind]; rfl }
    have h := slRootM_natural pr Φpure (fun x => pure (slSecOf pr u x.2.1)) pk
    exact h.symm
  have hsign : ∀ pkSl msg R,
      slSignLazyM (m := ProbComp) pr pk pkSl (fun x => pure (slSecOf pr u x.2.1)) msg R =
      pure (slSignDet pr pk pkSl u msg R) := by
    intro pkSl msg R
    unfold slSignLazyM slSignDet
    let _ := pubQ pr Id
    let _ := pubQ pr ProbComp
    let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core) Id ProbComp :=
      { toMonadHom :=
          { toFun := fun {_} x => pure (Id.run x)
            toFun_pure' := fun _ => rfl
            toFun_bind' := fun _ _ => by rw [pure_bind]; rfl }
        map_query' := fun _ => rfl }
    have h := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
      pr.toSLHDSA.core G (fun a => (pure (slSecOf pr u a) : Id pr.Y))
      (guardSec pr (fun x => (pure (slSecOf pr u x.2.1) : ProbComp pr.Y)) pk)
      (fun a ha => by unfold guardSec; simp [ha]) msg pk pkSl R
    exact h.symm
  unfold slLazyPhaseM slPhaseM
  rw [hroot, pure_bind]
  have himpl : slLazyPhaseImpl (m := ProbComp) pr Msg enc pk (slRootDet pr pk u) skPrf
        (fun x => pure (slSecOf pr u x.2.1)) =
      slPhaseImpl (m := ProbComp) pr Msg enc pk (slRootDet pr pk u) u
        (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2)) := by
    funext q
    rcases q with n | msg
    · rfl
    · dsimp only [slLazyPhaseImpl, slPhaseImpl, HAdd.hAdd, QueryImpl.add]
      ext log
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_modify,
        StateT.run_pure, bind_assoc, pure_bind]
      refine bind_congr fun optRand => ?_
      rw [hsign, pure_bind]
  rw [himpl]
  refine bind_congr fun z => ?_
  rcases z with ⟨⟨m, σ⟩, log⟩
  dsimp only
  rw [statelessVerify_eq_verifyInternal]
  exact congrArg pure (by congr 2; exact decide_eq_decide.2 Iff.rfl)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] in
private theorem simulateQ_prf_congr_aqs {α : Type} (pk : pr.PkSeed)
    (oa : OracleComp (PrfSpec pr) α)
    (impl₁ impl₂ : QueryImpl (PrfSpec pr) ProbComp)
    (hoa : oa.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)))
    (hL : ∀ n, impl₁ (.inl n) = impl₂ (.inl n))
    (hR : ∀ q ∈ slPrfInputs pr pk, impl₁ (.inr q) = impl₂ (.inr q)) :
    simulateQ impl₁ oa = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with n | q
    · rw [hL n]; exact bind_congr fun u => ih u (hoa.2 u)
    · rw [hR q hoa.1]; exact bind_congr fun u => ih u (hoa.2 u)

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Real world of `B_sl_prfLazy` equals `slGame0`**. -/
theorem prfReal_B_sl_prfLazy {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    (Notions.KeyedHash.toPRF (prfF pr)).prfRealExperiment (B_sl_prfLazy pr Msg enc A) =
      slGame0 pr Msg enc A := by
  unfold PRFScheme.prfRealExperiment slGame0 B_sl_prfLazy
  refine bind_congr fun skSeed => ?_
  set Φ := simulateQ' ((Notions.KeyedHash.toPRF (prfF pr)).prfRealQueryImpl skSeed)
  have hL : LiftPres Φ := Claim411.liftPres_real pr skSeed
  change Φ _ = _
  rw [MonadHom.mmap_bind, hL]
  refine bind_congr fun pk => ?_
  rw [MonadHom.mmap_bind, hL]
  refine bind_congr fun skPrf => ?_
  let prog : OracleComp (PrfSpec pr) Bool := slLazyPhaseM pr Msg enc A pk skPrf (secQ pr)
  have haqs : prog.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) := by
    unfold prog slLazyPhaseM
    refine allQueriesSatisfy_bind (aqs_slRootM_sl pr pk) fun pkSl => ?_
    refine allQueriesSatisfy_bind
      (aqs_simulateQ_run _ (aqs_slLazyPhaseImpl pr Msg enc pk pkSl skPrf) _ []) fun _ =>
      allQueriesSatisfy_pure _ _
  let u0 : SlSecAdrs vp → pr.Y := fun a => pr.PRF pk skSeed a.1
  let implU : QueryImpl (PrfSpec pr) ProbComp
    | .inl n => liftM (unifSpec.query n)
    | .inr q => pure (slSecOf pr u0 q.2)
  have hcongr : simulateQ ((Notions.KeyedHash.toPRF (prfF pr)).prfRealQueryImpl skSeed) prog =
      simulateQ implU prog := by
    refine simulateQ_prf_congr_aqs pr pk prog _ implU haqs (fun _ => rfl) fun q hq => ?_
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hq
    change (pure (pr.PRF pk skSeed a') : ProbComp pr.Y) = (pure (slSecOf pr u0 a') : ProbComp pr.Y)
    simp [slSecOf, ha', u0]
  change simulateQ ((Notions.KeyedHash.toPRF (prfF pr)).prfRealQueryImpl skSeed) prog = _
  rw [hcongr]
  set Φu := simulateQ' implU
  have hLu : LiftPres Φu := fun p => by
    change simulateQ implU (liftM p) = p
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      change simulateQ implU ((PrfSpec pr).query (.inl t) >>= fun x => liftM (k x)) = _
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_congr fun x => ih x
  change Φu (slLazyPhaseM pr Msg enc A pk skPrf (secQ pr)) = _
  rw [slLazyPhaseM_natural pr Msg enc Φu hLu A pk skPrf (secQ pr)]
  have hsecu : (fun x : pr.PkSeed × SecAdrs => Φu (secQ pr x)) =
      fun x => pure (slSecOf pr u0 x.2.1) := by
    funext x
    change simulateQ implU ((PrfSpec pr).query (.inr (x.1, x.2.1))) = _
    rfl
  rw [hsecu]
  exact slLazyPhaseM_pure_eq_slPhaseM pr Msg enc A pk skPrf u0

omit [Fintype pr.Y] in
/-- **Ideal world of `B_sl_prfLazy` is distributed as `slGame1`**: eager uniform `u` on
`SlSecAdrs vp` matches lazy random-oracle sampling on `(pk, a)`. -/
theorem prfIdeal_B_sl_prfLazy {qs : ℕ}
    (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    PRFScheme.prfIdealExperiment (B_sl_prfLazy pr Msg enc A) =ᵈ slGame1 pr Msg enc A := by
  unfold PRFScheme.prfIdealExperiment slGame1 B_sl_prfLazy
  set Ψ := simulateQ' (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y))
  have hL : LiftPres Ψ := Claim411.liftPres_unifFwd _
  change (Ψ _).run' ∅ =ᵈ _
  rw [MonadHom.mmap_bind, hL, Claim411.run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun pk => ?_
  rw [MonadHom.mmap_bind, hL, Claim411.run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun skPrf => ?_
  -- Step 1: By `slLazyPhaseM_natural`, `Ψ (slLazyPhaseM secQ)` runs `slLazyPhaseM` with `randomOracle`.
  change (Ψ (slLazyPhaseM pr Msg enc A pk skPrf (secQ pr))).run' ∅ =ᵈ _
  rw [slLazyPhaseM_natural pr Msg enc Ψ hL A pk skPrf (secQ pr)]
  have hsec : (fun x : pr.PkSeed × SecAdrs => Ψ (secQ pr x)) =
      fun x => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1) :=
    funext fun x => PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery _
  rw [hsec]
  -- Step 2: Couple lazy `randomOracle` cache `c` with eager uniform `u : SlSecAdrs vp → pr.Y`
  -- on any program whose queries all lie in `slPrfInputs pr pk`.
  let prog : OracleComp (PrfSpec pr) Bool := slLazyPhaseM pr Msg enc A pk skPrf (secQ pr)
  have haqs : prog.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) := by
    unfold prog slLazyPhaseM
    refine allQueriesSatisfy_bind (aqs_slRootM_sl pr pk) fun pkSl => ?_
    refine allQueriesSatisfy_bind
      (aqs_simulateQ_run _ (aqs_slLazyPhaseImpl pr Msg enc pk pkSl skPrf) _ []) fun _ =>
      allQueriesSatisfy_pure _ _
  have hcongr_aqs : ∀ {α : Type} (oa : OracleComp (PrfSpec pr) α)
      (impl₁ impl₂ : QueryImpl (PrfSpec pr) ProbComp),
      oa.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) →
      (∀ n, impl₁ (.inl n) = impl₂ (.inl n)) →
      (∀ q ∈ slPrfInputs pr pk, impl₁ (.inr q) = impl₂ (.inr q)) →
      simulateQ impl₁ oa = simulateQ impl₂ oa := by
    intro α oa impl₁ impl₂ hoa hL' hR'
    induction oa using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      simp only [simulateQ_bind, simulateQ_spec_query]
      rcases t with n | q
      · rw [hL' n]; exact bind_congr fun u => ih u (hoa.2 u)
      · rw [hR' q hoa.1]; exact bind_congr fun u => ih u (hoa.2 u)
  let evalWith (c : Claim411.PrfCache pr) (u : SlSecAdrs vp → pr.Y) :
      QueryImpl (PrfSpec pr) ProbComp
    | .inl n => liftM (unifSpec.query n)
    | .inr q => pure (match c q with | some y => y | none => slSecOf pr u q.2)
  have hgen : ∀ (oa : OracleComp (PrfSpec pr) Bool) (c : Claim411.PrfCache pr),
      oa.AllQueriesSatisfy (CachedPRF.InSet (slPrfInputs pr pk)) →
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y)) oa).run' c =ᵈ
        ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun u => simulateQ (evalWith c u) oa) := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure b =>
      intro c _
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (EvalDistEq.bind_const ($ᵗ (SlSecAdrs vp → pr.Y)) (pure b)).symm
    | query_bind t k ih =>
      intro c hoa
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      rcases t with n | ⟨pk', a⟩
      · have hcoin : (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y) (.inl n)).run c =
            (fun x => (x, c)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
          simp [PRFScheme.prfIdealQueryImpl, unifFwdImpl, StateT.run_monadLift]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, hcoin,
          bind_map_left, map_bind, evalWith]
        refine (EvalDistEq.bind_right _ fun x => by
          simpa only [StateT.run'_eq] using ih x c (hoa.2 x)).trans ?_
        exact (EvalDistEq.bind_bind_swap _ _ _).symm
      · have hmem : (pk', a) ∈ slPrfInputs pr pk := hoa.1
        obtain ⟨a', ha', heq⟩ := Finset.mem_image.1 hmem
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        let aSec : SlSecAdrs vp := ⟨a', ha'⟩
        have hro : (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y)
            (.inr (pk, a'))).run c =
            ((pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, a')).run c := rfl
        cases hcval : c (pk, a') with
        | some y =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, hro,
            randomOracle.run_eq, hcval, pure_bind, evalWith]
          simpa only [StateT.run'_eq] using ih y c (hoa.2 y)
        | none =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, hro,
            randomOracle.run_eq, hcval, map_bind, bind_assoc, pure_bind, evalWith]
          have hstep : (($ᵗ pr.Y : ProbComp pr.Y) >>= fun y =>
              Prod.fst <$> (simulateQ (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y))
                (k y)).run (c.cacheQuery (pk, a') y)) =ᵈ
              (($ᵗ pr.Y : ProbComp pr.Y) >>= fun y =>
                $ᵗ (SlSecAdrs vp → pr.Y) >>= fun u =>
                  simulateQ (evalWith (c.cacheQuery (pk, a') y) u) (k y)) :=
            EvalDistEq.bind_right _ fun y => by
              simpa only [StateT.run'_eq] using ih y (c.cacheQuery (pk, a') y) (hoa.2 y)
          refine hstep.trans ?_
          have hcongr_y : ∀ (y : pr.Y) (u : SlSecAdrs vp → pr.Y),
              simulateQ (evalWith (c.cacheQuery (pk, a') y) u) (k y) =
                simulateQ (evalWith c (Function.update u aSec y)) (k y) := by
            intro y u
            refine hcongr_aqs (k y) _ _ (hoa.2 y) (fun _ => rfl) fun q hq => ?_
            obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hq
            dsimp only [evalWith]
            by_cases hba : b' = a'
            · subst hba
              simp only [QueryCache.cacheQuery_self, hcval, slSecOf, hb', ↓reduceDIte]
              have hsel : (⟨b', hb'⟩ : SlSecAdrs vp) = aSec := rfl
              rw [hsel, Function.update_self]
            · have hqne : (pk, b') ≠ (pk, a') := fun e => hba (congrArg Prod.snd e)
              rw [QueryCache.cacheQuery_of_ne _ _ hqne]
              cases c (pk, b') with
              | some v => rfl
              | none =>
                simp only [slSecOf, hb', ↓reduceDIte]
                have hne : (⟨b', hb'⟩ : SlSecAdrs vp) ≠ aSec := fun e => hba (congrArg Subtype.val e)
                rw [Function.update_of_ne hne]
          have hres := Repro.resample aSec (fun u : SlSecAdrs vp → pr.Y =>
            simulateQ (evalWith c u) (k (u aSec)))
          refine (EvalDistEq.trans (EvalDistEq.bind_right _ fun y =>
            EvalDistEq.bind_right _ fun u => ?_) hres).trans (EvalDistEq.bind_right _ fun u => ?_)
          · rw [hcongr_y y u, Function.update_self]
          · have hsel : slSecOf pr u a' = u aSec := by simp [slSecOf, ha', aSec]
            rw [hsel]
  have h1 := hgen prog ∅ haqs
  have hL_eq : (slLazyPhaseM pr Msg enc A pk skPrf
      (fun x => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1))).run' ∅ =
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y)) prog).run' ∅ := by
    unfold prog
    change _ = (Ψ (slLazyPhaseM pr Msg enc A pk skPrf (secQ pr))).run' ∅
    rw [slLazyPhaseM_natural pr Msg enc Ψ hL A pk skPrf (secQ pr), hsec]
  rw [hL_eq]
  refine h1.trans (EvalDistEq.bind_right _ fun u => ?_)
  have hR_eq : simulateQ (evalWith ∅ u) prog =
      slPhaseM (m := ProbComp) pr Msg enc A pk u (fun x => pure (pr.PRFmsgSl skPrf x.1 x.2)) := by
    unfold prog
    set Φu := simulateQ' (evalWith ∅ u)
    have hLu : LiftPres Φu := fun p => by
      change simulateQ (evalWith ∅ u) (liftM p) = p
      induction p using OracleComp.inductionOn with
      | pure a => simp
      | query_bind t k ih =>
        change simulateQ (evalWith ∅ u) ((PrfSpec pr).query (.inl t) >>= fun x => liftM (k x)) = _
        rw [simulateQ_bind, simulateQ_spec_query]
        exact bind_congr fun x => ih x
    change Φu (slLazyPhaseM pr Msg enc A pk skPrf (secQ pr)) = _
    rw [slLazyPhaseM_natural pr Msg enc Φu hLu A pk skPrf (secQ pr)]
    have hsecu : (fun x : pr.PkSeed × SecAdrs => Φu (secQ pr x)) =
        fun x => pure (slSecOf pr u x.2.1) := by
      funext x
      change simulateQ (evalWith ∅ u) ((PrfSpec pr).query (.inr (x.1, x.2.1))) = _
      simp [evalWith]
    rw [hsecu]
    exact slLazyPhaseM_pure_eq_slPhaseM pr Msg enc A pk skPrf u
  rw [hR_eq]

omit [Fintype pr.Y] in
/-- **Hop 1 with lazy-cached `B_sl_prfLazyAdv`**: exact same bound as `hop1_prf`, with the lazy
cached PRF reduction querying only accessed secret addresses (`≤ slSecretCount vp.sl`). -/
theorem hop1_prf_lazy {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Pr{let b ← slGame0 pr Msg enc A}[b = true] ≤
      Pr{let b ← slGame1 pr Msg enc A}[b = true] +
        Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfLazyAdv pr Msg enc A) := by
  have hcache : Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfLazyAdv pr Msg enc A) =
      (Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (B_sl_prfLazy pr Msg enc A) :=
    CachedPRF.prfAdvantage_cacheAdv _ _
  have h0 : 𝒟[slGame0 pr Msg enc A] {true} =
      𝒟[(Notions.KeyedHash.toPRF (prfF pr)).prfRealExperiment (B_sl_prfLazy pr Msg enc A)] {true} :=
    congrArg (fun m => 𝒟[m] {true}) (prfReal_B_sl_prfLazy pr Msg enc A).symm
  have h1 : 𝒟[slGame1 pr Msg enc A] {true} =
      𝒟[PRFScheme.prfIdealExperiment (B_sl_prfLazy pr Msg enc A)] {true} := by
    have htop : (⊤ : MeasurableSpace Bool) = (inferInstance : MeasurableSpace Bool) :=
      MeasurableSpace.ext fun _ => ⟨fun _ => MeasurableSet.of_discrete, fun _ => trivial⟩
    simpa only [htop] using congrArg (fun μ => μ {true})
      (prfIdeal_B_sl_prfLazy pr Msg enc A).symm.evalDist_eq
  rw [hcache, prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, h0, h1]
  unfold PRFScheme.prfAdvantage
  exact (ENNReal.absDiff_le_iff.1 le_rfl).1

/-- **Theorem 4.3 with lazy-cached `B_sl_prfLazyAdv` (`theorem_4_3_lazy`)**: standalone EU-CMA
security of pure-mode hedged SLH-DSA with the lazy cached PRF reduction `B_sl_prfLazyAdv`
(replacing eager `tableM`-based `B_sl_prfAdv`) and all 11 remaining summands identical to
`Slhdsa.theorem_4_3`. -/
theorem theorem_4_3_lazy
    (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    {qs : ℕ} (A : Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs) :
    Notions.euCmaSucc ProbCompRuntime.probComp A ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfLazyAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr)) (B_sl_prfmsgAdv pr Msg enc A) +
      Notions.itsrSucc (slHmsg pr) (slMap vp)
        (B_itsr pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (B_ud pr (SfStage1.unit pr) (wotsStage2 pr (slPostPrfAdv pr Msg enc A)) γ) +
      SM_DT_PRE_Advantage (B_pre pr (SfStage1.unit pr) (wotsStage2 pr (slPostPrfAdv pr Msg enc A))) +
      SM_DT_TCR_Advantage (B_tcrF_wots pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrH_xmss pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrThK pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrThLsl pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (B_tcrH_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      3 * SM_DT_TCR_Advantage (B_tcrF_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) +
      SM_DT_DSPR_Advantage (B_dsprF_fors pr (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A)) := by
  rw [euCmaSucc_eq_slGame0 pr Msg enc A]
  have h1 := hop1_prf_lazy pr Msg enc A
  have h2 := hop2_prfmsg pr Msg enc A
  have h3 := (pr_slGame2_le_postPrf pr Msg enc henc A).trans
    (postPrf_bound pr hinj (SfStage1.unit pr) (slPostPrfAdv pr Msg enc A))
  calc Pr{let b ← slGame0 pr Msg enc A}[b = true]
      ≤ Pr{let b ← slGame1 pr Msg enc A}[b = true] +
          Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfLazyAdv pr Msg enc A) := h1
    _ ≤ (Pr{let b ← slGame2 pr Msg enc A}[b = true] +
          Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr)) (B_sl_prfmsgAdv pr Msg enc A)) +
          Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (B_sl_prfLazyAdv pr Msg enc A) :=
        add_le_add h2 le_rfl
    _ ≤ _ := by
        have hstep := add_le_add (add_le_add h3
          (le_refl (Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgSlF pr))
            (B_sl_prfmsgAdv pr Msg enc A))))
          (le_refl (Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr))
            (B_sl_prfLazyAdv pr Msg enc A)))
        refine hstep.trans (le_of_eq ?_)
        ring

end LazySlPrf

end ShrincsSecurity.Complexity

end
