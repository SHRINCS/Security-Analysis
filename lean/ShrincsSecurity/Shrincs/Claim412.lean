module

public import ShrincsSecurity.Shrincs.Natural

/-!
# Claim 4.12: `GAME.1 → GAME.2`, uniform randomizers on both paths

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.12** (txt lines 3963–3985): "Both
derivations are calls of the combined randomizer function `PRF_msg` under the single key `SK.prf`,
so we replace it once, for both paths together: a standard reduction `B₂` replaces every `PRF_msg`
call, on either path, by a query to a PRF-or-random oracle and simulates the rest of the
experiment honestly, using the uniform secret elements of `GAME.1`, which it samples itself."

The reduction is `Bprfmsg` (`Games.lean`); its real world is `GAME.1` and its ideal world is
`GAME.2` (the lazily sampled random function of the `PRF_msg` input, footnote 11: a repeated
input receives the cached randomizer).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys SkIdx skOf pkSfOf)

/-! ## Proof of Claim 4.12

Both worlds of the PRF experiment against `B_prfmsg` are games by interpretation. The
interpretation `simulateQ'` of the oracle of `B_prfmsg` is a monad morphism; lifted through the
secret cache (`MonadHom.stateT`) it commutes with the keyed part of the games (`body`, by the
naturality theorems of `Natural.lean`), maps the lazily sampled secrets `lazyRO` to `lazyRO`, and
maps the `PRF_msg` query to the real function `PRF_msg(k, ·)` (real world, `real_eq`) or to the
lazily sampled random function (ideal world, `ideal_map`; VCVio's `randomOracle` is `lazyRO`,
`randomOracle_eq_lazyRO`). The real world draws `k` before the structure phase, `GAME.1` after
`PK.seed`; the draws commute in distribution (`real_evalDistEq`). The ideal world is `GAME.2`
exactly (`ideal_eq`). -/

namespace Claim412

section Hom

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]

omit [LawfulMonad m] [LawfulMonad n] in
/-- A morphism lifted through a state commutes with `StateT.lift`. -/
theorem stateT_lift (σ : Type) (Φ : m →ᵐ n) {α : Type} (q : m α) :
    MonadHom.stateT σ Φ (StateT.lift q) = StateT.lift (Φ q) := by
  ext s
  rw [MonadHom.stateT_run, StateT.run_lift, StateT.run_lift, MonadHom.mmap_bind]
  simp only [MonadHom.mmap_pure]

/-- A morphism that preserves the lift of `ProbComp`, lifted through the cache, maps a lazily
sampled function to the lazily sampled function. -/
theorem stateT_lazyRO [MonadLiftT ProbComp m] [MonadLiftT ProbComp n] {D R : Type}
    [DecidableEq D] [SampleableType R] (Φ : m →ᵐ n) (hΦ : LiftPres Φ) (x : D) :
    MonadHom.stateT _ Φ (lazyRO (m := m) (R := R) x) = lazyRO x := by
  ext c
  rw [MonadHom.stateT_run]
  unfold lazyRO
  rw [StateT.run_mk, StateT.run_mk]
  cases c x
  · rw [MonadHom.mmap_map, hΦ]
  · rw [MonadHom.mmap_pure]

/-- A morphism commutes with running a state from a given initial value. -/
theorem mmap_run' {σ α : Type} (Φ : m →ᵐ n) (x : StateT σ m α) (s : σ) :
    Φ (x.run' s) = (MonadHom.stateT σ Φ x).run' s := by
  rw [StateT.run'_eq, StateT.run'_eq, MonadHom.mmap_map, MonadHom.stateT_run]

end Hom

/-- Running a state over `ProbComp` from `s` after a lifted sample. -/
theorem run'_liftM_bind {σ α β : Type} (p : ProbComp α) (g : α → StateT σ ProbComp β) (s : σ) :
    ((liftM p : StateT σ ProbComp α) >>= g).run' s = p >>= fun a => (g a).run' s := by
  simp [StateT.run'_eq]

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

/-- The keyed part of `GAME.1`, `GAME.2` and `B_prfmsg`: the stateless root over the secret
source `sec`, then the signing phase with the randomizer source `rnd`. -/
def body (m : Type → Type) [Monad m] [MonadLiftT ProbComp (StateT (SecCache pr) m)] {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (z : (Structure × A.State) × (Fxmss.Rom.roSpec pr (BMsg pr Msg)).QueryCache)
    (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y)
    (sec : pr.PkSeed × SecAdrs → StateT (SecCache pr) m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → StateT (SecCache pr) m pr.Y) :
    StateT (SecCache pr) m Bool := do
  let pkSl ← slRootM pr sec pk
  let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
  (phase2C pr Msg enc A z.1.2 K sec rnd sk).run' (CSt.init pr Msg z.2)

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The keyed part is natural: a morphism lifted through the secret cache maps it to the keyed
part over the mapped sources. The lifts of `ProbComp` into the stateful monads are those found by
instance search (for `OracleComp` they go through the `StateT` sub-spec lift). -/
theorem map_body {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT ProbComp (StateT (SecCache pr) m)]
    [MonadLiftT ProbComp (StateT (SecCache pr) n)] (Φ : m →ᵐ n)
    (hΦ : LiftPres (MonadHom.stateT (SecCache pr) Φ)) {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (z : (Structure × A.State) × (Fxmss.Rom.roSpec pr (BMsg pr Msg)).QueryCache)
    (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y)
    (sec : pr.PkSeed × SecAdrs → StateT (SecCache pr) m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → StateT (SecCache pr) m pr.Y)
    (sec' : pr.PkSeed × SecAdrs → StateT (SecCache pr) n pr.Y)
    (rnd' : PrfMsgInput pr.PkSeed pr.Y → StateT (SecCache pr) n pr.Y)
    (hsec : ∀ x, MonadHom.stateT (SecCache pr) Φ (sec x) = sec' x)
    (hrnd : ∀ x, MonadHom.stateT (SecCache pr) Φ (rnd x) = rnd' x) :
    MonadHom.stateT (SecCache pr) Φ (body pr Msg enc m A z pk sk sec rnd) =
      body pr Msg enc n A z pk sk sec' rnd' := by
  have hsec' : (fun x => MonadHom.stateT (SecCache pr) Φ (sec x)) = sec' := funext hsec
  have hrnd' : (fun x => MonadHom.stateT (SecCache pr) Φ (rnd x)) = rnd' := funext hrnd
  unfold body
  rw [MonadHom.mmap_bind, slRootM_natural, hsec']
  congr 1
  funext pkSl
  rw [StateT.run'_eq, StateT.run'_eq, MonadHom.mmap_map,
    phase2C_natural pr Msg enc _ hΦ, hsec', hrnd']

/-! ### The real world is `GAME.1` -/

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The real `PRF_msg` oracle preserves the lift of `ProbComp`. -/
theorem liftPres_real (k : pr.SkPrf) :
    LiftPres (simulateQ' ((Notions.KeyedHash.toPRF (prfMsgF pr)).prfRealQueryImpl k)) := by
  intro α p
  rw [simulateQ'_apply, ← liftComp_eq_liftM, PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The real `PRF_msg` oracle, lifted through the secret cache, preserves the lift of `ProbComp`
(into `StateT (SecCache pr) (OracleComp _)` it is the `StateT` sub-spec lift). -/
theorem liftPres_real_stateT (k : pr.SkPrf) :
    LiftPres (m := StateT (SecCache pr) (OracleComp (PrfMsgSpec pr)))
      (n := StateT (SecCache pr) ProbComp) (MonadHom.stateT (SecCache pr)
        (simulateQ' ((Notions.KeyedHash.toPRF (prfMsgF pr)).prfRealQueryImpl k))) := by
  intro α p
  ext s
  rw [MonadHom.stateT_run, simulateQ'_apply]
  show simulateQ _ (liftComp ((StateT.lift p : StateT _ ProbComp α).run s) (PrfMsgSpec pr)) =
    (StateT.lift p : StateT _ ProbComp α).run s
  rw [PRFScheme.simulateQ_prfRealQueryImpl_liftComp]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The real world of `B_prfmsg` is `GAME.1` with the key `SK.prf` drawn first. -/
theorem real_eq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    (Notions.KeyedHash.toPRF (prfMsgF pr)).prfRealExperiment (Bprfmsg pr Msg enc A) =
      (do
        let k ← $ᵗ pr.SkPrf
        let z ← stage1S pr Msg enc A
        if ¬ z.1.1.Valid vp.params.hsf then return false else do
        let pk ← $ᵗ pr.PkSeed
        let f ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
        (body pr Msg enc ProbComp A z pk (skOf pr z.1.1 f) lazyRO
          (fun x => pure (pr.PRFmsg k x))).run' ∅ : ProbComp Bool) := by
  unfold PRFScheme.prfRealExperiment
  refine congrArg (fun g => (_ : ProbComp _) >>= g) (funext fun k => ?_)
  have hL : LiftPres (simulateQ' ((Notions.KeyedHash.toPRF (prfMsgF pr)).prfRealQueryImpl k)) :=
    liftPres_real pr k
  rw [← simulateQ'_apply]
  unfold Bprfmsg
  rw [MonadHom.mmap_bind, hL]
  refine congrArg (fun g => (stage1S pr Msg enc A : ProbComp _) >>= g) (funext fun z => ?_)
  rw [MonadHom.mmap_ite, MonadHom.mmap_pure]
  refine congrArg (ite _ _) ?_
  rw [MonadHom.mmap_bind, hL]
  refine congrArg (fun g => ($ᵗ pr.PkSeed : ProbComp _) >>= g) (funext fun pk => ?_)
  rw [MonadHom.mmap_bind, hL]
  refine congrArg (fun g => ($ᵗ (SkIdx vp.params z.1.1 → pr.Y) : ProbComp _) >>= g)
    (funext fun f => ?_)
  rw [mmap_run']
  refine congrArg (StateT.run' · ∅) ?_
  refine map_body pr Msg enc _ (liftPres_real_stateT pr k) A z pk (skOf pr z.1.1 f) _ _ _ _
    (fun x => stateT_lazyRO _ hL x) (fun x => ?_)
  show MonadHom.stateT _ _ (StateT.lift (PRFScheme.functionQuery x)) = _
  rw [stateT_lift, simulateQ'_apply, PRFScheme.simulateQ_prfRealQueryImpl_functionQuery]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The real world of `B_prfmsg` is distributed as `GAME.1`: the key draw commutes with the
structure phase and with `PK.seed`, and is unused when the structure is invalid. -/
theorem real_evalDistEq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    (Notions.KeyedHash.toPRF (prfMsgF pr)).prfRealExperiment (Bprfmsg pr Msg enc A) =ᵈ
      game1 pr Msg enc A := by
  rw [real_eq]
  refine (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun z => ?_)
  show _ =ᵈ (if ¬ z.1.1.Valid vp.params.hsf then pure false else do
        let pk ← $ᵗ pr.PkSeed
        let k ← $ᵗ pr.SkPrf
        let f ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
        (body pr Msg enc ProbComp A z pk (skOf pr z.1.1 f) lazyRO
          (fun x => pure (pr.PRFmsg k x))).run' ∅ : ProbComp Bool)
  by_cases hc : z.1.1.Valid vp.params.hsf
  · simp only [hc, not_true_eq_false, ↓reduceIte]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [hc, not_false_eq_true, ↓reduceIte]
    exact EvalDistEq.bind_const _ _

/-! ### The ideal world is `GAME.2` -/

omit [Fintype pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The ideal (random-oracle) `PRF_msg` oracle preserves the lift of `ProbComp`. -/
theorem liftPres_ideal :
    LiftPres (simulateQ' (PRFScheme.prfIdealQueryImpl (D := PrfMsgInput pr.PkSeed pr.Y)
      (R := pr.Y))) := by
  intro α p
  rw [simulateQ'_apply, ← liftComp_eq_liftM, PRFScheme.simulateQ_prfIdealQueryImpl_liftComp]

omit [Fintype pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The ideal `PRF_msg` oracle, lifted through the secret cache, preserves the lift of
`ProbComp` into the monad `M2` of `GAME.2`. -/
theorem liftPres_ideal_stateT :
    LiftPres (m := StateT (SecCache pr) (OracleComp (PrfMsgSpec pr))) (n := M2 pr)
      (MonadHom.stateT (SecCache pr) (simulateQ' (PRFScheme.prfIdealQueryImpl
        (D := PrfMsgInput pr.PkSeed pr.Y) (R := pr.Y)))) := by
  intro α p
  refine StateT.ext fun s => ?_
  rw [MonadHom.stateT_run, simulateQ'_apply]
  show simulateQ _ (liftComp ((StateT.lift p : StateT _ ProbComp α).run s) (PrfMsgSpec pr)) =
    (liftM p : M2 pr α).run s
  rw [PRFScheme.simulateQ_prfIdealQueryImpl_liftComp]
  simp

omit [Fintype pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- VCVio's lazy random oracle is the lazily sampled function `lazyRO` of `Games.lean`. -/
theorem randomOracle_eq_lazyRO (x : PrfMsgInput pr.PkSeed pr.Y) :
    (PrfMsgInput pr.PkSeed pr.Y →ₒ pr.Y).randomOracle x =
      (lazyRO x : StateT (RndCache pr) ProbComp pr.Y) := by
  ext c
  rw [randomOracle.run_eq]
  unfold lazyRO
  rw [StateT.run_mk]
  cases c x
  · simp [map_eq_bind_pure_comp]
  · rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The ideal world of `B_prfmsg` before running the randomizer cache. -/
theorem ideal_map {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    simulateQ' (PRFScheme.prfIdealQueryImpl (D := PrfMsgInput pr.PkSeed pr.Y) (R := pr.Y))
        (Bprfmsg pr Msg enc A) =
      (do
        let z ← (liftM (stage1S pr Msg enc A) : StateT (RndCache pr) ProbComp _)
        if ¬ z.1.1.Valid vp.params.hsf then return false else do
        let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp _) : StateT (RndCache pr) ProbComp _)
        let f ← (liftM ($ᵗ (SkIdx vp.params z.1.1 → pr.Y) : ProbComp _) :
          StateT (RndCache pr) ProbComp _)
        (body pr Msg enc (StateT (RndCache pr) ProbComp) A z pk (skOf pr z.1.1 f) lazyRO
          (fun x => liftM (lazyRO x : StateT (RndCache pr) ProbComp pr.Y))).run' ∅ :
        StateT (RndCache pr) ProbComp Bool) := by
  have hL : LiftPres (simulateQ' (PRFScheme.prfIdealQueryImpl
      (D := PrfMsgInput pr.PkSeed pr.Y) (R := pr.Y))) := liftPres_ideal pr
  unfold Bprfmsg
  rw [MonadHom.mmap_bind, hL]
  refine congrArg
    (fun g => (liftM (stage1S pr Msg enc A) : StateT (RndCache pr) ProbComp _) >>= g)
    (funext fun z => ?_)
  rw [MonadHom.mmap_ite, MonadHom.mmap_pure]
  refine congrArg (ite _ _) ?_
  rw [MonadHom.mmap_bind, hL]
  refine congrArg
    (fun g => (liftM ($ᵗ pr.PkSeed : ProbComp _) : StateT (RndCache pr) ProbComp _) >>= g)
    (funext fun pk => ?_)
  rw [MonadHom.mmap_bind, hL]
  refine congrArg (fun g => (liftM ($ᵗ (SkIdx vp.params z.1.1 → pr.Y) : ProbComp _) :
    StateT (RndCache pr) ProbComp _) >>= g) (funext fun f => ?_)
  rw [mmap_run']
  refine congrArg (StateT.run' · ∅) ?_
  refine map_body pr Msg enc _ (liftPres_ideal_stateT pr) A z pk (skOf pr z.1.1 f) _ _ _ _
    (fun x => stateT_lazyRO _ hL x) (fun x => ?_)
  show MonadHom.stateT _ _ (StateT.lift (PRFScheme.functionQuery x)) = _
  rw [stateT_lift, simulateQ'_apply, PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery,
    randomOracle_eq_lazyRO]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The ideal world of `B_prfmsg` is `GAME.2`. -/
theorem ideal_eq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    PRFScheme.prfIdealExperiment (Bprfmsg pr Msg enc A) = game2 pr Msg enc A := by
  unfold PRFScheme.prfIdealExperiment
  rw [← simulateQ'_apply, ideal_map, run'_liftM_bind]
  refine congrArg (fun g => (stage1S pr Msg enc A : ProbComp _) >>= g) (funext fun z => ?_)
  by_cases hc : z.1.1.Valid vp.params.hsf
  · simp only [hc, not_true_eq_false, ↓reduceIte]
    rw [run'_liftM_bind]
    refine congrArg (fun g => ($ᵗ pr.PkSeed : ProbComp _) >>= g) (funext fun pk => ?_)
    rw [run'_liftM_bind]
    rfl
  · simp only [hc, not_false_eq_true, ↓reduceIte, StateT.run'_eq, StateT.run_pure, map_pure]

end Claim412

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

-- The statement keeps the shared instance context of the skeleton (used by `Theorem41.lean`);
-- `[Fintype pr.Y]` and `[DecidableEq pr.Digest]` are not needed by this proof.
set_option linter.unusedSectionVars false in
/-- **Claim 4.12** (`GAME.1 → GAME.2`): `Succ₁(A) ≤ Succ₂(A) + Adv^{prf}_{PRF_msg}(B_prfmsg)`. -/
theorem claim_4_12 {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let b ← game1 pr Msg enc A}[b = true] ≤
      Pr{let b ← game2 pr Msg enc A}[b = true] +
        (Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage (Bprfmsg pr Msg enc A) := by
  rw [← ((Claim412.real_evalDistEq pr Msg enc A).prEvent_eq _), ← Claim412.ideal_eq pr Msg enc A,
    prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, PRFScheme.prfAdvantage,
    MeasureTheory.Measure.boolDist]
  exact (ENNReal.absDiff_le_iff.1 le_rfl).1

end ShrincsSecurity.Shrincs

end
