module

public import ShrincsSecurity.Repro.Defs
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.EvalDist.EvalDistEq
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Lazy sampling of the reprogramming experiments

`SHRINCS-Security-Analysis.pdf`, Appendix C, proof of **Lemma C.4** (first paragraph): "We sample
the oracle lazily: the value at a point is sampled uniformly from `Y` when the point is queried for
the first time, and recorded. In `Repro_1` a call `Reprogram(x₂)` that returns `x₁` discards the
value recorded at `(x₁, x₂)`, if there is one, so that the next query at this point is answered
with a fresh uniform value. This is the distribution of Definition C.1."

This file proves that last sentence. The lazy experiments keep a partial table and a flag `bad`,
raised by a call whose point `(x₁, x₂)` already carries a recorded value (the event `Bad_j` of the
paper: a value is recorded only at a queried point). For both `Repro_b` (Definition C.1) and
`DI-Repro_b` (Definition C.2) the lazy experiment has the output distribution of the eager one
(`experiment_evalDistEq_lazy`, `diExperiment_evalDistEq_lazy`).

The induction vehicle is `run'_evalDistEq_of_step`: a randomized map `κ` from lazy to eager states
that commutes with every step makes the two simulations equal in distribution. Here `κ` completes
the partial table with a fresh uniform full table (`fillTable`), and commutation with a fresh
query or a reprogramming is VCVio's uniform-cell resampling `evalDist_bind_bind_update`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace ShrincsSecurity.Repro

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σL σE α : Type}

/-- **Simulation through a randomized state map.** If drawing an eager state from `κ sL` and taking
one eager step is equal in distribution to taking one lazy step and then drawing the eager state
from `κ`, for every query and lazy state, then the eager simulation started from `κ sL` and the
lazy simulation started from `sL` have equal output distributions. -/
theorem run'_evalDistEq_of_step
    (implL : QueryImpl spec (StateT σL ProbComp)) (implE : QueryImpl spec (StateT σE ProbComp))
    (κ : σL → ProbComp σE)
    (hstep : ∀ t sL, (κ sL >>= fun sE => (implE t).run sE) =ᵈ
      ((implL t).run sL >>= fun z => (z.1, ·) <$> κ z.2))
    (oa : OracleComp spec α) (sL : σL) :
    (κ sL >>= fun sE => (simulateQ implE oa).run' sE) =ᵈ (simulateQ implL oa).run' sL := by
  induction oa using OracleComp.inductionOn generalizing sL with
  | pure a => simpa using EvalDistEq.bind_const (κ sL) (pure a)
  | query_bind t k ih =>
    have e : ∀ (σ : Type) (impl : QueryImpl spec (StateT σ ProbComp)) (s : σ),
        (simulateQ impl (liftM (spec.query t) >>= k)).run' s =
          (impl t).run s >>= fun z => (simulateQ impl (k z.1)).run' z.2 := by
      intro σ impl s
      simp [StateT.run'_eq]
    simp only [e]
    calc (κ sL >>= fun sE => (implE t).run sE >>= fun z => (simulateQ implE (k z.1)).run' z.2)
        = ((κ sL >>= fun sE => (implE t).run sE) >>= fun z =>
            (simulateQ implE (k z.1)).run' z.2) := by rw [bind_assoc]
      _ =ᵈ (((implL t).run sL >>= fun z => (z.1, ·) <$> κ z.2) >>= fun z =>
            (simulateQ implE (k z.1)).run' z.2) := EvalDistEq.bind_left (hstep t sL) _
      _ = ((implL t).run sL >>= fun z => κ z.2 >>= fun sE =>
            (simulateQ implE (k z.1)).run' sE) := by simp [bind_assoc, bind_map_left]
      _ =ᵈ ((implL t).run sL >>= fun z => (simulateQ implL (k z.1)).run' z.2) :=
          EvalDistEq.bind_right _ fun z => ih z.1 z.2

/-- A uniform pair is a uniform first component followed by an independent uniform second. -/
theorem uniformSample_prod_eq (A B : Type) [SampleableType A] [SampleableType B] :
    ($ᵗ (A × B) : ProbComp (A × B)) =
      (do let a ← ($ᵗ A); let b ← ($ᵗ B); pure (a, b)) := by
  change (·, ·) <$> ($ᵗ A) <*> ($ᵗ B) = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp]

variable {D R : Type} [Fintype D] [DecidableEq D] [SampleableType R]

/-- **Uniform-cell resampling.** Overwriting one cell of a uniform table with an independent
uniform value leaves the table uniform. -/
theorem resample (x : D) {β : Type} (f : (D → R) → ProbComp β) :
    (do let u ← ($ᵗ R); let g ← ($ᵗ (D → R)); f (Function.update g x u)) =ᵈ
      ($ᵗ (D → R) >>= f) := by
  let _ : MeasurableSpace β := ⊤
  let _ : MeasurableSpace R := ⊤
  exact EvalDistEq.of_evalDist_eq (evalDist_bind_bind_update _ _
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample x f)

end Generic

variable (X₁ X₂ Y : Type)

/-- The state of the lazy experiments: the recorded values, the submitted second inputs (used by
`DI-Repro` only), the flag `bad`, and the instrumentation of Lemma C.4 and Corollary C.2: the log of
queries to `O_b` and a counter (`Σ_j n_j`, resp. `q_pre`). -/
structure LazyState where
  /-- The recorded values of the lazily sampled oracle. -/
  table : X₁ × X₂ → Option Y
  /-- The list `L` of submitted second inputs (`DI-Repro`). -/
  submitted : Finset X₂
  /-- Some call has hit a point with a recorded value. -/
  bad : Bool
  /-- The queries to `O_b` so far, latest first. -/
  log : List (X₁ × X₂)
  /-- The counter: `Σ_j n_j` in `Repro`, `q_pre` in `DI-Repro`. -/
  count : ℕ

variable {X₁ X₂ Y}

/-- The initial lazy state: nothing recorded, nothing submitted, not bad. -/
def LazyState.init : LazyState X₁ X₂ Y := ⟨fun _ => none, ∅, false, [], 0⟩

/-- Complete a partial table with a full table. -/
def fill (t : X₁ × X₂ → Option Y) (ys : X₁ × X₂ → Y) : X₁ × X₂ → Y :=
  fun p => (t p).getD (ys p)

/-- Completing the empty partial table returns the full table. -/
@[simp] theorem fill_none (ys : X₁ × X₂ → Y) : fill (fun _ => none) ys = ys := rfl

variable [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y]

/-- The lazily sampled oracle: answer a recorded value, or record a fresh uniform one; log the
query. -/
def lazyHash (x : X₁ × X₂) : StateT (LazyState X₁ X₂ Y) ProbComp Y := fun s =>
  match s.table x with
  | some y => pure (y, { s with log := x :: s.log })
  | none => (fun y => (y, { s with
      table := Function.update s.table x (some y)
      log := x :: s.log })) <$> ($ᵗ Y)

/-- Lazy `Reprogram(x₂)`: sample `(x₁, y)`, raise `bad` if `(x₁, x₂)` carries a recorded value, and
in game `1` discard that value; add `n_j` to the counter. -/
def lazyRepro (b : Bool) (x₂ : X₂) : StateT (LazyState X₁ X₂ Y) ProbComp X₁ := fun s =>
  (fun z : X₁ × Y => (z.1, { s with
    table := if b then Function.update s.table (z.1, x₂) none else s.table
    bad := s.bad || (s.table (z.1, x₂)).isSome
    count := s.count + seedCount s.log x₂ })) <$> ($ᵗ (X₁ × Y))

/-- Lazy guarded `Reprogram(x₂)` of `DI-Repro`; a fresh call adds its share of `q_pre`. -/
def lazyDIRepro (b : Bool) (x₂ : X₂) : StateT (LazyState X₁ X₂ Y) ProbComp (Option X₁) :=
  fun s =>
  if x₂ ∈ s.submitted then pure (none, s) else
  (fun z : X₁ × Y => (some z.1, { s with
    table := if b then Function.update s.table (z.1, x₂) none else s.table
    submitted := insert x₂ s.submitted
    bad := s.bad || (s.table (z.1, x₂)).isSome
    count := s.count + preCount s.log x₂ })) <$> ($ᵗ (X₁ × Y))

/-- The lazy `Repro_b` handler. -/
def lazyImpl (b : Bool) : QueryImpl (AdvSpec X₁ X₂ Y) (StateT (LazyState X₁ X₂ Y) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (LazyState X₁ X₂ Y) ProbComp) +
    ((fun x => lazyHash x : QueryImpl (HashSpec X₁ X₂ Y) (StateT (LazyState X₁ X₂ Y) ProbComp)) +
      (fun x₂ => lazyRepro b x₂ :
        QueryImpl (ReproSpec X₁ X₂) (StateT (LazyState X₁ X₂ Y) ProbComp)))

/-- The lazy `DI-Repro_b` handler. -/
def lazyDIImpl (b : Bool) :
    QueryImpl (DIAdvSpec X₁ X₂ Y) (StateT (LazyState X₁ X₂ Y) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (LazyState X₁ X₂ Y) ProbComp) +
    ((fun x => lazyHash x : QueryImpl (HashSpec X₁ X₂ Y) (StateT (LazyState X₁ X₂ Y) ProbComp)) +
      (fun x₂ => lazyDIRepro b x₂ :
        QueryImpl (DIReproSpec X₁ X₂) (StateT (LazyState X₁ X₂ Y) ProbComp)))

variable [Fintype X₁] [Fintype X₂]

/-- Complete the recorded values of a lazy state with a uniform full table. -/
noncomputable def fillTable (s : LazyState X₁ X₂ Y) : ProbComp (X₁ × X₂ → Y) :=
  (fun ys => fill s.table ys) <$> ($ᵗ (X₁ × X₂ → Y))

/-- `fillTable` together with the submitted list, the state of `DI-Repro`. -/
noncomputable def fillDI (s : LazyState X₁ X₂ Y) : ProbComp ((X₁ × X₂ → Y) × Finset X₂) :=
  (fun ys => (fill s.table ys, s.submitted)) <$> ($ᵗ (X₁ × X₂ → Y))

omit [Fintype X₁] [Fintype X₂] in
/-- Unfolding of `lazyRepro`. -/
theorem lazyRepro_run (b : Bool) (x₂ : X₂) (s : LazyState X₁ X₂ Y) :
    (lazyRepro b x₂).run s = (fun z : X₁ × Y => (z.1, { s with
      table := if b then Function.update s.table (z.1, x₂) none else s.table
      bad := s.bad || (s.table (z.1, x₂)).isSome
      count := s.count + seedCount s.log x₂ })) <$> ($ᵗ (X₁ × Y)) := rfl

omit [Fintype X₁] [Fintype X₂] in
/-- Unfolding of `lazyDIRepro`. -/
theorem lazyDIRepro_run (b : Bool) (x₂ : X₂) (s : LazyState X₁ X₂ Y) :
    (lazyDIRepro b x₂).run s = if x₂ ∈ s.submitted then pure (none, s) else
      (fun z : X₁ × Y => (some z.1, { s with
        table := if b then Function.update s.table (z.1, x₂) none else s.table
        submitted := insert x₂ s.submitted
        bad := s.bad || (s.table (z.1, x₂)).isSome
        count := s.count + preCount s.log x₂ })) <$> ($ᵗ (X₁ × Y)) := rfl

section Steps

variable {β : Type}

omit [SampleableType X₁] in
/-- A fresh or recorded hash answer commutes with completing the table. The continuation `F` may
read the answer, the completed table, and the untabled part of the state (submitted list, log,
counter). -/
theorem hash_comm (x : X₁ × X₂) (s : LazyState X₁ X₂ Y)
    (F : Y → (X₁ × X₂ → Y) → Finset X₂ × List (X₁ × X₂) × ℕ → β) :
    (do let ys ← ($ᵗ (X₁ × X₂ → Y));
        pure (F (fill s.table ys x) (fill s.table ys) (s.submitted, x :: s.log, s.count))) =ᵈ
      ((lazyHash x).run s >>= fun z => do
        let ys ← ($ᵗ (X₁ × X₂ → Y));
        pure (F z.1 (fill z.2.table ys) (z.2.submitted, z.2.log, z.2.count))) := by
  change _ =ᵈ (lazyHash x s >>= _)
  unfold lazyHash
  rcases hx : s.table x with _ | v
  · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine EvalDistEq.trans (EvalDistEq.symm (resample x _)) ?_
    refine EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun g => ?_
    have h1 : fill s.table (Function.update g x u) x = u := by simp [fill, hx]
    have h2 : fill s.table (Function.update g x u) =
        fill (Function.update s.table x (some u)) g := by
      funext p
      by_cases hp : p = x
      · subst hp; simp [fill, hx]
      · simp [fill, hp]
    rw [h1, h2]
  · simp only [pure_bind]
    have h1 : ∀ ys, fill s.table ys x = v := fun ys => by simp [fill, hx]
    simp only [h1]
    rfl

/-- A reprogramming call commutes with completing the table: overwriting the completed table at
`(x₁, x₂)` with a fresh `y` is completing the table after discarding the recorded value. -/
theorem repro_comm (b : Bool) (x₂ : X₂) (t : X₁ × X₂ → Option Y)
    (F : X₁ → (X₁ × X₂ → Y) → β) :
    (do let ys ← ($ᵗ (X₁ × X₂ → Y)); let z ← ($ᵗ (X₁ × Y));
        pure (F z.1 (if b then Function.update (fill t ys) (z.1, x₂) z.2 else fill t ys))) =ᵈ
      (do let z ← ($ᵗ (X₁ × Y)); let ys ← ($ᵗ (X₁ × X₂ → Y));
          pure (F z.1 (fill (if b then Function.update t (z.1, x₂) none else t) ys))) := by
  refine EvalDistEq.trans (EvalDistEq.bind_bind_swap _ _ _) ?_
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rfl
  · simp only [ite_true, uniformSample_prod_eq, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun a => ?_
    refine EvalDistEq.trans ?_ (EvalDistEq.symm (EvalDistEq.bind_const ($ᵗ Y) _))
    have h : ∀ u ys, Function.update (fill t ys) (a, x₂) u =
        fill (Function.update t (a, x₂) none) (Function.update ys (a, x₂) u) := by
      intro u ys
      funext p
      by_cases hp : p = (a, x₂)
      · subst hp; simp [fill]
      · simp [fill, hp]
    simp only [h]
    exact resample (a, x₂) fun ys => pure (F a (fill (Function.update t (a, x₂) none) ys))

/-- Every step of the lazy `Repro_b` handler commutes with completing the table. -/
theorem lazyImpl_step (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) :
    (fillTable s >>= fun O => (gameImpl b t).run O) =ᵈ
      ((lazyImpl b t).run s >>= fun z => (z.1, ·) <$> fillTable z.2) := by
  rcases t with n | x | x₂
  · simp only [gameImpl, lazyImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply_run,
      fillTable, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    exact EvalDistEq.bind_bind_swap _ _ _
  · have e : (fillTable s >>= fun O => (gameImpl b (.inr (.inl x))).run O) =
        (($ᵗ (X₁ × X₂ → Y)) >>= fun ys =>
          pure ((fun y O (_ : Finset X₂ × List (X₁ × X₂) × ℕ) => (y, O)) (fill s.table ys x)
            (fill s.table ys) (s.submitted, x :: s.log, s.count))) := by
      simp [gameImpl, fillTable, hashImpl, map_eq_bind_pure_comp]
    rw [e]
    refine EvalDistEq.trans (hash_comm x s (fun y O _ => (y, O))) ?_
    simp [lazyImpl, fillTable, map_eq_bind_pure_comp]
  · have e : (fillTable s >>= fun O => (gameImpl b (.inr (.inr x₂))).run O) =
        (($ᵗ (X₁ × X₂ → Y)) >>= fun ys => ($ᵗ (X₁ × Y)) >>= fun z =>
          pure (Prod.mk z.1
            (if b then Function.update (fill s.table ys) (z.1, x₂) z.2 else fill s.table ys))) := by
      cases b <;> simp [gameImpl, fillTable, reproImpl, map_eq_bind_pure_comp]
    rw [e]
    refine EvalDistEq.trans (repro_comm b x₂ s.table Prod.mk) ?_
    simp [lazyImpl, lazyRepro_run, fillTable, map_eq_bind_pure_comp]

/-- Every step of the lazy `DI-Repro_b` handler commutes with completing the table. -/
theorem lazyDIImpl_step (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) :
    (fillDI s >>= fun O => (diGameImpl b t).run O) =ᵈ
      ((lazyDIImpl b t).run s >>= fun z => (z.1, ·) <$> fillDI z.2) := by
  rcases t with n | x | x₂
  · simp only [diGameImpl, lazyDIImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply_run,
      fillDI, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    exact EvalDistEq.bind_bind_swap _ _ _
  · have e : (fillDI s >>= fun O => (diGameImpl b (.inr (.inl x))).run O) =
        (($ᵗ (X₁ × X₂ → Y)) >>= fun ys =>
          pure ((fun y O (a : Finset X₂ × List (X₁ × X₂) × ℕ) => (y, (O, a.1)))
            (fill s.table ys x) (fill s.table ys) (s.submitted, x :: s.log, s.count))) := by
      simp [diGameImpl, fillDI, hashImpl, map_eq_bind_pure_comp]
    rw [e]
    refine EvalDistEq.trans (hash_comm x s (fun y O a => (y, (O, a.1)))) ?_
    simp [lazyDIImpl, fillDI, map_eq_bind_pure_comp]
  · by_cases hx : x₂ ∈ s.submitted
    · simp [diGameImpl, lazyDIImpl, lazyDIRepro_run, diReproImpl, fillDI, hx,
        map_eq_bind_pure_comp]
    · have e : (fillDI s >>= fun O => (diGameImpl b (.inr (.inr x₂))).run O) =
          (($ᵗ (X₁ × X₂ → Y)) >>= fun ys => ($ᵗ (X₁ × Y)) >>= fun z =>
            pure ((fun x₁ O => (some x₁, (O, insert x₂ s.submitted))) z.1
              (if b then Function.update (fill s.table ys) (z.1, x₂) z.2
                else fill s.table ys))) := by
        cases b <;> simp [diGameImpl, fillDI, diReproImpl, hx, map_eq_bind_pure_comp]
      rw [e]
      refine EvalDistEq.trans
        (repro_comm b x₂ s.table (fun x₁ O => (some x₁, (O, insert x₂ s.submitted)))) ?_
      simp [lazyDIImpl, lazyDIRepro_run, hx, fillDI, map_eq_bind_pure_comp]

end Steps

/-- **Lazy sampling of `Repro_b`** (proof of Lemma C.4, first paragraph): the experiment of
Definition C.1 has the output distribution of the lazy experiment, in which `Repro_1` discards the
recorded value at the reprogrammed point. -/
theorem experiment_evalDistEq_lazy (b : Bool) (A : OracleComp (AdvSpec X₁ X₂ Y) Bool) :
    experiment b A =ᵈ (simulateQ (lazyImpl b) A).run' LazyState.init := by
  have e : experiment b A = fillTable LazyState.init >>= fun O =>
      (simulateQ (gameImpl b) A).run' O := by
    simp [experiment, fillTable, fill_none, LazyState.init]
  rw [e]
  exact run'_evalDistEq_of_step _ _ _ (lazyImpl_step b) A _

/-- **Lazy sampling of `DI-Repro_b`**: the experiment of Definition C.2 has the output
distribution of the lazy experiment. -/
theorem diExperiment_evalDistEq_lazy (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) :
    diExperiment b A =ᵈ (simulateQ (lazyDIImpl b) A).run' LazyState.init := by
  have e : diExperiment b A = fillDI LazyState.init >>= fun O =>
      (simulateQ (diGameImpl b) A).run' O := by
    simp [diExperiment, fillDI, fill_none, LazyState.init]
  rw [e]
  exact run'_evalDistEq_of_step _ _ _ (lazyDIImpl_step b) A _

end ShrincsSecurity.Repro

end
