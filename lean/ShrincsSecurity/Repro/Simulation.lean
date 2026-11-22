module

public import ShrincsSecurity.Repro.Bound

/-!
# Simulating `DI-Repro` inside `Repro`

`SHRINCS-Security-Analysis.pdf`, Appendix C, **Lemma C.5**: for every `DI-Repro` adversary `A` the
adversary `A'` that keeps the list `L` itself, answers a repeated call with `⊥` without calling its
own oracle, and forwards every other call and every query, has
`Pr[Repro_b(A') ⇒ 1] = Pr[DI-Repro_b(A) ⇒ 1]` for `b ∈ {0, 1}`, with the same query bound and at
most as many calls. As the paper notes, Lemma C.2 then holds for `DI-Repro` with the same
right-hand side (`diAdvantage_le_mul`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace ShrincsSecurity.Repro

variable {X₁ X₂ Y : Type} [DecidableEq X₂]

/-- The filter of Lemma C.5: keep `L`, refuse a repeated call locally, forward everything else. -/
def filterImpl :
    QueryImpl (DIAdvSpec X₁ X₂ Y) (StateT (Finset X₂) (OracleComp (AdvSpec X₁ X₂ Y)))
  | .inl n => fun L =>
      (fun u => (u, L)) <$> (liftM ((AdvSpec X₁ X₂ Y).query (.inl n)) :
        OracleComp (AdvSpec X₁ X₂ Y) (Fin (n + 1)))
  | .inr (.inl x) => fun L =>
      (fun y => (y, L)) <$> (liftM ((AdvSpec X₁ X₂ Y).query (.inr (.inl x))) :
        OracleComp (AdvSpec X₁ X₂ Y) Y)
  | .inr (.inr x₂) => fun L =>
      if x₂ ∈ L then pure (none, L) else
      (fun x₁ => (some x₁, insert x₂ L)) <$> (liftM ((AdvSpec X₁ X₂ Y).query (.inr (.inr x₂))) :
        OracleComp (AdvSpec X₁ X₂ Y) X₁)

/-- A coin query is forwarded. -/
theorem filterImpl_unif_run (n : ℕ) (L : Finset X₂) :
    (filterImpl (.inl n) : StateT _ (OracleComp (AdvSpec X₁ X₂ Y)) _).run L =
      (fun u => (u, L)) <$> (liftM ((AdvSpec X₁ X₂ Y).query (.inl n)) :
        OracleComp (AdvSpec X₁ X₂ Y) (Fin (n + 1))) := rfl

/-- A query to `O_b` is forwarded. -/
theorem filterImpl_hash_run (x : X₁ × X₂) (L : Finset X₂) :
    (filterImpl (.inr (.inl x)) : StateT _ (OracleComp (AdvSpec X₁ X₂ Y)) _).run L =
      (fun y => (y, L)) <$> (liftM ((AdvSpec X₁ X₂ Y).query (.inr (.inl x))) :
        OracleComp (AdvSpec X₁ X₂ Y) Y) := rfl

/-- A repeated call is refused locally; a fresh call is recorded and forwarded. -/
theorem filterImpl_repro_run (x₂ : X₂) (L : Finset X₂) :
    (filterImpl (.inr (.inr x₂)) : StateT _ (OracleComp (AdvSpec X₁ X₂ Y)) _).run L =
      if x₂ ∈ L then pure (none, L) else
      (fun x₁ => (some x₁, insert x₂ L)) <$> (liftM ((AdvSpec X₁ X₂ Y).query (.inr (.inr x₂))) :
        OracleComp (AdvSpec X₁ X₂ Y) X₁) := rfl

/-- The `Repro` adversary `A'` of Lemma C.5, as a computation. -/
def filterRun (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) : OracleComp (AdvSpec X₁ X₂ Y) Bool :=
  (simulateQ filterImpl A).run' ∅

/-- `A'` makes the queries of `A`. -/
theorem filterRun_hashBound {A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool} {q : ℕ}
    (h : A.IsQueryBoundP (IsHashQuery X₁ X₂) q) :
    (filterRun A).IsQueryBoundP (IsHashQuery X₁ X₂) q := by
  unfold filterRun
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step h (fun t L => ?_) ∅
  rcases t with n | x | x₂
  · simp [filterImpl, StateT.run, IsHashQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · simp [filterImpl, StateT.run, IsHashQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · by_cases hx : x₂ ∈ L <;>
      simp [filterImpl, StateT.run, hx, IsHashQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        isQueryBoundP_pure]

/-- `A'` makes at most the calls of `A`: the calls of `A` not answered by `⊥`. -/
theorem filterRun_reproBound {A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool} {R : ℕ}
    (h : A.IsQueryBoundP (IsReproQuery X₁ X₂) R) :
    (filterRun A).IsQueryBoundP (IsReproQuery X₁ X₂) R := by
  unfold filterRun
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step h (fun t L => ?_) ∅
  rcases t with n | x | x₂
  · simp [filterImpl, StateT.run, IsReproQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · simp [filterImpl, StateT.run, IsReproQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · by_cases hx : x₂ ∈ L <;>
      simp [filterImpl, StateT.run, hx, IsReproQuery, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        isQueryBoundP_pure]

/-- The adversary `A'` of Lemma C.5, with the bounds of `A`. -/
def DIAdversary.toAdversary {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) : Adversary X₁ X₂ Y q R where
  run := filterRun A.run
  hashBound := filterRun_hashBound A.hashBound
  reproBound := filterRun_reproBound A.reproBound

variable [DecidableEq X₁] [SampleableType X₁] [SampleableType Y]

/-- The simulation of Lemma C.5, step by step: running `A` through the filter inside `Repro_b` is
running `A` in `DI-Repro_b`, with the filter's list as the challenger's list. -/
theorem simulateQ_filter_run {α : Type} (b : Bool) (oa : OracleComp (DIAdvSpec X₁ X₂ Y) α)
    (p : (X₁ × X₂ → Y) × Finset X₂) :
    (fun z => (z.1.1, (z.2, z.1.2))) <$>
        (simulateQ (gameImpl b) ((simulateQ filterImpl oa).run p.2)).run p.1 =
      (simulateQ (diGameImpl b) oa).run p := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    simp only [← ih]
    obtain ⟨O, L⟩ := p
    rcases t with n | x | x₂
    · rw [filterImpl_unif_run]
      simp [gameImpl, diGameImpl]
    · rw [filterImpl_hash_run]
      simp [gameImpl, diGameImpl, hashImpl]
    · rw [filterImpl_repro_run]
      by_cases hx : x₂ ∈ L
      · simp [diGameImpl, diReproImpl, hx]
      · cases b <;> simp [gameImpl, diGameImpl, reproImpl, diReproImpl, hx]

variable [Fintype X₁] [Fintype X₂]

/-- **Lemma C.5.** `Pr[Repro_b(A') ⇒ 1] = Pr[DI-Repro_b(A) ⇒ 1]`, for `b ∈ {0, 1}`. -/
theorem experiment_filterRun (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) :
    experiment b (filterRun A) = diExperiment b A := by
  unfold experiment diExperiment filterRun
  congr 1
  funext O
  have h := congrArg (fun m => Prod.fst <$> m) (simulateQ_filter_run b A (O, ∅))
  simpa [StateT.run'_eq, simulateQ_map, Functor.map_map] using h

/-- **Lemma C.5**, advantage form: `A'` has the advantage of `A`. -/
theorem advantage_toAdversary {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) :
    advantage A.toAdversary = diAdvantage A := by
  simp [advantage, diAdvantage, DIAdversary.toAdversary, experiment_filterRun]

/-- **Lemma C.2 for `DI-Repro`** (consequence of Lemma C.5): `Adv^DI-Repro_{R,q}(A) ≤ R q / |X₁|`. -/
theorem diAdvantage_le_mul {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) :
    diAdvantage A ≤ (R * q : ℝ) / Fintype.card X₁ :=
  advantage_toAdversary A ▸ advantage_le A.toAdversary

end ShrincsSecurity.Repro

end
