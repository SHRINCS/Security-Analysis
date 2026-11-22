module

public import ShrincsSecurity.Repro.Simulation

/-!
# Per-call counts: Lemma C.4 and the expectation form of Corollary C.2

`SHRINCS-Security-Analysis.pdf`, Appendix C.

* **Lemma C.4** (classical reprogramming, per-call count):
  `Adv^Repro_{R,q}(A) ≤ (1/|X₁|) Σ_j E[n_j]`, with `n_j` the number of seeds `x₁` such that `A` has
  queried `O_b` at `(x₁, x₂^{(j)})` before its `j`-th call (`n_j := 0` if there is no `j`-th call), and
  the expectation taken in either game (`advantage_le_expectedSeedSum`).
* **Corollary C.2** (classical bound for `DI-Repro`):
  `Adv^DI-Repro_{R,q}(A) ≤ E[q_pre] / |X₁| ≤ q / |X₁|`, with `q_pre` the number of queries of `A`
  whose second input is submitted to `Reprogram` for the first time after the query, the expectation
  taken in either game (`diAdvantage_le_expectedPre`, `expectedPre_le`).

The statistics are defined on instrumentations of the experiments of Definitions C.1 and C.2
(`countExperiment`, `diCountExperiment`): the experiment additionally logs the queries to `O_b` and
accumulates `n_j` (resp. the share of `q_pre` of each call that is not refused) in a counter; the
instrumentation does not change the output (`countExperiment_fst`, `diCountExperiment_fst`).
`Σ_j E[n_j]` is the expectation of the accumulated `Σ_j n_j`.

Proof (as in the paper): by lazy sampling the counter has the same law in the eager and the lazy
game (`run_map_evalDistEq_of_step` with a projection); `Pr[Bad]` is the same in both lazy games
(identical until bad), and a call with second input `x₂` raises `Bad` with probability at most
`n / |X₁|` where `n` is its contribution to the counter, since every recorded point was queried.
The potential argument `prBad_mul_add_cnt_le` turns this into `|X₁| · Pr[Bad] ≤ E[counter]`.
For `DI-Repro`, `q_pre ≤ q` on every execution (`count_add_pend_le`).

The expectations are in `ℝ≥0∞`; the advantage is compared through `ENNReal.ofReal`.
-/

@[expose] public section

open OracleComp OracleSpec ProgramLogic.Relational MeasureTheory
open scoped ENNReal

namespace ShrincsSecurity.Repro

/-- The expectation of a natural-valued random variable. -/
noncomputable def expect (m : ProbComp ℕ) : ℝ≥0∞ := ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[m]

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σL σE σ α β γ : Type}

/-- **Simulation through a randomized state map, with a projection.** As
`run'_evalDistEq_of_step`, keeping a component `π` of the final state that the randomized map
preserves. -/
theorem run_map_evalDistEq_of_step
    (implL : QueryImpl spec (StateT σL ProbComp)) (implE : QueryImpl spec (StateT σE ProbComp))
    (κ : σL → ProbComp σE) (πL : σL → γ) (πE : σE → γ)
    (hκ : ∀ sL, ∀ sE ∈ support (κ sL), πE sE = πL sL)
    (hstep : ∀ t sL, (κ sL >>= fun sE => (implE t).run sE) =ᵈ
      ((implL t).run sL >>= fun z => (z.1, ·) <$> κ z.2))
    (oa : OracleComp spec α) (sL : σL) :
    (κ sL >>= fun sE => (fun z => (z.1, πE z.2)) <$> (simulateQ implE oa).run sE) =ᵈ
      (fun z => (z.1, πL z.2)) <$> (simulateQ implL oa).run sL := by
  induction oa using OracleComp.inductionOn generalizing sL with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ fun sE hsE => ?_)
      (EvalDistEq.bind_const (κ sL) (pure (a, πL sL)))
    rw [hκ sL sE hsE]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    calc (κ sL >>= fun sE => (implE t).run sE >>= fun z =>
          (fun w => (w.1, πE w.2)) <$> (simulateQ implE (k z.1)).run z.2)
        = ((κ sL >>= fun sE => (implE t).run sE) >>= fun z =>
            (fun w => (w.1, πE w.2)) <$> (simulateQ implE (k z.1)).run z.2) := by
          rw [bind_assoc]
      _ =ᵈ (((implL t).run sL >>= fun z => (z.1, ·) <$> κ z.2) >>= fun z =>
            (fun w => (w.1, πE w.2)) <$> (simulateQ implE (k z.1)).run z.2) :=
          EvalDistEq.bind_left (hstep t sL) _
      _ = ((implL t).run sL >>= fun z => κ z.2 >>= fun sE =>
            (fun w => (w.1, πE w.2)) <$> (simulateQ implE (k z.1)).run sE) := by
          simp [bind_assoc, bind_map_left]
      _ =ᵈ ((implL t).run sL >>= fun z =>
            (fun w => (w.1, πL w.2)) <$> (simulateQ implL (k z.1)).run z.2) :=
          EvalDistEq.bind_right _ fun z => ih z.1 z.2

/-- A natural-valued statistic bounded below on the support has expectation at least the bound. -/
theorem le_expect_of_forall (m : ProbComp ℕ) (k : ℕ) (h : ∀ n ∈ support m, k ≤ n) :
    (k : ℝ≥0∞) ≤ expect m := by
  calc (k : ℝ≥0∞) = ∫⁻ _, (k : ℝ≥0∞) ∂𝒟[m] := by
        rw [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]
    _ ≤ expect m := lintegral_mono_ae (by
        filter_upwards [ae_evalDist_of_forall_mem_support m h] with n hn using by
          exact_mod_cast hn)

/-- A natural-valued statistic bounded above on the support has expectation at most the bound. -/
theorem expect_le_of_forall (m : ProbComp ℕ) (k : ℕ) (h : ∀ n ∈ support m, n ≤ k) :
    expect m ≤ k := by
  calc expect m ≤ ∫⁻ _, (k : ℝ≥0∞) ∂𝒟[m] := lintegral_mono_ae (by
        filter_upwards [ae_evalDist_of_forall_mem_support m h] with n hn using by
          exact_mod_cast hn)
    _ = k := by rw [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- The expectation of a statistic of a bind is the average of the conditional expectations. -/
theorem expect_map_bind (mx : ProbComp β) (g : β → ProbComp γ) (f : γ → ℕ) :
    letI : MeasurableSpace β := ⊤
    expect (f <$> (mx >>= g)) = ∫⁻ a, expect (f <$> g a) ∂𝒟[mx] := by
  let : MeasurableSpace β := ⊤
  rw [expect, map_bind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
  rfl

/-- The expectation of a statistic of a computation, as an integral over its outputs. -/
theorem expect_map (mx : ProbComp β) (f : β → ℕ) :
    letI : MeasurableSpace β := ⊤
    expect (f <$> mx) = ∫⁻ a, (f a : ℝ≥0∞) ∂𝒟[mx] := by
  let : MeasurableSpace β := ⊤
  exact lintegral_evalDist_map_of_discrete mx f _

/-- A counter that never decreases along a step never decreases along a run. -/
theorem cnt_le_of_mem_support_run (impl : QueryImpl spec (StateT σ ProbComp)) (cnt : σ → ℕ)
    (hcnt : ∀ t s, ∀ z ∈ support ((impl t).run s), cnt s ≤ cnt z.2)
    (oa : OracleComp spec α) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), cnt s ≤ cnt z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    exact (hcnt t s us hus).trans (ih us.1 us.2 z hz)

/-- **Expected-count potential.** If every step from a good state satisfying an invariant raises
the bad flag with probability at most `1/c` times the expected increase of a counter that never
decreases, then `c · Pr[bad at the end] + counter at the start ≤ E[counter at the end]`. -/
theorem prBad_mul_add_cnt_le (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    [DecidablePred bad] (cnt : σ → ℕ) (inv : σ → Prop) (c : ℝ≥0∞)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hcnt : ∀ t s, ∀ z ∈ support ((impl t).run s), cnt s ≤ cnt z.2)
    (hstep : ∀ t s, inv s → ¬bad s →
      c * Pr{let z ← (impl t).run s}[bad z.2] + cnt s ≤
        expect ((fun z => cnt z.2) <$> (impl t).run s))
    (oa : OracleComp spec α) (s : σ) (hs : inv s) (hb : ¬bad s) :
    c * Pr{let z ← (simulateQ impl oa).run s}[bad z.2] + cnt s ≤
      expect ((fun z => cnt z.2) <$> (simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure]
    simp only [hb, ↓reduceIte, mul_zero, zero_add]
    exact le_expect_of_forall _ _ (by simp)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    let : MeasurableSpace (spec.Range t × σ) := ⊤
    set mx := (impl t).run s
    set P : spec.Range t × σ → ℝ≥0∞ := fun z =>
      Pr{let w ← (simulateQ impl (k z.1)).run z.2}[bad w.2]
    set E : spec.Range t × σ → ℝ≥0∞ := fun z =>
      expect ((fun w => cnt w.2) <$> (simulateQ impl (k z.1)).run z.2)
    have hP : Pr{let w ← mx >>= fun z => (simulateQ impl (k z.1)).run z.2}[bad w.2] =
        ∫⁻ z, P z ∂𝒟[mx] := prEvent_bind_eq_lintegral_of_discrete _ _ _
    have hE : expect ((fun w => cnt w.2) <$> (mx >>= fun z => (simulateQ impl (k z.1)).run z.2)) =
        ∫⁻ z, E z ∂𝒟[mx] := expect_map_bind _ _ _
    have hbad : Pr{let z ← mx}[bad z.2] = ∫⁻ z, {z | bad z.2}.indicator 1 z ∂𝒟[mx] := by
      rw [lintegral_indicator_one MeasurableSet.of_discrete, prEvent_eq_evalDist_of_discrete]
    have hcntμ : expect ((fun z => cnt z.2) <$> mx) = ∫⁻ z, (cnt z.2 : ℝ≥0∞) ∂𝒟[mx] :=
      expect_map _ _
    have hpt₁ : ∀ z, c * P z ≤ c * {z | bad z.2}.indicator 1 z +
        {z | ¬bad z.2}.indicator (fun z => c * P z) z := by
      intro z
      by_cases hz : bad z.2
      · simp only [Set.indicator, Set.mem_ofPred_eq, hz, ↓reduceIte, not_true_eq_false,
          add_zero, Pi.one_apply, mul_one]
        exact mul_le_of_le_one_right' (prEvent_le_one _)
      · simp [Set.indicator, hz]
    have hpt₂ : ∀ z ∈ support mx,
        (cnt z.2 : ℝ≥0∞) + {z | ¬bad z.2}.indicator (fun z => c * P z) z ≤ E z := by
      intro z hz
      by_cases hzb : bad z.2
      · simp only [Set.indicator, Set.mem_ofPred_eq, hzb, not_true_eq_false, ↓reduceIte,
          add_zero]
        refine le_expect_of_forall _ _ fun n hn => ?_
        simp only [support_map, Set.mem_image] at hn
        obtain ⟨w, hw, rfl⟩ := hn
        exact cnt_le_of_mem_support_run impl cnt hcnt _ _ w hw
      · simp only [Set.indicator, Set.mem_ofPred_eq, hzb, not_false_eq_true, ↓reduceIte]
        rw [add_comm]
        exact ih z.1 z.2 (hinv t s hs z hz) hzb
    rw [hP, hE]
    calc c * ∫⁻ z, P z ∂𝒟[mx] + cnt s
        = ∫⁻ z, c * P z ∂𝒟[mx] + cnt s := by
          rw [lintegral_const_mul _ Measurable.of_discrete]
      _ ≤ ∫⁻ z, (c * {z | bad z.2}.indicator 1 z +
            {z | ¬bad z.2}.indicator (fun z => c * P z) z) ∂𝒟[mx] + cnt s := by
          gcongr with z
          exact hpt₁ z
      _ = (c * Pr{let z ← mx}[bad z.2] + cnt s) +
            ∫⁻ z, {z | ¬bad z.2}.indicator (fun z => c * P z) z ∂𝒟[mx] := by
          rw [lintegral_add_left (Measurable.of_discrete), lintegral_const_mul _
            Measurable.of_discrete, hbad]
          ring
      _ ≤ ∫⁻ z, (cnt z.2 : ℝ≥0∞) ∂𝒟[mx] +
            ∫⁻ z, {z | ¬bad z.2}.indicator (fun z => c * P z) z ∂𝒟[mx] := by
          gcongr
          rw [← hcntμ]
          exact hstep t s hs hb
      _ = ∫⁻ z, ((cnt z.2 : ℝ≥0∞) + {z | ¬bad z.2}.indicator (fun z => c * P z) z) ∂𝒟[mx] := by
          rw [lintegral_add_left (Measurable.of_discrete)]
      _ ≤ ∫⁻ z, E z ∂𝒟[mx] := lintegral_mono_ae (by
          filter_upwards [ae_evalDist_of_forall_mem_support mx hpt₂] with z hz using hz)

end Generic

variable {X₁ X₂ Y : Type} [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y]

/-! ## Instrumented experiments -/

/-- `O_b` of the instrumented `Repro_b`: read the table and log the query. The state is the table,
the log of queries (latest first) and the counter. -/
def countHash (x : X₁ × X₂) :
    StateT ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) ProbComp Y := fun s =>
  pure (s.1 x, (s.1, x :: s.2.1, s.2.2))

/-- `Reprogram(x₂)` of the instrumented `Repro_b`: as in Definition C.1, and add `n_j` to the
counter. -/
def countRepro (b : Bool) (x₂ : X₂) :
    StateT ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) ProbComp X₁ := fun s =>
  (fun z : X₁ × Y => (z.1, (if b then Function.update s.1 (z.1, x₂) z.2 else s.1, s.2.1,
    s.2.2 + seedCount s.2.1 x₂))) <$> ($ᵗ (X₁ × Y))

/-- The handler of the instrumented `Repro_b`. -/
def countGameImpl (b : Bool) :
    QueryImpl (AdvSpec X₁ X₂ Y) (StateT ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) ProbComp) +
    ((fun x => countHash x : QueryImpl (HashSpec X₁ X₂ Y)
        (StateT ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) ProbComp)) +
      (fun x₂ => countRepro b x₂ : QueryImpl (ReproSpec X₁ X₂)
        (StateT ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) ProbComp)))

/-- `O_b` of the instrumented `DI-Repro_b`; the state is the table, the list `L`, the log and the
counter. -/
def diCountHash (x : X₁ × X₂) :
    StateT ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) ProbComp Y := fun s =>
  pure (s.1 x, (s.1, s.2.1, x :: s.2.2.1, s.2.2.2))

/-- `Reprogram(x₂)` of the instrumented `DI-Repro_b`: as in Definition C.2, and a call that is not
refused adds its share of `q_pre` to the counter. -/
def diCountRepro (b : Bool) (x₂ : X₂) :
    StateT ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) ProbComp (Option X₁) := fun s =>
  if x₂ ∈ s.2.1 then pure (none, s) else
  (fun z : X₁ × Y => (some z.1, (if b then Function.update s.1 (z.1, x₂) z.2 else s.1,
    insert x₂ s.2.1, s.2.2.1, s.2.2.2 + preCount s.2.2.1 x₂))) <$> ($ᵗ (X₁ × Y))

/-- The handler of the instrumented `DI-Repro_b`. -/
def diCountGameImpl (b : Bool) : QueryImpl (DIAdvSpec X₁ X₂ Y)
    (StateT ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) ProbComp) +
    ((fun x => diCountHash x : QueryImpl (HashSpec X₁ X₂ Y)
        (StateT ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) ProbComp)) +
      (fun x₂ => diCountRepro b x₂ : QueryImpl (DIReproSpec X₁ X₂)
        (StateT ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) ProbComp)))

omit [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y] in
/-- Unfolding of `countHash`. -/
theorem countHash_run (x : X₁ × X₂) (s : (X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) :
    (countHash x).run s = pure (s.1 x, (s.1, x :: s.2.1, s.2.2)) := rfl

/-- Unfolding of `countRepro`. -/
theorem countRepro_run (b : Bool) (x₂ : X₂) (s : (X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) :
    (countRepro b x₂).run s =
      (fun z : X₁ × Y => (z.1, (if b then Function.update s.1 (z.1, x₂) z.2 else s.1, s.2.1,
        s.2.2 + seedCount s.2.1 x₂))) <$> ($ᵗ (X₁ × Y)) := rfl

omit [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y] in
/-- Unfolding of `diCountHash`. -/
theorem diCountHash_run (x : X₁ × X₂)
    (s : (X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) :
    (diCountHash x).run s = pure (s.1 x, (s.1, s.2.1, x :: s.2.2.1, s.2.2.2)) := rfl

/-- Unfolding of `diCountRepro`. -/
theorem diCountRepro_run (b : Bool) (x₂ : X₂)
    (s : (X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) :
    (diCountRepro b x₂).run s = if x₂ ∈ s.2.1 then pure (none, s) else
      (fun z : X₁ × Y => (some z.1, (if b then Function.update s.1 (z.1, x₂) z.2 else s.1,
        insert x₂ s.2.1, s.2.2.1, s.2.2.2 + preCount s.2.2.1 x₂))) <$> ($ᵗ (X₁ × Y)) := rfl

variable [Fintype X₁] [Fintype X₂]

/-- The instrumented `Repro_b(A)`: its output and `Σ_j n_j`. -/
noncomputable def countExperiment (b : Bool) (A : OracleComp (AdvSpec X₁ X₂ Y) Bool) :
    ProbComp (Bool × ℕ) := do
  let O ← $ᵗ (X₁ × X₂ → Y)
  (fun z => (z.1, z.2.2.2)) <$> (simulateQ (countGameImpl b) A).run (O, [], 0)

/-- The instrumented `DI-Repro_b(A)`: its output and `q_pre`. -/
noncomputable def diCountExperiment (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) :
    ProbComp (Bool × ℕ) := do
  let O ← $ᵗ (X₁ × X₂ → Y)
  (fun z => (z.1, z.2.2.2.2)) <$> (simulateQ (diCountGameImpl b) A).run (O, ∅, [], 0)

/-- **`Σ_j E[n_j]`** of Lemma C.4, in `Repro_b`. -/
noncomputable def expectedSeedSum (b : Bool) (A : OracleComp (AdvSpec X₁ X₂ Y) Bool) : ℝ≥0∞ :=
  expect (Prod.snd <$> countExperiment b A)

/-- **`E[q_pre]`** of Corollary C.2, in `DI-Repro_b`. -/
noncomputable def expectedPre (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) : ℝ≥0∞ :=
  expect (Prod.snd <$> diCountExperiment b A)

/-- The instrumentation does not change `Repro_b`. -/
theorem countExperiment_fst (b : Bool) (A : OracleComp (AdvSpec X₁ X₂ Y) Bool) :
    Prod.fst <$> countExperiment b A =ᵈ experiment b A := by
  have hstep : ∀ t (s : (X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ),
      ((pure s.1 : ProbComp _) >>= fun O => (gameImpl b t).run O) =ᵈ
        ((countGameImpl b t).run s >>= fun z => (z.1, ·) <$> (pure z.2.1 : ProbComp _)) := by
    intro t s
    rcases t with n | x | x₂
    · simp [gameImpl, countGameImpl]
    · simp [gameImpl, countGameImpl, hashImpl, countHash_run]
    · cases b <;> simp [gameImpl, countGameImpl, reproImpl, countRepro_run]
  unfold countExperiment experiment
  simp only [map_bind, Functor.map_map]
  refine EvalDistEq.bind_right _ fun O => ?_
  have h := run'_evalDistEq_of_step (countGameImpl b) (gameImpl b) (fun s => pure s.1) hstep A
    (O, [], 0)
  simpa [StateT.run'_eq] using h.symm

/-- The instrumentation does not change `DI-Repro_b`. -/
theorem diCountExperiment_fst (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) :
    Prod.fst <$> diCountExperiment b A =ᵈ diExperiment b A := by
  have hstep : ∀ t (s : (X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ),
      ((pure (s.1, s.2.1) : ProbComp _) >>= fun O => (diGameImpl b t).run O) =ᵈ
        ((diCountGameImpl b t).run s >>= fun z =>
          (z.1, ·) <$> (pure (z.2.1, z.2.2.1) : ProbComp _)) := by
    intro t s
    rcases t with n | x | x₂
    · simp [diGameImpl, diCountGameImpl]
    · simp [diGameImpl, diCountGameImpl, hashImpl, diCountHash_run]
    · by_cases hx : x₂ ∈ s.2.1
      · simp [diGameImpl, diCountGameImpl, diReproImpl, diCountRepro_run, hx]
      · cases b <;> simp [diGameImpl, diCountGameImpl, diReproImpl, diCountRepro_run, hx]
  unfold diCountExperiment diExperiment
  simp only [map_bind, Functor.map_map]
  refine EvalDistEq.bind_right _ fun O => ?_
  have h := run'_evalDistEq_of_step (diCountGameImpl b) (diGameImpl b)
    (fun s => pure (s.1, s.2.1)) hstep A (O, ∅, [], 0)
  simpa [StateT.run'_eq] using h.symm

/-! ## The counters under lazy sampling -/

/-- Complete the table of a lazy state, keeping the log and the counter. -/
noncomputable def fillCount (s : LazyState X₁ X₂ Y) :
    ProbComp ((X₁ × X₂ → Y) × List (X₁ × X₂) × ℕ) :=
  (fun ys => (fill s.table ys, s.log, s.count)) <$> ($ᵗ (X₁ × X₂ → Y))

/-- Complete the table of a lazy state, keeping the submitted list, the log and the counter. -/
noncomputable def fillDICount (s : LazyState X₁ X₂ Y) :
    ProbComp ((X₁ × X₂ → Y) × Finset X₂ × List (X₁ × X₂) × ℕ) :=
  (fun ys => (fill s.table ys, s.submitted, s.log, s.count)) <$> ($ᵗ (X₁ × X₂ → Y))

/-- Every step of the lazy `Repro_b` commutes with completing the table of the instrumented
state. -/
theorem countImpl_step (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) :
    (fillCount s >>= fun sE => (countGameImpl b t).run sE) =ᵈ
      ((lazyImpl b t).run s >>= fun z => (z.1, ·) <$> fillCount z.2) := by
  rcases t with n | x | x₂
  · simp only [countGameImpl, lazyImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply_run,
      fillCount, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    exact EvalDistEq.bind_bind_swap _ _ _
  · have e : (fillCount s >>= fun sE => (countGameImpl b (.inr (.inl x))).run sE) =
        (($ᵗ (X₁ × X₂ → Y)) >>= fun ys =>
          pure ((fun y O (a : Finset X₂ × List (X₁ × X₂) × ℕ) => (y, (O, a.2.1, a.2.2)))
            (fill s.table ys x) (fill s.table ys) (s.submitted, x :: s.log, s.count))) := by
      simp [countGameImpl, fillCount, countHash_run, map_eq_bind_pure_comp]
    rw [e]
    refine EvalDistEq.trans (hash_comm x s (fun y O a => (y, (O, a.2.1, a.2.2)))) ?_
    simp [lazyImpl, fillCount, map_eq_bind_pure_comp]
  · have e : (fillCount s >>= fun sE => (countGameImpl b (.inr (.inr x₂))).run sE) =
        (($ᵗ (X₁ × X₂ → Y)) >>= fun ys => ($ᵗ (X₁ × Y)) >>= fun z =>
          pure ((fun x₁ O => (x₁, (O, s.log, s.count + seedCount s.log x₂))) z.1
            (if b then Function.update (fill s.table ys) (z.1, x₂) z.2
              else fill s.table ys))) := by
      cases b <;> simp [countGameImpl, fillCount, countRepro_run, map_eq_bind_pure_comp]
    rw [e]
    refine EvalDistEq.trans (repro_comm b x₂ s.table
      (fun x₁ O => (x₁, (O, s.log, s.count + seedCount s.log x₂)))) ?_
    simp [lazyImpl, lazyRepro_run, fillCount, map_eq_bind_pure_comp]

/-- Every step of the lazy `DI-Repro_b` commutes with completing the table of the instrumented
state. -/
theorem diCountImpl_step (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) :
    (fillDICount s >>= fun sE => (diCountGameImpl b t).run sE) =ᵈ
      ((lazyDIImpl b t).run s >>= fun z => (z.1, ·) <$> fillDICount z.2) := by
  rcases t with n | x | x₂
  · simp only [diCountGameImpl, lazyDIImpl, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply_run, fillDICount, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    exact EvalDistEq.bind_bind_swap _ _ _
  · have e : (fillDICount s >>= fun sE => (diCountGameImpl b (.inr (.inl x))).run sE) =
        (($ᵗ (X₁ × X₂ → Y)) >>= fun ys =>
          pure ((fun y O (a : Finset X₂ × List (X₁ × X₂) × ℕ) => (y, (O, a.1, a.2.1, a.2.2)))
            (fill s.table ys x) (fill s.table ys) (s.submitted, x :: s.log, s.count))) := by
      simp [diCountGameImpl, fillDICount, diCountHash_run, map_eq_bind_pure_comp]
    rw [e]
    refine EvalDistEq.trans (hash_comm x s (fun y O a => (y, (O, a.1, a.2.1, a.2.2)))) ?_
    simp [lazyDIImpl, fillDICount, map_eq_bind_pure_comp]
  · by_cases hx : x₂ ∈ s.submitted
    · simp [diCountGameImpl, lazyDIImpl, lazyDIRepro_run, diCountRepro_run, fillDICount, hx,
        map_eq_bind_pure_comp]
    · have e : (fillDICount s >>= fun sE => (diCountGameImpl b (.inr (.inr x₂))).run sE) =
          (($ᵗ (X₁ × X₂ → Y)) >>= fun ys => ($ᵗ (X₁ × Y)) >>= fun z =>
            pure ((fun x₁ O => (some x₁, (O, insert x₂ s.submitted, s.log,
                s.count + preCount s.log x₂))) z.1
              (if b then Function.update (fill s.table ys) (z.1, x₂) z.2
                else fill s.table ys))) := by
        cases b <;> simp [diCountGameImpl, fillDICount, diCountRepro_run, hx,
          map_eq_bind_pure_comp]
      rw [e]
      refine EvalDistEq.trans (repro_comm b x₂ s.table (fun x₁ O => (some x₁,
        (O, insert x₂ s.submitted, s.log, s.count + preCount s.log x₂)))) ?_
      simp [lazyDIImpl, lazyDIRepro_run, hx, fillDICount, map_eq_bind_pure_comp]

/-- **`Σ_j E[n_j]` under lazy sampling**: the counter of the instrumented `Repro_b` has the law of
the counter of the lazy `Repro_b`. -/
theorem expectedSeedSum_eq_lazy (b : Bool) (A : OracleComp (AdvSpec X₁ X₂ Y) Bool) :
    expectedSeedSum b A =
      expect ((fun z => z.2.count) <$> (simulateQ (lazyImpl b) A).run LazyState.init) := by
  have e : countExperiment b A = fillCount LazyState.init >>= fun sE =>
      (fun z => (z.1, z.2.2.2)) <$> (simulateQ (countGameImpl b) A).run sE := by
    simp [countExperiment, fillCount, LazyState.init]
  have h := run_map_evalDistEq_of_step (lazyImpl b) (countGameImpl b) fillCount
    LazyState.count (fun sE => sE.2.2)
    (fun sL sE hsE => by
      simp only [fillCount, support_map, Set.mem_image] at hsE
      obtain ⟨ys, -, rfl⟩ := hsE
      rfl)
    (countImpl_step b) A LazyState.init
  have h' := h.map Prod.snd
  rw [← e] at h'
  unfold expectedSeedSum expect
  rw [h'.evalDist_eq]
  simp [Functor.map_map]

/-- **`E[q_pre]` under lazy sampling**: the counter of the instrumented `DI-Repro_b` has the law
of the counter of the lazy `DI-Repro_b`. -/
theorem expectedPre_eq_lazy (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) :
    expectedPre b A =
      expect ((fun z => z.2.count) <$> (simulateQ (lazyDIImpl b) A).run LazyState.init) := by
  have e : diCountExperiment b A = fillDICount LazyState.init >>= fun sE =>
      (fun z => (z.1, z.2.2.2.2)) <$> (simulateQ (diCountGameImpl b) A).run sE := by
    simp [diCountExperiment, fillDICount, LazyState.init]
  have h := run_map_evalDistEq_of_step (lazyDIImpl b) (diCountGameImpl b) fillDICount
    LazyState.count (fun sE => sE.2.2.2)
    (fun sL sE hsE => by
      simp only [fillDICount, support_map, Set.mem_image] at hsE
      obtain ⟨ys, -, rfl⟩ := hsE
      rfl)
    (diCountImpl_step b) A LazyState.init
  have h' := h.map Prod.snd
  rw [← e] at h'
  unfold expectedPre expect
  rw [h'.evalDist_eq]
  simp [Functor.map_map]

/-! ## The potential steps -/

/-- Every recorded point of the lazy table has been queried. -/
def Logged (s : LazyState X₁ X₂ Y) : Prop := ∀ p, (s.table p).isSome → p ∈ s.log

omit [SampleableType X₁] [SampleableType Y] [Fintype X₂] in
/-- In a logged state, the seeds recorded at `x₂` are among the `n` queried ones. -/
theorem card_seeds_le_seedCount (s : LazyState X₁ X₂ Y) (hs : Logged s) (x₂ : X₂) :
    (Finset.univ.filter fun x₁ => (s.table (x₁, x₂)).isSome = true).card ≤
      seedCount s.log x₂ :=
  Finset.card_le_card_of_injOn (fun x₁ => (x₁, x₂))
    (fun x₁ hx => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp [hs _ hx])
    (fun _ _ _ _ h => by simpa using h)

omit [SampleableType X₁] [SampleableType Y] [Fintype X₁] [Fintype X₂] in
/-- Distinct queried seeds at `x₂` are at most the queries at `x₂`. -/
theorem seedCount_le_preCount (log : List (X₁ × X₂)) (x₂ : X₂) :
    seedCount log x₂ ≤ preCount log x₂ := by
  induction log with
  | nil => simp [seedCount, preCount]
  | cons a l ih =>
    simp only [seedCount, preCount] at ih ⊢
    rw [List.toFinset_cons, Finset.filter_insert, List.countP_cons]
    by_cases h : a.2 = x₂
    · simp only [h, ↓reduceIte, decide_true]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · simpa [h] using ih

omit [Fintype X₁] [Fintype X₂] in
/-- The lazy `Repro_b` keeps every recorded point logged. -/
theorem lazyImpl_logged (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (hs : Logged s) : ∀ z ∈ support ((lazyImpl b t).run s), Logged z.2 := by
  rcases t with n | x | x₂
  · intro z hz
    obtain ⟨u, rfl⟩ : ∃ u, (u, s) = z := by simpa [lazyImpl] using hz
    exact hs
  · intro z hz
    obtain ⟨-, -, hl, -, y, ht | ht⟩ := lazyHash_support x s z hz
    · intro p hp
      rw [ht] at hp
      rw [hl]
      exact List.mem_cons_of_mem _ (hs p hp)
    · intro p hp
      rw [ht] at hp
      rw [hl]
      by_cases hpx : p = x
      · subst hpx
        exact List.mem_cons_self
      · rw [Function.update_of_ne hpx] at hp
        exact List.mem_cons_of_mem _ (hs p hp)
  · intro z hz
    change z ∈ support ((lazyRepro b x₂).run s) at hz
    rw [lazyRepro_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    intro p hp
    cases b
    · exact hs p hp
    · simp only [ite_true] at hp
      by_cases hpx : p = (w.1, x₂)
      · subst hpx
        simp at hp
      · rw [Function.update_of_ne hpx] at hp
        exact hs p hp

omit [Fintype X₁] [Fintype X₂] in
/-- The lazy `DI-Repro_b` keeps every recorded point logged. -/
theorem lazyDIImpl_logged (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (hs : Logged s) : ∀ z ∈ support ((lazyDIImpl b t).run s), Logged z.2 := by
  rcases t with n | x | x₂
  · exact lazyImpl_logged b (.inl n) s hs
  · exact lazyImpl_logged b (.inr (.inl x)) s hs
  · intro z hz
    change z ∈ support ((lazyDIRepro b x₂).run s) at hz
    rw [lazyDIRepro_run] at hz
    by_cases hx : x₂ ∈ s.submitted
    · simp only [hx, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
    · simp only [hx, ↓reduceIte, support_map, Set.mem_image] at hz
      obtain ⟨w, -, rfl⟩ := hz
      intro p hp
      cases b
      · exact hs p hp
      · simp only [ite_true] at hp
        by_cases hpx : p = (w.1, x₂)
        · subst hpx
          simp at hp
        · rw [Function.update_of_ne hpx] at hp
          exact hs p hp

omit [Fintype X₁] [Fintype X₂] in
/-- The counter of the lazy `Repro_b` never decreases. -/
theorem lazyImpl_count_mono (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) :
    ∀ z ∈ support ((lazyImpl b t).run s), s.count ≤ z.2.count := by
  rcases t with n | x | x₂
  · intro z hz
    obtain ⟨u, rfl⟩ : ∃ u, (u, s) = z := by simpa [lazyImpl] using hz
    exact le_rfl
  · intro z hz
    exact (lazyHash_support x s z hz).2.2.2.1.ge
  · intro z hz
    change z ∈ support ((lazyRepro b x₂).run s) at hz
    rw [lazyRepro_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Nat.le_add_right _ _

omit [Fintype X₁] [Fintype X₂] in
/-- The counter of the lazy `DI-Repro_b` never decreases. -/
theorem lazyDIImpl_count_mono (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) :
    ∀ z ∈ support ((lazyDIImpl b t).run s), s.count ≤ z.2.count := by
  rcases t with n | x | x₂
  · exact lazyImpl_count_mono b (.inl n) s
  · exact lazyImpl_count_mono b (.inr (.inl x)) s
  · intro z hz
    change z ∈ support ((lazyDIRepro b x₂).run s) at hz
    rw [lazyDIRepro_run] at hz
    by_cases hx : x₂ ∈ s.submitted
    · simp only [hx, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_rfl
    · simp only [hx, ↓reduceIte, support_map, Set.mem_image] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact Nat.le_add_right _ _

omit [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y] [Fintype X₁]
  [Fintype X₂] in
/-- A step that keeps `bad` and the counter satisfies the potential inequality. -/
theorem count_step_of_keep {ρ : Type} (mx : ProbComp (ρ × LazyState X₁ X₂ Y))
    (s : LazyState X₁ X₂ Y) (hb : ¬s.bad = true)
    (h : ∀ z ∈ support mx, z.2.bad = s.bad ∧ z.2.count = s.count) (c : ℝ≥0∞) :
    c * Pr{let z ← mx}[z.2.bad = true] + s.count ≤ expect ((fun z => z.2.count) <$> mx) := by
  rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => hb ((h z hz).1 ▸ hz'),
    mul_zero, zero_add]
  refine le_expect_of_forall _ _ fun n hn => ?_
  simp only [support_map, Set.mem_image] at hn
  obtain ⟨z, hz, rfl⟩ := hn
  exact (h z hz).2.ge

omit [Fintype X₂] in
/-- **The per-call charge of Lemma C.4**: a call raises `bad` with probability at most `n_j / |X₁|`
and adds `n_j` to the counter. -/
theorem lazyImpl_count_step (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (hs : Logged s) (hb : ¬s.bad = true) :
    (Fintype.card X₁ : ℝ≥0∞) * Pr{let z ← (lazyImpl b t).run s}[z.2.bad = true] + s.count ≤
      expect ((fun z => z.2.count) <$> (lazyImpl b t).run s) := by
  rcases t with n | x | x₂
  · refine count_step_of_keep _ s hb (fun z hz => ?_) _
    obtain ⟨u, rfl⟩ : ∃ u, (u, s) = z := by simpa [lazyImpl] using hz
    exact ⟨rfl, rfl⟩
  · refine count_step_of_keep _ s hb (fun z hz => ?_) _
    exact ⟨(lazyHash_support x s z hz).1, (lazyHash_support x s z hz).2.2.2.1⟩
  · change (Fintype.card X₁ : ℝ≥0∞) * Pr{let z ← (lazyRepro b x₂).run s}[z.2.bad = true] +
      s.count ≤ expect ((fun z => z.2.count) <$> (lazyRepro b x₂).run s)
    have hb' : s.bad = false := by simpa using hb
    refine le_trans ?_ (le_expect_of_forall _ (s.count + seedCount s.log x₂) fun n hn => ?_)
    · rw [lazyRepro_run, prEvent_map]
      simp only [hb', Bool.false_or]
      rw [prEvent_uniformSample_prod_fst (Y := Y) (fun x₁ => (s.table (x₁, x₂)).isSome = true),
        ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), add_comm]
      push_cast
      gcongr
      exact_mod_cast card_seeds_le_seedCount s hs x₂
    · rw [lazyRepro_run] at hn
      simp only [Functor.map_map, support_map, Set.mem_image] at hn
      obtain ⟨w, -, rfl⟩ := hn
      exact le_rfl

omit [Fintype X₂] in
/-- **The per-call charge of Corollary C.2**: a call that is not refused raises `bad` with
probability at most its share of `q_pre` over `|X₁|`, and adds that share to the counter. -/
theorem lazyDIImpl_count_step (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (hs : Logged s) (hb : ¬s.bad = true) :
    (Fintype.card X₁ : ℝ≥0∞) * Pr{let z ← (lazyDIImpl b t).run s}[z.2.bad = true] + s.count ≤
      expect ((fun z => z.2.count) <$> (lazyDIImpl b t).run s) := by
  rcases t with n | x | x₂
  · exact lazyImpl_count_step b (.inl n) s hs hb
  · exact lazyImpl_count_step b (.inr (.inl x)) s hs hb
  · change (Fintype.card X₁ : ℝ≥0∞) * Pr{let z ← (lazyDIRepro b x₂).run s}[z.2.bad = true] +
      s.count ≤ expect ((fun z => z.2.count) <$> (lazyDIRepro b x₂).run s)
    by_cases hx : x₂ ∈ s.submitted
    · refine count_step_of_keep _ s hb (fun z hz => ?_) _
      rw [lazyDIRepro_run] at hz
      simp only [hx, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, rfl⟩
    have hb' : s.bad = false := by simpa using hb
    refine le_trans ?_ (le_expect_of_forall _ (s.count + preCount s.log x₂) fun n hn => ?_)
    · rw [lazyDIRepro_run, ite_eq_right_of_eq_false _ _ (eq_false hx), prEvent_map]
      simp only [hb', Bool.false_or]
      rw [prEvent_uniformSample_prod_fst (Y := Y) (fun x₁ => (s.table (x₁, x₂)).isSome = true),
        ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), add_comm]
      push_cast
      gcongr
      exact_mod_cast (card_seeds_le_seedCount s hs x₂).trans (seedCount_le_preCount _ _)
    · rw [lazyDIRepro_run, ite_eq_right_of_eq_false _ _ (eq_false hx)] at hn
      simp only [Functor.map_map, support_map, Set.mem_image] at hn
      obtain ⟨w, -, rfl⟩ := hn
      exact le_rfl

/-! ## `q_pre ≤ q` -/

/-- The queries whose second input has not been submitted yet. -/
def pendQ (s : LazyState X₁ X₂ Y) : ℕ := s.log.countP fun p => p.2 ∉ s.submitted

omit [DecidableEq X₁] [SampleableType X₁] [SampleableType Y] [Fintype X₁] [Fintype X₂] in
/-- Submitting a fresh `x₂` moves exactly the queries at `x₂` out of the pending ones. -/
theorem countP_not_mem_insert (log : List (X₁ × X₂)) (L : Finset X₂) {x₂ : X₂} (hx : x₂ ∉ L) :
    log.countP (fun p => p.2 ∉ L) =
      log.countP (fun p => p.2 ∉ insert x₂ L) + log.countP (fun p => p.2 = x₂) := by
  induction log with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    by_cases h : a.2 = x₂
    · simp [h, hx]
      omega
    · by_cases h' : a.2 ∈ L
      · simp [h, h']
      · simp [h, h']
        omega

omit [Fintype X₁] [Fintype X₂] in
/-- **`q_pre` is at most the number of queries**: along a run of the lazy `DI-Repro_b` making at
most `q` queries, the counter plus the pending queries grows by at most `q`. -/
theorem count_add_pend_le (b : Bool) {α : Type} (oa : OracleComp (DIAdvSpec X₁ X₂ Y) α) (q : ℕ)
    (hq : oa.IsQueryBoundP (IsHashQuery X₁ X₂) q) (s : LazyState X₁ X₂ Y) :
    ∀ z ∈ support ((simulateQ (lazyDIImpl b) oa).run s),
      z.2.count + pendQ z.2 ≤ s.count + pendQ s + q := by
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    omega
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨us, hus, hz⟩ := hz
    rcases t with n | x | x₂
    · simp only [IsHashQuery, ite_false] at hq
      obtain ⟨u, rfl⟩ : ∃ u, (u, s) = us := by simpa [lazyDIImpl] using hus
      exact ih u q (hq.2 u) s z hz
    · simp only [IsHashQuery, ite_true] at hq
      have hq0 : 0 < q := by simpa using hq.1
      obtain ⟨-, hL, hl, hc, -⟩ := lazyHash_support x s us hus
      have h1 := ih us.1 (q - 1) (hq.2 us.1) us.2 z hz
      have h2 : pendQ us.2 ≤ pendQ s + 1 := by
        simp only [pendQ, hL, hl, List.countP_cons]
        split_ifs <;> omega
      omega
    · simp only [IsHashQuery, ite_false] at hq
      change us ∈ support ((lazyDIRepro b x₂).run s) at hus
      rw [lazyDIRepro_run] at hus
      by_cases hx : x₂ ∈ s.submitted
      · simp only [hx, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hus
        subst hus
        exact ih _ q (hq.2 _) s z hz
      · simp only [hx, ↓reduceIte, support_map, Set.mem_image] at hus
        obtain ⟨w, -, rfl⟩ := hus
        have h1 := ih _ q (hq.2 _) _ z hz
        have h2 := countP_not_mem_insert s.log s.submitted hx
        simp only [pendQ, preCount] at h1 h2 ⊢
        omega

/-! ## Main results -/

/-- **Lemma C.4** (classical reprogramming, per-call count). For a classical adversary,
`Adv^Repro_{R,q}(A) ≤ (1/|X₁|) Σ_j E[n_j]`, with the expectation taken in either game `Repro_b`. -/
theorem advantage_le_expectedSeedSum {q R : ℕ} (A : Adversary X₁ X₂ Y q R) (b : Bool) :
    ENNReal.ofReal (advantage A) ≤ expectedSeedSum b A.run / Fintype.card X₁ := by
  have h0 := abs_sub_le_prBad (lazyImpl false) (lazyImpl true) lazyImpl_agree
    (lazyImpl_mono false) (lazyImpl_mono true) A.run _ _ (experiment_evalDistEq_lazy false A.run)
    (experiment_evalDistEq_lazy true A.run)
  have hbad : Pr{let z ← (simulateQ (lazyImpl false) A.run).run LazyState.init}[z.2.bad = true] =
      Pr{let z ← (simulateQ (lazyImpl b) A.run).run LazyState.init}[z.2.bad = true] := by
    cases b
    · rfl
    · exact prEvent_simulateQ_run_bad_eq _ _ (fun s : LazyState X₁ X₂ Y => s.bad = true)
        lazyImpl_agree
        (lazyImpl_mono false) (lazyImpl_mono true) A.run _
  have hpot := prBad_mul_add_cnt_le (lazyImpl b) (fun s : LazyState X₁ X₂ Y => s.bad = true)
    LazyState.count Logged
    (Fintype.card X₁) (lazyImpl_logged b) (lazyImpl_count_mono b) (lazyImpl_count_step b) A.run
    LazyState.init (fun p hp => by simp [LazyState.init] at hp) (by simp [LazyState.init])
  rw [← expectedSeedSum_eq_lazy] at hpot
  simp only [LazyState.init, Nat.cast_zero, add_zero] at hpot
  calc ENNReal.ofReal (advantage A)
      ≤ Pr{let z ← (simulateQ (lazyImpl false) A.run).run LazyState.init}[z.2.bad = true] :=
        ENNReal.ofReal_le_of_le_toReal h0
    _ = Pr{let z ← (simulateQ (lazyImpl b) A.run).run LazyState.init}[z.2.bad = true] := hbad
    _ ≤ expectedSeedSum b A.run / Fintype.card X₁ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
          (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]
        exact hpot

/-- **Corollary C.2**, first inequality: `Adv^DI-Repro_{R,q}(A) ≤ E[q_pre] / |X₁|`, with the
expectation taken in either game `DI-Repro_b`. -/
theorem diAdvantage_le_expectedPre {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) (b : Bool) :
    ENNReal.ofReal (diAdvantage A) ≤ expectedPre b A.run / Fintype.card X₁ := by
  have h0 := abs_sub_le_prBad (lazyDIImpl false) (lazyDIImpl true) lazyDIImpl_agree
    (lazyDIImpl_mono false) (lazyDIImpl_mono true) A.run _ _
    (diExperiment_evalDistEq_lazy false A.run) (diExperiment_evalDistEq_lazy true A.run)
  have hbad :
      Pr{let z ← (simulateQ (lazyDIImpl false) A.run).run LazyState.init}[z.2.bad = true] =
        Pr{let z ← (simulateQ (lazyDIImpl b) A.run).run LazyState.init}[z.2.bad = true] := by
    cases b
    · rfl
    · exact prEvent_simulateQ_run_bad_eq _ _ (fun s : LazyState X₁ X₂ Y => s.bad = true)
        lazyDIImpl_agree
        (lazyDIImpl_mono false) (lazyDIImpl_mono true) A.run _
  have hpot := prBad_mul_add_cnt_le (lazyDIImpl b) (fun s : LazyState X₁ X₂ Y => s.bad = true)
    LazyState.count Logged
    (Fintype.card X₁) (lazyDIImpl_logged b) (lazyDIImpl_count_mono b) (lazyDIImpl_count_step b)
    A.run LazyState.init (fun p hp => by simp [LazyState.init] at hp) (by simp [LazyState.init])
  rw [← expectedPre_eq_lazy] at hpot
  simp only [LazyState.init, Nat.cast_zero, add_zero] at hpot
  calc ENNReal.ofReal (diAdvantage A)
      ≤ Pr{let z ← (simulateQ (lazyDIImpl false) A.run).run LazyState.init}[z.2.bad = true] :=
        ENNReal.ofReal_le_of_le_toReal h0
    _ = Pr{let z ← (simulateQ (lazyDIImpl b) A.run).run LazyState.init}[z.2.bad = true] := hbad
    _ ≤ expectedPre b A.run / Fintype.card X₁ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
          (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]
        exact hpot

/-- **Corollary C.2**, second inequality: `E[q_pre] ≤ q`, in either game. -/
theorem expectedPre_le {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) (b : Bool) :
    expectedPre b A.run ≤ q := by
  rw [expectedPre_eq_lazy]
  refine expect_le_of_forall _ _ fun n hn => ?_
  simp only [support_map, Set.mem_image] at hn
  obtain ⟨z, hz, rfl⟩ := hn
  have h := count_add_pend_le b A.run q A.hashBound LazyState.init z hz
  simp only [pendQ, LazyState.init, List.countP_nil] at h
  omega

/-- **Corollary C.2** (classical bound for `DI-Repro`), both inequalities:
`Adv^DI-Repro_{R,q}(A) ≤ E[q_pre] / |X₁| ≤ q / |X₁|`, in either game, for every `R`. -/
theorem corollaryC2 {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) (b : Bool) :
    ENNReal.ofReal (diAdvantage A) ≤ expectedPre b A.run / Fintype.card X₁ ∧
      expectedPre b A.run / Fintype.card X₁ ≤ q / Fintype.card X₁ :=
  ⟨diAdvantage_le_expectedPre A b, ENNReal.div_le_div_right (expectedPre_le A b) _⟩

end ShrincsSecurity.Repro

end
