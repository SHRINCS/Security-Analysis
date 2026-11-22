module

public import ShrincsSecurity.Repro.Lazy
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.EvalDist.MeasureTVDist.Event
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Classical bounds for adaptive reprogramming

`SHRINCS-Security-Analysis.pdf`, Appendix C: **Lemma C.2** (`Adv^Repro_{R,q}(A) ≤ R q / |X₁|`) and
the bound `Adv^DI-Repro_{R,q}(A) ≤ q / |X₁|` of **Corollary C.2**, for every `R`.

Both follow the proof of Lemma C.4. By lazy sampling (`ShrincsSecurity.Repro.Lazy`) the two games
differ only on the event `Bad` that a call to `Reprogram` returns a seed `x₁` for which `(x₁, x₂)`
already carries a recorded value; the two lazy games are identical until `Bad` (VCVio's
`measureETVDist_simulateQ_run'_le_prEvent_bad`), so the advantage is at most `Pr[Bad]` in the lazy
`Repro_0`. Each seed is uniform and independent of the current table, so a call with second input
`x₂` raises `Bad` with probability `n / |X₁|`, where `n` is the number of seeds `x₁` with `(x₁, x₂)`
recorded, i.e. queried before the call (in the lazy `Repro_0` the table records exactly the
queried points).

* Lemma C.2: `n ≤ #recorded ≤ q`, and a union bound over the `R` calls.
* Corollary C.2: with distinct second inputs a recorded point `(x₁, x₂)` can be charged to at most
  one call, the first call at `x₂`. The potential `#pending + q`, with `pending` the recorded points
  whose second input has not been submitted, bounds `|X₁| · Pr[Bad]`: a query raises `#pending` by
  at most one and uses one unit of `q`; a call at a fresh `x₂` raises `Bad` with probability
  `n / |X₁|` and removes exactly those `n` points from `pending`; a refused call does nothing.
  The number of calls never enters.
-/

@[expose] public section

open OracleComp OracleSpec ProgramLogic.Relational MeasureTheory
open scoped ENNReal

namespace ShrincsSecurity.Repro

/-- Bound an event after a common prefix by the probability of an exceptional prefix outcome plus a
bound valid after every reachable unexceptional outcome. -/
theorem prEvent_bind_le_add_of_good {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ)
    (B : β → Prop) (p : γ → Prop) (ε : ℝ≥0∞)
    (h : ∀ a ∈ support mx, ¬B a → Pr{let c ← f a}[p c] ≤ ε) :
    Pr{let c ← mx >>= f}[p c] ≤ Pr{let a ← mx}[B a] + ε := by
  classical
  have key := prEvent_bind_le_sum_add_of_support (ι := Unit) mx f p
    (fun _ a => pure (B a)) ε fun a ha => by
      by_cases hb : B a
      · simp only [Finset.univ_unique, Finset.sum_singleton, prEvent_pure_prop, hb, ite_true]
        exact (prEvent_le_one _).trans le_self_add
      · simpa [hb] using h a ha hb
  simpa [Finset.univ_unique, map_bind] using key

/-- Bound an event after a common prefix by a bound valid after every reachable outcome. -/
theorem prEvent_bind_le_of_forall {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ)
    (p : γ → Prop) (ε : ℝ≥0∞) (h : ∀ a ∈ support mx, Pr{let c ← f a}[p c] ≤ ε) :
    Pr{let c ← mx >>= f}[p c] ≤ ε :=
  (prEvent_bind_le_add_of_good mx f (fun _ => False) p ε fun a ha _ => h a ha).trans
    (by simp)

variable {X₁ X₂ Y : Type}

/-- The recorded points of a partial table. -/
def recorded [Fintype X₁] [Fintype X₂] (t : X₁ × X₂ → Option Y) : Finset (X₁ × X₂) :=
  Finset.univ.filter fun p => (t p).isSome

/-- The seeds `x₁` for which `(x₁, x₂)` is recorded: the count `n_j` of Lemma C.4. -/
def seeds [Fintype X₁] (t : X₁ × X₂ → Option Y) (x₂ : X₂) : Finset X₁ :=
  Finset.univ.filter fun x₁ => (t (x₁, x₂)).isSome

/-- The recorded points whose second input has not been submitted to `Reprogram`. -/
def pending [Fintype X₁] [Fintype X₂] [DecidableEq X₂] (t : X₁ × X₂ → Option Y)
    (L : Finset X₂) : Finset (X₁ × X₂) :=
  Finset.univ.filter fun p => (t p).isSome ∧ p.2 ∉ L

section Counting

variable [Fintype X₁] [Fintype X₂] [DecidableEq X₁] [DecidableEq X₂]

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- At most all recorded points have second input `x₂`. -/
theorem card_seeds_le_recorded (t : X₁ × X₂ → Option Y) (x₂ : X₂) :
    (seeds t x₂).card ≤ (recorded t).card :=
  Finset.card_le_card_of_injOn (fun x₁ => (x₁, x₂))
    (fun x₁ hx => by simpa [seeds, recorded] using hx)
    (fun _ _ _ _ h => by simpa using h)

/-- Recording one more value raises the number of recorded points by at most one. -/
theorem card_recorded_update_le (t : X₁ × X₂ → Option Y) (x : X₁ × X₂) (y : Y) :
    (recorded (Function.update t x (some y))).card ≤ (recorded t).card + 1 := by
  refine (Finset.card_le_card fun p hp => ?_).trans (Finset.card_insert_le x _)
  by_cases hpx : p = x
  · simp [hpx]
  · simp_all [recorded]

/-- Recording one more value raises the number of pending points by at most one. -/
theorem card_pending_update_le (t : X₁ × X₂ → Option Y) (L : Finset X₂) (x : X₁ × X₂) (y : Y) :
    (pending (Function.update t x (some y)) L).card ≤ (pending t L).card + 1 := by
  refine (Finset.card_le_card fun p hp => ?_).trans (Finset.card_insert_le x _)
  by_cases hpx : p = x
  · simp [hpx]
  · simp_all [pending]

omit [DecidableEq X₁] in
/-- Submitting a fresh `x₂` removes from `pending` exactly the points counted by `seeds t x₂`. -/
theorem card_seeds_add_pending_insert (t : X₁ × X₂ → Option Y) (L : Finset X₂) {x₂ : X₂}
    (hx : x₂ ∉ L) :
    (seeds t x₂).card + (pending t (insert x₂ L)).card = (pending t L).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := pending t L) (fun p => p.2 = x₂)]
  congr 1
  · refine Finset.card_bij (fun x₁ _ => (x₁, x₂)) (fun x₁ hx₁ => ?_) (fun _ _ _ _ h => ?_)
      (fun p hp => ?_)
    · simp_all [seeds, pending]
    · simpa using h
    · simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨p.1, by simp [seeds, ← hp.2, hp.1.1], by simp [← hp.2]⟩
  · congr 1
    ext p
    simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    tauto

end Counting

variable [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y]
  [Fintype X₁] [Fintype X₂]

omit [DecidableEq X₁] in
/-- The seed of a uniform pair `(x₁, y)` lands in a set with its share of `X₁`. -/
theorem prEvent_uniformSample_prod_fst (P : X₁ → Prop) [DecidablePred P] :
    Pr{let w ← $ᵗ (X₁ × Y)}[P w.1] =
      (Finset.univ.filter P).card / (Fintype.card X₁ : ℝ≥0∞) := by
  rw [← SampleableType.prEvent_uniformSample P, uniformSample_prod_eq]
  refine (prEvent_bind_congr ($ᵗ X₁) _ (fun a => (pure a : ProbComp X₁))
    (fun w : X₁ × Y => P w.1) P fun x => ?_).trans (by simp)
  simpa [map_bind] using OracleComp.prEvent_bind_const ($ᵗ Y) (pure (P x))

omit [SampleableType X₁] [Fintype X₁] [Fintype X₂] in
/-- A lazy query keeps `bad`, the submitted list and the counter, logs the query, and records at
most the queried point. -/
theorem lazyHash_support (x : X₁ × X₂) (s : LazyState X₁ X₂ Y) :
    ∀ z ∈ support ((lazyHash x).run s), z.2.bad = s.bad ∧ z.2.submitted = s.submitted ∧
      z.2.log = x :: s.log ∧ z.2.count = s.count ∧
      ∃ y, z.2.table = s.table ∨ z.2.table = Function.update s.table x (some y) := by
  intro z hz
  change z ∈ support (lazyHash x s) at hz
  unfold lazyHash at hz
  rcases h : s.table x with _ | v <;> simp only [h] at hz
  · simp only [support_map, Set.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz
    exact ⟨rfl, rfl, rfl, rfl, y, Or.inr rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl, rfl, rfl, v, Or.inl rfl⟩

/-! ## Identical until bad -/

omit [Fintype X₁] [Fintype X₂] in
/-- The lazy games keep a bad state bad. -/
theorem lazyImpl_mono (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (hs : s.bad = true) : ∀ z ∈ support ((lazyImpl b t).run s), z.2.bad = true := by
  rcases t with n | x | x₂
  · simp [lazyImpl, hs]
  · intro z hz
    exact (lazyHash_support x s z hz).1.trans hs
  · simp [lazyImpl, lazyRepro_run, hs]

omit [Fintype X₁] [Fintype X₂] in
/-- The lazy `DI-Repro` games keep a bad state bad. -/
theorem lazyDIImpl_mono (b : Bool) (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (hs : s.bad = true) : ∀ z ∈ support ((lazyDIImpl b t).run s), z.2.bad = true := by
  rcases t with n | x | x₂
  · simp [lazyDIImpl, hs]
  · intro z hz
    exact (lazyHash_support x s z hz).1.trans hs
  · by_cases hx : x₂ ∈ s.submitted <;> simp [lazyDIImpl, lazyDIRepro_run, hs, hx]

omit [SampleableType X₁] [SampleableType Y] [Fintype X₁] [Fintype X₂] in
/-- Discarding the value at an unrecorded point changes nothing. -/
theorem update_none_of_isSome_eq_false (t : X₁ × X₂ → Option Y) (p : X₁ × X₂)
    (h : (t p).isSome = false) : Function.update t p none = t := by
  rw [Function.update_eq_self_iff]
  exact (by simpa using h : t p = none).symm

omit [Fintype X₁] [Fintype X₂] in
/-- From a good state, the lazy `Repro_0` and `Repro_1` agree on every good outcome. -/
theorem lazyImpl_agree (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y) (_hs : ¬s.bad = true)
    (q : (AdvSpec X₁ X₂ Y).Range t × LazyState X₁ X₂ Y → Prop) :
    Pr{let z ← (lazyImpl false t).run s}[q z ∧ ¬z.2.bad = true] =
      Pr{let z ← (lazyImpl true t).run s}[q z ∧ ¬z.2.bad = true] := by
  rcases t with n | x | x₂
  · rfl
  · rfl
  · change Pr{let z ← (lazyRepro false x₂).run s}[_] = Pr{let z ← (lazyRepro true x₂).run s}[_]
    simp only [lazyRepro_run, prEvent_map]
    refine prEvent_congr _ _ _ fun w => ?_
    rcases h : (s.table (w.1, x₂)).isSome
    · simp [update_none_of_isSome_eq_false _ _ h]
    · simp

omit [Fintype X₁] [Fintype X₂] in
/-- From a good state, the lazy `DI-Repro_0` and `DI-Repro_1` agree on every good outcome. -/
theorem lazyDIImpl_agree (t : ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) (s : LazyState X₁ X₂ Y)
    (_hs : ¬s.bad = true) (q : (DIAdvSpec X₁ X₂ Y).Range t × LazyState X₁ X₂ Y → Prop) :
    Pr{let z ← (lazyDIImpl false t).run s}[q z ∧ ¬z.2.bad = true] =
      Pr{let z ← (lazyDIImpl true t).run s}[q z ∧ ¬z.2.bad = true] := by
  rcases t with n | x | x₂
  · rfl
  · rfl
  · change Pr{let z ← (lazyDIRepro false x₂).run s}[_] =
      Pr{let z ← (lazyDIRepro true x₂).run s}[_]
    by_cases hx : x₂ ∈ s.submitted
    · simp [lazyDIRepro_run, hx]
    · simp only [lazyDIRepro_run, hx, ite_false, prEvent_map]
      refine prEvent_congr _ _ _ fun w => ?_
      rcases h : (s.table (w.1, x₂)).isSome
      · simp [update_none_of_isSome_eq_false _ _ h]
      · simp

omit [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y] [Fintype X₁]
  [Fintype X₂] in
/-- Two Boolean experiments equal in distribution to the two lazy simulations differ by at most the
probability of a bad final state of the first. -/
theorem abs_sub_le_prBad {spec : OracleSpec (ℕ ⊕ ((X₁ × X₂) ⊕ X₂))}
    (impl₀ impl₁ : QueryImpl spec (StateT (LazyState X₁ X₂ Y) ProbComp))
    (h_agree : ∀ t s, ¬s.bad = true → ∀ q : spec.Range t × LazyState X₁ X₂ Y → Prop,
      Pr{let z ← (impl₀ t).run s}[q z ∧ ¬z.2.bad = true] =
        Pr{let z ← (impl₁ t).run s}[q z ∧ ¬z.2.bad = true])
    (h_mono₀ : ∀ t s, s.bad = true → ∀ z ∈ support ((impl₀ t).run s), z.2.bad = true)
    (h_mono₁ : ∀ t s, s.bad = true → ∀ z ∈ support ((impl₁ t).run s), z.2.bad = true)
    (A : OracleComp spec Bool) (e₀ e₁ : ProbComp Bool)
    (h₀ : e₀ =ᵈ (simulateQ impl₀ A).run' LazyState.init)
    (h₁ : e₁ =ᵈ (simulateQ impl₁ A).run' LazyState.init) :
    |(Pr{let b ← e₀}[b = true]).toReal - (Pr{let b ← e₁}[b = true]).toReal| ≤
      (Pr{let z ← (simulateQ impl₀ A).run LazyState.init}[z.2.bad = true]).toReal := by
  rw [h₀.prEvent_eq, h₁.prEvent_eq]
  refine (abs_prEvent_toReal_sub_le_measureTVDist _ _ _ Measurable.of_discrete).trans ?_
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_mono (prEvent_ne_top _)
    (measureETVDist_simulateQ_run'_le_prEvent_bad impl₀ impl₁ (fun s => s.bad = true)
      h_agree h_mono₀ h_mono₁ A LazyState.init)

/-! ## Bounding the bad event -/

omit [SampleableType X₁] in
/-- A query raises the number of recorded points by at most one and keeps `bad`. -/
theorem lazyHash_recorded (x : X₁ × X₂) (s : LazyState X₁ X₂ Y) :
    ∀ z ∈ support ((lazyHash x).run s), z.2.bad = s.bad ∧
      (recorded z.2.table).card ≤ (recorded s.table).card + 1 := by
  intro z hz
  obtain ⟨hb, -, -, -, y, ht | ht⟩ := lazyHash_support x s z hz
  · exact ⟨hb, by rw [ht]; omega⟩
  · exact ⟨hb, by rw [ht]; exact card_recorded_update_le _ _ _⟩

omit [SampleableType X₁] in
/-- A query raises the number of pending points by at most one and keeps `bad`. -/
theorem lazyHash_pending (x : X₁ × X₂) (s : LazyState X₁ X₂ Y) :
    ∀ z ∈ support ((lazyHash x).run s), z.2.bad = s.bad ∧
      (pending z.2.table z.2.submitted).card ≤ (pending s.table s.submitted).card + 1 := by
  intro z hz
  obtain ⟨hb, hL, -, -, y, ht | ht⟩ := lazyHash_support x s z hz
  · exact ⟨hb, by rw [ht, hL]; omega⟩
  · exact ⟨hb, by rw [ht, hL]; exact card_pending_update_le _ _ _ _⟩

/-- **Union bound of Lemma C.2.** In the lazy `Repro_0`, from a good state with `m` recorded points,
a computation making at most `q` queries and `R` calls ends bad with probability at most
`R (m + q) / |X₁|`. -/
theorem prBad_le {α : Type} (oa : OracleComp (AdvSpec X₁ X₂ Y) α) (q R : ℕ)
    (hq : oa.IsQueryBoundP (IsHashQuery X₁ X₂) q) (hR : oa.IsQueryBoundP (IsReproQuery X₁ X₂) R)
    (s : LazyState X₁ X₂ Y) (hs : s.bad = false) :
    Pr{let z ← (simulateQ (lazyImpl false) oa).run s}[z.2.bad = true] ≤
      ((R * ((recorded s.table).card + q) : ℕ) : ℝ≥0∞) / Fintype.card X₁ := by
  induction oa using OracleComp.inductionOn generalizing q R s with
  | pure a => simp [hs]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq hR
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rcases t with n | x | x₂
    · simp only [IsHashQuery, IsReproQuery, ite_false] at hq hR
      refine prEvent_bind_le_of_forall _ _ _ _ fun z hz => ?_
      have hz' : z.2 = s := by
        obtain ⟨y, rfl⟩ := (by simpa [lazyImpl] using hz : ∃ y, (y, s) = z)
        rfl
      rw [hz']
      exact ih z.1 q R (hq.2 z.1) (hR.2 z.1) s hs
    · simp only [IsHashQuery, IsReproQuery, ite_true, ite_false] at hq hR
      have hq0 : 0 < q := by simpa using hq.1
      refine prEvent_bind_le_of_forall _ _ _ _ fun z hz => ?_
      obtain ⟨hb, hc⟩ := lazyHash_recorded x s z hz
      refine (ih z.1 (q - 1) R (hq.2 z.1) (hR.2 z.1) z.2 (hb.trans hs)).trans ?_
      refine ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ ?_)) _
      omega
    · simp only [IsHashQuery, IsReproQuery, ite_true, ite_false] at hq hR
      have hR0 : 0 < R := by simpa using hR.1
      refine (prEvent_bind_le_add_of_good _ _ (fun z => z.2.bad = true) _
        (((R - 1) * ((recorded s.table).card + q) : ℕ) / Fintype.card X₁)
        fun z hz hzb => ?_).trans ?_
      · change z ∈ support ((lazyRepro false x₂).run s) at hz
        simp only [lazyRepro_run, Bool.false_eq_true, ite_false, support_map,
          Set.mem_image] at hz
        obtain ⟨w, -, rfl⟩ := hz
        exact ih _ q (R - 1) (hq.2 _) (hR.2 _) _ (by simpa using hzb)
      · change Pr{let z ← (lazyRepro false x₂).run s}[_] + _ ≤ _
        rw [lazyRepro_run, prEvent_map]
        simp only [hs, Bool.false_or]
        rw [prEvent_uniformSample_prod_fst (Y := Y) (fun x₁ => (s.table (x₁, x₂)).isSome = true),
          ENNReal.div_add_div_same]
        gcongr
        have h1 : (Finset.univ.filter fun x₁ => (s.table (x₁, x₂)).isSome = true).card ≤
            (recorded s.table).card := card_seeds_le_recorded s.table x₂
        have h2 : (R - 1) * ((recorded s.table).card + q) + ((recorded s.table).card + q) =
            R * ((recorded s.table).card + q) := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hR0]
        exact_mod_cast (by omega :
          (Finset.univ.filter fun x₁ => (s.table (x₁, x₂)).isSome = true).card +
            (R - 1) * ((recorded s.table).card + q) ≤ R * ((recorded s.table).card + q))

/-- **Potential bound of Corollary C.2.** In the lazy `DI-Repro_0`, from a good state, a
computation making at most `q` queries, and any number of calls, ends bad with probability at most
`(#pending + q) / |X₁|`. -/
theorem diPrBad_le {α : Type} (oa : OracleComp (DIAdvSpec X₁ X₂ Y) α) (q : ℕ)
    (hq : oa.IsQueryBoundP (IsHashQuery X₁ X₂) q) (s : LazyState X₁ X₂ Y) (hs : s.bad = false) :
    Pr{let z ← (simulateQ (lazyDIImpl false) oa).run s}[z.2.bad = true] ≤
      (((pending s.table s.submitted).card + q : ℕ) : ℝ≥0∞) / Fintype.card X₁ := by
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure a => simp [hs]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rcases t with n | x | x₂
    · simp only [IsHashQuery, ite_false] at hq
      refine prEvent_bind_le_of_forall _ _ _ _ fun z hz => ?_
      have hz' : z.2 = s := by
        obtain ⟨y, rfl⟩ := (by simpa [lazyDIImpl] using hz : ∃ y, (y, s) = z)
        rfl
      rw [hz']
      exact ih z.1 q (hq.2 z.1) s hs
    · simp only [IsHashQuery, ite_true] at hq
      have hq0 : 0 < q := by simpa using hq.1
      refine prEvent_bind_le_of_forall _ _ _ _ fun z hz => ?_
      obtain ⟨hb, hc⟩ := lazyHash_pending x s z hz
      refine (ih z.1 (q - 1) (hq.2 z.1) z.2 (hb.trans hs)).trans ?_
      refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
      omega
    · simp only [IsHashQuery, ite_false] at hq
      by_cases hx : x₂ ∈ s.submitted
      · refine prEvent_bind_le_of_forall _ _ _ _ fun z hz => ?_
        change z ∈ support ((lazyDIRepro false x₂).run s) at hz
        simp only [lazyDIRepro_run, hx, ite_true, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact ih _ q (hq.2 _) s hs
      · refine (prEvent_bind_le_add_of_good _ _ (fun z => z.2.bad = true) _
          (((pending s.table (insert x₂ s.submitted)).card + q : ℕ) / Fintype.card X₁)
          fun z hz hzb => ?_).trans ?_
        · change z ∈ support ((lazyDIRepro false x₂).run s) at hz
          simp only [lazyDIRepro_run, hx, ite_false, Bool.false_eq_true, support_map,
            Set.mem_image] at hz
          obtain ⟨w, -, rfl⟩ := hz
          exact ih _ q (hq.2 _) _ (by simpa using hzb)
        · change Pr{let z ← (lazyDIRepro false x₂).run s}[_] + _ ≤ _
          rw [lazyDIRepro_run, ite_eq_right_of_eq_false _ _ (eq_false hx), prEvent_map]
          simp only [hs, Bool.false_or]
          rw [prEvent_uniformSample_prod_fst (Y := Y)
              (fun x₁ => (s.table (x₁, x₂)).isSome = true),
            ENNReal.div_add_div_same]
          gcongr
          have h := card_seeds_add_pending_insert s.table s.submitted hx
          simp only [seeds] at h
          exact_mod_cast (by omega :
            (Finset.univ.filter fun x₁ => (s.table (x₁, x₂)).isSome = true).card +
              ((pending s.table (insert x₂ s.submitted)).card + q) ≤
                (pending s.table s.submitted).card + q)

/-! ## Main results -/

/-- **Lemma C.2** (classical reprogramming). A classical adversary with at most `q` queries to
`O_b` and at most `R` calls to `Reprogram` has `Adv^Repro_{R,q}(A) ≤ R q / |X₁|`. -/
theorem advantage_le {q R : ℕ} (A : Adversary X₁ X₂ Y q R) :
    advantage A ≤ (R * q : ℝ) / Fintype.card X₁ := by
  refine (abs_sub_le_prBad (lazyImpl false) (lazyImpl true) lazyImpl_agree (lazyImpl_mono false)
    (lazyImpl_mono true) A.run _ _ (experiment_evalDistEq_lazy false A.run)
    (experiment_evalDistEq_lazy true A.run)).trans ?_
  have h := prBad_le A.run q R A.hashBound A.reproBound LazyState.init rfl
  have hr : (recorded (LazyState.init : LazyState X₁ X₂ Y).table).card = 0 := by
    simp [recorded, LazyState.init]
  rw [hr, zero_add] at h
  refine (ENNReal.toReal_mono (ENNReal.div_lt_top (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).ne h).trans_eq ?_
  rw [ENNReal.toReal_div]
  simp

/-- **Corollary C.2** (classical bound for `DI-Repro`), the form `≤ q / |X₁|`. A classical
adversary with at most `q` queries to `O_b` has `Adv^DI-Repro_{R,q}(A) ≤ q / |X₁|`, for every
number `R` of calls. -/
theorem diAdvantage_le {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) :
    diAdvantage A ≤ (q : ℝ) / Fintype.card X₁ := by
  refine (abs_sub_le_prBad (lazyDIImpl false) (lazyDIImpl true) lazyDIImpl_agree
    (lazyDIImpl_mono false) (lazyDIImpl_mono true) A.run _ _
    (diExperiment_evalDistEq_lazy false A.run) (diExperiment_evalDistEq_lazy true A.run)).trans ?_
  have h := diPrBad_le A.run q A.hashBound LazyState.init rfl
  have hr : (pending (LazyState.init : LazyState X₁ X₂ Y).table
      (LazyState.init : LazyState X₁ X₂ Y).submitted).card = 0 := by
    simp [pending, LazyState.init]
  rw [hr, zero_add] at h
  refine (ENNReal.toReal_mono (ENNReal.div_lt_top (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).ne h).trans_eq ?_
  rw [ENNReal.toReal_div]
  simp

end ShrincsSecurity.Repro

end
