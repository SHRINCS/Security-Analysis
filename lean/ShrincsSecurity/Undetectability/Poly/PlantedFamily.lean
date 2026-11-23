module

public import ShrincsSecurity.Undetectability.Poly.Markov
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The planted-family lemma

Undetectability paper (`notes/txt/Undetectability.txt`), Section 3, **Lemma 7** (lines 457–499).

Let `N ≥ 1`, `E₀, …, E_N` distributions on `Ω`, and `D_λ := ∑_{k ≤ N} b_{N,k}(λ) E_k` the mixture
with binomial weights `b_{N,k}(λ) = C(N,k) λ^k (1-λ)^{N-k}` (Mathlib's
`bernsteinPolynomial ℝ N k`). For an algorithm `B` with input `ω ∈ Ω` and output a bit, put
`p_k := Pr_{ω ← E_k}[B(ω) = 1]` and `g(λ) := Pr_{ω ← D_λ}[B(ω) = 1]`. If `g` coincides on `[0, 1]`
with a real polynomial of degree at most `d`, then `|p₁ - p₀| ≤ d² / N`.

## Modelling choices

* `λ` is a Lean keyword; the mixture parameter is written `x`.
* The hypothesis "`g` coincides on `[0, 1]` with a real polynomial of degree at most `d`" is
  `IsPolyOnUnitInterval g d`. This is the interface that the quantum degree bound (Lemma 1 via
  Lemma 8, resp. Lemma 15) supplies; see `ShrincsSecurity.Undetectability.Poly.Acceptance`.
* A distribution on `Ω` is a probability measure (`planted_family`). The algorithm `B` may be
  randomised (or quantum), so it enters through its acceptance probability `acc ω ∈ [0, 1]` on
  input `ω`, and `p_k = ∫ acc ∂E_k`, `g(x) = ∫ acc ∂D_x` (law of total probability over the
  internal coins of `B`). A deterministic `B` is the indicator of the event `{B = 1}`
  (`planted_family_event`).
* `planted_family_of_bounded` is the arithmetic core, stated with the numbers `p_k` only, for use
  with finite explicit weights (as in `Poly.Boolean`).

## Main statements

* `planted_family`: **Lemma 7** for a randomised `B` given by its acceptance probability.
* `planted_family_event`: **Lemma 7** for a deterministic `B`, i.e. a measurable event.
* `planted_family_of_bounded`, `planted_family_real`: the core inequality on the numbers `p_k`.
* `derivative_bernsteinMix_eval_zero`: equation (2), `g'(0) = N (p₁ - p₀)`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Polynomial MeasureTheory

/-! ### Polynomials on the unit interval -/

/-- `g` coincides on `[0, 1]` with a real polynomial of degree at most `d` (the hypothesis of
Lemma 7, line 461). -/
def IsPolyOnUnitInterval (g : ℝ → ℝ) (d : ℕ) : Prop :=
  ∃ Q : ℝ[X], Q.natDegree ≤ d ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = Q.eval x

namespace IsPolyOnUnitInterval

lemma of_poly {Q : ℝ[X]} {d : ℕ} (hQ : Q.natDegree ≤ d) :
    IsPolyOnUnitInterval (fun x => Q.eval x) d :=
  ⟨Q, hQ, fun _ _ => rfl⟩

lemma mono {g : ℝ → ℝ} {d d' : ℕ} (h : IsPolyOnUnitInterval g d) (hd : d ≤ d') :
    IsPolyOnUnitInterval g d' := by
  obtain ⟨Q, hQ, hg⟩ := h
  exact ⟨Q, hQ.trans hd, hg⟩

lemma congr {g g' : ℝ → ℝ} {d : ℕ} (h : IsPolyOnUnitInterval g d)
    (hgg' : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = g' x) : IsPolyOnUnitInterval g' d := by
  obtain ⟨Q, hQ, hg⟩ := h
  exact ⟨Q, hQ, fun x hx => (hgg' x hx).symm.trans (hg x hx)⟩

/-- Linear combinations, with coefficients that do not depend on the parameter, of polynomials of
degree at most `d` are polynomials of degree at most `d` (the last steps of the proofs of Lemma 8,
line 600, and of Lemma 15, lines 975–986). -/
lemma sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) {g : ι → ℝ → ℝ} {d : ℕ}
    (h : ∀ i ∈ s, IsPolyOnUnitInterval (g i) d) :
    IsPolyOnUnitInterval (fun x => ∑ i ∈ s, w i * g i x) d := by
  classical
  choose! Q hQ hg using h
  refine ⟨∑ i ∈ s, C (w i) * Q i, natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_le _ _).trans (hQ i hi), fun x hx => ?_⟩
  rw [eval_finsetSum]
  exact Finset.sum_congr rfl fun i hi => by rw [eval_mul, eval_C, hg i hi x hx]

end IsPolyOnUnitInterval

/-! ### Binomial weights -/

/-- The binomial weight `b_{N,k}(x) = C(N,k) x^k (1 - x)^{N-k}`. -/
noncomputable def binomWeight (N k : ℕ) (x : ℝ) : ℝ := (bernsteinPolynomial ℝ N k).eval x

lemma binomWeight_eq (N k : ℕ) (x : ℝ) :
    binomWeight N k x = N.choose k * x ^ k * (1 - x) ^ (N - k) := by
  simp [binomWeight, bernsteinPolynomial]

lemma binomWeight_nonneg (N k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binomWeight N k x := by
  rw [binomWeight_eq]
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.2 hx.2) _)

lemma sum_binomWeight (N : ℕ) (x : ℝ) : ∑ k ∈ Finset.range (N + 1), binomWeight N k x = 1 := by
  simpa [binomWeight, eval_finsetSum] using congrArg (eval x) (bernsteinPolynomial.sum ℝ N)

/-- A binomial mixture of numbers in `[0, 1]` lies in `[0, 1]` (line 492). -/
lemma sum_binomWeight_mul_mem_Icc (N : ℕ) {p : ℕ → ℝ} (hp : ∀ k ≤ N, p k ∈ Set.Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∑ k ∈ Finset.range (N + 1), binomWeight N k x * p k ∈ Set.Icc (0 : ℝ) 1 := by
  have hp' : ∀ k ∈ Finset.range (N + 1), p k ∈ Set.Icc (0 : ℝ) 1 :=
    fun k hk => hp k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  refine ⟨Finset.sum_nonneg fun k hk => mul_nonneg (binomWeight_nonneg N k hx) (hp' k hk).1, ?_⟩
  calc ∑ k ∈ Finset.range (N + 1), binomWeight N k x * p k
      ≤ ∑ k ∈ Finset.range (N + 1), binomWeight N k x :=
        Finset.sum_le_sum fun k hk =>
          mul_le_of_le_one_right (binomWeight_nonneg N k hx) (hp' k hk).2
    _ = 1 := sum_binomWeight N x

/-- The polynomial `G(λ) = ∑_{k ≤ N} b_{N,k}(λ) p_k` of the proof of Lemma 7 (line 474). -/
noncomputable def bernsteinMix (N : ℕ) (p : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C (p k) * bernsteinPolynomial ℝ N k

lemma eval_bernsteinMix (N : ℕ) (p : ℕ → ℝ) (x : ℝ) :
    (bernsteinMix N p).eval x = ∑ k ∈ Finset.range (N + 1), binomWeight N k x * p k := by
  simp [bernsteinMix, eval_finsetSum, binomWeight, mul_comm]

/-- Equation (2) of the proof of Lemma 7 (line 490): `G'(0) = N (p₁ - p₀)`. -/
theorem derivative_bernsteinMix_eval_zero {N : ℕ} (hN : 1 ≤ N) (p : ℕ → ℝ) :
    (derivative (bernsteinMix N p)).eval 0 = N * (p 1 - p 0) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' hN
  have hk : ∀ k, (derivative (bernsteinPolynomial ℝ (M + 1) (k + 2))).eval 0 = 0 := fun k => by
    simpa using bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt ℝ (M + 1)
      (k := 1) (ν := k + 2) (by omega)
  rw [bernsteinMix, map_sum, eval_finsetSum, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [derivative_C_mul, eval_mul, eval_C, hk, mul_zero, Finset.sum_const_zero, zero_add]
  rw [bernsteinPolynomial.derivative_zero, bernsteinPolynomial.derivative_succ]
  simp [bernsteinPolynomial.eval_at_0]
  ring

/-! ### Lemma 7 -/

/-- **Lemma 7, arithmetic core.** If the binomial mixture `g(x) = ∑_{k ≤ N} b_{N,k}(x) p_k` takes
values in `[0, 1]` on `[0, 1]` and coincides there with a polynomial of degree at most `d`, then
`|p₁ - p₀| ≤ d² / N`. -/
theorem planted_family_of_bounded {N d : ℕ} (hN : 1 ≤ N) (p : ℕ → ℝ)
    (hbnd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∑ k ∈ Finset.range (N + 1), binomWeight N k x * p k ∈ Set.Icc (0 : ℝ) 1)
    (hg : IsPolyOnUnitInterval (fun x => ∑ k ∈ Finset.range (N + 1), binomWeight N k x * p k) d) :
    |p 1 - p 0| ≤ (d : ℝ) ^ 2 / N := by
  obtain ⟨Q, hQdeg, hQ⟩ := hg
  -- `G - Q` vanishes on the infinite set `[0, 1]`, so `G = Q` (line 478).
  have hGQ : bernsteinMix N p = Q := by
    refine eq_of_infinite_eval_eq _ _ ((Set.Icc_infinite (zero_lt_one' ℝ)).mono fun x hx => ?_)
    simp only [Set.mem_ofPred_eq, eval_bernsteinMix]
    exact hQ x hx
  have hderiv := abs_derivative_eval_zero_le_of_unitInterval (g := bernsteinMix N p)
    (hGQ ▸ hQdeg) fun x hx => by rw [eval_bernsteinMix]; exact hbnd x hx
  rw [derivative_bernsteinMix_eval_zero hN, abs_mul, Nat.abs_cast] at hderiv
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hN', mul_comm]
  exact hderiv

/-- **Lemma 7 on the numbers `p_k ∈ [0, 1]`.** If `∑_{k ≤ N} b_{N,k}(x) p_k` coincides on `[0, 1]`
with a polynomial of degree at most `d`, then `|p₁ - p₀| ≤ d² / N`. -/
theorem planted_family_real {N d : ℕ} (hN : 1 ≤ N) {p : ℕ → ℝ}
    (hp : ∀ k ≤ N, p k ∈ Set.Icc (0 : ℝ) 1)
    (hg : IsPolyOnUnitInterval (fun x => ∑ k ∈ Finset.range (N + 1), binomWeight N k x * p k) d) :
    |p 1 - p 0| ≤ (d : ℝ) ^ 2 / N :=
  planted_family_of_bounded hN p (fun _ hx => sum_binomWeight_mul_mem_Icc N hp hx) hg

section Measure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The binomial mixture `D_λ := ∑_{k ≤ N} b_{N,k}(λ) E_k` of Lemma 7 (line 459). -/
noncomputable def plantedMixture (N : ℕ) (E : ℕ → Measure Ω) (x : ℝ) : Measure Ω :=
  ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (binomWeight N k x) • E k

lemma integral_finset_sum_measure' {ι : Type*} (s : Finset ι) (μ : ι → Measure Ω) {f : Ω → ℝ}
    (hf : ∀ i ∈ s, Integrable f (μ i)) :
    ∫ ω, f ω ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ ω, f ω ∂(μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, Integrable f (μ j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsum : Integrable f (∑ j ∈ s, μ j) := by
      clear ih
      induction s using Finset.induction_on with
      | empty => simp
      | insert j t hj iht =>
        rw [Finset.sum_insert hj]
        exact (hs j (Finset.mem_insert_self j t)).add_measure
          (iht (fun h => hi (Finset.mem_insert_of_mem h))
            (fun k hk => hf k (by grind)) fun k hk => hs k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integral_add_measure (hf i (Finset.mem_insert_self i s)) hsum, ih hs]

/-- Law of total probability for the mixture (line 474): `∫ acc ∂D_x = ∑ b_{N,k}(x) ∫ acc ∂E_k`. -/
theorem integral_plantedMixture {N : ℕ} {E : ℕ → Measure Ω} {acc : Ω → ℝ}
    (hint : ∀ k ≤ N, Integrable acc (E k)) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, acc ω ∂(plantedMixture N E x) =
      ∑ k ∈ Finset.range (N + 1), binomWeight N k x * ∫ ω, acc ω ∂(E k) := by
  rw [plantedMixture, integral_finset_sum_measure' _ _ fun k hk =>
    (hint k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (binomWeight_nonneg N k hx), smul_eq_mul]

/-- **Lemma 7 (Planted family)**, Undetectability lines 457–499. Let `N ≥ 1`, let `E₀, …, E_N` be
probability distributions on `Ω`, and let `B` be an algorithm on inputs `ω ∈ Ω` accepting with
probability `acc ω ∈ [0, 1]`. Put `p_k := ∫ acc ∂E_k = Pr_{ω ← E_k}[B(ω) = 1]` and
`g(λ) := ∫ acc ∂D_λ = Pr_{ω ← D_λ}[B(ω) = 1]`. If `g` coincides on `[0, 1]` with a real polynomial
of degree at most `d`, then `|p₁ - p₀| ≤ d² / N`. -/
theorem planted_family {N d : ℕ} (hN : 1 ≤ N) {E : ℕ → Measure Ω}
    (hE : ∀ k ≤ N, IsProbabilityMeasure (E k)) {acc : Ω → ℝ} (hmeas : Measurable acc)
    (hacc : ∀ ω, acc ω ∈ Set.Icc (0 : ℝ) 1)
    (hg : IsPolyOnUnitInterval (fun x => ∫ ω, acc ω ∂(plantedMixture N E x)) d) :
    |∫ ω, acc ω ∂(E 1) - ∫ ω, acc ω ∂(E 0)| ≤ (d : ℝ) ^ 2 / N := by
  have hint : ∀ k ≤ N, Integrable acc (E k) := fun k hk =>
    have := hE k hk
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hacc ω).1]; exact (hacc ω).2)
  have hp : ∀ k ≤ N, ∫ ω, acc ω ∂(E k) ∈ Set.Icc (0 : ℝ) 1 := fun k hk =>
    have := hE k hk
    ⟨integral_nonneg fun ω => (hacc ω).1, by
      simpa using integral_mono (hint k hk) (integrable_const (1 : ℝ)) fun ω => (hacc ω).2⟩
  exact planted_family_real (p := fun k => ∫ ω, acc ω ∂(E k)) hN hp
    (hg.congr fun x hx => integral_plantedMixture hint hx)

/-- **Lemma 7 for a deterministic distinguisher**: `B(ω) = 1` iff `ω ∈ A` for a measurable `A`;
`p_k = E_k(A)` and `g(λ) = D_λ(A)`. -/
theorem planted_family_event {N d : ℕ} (hN : 1 ≤ N) {E : ℕ → Measure Ω}
    (hE : ∀ k ≤ N, IsProbabilityMeasure (E k)) {A : Set Ω} (hA : MeasurableSet A)
    (hg : IsPolyOnUnitInterval (fun x => (plantedMixture N E x).real A) d) :
    |(E 1).real A - (E 0).real A| ≤ (d : ℝ) ^ 2 / N := by
  have hacc : ∀ ω, A.indicator (1 : Ω → ℝ) ω ∈ Set.Icc (0 : ℝ) 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [h]
  have := planted_family hN hE ((measurable_one).indicator hA) hacc
    (hg.congr fun x _ => (integral_indicator_one hA).symm)
  simpa [integral_indicator_one hA] using this

end Measure

end ShrincsSecurity.Undetectability
