module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Markov's inequality at the endpoints

Undetectability paper (`notes/txt/Undetectability.txt`), **Lemma 3** (Markov brothers' inequality,
lines 384–389), in the endpoint form used by the proof of **Lemma 7** (line 496): a real polynomial
`h` of degree at most `d` with `|h t| ≤ 1` on `[-1, 1]` has `|h' (±1)| ≤ d²`.

The proof of Lemma 7 applies Lemma 3 only at `t = -1` (after the affine change of variable
`t ↦ (1 + t) / 2` from `[-1, 1]` to `[0, 1]`). The endpoint bound is derived from Mathlib's
Chebyshev extremality `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`
(`h^{(k)}(x) ≤ T_d^{(k)}(x)` for `x ≥ 1`) and `Polynomial.Chebyshev.derivative_T_eval_one`
(`T_d'(1) = d²`), applied to `h` and `-h`, and to `h(-t)` for the left endpoint.

The interior form of Lemma 3 (`|h'(t)| ≤ d²` for every `t ∈ [-1, 1]`) is not formalised: it is not
in Mathlib, its standard proofs need Bernstein's inequality for trigonometric polynomials or a
pointwise interpolation argument at interior points, and no result of the paper uses it.

## Main statements

* `abs_derivative_eval_one_le`, `abs_derivative_eval_neg_one_le`: Lemma 3 at `t = 1` and `t = -1`.
* `abs_derivative_eval_zero_le_of_unitInterval`, `abs_derivative_eval_one_le_of_unitInterval`:
  the rescaled form on `[0, 1]` used in Lemma 7: a polynomial `g` of degree at most `d` with
  `g λ ∈ [0, 1]` for `λ ∈ [0, 1]` has `|g'(0)| ≤ d²` and `|g'(1)| ≤ d²`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Polynomial

/-- One-sided Markov bound at `1`, from Mathlib's Chebyshev extremality. -/
theorem derivative_eval_one_le {d : ℕ} {h : ℝ[X]} (hdeg : h.natDegree ≤ d)
    (hbnd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |h.eval t| ≤ 1) :
    (derivative h).eval 1 ≤ (d : ℝ) ^ 2 := by
  have := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1) le_rfl
    (natDegree_le_iff_degree_le.mp hdeg) hbnd
  simpa [Chebyshev.derivative_T_eval_one] using this

/-- **Lemma 3 at `t = 1`** (Undetectability, lines 384–389): a real polynomial of degree at most
`d` bounded by `1` in absolute value on `[-1, 1]` has `|h'(1)| ≤ d²`. -/
theorem abs_derivative_eval_one_le {d : ℕ} {h : ℝ[X]} (hdeg : h.natDegree ≤ d)
    (hbnd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |h.eval t| ≤ 1) :
    |(derivative h).eval 1| ≤ (d : ℝ) ^ 2 := by
  have h₁ := derivative_eval_one_le hdeg hbnd
  have h₂ := derivative_eval_one_le (d := d) (h := -h) (by rwa [natDegree_neg])
    (fun t ht => by simpa using hbnd t ht)
  rw [abs_le]
  constructor <;> simp at h₂ <;> linarith

/-- **Lemma 3 at `t = -1`** (Undetectability, lines 384–389): a real polynomial of degree at most
`d` bounded by `1` in absolute value on `[-1, 1]` has `|h'(-1)| ≤ d²`. -/
theorem abs_derivative_eval_neg_one_le {d : ℕ} {h : ℝ[X]} (hdeg : h.natDegree ≤ d)
    (hbnd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |h.eval t| ≤ 1) :
    |(derivative h).eval (-1)| ≤ (d : ℝ) ^ 2 := by
  have hdeg' : (h.comp (-X)).natDegree ≤ d :=
    (natDegree_comp_le).trans (by simpa using hdeg)
  have := abs_derivative_eval_one_le hdeg' fun t ht => by
    simpa using hbnd (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa [derivative_comp] using this

/-- The affine bijection `[-1, 1] → [0, 1]`, `t ↦ (1 + t) / 2`, as a polynomial. -/
noncomputable def toUnitInterval : ℝ[X] := C (1 / 2) * X + C (1 / 2)

/-- The rescaling `h(t) := 2 g((1 + t) / 2) - 1` of the proof of Lemma 7 (line 494). -/
noncomputable def rescale (g : ℝ[X]) : ℝ[X] := C 2 * g.comp toUnitInterval - 1

lemma natDegree_rescale_le {d : ℕ} {g : ℝ[X]} (hdeg : g.natDegree ≤ d) :
    (rescale g).natDegree ≤ d := by
  unfold rescale
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  have : toUnitInterval.natDegree ≤ 1 := natDegree_linear_le
  calc g.natDegree * toUnitInterval.natDegree ≤ d * 1 := Nat.mul_le_mul hdeg this
    _ = d := mul_one d

lemma abs_eval_rescale_le {g : ℝ[X]} (hbnd : ∀ x ∈ Set.Icc (0 : ℝ) 1, g.eval x ∈ Set.Icc 0 1) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(rescale g).eval t| ≤ 1 := by
  intro t ht
  have := hbnd (1 / 2 * t + 1 / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [rescale, toUnitInterval, eval_sub, eval_mul, eval_C, eval_comp, eval_add, eval_X,
    eval_one]
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

lemma derivative_rescale_eval (g : ℝ[X]) (t : ℝ) :
    (derivative (rescale g)).eval t = (derivative g).eval (1 / 2 * t + 1 / 2) := by
  simp only [rescale, toUnitInterval, derivative_sub, derivative_mul, derivative_C, zero_mul,
    zero_add, derivative_comp, derivative_add, derivative_X, mul_one, add_zero, derivative_one,
    sub_zero, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  ring

/-- Lemma 3 at `t = -1` in the form used by **Lemma 7** (line 496): a real polynomial `g` of
degree at most `d` with values in `[0, 1]` on `[0, 1]` has `|g'(0)| ≤ d²`. -/
theorem abs_derivative_eval_zero_le_of_unitInterval {d : ℕ} {g : ℝ[X]} (hdeg : g.natDegree ≤ d)
    (hbnd : ∀ x ∈ Set.Icc (0 : ℝ) 1, g.eval x ∈ Set.Icc 0 1) :
    |(derivative g).eval 0| ≤ (d : ℝ) ^ 2 := by
  have := abs_derivative_eval_neg_one_le (natDegree_rescale_le hdeg) (abs_eval_rescale_le hbnd)
  rw [derivative_rescale_eval] at this
  norm_num at this
  exact this

/-- Lemma 3 at `t = 1` rescaled to `[0, 1]`: `|g'(1)| ≤ d²`. -/
theorem abs_derivative_eval_one_le_of_unitInterval {d : ℕ} {g : ℝ[X]} (hdeg : g.natDegree ≤ d)
    (hbnd : ∀ x ∈ Set.Icc (0 : ℝ) 1, g.eval x ∈ Set.Icc 0 1) :
    |(derivative g).eval 1| ≤ (d : ℝ) ^ 2 := by
  have := abs_derivative_eval_one_le (natDegree_rescale_le hdeg) (abs_eval_rescale_le hbnd)
  rw [derivative_rescale_eval] at this
  norm_num at this
  exact this

/-- Rescaling the endpoint Markov bound from `[x, 1] ⊆ [0, 1]` to `[0, 1]`: for `x ∈ [0, 1/2]`,
a polynomial `g` of degree at most `d` bounded in `[0, 1]` on `[0, 1]` satisfies
`|g'(x)| ≤ 2 d²`. -/
theorem abs_derivative_eval_le_two_mul_sq_of_unitInterval {d : ℕ} {g : ℝ[X]}
    (hdeg : g.natDegree ≤ d) (hbnd : ∀ u ∈ Set.Icc (0 : ℝ) 1, g.eval u ∈ Set.Icc 0 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    |(derivative g).eval x| ≤ 2 * (d : ℝ) ^ 2 := by
  let lin : ℝ[X] := C (1 - x) * X + C x
  let h : ℝ[X] := g.comp lin
  have hdeg' : h.natDegree ≤ d := by
    refine natDegree_comp_le.trans ?_
    have hlin : lin.natDegree ≤ 1 := natDegree_linear_le
    calc g.natDegree * lin.natDegree ≤ d * 1 := Nat.mul_le_mul hdeg hlin
      _ = d := mul_one d
  have hbnd' : ∀ u ∈ Set.Icc (0 : ℝ) 1, h.eval u ∈ Set.Icc 0 1 := by
    intro u hu
    have hval : h.eval u = g.eval ((1 - x) * u + x) := by
      simp [h, lin, eval_comp]
    rw [hval]
    exact hbnd _ ⟨by nlinarith [hx.1, hx.2, hu.1], by nlinarith [hx.1, hx.2, hu.1, hu.2]⟩
  have h0 := abs_derivative_eval_zero_le_of_unitInterval hdeg' hbnd'
  have hderiv : (derivative h).eval 0 = (1 - x) * (derivative g).eval x := by
    simp only [h, lin, derivative_comp, derivative_add, derivative_mul, derivative_C, zero_mul,
      zero_add, derivative_X, mul_one, add_zero, eval_mul, eval_comp, eval_add, eval_C, eval_X,
      mul_zero, zero_add]
  rw [hderiv, abs_mul, abs_of_nonneg (by linarith [hx.2])] at h0
  have hpos : (1 / 2 : ℝ) ≤ 1 - x := by linarith [hx.2]
  have h1 : (1 / 2 : ℝ) * |(derivative g).eval x| ≤ (1 - x) * |(derivative g).eval x| :=
    mul_le_mul_of_nonneg_right hpos (abs_nonneg _)
  linarith

/-- A polynomial `g` of degree at most `d` bounded in `[0, 1]` on `[0, 1]` with `g(0) = 0`
satisfies `g(t) ≤ 2 d² t` for every `t ∈ [0, 1/2]` (Mean Value Theorem plus the rescaled
endpoint Markov bound). -/
theorem eval_le_two_mul_sq_mul_of_unitInterval {d : ℕ} {g : ℝ[X]} (hdeg : g.natDegree ≤ d)
    (hbnd : ∀ u ∈ Set.Icc (0 : ℝ) 1, g.eval u ∈ Set.Icc 0 1) (hzero : g.eval 0 = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g.eval t ≤ 2 * (d : ℝ) ^ 2 * t := by
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · simp [hzero]
  have hcont : ContinuousOn (fun u => g.eval u) (Set.Icc 0 t) :=
    fun u _ => (g.hasDerivAt u).continuousAt.continuousWithinAt
  have hdiff : ∀ u ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun x => g.eval x) ((derivative g).eval u) u :=
    fun u _ => g.hasDerivAt u
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun u => g.eval u)
    (fun u => (derivative g).eval u) htpos hcont hdiff
  rw [hzero, sub_zero, sub_zero, eq_div_iff htpos.ne'] at hslope
  have hξ_bound := abs_derivative_eval_le_two_mul_sq_of_unitInterval hdeg hbnd
    ⟨hξ.1.le, hξ.2.le.trans ht.2⟩
  have hle : (derivative g).eval ξ ≤ 2 * (d : ℝ) ^ 2 := (le_abs_self _).trans hξ_bound
  nlinarith [htpos]

end ShrincsSecurity.Undetectability
