module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

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

end ShrincsSecurity.Undetectability
