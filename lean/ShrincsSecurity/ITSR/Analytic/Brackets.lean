module

public import ShrincsSecurity.ITSR.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Certified brackets for `Γ_j(r)`

`ITSR-Classical.pdf`, Appendix B: **Lemma 13** (bracket for `Γ_j`).

With `P_g = binomWeight θ r g` and `u_g = leafReveal t g`, so that `Γ_j(r) = ∑_{g=0}^{r} P_g u_g^j`:

* (i) `truncated_le_gamma` and `gamma_le_truncated_add`: for `G ≥ 0` with `rθ < G + 2`,
  `∑_{g ≤ min(G, r)} P_g u_g^j ≤ Γ_j(r) ≤ ∑_{g ≤ min(G, r)} P_g u_g^j +
   (rθ)^{G+1} / (G + 1)! · 1 / (1 - rθ / (G + 2))`;
* (ii) `exp_neg_le_one_sub_pow` and `one_sub_pow_le_exp_neg`:
  `e^{-nθ/(1-θ)} ≤ (1 - θ)^n ≤ e^{-nθ}`;
* (iii) `abs_exp_neg_sub_sum_le`: `|e^{-x} - ∑_{i=0}^{M} (-x)^i / i!| ≤ x^{M+1} / (M + 1)!`.

Deviations (all weakenings of hypotheses, so the statements imply the paper's):
(i) needs only `0 ≤ θ ≤ 1` (the paper: `r ≥ 1`, `θ ∈ (0, 1)`, `t ≥ 2`); (ii) needs only `θ < 1` for
the lower bound and `θ ≤ 1` for the upper one; (iii) holds for every `x ≥ 0` and every `M`, without
the paper's hypothesis `M ≥ x` (we prove it from the Taylor remainder by integrating the derivative
bounds, instead of the alternating-series argument), and it bounds the absolute value.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR

open Finset

/-! ## Part (i): the truncated sum -/

/-- **Lemma 13(i)**, lower bound: `∑_{g ≤ min(G, r)} P_g u_g^j ≤ Γ_j(r)`. -/
theorem truncated_le_gamma {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t r j G : ℕ) :
    ∑ g ∈ range (min G r + 1), binomWeight θ r g * leafReveal t g ^ j ≤ gamma θ t r j := by
  rw [gamma_eq_binomExp]
  refine sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun g _ _ => ?_
  exact mul_nonneg (binomWeight_nonneg h0 h1 r g) (pow_nonneg (leafReveal_nonneg t g) j)

/-- `P_g u_g^j ≤ (rθ)^g / g!` (proof of Lemma 13(i)). -/
theorem binomWeight_mul_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t r j g : ℕ) :
    binomWeight θ r g * leafReveal t g ^ j ≤ ((r : ℝ) * θ) ^ g / g.factorial := by
  have hu : leafReveal t g ^ j ≤ 1 := pow_le_one₀ (leafReveal_nonneg t g) (leafReveal_le_one t g)
  have hθ : (1 - θ) ^ (r - g) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  calc binomWeight θ r g * leafReveal t g ^ j ≤ binomWeight θ r g * 1 :=
        mul_le_mul_of_nonneg_left hu (binomWeight_nonneg h0 h1 r g)
    _ = (r.choose g : ℝ) * θ ^ g * (1 - θ) ^ (r - g) := by rw [mul_one, binomWeight]
    _ ≤ (r : ℝ) ^ g / g.factorial * θ ^ g * 1 := by
        gcongr
        · exact Nat.choose_le_pow_div g r
    _ = ((r : ℝ) * θ) ^ g / g.factorial := by rw [mul_pow]; ring

/-- `a^{G+1+i} / (G+1+i)! ≤ a^{G+1} / (G+1)! · (a / (G+2))^i` for `a ≥ 0`. -/
theorem pow_div_factorial_shift_le {a : ℝ} (ha : 0 ≤ a) (G i : ℕ) :
    a ^ (G + 1 + i) / (G + 1 + i).factorial ≤
      a ^ (G + 1) / (G + 1).factorial * (a / (G + 2)) ^ i := by
  have hf : ((G + 1).factorial : ℝ) * ((G + 2 : ℝ)) ^ i ≤ (G + 1 + i).factorial := by
    have := Nat.factorial_mul_pow_le_factorial (m := G + 1) (n := i)
    exact_mod_cast this
  have hpos : (0 : ℝ) < (G + 1).factorial * ((G + 2 : ℝ)) ^ i := by positivity
  calc a ^ (G + 1 + i) / (G + 1 + i).factorial
      ≤ a ^ (G + 1 + i) / ((G + 1).factorial * ((G + 2 : ℝ)) ^ i) :=
        div_le_div_of_nonneg_left (by positivity) hpos hf
    _ = a ^ (G + 1) / (G + 1).factorial * (a / (G + 2)) ^ i := by
        rw [div_pow, pow_add]; field_simp

/-- **Lemma 13(i)**, upper bound: for `rθ < G + 2`,
`Γ_j(r) ≤ ∑_{g ≤ min(G, r)} P_g u_g^j + (rθ)^{G+1} / (G + 1)! · 1 / (1 - rθ / (G + 2))`. -/
theorem gamma_le_truncated_add {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t r j G : ℕ)
    (hG : (r : ℝ) * θ < G + 2) :
    gamma θ t r j ≤
      ∑ g ∈ range (min G r + 1), binomWeight θ r g * leafReveal t g ^ j +
        ((r : ℝ) * θ) ^ (G + 1) / (G + 1).factorial * (1 / (1 - r * θ / (G + 2))) := by
  set a : ℝ := (r : ℝ) * θ with ha
  have ha0 : 0 ≤ a := by positivity
  have hG2 : (0 : ℝ) < G + 2 := by positivity
  have hρ0 : 0 ≤ a / (G + 2) := by positivity
  have hρ1 : a / (G + 2) < 1 := by rw [div_lt_one hG2]; exact hG
  have htail0 : 0 ≤ a ^ (G + 1) / (G + 1).factorial * (1 / (1 - a / (G + 2))) := by
    have : 0 < 1 - a / (G + 2) := by linarith
    positivity
  rw [gamma_eq_binomExp]
  unfold binomExp
  rcases le_or_gt r G with hrG | hGr
  · rw [min_eq_right hrG]
    linarith
  rw [min_eq_left hGr.le, show r + 1 = (G + 1) + (r - G) by omega, sum_range_add]
  gcongr
  calc ∑ i ∈ range (r - G), binomWeight θ r (G + 1 + i) * leafReveal t (G + 1 + i) ^ j
      ≤ ∑ i ∈ range (r - G), a ^ (G + 1) / (G + 1).factorial * (a / (G + 2)) ^ i :=
        sum_le_sum fun i _ =>
          (binomWeight_mul_le h0 h1 t r j (G + 1 + i)).trans (pow_div_factorial_shift_le ha0 G i)
    _ = a ^ (G + 1) / (G + 1).factorial * ∑ i ∈ Ico 0 (r - G), (a / (G + 2)) ^ i := by
        rw [mul_sum, Nat.Ico_zero_eq_range]
    _ ≤ a ^ (G + 1) / (G + 1).factorial * ((a / (G + 2)) ^ 0 / (1 - a / (G + 2))) := by
        gcongr; exact geom_sum_Ico_le_of_lt_one hρ0 hρ1
    _ = a ^ (G + 1) / (G + 1).factorial * (1 / (1 - a / (G + 2))) := by rw [pow_zero]

/-! ## Part (ii): the factor `(1 - θ)^n` -/

/-- **Lemma 13(ii)**, upper bound: `(1 - θ)^n ≤ e^{-nθ}` for `θ ≤ 1`. -/
theorem one_sub_pow_le_exp_neg {θ : ℝ} (h1 : θ ≤ 1) (n : ℕ) :
    (1 - θ) ^ n ≤ Real.exp (-(n * θ)) := by
  rw [show -((n : ℝ) * θ) = n * (-θ) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-θ)]) n

/-- **Lemma 13(ii)**, lower bound: `e^{-nθ/(1-θ)} ≤ (1 - θ)^n` for `θ < 1`. -/
theorem exp_neg_le_one_sub_pow {θ : ℝ} (h1 : θ < 1) (n : ℕ) :
    Real.exp (-(n * θ / (1 - θ))) ≤ (1 - θ) ^ n := by
  have hpos : 0 < 1 - θ := by linarith
  have hbase : Real.exp (-(θ / (1 - θ))) ≤ 1 - θ := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hpos]
    have h := Real.add_one_le_exp (θ / (1 - θ))
    have : θ / (1 - θ) + 1 = (1 - θ)⁻¹ := by field_simp; ring
    linarith
  rw [show -((n : ℝ) * θ / (1 - θ)) = n * (-(θ / (1 - θ))) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hbase n

/-! ## Part (iii): the truncated exponential series -/

/-- The signed Taylor remainder `(-1)^N (e^{-x} - ∑_{i<N} (-x)^i / i!)` of `e^{-x}`. -/
noncomputable def expNegRem (N : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ N * (Real.exp (-x) - ∑ i ∈ range N, (-x) ^ i / i.factorial)

theorem hasDerivAt_expNegPartial (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y => ∑ i ∈ range (N + 1), (-y) ^ i / (i.factorial : ℝ))
      (-∑ i ∈ range N, (-x) ^ i / (i.factorial : ℝ)) x := by
  induction N with
  | zero => simpa using hasDerivAt_const x (1 : ℝ)
  | succ N ih =>
    have h2 : HasDerivAt (fun y => (-y) ^ (N + 1) / ((N + 1).factorial : ℝ))
        (-((-x) ^ N / (N.factorial : ℝ))) x := by
      have := ((hasDerivAt_neg x).pow (N + 1)).div_const ((N + 1).factorial : ℝ)
      convert this using 1
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    convert ih.add h2 using 1
    · funext y; rw [sum_range_succ _ (N + 1)]; rfl
    · rw [sum_range_succ]; ring

theorem hasDerivAt_expNegRem (N : ℕ) (x : ℝ) :
    HasDerivAt (expNegRem (N + 1)) (expNegRem N x) x := by
  have he : HasDerivAt (fun y => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have := (he.sub (hasDerivAt_expNegPartial N x)).const_mul ((-1 : ℝ) ^ (N + 1))
  unfold expNegRem
  convert this using 1
  rw [pow_succ]; ring

theorem hasDerivAt_pow_div_factorial (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y => y ^ (N + 1) / ((N + 1).factorial : ℝ)) (x ^ N / N.factorial) x := by
  have := (hasDerivAt_pow (N + 1) x).div_const ((N + 1).factorial : ℝ)
  convert this using 1
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- `0 ≤ (-1)^N (e^{-x} - ∑_{i<N} (-x)^i / i!) ≤ x^N / N!` for `x ≥ 0`. -/
theorem expNegRem_mem (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ expNegRem N x ∧ expNegRem N x ≤ x ^ N / N.factorial := by
  induction N generalizing x with
  | zero =>
    simp only [expNegRem, pow_zero, one_mul, range_zero, sum_empty, sub_zero,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  | succ N ih =>
    have hzero : expNegRem (N + 1) 0 = 0 := by
      simp [expNegRem, sum_range_succ']
    have hint : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
    have hmono1 : MonotoneOn (expNegRem (N + 1)) (Set.Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := expNegRem N) (convex_Ici 0)
        (fun y _ => (hasDerivAt_expNegRem N y).continuousAt.continuousWithinAt)
        (fun y _ => (hasDerivAt_expNegRem N y).hasDerivWithinAt) fun y hy => ?_
      rw [hint] at hy
      exact (ih (le_of_lt hy)).1
    have hmono2 : MonotoneOn (fun y => y ^ (N + 1) / ((N + 1).factorial : ℝ) -
        expNegRem (N + 1) y) (Set.Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun y => y ^ N / (N.factorial : ℝ) - expNegRem N y) (convex_Ici 0)
        (fun y _ => ((hasDerivAt_pow_div_factorial N y).sub
          (hasDerivAt_expNegRem N y)).continuousAt.continuousWithinAt)
        (fun y _ => ((hasDerivAt_pow_div_factorial N y).sub
          (hasDerivAt_expNegRem N y)).hasDerivWithinAt) fun y hy => ?_
      rw [hint] at hy
      exact sub_nonneg.mpr (ih (le_of_lt hy)).2
    have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
    have hxmem : x ∈ Set.Ici (0 : ℝ) := hx
    refine ⟨?_, ?_⟩
    · have := hmono1 h0mem hxmem hx
      rwa [hzero] at this
    · have := hmono2 h0mem hxmem hx
      simp only [hzero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, sub_zero] at this
      linarith

/-- **Lemma 13(iii)**: `|e^{-x} - ∑_{i=0}^{M} (-x)^i / i!| ≤ x^{M+1} / (M + 1)!` for every
`x ≥ 0` and every `M` (the paper assumes in addition `M ≥ x`). -/
theorem abs_exp_neg_sub_sum_le {x : ℝ} (hx : 0 ≤ x) (M : ℕ) :
    |Real.exp (-x) - ∑ i ∈ range (M + 1), (-x) ^ i / (i.factorial : ℝ)| ≤
      x ^ (M + 1) / (M + 1).factorial := by
  obtain ⟨h0, h1⟩ := expNegRem_mem (M + 1) hx
  have : |expNegRem (M + 1) x| =
      |Real.exp (-x) - ∑ i ∈ range (M + 1), (-x) ^ i / (i.factorial : ℝ)| := by
    rw [expNegRem, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← this, abs_of_nonneg h0]
  exact h1

end ShrincsSecurity.ITSR

end
