module

public import ShrincsSecurity.ITSR.Analytic.Basic
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.LinearCombination

/-!
# The upper form of `Γ_j(r)` and `A_m`

`ITSR-Classical.pdf`, Section 7: **Lemma 12** (upper form), together with the identity (26) of
Remark 4.

* `binomMoment θ r j = ∑_{s=0}^{j} St(j, s) (r)_s θ^s` is the closed form of the binomial moment
  `E[g^j]`, `g ∼ Bin(r, θ)` (`binomExp_pow_eq_binomMoment`).
* `fwdDiffPow k m x = ∑_{s=0}^{m} (-1)^{m-s} C(m, s) (x + s)^k` is the forward difference `Δ_m(x)`
  of Eq. (24), and `fwdDiffPow_eq_sum` is Eq. (26):
  `Δ_m(x) = ∑_{ω=m}^{k} C(k, ω) m! St(ω, m) x^{k-ω}`.
* Lemma 12(i) is `gamma_le_binomMoment_div`: `Γ_j(r) ≤ E[g^j] / t^j`.
* Lemma 12(ii) is `pullHarmUpper_eq` (the expression obtained from `A_m` by replacing every
  `Γ_{k-ω}(r)` with `E[g^{k-ω}] / t^{k-ω}` equals `t^{-k} E[Δ_m(g)]`) and
  `pullHarm_le_binomExp_fwdDiffPow` (`A_m ≤ t^{-k} E[Δ_m(g)]`).

The expectation `E[Δ_m(g)]` is the finite sum `binomExp θ r (fun g => fwdDiffPow k m g)`. The
statements hold for every `j` and `m` (the paper restricts to `j ≤ k` and `1 ≤ m ≤ k`) and every
`t` (the paper has `t ≥ 1`); the inequalities need `0 ≤ θ ≤ 1`.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR

open Finset

/-- The binomial moment `E[g^j] = ∑_{s=0}^{j} St(j, s) (r)_s θ^s` of `g ∼ Bin(r, θ)`
(Lemma 12(i)). -/
noncomputable def binomMoment (θ : ℝ) (r j : ℕ) : ℝ :=
  ∑ s ∈ range (j + 1), (Nat.stirlingSecond j s : ℝ) * (r.descFactorial s : ℝ) * θ ^ s

/-- The forward difference `Δ_m(x) = ∑_{s=0}^{m} (-1)^{m-s} C(m, s) (x + s)^k` (Eq. (24)). -/
noncomputable def fwdDiffPow (k m : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ range (m + 1), (-1 : ℝ) ^ (m - s) * (m.choose s : ℝ) * (x + s) ^ k

/-- The upper form of `A_m` (Lemma 12(ii)): `A_m` with every `Γ_{k-ω}(r)` replaced by
`E[g^{k-ω}] / t^{k-ω}`. -/
noncomputable def pullHarmUpper (θ : ℝ) (t k r m : ℕ) : ℝ :=
  ∑ ω ∈ Icc m k,
    (k.choose ω : ℝ) * (m.factorial : ℝ) * (Nat.stirlingSecond ω m : ℝ) * ((t : ℝ)⁻¹) ^ ω *
      (binomMoment θ r (k - ω) / (t : ℝ) ^ (k - ω))

/-! ## Binomial moments -/

/-- `C(s + d, s + i) (s + i)_s = (s + d)_s C(d, i)`. -/
theorem choose_mul_descFactorial_shift (s d i : ℕ) :
    (s + d).choose (s + i) * (s + i).descFactorial s = (s + d).descFactorial s * d.choose i := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_left_comm, Nat.choose_mul (Nat.le_add_right s i)]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- The factorial moments of the binomial law: `E[(g)_s] = (r)_s θ^s` (proof of Lemma 12(i)). -/
theorem binomExp_descFactorial (θ : ℝ) (r s : ℕ) :
    binomExp θ r (fun g => (g.descFactorial s : ℝ)) = (r.descFactorial s : ℝ) * θ ^ s := by
  unfold binomExp
  beta_reduce
  rcases lt_or_ge r s with hrs | hsr
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hrs, Nat.cast_zero, zero_mul]
    refine sum_eq_zero fun g hg => ?_
    have : g < s := (Nat.lt_succ_iff.mp (mem_range.mp hg)).trans_lt hrs
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr this, Nat.cast_zero, mul_zero]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsr
  rw [show s + d + 1 = s + (d + 1) by ring, sum_range_add]
  have h1 : ∑ g ∈ range s, binomWeight θ (s + d) g * (g.descFactorial s : ℝ) = 0 :=
    sum_eq_zero fun g hg => by
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hg), Nat.cast_zero, mul_zero]
  rw [h1, zero_add, ← mul_one ((s + d).descFactorial s * θ ^ s : ℝ), ← sum_binomWeight θ d,
    mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hc : ((s + d).choose (s + i) : ℝ) * ((s + i).descFactorial s : ℝ) =
      ((s + d).descFactorial s : ℝ) * (d.choose i : ℝ) := by
    exact_mod_cast choose_mul_descFactorial_shift s d i
  have he : s + d - (s + i) = d - i := Nat.add_sub_add_left s d i
  unfold binomWeight
  rw [he, pow_add]
  linear_combination (θ ^ s * θ ^ i * (1 - θ) ^ (d - i)) * hc

/-- `E[g^j] = ∑_{s=0}^{j} St(j, s) (r)_s θ^s` (Lemma 12(i), closed form). -/
theorem binomExp_pow_eq_binomMoment (θ : ℝ) (r j : ℕ) :
    binomExp θ r (fun g => (g : ℝ) ^ j) = binomMoment θ r j := by
  have hpow : (fun g : ℕ => (g : ℝ) ^ j) = fun g => ∑ s ∈ range (j + 1),
      (Nat.stirlingSecond j s : ℝ) * (g.descFactorial s : ℝ) := by
    funext g
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial g j
  rw [hpow, binomExp_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [binomExp_const_mul, binomExp_descFactorial]
  ring

/-- **Lemma 12(i)** (upper form): `Γ_j(r) ≤ E[g^j] / t^j`, with
`E[g^j] = ∑_{s=0}^{j} St(j, s) (r)_s θ^s`. -/
theorem gamma_le_binomMoment_div {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t r j : ℕ) :
    gamma θ t r j ≤ binomMoment θ r j / (t : ℝ) ^ j := by
  rw [gamma_eq_binomExp, ← binomExp_pow_eq_binomMoment, div_eq_inv_mul, ← binomExp_const_mul]
  refine binomExp_mono h0 h1 fun g _ => ?_
  calc leafReveal t g ^ j ≤ ((g : ℝ) / t) ^ j :=
        pow_le_pow_left₀ (leafReveal_nonneg t g) (leafReveal_le_div t g) j
    _ = ((t : ℝ) ^ j)⁻¹ * (g : ℝ) ^ j := by rw [div_pow]; ring

/-! ## The forward difference `Δ_m` -/

/-- `∑_{s=0}^{m} (-1)^{m-s} C(m, s) C(s, j) = [m = j]`. -/
theorem sum_alternating_choose_mul_choose (m j : ℕ) :
    ∑ s ∈ range (m + 1), (-1 : ℝ) ^ (m - s) * (m.choose s : ℝ) * (s.choose j : ℝ) =
      if m = j then 1 else 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x : ℕ => (x.choose j : ℝ)) m 0
  rw [fwdDiff_iter_choose_zero] at h
  rw [h]
  refine sum_congr rfl fun s _ => ?_
  simp [zsmul_eq_mul]

/-- The surjection count (Step 3 of Remark 4):
`∑_{s=0}^{m} (-1)^{m-s} C(m, s) s^ω = m! St(ω, m)`. -/
theorem sum_alternating_choose_mul_pow (ω m : ℕ) :
    ∑ s ∈ range (m + 1), (-1 : ℝ) ^ (m - s) * (m.choose s : ℝ) * (s : ℝ) ^ ω =
      (m.factorial : ℝ) * Nat.stirlingSecond ω m := by
  have hpow : ∀ s : ℕ, (s : ℝ) ^ ω = ∑ j ∈ range (ω + 1),
      (Nat.stirlingSecond ω j : ℝ) * (j.factorial : ℝ) * (s.choose j : ℝ) := by
    intro s
    have := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial s ω
    simp only [Nat.descFactorial_eq_factorial_mul_choose, ← mul_assoc] at this
    exact_mod_cast this
  simp_rw [hpow, mul_sum]
  rw [sum_comm]
  have hinner : ∀ j ∈ range (ω + 1), ∑ s ∈ range (m + 1), (-1 : ℝ) ^ (m - s) * (m.choose s : ℝ) *
      ((Nat.stirlingSecond ω j : ℝ) * (j.factorial : ℝ) * (s.choose j : ℝ)) =
      (Nat.stirlingSecond ω j : ℝ) * (j.factorial : ℝ) * (if m = j then 1 else 0) := by
    intro j _
    rw [← sum_alternating_choose_mul_choose, mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [sum_congr rfl hinner]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with h
  · ring
  · rw [Nat.stirlingSecond_eq_zero_of_lt (by simpa using h)]
    simp

/-- **Eq. (26)** (Remark 4): `Δ_m(x) = ∑_{ω=m}^{k} C(k, ω) m! St(ω, m) x^{k-ω}`. -/
theorem fwdDiffPow_eq_sum (k m : ℕ) (x : ℝ) :
    fwdDiffPow k m x = ∑ ω ∈ Icc m k,
      (k.choose ω : ℝ) * (m.factorial : ℝ) * (Nat.stirlingSecond ω m : ℝ) * x ^ (k - ω) := by
  unfold fwdDiffPow
  have hexp : ∀ s : ℕ, (x + s) ^ k =
      ∑ ω ∈ range (k + 1), (s : ℝ) ^ ω * x ^ (k - ω) * (k.choose ω : ℝ) := by
    intro s; rw [add_comm, add_pow]
  simp_rw [hexp, mul_sum]
  rw [sum_comm]
  have hω : ∀ ω ∈ range (k + 1), ∑ s ∈ range (m + 1), (-1 : ℝ) ^ (m - s) * (m.choose s : ℝ) *
      ((s : ℝ) ^ ω * x ^ (k - ω) * (k.choose ω : ℝ)) =
      (k.choose ω : ℝ) * (m.factorial : ℝ) * (Nat.stirlingSecond ω m : ℝ) * x ^ (k - ω) := by
    intro ω _
    have := sum_alternating_choose_mul_pow ω m
    calc _ = (∑ s ∈ range (m + 1), (-1 : ℝ) ^ (m - s) * (m.choose s : ℝ) * (s : ℝ) ^ ω) *
          (x ^ (k - ω) * (k.choose ω : ℝ)) := by
            rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [this]; ring
  rw [sum_congr rfl hω]
  symm
  refine sum_subset (fun ω hω => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hω).2))
    fun ω hω hω' => ?_
  have : ω < m := by
    by_contra h
    exact hω' (mem_Icc.mpr ⟨not_lt.mp h, Nat.lt_succ_iff.mp (mem_range.mp hω)⟩)
  simp [Nat.stirlingSecond_eq_zero_of_lt this]

/-- **Lemma 12(ii)** (upper form), the identity: replacing every `Γ_{k-ω}(r)` in `A_m` with
`E[g^{k-ω}] / t^{k-ω}` gives `t^{-k} E[Δ_m(g)]`. -/
theorem pullHarmUpper_eq (θ : ℝ) (t k r m : ℕ) :
    pullHarmUpper θ t k r m = ((t : ℝ)⁻¹) ^ k * binomExp θ r (fun g => fwdDiffPow k m g) := by
  simp_rw [fwdDiffPow_eq_sum]
  rw [binomExp_sum, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  have hωk := (mem_Icc.mp hω).2
  rw [binomExp_const_mul, binomExp_pow_eq_binomMoment, div_eq_mul_inv, ← inv_pow]
  have : ((t : ℝ)⁻¹) ^ k = ((t : ℝ)⁻¹) ^ ω * ((t : ℝ)⁻¹) ^ (k - ω) := by
    rw [← pow_add, Nat.add_sub_cancel' hωk]
  rw [this]
  ring

/-- `A_m` is at most its upper form (proof of Lemma 12(ii)). -/
theorem pullHarm_le_pullHarmUpper {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r m : ℕ) :
    pullHarm θ t k r m ≤ pullHarmUpper θ t k r m := by
  unfold pullHarm pullHarmUpper
  refine sum_le_sum fun ω _ => ?_
  gcongr
  exact gamma_le_binomMoment_div h0 h1 t r (k - ω)

/-- **Lemma 12(ii)** (upper form): `A_m ≤ t^{-k} E[Δ_m(g)]`, `g ∼ Bin(r, θ)`. -/
theorem pullHarm_le_binomExp_fwdDiffPow {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r m : ℕ) :
    pullHarm θ t k r m ≤ ((t : ℝ)⁻¹) ^ k * binomExp θ r (fun g => fwdDiffPow k m g) :=
  (pullHarm_le_pullHarmUpper h0 h1 t k r m).trans_eq (pullHarmUpper_eq θ t k r m)

end ShrincsSecurity.ITSR

end
