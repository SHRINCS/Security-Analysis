module

public import ShrincsSecurity.ITSR.Analytic.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Higher-order pulls

`ITSR-Classical.pdf`, Section 6: **Lemma 11** (higher-order pulls), parts (a), (b) and (c).

With `T_m = pullTerm θ t k r q nK m`, `A_m = pullHarm θ t k r m` (Eq. (19)) and
`η = q r θ / |K|` (`pullRate`, Eq. (20)):

* (a) `pullTerm_le_pow_mul_pullTerm_one`: `T_m ≤ m^k η^(m-1) / m! · T_1`;
* (b) `remainderTwo_le_two_pow_mul`: if `η ≤ e^{-(k-1)/2}` then `R₂ ≤ 2^k η T_1`;
* (c) `pullTerm_succ_le` (`T_{m+1} ≤ λ_m η T_m`), `pullTerm_le_prod_harmRatio`
  (`T_m ≤ (∏_{i<m} λ_i) η^(m-1) T_1 ≤ (λη)^(m-1) T_1`) and `remainderTwo_le_geom`
  (`R₂ ≤ λη / (1 - λη) T_1` when `λη < 1`), with `λ_m = harmRatio` and `λ = harmRatioMax`.

Hypotheses. All parts assume `0 ≤ θ ≤ 1` (so that the binomial weights, hence `Γ_j` and `A_m`,
are nonnegative). Part (c) also assumes `t ≥ 1`, which the paper uses implicitly to get `A_m > 0`
(the factor `t^{-k}`; in Lean `(0 : ℝ)⁻¹ = 0`). The ranges of `m` are wider than the paper's
`1 ≤ m ≤ min(k, q, r)`: (a) and the step of (c) hold for every `m ≥ 1`, and the product bound of
(c) for every `1 ≤ m ≤ k`. The paper's `k ≥ 2` in (c) is only needed to make `λ ≥ 0`.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR

open Finset

/-- **`η`** (Eq. (20)): `η = q r θ / |K|`. -/
noncomputable def pullRate (θ : ℝ) (r q nK : ℕ) : ℝ := (q : ℝ) * r * θ / nK

/-- **`λ_m`** (Eq. (21), Lemma 11(c)): `λ_m = A_{m+1} / ((m + 1) A_m)`. -/
noncomputable def harmRatio (θ : ℝ) (t k r m : ℕ) : ℝ :=
  pullHarm θ t k r (m + 1) / ((m + 1 : ℝ) * pullHarm θ t k r m)

/-- **`λ`** (Eq. (21), Lemma 11(c)): `λ = max_{1 ≤ m ≤ k-1} λ_m` (`0` if `k < 2`). -/
noncomputable def harmRatioMax (θ : ℝ) (t k r : ℕ) : ℝ :=
  ⨆ i : Icc 1 (k - 1), harmRatio θ t k r i

variable {θ : ℝ}

theorem pullRate_nonneg (h0 : 0 ≤ θ) (r q nK : ℕ) : 0 ≤ pullRate θ r q nK := by
  unfold pullRate; positivity

/-- `T_1 = (q + 1) η A_1` (Section 6, after Eq. (20)). -/
theorem pullTerm_one_eq_pullRate (θ : ℝ) (t k r q nK : ℕ) :
    pullTerm θ t k r q nK 1 = (q + 1 : ℝ) * pullRate θ r q nK * pullHarm θ t k r 1 := by
  simp only [pullTerm, pullRate, Nat.choose_one_right, Nat.descFactorial_one, pow_one]
  ring

/-- Eq. (22) (proof of Lemma 11(a)): `A_m ≤ m^k A_1` for `m ≥ 1`. -/
theorem pullHarm_le_pow_mul (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    pullHarm θ t k r m ≤ (m : ℝ) ^ k * pullHarm θ t k r 1 := by
  unfold pullHarm
  rw [mul_sum]
  refine (sum_le_sum fun ω hω => ?_).trans
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left hm) fun ω _ _ => ?_)
  · obtain ⟨-, hωk⟩ := mem_Icc.mp hω
    have hg := gamma_nonneg h0 h1 t r (k - ω)
    have hst : ((m.factorial : ℝ) * Nat.stirlingSecond ω m) ≤ (m : ℝ) ^ k := by
      have := factorial_mul_stirlingSecond_le_pow ω m
      have h' : m ^ ω ≤ m ^ k := Nat.pow_le_pow_right hm hωk
      exact_mod_cast this.trans h'
    have hω1 : 1 ≤ ω := hm.trans (mem_Icc.mp hω).1
    obtain ⟨ω', rfl⟩ := Nat.exists_eq_add_of_le' hω1
    rw [Nat.stirlingSecond_one_right]
    calc (k.choose (ω' + 1) : ℝ) * m.factorial * Nat.stirlingSecond (ω' + 1) m *
          (t : ℝ)⁻¹ ^ (ω' + 1) * gamma θ t r (k - (ω' + 1))
        = ((m.factorial : ℝ) * Nat.stirlingSecond (ω' + 1) m) *
          ((k.choose (ω' + 1) : ℝ) * (t : ℝ)⁻¹ ^ (ω' + 1) * gamma θ t r (k - (ω' + 1))) := by
          ring
      _ ≤ (m : ℝ) ^ k *
          ((k.choose (ω' + 1) : ℝ) * (t : ℝ)⁻¹ ^ (ω' + 1) * gamma θ t r (k - (ω' + 1))) := by
          gcongr
      _ = _ := by simp
  · have := gamma_nonneg h0 h1 t r (k - ω)
    positivity

/-- Eq. (23) (proof of Lemma 11(a)): the pull-rate factor `C(q, m) (r)_m |K|^{-m} θ^m` is at most
`η^m / m!`. -/
theorem pullRateFactor_le (h0 : 0 ≤ θ) (r q nK m : ℕ) :
    (q.choose m : ℝ) * (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m * θ ^ m ≤
      pullRate θ r q nK ^ m / m.factorial := by
  have hc : (q.choose m : ℝ) ≤ (q : ℝ) ^ m / m.factorial := Nat.choose_le_pow_div m q
  have hd : (r.descFactorial m : ℝ) ≤ (r : ℝ) ^ m := by
    exact_mod_cast Nat.descFactorial_le_pow r m
  calc (q.choose m : ℝ) * (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m * θ ^ m
      ≤ (q : ℝ) ^ m / m.factorial * (r : ℝ) ^ m * ((nK : ℝ)⁻¹) ^ m * θ ^ m := by gcongr
    _ = pullRate θ r q nK ^ m / m.factorial := by unfold pullRate; ring

/-- **Lemma 11(a)** (higher-order pulls): `T_m ≤ m^k η^(m-1) / m! · T_1`, for every `m ≥ 1`
(the paper states it for `1 ≤ m ≤ min(k, q, r)`). -/
theorem pullTerm_le_pow_mul_pullTerm_one (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r q nK : ℕ) {m : ℕ}
    (hm : 1 ≤ m) :
    pullTerm θ t k r q nK m ≤
      (m : ℝ) ^ k * pullRate θ r q nK ^ (m - 1) / m.factorial * pullTerm θ t k r q nK 1 := by
  have hA := pullHarm_nonneg h0 h1 t k r m
  have hA1 := pullHarm_nonneg h0 h1 t k r 1
  have hη := pullRate_nonneg h0 r q nK
  calc pullTerm θ t k r q nK m
      = (q + 1 : ℝ) * ((q.choose m : ℝ) * (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m * θ ^ m) *
          pullHarm θ t k r m := by unfold pullTerm; ring
    _ ≤ (q + 1 : ℝ) * (pullRate θ r q nK ^ m / m.factorial) *
          ((m : ℝ) ^ k * pullHarm θ t k r 1) := by
        gcongr
        · exact pullRateFactor_le h0 r q nK m
        · exact pullHarm_le_pow_mul h0 h1 t k r hm
    _ = _ := by
        obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
        rw [pullTerm_one_eq_pullRate, Nat.add_sub_cancel, pow_succ]
        ring

/-- A finite geometric tail: if `f m ≤ a ρ^(m-2)` on `[2, N]` with `0 ≤ ρ < 1` and `a ≥ 0`, then
`∑_{m=2}^{N} f m ≤ a / (1 - ρ)`. -/
theorem sum_Icc_two_le_of_geom {f : ℕ → ℝ} {a ρ : ℝ} (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (N : ℕ) (hf : ∀ m ∈ Icc 2 N, f m ≤ a * ρ ^ (m - 2)) :
    ∑ m ∈ Icc 2 N, f m ≤ a / (1 - ρ) := by
  calc ∑ m ∈ Icc 2 N, f m ≤ ∑ m ∈ Icc 2 N, a * ρ ^ (m - 2) := sum_le_sum hf
    _ = a * ∑ i ∈ Ico 0 (N + 1 - 2), ρ ^ i := by
        rw [← mul_sum, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, ← Nat.Ico_zero_eq_range]
        simp
    _ ≤ a * (ρ ^ 0 / (1 - ρ)) := by gcongr; exact geom_sum_Ico_le_of_lt_one hρ0 hρ1
    _ = a / (1 - ρ) := by ring

/-- The ratio step of Lemma 11(b): for `k ≥ 1`, `m ≥ 2` and `η ≤ e^{-(k-1)/2}`,
`c_{m+1} ≤ c_m / 2` where `c_m = m^k η^(m-1) / m!`. -/
theorem pullCoeff_succ_le {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ Real.exp (-(((k : ℝ) - 1) / 2))) {m : ℕ} (hm : 2 ≤ m) :
    ((m + 1 : ℕ) : ℝ) ^ k * η ^ (m + 1 - 1) / (m + 1).factorial ≤
      (m : ℝ) ^ k * η ^ (m - 1) / m.factorial / 2 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' (one_le_two.trans hm)
  have hm2 : (2 : ℝ) ≤ (m' + 1 : ℕ) := by exact_mod_cast hm
  have hk' : ((k' + 1 : ℕ) : ℝ) - 1 = k' := by push_cast; ring
  rw [hk'] at hη
  -- `(3/2)^k' η ≤ 1`
  have h32 : (3 / 2 : ℝ) ^ k' * η ≤ 1 := by
    have he : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    calc (3 / 2 : ℝ) ^ k' * η ≤ Real.exp (1 / 2) ^ k' * Real.exp (-((k' : ℝ) / 2)) := by gcongr
      _ = 1 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
  have hf : ((m' + 1 + 1).factorial : ℝ) = ((m' + 1 + 1 : ℕ) : ℝ) * (m' + 1).factorial := by
    exact_mod_cast Nat.factorial_succ (m' + 1)
  have hcast : ((m' + 1 + 1 : ℕ) : ℝ) = ((m' + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hfpos : (0 : ℝ) < (m' + 1).factorial := by positivity
  rw [hf, hcast]
  simp only [Nat.add_sub_cancel]
  generalize ((m' + 1 : ℕ) : ℝ) = x at hm2 ⊢
  generalize ((m' + 1).factorial : ℝ) = F at hfpos ⊢
  -- `(x + 1)^k' ≤ (3/2)^k' x^k'`
  have hx0 : 0 < x + 1 := by linarith
  have hx1 : x + 1 ≤ 3 / 2 * x := by linarith
  have hpow : (x + 1) ^ k' ≤ (3 / 2) ^ k' * x ^ k' := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hx0.le hx1 k'
  have hxk : 0 ≤ x ^ k' := pow_nonneg (by linarith) k'
  have hkey : 2 * ((x + 1) ^ k' * η) ≤ x * x ^ k' := by
    have : (x + 1) ^ k' * η ≤ x ^ k' := by
      calc (x + 1) ^ k' * η ≤ (3 / 2) ^ k' * x ^ k' * η := mul_le_mul_of_nonneg_right hpow hη0
        _ = ((3 / 2) ^ k' * η) * x ^ k' := by ring
        _ ≤ 1 * x ^ k' := mul_le_mul_of_nonneg_right h32 hxk
        _ = x ^ k' := one_mul _
    nlinarith
  have hc0 : 0 ≤ (x + 1) * F * η ^ m' := mul_nonneg (mul_nonneg hx0.le hfpos.le) (pow_nonneg hη0 _)
  rw [div_div, div_le_div_iff₀ (mul_pos hx0 hfpos) (by linarith)]
  calc (x + 1) ^ (k' + 1) * η ^ (m' + 1) * (F * 2)
      = ((x + 1) * F * η ^ m') * (2 * ((x + 1) ^ k' * η)) := by ring
    _ ≤ ((x + 1) * F * η ^ m') * (x * x ^ k') := mul_le_mul_of_nonneg_left hkey hc0
    _ = x ^ (k' + 1) * η ^ m' * ((x + 1) * F) := by ring

/-- **Lemma 11(b)** (higher-order pulls): if `η ≤ e^{-(k-1)/2}`, then `R₂ ≤ 2^k η T_1`. -/
theorem remainderTwo_le_two_pow_mul (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r q nK : ℕ)
    (hη : pullRate θ r q nK ≤ Real.exp (-(((k : ℝ) - 1) / 2))) :
    remainderTwo θ t k r q nK ≤ 2 ^ k * pullRate θ r q nK * pullTerm θ t k r q nK 1 := by
  set η := pullRate θ r q nK with hηdef
  have hη0 : 0 ≤ η := pullRate_nonneg h0 r q nK
  have hT1 := pullTerm_nonneg h0 h1 t k r q nK 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [remainderTwo, Nat.zero_min, Icc_eq_empty_of_lt (show 0 < 2 by norm_num),
      sum_empty]
    positivity
  -- `c_m ≤ 2^(k-1) η (1/2)^(m-2)` for `m ≥ 2`
  have hc : ∀ m : ℕ, 2 ≤ m →
      (m : ℝ) ^ k * η ^ (m - 1) / m.factorial ≤ 2 ^ (k - 1) * η * (1 / 2) ^ (m - 2) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
      norm_num [pow_succ]
      ring_nf; rfl
    | succ m hm ih =>
      have := pullCoeff_succ_le hk hη0 hη hm
      push_cast at this
      calc ((m + 1 : ℕ) : ℝ) ^ k * η ^ (m + 1 - 1) / (m + 1).factorial
          ≤ (m : ℝ) ^ k * η ^ (m - 1) / m.factorial / 2 := by push_cast; exact this
        _ ≤ 2 ^ (k - 1) * η * (1 / 2) ^ (m - 2) / 2 := by gcongr
        _ = 2 ^ (k - 1) * η * (1 / 2) ^ (m + 1 - 2) := by
          rw [show m + 1 - 2 = m - 2 + 1 by omega, pow_succ]; ring
  have hmain := sum_Icc_two_le_of_geom (f := fun m => pullTerm θ t k r q nK m)
    (a := 2 ^ (k - 1) * η * pullTerm θ t k r q nK 1) (ρ := 1 / 2) (by positivity) (by norm_num)
    (by norm_num) (min k (min q r)) fun m hm => by
      have hm2 := (mem_Icc.mp hm).1
      calc pullTerm θ t k r q nK m
          ≤ (m : ℝ) ^ k * η ^ (m - 1) / m.factorial * pullTerm θ t k r q nK 1 :=
            pullTerm_le_pow_mul_pullTerm_one h0 h1 t k r q nK (one_le_two.trans hm2)
        _ ≤ 2 ^ (k - 1) * η * (1 / 2) ^ (m - 2) * pullTerm θ t k r q nK 1 := by
            gcongr; exact hc m hm2
        _ = _ := by ring
  refine hmain.trans (le_of_eq ?_)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-! ## Part (c) -/

theorem harmRatio_nonneg (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r m : ℕ) : 0 ≤ harmRatio θ t k r m := by
  unfold harmRatio
  have := pullHarm_nonneg h0 h1 t k r (m + 1)
  have := pullHarm_nonneg h0 h1 t k r m
  positivity

/-- `A_{m+1} = 0` for `m ≥ k`. -/
theorem pullHarm_eq_zero_of_lt (θ : ℝ) (t k r : ℕ) {m : ℕ} (hm : k < m) :
    pullHarm θ t k r m = 0 := by
  simp [pullHarm, Icc_eq_empty_of_lt hm]

/-- **Lemma 11(c)**, step: `T_{m+1} ≤ λ_m η T_m`, for every `m ≥ 1` (the paper states it for
`1 ≤ m < min(k, q, r)`). Requires `t ≥ 1` (so that `A_m > 0` for `m ≤ k`). -/
theorem pullTerm_succ_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℕ} (ht : 1 ≤ t) (k r q nK : ℕ) {m : ℕ}
    (hm : 1 ≤ m) :
    pullTerm θ t k r q nK (m + 1) ≤
      harmRatio θ t k r m * pullRate θ r q nK * pullTerm θ t k r q nK m := by
  have hlam := harmRatio_nonneg h0 h1 t k r m
  have hη := pullRate_nonneg h0 r q nK
  have hTm := pullTerm_nonneg h0 h1 t k r q nK m
  rcases lt_or_ge m k with hmk | hmk
  swap
  · have : pullTerm θ t k r q nK (m + 1) = 0 := by
      simp [pullTerm, pullHarm_eq_zero_of_lt θ t k r (show k < m + 1 by omega)]
    rw [this]; positivity
  have hA := pullHarm_pos h0 h1 (r := r) ht hm hmk.le
  have hA1 := pullHarm_nonneg h0 h1 t k r (m + 1)
  have hc : (q.choose (m + 1) : ℝ) = q.choose m * ((q - m : ℕ) : ℝ) / (m + 1) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast Nat.choose_succ_right_eq q m
  have hd : (r.descFactorial (m + 1) : ℝ) = ((r - m : ℕ) : ℝ) * r.descFactorial m := by
    exact_mod_cast Nat.descFactorial_succ r m
  have hqm : ((q - m : ℕ) : ℝ) ≤ q := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hrm : ((r - m : ℕ) : ℝ) ≤ r := Nat.cast_le.mpr (Nat.sub_le _ _)
  set X : ℝ := (q + 1 : ℝ) * (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m * θ ^ m *
    pullHarm θ t k r (m + 1) * θ * (nK : ℝ)⁻¹ * q.choose m / (m + 1) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have e1 : pullTerm θ t k r q nK (m + 1) = X * (((q - m : ℕ) : ℝ) * ((r - m : ℕ) : ℝ)) := by
    simp only [pullTerm, hc, hd, hX, pow_succ]
    ring
  have hcancel : harmRatio θ t k r m * pullHarm θ t k r m =
      pullHarm θ t k r (m + 1) / (m + 1) := by
    unfold harmRatio; field_simp
  have e2 : harmRatio θ t k r m * pullRate θ r q nK * pullTerm θ t k r q nK m =
      X * ((q : ℝ) * r) := by
    calc harmRatio θ t k r m * pullRate θ r q nK * pullTerm θ t k r q nK m
        = (harmRatio θ t k r m * pullHarm θ t k r m) * ((q : ℝ) * r * θ / nK) *
            ((q + 1 : ℝ) * (q.choose m : ℝ) * (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m *
              θ ^ m) := by
          simp only [pullTerm, pullRate]; ring
      _ = X * ((q : ℝ) * r) := by rw [hcancel, hX]; ring
  rw [e1, e2]
  gcongr

/-- **Lemma 11(c)**, product form: `T_m ≤ (∏_{i=1}^{m-1} λ_i) η^(m-1) T_1` for every `m ≥ 1`. -/
theorem pullTerm_le_prod_harmRatio (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    (k r q nK : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    pullTerm θ t k r q nK m ≤
      (∏ i ∈ Ico 1 m, harmRatio θ t k r i) * pullRate θ r q nK ^ (m - 1) *
        pullTerm θ t k r q nK 1 := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hlam := harmRatio_nonneg h0 h1 t k r n
    have hη := pullRate_nonneg h0 r q nK
    calc pullTerm θ t k r q nK (n + 1)
        ≤ harmRatio θ t k r n * pullRate θ r q nK * pullTerm θ t k r q nK n :=
          pullTerm_succ_le h0 h1 ht k r q nK hn
      _ ≤ harmRatio θ t k r n * pullRate θ r q nK *
            ((∏ i ∈ Ico 1 n, harmRatio θ t k r i) * pullRate θ r q nK ^ (n - 1) *
              pullTerm θ t k r q nK 1) := by gcongr
      _ = _ := by
          obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [prod_Ico_succ_top hn, Nat.add_sub_cancel, Nat.add_sub_cancel, pow_succ]
          ring

/-- **Lemma 11(c)**, geometric form, for any common upper bound `L` of the `λ_i`, `1 ≤ i ≤ k-1`:
`T_m ≤ (L η)^(m-1) T_1` for `1 ≤ m ≤ k`. -/
theorem pullTerm_le_pow_of_harmRatio_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    (k r q nK : ℕ) {L : ℝ} (hL : ∀ i ∈ Icc 1 (k - 1), harmRatio θ t k r i ≤ L) {m : ℕ}
    (hm : 1 ≤ m) (hmk : m ≤ k) :
    pullTerm θ t k r q nK m ≤ (L * pullRate θ r q nK) ^ (m - 1) * pullTerm θ t k r q nK 1 := by
  have hη := pullRate_nonneg h0 r q nK
  have hT1 := pullTerm_nonneg h0 h1 t k r q nK 1
  have hprod : ∏ i ∈ Ico 1 m, harmRatio θ t k r i ≤ L ^ (m - 1) := by
    calc ∏ i ∈ Ico 1 m, harmRatio θ t k r i ≤ ∏ _i ∈ Ico 1 m, L :=
          prod_le_prod₀ (fun i _ => harmRatio_nonneg h0 h1 t k r i) fun i hi => by
            obtain ⟨hi1, hi2⟩ := mem_Ico.mp hi
            exact hL i (mem_Icc.mpr ⟨hi1, by omega⟩)
      _ = L ^ (m - 1) := by rw [prod_const, Nat.card_Ico]
  calc pullTerm θ t k r q nK m
      ≤ (∏ i ∈ Ico 1 m, harmRatio θ t k r i) * pullRate θ r q nK ^ (m - 1) *
          pullTerm θ t k r q nK 1 := pullTerm_le_prod_harmRatio h0 h1 ht k r q nK hm
    _ ≤ L ^ (m - 1) * pullRate θ r q nK ^ (m - 1) * pullTerm θ t k r q nK 1 := by gcongr
    _ = _ := by rw [mul_pow]

/-- **Lemma 11(c)**, tail, for any nonnegative common upper bound `L` of the `λ_i`: if `L η < 1`,
then `R₂ ≤ L η / (1 - L η) · T_1`. -/
theorem remainderTwo_le_geom_of_harmRatio_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    (k r q nK : ℕ) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ i ∈ Icc 1 (k - 1), harmRatio θ t k r i ≤ L)
    (hLη : L * pullRate θ r q nK < 1) :
    remainderTwo θ t k r q nK ≤
      L * pullRate θ r q nK / (1 - L * pullRate θ r q nK) * pullTerm θ t k r q nK 1 := by
  have hη := pullRate_nonneg h0 r q nK
  have hT1 := pullTerm_nonneg h0 h1 t k r q nK 1
  have hmain := sum_Icc_two_le_of_geom (f := fun m => pullTerm θ t k r q nK m)
    (a := L * pullRate θ r q nK * pullTerm θ t k r q nK 1) (ρ := L * pullRate θ r q nK)
    (by positivity) (by positivity) hLη (min k (min q r)) fun m hm => by
      obtain ⟨hm2, hmN⟩ := mem_Icc.mp hm
      calc pullTerm θ t k r q nK m
          ≤ (L * pullRate θ r q nK) ^ (m - 1) * pullTerm θ t k r q nK 1 :=
            pullTerm_le_pow_of_harmRatio_le h0 h1 ht k r q nK hL (by omega)
              (hmN.trans (min_le_left _ _))
        _ = _ := by rw [show m - 1 = m - 2 + 1 by omega, pow_succ]; ring
  refine hmain.trans (le_of_eq ?_)
  ring

/-- `λ_i ≤ λ` for `1 ≤ i ≤ k - 1`. -/
theorem harmRatio_le_harmRatioMax (θ : ℝ) (t k r : ℕ) {i : ℕ} (hi : i ∈ Icc 1 (k - 1)) :
    harmRatio θ t k r i ≤ harmRatioMax θ t k r :=
  le_ciSup (f := fun i : Icc 1 (k - 1) => harmRatio θ t k r i) (Set.finite_range _).bddAbove
    ⟨i, hi⟩

/-- `λ ≥ 0` for `k ≥ 2`. -/
theorem harmRatioMax_nonneg (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t : ℕ) {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    0 ≤ harmRatioMax θ t k r :=
  (harmRatio_nonneg h0 h1 t k r 1).trans
    (harmRatio_le_harmRatioMax θ t k r (mem_Icc.mpr ⟨le_rfl, by omega⟩))

/-- **Lemma 11(c)** (higher-order pulls), with `λ = max_{1 ≤ m ≤ k-1} λ_m`:
`T_m ≤ (λ η)^(m-1) T_1` for `1 ≤ m ≤ k` (in particular for `1 ≤ m ≤ min(k, q, r)`). -/
theorem pullTerm_le_pow_harmRatioMax (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℕ} (ht : 1 ≤ t)
    (k r q nK : ℕ) {m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) :
    pullTerm θ t k r q nK m ≤
      (harmRatioMax θ t k r * pullRate θ r q nK) ^ (m - 1) * pullTerm θ t k r q nK 1 :=
  pullTerm_le_pow_of_harmRatio_le h0 h1 ht k r q nK
    (fun _ hi => harmRatio_le_harmRatioMax θ t k r hi) hm hmk

/-- **Lemma 11(c)** (higher-order pulls), tail: for `k ≥ 2` and `λ η < 1`,
`R₂ ≤ λ η / (1 - λ η) · T_1`. -/
theorem remainderTwo_le_geom (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t : ℕ} (ht : 1 ≤ t) {k : ℕ}
    (hk : 2 ≤ k) (r q nK : ℕ) (hlη : harmRatioMax θ t k r * pullRate θ r q nK < 1) :
    remainderTwo θ t k r q nK ≤
      harmRatioMax θ t k r * pullRate θ r q nK / (1 - harmRatioMax θ t k r * pullRate θ r q nK) *
        pullTerm θ t k r q nK 1 :=
  remainderTwo_le_geom_of_harmRatio_le h0 h1 ht k r q nK (harmRatioMax_nonneg h0 h1 t hk r)
    (fun _ hi => harmRatio_le_harmRatioMax θ t k r hi) hlη

end ShrincsSecurity.ITSR

end
