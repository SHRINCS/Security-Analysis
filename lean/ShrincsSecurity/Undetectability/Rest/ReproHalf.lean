module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Corollary C.1 and the arithmetic of Corollary C.3

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), Appendix C:

* **Lemma C.3** (lines 5916–5933, adapted from the proof of [LGX25, Theorem 7]): for a halting
  quantum algorithm in the game of Definition C.1 with `R` calls to `Reprogram` and `q̂_j` an upper
  bound on the queries before the `j`-th call, for `e ∈ {1, 1/2}`,
  `|Pr[Repro₀ ⇒ 1]^e - Pr[Repro₁ ⇒ 1]^e| ≤ 4 √(∑_j q̂_j / |X₁|)`.
  The paper does not prove this lemma: it transfers an external proof ([LGX25]) to the game of
  Definition C.1 in prose. Its conclusion is therefore an **explicit hypothesis** of every
  statement below (`lemmaC3`), for the two output probabilities `p₀ = Pr[Repro₀(A) ⇒ 1]`,
  `p₁ = Pr[Repro₁(A) ⇒ 1]` of one algorithm.
* **Remark C.4** (lines 6015–6027): if `q̂_j ≤ q + j - 1` for every `j ∈ [R]`, then
  `∑_j q̂_j ≤ Rq + R(R - 1)/2 < Rq + R(R - 1)/2 + 1` (`remarkC4`).
* **Corollary C.1** (lines 6030–6042): from Lemma C.3 with `e = 1/2`,
  `Pr[Repro₀ ⇒ 1] ≤ 2 Pr[Repro₁ ⇒ 1] + 32 ∑_j q̂_j / |X₁|`, and the same with the games exchanged
  (`corollaryC1`). The proof is the real inequality `(a + ε)² ≤ 2a² + 2ε²`
  (`le_two_mul_add_of_abs_sqrt_sub_le`).
* **Corollary C.3** (lines 6248–6300), the arithmetic: with `S := q_s q_h + q_s(q_s - 1)/2 + 1`
  (`corollaryC3S`), a distinguisher with `R ≤ q_s` calls and `q̂_i ≤ q_h + i - 1` has
  `∑_i q̂_i ≤ S - 1` (`sum_qhat_add_one_le_corollaryC3S`); hence, with `|X₁| = 2ⁿ`,
  `|p₀ - p₁| ≤ 4 √(S/2ⁿ)` from Lemma C.3 with `e = 1` (`corollaryC3_adv_le`), and
  `p₀ ≤ 2p₁ + 32 S/2ⁿ` from Corollary C.1 (`corollaryC3_half`). The `min` with the bound of
  Lemma C.1 ([GHHM21], also quoted and taken as a hypothesis) is `corollaryC3_adv_le_min`, and the
  class-level line with `∑_j q̂_j ≤ Rq` is `corollaryC3_class_adv_le`.

The query bounds `q̂_j` are indexed by `j : Fin R`, so `j` here is the paper's `j - 1`: the
hypothesis `q̂_{j+1} ≤ q + j` is the paper's `q̂_j ≤ q + j - 1`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability.ReproHalf

open Finset

/-! ### Corollary C.1 -/

/-- The step of the proof of Corollary C.1: `(a + ε)² ≤ 2a² + 2ε²`, since the difference is
`(a - ε)² ≥ 0`. -/
lemma add_sq_le_two_mul (a ε : ℝ) : (a + ε) ^ 2 ≤ 2 * a ^ 2 + 2 * ε ^ 2 := by
  nlinarith [sq_nonneg (a - ε)]

/-- If `|√p₀ - √p₁| ≤ ε` then `p₀ ≤ 2 p₁ + 2 ε²`. -/
theorem le_two_mul_add_of_abs_sqrt_sub_le {p₀ p₁ ε : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (h : |√p₀ - √p₁| ≤ ε) : p₀ ≤ 2 * p₁ + 2 * ε ^ 2 := by
  have h₀ : √p₀ ≤ √p₁ + ε := by linarith [(abs_le.mp h).2]
  calc p₀ = √p₀ ^ 2 := (Real.sq_sqrt hp₀).symm
    _ ≤ (√p₁ + ε) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h₀ 2
    _ ≤ 2 * √p₁ ^ 2 + 2 * ε ^ 2 := add_sq_le_two_mul _ _
    _ = 2 * p₁ + 2 * ε ^ 2 := by rw [Real.sq_sqrt hp₁]

/-- **Corollary C.1** (main paper, lines 6030–6042), from the conclusion of Lemma C.3 with
`e = 1/2`, `|√p₀ - √p₁| ≤ 4 √(∑_j q̂_j / |X₁|)`, which is taken as the hypothesis `lemmaC3`:
`p₀ ≤ 2 p₁ + 32 ∑_j q̂_j / |X₁|` and `p₁ ≤ 2 p₀ + 32 ∑_j q̂_j / |X₁|`, where
`p_b = Pr[Repro_b(A) ⇒ 1]`. -/
theorem corollaryC1 {R : ℕ} (qhat : Fin R → ℕ) (cardX₁ : ℕ) {p₀ p₁ : ℝ} (hp₀ : 0 ≤ p₀)
    (hp₁ : 0 ≤ p₁)
    (lemmaC3 : |√p₀ - √p₁| ≤ 4 * √((∑ j, (qhat j : ℝ)) / cardX₁)) :
    p₀ ≤ 2 * p₁ + 32 * ((∑ j, (qhat j : ℝ)) / cardX₁) ∧
      p₁ ≤ 2 * p₀ + 32 * ((∑ j, (qhat j : ℝ)) / cardX₁) := by
  have hQ : 0 ≤ (∑ j, (qhat j : ℝ)) / cardX₁ := by positivity
  have hε : (4 * √((∑ j, (qhat j : ℝ)) / cardX₁)) ^ 2 =
      16 * ((∑ j, (qhat j : ℝ)) / cardX₁) := by
    rw [mul_pow, Real.sq_sqrt hQ]
    norm_num
  constructor
  · have := le_two_mul_add_of_abs_sqrt_sub_le hp₀ hp₁ lemmaC3
    rw [hε] at this
    linarith
  · have := le_two_mul_add_of_abs_sqrt_sub_le hp₁ hp₀ ((abs_sub_comm _ _).trans_le lemmaC3)
    rw [hε] at this
    linarith

/-! ### Remark C.4 -/

/-- `∑_{j < R} (q + j) = Rq + R(R - 1)/2`. -/
lemma sum_fin_add_id (R q : ℕ) : ∑ j : Fin R, (q + (j : ℕ)) = R * q + R * (R - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => q + j) R, sum_add_distrib, sum_range_id, sum_const,
    card_range, smul_eq_mul]

/-- **Remark C.4** (main paper, lines 6015–6027): if `q̂_j ≤ q + j - 1` for every call `j ∈ [R]`
(here `j : Fin R` is the paper's `j - 1`), then `∑_j q̂_j ≤ Rq + R(R - 1)/2`, and so
`∑_j q̂_j < Rq + R(R - 1)/2 + 1`. -/
theorem remarkC4 {R q : ℕ} (qhat : Fin R → ℕ) (hq : ∀ j : Fin R, qhat j ≤ q + j) :
    ∑ j, qhat j ≤ R * q + R * (R - 1) / 2 ∧ ∑ j, qhat j < R * q + R * (R - 1) / 2 + 1 := by
  have h : ∑ j, qhat j ≤ R * q + R * (R - 1) / 2 :=
    (sum_le_sum fun j _ => hq j).trans (sum_fin_add_id R q).le
  exact ⟨h, Nat.lt_succ_of_le h⟩

/-! ### Corollary C.3 -/

/-- `S := q_s q_h + q_s(q_s - 1)/2 + 1` of Corollary C.3 (line 6248). -/
def corollaryC3S (qs qh : ℕ) : ℕ := qs * qh + qs * (qs - 1) / 2 + 1

/-- The count of the proof of Corollary C.3 (lines 6283–6293): a distinguisher with `R ≤ q_s`
calls and `q̂_i ≤ q_h + i - 1` for every call has `∑_i q̂_i ≤ S - 1`. -/
theorem sum_qhat_add_one_le_corollaryC3S {R qs qh : ℕ} (hR : R ≤ qs) (qhat : Fin R → ℕ)
    (hq : ∀ j : Fin R, qhat j ≤ qh + j) : ∑ j, qhat j + 1 ≤ corollaryC3S qs qh := by
  have h₁ := (remarkC4 qhat hq).1
  have h₂ : R * qh + R * (R - 1) / 2 ≤ qs * qh + qs * (qs - 1) / 2 :=
    Nat.add_le_add (Nat.mul_le_mul_right qh hR)
      (Nat.div_le_div_right (Nat.mul_le_mul hR (Nat.sub_le_sub_right hR 1)))
  unfold corollaryC3S
  omega

lemma sum_qhat_le_corollaryC3S {R qs qh : ℕ} (hR : R ≤ qs) (qhat : Fin R → ℕ)
    (hq : ∀ j : Fin R, qhat j ≤ qh + j) :
    (∑ j, (qhat j : ℝ)) ≤ corollaryC3S qs qh := by
  have := sum_qhat_add_one_le_corollaryC3S hR qhat hq
  exact_mod_cast (Nat.le_succ _).trans this

/-- **Corollary C.3**, QROM bound from Lemma C.3 with `e = 1` (main paper, lines 6262–6265):
`Adv^{DI-Repro}(B) = |p₀ - p₁| ≤ 4 √(S / 2ⁿ)` for a distinguisher with `R ≤ q_s` calls and
`q̂_i ≤ q_h + i - 1`, given the conclusion `lemmaC3` of Lemma C.3 (`e = 1`, `|X₁| = 2ⁿ`). -/
theorem corollaryC3_adv_le {R qs qh n : ℕ} (hR : R ≤ qs) (qhat : Fin R → ℕ)
    (hq : ∀ j : Fin R, qhat j ≤ qh + j) {p₀ p₁ : ℝ}
    (lemmaC3 : |p₀ - p₁| ≤ 4 * √((∑ j, (qhat j : ℝ)) / 2 ^ n)) :
    |p₀ - p₁| ≤ 4 * √(corollaryC3S qs qh / 2 ^ n) := by
  refine lemmaC3.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
  exact div_le_div_of_nonneg_right (sum_qhat_le_corollaryC3S hR qhat hq) (by positivity)

/-- **Corollary C.3**, the `min` of the two QROM bounds: the bound `(3/2) q_s √((q_s+q_h+1)/2ⁿ)`
of Lemma C.1 ([GHHM21], quoted; taken as the hypothesis `lemmaC1` with `R = q_s` and
`q = q_s + q_h + 1`) and `4 √(S/2ⁿ)` from Lemma C.3. -/
theorem corollaryC3_adv_le_min {R qs qh n : ℕ} (hR : R ≤ qs) (qhat : Fin R → ℕ)
    (hq : ∀ j : Fin R, qhat j ≤ qh + j) {p₀ p₁ : ℝ}
    (lemmaC1 : |p₀ - p₁| ≤ 3 / 2 * qs * √((qs + qh + 1 : ℕ) / 2 ^ n))
    (lemmaC3 : |p₀ - p₁| ≤ 4 * √((∑ j, (qhat j : ℝ)) / 2 ^ n)) :
    |p₀ - p₁| ≤
      min (3 / 2 * qs * √((qs + qh + 1 : ℕ) / 2 ^ n)) (4 * √(corollaryC3S qs qh / 2 ^ n)) :=
  le_min lemmaC1 (corollaryC3_adv_le hR qhat hq lemmaC3)

/-- **Corollary C.3**, last inequality (main paper, lines 6267–6268): with Corollary C.1,
`Pr[DI-Repro₀(B) ⇒ 1] ≤ 2 Pr[DI-Repro₁(B) ⇒ 1] + 32 S / 2ⁿ`, given the conclusion `lemmaC3` of
Lemma C.3 with `e = 1/2` (`|X₁| = 2ⁿ`). -/
theorem corollaryC3_half {R qs qh n : ℕ} (hR : R ≤ qs) (qhat : Fin R → ℕ)
    (hq : ∀ j : Fin R, qhat j ≤ qh + j) {p₀ p₁ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (lemmaC3 : |√p₀ - √p₁| ≤ 4 * √((∑ j, (qhat j : ℝ)) / 2 ^ n)) :
    p₀ ≤ 2 * p₁ + 32 * (corollaryC3S qs qh / 2 ^ n) := by
  have h := (corollaryC1 qhat (2 ^ n) hp₀ hp₁ (by exact_mod_cast lemmaC3)).1
  have hS : (∑ j, (qhat j : ℝ)) / ((2 ^ n : ℕ) : ℝ) ≤ corollaryC3S qs qh / 2 ^ n := by
    push_cast
    exact div_le_div_of_nonneg_right (sum_qhat_le_corollaryC3S hR qhat hq) (by positivity)
  linarith

/-- **Lemma C.3, class form** (main paper, lines 5934–5936, used in the first QROM line of
Corollary C.3): if the algorithm makes at most `q` queries in every execution, then `q̂_j ≤ q`,
`∑_j q̂_j ≤ Rq`, and the bound is at most `4 √(Rq / |X₁|)`. -/
theorem corollaryC3_class_adv_le {R q n : ℕ} (qhat : Fin R → ℕ) (hq : ∀ j, qhat j ≤ q)
    {p₀ p₁ : ℝ} (lemmaC3 : |p₀ - p₁| ≤ 4 * √((∑ j, (qhat j : ℝ)) / 2 ^ n)) :
    |p₀ - p₁| ≤ 4 * √((R * q : ℕ) / 2 ^ n) := by
  refine lemmaC3.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : ∑ j, qhat j ≤ R * q :=
    (sum_le_sum fun j _ => hq j).trans (by simp)
  exact_mod_cast this

end ShrincsSecurity.Undetectability.ReproHalf
