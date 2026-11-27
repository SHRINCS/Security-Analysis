module

public import ShrincsSecurity.ITSR.Analytic.Brackets
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Kernel-checkable certificates for the concrete bounds

`ITSR-Classical.pdf`, Section 7 and Appendix B. This file contains the generic machinery behind the
concrete bounds of `ShrincsSecurity.ITSR.Concrete`:

* `gammaHiQ`: a rational upper endpoint of the bracket of **Lemma 13** for `Γ_j(r)` at
  `θ = 2^-h`, `t = 2^a`, `r = 2^e`, computable by the kernel, and its soundness
  `gamma_le_gammaHiQ`. It truncates the binomial sum at `G` (Lemma 13(i),
  `gamma_le_truncated_add`) and writes the weight as
  `P_g = (1 - θ)^r · C(r, g) · (θ / (1 - θ))^g`; the only factor that is not an exact small
  rational, `(1 - θ)^r = (1 - θ)^(2^e)`, is bounded from above by `e` squarings, each rounded up to
  a multiple of `2^-P` (`sqUpQ`). This replaces the exponential enclosures of Lemma 13(ii)–(iii)
  by a direct enclosure of the same power, which is sharper and needs no series. The leaf factor
  `u_g = 1 - (1 - 1/t)^g` is used exactly.
* `searchTermQ`, `pullTermQ`, `pullSumQ`, `remainderTwoQ`, `mainBoundQ`: the terms of Theorem 2 as
  rational functions of upper bounds `γ j ≥ Γ_j(r)`; every summand of Theorem 2 is nondecreasing in
  each `Γ_j` (all coefficients are nonnegative), so these are upper bounds (`searchTerm_le_Q`,
  `pullTerm_le_Q`, `pullSum_le_Q`, `remainderTwo_le_Q`, `mainBound_le_Q`).
* `le_two_rpow_of_check`: from `X ≤ x` and the rational inequality `x^N ≤ 2^B` (checked by
  `decide +kernel`), `X ≤ 2^(B / N)`.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete

open Finset

/-- `θ = 1 / |ι| = 2^-h` for the paper's instance set `ι = {0,1}^h ≅ Fin (2^h)`. -/
theorem theta_fin_two_pow (h : ℕ) : theta (Fin (2 ^ h)) = 1 / 2 ^ h := by
  simp [theta]

/-- The `|K|`-term of Theorem 2: `∑_{m=1}^{min(k,q,r)} T_m`, so that
`mainBound = searchTerm + pullSum` (`mainBound_eq`). -/
noncomputable def pullSum (θ : ℝ) (t k r q nK : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 (min k (min q r)), pullTerm θ t k r q nK m

theorem mainBound_eq (θ : ℝ) (t k r q nK : ℕ) :
    mainBound θ t k r q nK = searchTerm θ t k r q + pullSum θ t k r q nK := rfl

/-- The `|K|`-term `r · min(q, |K|) / |K|` of Theorem 1, so that
`crudeBound = searchTerm + crudeTerm` (`crudeBound_eq`). -/
noncomputable def crudeTerm (r q nK : ℕ) : ℝ := (r : ℝ) * (min q nK : ℕ) / (nK : ℝ)

theorem crudeBound_eq (θ : ℝ) (t k r q nK : ℕ) :
    crudeBound θ t k r q nK = searchTerm θ t k r q + crudeTerm r q nK := rfl

/-! ## Outward rounding and squaring -/

/-- Round up to a multiple of `2^-P`. -/
def rupQ (x : ℚ) (P : ℕ) : ℚ := ((⌈x * 2 ^ P⌉ : ℤ) : ℚ) / 2 ^ P

/-- Iterated squaring, each step rounded up: an upper bound for `x^(2^s)`. -/
def sqUpQ (P : ℕ) : ℕ → ℚ → ℚ
  | 0, x => x
  | s + 1, x => sqUpQ P s (rupQ (x * x) P)

theorem le_rupQ (x : ℚ) (P : ℕ) : x ≤ rupQ x P := by
  unfold rupQ
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem pow_two_pow_le_sqUpQ (P : ℕ) :
    ∀ (s : ℕ) (x : ℚ) (y : ℝ), 0 ≤ y → y ≤ x → y ^ (2 ^ s) ≤ (sqUpQ P s x : ℝ)
  | 0, x, y, _, h => by simpa [sqUpQ] using h
  | s + 1, x, y, hy, h => by
      simp only [sqUpQ]
      have h2 : y ^ 2 ≤ ((rupQ (x * x) P : ℚ) : ℝ) := by
        calc y ^ 2 ≤ (x : ℝ) * x := by nlinarith
          _ = ((x * x : ℚ) : ℝ) := by push_cast; ring
          _ ≤ _ := by exact_mod_cast le_rupQ (x * x) P
      have := pow_two_pow_le_sqUpQ P s (rupQ (x * x) P) (y ^ 2) (by positivity) h2
      rwa [← pow_mul, ← pow_succ'] at this

/-! ## The bracket of Lemma 13 -/

/-- `C(n, k) = (n)_k / k!`, the form in which the kernel evaluates binomial coefficients of large
`n`. -/
def chooseQ (n k : ℕ) : ℚ := (n.descFactorial k : ℚ) / (k.factorial : ℚ)

@[simp]
theorem cast_chooseQ (n k : ℕ) : ((chooseQ n k : ℚ) : ℝ) = (n.choose k : ℝ) := by
  unfold chooseQ
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- Upper bound for the binomial weight `P_g` at `θ = 2^-h`, `r = 2^e`:
`sqUp((1 - θ), e) · C(r, g) · (θ / (1 - θ))^g`. -/
def weightHiQ (h e P g : ℕ) : ℚ :=
  sqUpQ P e (1 - 1 / 2 ^ h) * chooseQ (2 ^ e) g * ((1 / 2 ^ h) / (1 - 1 / 2 ^ h)) ^ g

/-- `u_g = 1 - (1 - 1/t)^g` at `t = 2^a`, exactly. -/
def revealQ (a g : ℕ) : ℚ := 1 - (1 - 1 / 2 ^ a) ^ g

/-- The tail of Lemma 13(i): `(rθ)^(G+1) / (G+1)! · 1 / (1 - rθ / (G + 2))`. -/
def tailQ (h e G : ℕ) : ℚ :=
  (2 ^ e * (1 / 2 ^ h)) ^ (G + 1) / (G + 1).factorial * (1 / (1 - 2 ^ e * (1 / 2 ^ h) / (G + 2)))

/-- The upper endpoint of the bracket of Lemma 13 for `Γ_j(r)` at `θ = 2^-h`, `t = 2^a`,
`r = 2^e`, truncation point `G` and rounding precision `2^-P`. -/
def gammaHiQ (h a e G P j : ℕ) : ℚ :=
  ∑ g ∈ range (G + 1), weightHiQ h e P g * revealQ a g ^ j + tailQ h e G

theorem binomWeight_le_weightHiQ {h : ℕ} (hh : 1 ≤ h) (e P : ℕ) {g : ℕ} (hg : g ≤ 2 ^ e) :
    binomWeight (1 / 2 ^ h) (2 ^ e) g ≤ (weightHiQ h e P g : ℝ) := by
  have hθ1 : (1 / 2 ^ h : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hy : (0 : ℝ) < 1 - 1 / 2 ^ h := by linarith
  have hA : (1 - 1 / 2 ^ h : ℝ) ^ (2 ^ e) ≤ (sqUpQ P e (1 - 1 / 2 ^ h) : ℝ) :=
    pow_two_pow_le_sqUpQ P e _ _ hy.le (by push_cast; rfl)
  have hc : (0 : ℝ) ≤ ((2 ^ e : ℕ).choose g : ℝ) * ((1 / 2 ^ h) / (1 - 1 / 2 ^ h)) ^ g := by
    positivity
  calc binomWeight (1 / 2 ^ h) (2 ^ e) g
      = (1 - 1 / 2 ^ h) ^ 2 ^ e *
          (((2 ^ e : ℕ).choose g : ℝ) * ((1 / 2 ^ h) / (1 - 1 / 2 ^ h)) ^ g) := by
        unfold binomWeight
        rw [pow_sub₀ _ hy.ne' hg, div_pow]
        ring
    _ ≤ (sqUpQ P e (1 - 1 / 2 ^ h) : ℝ) *
          (((2 ^ e : ℕ).choose g : ℝ) * ((1 / 2 ^ h) / (1 - 1 / 2 ^ h)) ^ g) := by
        gcongr
    _ = (weightHiQ h e P g : ℝ) := by
        unfold weightHiQ
        push_cast
        simp only [cast_chooseQ]
        ring

/-- **Lemma 13(i)**, evaluated: `Γ_j(r) ≤ gammaHiQ` at `θ = 2^-h`, `t = 2^a`, `r = 2^e`, for
`G ≤ r` and `rθ < G + 2`. -/
theorem gamma_le_gammaHiQ {h : ℕ} (hh : 1 ≤ h) (a e G P j : ℕ) (hG : G ≤ 2 ^ e)
    (hrθ : (2 ^ e : ℝ) * (1 / 2 ^ h) < G + 2) :
    gamma (1 / 2 ^ h) (2 ^ a) (2 ^ e) j ≤ (gammaHiQ h a e G P j : ℝ) := by
  have h0 : (0 : ℝ) ≤ 1 / 2 ^ h := by positivity
  have h1 : (1 / 2 ^ h : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hrθ' : ((2 ^ e : ℕ) : ℝ) * (1 / 2 ^ h) < G + 2 := by push_cast; exact hrθ
  refine (gamma_le_truncated_add h0 h1 _ _ j G hrθ').trans ?_
  rw [min_eq_left hG]
  simp only [gammaHiQ, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
  refine add_le_add (sum_le_sum fun g hg => ?_) (le_of_eq ?_)
  · have hu : leafReveal (2 ^ a) g = (revealQ a g : ℝ) := by
      unfold leafReveal revealQ
      push_cast
      ring
    rw [hu]
    refine mul_le_mul_of_nonneg_right
      (binomWeight_le_weightHiQ hh e P (by have := mem_range.mp hg; omega)) ?_
    exact pow_nonneg (hu ▸ leafReveal_nonneg _ g) j
  · unfold tailQ
    push_cast
    ring

/-! ## The terms of Theorem 2 from upper bounds on `Γ_j` -/

section Terms

variable (γ : ℕ → ℚ) (θq : ℚ) (t k r q nK : ℕ)

/-- `A_m` of Eq. (19) with `Γ_j` replaced by `γ j`. -/
def pullHarmQ (m : ℕ) : ℚ :=
  ∑ ω ∈ Icc m k, chooseQ k ω * (m.factorial : ℚ) * (Nat.stirlingSecond ω m : ℚ) *
    ((t : ℚ)⁻¹) ^ ω * γ (k - ω)

/-- `T_m` of Eq. (19) with `Γ_j` replaced by `γ j`. -/
def pullTermQ (m : ℕ) : ℚ :=
  (q + 1 : ℚ) * chooseQ q m * (r.descFactorial m : ℚ) * ((nK : ℚ)⁻¹) ^ m * θq ^ m *
    pullHarmQ γ t k m

/-- The search term `(q + 1) Γ_k(r)` with `Γ_k` replaced by `γ k`. -/
def searchTermQ : ℚ := (q + 1 : ℚ) * γ k

/-- The `|K|`-term `∑_{m=1}^{min(k,q,r)} T_m`, with `Γ_j` replaced by `γ j`. -/
def pullSumQ : ℚ := ∑ m ∈ Icc 1 (min k (min q r)), pullTermQ γ θq t k r q nK m

/-- `R₂ = ∑_{m=2}^{min(k,q,r)} T_m`, with `Γ_j` replaced by `γ j`. -/
def remainderTwoQ : ℚ := ∑ m ∈ Icc 2 (min k (min q r)), pullTermQ γ θq t k r q nK m

/-- The bound of Theorem 2 with `Γ_j` replaced by `γ j`. -/
def mainBoundQ : ℚ := searchTermQ γ k q + pullSumQ γ θq t k r q nK

end Terms

section Bounds

variable {γ : ℕ → ℚ} {θ : ℝ} {θq : ℚ} {t k r : ℕ}

theorem searchTerm_le_Q (hγ : ∀ j ≤ k, gamma θ t r j ≤ γ j) (q : ℕ) :
    searchTerm θ t k r q ≤ (searchTermQ γ k q : ℝ) := by
  unfold searchTerm searchTermQ
  push_cast
  gcongr
  exact hγ k le_rfl

theorem pullHarm_le_Q (hγ : ∀ j ≤ k, gamma θ t r j ≤ γ j) (m : ℕ) :
    pullHarm θ t k r m ≤ (pullHarmQ γ t k m : ℝ) := by
  unfold pullHarm pullHarmQ
  push_cast
  simp only [cast_chooseQ]
  gcongr with ω
  exact hγ _ (Nat.sub_le k ω)

theorem pullTerm_le_Q (hθ : θ = θq) (hθ0 : 0 ≤ θq) (hγ : ∀ j ≤ k, gamma θ t r j ≤ γ j)
    (q nK m : ℕ) : pullTerm θ t k r q nK m ≤ (pullTermQ γ θq t k r q nK m : ℝ) := by
  unfold pullTerm pullTermQ
  have : (0 : ℝ) ≤ θq := by exact_mod_cast hθ0
  push_cast
  simp only [cast_chooseQ]
  rw [hθ]
  gcongr
  exact hθ ▸ pullHarm_le_Q hγ m

theorem pullSum_le_Q (hθ : θ = θq) (hθ0 : 0 ≤ θq) (hγ : ∀ j ≤ k, gamma θ t r j ≤ γ j)
    (q nK : ℕ) : pullSum θ t k r q nK ≤ (pullSumQ γ θq t k r q nK : ℝ) := by
  unfold pullSum pullSumQ
  push_cast
  exact sum_le_sum fun m _ => pullTerm_le_Q hθ hθ0 hγ q nK m

theorem remainderTwo_le_Q (hθ : θ = θq) (hθ0 : 0 ≤ θq) (hγ : ∀ j ≤ k, gamma θ t r j ≤ γ j)
    (q nK : ℕ) : remainderTwo θ t k r q nK ≤ (remainderTwoQ γ θq t k r q nK : ℝ) := by
  unfold remainderTwo remainderTwoQ
  push_cast
  exact sum_le_sum fun m _ => pullTerm_le_Q hθ hθ0 hγ q nK m

theorem mainBound_le_Q (hθ : θ = θq) (hθ0 : 0 ≤ θq) (hγ : ∀ j ≤ k, gamma θ t r j ≤ γ j)
    (q nK : ℕ) : mainBound θ t k r q nK ≤ (mainBoundQ γ θq t k r q nK : ℝ) := by
  rw [mainBound_eq, mainBoundQ]
  push_cast
  exact add_le_add (searchTerm_le_Q hγ q) (pullSum_le_Q hθ hθ0 hγ q nK)

end Bounds

/-! ## From a rational inequality to a power of two -/

/-- If `X ≤ x` and `x^N ≤ 2^B`, then `X ≤ 2^(B / N)`. With `N = 100` this certifies a bound
`X ≤ 2^b` for a `b` given to two decimals. -/
theorem le_two_rpow_of_check {X : ℝ} {x : ℚ} {b : ℝ} {N : ℕ} (hN : 0 < N) (B : ℤ)
    (hb : b = (B : ℝ) / N) (hX : X ≤ x) (hx : x ^ N ≤ (2 : ℚ) ^ B) : X ≤ (2 : ℝ) ^ b := by
  refine hX.trans ?_
  by_contra hlt
  push Not at hlt
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ b := by positivity
  have h1 : ((2 : ℝ) ^ b) ^ N < (x : ℝ) ^ N := pow_lt_pow_left₀ hlt hpos (by omega)
  have h2 : ((2 : ℝ) ^ b) ^ N = (2 : ℝ) ^ B := by
    rw [← Real.rpow_mul_natCast (by norm_num), hb, div_mul_cancel₀ _ (by exact_mod_cast hN.ne'),
      Real.rpow_intCast]
  have h3 : ((x ^ N : ℚ) : ℝ) ≤ (((2 : ℚ) ^ B : ℚ) : ℝ) := by exact_mod_cast hx
  push_cast at h3
  linarith

/-- If `2^B ≤ y^N` for a natural number `y`, then `2^(B / N) ≤ y`. -/
theorem two_rpow_le_of_check {y : ℕ} {b : ℝ} {N : ℕ} (hN : 0 < N) (B : ℕ)
    (hb : b = (B : ℝ) / N) (hy : 2 ^ B ≤ y ^ N) : (2 : ℝ) ^ b ≤ y := by
  by_contra hlt
  push Not at hlt
  have h1 : (y : ℝ) ^ N < ((2 : ℝ) ^ b) ^ N := pow_lt_pow_left₀ hlt (by positivity) (by omega)
  have h2 : ((2 : ℝ) ^ b) ^ N = (2 : ℝ) ^ B := by
    rw [← Real.rpow_mul_natCast (by norm_num), hb, div_mul_cancel₀ _ (by exact_mod_cast hN.ne'),
      Real.rpow_natCast]
  have h3 : ((2 ^ B : ℕ) : ℝ) ≤ ((y ^ N : ℕ) : ℝ) := by exact_mod_cast hy
  push_cast at h3
  linarith

theorem le_one_of_check {X : ℝ} {x : ℚ} (hX : X ≤ x) (hx : x ≤ 1) : X ≤ 1 :=
  hX.trans (by exact_mod_cast hx)

/-- From `X ≤ 2^b`, `Y = 2^c` and `b ≤ d + c`: `X ≤ 2^d · Y`. -/
theorem le_two_rpow_mul_of_le {X Y b d : ℝ} {c : ℤ} (hX : X ≤ (2 : ℝ) ^ b) (hY : Y = (2 : ℝ) ^ c)
    (hbd : b ≤ d + c) : X ≤ (2 : ℝ) ^ d * Y := by
  rw [hY, ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
  exact hX.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbd)

/-- The `|K|`-term of Theorem 1 at powers of two: `2^lr · 2^lq / 2^lK = 2^(lr + lq - lK)` for
`q ≤ |K|`. -/
theorem crudeTerm_two_pow (lr lq lK : ℕ) (h : lq ≤ lK) :
    crudeTerm (2 ^ lr) (2 ^ lq) (2 ^ lK) = (2 : ℝ) ^ ((lr : ℤ) + lq - lK) := by
  unfold crudeTerm
  rw [min_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
  push_cast
  rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
  simp only [zpow_natCast]

end ShrincsSecurity.ITSR.Concrete

end
