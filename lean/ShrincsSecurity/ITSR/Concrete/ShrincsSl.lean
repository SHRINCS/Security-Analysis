module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SHRINCS-sl

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SHRINCS-sl:
`h = 45` (`θ = 2^-45`), `k = 10`, `t = 2^13`, `|K| = 2^128`, `r = 2^40`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 10`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 60`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.ShrincsSl

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^40)`, `j = 0, …, 10`, at SHRINCS-sl. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9223354444691101008 / 2 ^ 81,
    9511530947168768747 / 2 ^ 94,
    10096850975392183523 / 2 ^ 107,
    11294704052010983477 / 2 ^ 120,
    6886620315799377633 / 2 ^ 132,
    9491743522166876833 / 2 ^ 145,
    7545550629515090778 / 2 ^ 157,
    6873720206684596735 / 2 ^ 169,
    7008867790693016079 / 2 ^ 181,
    7822208915061017503 / 2 ^ 193
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 10, gammaHiQ 45 13 40 60 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^40) ≤ gammaHi j` for `j ≤ 10` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 10, gamma (1 / 2 ^ 45) (2 ^ 13) (2 ^ 40) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 13 40 60 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 45 : ℝ) = ((1 / 2 ^ 45 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 130.24`): `Γ_10(2^40) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 45) (2 ^ 13) (2 ^ 40) 10 ≤ (2 : ℝ) ^ (-130.23 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-13023) (by norm_num)
      (gamma_le 10 le_rfl) (by decide +kernel)

/-- Table 3, SHRINCS-sl, `q = 1` (exact column): search term `2^-129.24`,
`|K|`-term `2^-255.99`, `T₁ = 2^-255.99` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-88` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 ≤ (2 : ℝ) ^ (-129.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-255.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-255.98 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-129.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 40) 1 (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-255.98 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-25598) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-12923) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-25598) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-12923) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 40 0 128 (by norm_num)) (by norm_num)⟩

/-- Table 3, SHRINCS-sl, `q = 2^40` (exact column): search term `2^-90.24`,
`|K|`-term `2^-176.99`, `T₁ = 2^-176.99`, `T₂ = 2^-265.36`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-48` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e40 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) ≤ (2 : ℝ) ^ (-90.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) (2 ^ 128) ≤ (2 : ℝ) ^ (-176.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-176.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-265.35 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) (2 ^ 128) ≤ (2 : ℝ) ^ (-90.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 40) (2 ^ 40) (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 40) (2 ^ 128) ≤ (2 : ℝ) ^ (-176.98 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-17698) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-9023) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-17698) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-26535) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-9023) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 40 40 128 (by norm_num)) (by norm_num)⟩

/-- Table 3, SHRINCS-sl, `q = 2^64` (exact column): search term `2^-66.24`,
`|K|`-term `2^-128.99`, `T₁ = 2^-128.99`, `T₂ = 2^-193.36`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-24` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e64 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) ≤ (2 : ℝ) ^ (-66.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-128.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-128.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-193.35 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-66.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 40) (2 ^ 64) (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-128.98 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-12898) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-6623) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-12898) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-19335) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-6623) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 40 64 128 (by norm_num)) (by norm_num)⟩

/-- Table 3, SHRINCS-sl, `q = 2^80` (exact column): search term `2^-50.24`,
`|K|`-term `2^-96.99`, `T₁ = 2^-96.99`, `T₂ = 2^-145.36`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-8` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e80 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) ≤ (2 : ℝ) ^ (-50.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) (2 ^ 128) ≤ (2 : ℝ) ^ (-96.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-96.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-145.35 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) (2 ^ 128) ≤ (2 : ℝ) ^ (-50.23 : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 40) (2 ^ 80) (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 80) (2 ^ 128) ≤ (2 : ℝ) ^ (-96.98 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-9698) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-5023) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-9698) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-14535) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-5023) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 40 80 128 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SHRINCS-sl: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 127.9933`; the paper
prints `q* = 2^127.99`). -/
def qStar : ℕ := 338696637449105597350431349957205583443

/-- Table 3, SHRINCS-sl, last row (`q = q* = 2^127.99`, exact column): at a
`q ≥ 2^127.98` the `|K|`-term is at most `1`, the search term is `2^-2.24`,
`T₁ = 2^-1.00`, `T₂ = 2^-1.38`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (127.98 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qStar (2 ^ 128) ≤ 1 ∧
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qStar ≤ (2 : ℝ) ^ (-2.23 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qStar (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-0.99 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qStar (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-1.37 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 12798 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-223) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-99) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-137) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 4, SHRINCS-sl, `log₂ q = 112` (exact column): search term `2^-18.24`,
`T₁ = 2^-32.99`, `R₂ = 2^-49.36`, and the bound of Theorem 2 `2^-18.24`. -/
theorem table4_q2e112 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 112) ≤ (2 : ℝ) ^ (-18.23 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 112) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-32.98 : ℝ) ∧
    remainderTwo (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 112) (2 ^ 128) ≤ (2 : ℝ) ^ (-49.35 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 112) (2 ^ 128) ≤ (2 : ℝ) ^ (-18.23 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1823) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-3298) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4935) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1823) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SHRINCS-sl, `log₂ q = 120` (exact column): search term `2^-10.24`,
`T₁ = 2^-16.99`, `R₂ = 2^-25.36`, and the bound of Theorem 2 `2^-10.22`. -/
theorem table4_q2e120 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 120) ≤ (2 : ℝ) ^ (-10.23 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 120) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-16.98 : ℝ) ∧
    remainderTwo (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 120) (2 ^ 128) ≤ (2 : ℝ) ^ (-25.35 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 120) (2 ^ 128) ≤ (2 : ℝ) ^ (-10.21 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1023) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1698) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2535) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1021) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SHRINCS-sl, `log₂ q = 124` (exact column): search term `2^-6.24`,
`T₁ = 2^-8.99`, `R₂ = 2^-13.33`, and the bound of Theorem 2 `2^-6.03`. -/
theorem table4_q2e124 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 124) ≤ (2 : ℝ) ^ (-6.23 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 124) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-8.98 : ℝ) ∧
    remainderTwo (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 124) (2 ^ 128) ≤ (2 : ℝ) ^ (-13.32 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 124) (2 ^ 128) ≤ (2 : ℝ) ^ (-6.02 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-623) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-898) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1332) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-602) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SHRINCS-sl, `log₂ q = 128` (exact column): search term `2^-2.24`,
`T₁ = 2^-0.99`, `R₂ = 2^-0.98`, and the bound of Theorem 2 `2^0.29`. -/
theorem table4_q2e128 :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 128) ≤ (2 : ℝ) ^ (-2.23 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 128) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-0.98 : ℝ) ∧
    remainderTwo (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 128) (2 ^ 128) ≤ (2 : ℝ) ^ (-0.97 : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (2 ^ 128) (2 ^ 128) ≤ (2 : ℝ) ^ (0.30 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-223) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-98) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-97) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (30) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^127.86` (Table 7 prints `q₁ = 2^127.87`). -/
def qOne : ℕ := 308812766197414273098487046780563680682

/-- Table 7, SHRINCS-sl: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^127.86`,
consistent with `q₁ = 2^127.87`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (127.86 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qOne (2 ^ 128) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 12786 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- `⌊2^122.35⌋` (characterised in `table6_terms`). -/
def qSix : ℕ := 6776726672631791646073157945356366484

/-- Table 6, last row: the summands `T₁, …, T₁₀` of Theorem 2 at SHRINCS-sl and `q = ⌊2^122.35⌋`. -/
theorem table6_terms :
    qSix ^ 100 ≤ 2 ^ 12235 ∧
    2 ^ 12235 < (qSix + 1) ^ 100 ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-12.28 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-18.30 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 3 ≤ (2 : ℝ) ^ (-25.81 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 4 ≤ (2 : ℝ) ^ (-34.91 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 5 ≤ (2 : ℝ) ^ (-45.37 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 6 ≤ (2 : ℝ) ^ (-56.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 7 ≤ (2 : ℝ) ^ (-69.62 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 8 ≤ (2 : ℝ) ^ (-83.27 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 9 ≤ (2 : ℝ) ^ (-97.99 : ℝ) ∧
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) qSix (2 ^ 128) 10 ≤ (2 : ℝ) ^ (-114.14 : ℝ) :=
  ⟨by decide +kernel,
    by decide +kernel,
    le_two_rpow_of_check (N := 100) (by norm_num) (-1228) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1830) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2581) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 3) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-3491) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 4) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4537) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 5) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-5698) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 6) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-6962) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 7) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-8327) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 8) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-9799) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 9) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-11414) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 10) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.ShrincsSl

end
