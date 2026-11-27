module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SLH-DSA-128s

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SLH-DSA-128s:
`h = 63` (`θ = 2^-63`), `k = 14`, `t = 2^12`, `|K| = 2^128`, `r = 2^64`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 14`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 60`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.SLH128s

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^64)`, `j = 0, …, 14`, at SLH-DSA-128s. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9221120603500231612 / 2 ^ 74,
    6913027305719906986 / 2 ^ 84,
    6333474014049602340 / 2 ^ 94,
    6760761461041182036 / 2 ^ 104,
    8156843871029713349 / 2 ^ 114,
    5452477690492629945 / 2 ^ 123,
    7965446842627683611 / 2 ^ 133,
    6291776030887247000 / 2 ^ 142,
    5330608013852672184 / 2 ^ 151,
    4812616668744410924 / 2 ^ 160,
    9210500100957295902 / 2 ^ 170,
    9299683900819891196 / 2 ^ 179,
    4934849527302214981 / 2 ^ 187,
    5486914118476369484 / 2 ^ 196
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 14, gammaHiQ 63 12 64 60 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^64) ≤ gammaHi j` for `j ≤ 14` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 14, gamma (1 / 2 ^ 63) (2 ^ 12) (2 ^ 64) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 12 64 60 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 63 : ℝ) = ((1 / 2 ^ 63 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 133.75`): `Γ_14(2^64) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 63) (2 ^ 12) (2 ^ 64) 14 ≤ (2 : ℝ) ^ (-133.74 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-13374) (by norm_num)
      (gamma_le 14 le_rfl) (by decide +kernel)

/-- Table 3, SLH-DSA-128s, `q = 1` (exact column): search term `2^-132.75`,
`|K|`-term `2^-257.88`, `T₁ = 2^-257.88` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-64` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) 1 ≤ (2 : ℝ) ^ (-132.74 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-257.87 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) 1 (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-257.87 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-132.74 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) 1 (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) 1 (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-257.87 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-25787) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-13274) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-25787) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-13274) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 0 128 (by norm_num)) (by norm_num)⟩

/-- Table 3, SLH-DSA-128s, `q = 2^64` (exact column): search term `2^-69.75`,
`|K|`-term `2^-130.88`, `T₁ = 2^-130.88`, `T₂ = 2^-193.16`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^0` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e64 :
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) ≤ (2 : ℝ) ^ (-69.74 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-130.87 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-130.87 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-193.15 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-69.74 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) (2 ^ 64) (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-130.87 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-13087) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-6974) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-13087) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-19315) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-6974) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 64 128 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SLH-DSA-128s: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 127.5601`; the paper
prints `q* = 2^127.56`). -/
def qStar : ℕ := 250858914120213131334775798725757551888

/-- Table 3, SLH-DSA-128s, last row (`q = q* = 2^127.56`, exact column): at a
`q ≥ 2^127.55` the `|K|`-term is at most `1`, the search term is `2^-6.19`,
`T₁ = 2^-3.76`, `T₂ = 2^-2.48`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (127.55 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) qStar (2 ^ 128) ≤ 1 ∧
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) qStar ≤ (2 : ℝ) ^ (-6.18 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) qStar (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-3.75 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) qStar (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-2.47 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 12755 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-618) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-375) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-247) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128s, `log₂ q = 112` (exact column): search term `2^-21.75`,
`T₁ = 2^-34.88`, `R₂ = 2^-49.16`, and the bound of Theorem 2 `2^-21.75`. -/
theorem table4_q2e112 :
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 112) ≤ (2 : ℝ) ^ (-21.74 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 112) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-34.87 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 112) (2 ^ 128) ≤ (2 : ℝ) ^ (-49.15 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 112) (2 ^ 128) ≤ (2 : ℝ) ^ (-21.74 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-2174) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-3487) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4915) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2174) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128s, `log₂ q = 120` (exact column): search term `2^-13.75`,
`T₁ = 2^-18.88`, `R₂ = 2^-25.15`, and the bound of Theorem 2 `2^-13.71`. -/
theorem table4_q2e120 :
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 120) ≤ (2 : ℝ) ^ (-13.74 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 120) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-18.87 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 120) (2 ^ 128) ≤ (2 : ℝ) ^ (-25.14 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 120) (2 ^ 128) ≤ (2 : ℝ) ^ (-13.70 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1374) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1887) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2514) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1370) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128s, `log₂ q = 124` (exact column): search term `2^-9.75`,
`T₁ = 2^-10.88`, `R₂ = 2^-12.99`, and the bound of Theorem 2 `2^-9.10`. -/
theorem table4_q2e124 :
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 124) ≤ (2 : ℝ) ^ (-9.74 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 124) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-10.87 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 124) (2 ^ 128) ≤ (2 : ℝ) ^ (-12.98 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 124) (2 ^ 128) ≤ (2 : ℝ) ^ (-9.09 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-974) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1087) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1298) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-909) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128s, `log₂ q = 128` (exact column): search term `2^-5.75`,
`T₁ = 2^-2.88`, `R₂ = 2^2.12`, and the bound of Theorem 2 `2^2.17`. -/
theorem table4_q2e128 :
    searchTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-5.74 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 128) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-2.87 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 128) (2 ^ 128) ≤ (2 : ℝ) ^ (2.13 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) (2 ^ 128) (2 ^ 128) ≤ (2 : ℝ) ^ (2.18 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-574) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-287) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (213) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (218) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^127.55` (Table 7 prints `q₁ = 2^127.56`). -/
def qOne : ℕ := 249101272995733428353121985496276903120

/-- Table 7, SLH-DSA-128s: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^127.55`,
consistent with `q₁ = 2^127.56`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (127.55 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 12) 14 (2 ^ 64) qOne (2 ^ 128) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 12755 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.SLH128s

end
