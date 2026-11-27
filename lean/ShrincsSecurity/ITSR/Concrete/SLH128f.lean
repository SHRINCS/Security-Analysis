module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SLH-DSA-128f

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SLH-DSA-128f:
`h = 66` (`θ = 2^-66`), `k = 33`, `t = 2^6`, `|K| = 2^128`, `r = 2^64`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 33`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 60`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.SLH128f

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^64)`, `j = 0, …, 33`, at SLH-DSA-128f. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9205381071704744853 / 2 ^ 71,
    11448730776280881501 / 2 ^ 77,
    16434356888653069061 / 2 ^ 83,
    14014445910106000808 / 2 ^ 88,
    14143569178771368697 / 2 ^ 93,
    16465192201622212446 / 2 ^ 98,
    10769073105437461872 / 2 ^ 102,
    15543813737770102361 / 2 ^ 107,
    12231347295583719937 / 2 ^ 111,
    10401702144273078371 / 2 ^ 115,
    9489388015484011313 / 2 ^ 119,
    9228783357036295186 / 2 ^ 123,
    9517466456410006116 / 2 ^ 127,
    10361597322386839935 / 2 ^ 131,
    11863086002033634704 / 2 ^ 135,
    14235971113213017948 / 2 ^ 139,
    8926702208437791396 / 2 ^ 142,
    11669172003211348253 / 2 ^ 146,
    15863423062842437958 / 2 ^ 150,
    11189953532183232054 / 2 ^ 153,
    16352312521431626215 / 2 ^ 157,
    12355217914508543119 / 2 ^ 160,
    9638254319093026465 / 2 ^ 163,
    15503749925176242084 / 2 ^ 167,
    12839244970813345508 / 2 ^ 170,
    10934902090233324754 / 2 ^ 173,
    9567108051063500488 / 2 ^ 176,
    8589928817731468211 / 2 ^ 179,
    15814507017652279944 / 2 ^ 183,
    14911840681956578052 / 2 ^ 186,
    14390770737460411119 / 2 ^ 189,
    14202825809583906536 / 2 ^ 192,
    14324681022342415488 / 2 ^ 195
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 33, gammaHiQ 66 6 64 60 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^64) ≤ gammaHi j` for `j ≤ 33` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 33, gamma (1 / 2 ^ 66) (2 ^ 6) (2 ^ 64) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 6 64 60 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 66 : ℝ) = ((1 / 2 ^ 66 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 131.36`): `Γ_33(2^64) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 66) (2 ^ 6) (2 ^ 64) 33 ≤ (2 : ℝ) ^ (-131.35 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-13135) (by norm_num)
      (gamma_le 33 le_rfl) (by decide +kernel)

/-- Table 3, SLH-DSA-128f, `q = 1` (exact column): search term `2^-130.36`,
`|K|`-term `2^-254.60`, `T₁ = 2^-254.60` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-64` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) 1 ≤ (2 : ℝ) ^ (-130.35 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-254.59 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) 1 (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-254.59 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-130.35 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) 1 (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) 1 (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) 1 (2 ^ 128) ≤ (2 : ℝ) ^ (-254.59 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-25459) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-13035) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-25459) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-13035) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 0 128 (by norm_num)) (by norm_num)⟩

/-- Table 3, SLH-DSA-128f, `q = 2^64` (exact column): search term `2^-67.36`,
`|K|`-term `2^-127.60`, `T₁ = 2^-127.60`, `T₂ = 2^-189.06`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^0` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e64 :
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) ≤ (2 : ℝ) ^ (-67.35 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-127.59 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-127.59 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-189.05 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-67.35 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) (2 ^ 64) (2 ^ 128) := by
  have hK :
      pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-127.59 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-12759) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-6735) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-12759) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-18905) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-6735) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 64 128 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SLH-DSA-128f: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 126.3753`; the paper
prints `q* = 2^126.38`). -/
def qStar : ℕ := 110343393114078432379052033710150019576

/-- Table 3, SLH-DSA-128f, last row (`q = q* = 2^126.38`, exact column): at a
`q ≥ 2^126.37` the `|K|`-term is at most `1`, the search term is `2^-4.99`,
`T₁ = 2^-2.85`, `T₂ = 2^-1.94`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (126.37 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) qStar (2 ^ 128) ≤ 1 ∧
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) qStar ≤ (2 : ℝ) ^ (-4.98 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) qStar (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-2.84 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) qStar (2 ^ 128) 2 ≤ (2 : ℝ) ^ (-1.93 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 12637 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-498) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-284) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-193) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128f, `log₂ q = 112` (exact column): search term `2^-19.36`,
`T₁ = 2^-31.60`, `R₂ = 2^-45.06`, and the bound of Theorem 2 `2^-19.36`. -/
theorem table4_q2e112 :
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 112) ≤ (2 : ℝ) ^ (-19.35 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 112) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-31.59 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 112) (2 ^ 128) ≤ (2 : ℝ) ^ (-45.05 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 112) (2 ^ 128) ≤ (2 : ℝ) ^ (-19.35 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1935) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-3159) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4505) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1935) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128f, `log₂ q = 120` (exact column): search term `2^-11.36`,
`T₁ = 2^-15.60`, `R₂ = 2^-21.04`, and the bound of Theorem 2 `2^-11.29`. -/
theorem table4_q2e120 :
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 120) ≤ (2 : ℝ) ^ (-11.35 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 120) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-15.59 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 120) (2 ^ 128) ≤ (2 : ℝ) ^ (-21.03 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 120) (2 ^ 128) ≤ (2 : ℝ) ^ (-11.28 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1135) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1559) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2103) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1128) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128f, `log₂ q = 124` (exact column): search term `2^-7.36`,
`T₁ = 2^-7.60`, `R₂ = 2^-8.75`, and the bound of Theorem 2 `2^-6.21`. -/
theorem table4_q2e124 :
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 124) ≤ (2 : ℝ) ^ (-7.35 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 124) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (-7.59 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 124) (2 ^ 128) ≤ (2 : ℝ) ^ (-8.74 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 124) (2 ^ 128) ≤ (2 : ℝ) ^ (-6.20 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-735) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-759) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-874) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-620) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 4, SLH-DSA-128f, `log₂ q = 128` (exact column): search term `2^-3.36`,
`T₁ = 2^0.40`, `R₂ = 2^8.44`, and the bound of Theorem 2 `2^8.44`. -/
theorem table4_q2e128 :
    searchTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-3.35 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 128) (2 ^ 128) 1 ≤ (2 : ℝ) ^ (0.41 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 128) (2 ^ 128) ≤ (2 : ℝ) ^ (8.45 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) (2 ^ 128) (2 ^ 128) ≤ (2 : ℝ) ^ (8.45 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-335) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (41) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (845) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (845) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^126.35` (Table 7 prints `q₁ = 2^126.36`). -/
def qOne : ℕ := 108427626762108666337170527125701863756

/-- Table 7, SLH-DSA-128f: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^126.35`,
consistent with `q₁ = 2^126.36`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (126.35 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 6) 33 (2 ^ 64) qOne (2 ^ 128) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 12635 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.SLH128f

end
