module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SLH-DSA-192s

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SLH-DSA-192s:
`h = 63` (`θ = 2^-63`), `k = 17`, `t = 2^14`, `|K| = 2^192`, `r = 2^64`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 17`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 64`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.SLH192s

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^64)`, `j = 0, …, 17`, at SLH-DSA-192s. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9222809109807147708 / 2 ^ 76,
    13832806490240451974 / 2 ^ 89,
    12678337334174560282 / 2 ^ 101,
    13540496242697635209 / 2 ^ 113,
    8173107418766343351 / 2 ^ 124,
    10934034505100574265 / 2 ^ 136,
    7992672338590057109 / 2 ^ 147,
    12636971312148937357 / 2 ^ 159,
    10716078878833679791 / 2 ^ 170,
    9684127078014015293 / 2 ^ 181,
    9276461969585736972 / 2 ^ 192,
    9376624267755927900 / 2 ^ 203,
    9962998083362881259 / 2 ^ 214,
    11091242979315975734 / 2 ^ 225,
    12899382708715624895 / 2 ^ 236,
    7816792744703414124 / 2 ^ 246,
    9850222607403886429 / 2 ^ 257
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 17, gammaHiQ 63 14 64 64 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^64) ≤ gammaHi j` for `j ≤ 17` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 17, gamma (1 / 2 ^ 63) (2 ^ 14) (2 ^ 64) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 14 64 64 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 63 : ℝ) = ((1 / 2 ^ 63 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 193.91`): `Γ_17(2^64) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 63) (2 ^ 14) (2 ^ 64) 17 ≤ (2 : ℝ) ^ (-193.90 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-19390) (by norm_num)
      (gamma_le 17 le_rfl) (by decide +kernel)

/-- Table 3, SLH-DSA-192s, `q = 1` (exact column): search term `2^-192.91`,
`|K|`-term `2^-381.82`, `T₁ = 2^-381.82` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-128` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) 1 ≤ (2 : ℝ) ^ (-192.90 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) 1 (2 ^ 192) ≤ (2 : ℝ) ^ (-381.81 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) 1 (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-381.81 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) 1 (2 ^ 192) ≤ (2 : ℝ) ^ (-192.90 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) 1 (2 ^ 192) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) 1 (2 ^ 192) := by
  have hK :
      pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) 1 (2 ^ 192) ≤ (2 : ℝ) ^ (-381.81 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-38181) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-19290) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-38181) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-19290) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 0 192 (by norm_num)) (by norm_num)⟩

/-- Table 3, SLH-DSA-192s, `q = 2^96` (exact column): search term `2^-97.91`,
`|K|`-term `2^-190.82`, `T₁ = 2^-190.82`, `T₂ = 2^-284.88`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-32` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e96 :
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) ≤ (2 : ℝ) ^ (-97.90 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤ (2 : ℝ) ^ (-190.81 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-190.81 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) (2 ^ 192) 2 ≤ (2 : ℝ) ^ (-284.87 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤ (2 : ℝ) ^ (-97.90 : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) (2 ^ 96) (2 ^ 192) := by
  have hK :
      pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤ (2 : ℝ) ^ (-190.81 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-19081) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-9790) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-19081) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-28487) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-9790) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 96 192 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SLH-DSA-192s: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 190.4086`; the paper
prints `q* = 2^190.41`). -/
def qStar : ℕ := 2083122006244628831443960641356216958033203030074549596457

/-- Table 3, SLH-DSA-192s, last row (`q = q* = 2^190.41`, exact column): at a
`q ≥ 2^190.40` the `|K|`-term is at most `1`, the search term is `2^-3.50`,
`T₁ = 2^-2.00`, `T₂ = 2^-1.65`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (190.40 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) qStar (2 ^ 192) ≤ 1 ∧
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) qStar ≤ (2 : ℝ) ^ (-3.49 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) qStar (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-1.99 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) qStar (2 ^ 192) 2 ≤ (2 : ℝ) ^ (-1.64 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 19040 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-349) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-199) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-164) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192s, `log₂ q = 176` (exact column): search term `2^-17.91`,
`T₁ = 2^-30.82`, `R₂ = 2^-44.88`, and the bound of Theorem 2 `2^-17.90`. -/
theorem table5_q2e176 :
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 176) ≤ (2 : ℝ) ^ (-17.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 176) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-30.81 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 176) (2 ^ 192) ≤ (2 : ℝ) ^ (-44.87 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 176) (2 ^ 192) ≤ (2 : ℝ) ^ (-17.89 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1790) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-3081) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4487) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1789) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192s, `log₂ q = 184` (exact column): search term `2^-9.91`,
`T₁ = 2^-14.82`, `R₂ = 2^-20.86`, and the bound of Theorem 2 `2^-9.86`. -/
theorem table5_q2e184 :
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 184) ≤ (2 : ℝ) ^ (-9.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 184) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-14.81 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 184) (2 ^ 192) ≤ (2 : ℝ) ^ (-20.85 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 184) (2 ^ 192) ≤ (2 : ℝ) ^ (-9.85 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-990) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1481) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2085) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-985) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192s, `log₂ q = 188` (exact column): search term `2^-5.91`,
`T₁ = 2^-6.82`, `R₂ = 2^-8.66`, and the bound of Theorem 2 `2^-5.16`. -/
theorem table5_q2e188 :
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 188) ≤ (2 : ℝ) ^ (-5.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 188) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-6.81 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 188) (2 ^ 192) ≤ (2 : ℝ) ^ (-8.65 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 188) (2 ^ 192) ≤ (2 : ℝ) ^ (-5.15 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-590) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-681) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-865) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-515) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192s, `log₂ q = 192` (exact column): search term `2^-1.91`,
`T₁ = 2^1.18`, `R₂ = 2^7.24`, and the bound of Theorem 2 `2^7.26`. -/
theorem table5_q2e192 :
    searchTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 192) ≤ (2 : ℝ) ^ (-1.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 192) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (1.19 : ℝ) ∧
    remainderTwo (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 192) (2 ^ 192) ≤ (2 : ℝ) ^ (7.25 : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) (2 ^ 192) (2 ^ 192) ≤ (2 : ℝ) ^ (7.27 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-190) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (119) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (725) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (727) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^190.36` (Table 7 prints `q₁ = 2^190.37`). -/
def qOne : ℕ := 2014048732208078579944214954141737841382197578609962008794

/-- Table 7, SLH-DSA-192s: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^190.36`,
consistent with `q₁ = 2^190.37`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (190.36 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 63) (2 ^ 14) 17 (2 ^ 64) qOne (2 ^ 192) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 19036 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.SLH192s

end
