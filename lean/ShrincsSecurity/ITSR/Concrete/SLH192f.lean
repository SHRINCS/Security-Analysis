module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SLH-DSA-192f

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SLH-DSA-192f:
`h = 66` (`θ = 2^-66`), `k = 33`, `t = 2^8`, `|K| = 2^192`, `r = 2^64`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 33`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 60`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.SLH192f

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^64)`, `j = 0, …, 33`, at SLH-DSA-192f. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9218869902885064966 / 2 ^ 73,
    11508985268592731047 / 2 ^ 81,
    8322922025976572528 / 2 ^ 88,
    14364228511621733800 / 2 ^ 96,
    14724511734713289532 / 2 ^ 103,
    8731890052787098146 / 2 ^ 109,
    11670181790326599007 / 2 ^ 116,
    8630255847477555545 / 2 ^ 122,
    13958333950305098078 / 2 ^ 129,
    12233486621608845802 / 2 ^ 135,
    11533192964229718352 / 2 ^ 141,
    11621753479997482987 / 2 ^ 147,
    12450763594612130756 / 2 ^ 153,
    14117664203704955975 / 2 ^ 159,
    8438413462156844672 / 2 ^ 164,
    10599475570892358337 / 2 ^ 170,
    13948033715181241695 / 2 ^ 176,
    9588974622875081025 / 2 ^ 181,
    13743611704951072770 / 2 ^ 187,
    10245251446095616777 / 2 ^ 192,
    7929392026273144059 / 2 ^ 197,
    12721302461856681509 / 2 ^ 203,
    10559730084283813305 / 2 ^ 208,
    9057462394785104838 / 2 ^ 213,
    8017084439475223018 / 2 ^ 218,
    14627870168883889700 / 2 ^ 224,
    13738798234389295164 / 2 ^ 229,
    13270677725103089936 / 2 ^ 234,
    13170115398864773984 / 2 ^ 239,
    13416588206400458570 / 2 ^ 244,
    14017812697188684264 / 2 ^ 249,
    15009179821617315889 / 2 ^ 254,
    8228416126760534136 / 2 ^ 258
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 33, gammaHiQ 66 8 64 60 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^64) ≤ gammaHi j` for `j ≤ 33` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 33, gamma (1 / 2 ^ 66) (2 ^ 8) (2 ^ 64) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 8 64 60 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 66 : ℝ) = ((1 / 2 ^ 66 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 195.16`): `Γ_33(2^64) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 66) (2 ^ 8) (2 ^ 64) 33 ≤ (2 : ℝ) ^ (-195.15 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-19515) (by norm_num)
      (gamma_le 33 le_rfl) (by decide +kernel)

/-- Table 3, SLH-DSA-192f, `q = 1` (exact column): search term `2^-194.16`,
`|K|`-term `2^-382.85`, `T₁ = 2^-382.85` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-128` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) 1 ≤ (2 : ℝ) ^ (-194.15 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) 1 (2 ^ 192) ≤ (2 : ℝ) ^ (-382.84 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) 1 (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-382.84 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) 1 (2 ^ 192) ≤ (2 : ℝ) ^ (-194.15 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) 1 (2 ^ 192) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) 1 (2 ^ 192) := by
  have hK :
      pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) 1 (2 ^ 192) ≤ (2 : ℝ) ^ (-382.84 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-38284) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-19415) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-38284) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-19415) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 0 192 (by norm_num)) (by norm_num)⟩

/-- Table 3, SLH-DSA-192f, `q = 2^96` (exact column): search term `2^-99.16`,
`|K|`-term `2^-191.85`, `T₁ = 2^-191.85`, `T₂ = 2^-285.68`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-32` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e96 :
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) ≤ (2 : ℝ) ^ (-99.15 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤ (2 : ℝ) ^ (-191.84 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-191.84 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) (2 ^ 192) 2 ≤ (2 : ℝ) ^ (-285.67 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤ (2 : ℝ) ^ (-99.15 : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) (2 ^ 96) (2 ^ 192) := by
  have hK :
      pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 96) (2 ^ 192) ≤ (2 : ℝ) ^ (-191.84 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-19184) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-9915) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-19184) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-28567) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-9915) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 96 192 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SLH-DSA-192f: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 190.5951`; the paper
prints `q* = 2^190.60`). -/
def qStar : ℕ := 2370477015835305396973165166469963307752598746563068879477

/-- Table 3, SLH-DSA-192f, last row (`q = q* = 2^190.60`, exact column): at a
`q ≥ 2^190.59` the `|K|`-term is at most `1`, the search term is `2^-4.57`,
`T₁ = 2^-2.66`, `T₂ = 2^-1.90`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (190.59 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) qStar (2 ^ 192) ≤ 1 ∧
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) qStar ≤ (2 : ℝ) ^ (-4.56 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) qStar (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-2.65 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) qStar (2 ^ 192) 2 ≤ (2 : ℝ) ^ (-1.89 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 19059 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-456) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-265) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-189) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192f, `log₂ q = 176` (exact column): search term `2^-19.16`,
`T₁ = 2^-31.85`, `R₂ = 2^-45.68`, and the bound of Theorem 2 `2^-19.16`. -/
theorem table5_q2e176 :
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 176) ≤ (2 : ℝ) ^ (-19.15 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 176) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-31.84 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 176) (2 ^ 192) ≤ (2 : ℝ) ^ (-45.67 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 176) (2 ^ 192) ≤ (2 : ℝ) ^ (-19.15 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1915) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-3184) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4567) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1915) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192f, `log₂ q = 184` (exact column): search term `2^-11.16`,
`T₁ = 2^-15.85`, `R₂ = 2^-21.67`, and the bound of Theorem 2 `2^-11.11`. -/
theorem table5_q2e184 :
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 184) ≤ (2 : ℝ) ^ (-11.15 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 184) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-15.84 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 184) (2 ^ 192) ≤ (2 : ℝ) ^ (-21.66 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 184) (2 ^ 192) ≤ (2 : ℝ) ^ (-11.10 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1115) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1584) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2166) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1110) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192f, `log₂ q = 188` (exact column): search term `2^-7.16`,
`T₁ = 2^-7.85`, `R₂ = 2^-9.44`, and the bound of Theorem 2 `2^-6.29`. -/
theorem table5_q2e188 :
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 188) ≤ (2 : ℝ) ^ (-7.15 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 188) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (-7.84 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 188) (2 ^ 192) ≤ (2 : ℝ) ^ (-9.43 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 188) (2 ^ 192) ≤ (2 : ℝ) ^ (-6.28 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-715) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-784) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-943) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-628) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-192f, `log₂ q = 192` (exact column): search term `2^-3.16`,
`T₁ = 2^0.15`, `R₂ = 2^7.01`, and the bound of Theorem 2 `2^7.03`. -/
theorem table5_q2e192 :
    searchTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 192) ≤ (2 : ℝ) ^ (-3.15 : ℝ) ∧
    pullTerm (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 192) (2 ^ 192) 1 ≤ (2 : ℝ) ^ (0.16 : ℝ) ∧
    remainderTwo (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 192) (2 ^ 192) ≤ (2 : ℝ) ^ (7.02 : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) (2 ^ 192) (2 ^ 192) ≤ (2 : ℝ) ^ (7.04 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-315) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (16) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (702) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (704) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^190.57` (Table 7 prints `q₁ = 2^190.58`). -/
def qOne : ℕ := 2329626370354509003404563666139490918295611951942469080765

/-- Table 7, SLH-DSA-192f: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^190.57`,
consistent with `q₁ = 2^190.58`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (190.57 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 66) (2 ^ 8) 33 (2 ^ 64) qOne (2 ^ 192) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 19057 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.SLH192f

end
