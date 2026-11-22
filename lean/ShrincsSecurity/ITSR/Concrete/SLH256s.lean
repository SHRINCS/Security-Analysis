module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SLH-DSA-256s

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SLH-DSA-256s:
`h = 64` (`θ = 2^-64`), `k = 22`, `t = 2^14`, `|K| = 2^256`, `r = 2^64`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 22`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 64`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.SLH256s

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^64)`, `j = 0, …, 22`, at SLH-DSA-256s. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9223090567604600834 / 2 ^ 77,
    9222527664893198459 / 2 ^ 90,
    11527104230680627048 / 2 ^ 103,
    17288616236810868606 / 2 ^ 116,
    14981340246086010860 / 2 ^ 128,
    14618801859053563329 / 2 ^ 140,
    15786076181269488402 / 2 ^ 152,
    9313106779217144697 / 2 ^ 163,
    11890050468266271218 / 2 ^ 175,
    16297886567027608360 / 2 ^ 187,
    11916673179870386841 / 2 ^ 198,
    9246949578124883458 / 2 ^ 209,
    15162128336898659345 / 2 ^ 221,
    13083552504214668404 / 2 ^ 232,
    11843809294821606568 / 2 ^ 243,
    11215084481062651879 / 2 ^ 254,
    11080293088130044281 / 2 ^ 265,
    11395985282045164311 / 2 ^ 276,
    12176476987773511956 / 2 ^ 287,
    13491651870536132146 / 2 ^ 298,
    15476106619062725451 / 2 ^ 309,
    9175409785398257654 / 2 ^ 319
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 22, gammaHiQ 64 14 64 64 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^64) ≤ gammaHi j` for `j ≤ 22` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 22, gamma (1 / 2 ^ 64) (2 ^ 14) (2 ^ 64) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 14 64 64 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 64 : ℝ) = ((1 / 2 ^ 64 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 256.01`): `Γ_22(2^64) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 64) (2 ^ 14) (2 ^ 64) 22 ≤ (2 : ℝ) ^ (-256.00 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-25600) (by norm_num)
      (gamma_le 22 le_rfl) (by decide +kernel)

/-- Table 3, SLH-DSA-256s, `q = 1` (exact column): search term `2^-255.01`,
`|K|`-term `2^-507.87`, `T₁ = 2^-507.87` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-192` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) 1 ≤ (2 : ℝ) ^ (-255.00 : ℝ) ∧
    pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) 1 (2 ^ 256) ≤ (2 : ℝ) ^ (-507.86 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) 1 (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-507.86 : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) 1 (2 ^ 256) ≤ (2 : ℝ) ^ (-255.00 : ℝ) ∧
    pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) 1 (2 ^ 256) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) 1 (2 ^ 256) := by
  have hK :
      pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) 1 (2 ^ 256) ≤ (2 : ℝ) ^ (-507.86 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-50786) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-25500) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-50786) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-25500) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 0 256 (by norm_num)) (by norm_num)⟩

/-- Table 3, SLH-DSA-256s, `q = 2^128` (exact column): search term `2^-128.01`,
`|K|`-term `2^-252.87`, `T₁ = 2^-252.87`, `T₂ = 2^-378.86`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-64` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e128 :
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-128.00 : ℝ) ∧
    pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤ (2 : ℝ) ^ (-252.86 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-252.86 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) (2 ^ 256) 2 ≤ (2 : ℝ) ^ (-378.85 : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤ (2 : ℝ) ^ (-128.00 : ℝ) ∧
    pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) (2 ^ 128) (2 ^ 256) := by
  have hK :
      pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤ (2 : ℝ) ^ (-252.86 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-25286) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-12800) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-25286) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-37885) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-12800) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 128 256 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SLH-DSA-256s: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 253.7725`; the paper
prints `q* = 2^253.77`). -/
def qStar : ℕ := 24725743826660167188723527452690293272931634742544682843277079137096867680983

/-- Table 3, SLH-DSA-256s, last row (`q = q* = 2^253.77`, exact column): at a
`q ≥ 2^253.76` the `|K|`-term is at most `1`, the search term is `2^-2.23`,
`T₁ = 2^-1.32`, `T₂ = 2^-1.55`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (253.76 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) qStar (2 ^ 256) ≤ 1 ∧
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) qStar ≤ (2 : ℝ) ^ (-2.22 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) qStar (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-1.31 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) qStar (2 ^ 256) 2 ≤ (2 : ℝ) ^ (-1.54 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 25376 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-222) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-131) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-154) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256s, `log₂ q = 240` (exact column): search term `2^-16.01`,
`T₁ = 2^-28.87`, `R₂ = 2^-42.86`, and the bound of Theorem 2 `2^-16.01`. -/
theorem table5_q2e240 :
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 240) ≤ (2 : ℝ) ^ (-16.00 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 240) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-28.86 : ℝ) ∧
    remainderTwo (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 240) (2 ^ 256) ≤ (2 : ℝ) ^ (-42.85 : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 240) (2 ^ 256) ≤ (2 : ℝ) ^ (-16.00 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1600) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2886) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4285) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1600) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256s, `log₂ q = 248` (exact column): search term `2^-8.01`,
`T₁ = 2^-12.87`, `R₂ = 2^-18.85`, and the bound of Theorem 2 `2^-7.96`. -/
theorem table5_q2e248 :
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 248) ≤ (2 : ℝ) ^ (-8.00 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 248) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-12.86 : ℝ) ∧
    remainderTwo (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 248) (2 ^ 256) ≤ (2 : ℝ) ^ (-18.84 : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 248) (2 ^ 256) ≤ (2 : ℝ) ^ (-7.95 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-800) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1286) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1884) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-795) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256s, `log₂ q = 252` (exact column): search term `2^-4.01`,
`T₁ = 2^-4.87`, `R₂ = 2^-6.64`, and the bound of Theorem 2 `2^-3.23`. -/
theorem table5_q2e252 :
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 252) ≤ (2 : ℝ) ^ (-4.00 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 252) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-4.86 : ℝ) ∧
    remainderTwo (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 252) (2 ^ 256) ≤ (2 : ℝ) ^ (-6.63 : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 252) (2 ^ 256) ≤ (2 : ℝ) ^ (-3.22 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-400) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-486) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-663) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-322) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256s, `log₂ q = 256` (exact column): search term `2^-0.01`,
`T₁ = 2^3.13`, `R₂ = 2^9.50`, and the bound of Theorem 2 `2^9.52`. -/
theorem table5_q2e256 :
    searchTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 256) ≤ (2 : ℝ) ^ (0.00 : ℝ) ∧
    pullTerm (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 256) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (3.14 : ℝ) ∧
    remainderTwo (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 256) (2 ^ 256) ≤ (2 : ℝ) ^ (9.51 : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) (2 ^ 256) (2 ^ 256) ≤ (2 : ℝ) ^ (9.53 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (0) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (314) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (951) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (953) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^253.65` (Table 7 prints `q₁ = 2^253.66`). -/
def qOne : ℕ := 22712157969459946776139698507639822870823044363093170550002678478163636539642

/-- Table 7, SLH-DSA-256s: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^253.65`,
consistent with `q₁ = 2^253.66`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (253.65 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 64) (2 ^ 14) 22 (2 ^ 64) qOne (2 ^ 256) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 25365 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.SLH256s

end
