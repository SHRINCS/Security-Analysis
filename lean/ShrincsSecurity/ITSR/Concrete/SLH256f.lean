module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at SLH-DSA-256f

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at SLH-DSA-256f:
`h = 68` (`θ = 2^-68`), `k = 35`, `t = 2^9`, `|K| = 2^256`, `r = 2^64`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ 35`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = 60`, rounding `2^-256`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.SLH256f

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^64)`, `j = 0, …, 35`, at SLH-DSA-256f. -/
def gammaHi (j : ℕ) : ℚ :=
  [
    9223372036854775809 / 2 ^ 63,
    9222809109807147708 / 2 ^ 76,
    9797511999709720563 / 2 ^ 85,
    5490751031807406641 / 2 ^ 93,
    6728146437594745654 / 2 ^ 102,
    9368365080672493335 / 2 ^ 111,
    7582203097715235061 / 2 ^ 119,
    7094691472794637695 / 2 ^ 127,
    7497290040471964361 / 2 ^ 135,
    8746136402600561393 / 2 ^ 143,
    5552138611255809731 / 2 ^ 150,
    7613062128072027723 / 2 ^ 158,
    5607855308565431302 / 2 ^ 165,
    8832687036238074243 / 2 ^ 173,
    7399948359142928093 / 2 ^ 180,
    6565045851312067898 / 2 ^ 187,
    6143479474881525299 / 2 ^ 194,
    6044153543218021299 / 2 ^ 201,
    6234230202775088839 / 2 ^ 208,
    6724684829137529352 / 2 ^ 215,
    7568584492317553457 / 2 ^ 222,
    8869675456461394649 / 2 ^ 229,
    5401313183223556649 / 2 ^ 235,
    6825018269665383587 / 2 ^ 242,
    8933308841213715992 / 2 ^ 249,
    6047462397407097176 / 2 ^ 255,
    8458105501671367786 / 2 ^ 262,
    6102691179385218788 / 2 ^ 268,
    9075809612788818266 / 2 ^ 275,
    6947792730503352283 / 2 ^ 281,
    5470270912901966739 / 2 ^ 287,
    8851206852033919658 / 2 ^ 294,
    7351811679324321936 / 2 ^ 300,
    6264176114097129889 / 2 ^ 306,
    5471187073325180204 / 2 ^ 312,
    9789635948840897605 / 2 ^ 319
  ].getD j 0

theorem gammaHi_check : ∀ j ≤ 35, gammaHiQ 68 9 64 60 256 j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^64) ≤ gammaHi j` for `j ≤ 35` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ 35, gamma (1 / 2 ^ 68) (2 ^ 9) (2 ^ 64) j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) 9 64 60 256 j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : (1 / 2 ^ 68 : ℝ) = ((1 / 2 ^ 68 : ℚ) : ℝ) := by push_cast; rfl

/-- Table 7 (`x^ex = 255.91`): `Γ_35(2^64) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : gamma (1 / 2 ^ 68) (2 ^ 9) (2 ^ 64) 35 ≤ (2 : ℝ) ^ (-255.90 : ℝ) :=
  le_two_rpow_of_check (N := 100) (by norm_num) (-25590) (by norm_num)
      (gamma_le 35 le_rfl) (by decide +kernel)

/-- Table 3, SLH-DSA-256f, `q = 1` (exact column): search term `2^-254.91`,
`|K|`-term `2^-507.96`, `T₁ = 2^-507.96` (`T₂ = 0`);
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-192` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q1 :
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) 1 ≤ (2 : ℝ) ^ (-254.90 : ℝ) ∧
    pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) 1 (2 ^ 256) ≤ (2 : ℝ) ^ (-507.95 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) 1 (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-507.95 : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) 1 (2 ^ 256) ≤ (2 : ℝ) ^ (-254.90 : ℝ) ∧
    pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) 1 (2 ^ 256) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) 1 (2 ^ 256) := by
  have hK :
      pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) 1 (2 ^ 256) ≤ (2 : ℝ) ^ (-507.95 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-50795) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-25490) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-50795) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-25490) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 0 256 (by norm_num)) (by norm_num)⟩

/-- Table 3, SLH-DSA-256f, `q = 2^128` (exact column): search term `2^-127.91`,
`|K|`-term `2^-252.96`, `T₁ = 2^-252.96`, `T₂ = 2^-379.19`;
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^-64` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_q2e128 :
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) ≤ (2 : ℝ) ^ (-127.90 : ℝ) ∧
    pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤ (2 : ℝ) ^ (-252.95 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-252.95 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) (2 ^ 256) 2 ≤ (2 : ℝ) ^ (-379.18 : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤ (2 : ℝ) ^ (-127.90 : ℝ) ∧
    pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤
      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm (2 ^ 64) (2 ^ 128) (2 ^ 256) := by
  have hK :
      pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 128) (2 ^ 256) ≤ (2 : ℝ) ^ (-252.95 : ℝ) :=
    le_two_rpow_of_check (N := 100) (by norm_num) (-25295) (by norm_num)
      (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)
  exact ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-12790) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    hK,
    le_two_rpow_of_check (N := 100) (by norm_num) (-25295) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-37918) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-12790) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_mul_of_le hK (crudeTerm_two_pow 64 128 256 (by norm_num)) (by norm_num)⟩

/-- The `q` of the last row of Table 3 at SLH-DSA-256f: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ 253.8862`; the paper
prints `q* = 2^253.89`). -/
def qStar : ℕ := 26752537950645343098576641503300306864886725868128788605481770721031207626522

/-- Table 3, SLH-DSA-256f, last row (`q = q* = 2^253.89`, exact column): at a
`q ≥ 2^253.88` the `|K|`-term is at most `1`, the search term is `2^-2.03`,
`T₁ = 2^-1.19`, `T₂ = 2^-1.53`. -/
theorem table3_qStar :
    (2 : ℝ) ^ (253.88 : ℝ) ≤ (qStar : ℝ) ∧
    pullSum (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) qStar (2 ^ 256) ≤ 1 ∧
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) qStar ≤ (2 : ℝ) ^ (-2.02 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) qStar (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-1.18 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) qStar (2 ^ 256) 2 ≤ (2 : ℝ) ^ (-1.52 : ℝ) :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 25388 (by norm_num) (by decide +kernel),
    le_one_of_check (pullSum_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-202) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-118) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-152) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 2) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256f, `log₂ q = 240` (exact column): search term `2^-15.91`,
`T₁ = 2^-28.96`, `R₂ = 2^-43.19`, and the bound of Theorem 2 `2^-15.91`. -/
theorem table5_q2e240 :
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 240) ≤ (2 : ℝ) ^ (-15.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 240) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-28.95 : ℝ) ∧
    remainderTwo (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 240) (2 ^ 256) ≤ (2 : ℝ) ^ (-43.18 : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 240) (2 ^ 256) ≤ (2 : ℝ) ^ (-15.90 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-1590) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-2895) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-4318) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1590) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256f, `log₂ q = 248` (exact column): search term `2^-7.91`,
`T₁ = 2^-12.96`, `R₂ = 2^-19.18`, and the bound of Theorem 2 `2^-7.87`. -/
theorem table5_q2e248 :
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 248) ≤ (2 : ℝ) ^ (-7.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 248) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-12.95 : ℝ) ∧
    remainderTwo (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 248) (2 ^ 256) ≤ (2 : ℝ) ^ (-19.17 : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 248) (2 ^ 256) ≤ (2 : ℝ) ^ (-7.86 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-790) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1295) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-1917) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-786) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256f, `log₂ q = 252` (exact column): search term `2^-3.91`,
`T₁ = 2^-4.96`, `R₂ = 2^-7.01`, and the bound of Theorem 2 `2^-3.23`. -/
theorem table5_q2e252 :
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 252) ≤ (2 : ℝ) ^ (-3.90 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 252) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (-4.95 : ℝ) ∧
    remainderTwo (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 252) (2 ^ 256) ≤ (2 : ℝ) ^ (-7.00 : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 252) (2 ^ 256) ≤ (2 : ℝ) ^ (-3.22 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (-390) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-495) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-700) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (-322) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- Table 5, SLH-DSA-256f, `log₂ q = 256` (exact column): search term `2^0.09`,
`T₁ = 2^3.04`, `R₂ = 2^8.07`, and the bound of Theorem 2 `2^8.12`. -/
theorem table5_q2e256 :
    searchTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 256) ≤ (2 : ℝ) ^ (0.10 : ℝ) ∧
    pullTerm (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 256) (2 ^ 256) 1 ≤ (2 : ℝ) ^ (3.05 : ℝ) ∧
    remainderTwo (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 256) (2 ^ 256) ≤ (2 : ℝ) ^ (8.08 : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) (2 ^ 256) (2 ^ 256) ≤ (2 : ℝ) ^ (8.13 : ℝ) :=
  ⟨le_two_rpow_of_check (N := 100) (by norm_num) (10) (by norm_num)
      (searchTerm_le_Q gamma_le _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (305) (by norm_num)
      (pullTerm_le_Q theta_eq (by norm_num) gamma_le _ _ 1) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (808) (by norm_num)
      (remainderTwo_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel),
    le_two_rpow_of_check (N := 100) (by norm_num) (813) (by norm_num)
      (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

/-- The smallest `q` with `q ≥ 2^253.75` (Table 7 prints `q₁ = 2^253.76`). -/
def qOne : ℕ := 24342288188599352490146307195441198235054706427029853228662604299342563893415

/-- Table 7, SLH-DSA-256f: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^253.75`,
consistent with `q₁ = 2^253.76`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ (253.75 : ℝ) ≤ (qOne : ℝ) ∧
    mainBound (1 / 2 ^ 68) (2 ^ 9) 35 (2 ^ 64) qOne (2 ^ 256) ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) 25375 (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q theta_eq (by norm_num) gamma_le _ _) (by decide +kernel)⟩

end ShrincsSecurity.ITSR.Concrete.SLH256f

end
