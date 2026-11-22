module

public import ShrincsSecurity.Concrete.Figures

/-!
# Convention M: Table 8 (Section 6.8)

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), **Section 6.8** (lines 5430–5482) and
**Table 8** (lines 5463–5474), classical.

Under Convention M (Definition 5.1) every collection term is instantiated at
`q := ξ + V + q_λ,i` and its `|P|` summands at `ξ + q_λ,i`. Bounding every `q_λ,i` by the largest
collection budget `B`, the sums `sfSum c B` and `slSum dsprRow c B` of `Concrete.Paths` are exactly
these instantiations, and `sfSum_budget` / `slSum_budget` show that they add exactly `36 B/2^128`
and `52 B/2^128` to the Convention I bounds.

The budgets: `B = Q^sl_Λ = 2^45 · 164965` on the stateless path, and on the stateful path
`B = L (lsf w + 1) + I + qkg + qg` with `I = L − 1`, `qkg = 287743`, and the grinding budget either
the cap `qg = 2^c L` (`c = 16`, the only valid budget) or the expectation reading `qg ≤ 2^7 L`.

## Results (paper → certified)

| Path | `B` | `c B/2^128` | gap |
|---|---|---|---|
| stateless (`c = 52`) | `≈ 2^62.33` → `[62.33, 62.34]` | `2^-59.96` → `[−59.97, −59.96]` | `51.4` → `[51.35, 51.45]` |
| BXMSS-20, cap | `< 2^36.02` → `[36.01, 36.02]` | `2^-86.81` → `[−86.82, −86.81]` | `27.5` → `[27.45, 27.55]` |
| BXMSS-20, expected | `≈ 2^29.3` → `[29.32, 29.33]` | `2^-93.50` → `[−93.51, −93.50]` | `20.8` → `[20.75, 20.85]` |
| UXMSS-256, cap | `< 2^24.04` → `[24.03, 24.04]` | `2^-98.79` → `[−98.80, −98.79]` | `15.5` → `[15.45, 15.55]` |
| UXMSS-256, expected | `≈ 2^18.8` → `[18.78, 18.79]` | `2^-104.04` → `[−104.05, −104.04]` | `10.2` → `[10.15, 10.25]` |

(constants: `log₂` rounded up to two decimals; gaps: `log₂(c B/2^128) − log₂ B(0)`, rounded to
nearest, against the Convention I values at `ξ = 0`, `≈ 2^-111.41` and `≈ 2^-114.29`, certified in
`table8_caption`). With the theorem's rounded `qkg ≤ 2^19` the UXMSS-256 cap budget exceeds
`2^24.04` (`table8_qkg_rounded`). Convention M changes no classical `ξ*` of Table 5
(`section_6_8_xiStar`).
-/

@[expose] public section

namespace ShrincsSecurity.Concrete

open ShrincsSecurity.ITSR ShrincsSecurity.ITSR.Concrete ShrincsSecurity.Scheme

/-! ## Budgets -/

/-- BXMSS-20 (`L = 2^20`, `I = L − 1`), grinding cap `qg = 2^c L`. -/
def budgetBXcap : ℕ := budgetSf shrincs (2 ^ 20) (2 ^ 20 - 1) (2 ^ shrincs.c * 2 ^ 20)
/-- BXMSS-20, expectation reading `qg = 2^7 L`. -/
def budgetBXexp : ℕ := budgetSf shrincs (2 ^ 20) (2 ^ 20 - 1) (2 ^ 7 * 2 ^ 20)
/-- UXMSS-256 (`L = 2^8`, `I = L − 1`), grinding cap `qg = 2^c L`. -/
def budgetUXcap : ℕ := budgetSf shrincs (2 ^ 8) (2 ^ 8 - 1) (2 ^ shrincs.c * 2 ^ 8)
/-- UXMSS-256, expectation reading `qg = 2^7 L`. -/
def budgetUXexp : ℕ := budgetSf shrincs (2 ^ 8) (2 ^ 8 - 1) (2 ^ 7 * 2 ^ 8)

theorem budgets_eq :
    QslLam shrincs = 5804189941634170880 ∧ budgetBXcap = 69258732542 ∧
    budgetBXexp = 673473534 ∧ budgetUXcap = 17196542 ∧ budgetUXexp = 452094 := by
  decide +kernel

/-! ## Convention M bounds -/

/-- Claim 6.1 under Convention M: every collection term charged the budget `Q^sl_Λ`. -/
noncomputable def slBoundM (ξ : ℕ) : ℝ :=
  slSum dsprRow (.uniform (Vsl shrincs)) (QslLam shrincs) ξ

/-- Claim 6.2 under Convention M with the stateful budget `B`. -/
noncomputable def sfBoundM (B L ξ : ℕ) : ℝ := sfSum (.uniform (Vsf shrincs)) B L ξ

theorem slBoundM_eq (ξ : ℕ) : slBoundM ξ = slBound ξ + 52 * (QslLam shrincs : ℝ) / 2 ^ 128 :=
  slSum_budget _ _ _

theorem sfBoundM_eq (B L ξ : ℕ) : sfBoundM B L ξ = sfBound L ξ + 36 * (B : ℝ) / 2 ^ 128 :=
  sfSum_budget _ _ _ _

/-! ## Table 8 -/

/-- The caption of Table 8: the Convention I values at `ξ = 0` are `≈ 2^-111.41` (stateless) and
`≈ 2^-114.29` (stateful), to nearest. -/
theorem table8_caption (L : ℕ) :
    (-111.415 ≤ Real.logb 2 (slBound 0) ∧ Real.logb 2 (slBound 0) ≤ -111.405) ∧
    (-114.295 ≤ Real.logb 2 (sfBound L 0) ∧ Real.logb 2 (sfBound L 0) ≤ -114.285) :=
  ⟨logb_bracket_of_Q (N := 200) (by norm_num) (-22283) (-22281) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_slBound 0) (slBound_le_Q 0) (by decide +kernel)
      (by decide +kernel),
    logb_bracket_of_Q (N := 200) (by norm_num) (-22859) (-22857) (by norm_num) (by norm_num)
      (by decide +kernel) (sfBound_eq_Q L 0).ge (sfBound_eq_Q L 0).le (by decide +kernel)
      (by decide +kernel)⟩

/-- One row of Table 8: `log₂ B ∈ [b₀, b₁]`, `log₂ (c B/2^128) ∈ [k₀, k₁]`, and the gap
`log₂ (c B/2^128) − log₂ X ∈ [g₀, g₁]` to the Convention I value `X` at `ξ = 0`. -/
def Table8Row (B : ℕ) (c X b₀ b₁ k₀ k₁ g₀ g₁ : ℝ) : Prop :=
  (b₀ ≤ Real.logb 2 B ∧ Real.logb 2 B ≤ b₁) ∧
  (k₀ ≤ Real.logb 2 (c * B / 2 ^ 128) ∧ Real.logb 2 (c * B / 2 ^ 128) ≤ k₁) ∧
  (g₀ ≤ Real.logb 2 (c * B / 2 ^ 128) - Real.logb 2 X ∧
    Real.logb 2 (c * B / 2 ^ 128) - Real.logb 2 X ≤ g₁)

/-- **Table 8**, stateless row (`c = 52`, `B = Q^sl_Λ ≈ 2^62.33`): `c B/2^128 = 2^-59.96`, gap
`51.4`. -/
theorem table8_sl :
    Table8Row (QslLam shrincs) 52 (slBound 0) 62.33 62.34 (-59.97) (-59.96) 51.35 51.45 := by
  have hB : ((QslLam shrincs : ℕ) : ℝ) = ((5804189941634170880 : ℚ) : ℝ) := by
    rw [budgets_eq.1]; push_cast; rfl
  have hc : (52 : ℝ) * (QslLam shrincs : ℕ) / 2 ^ 128 =
      ((52 * 5804189941634170880 / 2 ^ 128 : ℚ) : ℝ) := by
    rw [budgets_eq.1]; push_cast; ring
  refine ⟨logb_bracket_of_Q (N := 100) (by norm_num) 6233 6234 (by norm_num) (by norm_num)
      (by decide +kernel) hB.ge hB.le (by decide +kernel) (by decide +kernel),
    ?_, ?_⟩
  · rw [hc]
    exact logb_bracket_of_Q (N := 100) (by norm_num) (-5997) (-5996) (by norm_num) (by norm_num)
      (by decide +kernel) le_rfl le_rfl (by decide +kernel) (by decide +kernel)
  · rw [hc]
    exact logb_sub_bracket (N := 100) (by norm_num) 5135 5145 (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) le_rfl le_rfl (Q_le_slBound 0) (slBound_le_Q 0)
      (by decide +kernel) (by decide +kernel)

/-- A stateful row of Table 8 (`c = 36`), from the value of the budget. -/
theorem table8_sf_row {B : ℕ} (b : ℕ) (hb : B = b) (L : ℕ) {b₀ b₁ k₀ k₁ g₀ g₁ : ℝ}
    (B₀ B₁ K₀ K₁ G₀ G₁ : ℤ) (hb₀ : b₀ = (B₀ : ℝ) / 100) (hb₁ : b₁ = (B₁ : ℝ) / 100)
    (hk₀ : k₀ = (K₀ : ℝ) / 100) (hk₁ : k₁ = (K₁ : ℝ) / 100)
    (hg₀ : g₀ = (G₀ : ℝ) / 100) (hg₁ : g₁ = (G₁ : ℝ) / 100) (hpos : 0 < b)
    (c₁ : (2 : ℚ) ^ B₀ ≤ (b : ℚ) ^ 100) (c₂ : (b : ℚ) ^ 100 ≤ (2 : ℚ) ^ B₁)
    (c₃ : (2 : ℚ) ^ K₀ ≤ (36 * b / 2 ^ 128 : ℚ) ^ 100)
    (c₄ : (36 * b / 2 ^ 128 : ℚ) ^ 100 ≤ (2 : ℚ) ^ K₁)
    (c₅ : (2 : ℚ) ^ G₀ * sfQ 0 ^ 100 ≤ (36 * b / 2 ^ 128 : ℚ) ^ 100)
    (c₆ : (36 * b / 2 ^ 128 : ℚ) ^ 100 ≤ (2 : ℚ) ^ G₁ * sfQ 0 ^ 100) :
    Table8Row B 36 (sfBound L 0) b₀ b₁ k₀ k₁ g₀ g₁ := by
  rw [hb]
  have hb' : ((b : ℕ) : ℝ) = ((b : ℚ) : ℝ) := by push_cast; rfl
  have hc : (36 : ℝ) * (b : ℕ) / 2 ^ 128 = ((36 * b / 2 ^ 128 : ℚ) : ℝ) := by push_cast; ring
  have hpos' : (0 : ℚ) < 36 * b / 2 ^ 128 := by positivity
  refine ⟨logb_bracket_of_Q (N := 100) (by norm_num) B₀ B₁ hb₀ hb₁ (by positivity) hb'.ge hb'.le
      c₁ c₂, ?_, ?_⟩
  · rw [hc]
    exact logb_bracket_of_Q (N := 100) (by norm_num) K₀ K₁ hk₀ hk₁ hpos'.le le_rfl le_rfl c₃ c₄
  · rw [hc]
    exact logb_sub_bracket (N := 100) (by norm_num) G₀ G₁ hg₀ hg₁ hpos' (by decide +kernel)
      le_rfl le_rfl (sfBound_eq_Q L 0).ge (sfBound_eq_Q L 0).le c₅ c₆

/-- **Table 8**, BXMSS-20 with the grinding cap `qg = 2^16 L`: `B < 2^36.02`,
`c B/2^128 = 2^-86.81`, gap `27.5`. -/
theorem table8_BXcap :
    Table8Row budgetBXcap 36 (sfBound (2 ^ 20) 0) 36.01 36.02 (-86.82) (-86.81) 27.45 27.55 :=
  table8_sf_row 69258732542 budgets_eq.2.1 _ 3601 3602 (-8682) (-8681) 2745 2755 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **Table 8**, BXMSS-20 with the expectation reading `qg ≤ 2^7 L`: `B ≈ 2^29.3`,
`c B/2^128 = 2^-93.50`, gap `20.8`. -/
theorem table8_BXexp :
    Table8Row budgetBXexp 36 (sfBound (2 ^ 20) 0) 29.32 29.33 (-93.51) (-93.50) 20.75 20.85 :=
  table8_sf_row 673473534 budgets_eq.2.2.1 _ 2932 2933 (-9351) (-9350) 2075 2085 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **Table 8**, UXMSS-256 with the grinding cap `qg = 2^16 L`: `B < 2^24.04`,
`c B/2^128 = 2^-98.79`, gap `15.5`. -/
theorem table8_UXcap :
    Table8Row budgetUXcap 36 (sfBound (2 ^ 8) 0) 24.03 24.04 (-98.80) (-98.79) 15.45 15.55 :=
  table8_sf_row 17196542 budgets_eq.2.2.2.1 _ 2403 2404 (-9880) (-9879) 1545 1555 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **Table 8**, UXMSS-256 with the expectation reading `qg ≤ 2^7 L`: `B ≈ 2^18.8`,
`c B/2^128 = 2^-104.04`, gap `10.2`. -/
theorem table8_UXexp :
    Table8Row budgetUXexp 36 (sfBound (2 ^ 8) 0) 18.78 18.79 (-104.05) (-104.04) 10.15 10.25 :=
  table8_sf_row 452094 budgets_eq.2.2.2.2 _ 1878 1879 (-10405) (-10404) 1015 1025 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **Section 6.8**: with the theorem's rounded bound `qkg ≤ 2^19` in place of `qkg = 287743`, the
UXMSS-256 cap budget would be slightly above `2^24.04`. -/
theorem table8_qkg_rounded :
    (2 : ℝ) ^ (24.05 : ℝ) ≤ ((2 ^ 8 * (shrincs.lsf * shrincs.w + 1) + (2 ^ 8 - 1) + 2 ^ 19 +
      2 ^ shrincs.c * 2 ^ 8 : ℕ) : ℝ) :=
  ITSR.Concrete.two_rpow_le_of_check (N := 100) (by norm_num) 2405 (by norm_num)
    (by decide +kernel)

/-! ## Section 6.8: no classical `ξ*` changes -/

/-- `⌊2^122.23⌋`. -/
def xiM₀ : ℕ := 6235860195815975280881007993686647491
/-- `⌊2^122.75⌋`. -/
def xiM₀' : ℕ := 8941944453683322737089245665759947262

theorem sfBoundM_mono (B L : ℕ) : Monotone (sfBoundM B L) := by
  intro a b h
  rw [sfBoundM_eq, sfBoundM_eq]
  linarith [sfBound_mono L h]

theorem sfM_xiStar_bracket (B L : ℕ) (hB : B ≤ budgetBXcap) :
    122.75 ≤ Real.logb 2 (xiStar (sfBoundM B L)) ∧
      Real.logb 2 (xiStar (sfBoundM B L)) ≤ 122.76 := by
  have hB' : (36 : ℝ) * (B : ℝ) / 2 ^ 128 ≤ ((36 * 69258732542 / 2 ^ 128 : ℚ) : ℝ) := by
    rw [budgets_eq.2.1] at hB
    have : (B : ℝ) ≤ 69258732542 := by exact_mod_cast hB
    push_cast
    gcongr
  have h₀ : sfBoundM B L xiM₀' < 1 := by
    rw [sfBoundM_eq, sfBound_eq_Q]
    refine lt_one_of_Q (x := sfQ xiM₀' + 36 * 69258732542 / 2 ^ 128) ?_ (by decide +kernel)
    push_cast at hB' ⊢
    linarith
  have h₁ : 1 ≤ sfBoundM B L (sfXi₀ + 1) := by
    rw [sfBoundM_eq]
    have := (sf_xiStar_mem L).2
    have h := one_le_of_Q (sfBound_eq_Q L (sfXi₀ + 1)).ge (by decide +kernel)
    have : (0 : ℝ) ≤ 36 * (B : ℝ) / 2 ^ 128 := by positivity
    linarith
  exact logb_xiStar_bracket (xiStar_bracket (sfBoundM_mono B L) h₀ h₁) (N := 100) (by norm_num)
    12275 12276 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **Section 6.8**: Convention M changes no classical `ξ*` of Table 5: the stateless bound with
the budget `Q^sl_Λ`, and the stateful bound with any budget up to the BXMSS-20 cap budget (which
covers every row of Table 8), still reach `1` at `2^122.23` and `2^122.75`. -/
theorem section_6_8_xiStar :
    (122.23 ≤ Real.logb 2 (xiStar slBoundM) ∧ Real.logb 2 (xiStar slBoundM) ≤ 122.24) ∧
    (∀ L, 122.75 ≤ Real.logb 2 (xiStar (sfBoundM budgetBXcap L)) ∧
      Real.logb 2 (xiStar (sfBoundM budgetBXcap L)) ≤ 122.76) ∧
    (∀ L, 122.75 ≤ Real.logb 2 (xiStar (sfBoundM budgetUXcap L)) ∧
      Real.logb 2 (xiStar (sfBoundM budgetUXcap L)) ≤ 122.76) := by
  refine ⟨?_, fun L => sfM_xiStar_bracket _ L le_rfl,
    fun L => sfM_xiStar_bracket _ L (by decide +kernel)⟩
  have hQ : (52 : ℝ) * (QslLam shrincs : ℕ) / 2 ^ 128 =
      ((52 * 5804189941634170880 / 2 ^ 128 : ℚ) : ℝ) := by
    rw [budgets_eq.1]; push_cast; ring
  have hmono : Monotone slBoundM := by
    intro a b h
    rw [slBoundM_eq, slBoundM_eq]
    linarith [slBound_mono h]
  have h₀ : slBoundM xiM₀ < 1 := by
    rw [slBoundM_eq, hQ]
    refine lt_one_of_Q (x := slHiQ xiM₀ + 52 * 5804189941634170880 / 2 ^ 128) ?_
      (by decide +kernel)
    push_cast
    linarith [slBound_le_Q xiM₀]
  have h₁ : 1 ≤ slBoundM slXi₁ := by
    rw [slBoundM_eq]
    have := one_le_of_Q (Q_le_slBound slXi₁) (by decide +kernel)
    have : (0 : ℝ) ≤ 52 * (QslLam shrincs : ℝ) / 2 ^ 128 := by positivity
    linarith
  exact logb_xiStar_bracket (xiStar_bracket hmono h₀ h₁) (N := 100) (by norm_num) 12223 12224
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

end ShrincsSecurity.Concrete

end
