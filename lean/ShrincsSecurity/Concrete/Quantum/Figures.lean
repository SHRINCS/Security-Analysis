module

public import ShrincsSecurity.Concrete.Quantum.Paths

/-!
# The quantum figures of Section 6 (Table 5, Claims 6.1, 6.2, 6.4, Section 6.1, abstract)

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Table 5** quantum columns
(lines 4796–4820, rendered page 76), the quantum lines of **Claims 6.1, 6.2, 6.4** (Eqs. (2), (4),
(5), (10), (11) and their rounded forms, pages 82–85), the quantum statements of **Section 6.1**
(lines 4777–4800) and the **abstract** (line 214: "quantumly, they reach 1 at `2^58.0` to `2^59.2`
hash queries").

## What is certified

As in `Concrete.Figures`, a bound `B : ℕ → ℝ` is reported by `log₂ ξ*`, `ξ* = xiStar B` the least
hash-query count at which `B` reaches `1`, and by `log₂ B(0)`. The caption of Table 5 rounds every
quantum `log₂ ξ*` down and every `log₂ B(0)` up, to one decimal. We certify each entry as a bracket
of width `0.01`: `Y ≤ log₂ ξ* ≤ Y + 0.01` from an explicit pair `ξ₀ < ξ* ≤ ξ₁` (`*_mem`), and
`Z − 0.01 ≤ log₂ B(0) ≤ Z`. The bounds are the sums of `Quantum.Paths` (`slQ`, `sfQ`, `fullQ` at the
three forms of Table 5, and their pointwise minima `slMin`, `sfMin`, `fullMin`); every evaluation is
one `decide +kernel` on the rational enclosure of `Quantum.Enc`. The stateless and full-scheme
figures rest on the **conjectured** SM-DSPR row of Table 6.

## Results (paper → certified)

Table 5 (`log₂ ξ*` and, in parentheses, `log₂ B(0)`):

| Bound | `e = 1` | `e = 1/2` | minimum |
|---|---|---|---|
| Thm 4.3 | 58.5 (−22.4) → [58.53, 58.54] ([−22.50, −22.49]) | 58.5 (−43.9) → [58.53, 58.54] ([−44.00, −43.99]) | 58.5 (−43.9) → [58.53, 58.54] ([−44.00, −43.99]) |
| Thm 4.2, BXMSS-20 | 59.2 (−41.4) → [59.29, 59.30] ([−41.50, −41.49]) | 58.4 (−82.9) → [58.49, 58.50] ([−83.00, −82.99]) | 59.2 (−82.9) → [59.29, 59.30] ([−83.00, −82.99]) |
| Thm 4.2, UXMSS-256 | 59.2 (−53.4) → [59.29, 59.30] ([−53.50, −53.49]) | 58.4 (−101.3) → [58.49, 58.50] ([−101.33, −101.32]) | 59.2 (−101.3) → [59.29, 59.30] ([−101.33, −101.32]) |
| Thm 4.1, BXMSS-20 | 58.0 (−22.4) → [58.01, 58.02] ([−22.50, −22.49]) | 57.1 (−42.9) → [57.16, 57.17] ([−43.00, −42.99]) | 58.0 (−42.9) → [58.01, 58.02] ([−43.00, −42.99]) |
| Thm 4.1, UXMSS-256 | 58.0 (−22.4) → [58.01, 58.02] ([−22.50, −22.49]) | 57.1 (−42.9) → [57.16, 57.17] ([−43.00, −42.99]) | 58.0 (−43.9) → [58.01, 58.02] ([−44.00, −43.99]) |

Every printed entry is the certified bracket rounded as the caption says.

* Claims 6.1, 6.2, 6.4, rounded forms (`claim_6_1_rounded`, `claim_6_2_rounded_*`,
  `claim_6_4_rounded_*`): every printed exponent and constant holds.
* Claim 6.2: the minimum of Eqs. (4), (5) is `2^-82.9` / `2^-101.3` at `ξ = 0` and reaches `1` at
  `2^59.2` (both shapes); Eq. (4) alone at `2^58.4`; the minimum is Eq. (4) exactly for
  `ξ ≤ 286586 ≈ 2^18.1` (BXMSS-20) and `ξ ≤ 69` (UXMSS-256) (`claim_6_2_switch_*`).
* Claim 6.4: the minimum of Eqs. (10), (11) is `2^-42.9` / `2^-43.9` at `ξ = 0` and reaches `1` at
  `2^58.0`; Eq. (10) alone at `2^57.1`; for BXMSS-20 it switches from Eq. (10) to Eq. (11) after
  `ξ = 58088 ≈ 2^15.8` (`claim_6_4_switch_bx`).
* Claim 6.1 / Section 6.6: `e = 1/2` in the itsr proof is the smaller form at `ξ = 2^56.82`
  and `e = 1` at `ξ = 2^56.83` (`claim_6_1_switch`, "up to `ξ ≈ 2^56.8`"); the `e = 1` form
  reaches `1` at most `0.01` bits later (`claim_6_1_one_vs_half`).
* Section 6.1: `e = 1/2` loses `[0.79, 0.80]` bits of `ξ*` on the stateful path and `[0.85, 0.86]`
  for the full scheme (printed `0.8`, `0.9`); the column "minimum" and the column `e = 1` attain
  the core `ξ*` up to `0.01` bits (`section_6_1_core_*`).
* Abstract: every bound with `e = 1` and every minimum has `58.01 ≤ log₂ ξ* ≤ 59.30`
  (`abstract_quantum`), i.e. `2^58.0` to `2^59.2` in the rounding of Table 5.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete.Quantum

open ShrincsSecurity.Concrete ShrincsSecurity.Scheme ShrincsSecurity.ITSR.Concrete

/-! ## Core terms (Section 6.1) -/

/-- The quantum core terms of Theorem 4.3: the PRF terms, the search part `8(q+1)²Γ` of the itsr
term in its form `e = 1` (at `q = ξ + 1`), and the collection terms. -/
noncomputable def slCoreQ (ξ : ℕ) : ℝ :=
  prfTermsQ ξ + 8 * ((ξ : ℝ) + 2) ^ 2 * Gam + collSlQ .quad dsprRowQ (.uniform (Vsl shrincs)) ξ

/-- The quantum core terms of Theorem 4.2: the hash part `8(q+1)²/2^256` of the SM-rTCR term in its
form `e = 1` and the collection terms. -/
noncomputable def sfCoreQ (ξ : ℕ) : ℝ :=
  8 * ((ξ : ℝ) + 2) ^ 2 / 2 ^ 256 + collSfQ .quad (.uniform (Vsf shrincs)) ξ

/-- The quantum core terms of Theorem 4.1 (Claim 6.3 without the reprogramming terms), with
`ε_ds`. -/
noncomputable def fullCoreQ (ξ : ℕ) : ℝ :=
  prfTermsQ ξ + 8 * ((ξ : ℝ) + 2) ^ 2 / 2 ^ 256 + collSfQ .quad (.uniform (Vsf shrincs)) ξ +
    8 * ((ξ : ℝ) + 2) ^ 2 * Gam + collSlQ .quad dsprRowQ (.uniform (Vsl shrincs)) ξ + epsDs

def slCoreEnc (ξ : ℕ) : Enc :=
  prfEnc ξ + ⟨0, 8 * ((ξ : ℚ) + 2) ^ 2, []⟩ + .ofQ (collSlR .quad (.uniform 2741) ξ)

def sfCoreEnc (ξ : ℕ) : Enc :=
  .ofQ (8 * ((ξ : ℚ) + 2) ^ 2 / 2 ^ 256) + .ofQ (collSfR .quad (.uniform 497) ξ)

def fullCoreEnc (ξ : ℕ) : Enc :=
  prfEnc ξ + .ofQ (8 * ((ξ : ℚ) + 2) ^ 2 / 2 ^ 256) + .ofQ (collSfR .quad (.uniform 497) ξ) +
    ⟨0, 8 * ((ξ : ℚ) + 2) ^ 2, []⟩ + .ofQ (collSlR .quad (.uniform 2741) ξ) + .ofQ epsDsQ

theorem slCoreQ_eq_enc (ξ : ℕ) : slCoreQ ξ = (slCoreEnc ξ).val := by
  rw [slCoreEnc, Enc.val_add, Enc.val_add, Enc.val_ofQ, slCoreQ, Vsl_shrincs, collSlQ_eq,
    prfTermsQ_eq]
  simp only [Enc.val, sqSum_nil]; push_cast; ring

theorem sfCoreQ_eq_enc (ξ : ℕ) : sfCoreQ ξ = (sfCoreEnc ξ).val := by
  rw [sfCoreEnc, Enc.val_add, Enc.val_ofQ, Enc.val_ofQ, sfCoreQ, Vsf_shrincs, collSfQ_eq]
  push_cast; ring

theorem fullCoreQ_eq_enc (ξ : ℕ) : fullCoreQ ξ = (fullCoreEnc ξ).val := by
  rw [fullCoreEnc, Enc.val_add, Enc.val_add, Enc.val_add, Enc.val_add, Enc.val_add, Enc.val_ofQ,
    Enc.val_ofQ, Enc.val_ofQ, Enc.val_ofQ, fullCoreQ, Vsf_shrincs, Vsl_shrincs, collSfQ_eq,
    collSlQ_eq, prfTermsQ_eq, epsDs, epsDsQ]
  simp only [Enc.val, sqSum_nil]; push_cast; ring

theorem slCoreQ_mono : Monotone slCoreQ := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact add_le_add (add_le_add (prfTermsQ_mono hab)
    (mul_le_mul_of_nonneg_right (by gcongr) Gam_nonneg)) (collSlQ_mono _ _ hab)

theorem sfCoreQ_mono : Monotone sfCoreQ := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact add_le_add (by gcongr) (collSfQ_mono _ _ hab)

theorem fullCoreQ_mono : Monotone fullCoreQ := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (prfTermsQ_mono hab)
    (by gcongr)) (collSfQ_mono _ _ hab)) (mul_le_mul_of_nonneg_right (by gcongr) Gam_nonneg))
    (collSlQ_mono _ _ hab)) le_rfl

/-! ## Locating `ξ*` -/

theorem sl_one_mem :
    416710369840688285 < xiStar (slQ .one) ∧ xiStar (slQ .one) ≤ 416710521398949186 :=
  xiStar_bracket (slQ_mono .one)
    (Enc.lt_one_of_eq (slQ_eq_enc _ _) (by decide +kernel))
    (Enc.one_le_of_eq (slQ_eq_enc _ _) (by decide +kernel))

theorem sl_half_mem :
    416458247175489472 < xiStar (slQ .half) ∧ xiStar (slQ .half) ≤ 416458549560871549 :=
  xiStar_bracket (slQ_mono .half)
    (Enc.lt_one_of_eq (slQ_eq_enc _ _) (by decide +kernel))
    (Enc.one_le_of_eq (slQ_eq_enc _ _) (by decide +kernel))

theorem sl_min_mem :
    416710369840688285 < xiStar slMin ∧ xiStar slMin ≤ 416710521398949186 :=
  xiStar_bracket slMin_mono
    (minF_lt_of_one <|
      Enc.lt_one_of_eq (slQ_eq_enc _ _) (by decide +kernel))
    (one_le_minF1 (fun a => slQ_eq_enc a _) (by decide +kernel))

theorem sf_bx_one_mem :
    706304987277198904 < xiStar (sfQ .one .one (2 ^ 20)) ∧
      xiStar (sfQ .one .one (2 ^ 20)) ≤ 706304987277198905 :=
  xiStar_bracket (sfQ_mono .one .one _)
    (Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))

theorem sf_bx_half_mem :
    406767616153070237 < xiStar (sfQ .half .half (2 ^ 20)) ∧
      xiStar (sfQ .half .half (2 ^ 20)) ≤ 406767616153070238 :=
  xiStar_bracket (sfQ_mono .half .half _)
    (Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))

theorem sf_bx_min_mem :
    706305087829526821 < xiStar (sfMin (2 ^ 20)) ∧ xiStar (sfMin (2 ^ 20)) ≤ 706305087829526822 :=
  xiStar_bracket (sfMin_mono _)
    (minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (one_le_minF2 (fun a b => sfQ_eq_enc a b _ _) (by decide +kernel))

theorem sf_ux_one_mem :
    706305185239675552 < xiStar (sfQ .one .one (2 ^ 8)) ∧
      xiStar (sfQ .one .one (2 ^ 8)) ≤ 706305185239675553 :=
  xiStar_bracket (sfQ_mono .one .one _)
    (Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))

theorem sf_ux_half_mem :
    406767616153097285 < xiStar (sfQ .half .half (2 ^ 8)) ∧
      xiStar (sfQ .half .half (2 ^ 8)) ≤ 406767616153097286 :=
  xiStar_bracket (sfQ_mono .half .half _)
    (Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))

theorem sf_ux_min_mem :
    706305186810806426 < xiStar (sfMin (2 ^ 8)) ∧ xiStar (sfMin (2 ^ 8)) ≤ 706305186810806427 :=
  xiStar_bracket (sfMin_mono _)
    (minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (one_le_minF2 (fun a b => sfQ_eq_enc a b _ _) (by decide +kernel))

theorem full_bx_one_mem :
    292086628246681803 < xiStar (fullQ .one .one .one (2 ^ 20)) ∧
      xiStar (fullQ .one .one .one (2 ^ 20)) ≤ 292086682343812753 :=
  xiStar_bracket (fullQ_mono .one .one .one _)
    (Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))

theorem full_bx_half_mem :
    161599059639560292 < xiStar (fullQ .half .half .half (2 ^ 20)) ∧
      xiStar (fullQ .half .half .half (2 ^ 20)) ≤ 161599098164073746 :=
  xiStar_bracket (fullQ_mono .half .half .half _)
    (Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))

theorem full_bx_min_mem :
    292086658865389623 < xiStar (fullMin (2 ^ 20)) ∧
      xiStar (fullMin (2 ^ 20)) ≤ 292086712962533315 :=
  xiStar_bracket (fullMin_mono _)
    (minF_lt_of_one <| minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (one_le_minF3 (fun a b c => fullQ_eq_enc a b c _ _) (by decide +kernel))

theorem full_ux_one_mem :
    292086688527279577 < xiStar (fullQ .one .one .one (2 ^ 8)) ∧
      xiStar (fullQ .one .one .one (2 ^ 8)) ≤ 292086742624435613 :=
  xiStar_bracket (fullQ_mono .one .one .one _)
    (Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))

theorem full_ux_half_mem :
    161599059639565021 < xiStar (fullQ .half .half .half (2 ^ 8)) ∧
      xiStar (fullQ .half .half .half (2 ^ 8)) ≤ 161599098164078474 :=
  xiStar_bracket (fullQ_mono .half .half .half _)
    (Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))

theorem full_ux_min_mem :
    292086689005697055 < xiStar (fullMin (2 ^ 8)) ∧
      xiStar (fullMin (2 ^ 8)) ≤ 292086743102853290 :=
  xiStar_bracket (fullMin_mono _)
    (minF_lt_of_one <| minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (one_le_minF3 (fun a b c => fullQ_eq_enc a b c _ _) (by decide +kernel))

theorem claim_sf_bx_mem :
    706305087829440189 < xiStar (claimSf (2 ^ 20)) ∧
      xiStar (claimSf (2 ^ 20)) ≤ 706305087829440190 :=
  xiStar_bracket (claimSf_mono _)
    (min_lt_of_right_lt <|
      Enc.lt_one_of_eq (eq5_eq_enc _ _) (by decide +kernel))
    (le_min (Enc.one_le_of_eq (eq4_eq_enc _ _) (by decide +kernel))
      (Enc.one_le_of_eq (eq5_eq_enc _ _) (by decide +kernel)))

theorem claim_sf_ux_mem :
    706305186810806405 < xiStar (claimSf (2 ^ 8)) ∧
      xiStar (claimSf (2 ^ 8)) ≤ 706305186810806406 :=
  xiStar_bracket (claimSf_mono _)
    (min_lt_of_right_lt <|
      Enc.lt_one_of_eq (eq5_eq_enc _ _) (by decide +kernel))
    (le_min (Enc.one_le_of_eq (eq4_eq_enc _ _) (by decide +kernel))
      (Enc.one_le_of_eq (eq5_eq_enc _ _) (by decide +kernel)))

theorem claim_full_bx_mem :
    292009551616969727 < xiStar (claimFull (2 ^ 20)) ∧
      xiStar (claimFull (2 ^ 20)) ≤ 292009659686924728 :=
  xiStar_bracket (claimFull_mono _)
    (min_lt_of_right_lt <|
      Enc.lt_one_of_eq (eq11_eq_enc _ _) (by decide +kernel))
    (le_min (Enc.one_le_of_eq (eq10_eq_enc _ _) (by decide +kernel))
      (Enc.one_le_of_eq (eq11_eq_enc _ _) (by decide +kernel)))

theorem claim_full_ux_mem :
    292009581734596945 < xiStar (claimFull (2 ^ 8)) ∧
      xiStar (claimFull (2 ^ 8)) ≤ 292009689804576985 :=
  xiStar_bracket (claimFull_mono _)
    (min_lt_of_right_lt <|
      Enc.lt_one_of_eq (eq11_eq_enc _ _) (by decide +kernel))
    (le_min (Enc.one_le_of_eq (eq10_eq_enc _ _) (by decide +kernel))
      (Enc.one_le_of_eq (eq11_eq_enc _ _) (by decide +kernel)))

theorem sl_core_mem :
    416761919629679247 < xiStar slCoreQ ∧ xiStar slCoreQ ≤ 416762071228917367 :=
  xiStar_bracket slCoreQ_mono
    (Enc.lt_one_of_eq (slCoreQ_eq_enc _) (by decide +kernel))
    (Enc.one_le_of_eq (slCoreQ_eq_enc _) (by decide +kernel))

theorem sf_core_mem :
    706305188381937321 < xiStar sfCoreQ ∧ xiStar sfCoreQ ≤ 706305188381937322 :=
  xiStar_bracket sfCoreQ_mono
    (Enc.lt_one_of_eq (sfCoreQ_eq_enc _) (by decide +kernel))
    (Enc.one_le_of_eq (sfCoreQ_eq_enc _) (by decide +kernel))

theorem full_core_mem :
    292118044338648175 < xiStar fullCoreQ ∧ xiStar fullCoreQ ≤ 292118098448854013 :=
  xiStar_bracket fullCoreQ_mono
    (Enc.lt_one_of_eq (fullCoreQ_eq_enc _) (by decide +kernel))
    (Enc.one_le_of_eq (fullCoreQ_eq_enc _) (by decide +kernel))

/-! ## Table 5, quantum columns -/

/-- **Table 5**, Theorem 4.3 (stateless), quantum, `e = 1`: `58.5 (−22.4)`. -/
theorem table5_sl_one :
    (58.53 ≤ Real.logb 2 (xiStar (slQ .one)) ∧ Real.logb 2 (xiStar (slQ .one)) ≤ 58.54) ∧
    (-22.50 ≤ Real.logb 2 (slQ .one 0) ∧ Real.logb 2 (slQ .one 0) ≤ -22.49) :=
  ⟨logb_xiStar_bracket sl_one_mem (N := 100) (by norm_num) 5853 5854 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (slQ_eq_enc _ _) 100 (by norm_num) (-2250) (-2249) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.3 (stateless), quantum, `e = 1/2`: `58.5 (−43.9)`; **Claim 6.1**: the
bound of Eq. (2) is `2^-43.9` at `ξ = 0` and reaches `1` at `ξ* = 2^58.5`. -/
theorem table5_sl_half :
    (58.53 ≤ Real.logb 2 (xiStar (slQ .half)) ∧ Real.logb 2 (xiStar (slQ .half)) ≤ 58.54) ∧
    (-44.00 ≤ Real.logb 2 (slQ .half 0) ∧ Real.logb 2 (slQ .half 0) ≤ -43.99) :=
  ⟨logb_xiStar_bracket sl_half_mem (N := 100) (by norm_num) 5853 5854 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (slQ_eq_enc _ _) 100 (by norm_num) (-4400) (-4399) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.3 (stateless), quantum, minimum: `58.5 (−43.9)`. -/
theorem table5_sl_min :
    (58.53 ≤ Real.logb 2 (xiStar slMin) ∧ Real.logb 2 (xiStar slMin) ≤ 58.54) ∧
    (-44.00 ≤ Real.logb 2 (slMin 0) ∧ Real.logb 2 (slMin 0) ≤ -43.99) :=
  ⟨logb_xiStar_bracket sl_min_mem (N := 100) (by norm_num) 5853 5854 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 1099511627777 / 2 ^ 84) (hi := 549755813889 / 2 ^ 83) 100
      (by norm_num) (-4400) (-4399) (by norm_num) (by norm_num)
      (ge_minF1 (fun a => slQ_eq_enc a _) (by decide +kernel))
      (minF_le_of_half <|
        Enc.le_of_eq (slQ_eq_enc _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), BXMSS-20, quantum, `e = 1`: `59.2 (−41.4)`. -/
theorem table5_sf_bx_one :
    (59.29 ≤ Real.logb 2 (xiStar (sfQ .one .one (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfQ .one .one (2 ^ 20))) ≤ 59.30) ∧
    (-41.50 ≤ Real.logb 2 (sfQ .one .one (2 ^ 20) 0) ∧
      Real.logb 2 (sfQ .one .one (2 ^ 20) 0) ≤ -41.49) :=
  ⟨logb_xiStar_bracket sf_bx_one_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfQ_eq_enc _ _ _ _) 100 (by norm_num) (-4150) (-4149) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), BXMSS-20, quantum, `e = 1/2`: `58.4 (−82.9)`; this is Eq.
(4) alone (**Claim 6.2**: `2^58.4`). -/
theorem table5_sf_bx_half :
    (58.49 ≤ Real.logb 2 (xiStar (sfQ .half .half (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfQ .half .half (2 ^ 20))) ≤ 58.50) ∧
    (-83.00 ≤ Real.logb 2 (sfQ .half .half (2 ^ 20) 0) ∧
      Real.logb 2 (sfQ .half .half (2 ^ 20) 0) ≤ -82.99) :=
  ⟨logb_xiStar_bracket sf_bx_half_mem (N := 100) (by norm_num) 5849 5850 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfQ_eq_enc _ _ _ _) 100 (by norm_num) (-8300) (-8299) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), BXMSS-20, quantum, minimum: `59.2 (−82.9)`. -/
theorem table5_sf_bx_min :
    (59.29 ≤ Real.logb 2 (xiStar (sfMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfMin (2 ^ 20))) ≤ 59.30) ∧
    (-83.00 ≤ Real.logb 2 (sfMin (2 ^ 20) 0) ∧ Real.logb 2 (sfMin (2 ^ 20) 0) ≤ -82.99) :=
  ⟨logb_xiStar_bracket sf_bx_min_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 1099514909851 / 2 ^ 123) (hi := 274878727463 / 2 ^ 121) 100
      (by norm_num) (-8300) (-8299) (by norm_num) (by norm_num)
      (ge_minF2 (fun a b => sfQ_eq_enc a b _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <|
        Enc.le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), UXMSS-256, quantum, `e = 1`: `59.2 (−53.4)`. -/
theorem table5_sf_ux_one :
    (59.29 ≤ Real.logb 2 (xiStar (sfQ .one .one (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfQ .one .one (2 ^ 8))) ≤ 59.30) ∧
    (-53.50 ≤ Real.logb 2 (sfQ .one .one (2 ^ 8) 0) ∧
      Real.logb 2 (sfQ .one .one (2 ^ 8) 0) ≤ -53.49) :=
  ⟨logb_xiStar_bracket sf_ux_one_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfQ_eq_enc _ _ _ _) 100 (by norm_num) (-5350) (-5349) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), UXMSS-256, quantum, `e = 1/2`: `58.4 (−101.3)`; this is Eq.
(4) alone (**Claim 6.2**: `2^58.4`). -/
theorem table5_sf_ux_half :
    (58.49 ≤ Real.logb 2 (xiStar (sfQ .half .half (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfQ .half .half (2 ^ 8))) ≤ 58.50) ∧
    (-101.33 ≤ Real.logb 2 (sfQ .half .half (2 ^ 8) 0) ∧
      Real.logb 2 (sfQ .half .half (2 ^ 8) 0) ≤ -101.32) :=
  ⟨logb_xiStar_bracket sf_ux_half_mem (N := 100) (by norm_num) 5849 5850 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfQ_eq_enc _ _ _ _) 100 (by norm_num) (-10133) (-10132) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), UXMSS-256, quantum, minimum: `59.2 (−101.3)`. -/
theorem table5_sf_ux_min :
    (59.29 ≤ Real.logb 2 (xiStar (sfMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfMin (2 ^ 8))) ≤ 59.30) ∧
    (-101.33 ≤ Real.logb 2 (sfMin (2 ^ 8) 0) ∧ Real.logb 2 (sfMin (2 ^ 8) 0) ≤ -101.32) :=
  ⟨logb_xiStar_bracket sf_ux_min_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 3347611 / 2 ^ 123) (hi := 1755112275969 / 2 ^ 142) 100
      (by norm_num) (-10133) (-10132) (by norm_num) (by norm_num)
      (ge_minF2 (fun a b => sfQ_eq_enc a b _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <|
        Enc.le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full), BXMSS-20, quantum, `e = 1`: `58.0 (−22.4)`. -/
theorem table5_full_bx_one :
    (58.01 ≤ Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 20))) ≤ 58.02) ∧
    (-22.50 ≤ Real.logb 2 (fullQ .one .one .one (2 ^ 20) 0) ∧
      Real.logb 2 (fullQ .one .one .one (2 ^ 20) 0) ≤ -22.49) :=
  ⟨logb_xiStar_bracket full_bx_one_mem (N := 100) (by norm_num) 5801 5802 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullQ_eq_enc _ _ _ _ _) 100 (by norm_num) (-2250) (-2249) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full), BXMSS-20, quantum, `e = 1/2`: `57.1 (−42.9)`; this is Eq. (10)
alone (**Claim 6.4**: `2^57.1`). -/
theorem table5_full_bx_half :
    (57.16 ≤ Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 20))) ≤ 57.17) ∧
    (-43.00 ≤ Real.logb 2 (fullQ .half .half .half (2 ^ 20) 0) ∧
      Real.logb 2 (fullQ .half .half .half (2 ^ 20) 0) ≤ -42.99) :=
  ⟨logb_xiStar_bracket full_bx_half_mem (N := 100) (by norm_num) 5716 5717 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullQ_eq_enc _ _ _ _ _) 100 (by norm_num) (-4300) (-4299) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full), BXMSS-20, quantum, minimum: `58.0 (−42.9)`. -/
theorem table5_full_bx_min :
    (58.01 ≤ Real.logb 2 (xiStar (fullMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullMin (2 ^ 20))) ≤ 58.02) ∧
    (-43.00 ≤ Real.logb 2 (fullMin (2 ^ 20) 0) ∧ Real.logb 2 (fullMin (2 ^ 20) 0) ≤ -42.99) :=
  ⟨logb_xiStar_bracket full_bx_min_mem (N := 100) (by norm_num) 5801 5802 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 549755813889 / 2 ^ 82) (hi := 1099511627779 / 2 ^ 83) 100
      (by norm_num) (-4300) (-4299) (by norm_num) (by norm_num)
      (ge_minF3 (fun a b c => fullQ_eq_enc a b c _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <| minF_le_of_half <|
        Enc.le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full), UXMSS-256, quantum, `e = 1`: `58.0 (−22.4)`. -/
theorem table5_full_ux_one :
    (58.01 ≤ Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 8))) ≤ 58.02) ∧
    (-22.50 ≤ Real.logb 2 (fullQ .one .one .one (2 ^ 8) 0) ∧
      Real.logb 2 (fullQ .one .one .one (2 ^ 8) 0) ≤ -22.49) :=
  ⟨logb_xiStar_bracket full_ux_one_mem (N := 100) (by norm_num) 5801 5802 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullQ_eq_enc _ _ _ _ _) 100 (by norm_num) (-2250) (-2249) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full), UXMSS-256, quantum, `e = 1/2`: `57.1 (−42.9)`; this is Eq. (10)
alone (**Claim 6.4**: `2^57.1`). -/
theorem table5_full_ux_half :
    (57.16 ≤ Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 8))) ≤ 57.17) ∧
    (-43.00 ≤ Real.logb 2 (fullQ .half .half .half (2 ^ 8) 0) ∧
      Real.logb 2 (fullQ .half .half .half (2 ^ 8) 0) ≤ -42.99) :=
  ⟨logb_xiStar_bracket full_ux_half_mem (N := 100) (by norm_num) 5716 5717 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullQ_eq_enc _ _ _ _ _) 100 (by norm_num) (-4300) (-4299) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full), UXMSS-256, quantum, minimum: `58.0 (−43.9)`. -/
theorem table5_full_ux_min :
    (58.01 ≤ Real.logb 2 (xiStar (fullMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullMin (2 ^ 8))) ≤ 58.02) ∧
    (-44.00 ≤ Real.logb 2 (fullMin (2 ^ 8) 0) ∧ Real.logb 2 (fullMin (2 ^ 8) 0) ≤ -43.99) :=
  ⟨logb_xiStar_bracket full_ux_min_mem (N := 100) (by norm_num) 5801 5802 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 275067351287 / 2 ^ 82) (hi := 1100269405149 / 2 ^ 84) 100
      (by norm_num) (-4400) (-4399) (by norm_num) (by norm_num)
      (ge_minF3 (fun a b c => fullQ_eq_enc a b c _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <| minF_le_of_one <|
        Enc.le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-! ## Claims 6.1, 6.2 and 6.4: rounded forms -/

/-- A rational coefficient below a power of two: `x ≤ 2^(B/100)` from `x^100 ≤ 2^B`. -/
theorem coef_le {x : ℚ} {Y : ℝ} (B : ℤ) (hY : Y = (B : ℝ) / (100 : ℕ))
    (h : x ^ 100 ≤ (2 : ℚ) ^ B) : (x : ℝ) ≤ (2 : ℝ) ^ Y :=
  le_two_rpow_of_check (N := 100) (by norm_num) B hY le_rfl h

/-- `a ξ² + b ξ + c + ν ≤ ξ² 2^Y₂ + ξ 2^Y₁ + 2^Y₀ + ν`. -/
theorem rounded_le {ξ a b c ν Y₂ Y₁ Y₀ : ℝ} (hξ : 0 ≤ ξ) (ha : a ≤ (2 : ℝ) ^ Y₂)
    (hb : b ≤ (2 : ℝ) ^ Y₁) (hc : c ≤ (2 : ℝ) ^ Y₀) :
    a * ξ ^ 2 + b * ξ + c + ν ≤ ξ ^ 2 * (2 : ℝ) ^ Y₂ + ξ * (2 : ℝ) ^ Y₁ + (2 : ℝ) ^ Y₀ + ν := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg ξ), mul_le_mul_of_nonneg_left hb hξ]

/-- `a ξ² + b ξ + d √ξ + c + ν ≤ ξ² 2^Y₂ + ξ 2^Y₁ + d √ξ + 2^Y₀ + ν`. -/
theorem rounded_le_sqrt {ξ a b c d ν Y₂ Y₁ Y₀ : ℝ} (hξ : 0 ≤ ξ) (ha : a ≤ (2 : ℝ) ^ Y₂)
    (hb : b ≤ (2 : ℝ) ^ Y₁) (hc : c ≤ (2 : ℝ) ^ Y₀) :
    a * ξ ^ 2 + b * ξ + d * √ξ + c + ν ≤
      ξ ^ 2 * (2 : ℝ) ^ Y₂ + ξ * (2 : ℝ) ^ Y₁ + d * √ξ + (2 : ℝ) ^ Y₀ + ν := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg ξ), mul_le_mul_of_nonneg_left hb hξ]

/-- The constant `4√((L(L−1)/2 + 1)/2^128)` of Eqs. (5) and (11), from above. -/
theorem sqrt_const_le (L : ℕ) (h : sqrtOk (L * (L - 1) / 2 + 1) = true) :
    4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128) ≤
      ((4 / 2 ^ 64 * sqrtHiQ (L * (L - 1) / 2 + 1) : ℚ) : ℝ) := by
  have h2 := (sqrt_bounds h).2
  rw [sqrt_div_two_pow_128, ← cast_half_pred]
  push_cast at h2 ⊢
  linarith

theorem sqrt_two_pow_even (k : ℕ) : √((2 ^ (2 * k) : ℕ) : ℝ) = 2 ^ k := by
  rw [show ((2 ^ (2 * k) : ℕ) : ℝ) = (2 ^ k) ^ 2 by push_cast; ring, Real.sqrt_sq (by positivity)]

/-- **Claim 6.1**, Eq. (2), rounded: `ξ²/2^119.49 + ξ/2^58.83 + 2^-43.99 + ν^q_sl(ξ)`. -/
theorem claim_6_1_rounded (ξ : ℕ) :
    slQ .half ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-119.49 : ℝ) + ξ * (2 : ℝ) ^ (-58.83 : ℝ) +
      (2 : ℝ) ^ (-43.99 : ℝ) + nuSl ξ := by
  have e : slQ .half ξ = ((364 / 2 ^ 128 : ℚ) : ℝ) * (ξ : ℝ) ^ 2 +
      ((36 / 2 ^ 64 + (2 ^ 45 + 1996048) / 2 ^ 128 : ℚ) : ℝ) * ξ +
      (((2 ^ 84 + 2 ^ 44 + 2736406416) / 2 ^ 128 : ℚ) : ℝ) + nuSl ξ := by
    rw [slQ_half_eq]; push_cast; ring
  rw [e]
  exact rounded_le (by positivity) (coef_le (-11949) (by norm_num) (by decide +kernel))
    (coef_le (-5883) (by norm_num) (by decide +kernel))
    (coef_le (-4399) (by norm_num) (by decide +kernel))

/-- Eq. (4) with its coefficients. -/
theorem eq4_eq_coeffs (L ξ : ℕ) :
    eq4 L ξ = ((424 / 2 ^ 128 : ℚ) : ℝ) * (ξ : ℝ) ^ 2 +
      ((36 / 2 ^ 64 + (64 * L + 422048) / 2 ^ 128 : ℚ) : ℝ) * ξ +
      (((32 * (L : ℚ) ^ 2 + 105026400) / 2 ^ 128 : ℚ) : ℝ) + nuSf ξ := by
  unfold eq4; push_cast; ring

/-- Eq. (5) with its coefficients. -/
theorem eq5_eq_coeffs (L ξ : ℕ) :
    eq5 L ξ = ((212 / 2 ^ 128 : ℚ) : ℝ) * (ξ : ℝ) ^ 2 +
      ((18 / 2 ^ 64 + (32 * L + 211024) / 2 ^ 128 : ℚ) : ℝ) * ξ +
      4 * √(L : ℝ) / 2 ^ 64 * √(ξ : ℝ) +
      ((((16 * (L : ℚ) ^ 2 + 16 * L + 52513200) / 2 ^ 128 : ℚ) : ℝ) +
        4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128)) + nuSf ξ := by
  unfold eq5; push_cast; ring

/-- Eq. (10) with its coefficients. -/
theorem eq10_eq_coeffs (L ξ : ℕ) :
    eq10 L ξ = ((1152 / 2 ^ 128 : ℚ) : ℝ) * (ξ : ℝ) ^ 2 +
      ((104 / 2 ^ 64 + (2 ^ 46 + 64 * L + 4414144) / 2 ^ 128 : ℚ) : ℝ) * ξ +
      (((2 ^ 85 + 2 ^ 45 + 32 * (L : ℚ) ^ 2 + 5577839233) / 2 ^ 128 : ℚ) : ℝ) + nuFull 2 ξ := by
  unfold eq10; push_cast; ring

/-- Eq. (11) with its coefficients. -/
theorem eq11_eq_coeffs (L ξ : ℕ) :
    eq11 L ξ = ((576 / 2 ^ 128 : ℚ) : ℝ) * (ξ : ℝ) ^ 2 +
      ((54 / 2 ^ 64 + (2 ^ 45 + 32 * L + 2207072) / 2 ^ 128 : ℚ) : ℝ) * ξ +
      4 * √(L : ℝ) / 2 ^ 64 * √(ξ : ℝ) +
      ((((2 ^ 84 + 2 ^ 44 + 16 * (L : ℚ) ^ 2 + 16 * L + 2788919617) / 2 ^ 128 : ℚ) : ℝ) +
        4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128)) + nuFull 1 ξ := by
  unfold eq11; push_cast; ring

/-- The constant of Eq. (5) or (11) below a power of two. -/
theorem const_le {c : ℚ} (L : ℕ) {Y : ℝ} (B : ℤ) (hY : Y = (B : ℝ) / (100 : ℕ))
    (h : (sqrtOk (L * (L - 1) / 2 + 1) &&
      decide ((c + 4 / 2 ^ 64 * sqrtHiQ (L * (L - 1) / 2 + 1)) ^ 100 ≤ (2 : ℚ) ^ B)) = true) :
    (c : ℝ) + 4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128) ≤ (2 : ℝ) ^ Y := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := sqrt_const_le L h.1
  have h2 := coef_le B hY h.2
  push_cast at h1 h2
  linarith

/-- **Claim 6.2**, BXMSS-20 (`L = 2^20`), Eqs. (4) and (5) rounded:
`ξ²/2^119.27 + ξ/2^58.83 + 2^-82.99 + ν^q_sf(ξ)` and
`ξ²/2^120.27 + ξ/2^59.83 + √ξ/2^52 + 2^-42.50 + ν^q_sf(ξ)`. -/
theorem claim_6_2_rounded_bx (ξ : ℕ) :
    eq4 (2 ^ 20) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-119.27 : ℝ) + ξ * (2 : ℝ) ^ (-58.83 : ℝ) +
      (2 : ℝ) ^ (-82.99 : ℝ) + nuSf ξ ∧
    eq5 (2 ^ 20) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-120.27 : ℝ) + ξ * (2 : ℝ) ^ (-59.83 : ℝ) +
      √(ξ : ℝ) / 2 ^ 52 + (2 : ℝ) ^ (-42.50 : ℝ) + nuSf ξ := by
  have hs : 4 * √((2 ^ 20 : ℕ) : ℝ) / 2 ^ 64 = 1 / 2 ^ 52 := by
    rw [show 2 ^ 20 = 2 ^ (2 * 10) by norm_num, sqrt_two_pow_even]; norm_num
  constructor
  · rw [eq4_eq_coeffs]
    exact rounded_le (by positivity) (coef_le (-11927) (by norm_num) (by decide +kernel))
      (coef_le (-5883) (by norm_num) (by decide +kernel))
      (coef_le (-8299) (by norm_num) (by decide +kernel))
  · rw [eq5_eq_coeffs, hs]
    refine (rounded_le_sqrt (Y₂ := -120.27) (Y₁ := -59.83) (Y₀ := -42.50) (by positivity)
      (coef_le (-12027) (by norm_num) (by decide +kernel))
      (coef_le (-5983) (by norm_num) (by decide +kernel))
      (const_le _ (-4250) (by norm_num) (by decide +kernel))).trans_eq (by ring)

/-- **Claim 6.2**, UXMSS-256 (`L = 2^8`), Eqs. (4) and (5) rounded:
`ξ²/2^119.27 + ξ/2^58.83 + 2^-101.32 + ν^q_sf(ξ)` and
`ξ²/2^120.27 + ξ/2^59.83 + √ξ/2^58 + 2^-54.50 + ν^q_sf(ξ)`. -/
theorem claim_6_2_rounded_ux (ξ : ℕ) :
    eq4 (2 ^ 8) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-119.27 : ℝ) + ξ * (2 : ℝ) ^ (-58.83 : ℝ) +
      (2 : ℝ) ^ (-101.32 : ℝ) + nuSf ξ ∧
    eq5 (2 ^ 8) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-120.27 : ℝ) + ξ * (2 : ℝ) ^ (-59.83 : ℝ) +
      √(ξ : ℝ) / 2 ^ 58 + (2 : ℝ) ^ (-54.50 : ℝ) + nuSf ξ := by
  have hs : 4 * √((2 ^ 8 : ℕ) : ℝ) / 2 ^ 64 = 1 / 2 ^ 58 := by
    rw [show 2 ^ 8 = 2 ^ (2 * 4) by norm_num, sqrt_two_pow_even]; norm_num
  constructor
  · rw [eq4_eq_coeffs]
    exact rounded_le (by positivity) (coef_le (-11927) (by norm_num) (by decide +kernel))
      (coef_le (-5883) (by norm_num) (by decide +kernel))
      (coef_le (-10132) (by norm_num) (by decide +kernel))
  · rw [eq5_eq_coeffs, hs]
    refine (rounded_le_sqrt (Y₂ := -120.27) (Y₁ := -59.83) (Y₀ := -54.50) (by positivity)
      (coef_le (-12027) (by norm_num) (by decide +kernel))
      (coef_le (-5983) (by norm_num) (by decide +kernel))
      (const_le _ (-5450) (by norm_num) (by decide +kernel))).trans_eq (by ring)

/-- **Claim 6.4**, BXMSS-20, Eqs. (10) and (11) rounded:
`ξ²/2^117.83 + ξ/2^57.29 + 2^-42.99 + ν^q_2(ξ)` and
`ξ²/2^118.83 + ξ/2^58.24 + √ξ/2^52 + 2^-42.06 + ν^q_1(ξ)`. -/
theorem claim_6_4_rounded_bx (ξ : ℕ) :
    eq10 (2 ^ 20) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-117.83 : ℝ) + ξ * (2 : ℝ) ^ (-57.29 : ℝ) +
      (2 : ℝ) ^ (-42.99 : ℝ) + nuFull 2 ξ ∧
    eq11 (2 ^ 20) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-118.83 : ℝ) + ξ * (2 : ℝ) ^ (-58.24 : ℝ) +
      √(ξ : ℝ) / 2 ^ 52 + (2 : ℝ) ^ (-42.06 : ℝ) + nuFull 1 ξ := by
  have hs : 4 * √((2 ^ 20 : ℕ) : ℝ) / 2 ^ 64 = 1 / 2 ^ 52 := by
    rw [show 2 ^ 20 = 2 ^ (2 * 10) by norm_num, sqrt_two_pow_even]; norm_num
  constructor
  · rw [eq10_eq_coeffs]
    exact rounded_le (by positivity) (coef_le (-11783) (by norm_num) (by decide +kernel))
      (coef_le (-5729) (by norm_num) (by decide +kernel))
      (coef_le (-4299) (by norm_num) (by decide +kernel))
  · rw [eq11_eq_coeffs, hs]
    refine (rounded_le_sqrt (Y₂ := -118.83) (Y₁ := -58.24) (Y₀ := -42.06) (by positivity)
      (coef_le (-11883) (by norm_num) (by decide +kernel))
      (coef_le (-5824) (by norm_num) (by decide +kernel))
      (const_le _ (-4206) (by norm_num) (by decide +kernel))).trans_eq (by ring)

/-- **Claim 6.4**, UXMSS-256, Eqs. (10) and (11) rounded:
`ξ²/2^117.83 + ξ/2^57.29 + 2^-42.99 + ν^q_2(ξ)` and
`ξ²/2^118.83 + ξ/2^58.24 + √ξ/2^58 + 2^-43.99 + ν^q_1(ξ)`. -/
theorem claim_6_4_rounded_ux (ξ : ℕ) :
    eq10 (2 ^ 8) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-117.83 : ℝ) + ξ * (2 : ℝ) ^ (-57.29 : ℝ) +
      (2 : ℝ) ^ (-42.99 : ℝ) + nuFull 2 ξ ∧
    eq11 (2 ^ 8) ξ ≤ (ξ : ℝ) ^ 2 * (2 : ℝ) ^ (-118.83 : ℝ) + ξ * (2 : ℝ) ^ (-58.24 : ℝ) +
      √(ξ : ℝ) / 2 ^ 58 + (2 : ℝ) ^ (-43.99 : ℝ) + nuFull 1 ξ := by
  have hs : 4 * √((2 ^ 8 : ℕ) : ℝ) / 2 ^ 64 = 1 / 2 ^ 58 := by
    rw [show 2 ^ 8 = 2 ^ (2 * 4) by norm_num, sqrt_two_pow_even]; norm_num
  constructor
  · rw [eq10_eq_coeffs]
    exact rounded_le (by positivity) (coef_le (-11783) (by norm_num) (by decide +kernel))
      (coef_le (-5729) (by norm_num) (by decide +kernel))
      (coef_le (-4299) (by norm_num) (by decide +kernel))
  · rw [eq11_eq_coeffs, hs]
    refine (rounded_le_sqrt (Y₂ := -118.83) (Y₁ := -58.24) (Y₀ := -43.99) (by positivity)
      (coef_le (-11883) (by norm_num) (by decide +kernel))
      (coef_le (-5824) (by norm_num) (by decide +kernel))
      (const_le _ (-4399) (by norm_num) (by decide +kernel))).trans_eq (by ring)

/-! ## Claims 6.1, 6.2 and 6.4: the figures -/

/-- **Claim 6.2**, BXMSS-20: the minimum of Eqs. (4) and (5) is `2^-82.9` at `ξ = 0` and reaches `1`
at `ξ* = 2^59.2`; Eq. (4) alone reaches `1` at `2^58.4`. -/
theorem claim_6_2_figures_bx :
    (59.29 ≤ Real.logb 2 (xiStar (claimSf (2 ^ 20))) ∧
      Real.logb 2 (xiStar (claimSf (2 ^ 20))) ≤ 59.30) ∧
    (-83.00 ≤ Real.logb 2 (claimSf (2 ^ 20) 0) ∧ Real.logb 2 (claimSf (2 ^ 20) 0) ≤ -82.99) ∧
    (58.49 ≤ Real.logb 2 (xiStar (eq4 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (eq4 (2 ^ 20))) ≤ 58.50) := by
  refine ⟨logb_xiStar_bracket claim_sf_bx_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 1099514909851 / 2 ^ 123) (hi := 274878727463 / 2 ^ 121) 100
      (by norm_num) (-8300) (-8299) (by norm_num) (by norm_num)
      (le_min (Enc.ge_of_eq (eq4_eq_enc _ _) (by decide +kernel))
        (Enc.ge_of_eq (eq5_eq_enc _ _) (by decide +kernel)))
      (min_le_of_left_le <|
        Enc.le_of_eq (eq4_eq_enc _ _) (by decide +kernel))
      (by decide +kernel), ?_⟩
  rw [show eq4 (2 ^ 20) = sfQ .half .half (2 ^ 20) from
    funext fun ξ => (sfQ_half_half_eq _ ξ).symm]
  exact (table5_sf_bx_half).1

/-- **Claim 6.2**, UXMSS-256: the minimum of Eqs. (4) and (5) is `2^-101.3` at `ξ = 0` and reaches
`1` at `ξ* = 2^59.2`; Eq. (4) alone reaches `1` at `2^58.4`. -/
theorem claim_6_2_figures_ux :
    (59.29 ≤ Real.logb 2 (xiStar (claimSf (2 ^ 8))) ∧
      Real.logb 2 (xiStar (claimSf (2 ^ 8))) ≤ 59.30) ∧
    (-101.33 ≤ Real.logb 2 (claimSf (2 ^ 8) 0) ∧ Real.logb 2 (claimSf (2 ^ 8) 0) ≤ -101.32) ∧
    (58.49 ≤ Real.logb 2 (xiStar (eq4 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (eq4 (2 ^ 8))) ≤ 58.50) := by
  refine ⟨logb_xiStar_bracket claim_sf_ux_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 3347611 / 2 ^ 123) (hi := 1755112275969 / 2 ^ 142) 100
      (by norm_num) (-10133) (-10132) (by norm_num) (by norm_num)
      (le_min (Enc.ge_of_eq (eq4_eq_enc _ _) (by decide +kernel))
        (Enc.ge_of_eq (eq5_eq_enc _ _) (by decide +kernel)))
      (min_le_of_left_le <|
        Enc.le_of_eq (eq4_eq_enc _ _) (by decide +kernel))
      (by decide +kernel), ?_⟩
  rw [show eq4 (2 ^ 8) = sfQ .half .half (2 ^ 8) from
    funext fun ξ => (sfQ_half_half_eq _ ξ).symm]
  exact (table5_sf_ux_half).1

/-- **Claim 6.4**, BXMSS-20: the minimum of Eqs. (10) and (11) is `2^-42.9` at `ξ = 0` and reaches
`1` at `ξ* = 2^58.0`; Eq. (10) alone reaches `1` at `2^57.1`. -/
theorem claim_6_4_figures_bx :
    (58.01 ≤ Real.logb 2 (xiStar (claimFull (2 ^ 20))) ∧
      Real.logb 2 (xiStar (claimFull (2 ^ 20))) ≤ 58.02) ∧
    (-43.00 ≤ Real.logb 2 (claimFull (2 ^ 20) 0) ∧ Real.logb 2 (claimFull (2 ^ 20) 0) ≤ -42.99) ∧
    (57.16 ≤ Real.logb 2 (xiStar (eq10 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (eq10 (2 ^ 20))) ≤ 57.17) := by
  refine ⟨logb_xiStar_bracket claim_full_bx_mem (N := 100) (by norm_num) 5801 5802 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 549755813889 / 2 ^ 82) (hi := 1099511627779 / 2 ^ 83) 100
      (by norm_num) (-4300) (-4299) (by norm_num) (by norm_num)
      (le_min (Enc.ge_of_eq (eq10_eq_enc _ _) (by decide +kernel))
        (Enc.ge_of_eq (eq11_eq_enc _ _) (by decide +kernel)))
      (min_le_of_left_le <|
        Enc.le_of_eq (eq10_eq_enc _ _) (by decide +kernel))
      (by decide +kernel), ?_⟩
  rw [show eq10 (2 ^ 20) = fullQ .half .half .half (2 ^ 20) from
    funext fun ξ => (fullQ_half_half_half_eq _ ξ).symm]
  exact (table5_full_bx_half).1

/-- **Claim 6.4**, UXMSS-256: the minimum of Eqs. (10) and (11) is `2^-43.9` at `ξ = 0` and reaches
`1` at `ξ* = 2^58.0`; Eq. (10) alone reaches `1` at `2^57.1`. -/
theorem claim_6_4_figures_ux :
    (58.01 ≤ Real.logb 2 (xiStar (claimFull (2 ^ 8))) ∧
      Real.logb 2 (xiStar (claimFull (2 ^ 8))) ≤ 58.02) ∧
    (-44.00 ≤ Real.logb 2 (claimFull (2 ^ 8) 0) ∧ Real.logb 2 (claimFull (2 ^ 8) 0) ≤ -43.99) ∧
    (57.16 ≤ Real.logb 2 (xiStar (eq10 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (eq10 (2 ^ 8))) ≤ 57.17) := by
  refine ⟨logb_xiStar_bracket claim_full_ux_mem (N := 100) (by norm_num) 5801 5802 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 275067351287 / 2 ^ 82) (hi := 1100269405149 / 2 ^ 84) 100
      (by norm_num) (-4400) (-4399) (by norm_num) (by norm_num)
      (le_min (Enc.ge_of_eq (eq10_eq_enc _ _) (by decide +kernel))
        (Enc.ge_of_eq (eq11_eq_enc _ _) (by decide +kernel)))
      (min_le_of_right_le <|
        Enc.le_of_eq (eq11_eq_enc _ _) (by decide +kernel))
      (by decide +kernel), ?_⟩
  rw [show eq10 (2 ^ 8) = fullQ .half .half .half (2 ^ 8) from
    funext fun ξ => (fullQ_half_half_half_eq _ ξ).symm]
  exact (table5_full_ux_half).1

/-! ## Claims 6.1, 6.2 and 6.4: where the minimum switches -/

/-- Two bounds whose difference is `A ξ² + B ξ + C √ξ + D` with `A, B ≥ 0` (a convex function of
`√ξ`), ordered at `ξ = 0` and at `ξ = ξc`, and reversed at `ξc + 1`: the first is the smaller one
exactly for `ξ ≤ ξc`. -/
theorem crossover_of_convex {f₁ f₂ : ℕ → ℝ} (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ ξ : ℕ, f₁ ξ - f₂ ξ = A * (ξ : ℝ) ^ 2 + B * ξ + C * √(ξ : ℝ) + D) {ξc : ℕ}
    (h0 : f₁ 0 ≤ f₂ 0) (hc : f₁ ξc ≤ f₂ ξc) (hc' : f₂ (ξc + 1) < f₁ (ξc + 1)) :
    (∀ ξ ≤ ξc, f₁ ξ ≤ f₂ ξ) ∧ ∀ ξ, ξc < ξ → f₂ ξ < f₁ ξ := by
  set g : ℝ → ℝ := fun t => A * t ^ 4 + B * t ^ 2 + C * t + D with hg
  have hfg : ∀ ξ : ℕ, f₁ ξ - f₂ ξ = g √(ξ : ℝ) := by
    intro ξ
    have := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) ξ)
    rw [hf, hg]
    simp only
    rw [show √(ξ : ℝ) ^ 4 = (√(ξ : ℝ) ^ 2) ^ 2 by ring, this]
  have hD : D ≤ 0 := by
    have := hfg 0
    simp only [hg, Nat.cast_zero, Real.sqrt_zero] at this
    linarith
  have key : ∀ t T : ℝ, 0 ≤ t → t ≤ T → T * g t ≤ t * g T + (T - t) * D := by
    intro t T ht htT
    have hT : 0 ≤ T := ht.trans htT
    have e : t * g T + (T - t) * D - T * g t =
        A * t * T * (T ^ 3 - t ^ 3) + B * t * T * (T - t) := by
      simp only [hg]; ring
    have h3 : t ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ ht htT 3
    have : 0 ≤ A * t * T * (T ^ 3 - t ^ 3) :=
      mul_nonneg (mul_nonneg (mul_nonneg hA ht) hT) (by linarith)
    have : 0 ≤ B * t * T * (T - t) := mul_nonneg (mul_nonneg (mul_nonneg hB ht) hT) (by linarith)
    linarith
  constructor
  · intro ξ hξ
    have ht := Real.sqrt_nonneg (ξ : ℝ)
    have htT : √(ξ : ℝ) ≤ √(ξc : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hξ)
    have hgT : g √(ξc : ℝ) ≤ 0 := by rw [← hfg]; linarith
    have hgt : g √(ξ : ℝ) ≤ 0 := by
      rcases (Real.sqrt_nonneg (ξc : ℝ)).eq_or_lt with h | h
      · have h0' : √(ξ : ℝ) = 0 := le_antisymm (h ▸ htT) ht
        rw [h0']; simp only [hg]; norm_num; exact hD
      · have k := key _ _ ht htT
        by_contra hne
        push Not at hne
        nlinarith [mul_pos h hne, mul_nonneg ht (neg_nonneg.2 hgT),
          mul_nonneg (sub_nonneg.2 htT) (neg_nonneg.2 hD)]
    have := hfg ξ
    linarith
  · intro ξ hξ
    have hT1 : 0 < √((ξc + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have htT : √((ξc + 1 : ℕ) : ℝ) ≤ √(ξ : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hξ)
    have hgT : 0 < g √((ξc + 1 : ℕ) : ℝ) := by rw [← hfg]; linarith
    have k := key _ _ hT1.le htT
    have hpos : 0 < √(ξ : ℝ) := hT1.trans_le htT
    have hgt : 0 < g √(ξ : ℝ) := by
      by_contra hne
      push Not at hne
      nlinarith [mul_pos hpos hgT, mul_nonneg hT1.le (neg_nonneg.2 hne),
        mul_nonneg (sub_nonneg.2 htT) (neg_nonneg.2 hD)]
    have := hfg ξ
    linarith

/-- `log₂` of a natural number, bracketed. -/
theorem logb_nat_bracket (n : ℕ) {a b : ℝ} (A B : ℤ) (ha : a = (A : ℝ) / (100 : ℕ))
    (hb : b = (B : ℝ) / (100 : ℕ))
    (h : (decide (0 ≤ (n : ℚ)) && decide ((2 : ℚ) ^ A ≤ (n : ℚ) ^ 100) &&
      decide ((n : ℚ) ^ 100 ≤ (2 : ℚ) ^ B)) = true) :
    a ≤ Real.logb 2 n ∧ Real.logb 2 n ≤ b :=
  logb_bracket_of_le 100 (by norm_num) A B ha hb (by push_cast; rfl) (by push_cast; rfl) h

theorem eq4_sub_eq5 (L ξ : ℕ) :
    eq4 L ξ - eq5 L ξ = 212 / 2 ^ 128 * (ξ : ℝ) ^ 2 +
      (18 / 2 ^ 64 + (32 * L + 211024) / 2 ^ 128) * ξ +
      -(4 * √(L : ℝ) / 2 ^ 64) * √(ξ : ℝ) + ((16 * (L : ℝ) ^ 2 - 16 * L + 52513200) / 2 ^ 128 -
        4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128)) := by
  unfold eq4 eq5; ring

theorem eq10_sub_eq11 (L ξ : ℕ) :
    eq10 L ξ - eq11 L ξ = (576 / 2 ^ 128 + 16 * Gam) * (ξ : ℝ) ^ 2 +
      (50 / 2 ^ 64 + (2 ^ 45 + 32 * L + 2207072) / 2 ^ 128 + 64 * Gam) * ξ +
      -(4 * √(L : ℝ) / 2 ^ 64) * √(ξ : ℝ) +
      ((2 ^ 85 + 2 ^ 45 + 32 * (L : ℝ) ^ 2 + 5577839233 -
        (2 ^ 84 + 2 ^ 44 + 16 * (L : ℝ) ^ 2 + 16 * L + 2788919617)) / 2 ^ 128 -
        4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128) + 64 * Gam) := by
  unfold eq10 eq11 nuFull; ring

/-- **Claim 6.2**, BXMSS-20: the quantum minimum is Eq. (4) for `ξ ≤ 286586 ≈ 2^18.1` and Eq. (5)
above. -/
theorem claim_6_2_switch_bx :
    ((∀ ξ ≤ 286586, eq4 (2 ^ 20) ξ ≤ eq5 (2 ^ 20) ξ) ∧
      ∀ ξ, 286586 < ξ → eq5 (2 ^ 20) ξ < eq4 (2 ^ 20) ξ) ∧
    (18.12 ≤ Real.logb 2 (286586 : ℕ) ∧ Real.logb 2 (286586 : ℕ) ≤ 18.13) :=
  ⟨crossover_of_convex _ _ _ _ (by positivity) (by positivity) (eq4_sub_eq5 _)
    (Enc.le_le (eq4_eq_enc _ _) (eq5_eq_enc _ _) (by decide +kernel))
    (Enc.le_le (eq4_eq_enc _ _) (eq5_eq_enc _ _) (by decide +kernel))
    (Enc.lt_lt (eq5_eq_enc _ _) (eq4_eq_enc _ _) (by decide +kernel)),
    logb_nat_bracket 286586 1812 1813 (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- **Claim 6.2**, UXMSS-256: the quantum minimum is Eq. (4) for `ξ ≤ 69` and Eq. (5) above. -/
theorem claim_6_2_switch_ux :
    (∀ ξ ≤ 69, eq4 (2 ^ 8) ξ ≤ eq5 (2 ^ 8) ξ) ∧ ∀ ξ, 69 < ξ → eq5 (2 ^ 8) ξ < eq4 (2 ^ 8) ξ :=
  crossover_of_convex _ _ _ _ (by positivity) (by positivity) (eq4_sub_eq5 _)
    (Enc.le_le (eq4_eq_enc _ _) (eq5_eq_enc _ _) (by decide +kernel))
    (Enc.le_le (eq4_eq_enc _ _) (eq5_eq_enc _ _) (by decide +kernel))
    (Enc.lt_lt (eq5_eq_enc _ _) (eq4_eq_enc _ _) (by decide +kernel))

/-- **Claim 6.4**, BXMSS-20: the minimum switches from Eq. (10) to Eq. (11) after
`ξ = 58088 ≈ 2^15.8`. -/
theorem claim_6_4_switch_bx :
    ((∀ ξ ≤ 58088, eq10 (2 ^ 20) ξ ≤ eq11 (2 ^ 20) ξ) ∧
      ∀ ξ, 58088 < ξ → eq11 (2 ^ 20) ξ < eq10 (2 ^ 20) ξ) ∧
    (15.82 ≤ Real.logb 2 (58088 : ℕ) ∧ Real.logb 2 (58088 : ℕ) ≤ 15.83) :=
  ⟨crossover_of_convex _ _ _ _ (by have := Gam_nonneg; positivity)
    (by have := Gam_nonneg; positivity) (eq10_sub_eq11 _)
    (Enc.le_le (eq10_eq_enc _ _) (eq11_eq_enc _ _) (by decide +kernel))
    (Enc.le_le (eq10_eq_enc _ _) (eq11_eq_enc _ _) (by decide +kernel))
    (Enc.lt_lt (eq11_eq_enc _ _) (eq10_eq_enc _ _) (by decide +kernel)),
    logb_nat_bracket 58088 1582 1583 (by norm_num) (by norm_num) (by decide +kernel)⟩

/-- **Claim 6.1** (and Section 6.6): in the itsr proof the form `e = 1/2` gives the smaller bound at
`ξ = 127210908325549264 ≥ 2^56.82`, the form `e = 1` at `ξ = 128095730166168112 ≤ 2^56.83`
("up to `ξ ≈ 2^56.8`"). -/
theorem claim_6_1_switch :
    slQ .half 127210908325549264 ≤ slQ .one 127210908325549264 ∧
    slQ .one 128095730166168112 < slQ .half 128095730166168112 ∧
    56.82 ≤ Real.logb 2 (127210908325549264 : ℕ) ∧ Real.logb 2 (128095730166168112 : ℕ) ≤ 56.83 :=
  ⟨Enc.le_le (slQ_eq_enc _ _) (slQ_eq_enc _ _) (by decide +kernel),
    Enc.lt_lt (slQ_eq_enc _ _) (slQ_eq_enc _ _) (by decide +kernel),
    (logb_nat_bracket 127210908325549264 (a := 56.82) (b := 56.83) 5682 5683 (by norm_num)
      (by norm_num) (by decide +kernel)).1,
    (logb_nat_bracket 128095730166168112 (a := 56.82) (b := 56.83) 5682 5683 (by norm_num)
      (by norm_num) (by decide +kernel)).2⟩

/-! ## Section 6.1 and the abstract -/

/-- **Abstract** and **Section 6.1**: quantumly, every bound with `e = 1` and the minimum over the
forms reach `1` at `ξ* = 2^58.0` to `2^59.2` (rounded down as in Table 5): every such `log₂ ξ*`
lies in `[58.01, 59.30]`, the smallest in `[58.01, 58.02]` (full scheme) and the largest in
`[59.29, 59.30]` (stateful path). -/
theorem abstract_quantum :
    ∀ B ∈ ({slQ .one, slMin, sfQ .one .one (2 ^ 20), sfMin (2 ^ 20), sfQ .one .one (2 ^ 8),
      sfMin (2 ^ 8), fullQ .one .one .one (2 ^ 20), fullMin (2 ^ 20), fullQ .one .one .one (2 ^ 8),
      fullMin (2 ^ 8)} : Set (ℕ → ℝ)),
      58.01 ≤ Real.logb 2 (xiStar B) ∧ Real.logb 2 (xiStar B) ≤ 59.30 := by
  intro B hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := table5_sl_one.1; constructor <;> linarith
  · have := table5_sl_min.1; constructor <;> linarith
  · have := table5_sf_bx_one.1; constructor <;> linarith
  · have := table5_sf_bx_min.1; constructor <;> linarith
  · have := table5_sf_ux_one.1; constructor <;> linarith
  · have := table5_sf_ux_min.1; constructor <;> linarith
  · have := table5_full_bx_one.1; constructor <;> linarith
  · have := table5_full_bx_min.1; constructor <;> linarith
  · have := table5_full_ux_one.1; constructor <;> linarith
  · have := table5_full_ux_min.1; constructor <;> linarith

/-- **Section 6.1**: with `e = 1/2` at every place, `ξ*` loses `0.8` bits on the stateful path (both
shapes) and `0.9` bits for the full scheme (both shapes), against `e = 1`: the differences of
`log₂ ξ*` lie in `[0.79, 0.80]` and `[0.85, 0.86]`. -/
theorem section_6_1_half_loss :
    (0.79 ≤ Real.logb 2 (xiStar (sfQ .one .one (2 ^ 20))) -
        Real.logb 2 (xiStar (sfQ .half .half (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfQ .one .one (2 ^ 20))) -
        Real.logb 2 (xiStar (sfQ .half .half (2 ^ 20))) ≤ 0.80) ∧
    (0.79 ≤ Real.logb 2 (xiStar (sfQ .one .one (2 ^ 8))) -
        Real.logb 2 (xiStar (sfQ .half .half (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfQ .one .one (2 ^ 8))) -
        Real.logb 2 (xiStar (sfQ .half .half (2 ^ 8))) ≤ 0.80) ∧
    (0.85 ≤ Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 20))) -
        Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 20))) -
        Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 20))) ≤ 0.86) ∧
    (0.85 ≤ Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 8))) -
        Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 8))) -
        Real.logb 2 (xiStar (fullQ .half .half .half (2 ^ 8))) ≤ 0.86) :=
  ⟨logb_xiStar_sub_bracket sf_bx_one_mem sf_bx_half_mem (N := 100) (by norm_num) 79 80
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_ux_one_mem sf_ux_half_mem (N := 100) (by norm_num) 79 80
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_bx_one_mem full_bx_half_mem (N := 100) (by norm_num) 85 86
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_ux_one_mem full_ux_half_mem (N := 100) (by norm_num) 85 86
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Section 6.1**: the column "minimum" already attains the core value of `ξ*`: the bound over the
core terms alone reaches `1` at most `0.01` bits later (stateless; stateful and full scheme with
both shapes). -/
theorem section_6_1_core_min :
    (0.00 ≤ Real.logb 2 (xiStar slCoreQ) -
        Real.logb 2 (xiStar slMin) ∧
      Real.logb 2 (xiStar slCoreQ) -
        Real.logb 2 (xiStar slMin) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfMin (2 ^ 20))) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfMin (2 ^ 8))) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullMin (2 ^ 20))) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullMin (2 ^ 8))) ≤ 0.01) :=
  ⟨logb_xiStar_sub_bracket sl_core_mem sl_min_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_core_mem sf_bx_min_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_core_mem sf_ux_min_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_core_mem full_bx_min_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_core_mem full_ux_min_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Section 6.1**: with `e = 1` at every place, `ξ*` keeps its core value up to `0.01` bits. -/
theorem section_6_1_core_one :
    (0.00 ≤ Real.logb 2 (xiStar slCoreQ) -
        Real.logb 2 (xiStar (slQ .one)) ∧
      Real.logb 2 (xiStar slCoreQ) -
        Real.logb 2 (xiStar (slQ .one)) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfQ .one .one (2 ^ 20))) ∧
      Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfQ .one .one (2 ^ 20))) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfQ .one .one (2 ^ 8))) ∧
      Real.logb 2 (xiStar sfCoreQ) -
        Real.logb 2 (xiStar (sfQ .one .one (2 ^ 8))) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 20))) ∧
      Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 20))) ≤ 0.01) ∧
    (0.00 ≤ Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 8))) ∧
      Real.logb 2 (xiStar fullCoreQ) -
        Real.logb 2 (xiStar (fullQ .one .one .one (2 ^ 8))) ≤ 0.01) :=
  ⟨logb_xiStar_sub_bracket sl_core_mem sl_one_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_core_mem sf_bx_one_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_core_mem sf_ux_one_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_core_mem full_bx_one_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_core_mem full_ux_one_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Claim 6.1** (and Section 6.6): the form `e = 1` in the itsr proof reaches `1` at a `ξ*` at
most `0.01` bits larger than the form `e = 1/2` of Eq. (2). -/
theorem claim_6_1_one_vs_half :
    (0.00 ≤ Real.logb 2 (xiStar (slQ .one)) -
        Real.logb 2 (xiStar (slQ .half)) ∧
      Real.logb 2 (xiStar (slQ .one)) -
        Real.logb 2 (xiStar (slQ .half)) ≤ 0.01) :=
  logb_xiStar_sub_bracket sl_one_mem sl_half_mem (N := 100) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

end ShrincsSecurity.Concrete.Quantum

end
