module

public import ShrincsSecurity.Concrete.Quantum.Figures
public import ShrincsSecurity.Concrete.Figures

/-!
# The quantum comparisons of Section 6 (Remark 6.1, footnote 15, Section 6.4)

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): the quantum items of **Remark 6.1**
(lines 4821–4864, rendered pages 76–77), the quantum part of **footnote 15** (lines 5000–5004,
page 78) and the quantum items 1 and 3 of **Section 6.4** (lines 5048–5072, pages 79–80).

## The earlier bounds

Remark 6.1 switches one result back at a time. Quantumly:

* Lemma C.1 [GHHM21] at the three places of the reprogramming step: `Form.ghhm` in `slQ`, `sfQ`,
  `fullQ` (Theorem F.2 quantum line, Theorem G.1 Eq. (16), Corollary C.3 first QROM term);
* the earlier sm-ud and sm-pre bounds of the `‡` note of Table 6: `Rows.earlier`, in `slOld`,
  `sfOld`, `fullOld` and their minima over the forms (`slOldMin`, `sfOldMin`, `fullOldMin`);
* all four switched back: `slOld .ghhm`, `sfOld .ghhm .ghhm`, `fullOld .ghhm .ghhm .ghhm`.

Entries of the earlier bounds are rounded to nearest; gains are computed from the exact values and
rounded down (footnote 14).

## Results (paper → certified, `log₂ ξ*` and in parentheses `log₂ B(0)`)

* Lemma C.1: stateless `46.8 (−3.4)` → [46.81, 46.82] ([−3.42, −3.41]); stateful BXMSS-20
  `59.3 (−32.4)` → [59.29, 59.30] ([−32.42, −32.41]); UXMSS-256 `59.3 (−50.4)` → [59.29, 59.30]
  ([−50.42, −50.41]); full scheme `46.8 (−3.4)` → [46.81, 46.82] ([−3.42, −3.41]), both shapes.
* Gains of Lemma C.3: `11.7` → [11.71, 11.72] (stateless), `11.2` → [11.20, 11.21] (full, both
  shapes); stateful `ξ*` unchanged up to `0.001` bits → [0, 0.001]; floor `2^-3.4`: every bound with
  Lemma C.1 on the stateless path or for the full scheme is at least `3/32` for every `ξ`,
  `log₂(3/32) ∈ [−3.42, −3.41]`.
* Earlier sm-ud, sm-pre: `56.1 (−43.4)` → [56.08, 56.09] ([−43.39, −43.38]); `56.2 (−46.4)` →
  [56.20, 56.21] ([−46.38, −46.37]); `56.2 (−47.4)` → [56.20, 56.21] ([−47.37, −47.36]);
  `55.1 (−42.3)` → [55.14, 55.15] ([−42.30, −42.29]); `55.1 (−43.3)` → [55.14, 55.15]
  ([−43.30, −43.29]). Gains `2.4`, `3.0`, `2.8` → [2.44, 2.45], [3.09, 3.10], [2.87, 2.88].
* All four switched back: `46.8 (−3.4)` → [46.81, 46.82] (stateless), [46.80, 46.81] (full, both
  shapes), ([−3.42, −3.41]); `56.2 (−32.4)` → [56.20, 56.21] ([−32.42, −32.41]); `56.2 (−47.2)` →
  [56.20, 56.21] ([−47.21, −47.20]).
* Footnote 15, quantum: UXMSS-256 with `e = 1/2` and with the minimum, per-function charges:
  `2^-103.7` → [−103.76, −103.75].
* Section 6.4, item 1: the verification adds `(2736406384 − 300)/2^128 < 2^-96.6` (stateless) and
  `(52513168 − 148)/2^128 < 2^-102.3` (stateful) to the collection terms at `ξ = 0`. Item 3:
  `24 Γ < 2^-125.6`, `24/2^256 < 2^-251`, the randomizer part `4√(S/2^n)` grows from `q = 0` to
  `q = 1` by less than `2^-62.5` for every `p ≥ 1` (in particular `2^8`, `2^20`, `2^40`), and its
  form with `e = 1/2` by `32p/2^128 ≤ 2^-83` for `p ≤ 2^40`. With `e = 1/2` at the hop the stateful
  collection terms are doubled and the verification adds more than `2^-102.3` (at least
  `2^-101.36`) to the bound at `ξ = 0` (`section_6_4_quantum_verification_doubled`).
-/

@[expose] public section

namespace ShrincsSecurity.Concrete.Quantum

open ShrincsSecurity.Concrete ShrincsSecurity.Scheme ShrincsSecurity.ITSR.Concrete

/-! ## The earlier sm-ud and sm-pre bounds -/

/-- Theorem 4.3 (quantum) with the earlier sm-ud and sm-pre bounds of the `‡` note. -/
noncomputable def slOld (ei : Form) (ξ : ℕ) : ℝ :=
  slSumQ .earlier dsprRowQ (.uniform (Vsl shrincs)) ei ξ

/-- Theorem 4.2 (quantum) with the earlier sm-ud and sm-pre bounds. -/
noncomputable def sfOld (er eh : Form) (L ξ : ℕ) : ℝ :=
  sfSumQ .earlier (.uniform (Vsf shrincs)) er eh L ξ

/-- Theorem 4.1 (quantum, Claim 6.3) with the earlier sm-ud and sm-pre bounds. -/
noncomputable def fullOld (ei er eh : Form) (L ξ : ℕ) : ℝ :=
  fullSumQ .earlier dsprRowQ epsDs (.uniform (Vsf shrincs)) (.uniform (Vsl shrincs)) ei er eh L ξ

noncomputable def slOldMin (ξ : ℕ) : ℝ := minF fun ei => slOld ei ξ

noncomputable def sfOldMin (L ξ : ℕ) : ℝ := minF fun er => minF fun eh => sfOld er eh L ξ

noncomputable def fullOldMin (L ξ : ℕ) : ℝ :=
  minF fun ei => minF fun er => minF fun eh => fullOld ei er eh L ξ

theorem slOld_eq_enc (ei : Form) (ξ : ℕ) :
    slOld ei ξ = (slEnc .earlier (.uniform 2741) ei ξ).val := by
  rw [slOld, Vsl_shrincs, slSumQ_eq_enc]

theorem sfOld_eq_enc (er eh : Form) (L ξ : ℕ) :
    sfOld er eh L ξ = (sfEnc .earlier (.uniform 497) er eh L ξ).val := by
  rw [sfOld, Vsf_shrincs, sfSumQ_eq_enc]

theorem fullOld_eq_enc (ei er eh : Form) (L ξ : ℕ) :
    fullOld ei er eh L ξ = (fullEnc .earlier (.uniform 497) (.uniform 2741) ei er eh L ξ).val := by
  rw [fullOld, Vsf_shrincs, Vsl_shrincs, fullSumQ_eq_enc]

theorem slOld_mono (ei : Form) : Monotone (slOld ei) := slSumQ_mono _ _ _

theorem sfOld_mono (er eh : Form) (L : ℕ) : Monotone (sfOld er eh L) := sfSumQ_mono _ _ _ _ _

theorem fullOld_mono (ei er eh : Form) (L : ℕ) : Monotone (fullOld ei er eh L) :=
  fullSumQ_mono _ _ _ _ _ _ _

theorem slOldMin_mono : Monotone slOldMin := minF_mono' slOld_mono

theorem sfOldMin_mono (L : ℕ) : Monotone (sfOldMin L) :=
  minF_mono' fun er => minF_mono' fun eh => sfOld_mono er eh L

theorem fullOldMin_mono (L : ℕ) : Monotone (fullOldMin L) :=
  minF_mono' fun ei => minF_mono' fun er => minF_mono' fun eh => fullOld_mono ei er eh L

/-! ## Locating `ξ*` -/

theorem sl_ghhm_mem :
    123939963650531 < xiStar (slQ .ghhm) ∧ xiStar (slQ .ghhm) ≤ 123939963650542 :=
  xiStar_bracket (slQ_mono .ghhm)
    (Enc.lt_one_of_eq (slQ_eq_enc _ _) (by decide +kernel))
    (Enc.one_le_of_eq (slQ_eq_enc _ _) (by decide +kernel))

theorem sf_bx_ghhm_mem :
    706227966376409510 < xiStar (sfQ .ghhm .ghhm (2 ^ 20)) ∧
      xiStar (sfQ .ghhm .ghhm (2 ^ 20)) ≤ 706227966376409511 :=
  xiStar_bracket (sfQ_mono .ghhm .ghhm _)
    (Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))

theorem sf_ux_ghhm_mem :
    706305169528366816 < xiStar (sfQ .ghhm .ghhm (2 ^ 8)) ∧
      xiStar (sfQ .ghhm .ghhm (2 ^ 8)) ≤ 706305169528366817 :=
  xiStar_bracket (sfQ_mono .ghhm .ghhm _)
    (Enc.lt_one_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfQ_eq_enc _ _ _ _) (by decide +kernel))

theorem full_bx_ghhm_mem :
    123909259340173 < xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 20)) ∧
      xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 20)) ≤ 123909259340184 :=
  xiStar_bracket (fullQ_mono .ghhm .ghhm .ghhm _)
    (Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))

theorem full_ux_ghhm_mem :
    123909733646232 < xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 8)) ∧
      xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 8)) ≤ 123909733646243 :=
  xiStar_bracket (fullQ_mono .ghhm .ghhm .ghhm _)
    (Enc.lt_one_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullQ_eq_enc _ _ _ _ _) (by decide +kernel))

theorem sl_old_min_mem :
    76466023860049408 < xiStar slOldMin ∧ xiStar slOldMin ≤ 76466026070938303 :=
  xiStar_bracket slOldMin_mono
    (minF_lt_of_half <|
      Enc.lt_one_of_eq (slOld_eq_enc _ _) (by decide +kernel))
    (one_le_minF1 (fun a => slOld_eq_enc a _) (by decide +kernel))

theorem sf_bx_old_min_mem :
    82852059171883541 < xiStar (sfOldMin (2 ^ 20)) ∧
      xiStar (sfOldMin (2 ^ 20)) ≤ 82852059171883542 :=
  xiStar_bracket (sfOldMin_mono _)
    (minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))
    (one_le_minF2 (fun a b => sfOld_eq_enc a b _ _) (by decide +kernel))

theorem sf_ux_old_min_mem :
    82852064369402665 < xiStar (sfOldMin (2 ^ 8)) ∧
      xiStar (sfOldMin (2 ^ 8)) ≤ 82852064369402666 :=
  xiStar_bracket (sfOldMin_mono _)
    (minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))
    (one_le_minF2 (fun a b => sfOld_eq_enc a b _ _) (by decide +kernel))

theorem full_bx_old_min_mem :
    39845414942094336 < xiStar (fullOldMin (2 ^ 20)) ∧
      xiStar (fullOldMin (2 ^ 20)) ≤ 39845415255875890 :=
  xiStar_bracket (fullOldMin_mono _)
    (minF_lt_of_half <| minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))
    (one_le_minF3 (fun a b c => fullOld_eq_enc a b c _ _) (by decide +kernel))

theorem full_ux_old_min_mem :
    39845416676980072 < xiStar (fullOldMin (2 ^ 8)) ∧
      xiStar (fullOldMin (2 ^ 8)) ≤ 39845416990761661 :=
  xiStar_bracket (fullOldMin_mono _)
    (minF_lt_of_half <| minF_lt_of_half <| minF_lt_of_one <|
      Enc.lt_one_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))
    (one_le_minF3 (fun a b c => fullOld_eq_enc a b c _ _) (by decide +kernel))

theorem sl_old_ghhm_mem :
    123598459441903 < xiStar (slOld .ghhm) ∧ xiStar (slOld .ghhm) ≤ 123598459441914 :=
  xiStar_bracket (slOld_mono .ghhm)
    (Enc.lt_one_of_eq (slOld_eq_enc _ _) (by decide +kernel))
    (Enc.one_le_of_eq (slOld_eq_enc _ _) (by decide +kernel))

theorem sf_bx_old_ghhm_mem :
    82848009496036739 < xiStar (sfOld .ghhm .ghhm (2 ^ 20)) ∧
      xiStar (sfOld .ghhm .ghhm (2 ^ 20)) ≤ 82848009496036740 :=
  xiStar_bracket (sfOld_mono .ghhm .ghhm _)
    (Enc.lt_one_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))

theorem sf_ux_old_ghhm_mem :
    82852063461899421 < xiStar (sfOld .ghhm .ghhm (2 ^ 8)) ∧
      xiStar (sfOld .ghhm .ghhm (2 ^ 8)) ≤ 82852063461899422 :=
  xiStar_bracket (sfOld_mono .ghhm .ghhm _)
    (Enc.lt_one_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))

theorem full_bx_old_ghhm_mem :
    123229005557689 < xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 20)) ∧
      xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 20)) ≤ 123229005557699 :=
  xiStar_bracket (fullOld_mono .ghhm .ghhm .ghhm _)
    (Enc.lt_one_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))

theorem full_ux_old_ghhm_mem :
    123229474686055 < xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 8)) ∧
      xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 8)) ≤ 123229474686065 :=
  xiStar_bracket (fullOld_mono .ghhm .ghhm .ghhm _)
    (Enc.lt_one_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))
    (Enc.one_le_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))

/-! ## Remark 6.1: the entries -/

/-- **Remark 6.1**, with Lemma C.1 [GHHM21] at the three places, stateless: `46.8 (−3.4)` (entries
of the earlier bounds are rounded to nearest, footnote 14). -/
theorem remark_6_1_sl_ghhm :
    (46.81 ≤ Real.logb 2 (xiStar (slQ .ghhm)) ∧ Real.logb 2 (xiStar (slQ .ghhm)) ≤ 46.82) ∧
    (-3.42 ≤ Real.logb 2 (slQ .ghhm 0) ∧ Real.logb 2 (slQ .ghhm 0) ≤ -3.41) :=
  ⟨logb_xiStar_bracket sl_ghhm_mem (N := 100) (by norm_num) 4681 4682 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (slQ_eq_enc _ _) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, with Lemma C.1 [GHHM21], stateful, BXMSS-20: `59.3 (−32.4)`. -/
theorem remark_6_1_sf_bx_ghhm :
    (59.29 ≤ Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 20))) ≤ 59.30) ∧
    (-32.42 ≤ Real.logb 2 (sfQ .ghhm .ghhm (2 ^ 20) 0) ∧
      Real.logb 2 (sfQ .ghhm .ghhm (2 ^ 20) 0) ≤ -32.41) :=
  ⟨logb_xiStar_bracket sf_bx_ghhm_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfQ_eq_enc _ _ _ _) 100 (by norm_num) (-3242) (-3241) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, with Lemma C.1 [GHHM21], stateful, UXMSS-256: `59.3 (−50.4)`. -/
theorem remark_6_1_sf_ux_ghhm :
    (59.29 ≤ Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 8))) ≤ 59.30) ∧
    (-50.42 ≤ Real.logb 2 (sfQ .ghhm .ghhm (2 ^ 8) 0) ∧
      Real.logb 2 (sfQ .ghhm .ghhm (2 ^ 8) 0) ≤ -50.41) :=
  ⟨logb_xiStar_bracket sf_ux_ghhm_mem (N := 100) (by norm_num) 5929 5930 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfQ_eq_enc _ _ _ _) 100 (by norm_num) (-5042) (-5041) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, with Lemma C.1 [GHHM21], full scheme, BXMSS-20: `46.8 (−3.4)`. -/
theorem remark_6_1_full_bx_ghhm :
    (46.81 ≤ Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 20))) ≤ 46.82) ∧
    (-3.42 ≤ Real.logb 2 (fullQ .ghhm .ghhm .ghhm (2 ^ 20) 0) ∧
      Real.logb 2 (fullQ .ghhm .ghhm .ghhm (2 ^ 20) 0) ≤ -3.41) :=
  ⟨logb_xiStar_bracket full_bx_ghhm_mem (N := 100) (by norm_num) 4681 4682 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullQ_eq_enc _ _ _ _ _) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, with Lemma C.1 [GHHM21], full scheme, UXMSS-256: `46.8 (−3.4)`. -/
theorem remark_6_1_full_ux_ghhm :
    (46.81 ≤ Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 8))) ≤ 46.82) ∧
    (-3.42 ≤ Real.logb 2 (fullQ .ghhm .ghhm .ghhm (2 ^ 8) 0) ∧
      Real.logb 2 (fullQ .ghhm .ghhm .ghhm (2 ^ 8) 0) ≤ -3.41) :=
  ⟨logb_xiStar_bracket full_ux_ghhm_mem (N := 100) (by norm_num) 4681 4682 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullQ_eq_enc _ _ _ _ _) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, with the earlier sm-ud and sm-pre bounds (`‡` note of Table 6), stateless,
minimum over the forms: `56.1 (−43.4)`. -/
theorem remark_6_1_sl_old_min :
    (56.08 ≤ Real.logb 2 (xiStar slOldMin) ∧ Real.logb 2 (xiStar slOldMin) ≤ 56.09) ∧
    (-43.39 ≤ Real.logb 2 (slOldMin 0) ∧ Real.logb 2 (slOldMin 0) ≤ -43.38) :=
  ⟨logb_xiStar_bracket sl_old_min_mem (N := 100) (by norm_num) 5608 5609 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 1685850161153 / 2 ^ 84) (hi := 842925080577 / 2 ^ 83) 100
      (by norm_num) (-4339) (-4338) (by norm_num) (by norm_num)
      (ge_minF1 (fun a => slOld_eq_enc a _) (by decide +kernel))
      (minF_le_of_half <|
        Enc.le_of_eq (slOld_eq_enc _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Remark 6.1**, with the earlier sm-ud and sm-pre bounds, stateful, BXMSS-20: `56.2 (−46.4)`. -/
theorem remark_6_1_sf_bx_old_min :
    (56.20 ≤ Real.logb 2 (xiStar (sfOldMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfOldMin (2 ^ 20))) ≤ 56.21) ∧
    (-46.38 ≤ Real.logb 2 (sfOldMin (2 ^ 20) 0) ∧ Real.logb 2 (sfOldMin (2 ^ 20) 0) ≤ -46.37) :=
  ⟨logb_xiStar_bracket sf_bx_old_min_mem (N := 100) (by norm_num) 5620 5621 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 106325606401 / 2 ^ 83) (hi := 1701209702417 / 2 ^ 87) 100
      (by norm_num) (-4638) (-4637) (by norm_num) (by norm_num)
      (ge_minF2 (fun a b => sfOld_eq_enc a b _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <|
        Enc.le_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Remark 6.1**, with the earlier sm-ud and sm-pre bounds, stateful, UXMSS-256: `56.2 (−47.4)`.
-/
theorem remark_6_1_sf_ux_old_min :
    (56.20 ≤ Real.logb 2 (xiStar (sfOldMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfOldMin (2 ^ 8))) ≤ 56.21) ∧
    (-47.37 ≤ Real.logb 2 (sfOldMin (2 ^ 8) 0) ∧ Real.logb 2 (sfOldMin (2 ^ 8) 0) ≤ -47.36) :=
  ⟨logb_xiStar_bracket sf_ux_old_min_mem (N := 100) (by norm_num) 5620 5621 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 1713334140343 / 2 ^ 88) (hi := 214166767543 / 2 ^ 85) 100
      (by norm_num) (-4737) (-4736) (by norm_num) (by norm_num)
      (ge_minF2 (fun a b => sfOld_eq_enc a b _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_one <|
        Enc.le_of_eq (sfOld_eq_enc _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Remark 6.1**, with the earlier sm-ud and sm-pre bounds, full scheme, BXMSS-20: `55.1 (−42.3)`.
-/
theorem remark_6_1_full_bx_old_min :
    (55.14 ≤ Real.logb 2 (xiStar (fullOldMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullOldMin (2 ^ 20))) ≤ 55.15) ∧
    (-42.30 ≤ Real.logb 2 (fullOldMin (2 ^ 20) 0) ∧
      Real.logb 2 (fullOldMin (2 ^ 20) 0) ≤ -42.29) :=
  ⟨logb_xiStar_bracket full_bx_old_min_mem (N := 100) (by norm_num) 5514 5515 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 896087883777 / 2 ^ 82) (hi := 1792175767555 / 2 ^ 83) 100
      (by norm_num) (-4230) (-4229) (by norm_num) (by norm_num)
      (ge_minF3 (fun a b c => fullOld_eq_enc a b c _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <| minF_le_of_half <|
        Enc.le_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Remark 6.1**, with the earlier sm-ud and sm-pre bounds, full scheme, UXMSS-256:
`55.1 (−43.3)`. -/
theorem remark_6_1_full_ux_old_min :
    (55.14 ≤ Real.logb 2 (xiStar (fullOldMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullOldMin (2 ^ 8))) ≤ 55.15) ∧
    (-43.30 ≤ Real.logb 2 (fullOldMin (2 ^ 8) 0) ∧ Real.logb 2 (fullOldMin (2 ^ 8) 0) ≤ -43.29) :=
  ⟨logb_xiStar_bracket full_ux_old_min_mem (N := 100) (by norm_num) 5514 5515 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_le (lo := 448233386231 / 2 ^ 82) (hi := 1792933544925 / 2 ^ 84) 100
      (by norm_num) (-4330) (-4329) (by norm_num) (by norm_num)
      (ge_minF3 (fun a b c => fullOld_eq_enc a b c _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <| minF_le_of_one <|
        Enc.le_of_eq (fullOld_eq_enc _ _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-- **Remark 6.1**, all four results switched back (quantum: Lemma C.1 and the earlier sm-ud, sm-pre
bounds), stateless: `46.8 (−3.4)`. -/
theorem remark_6_1_sl_old_ghhm :
    (46.81 ≤ Real.logb 2 (xiStar (slOld .ghhm)) ∧ Real.logb 2 (xiStar (slOld .ghhm)) ≤ 46.82) ∧
    (-3.42 ≤ Real.logb 2 (slOld .ghhm 0) ∧ Real.logb 2 (slOld .ghhm 0) ≤ -3.41) :=
  ⟨logb_xiStar_bracket sl_old_ghhm_mem (N := 100) (by norm_num) 4681 4682 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (slOld_eq_enc _ _) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, all four results switched back, stateful, BXMSS-20: `56.2 (−32.4)`. -/
theorem remark_6_1_sf_bx_old_ghhm :
    (56.20 ≤ Real.logb 2 (xiStar (sfOld .ghhm .ghhm (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfOld .ghhm .ghhm (2 ^ 20))) ≤ 56.21) ∧
    (-32.42 ≤ Real.logb 2 (sfOld .ghhm .ghhm (2 ^ 20) 0) ∧
      Real.logb 2 (sfOld .ghhm .ghhm (2 ^ 20) 0) ≤ -32.41) :=
  ⟨logb_xiStar_bracket sf_bx_old_ghhm_mem (N := 100) (by norm_num) 5620 5621 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfOld_eq_enc _ _ _ _) 100 (by norm_num) (-3242) (-3241) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, all four results switched back, stateful, UXMSS-256: `56.2 (−47.2)`. -/
theorem remark_6_1_sf_ux_old_ghhm :
    (56.20 ≤ Real.logb 2 (xiStar (sfOld .ghhm .ghhm (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfOld .ghhm .ghhm (2 ^ 8))) ≤ 56.21) ∧
    (-47.21 ≤ Real.logb 2 (sfOld .ghhm .ghhm (2 ^ 8) 0) ∧
      Real.logb 2 (sfOld .ghhm .ghhm (2 ^ 8) 0) ≤ -47.20) :=
  ⟨logb_xiStar_bracket sf_ux_old_ghhm_mem (N := 100) (by norm_num) 5620 5621 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (sfOld_eq_enc _ _ _ _) 100 (by norm_num) (-4721) (-4720) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, all four results switched back, full scheme, BXMSS-20: `46.8 (−3.4)`. -/
theorem remark_6_1_full_bx_old_ghhm :
    (46.80 ≤ Real.logb 2 (xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 20))) ≤ 46.81) ∧
    (-3.42 ≤ Real.logb 2 (fullOld .ghhm .ghhm .ghhm (2 ^ 20) 0) ∧
      Real.logb 2 (fullOld .ghhm .ghhm .ghhm (2 ^ 20) 0) ≤ -3.41) :=
  ⟨logb_xiStar_bracket full_bx_old_ghhm_mem (N := 100) (by norm_num) 4680 4681 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullOld_eq_enc _ _ _ _ _) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-- **Remark 6.1**, all four results switched back, full scheme, UXMSS-256: `46.8 (−3.4)`. -/
theorem remark_6_1_full_ux_old_ghhm :
    (46.80 ≤ Real.logb 2 (xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullOld .ghhm .ghhm .ghhm (2 ^ 8))) ≤ 46.81) ∧
    (-3.42 ≤ Real.logb 2 (fullOld .ghhm .ghhm .ghhm (2 ^ 8) 0) ∧
      Real.logb 2 (fullOld .ghhm .ghhm .ghhm (2 ^ 8) 0) ≤ -3.41) :=
  ⟨logb_xiStar_bracket full_ux_old_ghhm_mem (N := 100) (by norm_num) 4680 4681 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    Enc.logb_bracket_of_eq (fullOld_eq_enc _ _ _ _ _) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by decide +kernel)⟩

/-! ## Remark 6.1: the gains -/

/-- **Remark 6.1**: Lemma C.3 adds `11.7` bits of `ξ*` on the stateless path and `11.2` bits for the
full scheme (both shapes), against Lemma C.1 at the three places (gains from the exact values,
rounded down; footnote 14). -/
theorem remark_6_1_ghhm_gain :
    (11.71 ≤ Real.logb 2 (xiStar slMin) -
        Real.logb 2 (xiStar (slQ .ghhm)) ∧
      Real.logb 2 (xiStar slMin) -
        Real.logb 2 (xiStar (slQ .ghhm)) ≤ 11.72) ∧
    (11.20 ≤ Real.logb 2 (xiStar (fullMin (2 ^ 20))) -
        Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullMin (2 ^ 20))) -
        Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 20))) ≤ 11.21) ∧
    (11.20 ≤ Real.logb 2 (xiStar (fullMin (2 ^ 8))) -
        Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullMin (2 ^ 8))) -
        Real.logb 2 (xiStar (fullQ .ghhm .ghhm .ghhm (2 ^ 8))) ≤ 11.21) :=
  ⟨logb_xiStar_sub_bracket sl_min_mem sl_ghhm_mem (N := 100) (by norm_num) 1171 1172
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_bx_min_mem full_bx_ghhm_mem (N := 100) (by norm_num) 1120 1121
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_ux_min_mem full_ux_ghhm_mem (N := 100) (by norm_num) 1120 1121
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Remark 6.1**: on the stateful path Lemma C.3 leaves `ξ*` unchanged up to `0.001` bits (both
shapes). -/
theorem remark_6_1_ghhm_sf :
    (0.000 ≤ Real.logb 2 (xiStar (sfMin (2 ^ 20))) -
        Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfMin (2 ^ 20))) -
        Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 20))) ≤ 0.001) ∧
    (0.000 ≤ Real.logb 2 (xiStar (sfMin (2 ^ 8))) -
        Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfMin (2 ^ 8))) -
        Real.logb 2 (xiStar (sfQ .ghhm .ghhm (2 ^ 8))) ≤ 0.001) :=
  ⟨logb_xiStar_sub_bracket sf_bx_min_mem sf_bx_ghhm_mem (N := 1000) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_ux_min_mem sf_ux_ghhm_mem (N := 1000) (by norm_num) 0 1
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Remark 6.1**: the quadratic sm-ud and sm-pre bounds add `2.4`, `3.0` and `2.8` bits of `ξ*` on
the stateless path, the stateful path and the full scheme (both shapes), against the earlier bounds
of the `‡` note. -/
theorem remark_6_1_old_gain :
    (2.44 ≤ Real.logb 2 (xiStar slMin) -
        Real.logb 2 (xiStar slOldMin) ∧
      Real.logb 2 (xiStar slMin) -
        Real.logb 2 (xiStar slOldMin) ≤ 2.45) ∧
    (3.09 ≤ Real.logb 2 (xiStar (sfMin (2 ^ 20))) -
        Real.logb 2 (xiStar (sfOldMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfMin (2 ^ 20))) -
        Real.logb 2 (xiStar (sfOldMin (2 ^ 20))) ≤ 3.10) ∧
    (3.09 ≤ Real.logb 2 (xiStar (sfMin (2 ^ 8))) -
        Real.logb 2 (xiStar (sfOldMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfMin (2 ^ 8))) -
        Real.logb 2 (xiStar (sfOldMin (2 ^ 8))) ≤ 3.10) ∧
    (2.87 ≤ Real.logb 2 (xiStar (fullMin (2 ^ 20))) -
        Real.logb 2 (xiStar (fullOldMin (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullMin (2 ^ 20))) -
        Real.logb 2 (xiStar (fullOldMin (2 ^ 20))) ≤ 2.88) ∧
    (2.87 ≤ Real.logb 2 (xiStar (fullMin (2 ^ 8))) -
        Real.logb 2 (xiStar (fullOldMin (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullMin (2 ^ 8))) -
        Real.logb 2 (xiStar (fullOldMin (2 ^ 8))) ≤ 2.88) :=
  ⟨logb_xiStar_sub_bracket sl_min_mem sl_old_min_mem (N := 100) (by norm_num) 244 245
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_bx_min_mem sf_bx_old_min_mem (N := 100) (by norm_num) 309 310
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket sf_ux_min_mem sf_ux_old_min_mem (N := 100) (by norm_num) 309 310
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_bx_min_mem full_bx_old_min_mem (N := 100) (by norm_num) 287 288
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket full_ux_min_mem full_ux_old_min_mem (N := 100) (by norm_num) 287 288
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-! ## Remark 6.1: the floor of Lemma C.1 -/

theorem prfTermsQ_nonneg (ξ : ℕ) : 0 ≤ prfTermsQ ξ := by
  simp only [prfTermsQ, prfQ]; positivity

theorem collSlQ_nonneg (rw : Rows) (c : SlCharge) (ξ : ℕ) : 0 ≤ collSlQ rw dsprRowQ c ξ := by
  rw [collSlQ_eq]
  cases rw <;> simp only [collSlR, Rows.udR, Rows.preR, tcrR] <;> push_cast <;> positivity

theorem collSfQ_nonneg (rw : Rows) (c : SfCharge) (ξ : ℕ) : 0 ≤ collSfQ rw c ξ := by
  rw [collSfQ_eq]
  cases rw <;> simp only [collSfR, Rows.udR, Rows.preR, tcrR, exclR] <;> push_cast <;> positivity

theorem rtcrQ_nonneg (e : Form) (L q : ℕ) : 0 ≤ rtcrQ e L q := by
  have := cast_reproSN L q
  have h0 : (0 : ℝ) ≤ reproS L q := by rw [← this]; positivity
  cases e <;> simp only [rtcrQ, smRtcrQ, mul_one] <;> positivity

theorem hopQ_nonneg (e : Form) (L ξ : ℕ) : 0 ≤ hopQ e L ξ := by
  have := cast_reproSN L ξ
  have h0 : (0 : ℝ) ≤ reproS L ξ := by rw [← this]; positivity
  cases e <;> simp only [hopQ, diReproQ] <;> positivity

/-- The itsr term with Lemma C.1 is at least `(3p/2)√(p/2^128) = 3/32` at `p = 2^40`, whatever the
query count. -/
theorem itsrSlQ_ghhm_ge (q : ℕ) : (3 / 32 : ℝ) ≤ itsrSlQ .ghhm q := by
  simp only [itsrSlQ, itsrQ]
  have h1 : (2 : ℝ) ^ 40 / 2 ^ 128 ≤ ((q : ℝ) + 2 ^ 40 + 1) / 2 ^ 128 := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    gcongr; linarith
  have h2 : √((2 : ℝ) ^ 40 / 2 ^ 128) = 1 / 2 ^ 44 := by
    rw [sqrt_div_two_pow_128, show (2 : ℝ) ^ 40 = (2 ^ 20) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  have h3 := Real.sqrt_le_sqrt h1
  rw [h2] at h3
  have hG : 0 ≤ 8 * ((q : ℝ) + 1) ^ 2 * Gam := by have := Gam_nonneg; positivity
  nlinarith

theorem slSumQ_ghhm_ge (rw : Rows) (c : SlCharge) (ξ : ℕ) :
    (3 / 32 : ℝ) ≤ slSumQ rw dsprRowQ c .ghhm ξ := by
  unfold slSumQ
  linarith [prfTermsQ_nonneg ξ, itsrSlQ_ghhm_ge (ξ + c.msg), collSlQ_nonneg rw c ξ]

theorem fullSumQ_ghhm_ge (rw : Rows) (cs : SfCharge) (cl : SlCharge) (er : Form) (L ξ : ℕ) :
    (3 / 32 : ℝ) ≤ fullSumQ rw dsprRowQ epsDs cs cl .ghhm er .ghhm L ξ := by
  unfold fullSumQ
  have : (0 : ℝ) ≤ epsDs := by unfold epsDs; positivity
  simp only [Form.factor, Rat.cast_one, one_mul]
  linarith [prfTermsQ_nonneg ξ, itsrSlQ_ghhm_ge (ξ + cl.msg), collSlQ_nonneg rw cl ξ,
    collSfQ_nonneg rw cs ξ, rtcrQ_nonneg er L (ξ + cs.msg), hopQ_nonneg .ghhm L ξ]

/-- **Remark 6.1**: with Lemma C.1 in the itsr proof, the stateless and full-scheme bounds never
drop below `3/32 = 2^-3.415`, whatever `ξ` (the `ξ`-independent floor `2^-3.4`), with the quadratic
or the earlier sm-ud and sm-pre rows. -/
theorem remark_6_1_ghhm_floor :
    (∀ ξ, (3 / 32 : ℝ) ≤ slQ .ghhm ξ) ∧ (∀ L ξ, (3 / 32 : ℝ) ≤ fullQ .ghhm .ghhm .ghhm L ξ) ∧
    (∀ ξ, (3 / 32 : ℝ) ≤ slOld .ghhm ξ) ∧ (∀ L ξ, (3 / 32 : ℝ) ≤ fullOld .ghhm .ghhm .ghhm L ξ) ∧
    (-3.42 ≤ Real.logb 2 (3 / 32) ∧ Real.logb 2 (3 / 32) ≤ -3.41) :=
  ⟨fun _ => slSumQ_ghhm_ge _ _ _, fun _ _ => fullSumQ_ghhm_ge _ _ _ _ _ _,
    fun _ => slSumQ_ghhm_ge _ _ _, fun _ _ => fullSumQ_ghhm_ge _ _ _ _ _ _,
    logb_bracket_of_le (lo := 3 / 32) (hi := 3 / 32) 100 (by norm_num) (-342) (-341) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)⟩

/-! ## Footnote 15 (quantum) -/

/-- **Footnote 15**, quantum: charging each term only the evaluations of its own function (Lemma
5.1) lowers the UXMSS-256 value at `ξ = 0` with `e = 1/2` and with the minimum over the forms to
`2^-103.7`. -/
theorem footnote_15_quantum :
    (-103.76 ≤ Real.logb 2 (sfSumQ .quad (.perFunction shrincs) .half .half (2 ^ 8) 0) ∧
      Real.logb 2 (sfSumQ .quad (.perFunction shrincs) .half .half (2 ^ 8) 0) ≤ -103.75) ∧
    (-103.76 ≤ Real.logb 2
        (minF fun er => minF fun eh => sfSumQ .quad (.perFunction shrincs) er eh (2 ^ 8) 0) ∧
      Real.logb 2
        (minF fun er => minF fun eh => sfSumQ .quad (.perFunction shrincs) er eh (2 ^ 8) 0) ≤
        -103.75) := by
  rw [SfCharge.perFunction_shrincs]
  exact ⟨Enc.logb_bracket_of_eq (sfSumQ_eq_enc _ _ _ _ _ _) 100 (by norm_num) (-10376) (-10375)
      (by norm_num) (by norm_num) (by decide +kernel),
    logb_bracket_of_le (lo := 2479093 / 2 ^ 125) (hi := 1299758710785 / 2 ^ 144) 100
      (by norm_num) (-10376) (-10375) (by norm_num) (by norm_num)
      (ge_minF2 (fun a b => sfSumQ_eq_enc _ _ a b _ _) (by decide +kernel))
      (minF_le_of_half <| minF_le_of_half <|
        Enc.le_of_eq (sfSumQ_eq_enc _ _ _ _ _ _) (by decide +kernel))
      (by decide +kernel)⟩

/-! ## Section 6.4: the verification in the quantum bounds -/

/-- **Section 6.4**, quantum item 1: charging the verification (`q := ξ + V` instead of `q := ξ`) to
the quadratic summands of the collection terms adds less than `2^-96.6` on the stateless path and
`2^-102.3` on the stateful path to their value at `ξ = 0` (before the factor `2` of a hop with
`e = 1/2`). -/
theorem section_6_4_quantum_verification :
    collSlQ .quad dsprRowQ (.uniform (Vsl shrincs)) 0 - collSlQ .quad dsprRowQ (.uniform 0) 0 <
      (2 : ℝ) ^ (-96.6 : ℝ) ∧
    collSfQ .quad (.uniform (Vsf shrincs)) 0 - collSfQ .quad (.uniform 0) 0 <
      (2 : ℝ) ^ (-102.3 : ℝ) := by
  rw [Vsl_shrincs, Vsf_shrincs, collSlQ_eq, collSlQ_eq, collSfQ_eq, collSfQ_eq, ← Rat.cast_sub,
    ← Rat.cast_sub]
  exact ⟨(coef_le (Y := -96.65) (-9665) (by norm_num) (by decide +kernel)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)),
    (coef_le (Y := -102.35) (-10235) (by norm_num) (by decide +kernel)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num))⟩

/-- **Section 6.4**, quantum item 1, for the bound itself: with `e = 1/2` at the hop (the form of the
column "minimum" at `ξ = 0` on the stateful path, Section 6.6) the collection terms are doubled
(Corollary 4.2), and the verification adds `2 (52513168 − 148)/2^128 ≥ 2^-101.36` to the value of
the stateful bound at `ξ = 0`, more than the `2^-102.3` printed in item 1. No printed entry depends
on it. -/
theorem section_6_4_quantum_verification_doubled (er : Form) (L : ℕ) :
    (2 : ℝ) ^ (-102.3 : ℝ) <
      sfSumQ .quad (.uniform (Vsf shrincs)) er .half L 0 -
        sfSumQ .quad (.uniform 0) er .half L 0 := by
  have e : sfSumQ .quad (.uniform (Vsf shrincs)) er .half L 0 -
      sfSumQ .quad (.uniform 0) er .half L 0 =
      ((2 * (collSfR .quad (.uniform 497) 0 - collSfR .quad (.uniform 0) 0) : ℚ) : ℝ) := by
    rw [Vsf_shrincs]
    simp only [sfSumQ, Form.factor, collSfQ_eq, SfCharge.uniform]
    push_cast; ring
  rw [e]
  refine (Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    (by norm_num : (-102.3 : ℝ) < -101.36)).trans_le ?_
  exact two_rpow_le_of_checkQ (N := 100) (by norm_num) (-10136) (by norm_num) (by decide +kernel)
    le_rfl (by decide +kernel)

/-- The randomizer part `4√(S/2^n)` with `S = pq + p(p−1)/2 + 1` grows from `q = 0` to `q = 1` by
less than `2^-62.5`, for every `p ≥ 1`. -/
theorem repro_growth_lt {p : ℝ} (hp : 1 ≤ p) :
    4 * √(reproS p 1 / 2 ^ 128) - 4 * √(reproS p 0 / 2 ^ 128) < (2 : ℝ) ^ (-62.5 : ℝ) := by
  rw [sqrt_div_two_pow_128, sqrt_div_two_pow_128]
  have e0 : reproS p 0 = p * (p - 1) / 2 + 1 := by simp only [reproS]; ring
  have e1 : reproS p 1 = p * (p + 1) / 2 + 1 := by simp only [reproS]; ring
  have hS0 : 1 ≤ reproS p 0 := by rw [e0]; nlinarith
  have hS1 : 1 ≤ reproS p 1 := by rw [e1]; nlinarith
  set a := √(reproS p 0) with ha_def
  set b := √(reproS p 1) with hb_def
  have ha2 : a ^ 2 = reproS p 0 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = reproS p 1 := Real.sq_sqrt (by linarith)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hab : p ^ 2 - 2 < 2 * a * b := by
    have hsq : (2 * a * b) ^ 2 = (p ^ 2 + 2) ^ 2 - p ^ 2 := by
      rw [mul_pow, mul_pow, ha2, hb2, e0, e1]; ring
    by_cases h : p ^ 2 - 2 ≤ 0
    · have : 0 < 2 * a * b := by positivity
      linarith
    · push Not at h
      have h2 : (p ^ 2 - 2) ^ 2 < (2 * a * b) ^ 2 := by rw [hsq]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hsum : 2 * p ^ 2 < (a + b) ^ 2 := by nlinarith
  have hdiff : (b - a) * (a + b) = p := by
    have : (b - a) * (a + b) = b ^ 2 - a ^ 2 := by ring
    rw [this, ha2, hb2, e0, e1]; ring
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : √2 * p < a + b := by
    have : (√2 * p) ^ 2 < (a + b) ^ 2 := by rw [mul_pow, h2]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  have hpos : 0 < a + b := by positivity
  have hba : √2 * (b - a) < 1 := by
    have : √2 * (b - a) * (a + b) < 1 * (a + b) := by
      rw [mul_assoc, hdiff]; linarith
    exact lt_of_mul_lt_mul_right this hpos.le
  have hba' : 2 * (b - a) < √2 := by
    have := mul_lt_mul_of_pos_left hba (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
    nlinarith
  have hr : (2 : ℝ) ^ (-62.5 : ℝ) = √2 / 2 ^ 63 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast 2 63, ← Real.rpow_sub (by norm_num)]
    norm_num
  rw [hr]
  have h64 : (2 : ℝ) ^ 64 = 2 * 2 ^ 63 := by norm_num
  rw [h64]
  have h63 : (0 : ℝ) < 2 ^ 63 := by positivity
  have e : 4 * (b / (2 * 2 ^ 63)) - 4 * (a / (2 * 2 ^ 63)) = 2 * (b - a) / 2 ^ 63 := by ring
  rw [e]
  exact (div_lt_div_iff_of_pos_right h63).2 hba'

/-- **Section 6.4**, quantum item 3: the message-hash terms receive its one evaluation; the
quadratic parts `8(q+1)²Γ` and `8(q+1)²/2^256` grow at `ξ = 0` by `24Γ < 2^-125.6` and
`24/2^256 < 2^-251`, the randomizer part `4√(S/2^n)` by less than `2^-62.5` for
`p ∈ {2^8, 2^20, 2^40}`, and the form with `e = 1/2` by `32p/2^128 ≤ 2^-83`. -/
theorem section_6_4_quantum_msg :
    8 * ((1 : ℝ) + 1) ^ 2 * Gam - 8 * ((0 : ℝ) + 1) ^ 2 * Gam = 24 * Gam ∧
    24 * Gam < (2 : ℝ) ^ (-125.6 : ℝ) ∧ (24 : ℝ) / 2 ^ 256 < (2 : ℝ) ^ (-251 : ℝ) ∧
    ∀ p ∈ ({2 ^ 8, 2 ^ 20, 2 ^ 40} : Set ℝ),
      4 * √(reproS p 1 / 2 ^ 128) - 4 * √(reproS p 0 / 2 ^ 128) < (2 : ℝ) ^ (-62.5 : ℝ) ∧
      32 * reproS p 1 / 2 ^ 128 - 32 * reproS p 0 / 2 ^ 128 ≤ 1 / 2 ^ 83 := by
  refine ⟨by ring, ?_, ?_, ?_⟩
  · have h := le_gamHi
    have : (24 : ℝ) * Gam ≤ ((24 * gamHi : ℚ) : ℝ) := by push_cast; linarith
    exact this.trans_lt ((coef_le (Y := -125.65) (-12565) (by norm_num)
      (by decide +kernel)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)))
  · rw [show (-251 : ℝ) = ((-251 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    have h1 : 1 ≤ p := by rcases hp with rfl | rfl | rfl <;> norm_num
    have h2 : p ≤ 2 ^ 40 := by rcases hp with rfl | rfl | rfl <;> norm_num
    refine ⟨repro_growth_lt h1, ?_⟩
    simp only [reproS]
    have : 32 * (p * 1 + p * (p - 1) / 2 + 1) / 2 ^ 128 - 32 * (p * 0 + p * (p - 1) / 2 + 1) /
        2 ^ 128 = 32 * p / 2 ^ 128 := by ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

end ShrincsSecurity.Concrete.Quantum

end
