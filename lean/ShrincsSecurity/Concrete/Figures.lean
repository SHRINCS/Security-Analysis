module

public import ShrincsSecurity.Concrete.Paths

/-!
# The classical figures of Section 6 (Table 5, Claims 6.1, 6.2, 6.4, Sections 6.1 and 6.4)

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Table 5** classical column
(lines 4804–4820), **Claims 6.1, 6.2, 6.4** classical lines (Eqs. (1), (3), (9)), the core levels
of **Section 6.1** (lines 4784–4788) and **Sections 6.6–6.7**, the constants of **Section 6.4**
(lines 4990–5045) and **footnote 15** (lines 5000–5004).

## What is certified

For a bound `B : ℕ → ℝ` of `Concrete.Paths` (`slBound`, `sfBound L`, `fullBound L`, and the core
sums), Section 6.1 reports `log₂ ξ*`, `ξ* = xiStar B` the least hash-query count at which `B`
reaches `1`, rounded **down** to two decimals, and `log₂ B(0)`, rounded **up** to one decimal
(caption of Table 5). We certify each printed `log₂ ξ* = Y` as
`Y ≤ log₂ ξ* ≤ Y + 0.01` and each value at `ξ = 0` as a bracket of `log₂ B(0)` of width `0.01`.
The lower bound `Y ≤ log₂ ξ*` says that `B(ξ) < 1` for every `ξ < 2^Y`; together with the
affine forms of Eqs. (1), (3), (9) (`claim_6_1_affine`, …), which bound the success probability by
`ξ/2^Y' + c + ν(ξ)`, this is the query-counting reading of Section 5.1.

Every certificate is an explicit pair `ξ₀ < ξ* ≤ ξ₁` (`xiStar_bracket`), with `B(ξ₀) < 1` checked
on a rational upper bound of `B` and `1 ≤ B(ξ₁)` on a rational lower bound, and `ξ₀`, `ξ₁` compared
with powers of two by the kernel. The rational bounds use `ITSR.Concrete.ShrincsSl.gammaHi` for
`Γ_j(2^40)` and, from below, `gammaLoQ 12 ≤ Γ`.

The stateless and full-scheme figures (`table5_sl`, `table5_full`, `section_6_1_core_sl`,
`section_6_1_core_full`) are statements about `slBound` and `fullBound`, which use the
**conjectured** SM-DSPR row of Table 6; the stateful figures use no conjecture beyond those of
Theorem 4.2 (which this file does not restate).

## Results (paper → certified)

* Table 5, Theorem 4.3: `122.23 (−111.4)` → `log₂ ξ* ∈ [122.23, 122.24]`,
  `log₂ B(0) ∈ [−111.41, −111.40]`.
* Table 5, Theorem 4.2, both shapes (every `L`): `122.75 (−114.2)` → `[122.75, 122.76]`,
  `[−114.29, −114.28]`.
* Table 5, Theorem 4.1, both shapes (every `L`): `121.47 (−111.2)` → `[121.47, 121.48]`,
  `[−111.23, −111.22]`.
* Eqs. (1), (3), (9): `ξ/2^122.24 + 2^-111.40`, `ξ/2^122.75 + 2^-114.28`, `ξ/2^121.47 + 2^-111.22`
  (plus `ν`).
* Section 6.1 core levels `122.23, 122.83, 121.50` → `[122.23, 122.24]`, `[122.83, 122.84]`,
  `[121.50, 121.51]`; the reprogramming terms cost less than `0.1` bits on every path.
* Section 6.4: `c₀,sf ≤ 2^-125.19`, `c₀,sl ≤ 2^-124.51`, `c_V,sf ≤ 2^-114.28`,
  `c_V,sl ≤ 2^-111.40`, `c_V ≤ 2^-111.22`, `c₀ ≤ 2^-123.81`, and the crossovers `≈ 353`, `≈ 1827`.
* Footnote 15: `5571` and `77162` units; values at `ξ = 0`: `2^-111.7`, `2^-115.5`, `2^-111.6`.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete

open ShrincsSecurity.ITSR ShrincsSecurity.ITSR.Concrete ShrincsSecurity.Scheme

/-! ## Rational enclosures -/

/-- Upper bound on `Γ` (`ShrincsSl.gammaHi 10`). -/
def gamHiQ : ℚ := ShrincsSl.gammaHi 10

/-- Lower bound on `Γ` (`gammaLoQ 12`). -/
def gamLoQ : ℚ := gammaLoQ 12

/-- Upper bound on the pull part at one query, `P_{45,10,2^13}(1, 2^40)`. -/
def pull1Q : ℚ := pullSumQ ShrincsSl.gammaHi (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128)

theorem Gam_le_hi : Gam ≤ gamHiQ := ShrincsSl.gamma_le 10 le_rfl

theorem lo_le_Gam : (gamLoQ : ℝ) ≤ Gam := gammaLo_le_Gam

theorem pull1_le : pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) ≤ pull1Q :=
  pullSum_le_Q ShrincsSl.theta_eq (by norm_num) ShrincsSl.gamma_le 1 _

theorem add_two_mul_Gam_le_itsrSl (ξ : ℕ) : ((ξ : ℝ) + 2) * Gam ≤ itsrSl (ξ + 1) := by
  have := mul_Gam_le_itsrSl (ξ + 1)
  push_cast at this
  linarith

theorem add_two_mul_lo_le (ξ : ℕ) : ((ξ : ℝ) + 2) * (gamLoQ : ℝ) ≤ ((ξ : ℝ) + 2) * Gam := by
  have := lo_le_Gam
  gcongr

/-- Stateless: upper enclosure of `slBound`. -/
def slHiQ (ξ : ℕ) : ℚ := (54 * ξ + 98687) / 2 ^ 128 + itsrSlQ (ξ + 1)

/-- Stateless: lower enclosure of `slBound`. -/
def slLoQ (ξ : ℕ) : ℚ := (54 * ξ + 98687) / 2 ^ 128 + (ξ + 2) * gamLoQ

theorem slBound_le_Q (ξ : ℕ) : slBound ξ ≤ slHiQ ξ := by
  rw [slBound_eq, slHiQ]; push_cast; linarith [itsrSl_le_Q (ξ + 1)]

theorem Q_le_slBound (ξ : ℕ) : (slLoQ ξ : ℝ) ≤ slBound ξ := by
  rw [slBound_eq, slLoQ]; push_cast
  linarith [add_two_mul_Gam_le_itsrSl ξ, add_two_mul_lo_le ξ]

/-- Full scheme: upper enclosure of `fullBound L`. -/
def fullHiQ (ξ : ℕ) : ℚ :=
  (92 * ξ + 112115) / 2 ^ 128 + itsrSlQ (ξ + 1) + (ξ + 12) / 2 ^ 256

/-- Full scheme: lower enclosure of `fullBound L`. -/
def fullLoQ (ξ : ℕ) : ℚ := (92 * ξ + 112115) / 2 ^ 128 + (ξ + 2) * gamLoQ + (ξ + 12) / 2 ^ 256

theorem fullBound_le_Q (L ξ : ℕ) : fullBound L ξ ≤ fullHiQ ξ := by
  rw [fullBound_eq, fullHiQ]; push_cast; linarith [itsrSl_le_Q (ξ + 1)]

theorem Q_le_fullBound (L ξ : ℕ) : (fullLoQ ξ : ℝ) ≤ fullBound L ξ := by
  rw [fullBound_eq, fullLoQ]; push_cast
  linarith [add_two_mul_Gam_le_itsrSl ξ, add_two_mul_lo_le ξ]

/-- Stateful: `sfBound L` is rational. -/
def sfQ (ξ : ℕ) : ℚ := (38 * ξ + 13427) / 2 ^ 128 + (ξ + 2) / 2 ^ 256

theorem sfBound_eq_Q (L ξ : ℕ) : sfBound L ξ = sfQ ξ := by
  rw [sfBound_eq, sfQ]; push_cast; ring

/-- Stateful core terms (rational). -/
def sfCoreQ (ξ : ℕ) : ℚ := (36 * ξ + 13426) / 2 ^ 128 + (ξ + 2) / 2 ^ 256

theorem sfCore_eq_Q (ξ : ℕ) : sfCore ξ = sfCoreQ ξ := by
  rw [sfCore_eq, sfCoreQ]; push_cast; ring

/-- Stateless core terms: enclosures. -/
def slCoreHiQ (ξ : ℕ) : ℚ := (54 * ξ + 98687) / 2 ^ 128 + (ξ + 2) * gamHiQ

def slCoreLoQ (ξ : ℕ) : ℚ := (54 * ξ + 98687) / 2 ^ 128 + (ξ + 2) * gamLoQ

theorem slCore_le_Q (ξ : ℕ) : slCore ξ ≤ slCoreHiQ ξ := by
  have : ((ξ : ℝ) + 2) * Gam ≤ ((ξ : ℝ) + 2) * (gamHiQ : ℝ) := by
    have := Gam_le_hi
    gcongr
  rw [slCore_eq, slCoreHiQ]; push_cast; linarith

theorem Q_le_slCore (ξ : ℕ) : (slCoreLoQ ξ : ℝ) ≤ slCore ξ := by
  rw [slCore_eq, slCoreLoQ]; push_cast; linarith [add_two_mul_lo_le ξ]

/-- Full-scheme core terms: enclosures. -/
def fullCoreHiQ (ξ : ℕ) : ℚ :=
  (90 * ξ + 112114) / 2 ^ 128 + (ξ + 2) * gamHiQ + (ξ + 12) / 2 ^ 256

def fullCoreLoQ (ξ : ℕ) : ℚ :=
  (90 * ξ + 112114) / 2 ^ 128 + (ξ + 2) * gamLoQ + (ξ + 12) / 2 ^ 256

theorem fullCore_le_Q (ξ : ℕ) : fullCore ξ ≤ fullCoreHiQ ξ := by
  have : ((ξ : ℝ) + 2) * Gam ≤ ((ξ : ℝ) + 2) * (gamHiQ : ℝ) := by
    have := Gam_le_hi
    gcongr
  rw [fullCore_eq, fullCoreHiQ]; push_cast; linarith

theorem Q_le_fullCore (ξ : ℕ) : (fullCoreLoQ ξ : ℝ) ≤ fullCore ξ := by
  rw [fullCore_eq, fullCoreLoQ]; push_cast; linarith [add_two_mul_lo_le ξ]

/-! ## Locating `ξ*` -/

/-- `slBound` is below `1` at this count. -/
def slXi₀ : ℕ := 6275786868185655950290523831710271370
/-- `slBound` is at least `1` at this count. -/
def slXi₁ : ℕ := 6276892498546498333867963697029742403

theorem sl_xiStar_mem : slXi₀ < xiStar slBound ∧ xiStar slBound ≤ slXi₁ :=
  xiStar_bracket slBound_mono (lt_one_of_Q (slBound_le_Q _) (by decide +kernel))
    (one_le_of_Q (Q_le_slBound _) (by decide +kernel))

def sfXi₀ : ℕ := 8954799129498380617457226511362321000

/-- For the stateful bound the two counts are adjacent: `ξ* = sfXi₀ + 1` exactly. -/
theorem sf_xiStar_mem (L : ℕ) : sfXi₀ < xiStar (sfBound L) ∧ xiStar (sfBound L) ≤ sfXi₀ + 1 :=
  xiStar_bracket (sfBound_mono L) (lt_one_of_Q (sfBound_eq_Q L _).le (by decide +kernel))
    (one_le_of_Q (sfBound_eq_Q L _).ge (by decide +kernel))

def fullXi₀ : ℕ := 3689996047137222405443365604348987053
def fullXi₁ : ℕ := 3690221208158343457981074793678139710

theorem full_xiStar_mem (L : ℕ) : fullXi₀ < xiStar (fullBound L) ∧ xiStar (fullBound L) ≤ fullXi₁ :=
  xiStar_bracket (fullBound_mono L) (lt_one_of_Q (fullBound_le_Q L _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullBound L _) (by decide +kernel))

def slCoreXi₀ : ℕ := 6276880259195306544618192559738225194

theorem slCore_xiStar_mem : slCoreXi₀ < xiStar slCore ∧ xiStar slCore ≤ slXi₁ :=
  xiStar_bracket slCore_mono (lt_one_of_Q (slCore_le_Q _) (by decide +kernel))
    (one_le_of_Q (Q_le_slCore _) (by decide +kernel))

def sfCoreXi₀ : ℕ := 9452287970026068429538183539771338834

theorem sfCore_xiStar_mem : sfCoreXi₀ < xiStar sfCore ∧ xiStar sfCore ≤ sfCoreXi₀ + 1 :=
  xiStar_bracket sfCore_mono (lt_one_of_Q (sfCore_eq_Q _).le (by decide +kernel))
    (one_le_of_Q (sfCore_eq_Q _).ge (by decide +kernel))

def fullCoreXi₀ : ℕ := 3772029067186275658063457071709560130
def fullCoreXi₁ : ℕ := 3772033487167577993069483923254954054

theorem fullCore_xiStar_mem :
    fullCoreXi₀ < xiStar fullCore ∧ xiStar fullCore ≤ fullCoreXi₁ :=
  xiStar_bracket fullCore_mono (lt_one_of_Q (fullCore_le_Q _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullCore _) (by decide +kernel))

/-! ## Table 5, classical column -/

/-- **Table 5**, Theorem 4.3 (stateless), classical: `122.23 (−111.4)`; **Claim 6.1**: the bound is
`2^-111.4` at `ξ = 0` and reaches `1` at `ξ = 2^122.23`. Rests on the conjectured SM-DSPR row. -/
theorem table5_sl :
    (122.23 ≤ Real.logb 2 (xiStar slBound) ∧ Real.logb 2 (xiStar slBound) ≤ 122.24) ∧
    (-111.41 ≤ Real.logb 2 (slBound 0) ∧ Real.logb 2 (slBound 0) ≤ -111.40) :=
  ⟨logb_xiStar_bracket sl_xiStar_mem (N := 100) (by norm_num) 12223 12224 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-11141) (-11140) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_slBound 0) (slBound_le_Q 0) (by decide +kernel)
      (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.2 (stateful), classical, BXMSS-20 and UXMSS-256 (indeed every `L`):
`122.75 (−114.2)`; **Claim 6.2**: `2^-114.2` at `ξ = 0`, reaches `1` at `ξ = 2^122.75`. -/
theorem table5_sf (L : ℕ) :
    (122.75 ≤ Real.logb 2 (xiStar (sfBound L)) ∧ Real.logb 2 (xiStar (sfBound L)) ≤ 122.76) ∧
    (-114.29 ≤ Real.logb 2 (sfBound L 0) ∧ Real.logb 2 (sfBound L 0) ≤ -114.28) :=
  ⟨logb_xiStar_bracket (sf_xiStar_mem L) (N := 100) (by norm_num) 12275 12276 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-11429) (-11428) (by norm_num) (by norm_num)
      (by decide +kernel) (sfBound_eq_Q L 0).ge (sfBound_eq_Q L 0).le (by decide +kernel)
      (by decide +kernel)⟩

/-- **Table 5**, Theorem 4.1 (full scheme), classical, BXMSS-20 and UXMSS-256 (indeed every `L`):
`121.47 (−111.2)`; **Claim 6.4**: `2^-111.2` at `ξ = 0`, reaches `1` at `ξ = 2^121.47`. Rests on
the conjectured SM-DSPR row. -/
theorem table5_full (L : ℕ) :
    (121.47 ≤ Real.logb 2 (xiStar (fullBound L)) ∧
      Real.logb 2 (xiStar (fullBound L)) ≤ 121.48) ∧
    (-111.23 ≤ Real.logb 2 (fullBound L 0) ∧ Real.logb 2 (fullBound L 0) ≤ -111.22) :=
  ⟨logb_xiStar_bracket (full_xiStar_mem L) (N := 100) (by norm_num) 12147 12148 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-11123) (-11122) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_fullBound L 0) (fullBound_le_Q L 0) (by decide +kernel)
      (by decide +kernel)⟩

/-! ## The affine forms of Eqs. (1), (3) and (9) -/

/-- **Claim 6.1**, Eq. (1): `(54 ξ + 98687)/2^128 + ν ≤ ξ/2^122.24 + 2^-111.40 + ν`, with
`ν = ν^sl_c(ξ) = itsrSl (ξ + 1) = (ξ + 2) Γ + P_{45,10,2^13}(ξ + 1, 2^40)`. -/
theorem claim_6_1_affine (ξ : ℕ) :
    slBound ξ ≤ ξ * (2 : ℝ) ^ (-122.24 : ℝ) + (2 : ℝ) ^ (-111.40 : ℝ) + itsrSl (ξ + 1) := by
  have h1 : (54 / 2 ^ 128 : ℝ) ≤ (2 : ℝ) ^ (-122.24 : ℝ) :=
    le_two_rpow_of_check (x := 54 / 2 ^ 128) (N := 100) (by norm_num) (-12224) (by norm_num)
      (by push_cast; rfl) (by decide +kernel)
  have h2 : (98687 / 2 ^ 128 : ℝ) ≤ (2 : ℝ) ^ (-111.40 : ℝ) :=
    le_two_rpow_of_check (x := 98687 / 2 ^ 128) (N := 100) (by norm_num) (-11140) (by norm_num)
      (by push_cast; rfl) (by decide +kernel)
  have h3 : (ξ : ℝ) * (54 / 2 ^ 128) ≤ ξ * (2 : ℝ) ^ (-122.24 : ℝ) := by gcongr
  rw [slBound_eq]
  linarith

/-- **Claim 6.2**, Eq. (3): `(38 ξ + 13427)/2^128 + ν ≤ ξ/2^122.75 + 2^-114.28 + ν`,
`ν = ν^sf_c(ξ) = (ξ + 2)/2^256`, for every `L`. -/
theorem claim_6_2_affine (L ξ : ℕ) :
    sfBound L ξ ≤ ξ * (2 : ℝ) ^ (-122.75 : ℝ) + (2 : ℝ) ^ (-114.28 : ℝ) + (ξ + 2) / 2 ^ 256 := by
  have h1 : (38 / 2 ^ 128 : ℝ) ≤ (2 : ℝ) ^ (-122.75 : ℝ) :=
    le_two_rpow_of_check (x := 38 / 2 ^ 128) (N := 100) (by norm_num) (-12275) (by norm_num)
      (by push_cast; rfl) (by decide +kernel)
  have h2 : (13427 / 2 ^ 128 : ℝ) ≤ (2 : ℝ) ^ (-114.28 : ℝ) :=
    le_two_rpow_of_check (x := 13427 / 2 ^ 128) (N := 100) (by norm_num) (-11428) (by norm_num)
      (by push_cast; rfl) (by decide +kernel)
  have h3 : (ξ : ℝ) * (38 / 2 ^ 128) ≤ ξ * (2 : ℝ) ^ (-122.75 : ℝ) := by gcongr
  rw [sfBound_eq]
  linarith

/-- **Claim 6.4**, Eq. (9): `(92 ξ + 112115)/2^128 + ν ≤ ξ/2^121.47 + 2^-111.22 + ν`,
`ν = ν^full_c(ξ) = itsrSl (ξ + 1) + (ξ + 12)/2^256`, for every `L`. -/
theorem claim_6_4_affine (L ξ : ℕ) :
    fullBound L ξ ≤ ξ * (2 : ℝ) ^ (-121.47 : ℝ) + (2 : ℝ) ^ (-111.22 : ℝ) + itsrSl (ξ + 1) +
      (ξ + 12) / 2 ^ 256 := by
  have h1 : (92 / 2 ^ 128 : ℝ) ≤ (2 : ℝ) ^ (-121.47 : ℝ) :=
    le_two_rpow_of_check (x := 92 / 2 ^ 128) (N := 100) (by norm_num) (-12147) (by norm_num)
      (by push_cast; rfl) (by decide +kernel)
  have h2 : (112115 / 2 ^ 128 : ℝ) ≤ (2 : ℝ) ^ (-111.22 : ℝ) :=
    le_two_rpow_of_check (x := 112115 / 2 ^ 128) (N := 100) (by norm_num) (-11122)
      (by norm_num) (by push_cast; rfl) (by decide +kernel)
  have h3 : (ξ : ℝ) * (92 / 2 ^ 128) ≤ ξ * (2 : ℝ) ^ (-121.47 : ℝ) := by gcongr
  rw [fullBound_eq]
  linarith

/-! ## Section 6.1: the core terms -/

/-- **Section 6.1**: the stateless core terms give `122.23` bits. Rests on the conjectured SM-DSPR
row. -/
theorem section_6_1_core_sl :
    122.23 ≤ Real.logb 2 (xiStar slCore) ∧ Real.logb 2 (xiStar slCore) ≤ 122.24 :=
  logb_xiStar_bracket slCore_xiStar_mem (N := 100) (by norm_num) 12223 12224 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **Section 6.1** (and Section 6.6): the stateful core terms give `122.83` bits. -/
theorem section_6_1_core_sf :
    122.83 ≤ Real.logb 2 (xiStar sfCore) ∧ Real.logb 2 (xiStar sfCore) ≤ 122.84 :=
  logb_xiStar_bracket sfCore_xiStar_mem (N := 100) (by norm_num) 12283 12284 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **Section 6.1** (and Section 6.7): the full-scheme core terms give `121.50` bits. Rests on the
conjectured SM-DSPR row. -/
theorem section_6_1_core_full :
    121.50 ≤ Real.logb 2 (xiStar fullCore) ∧ Real.logb 2 (xiStar fullCore) ≤ 121.51 :=
  logb_xiStar_bracket fullCore_xiStar_mem (N := 100) (by norm_num) 12150 12151 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem logb_xiStar_le_of_le {B B' : ℕ → ℝ} (h : ∀ ξ, B ξ ≤ B' ξ) {ξ₀ ξ₁ : ℕ}
    (h₁ : 1 ≤ B ξ₁) (h₀ : ξ₀ < xiStar B') :
    Real.logb 2 (xiStar B') ≤ Real.logb 2 (xiStar B) :=
  Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (Nat.zero_le ξ₀).trans_lt h₀)
    (by exact_mod_cast xiStar_anti h h₁)

/-- **Section 6.1**: the reprogramming terms add less than `0.1` bits on every path:
`0 ≤ log₂ ξ*(core) − log₂ ξ*(bound) < 0.1`. -/
theorem section_6_1_repro_cost (L : ℕ) :
    (0 ≤ Real.logb 2 (xiStar slCore) - Real.logb 2 (xiStar slBound) ∧
      Real.logb 2 (xiStar slCore) - Real.logb 2 (xiStar slBound) < 0.1) ∧
    (0 ≤ Real.logb 2 (xiStar sfCore) - Real.logb 2 (xiStar (sfBound L)) ∧
      Real.logb 2 (xiStar sfCore) - Real.logb 2 (xiStar (sfBound L)) < 0.1) ∧
    (0 ≤ Real.logb 2 (xiStar fullCore) - Real.logb 2 (xiStar (fullBound L)) ∧
      Real.logb 2 (xiStar fullCore) - Real.logb 2 (xiStar (fullBound L)) < 0.1) := by
  have hsl : ∀ ξ, slCore ξ ≤ slBound ξ := fun ξ => by
    rw [slBound_eq_core_add_repro]; linarith [pullSl_nonneg (ξ + 1)]
  have hsf : ∀ ξ, sfCore ξ ≤ sfBound L ξ := fun ξ => by
    have : 0 ≤ sfRepro L ξ := by
      unfold sfRepro smRtcrRand hop diReproBound; norm_num; positivity
    rw [sfBound_eq_core_add_repro]; linarith
  have hfull : ∀ ξ, fullCore ξ ≤ fullBound L ξ := fun ξ => by
    have h1 : 0 ≤ sfRepro L ξ := by
      unfold sfRepro smRtcrRand hop diReproBound; norm_num; positivity
    have h2 := add_nonneg h1 (pullSl_nonneg (ξ + 1))
    rw [fullBound_eq_core_add_repro]
    unfold sfRepro at h2
    calc fullCore ξ ≤ fullCore ξ + (smRtcrRand (2 ^ 128) 1 L (ξ + 1) + hop ξ +
          pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (ξ + 1) (2 ^ 128)) :=
          le_add_of_nonneg_right h2
      _ = _ := by ring
  have a1 := logb_xiStar_le_of_le hsl (one_le_of_Q (Q_le_slCore slXi₁) (by decide +kernel))
    sl_xiStar_mem.1
  have a2 := logb_xiStar_le_of_le hsf
    (one_le_of_Q (sfCore_eq_Q (sfCoreXi₀ + 1)).ge (by decide +kernel)) (sf_xiStar_mem L).1
  have a3 := logb_xiStar_le_of_le hfull
    (one_le_of_Q (Q_le_fullCore fullCoreXi₁) (by decide +kernel)) (full_xiStar_mem L).1
  have b1 := (table5_sl).1
  have b2 := (table5_sf L).1
  have b3 := (table5_full L).1
  have c1 := section_6_1_core_sl
  have c2 := section_6_1_core_sf
  have c3 := section_6_1_core_full
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ## Section 6.4: the additive constants -/

/-- **Section 6.4**: `c₀,sf ≤ 2^-125.19`, `c_V,sf ≤ 2^-114.28`, `c₀,sl ≤ 2^-124.51`,
`c_V,sl ≤ 2^-111.40`, `c₀ ≤ 2^-123.81` and `c_V ≤ 2^-111.22` (the last two for the full
scheme). -/
theorem section_6_4_constants :
    c0Sf ≤ (2 : ℝ) ^ (-125.19 : ℝ) ∧ cVSf ≤ (2 : ℝ) ^ (-114.28 : ℝ) ∧
    c0Sl ≤ (2 : ℝ) ^ (-124.51 : ℝ) ∧ cVSl ≤ (2 : ℝ) ^ (-111.40 : ℝ) ∧
    c0Full ≤ (2 : ℝ) ^ (-123.81 : ℝ) ∧ cVFull ≤ (2 : ℝ) ^ (-111.22 : ℝ) := by
  have hG := Gam_le_hi
  have hP := pull1_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_two_rpow_of_check (x := 7 / 2 ^ 128 + 1 / 2 ^ 256) (N := 100) (by norm_num)
      (-12519) (by norm_num) (by rw [c0Sf]; push_cast; rfl) (by decide +kernel)
  · exact le_two_rpow_of_check (x := 13420 / 2 ^ 128 + 1 / 2 ^ 256) (N := 100) (by norm_num)
      (-11428) (by norm_num) (by rw [cVSf]; push_cast; norm_num) (by decide +kernel)
  · exact le_two_rpow_of_check (x := 11 / 2 ^ 128 + gamHiQ) (N := 100) (by norm_num)
      (-12451) (by norm_num) (by rw [c0Sl]; push_cast; linarith) (by decide +kernel)
  · exact le_two_rpow_of_check (x := 98676 / 2 ^ 128 + gamHiQ + pull1Q) (N := 100)
      (by norm_num) (-11140) (by norm_num) (by rw [cVSl]; push_cast; linarith)
      (by decide +kernel)
  · exact le_two_rpow_of_check (x := 18 / 2 ^ 128 + gamHiQ + 1 / 2 ^ 256) (N := 100)
      (by norm_num) (-12381) (by norm_num) (by rw [c0Full]; push_cast; linarith)
      (by decide +kernel)
  · exact le_two_rpow_of_check (x := 112096 / 2 ^ 128 + 1 / 2 ^ 256 + gamHiQ + pull1Q)
      (N := 100) (by norm_num) (-11122) (by norm_num)
      (by rw [cVFull, cVSf, cVSl]; push_cast; linarith) (by decide +kernel)

/-- **Section 6.4**: the constant `c_V` dominates the linear part `a ξ/2^128` for
`ξ < c_V 2^128/a`, i.e. up to about `353` queries on the stateful path (`a = 38`) and about `1827`
on the stateless path (`a = 54`). -/
theorem section_6_4_crossover :
    (353 : ℝ) < cVSf * 2 ^ 128 / 38 ∧ cVSf * 2 ^ 128 / 38 < 354 ∧
    (1827 : ℝ) < cVSl * 2 ^ 128 / 54 ∧ cVSl * 2 ^ 128 / 54 < 1828 := by
  have hG := Gam_le_hi
  have hG0 := Gam_nonneg
  have hP := pull1_le
  have hP0 := pullSl_nonneg 1
  have hGq : (gamHiQ : ℝ) ≤ 1 / 2 ^ 130 := by
    have := (Rat.cast_le (K := ℝ)).mpr (show gamHiQ ≤ 1 / 2 ^ 130 by decide +kernel)
    push_cast at this
    exact this
  have hPq : (pull1Q : ℝ) ≤ 1 / 2 ^ 250 := by
    have := (Rat.cast_le (K := ℝ)).mpr (show pull1Q ≤ 1 / 2 ^ 250 by decide +kernel)
    push_cast at this
    exact this
  rw [cVSf, cVSl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith
  · rw [div_lt_iff₀ (by norm_num)]; nlinarith

/-! ## Footnote 15: per-function charges -/

theorem SfCharge.perFunction_shrincs :
    SfCharge.perFunction shrincs = ⟨1, 1, 240, 1, 255, 256⟩ := by
  have h := shrincs_verification
  simp only [SfCharge.perFunction, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1]

theorem SlCharge.perFunction_shrincs : SlCharge.perFunction shrincs = ⟨1, 2560, 175, 1, 5⟩ := by
  have h := shrincs_verification
  simp only [SlCharge.perFunction, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]

/-- **Footnote 15**: charging each term only the evaluations of its own function gives `5571`
units (stateful) instead of `13420`, and `77162` (stateless) instead of `98676`. -/
theorem footnote_15_units (L : ℕ) :
    sfSum (.perFunction shrincs) 0 L 0 - sfSum .zero 0 L 0 = 5571 / 2 ^ 128 + 1 / 2 ^ 256 ∧
    slSum dsprRow (.perFunction shrincs) 0 0 - slSum dsprRow .zero 0 0 =
      77162 / 2 ^ 128 + Gam + pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) := by
  rw [SfCharge.perFunction_shrincs, SlCharge.perFunction_shrincs, sfSum_eq, sfSum_eq, slSum_eq,
    slSum_eq]
  simp only [SfCharge.zero, SlCharge.zero]
  push_cast
  simp only [zero_add, add_zero, itsrSl_zero]
  rw [itsrSl_eq]
  push_cast
  constructor <;> ring

/-- **Footnote 15**: with per-function charges the classical values at `ξ = 0` of Table 5 would be
`2^-111.7` (stateless), `2^-115.5` (stateful) and `2^-111.6` (full scheme); certified as brackets
of width `0.01` of `log₂`. -/
theorem footnote_15_values (L : ℕ) :
    (-111.77 ≤ Real.logb 2 (slSum dsprRow (.perFunction shrincs) 0 0) ∧
      Real.logb 2 (slSum dsprRow (.perFunction shrincs) 0 0) ≤ -111.76) ∧
    (-115.56 ≤ Real.logb 2 (sfSum (.perFunction shrincs) 0 L 0) ∧
      Real.logb 2 (sfSum (.perFunction shrincs) 0 L 0) ≤ -115.55) ∧
    (-111.67 ≤ Real.logb 2
        (fullSum dsprRow epsDs (.perFunction shrincs) (.perFunction shrincs) L 0) ∧
      Real.logb 2 (fullSum dsprRow epsDs (.perFunction shrincs) (.perFunction shrincs) L 0) ≤
        -111.66) := by
  have hG := Gam_le_hi
  have hGl := lo_le_Gam
  have hP := pull1_le
  have hP0 := pullSl_nonneg 1
  have esl : slSum dsprRow (.perFunction shrincs) 0 0 =
      77173 / 2 ^ 128 + 2 * Gam + pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) := by
    rw [SlCharge.perFunction_shrincs, slSum_eq, itsrSl_eq]; push_cast; ring
  have esf : sfSum (.perFunction shrincs) 0 L 0 = 5578 / 2 ^ 128 + 2 / 2 ^ 256 := by
    rw [SfCharge.perFunction_shrincs, sfSum_eq]; push_cast; ring
  have efull : fullSum dsprRow epsDs (.perFunction shrincs) (.perFunction shrincs) L 0 =
      82752 / 2 ^ 128 + 2 * Gam + pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) +
        12 / 2 ^ 256 := by
    rw [SfCharge.perFunction_shrincs, SlCharge.perFunction_shrincs, fullSum_eq, itsrSl_eq, epsDs]
    push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [esl]
    exact logb_bracket_of_Q (lo := 77173 / 2 ^ 128 + 2 * gamLoQ)
      (hi := 77173 / 2 ^ 128 + 2 * gamHiQ + pull1Q)
      (N := 100) (by norm_num) (-11177) (-11176) (by norm_num) (by norm_num) (by decide +kernel)
      (by push_cast; linarith) (by push_cast; linarith) (by decide +kernel) (by decide +kernel)
  · rw [esf]
    exact logb_bracket_of_Q (lo := 5578 / 2 ^ 128 + 2 / 2 ^ 256)
      (hi := 5578 / 2 ^ 128 + 2 / 2 ^ 256) (N := 100) (by norm_num) (-11556) (-11555)
      (by norm_num) (by norm_num) (by decide +kernel) (by push_cast; rfl) (by push_cast; rfl)
      (by decide +kernel) (by decide +kernel)
  · rw [efull]
    exact logb_bracket_of_Q (lo := 82752 / 2 ^ 128 + 2 * gamLoQ + 12 / 2 ^ 256)
      (hi := 82752 / 2 ^ 128 + 2 * gamHiQ + pull1Q + 12 / 2 ^ 256) (N := 100) (by norm_num)
      (-11167) (-11166) (by norm_num) (by norm_num) (by decide +kernel) (by push_cast; linarith)
      (by push_cast; linarith) (by decide +kernel) (by decide +kernel)

end ShrincsSecurity.Concrete

end
