module

public import ShrincsSecurity.Concrete.Figures

/-!
# Remark 6.1: the classical bounds with the earlier results

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), **Remark 6.1** (lines 4822–4871), classical
entries and gains, with footnote 14 (earlier entries rounded to nearest, gains computed from the
exact values and rounded down).

Two classical results are switched back, one at a time:

* **Theorem F.2** in place of Theorem F.1 for itsr (`itsrSlF2`, `slBoundF2`, `fullBoundF2`);
* **Lemma C.2** in place of Corollaries G.1 and C.3 at the randomizer part of SM-rTCR and at the
  hop (`sfBoundC2`, `fullBoundC2`);

and, with all classical ones switched back, `fullBoundF2C2` (the stateless and stateful bounds with
all switched back are `slBoundF2` and `sfBoundC2`). The other two results of Remark 6.1 are quantum
and out of scope. All other terms are as in `Concrete.Paths`; the stateless and full-scheme
variants use the conjectured SM-DSPR row.

## Results (paper → certified)

Entries are rounded to nearest, so a printed `Y` is certified as `log₂ ξ* ∈ [Y − 0.005, Y + 0.005]`,
a printed value `v` at `ξ = 0` as `log₂ B(0) ∈ [v − 0.05, v + 0.05]`; a gain `g` (rounded down) as
`log₂ ξ*_new − log₂ ξ*_old ∈ [g, g + 0.01]`.

* Theorem F.2: `88.00 (−48.0)` stateless and full scheme (every `L`); gains `34.23`, `33.47`.
* Lemma C.2: `107.00 (−87.0)` / `118.90 (−110.9)` stateful BXMSS-20 / UXMSS-256, `107.00 (−87.0)` /
  `118.77 (−110.1)` full scheme; gains `15.75`, `3.85` (stateful), `14.47`, `2.70` (full scheme).
* All switched back: `88.00 (−48.0)` stateless and full scheme (both shapes), `107.00 (−87.0)` and
  `118.90 (−110.9)` stateful.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete

open ShrincsSecurity.ITSR ShrincsSecurity.ITSR.Concrete ShrincsSecurity.Scheme

/-! ## The variants -/

/-- The itsr term bounded by **Theorem F.2** at the stateless parameters. -/
noncomputable def itsrSlF2 (q : ℕ) : ℝ := itsrBoundF2 45 10 (2 ^ 13) (2 ^ 40) (2 ^ 128) q

theorem itsrSlF2_eq (q : ℕ) :
    itsrSlF2 q = 2 ^ 40 * (q + 2 ^ 40 + 1) / 2 ^ 128 + (q + 1) * Gam := by
  rw [itsrSlF2, itsrBoundF2, searchTerm_Gam]; push_cast; ring

/-- Theorem 4.3 at Section 6.3, with the itsr term bounded by Theorem F.2. -/
noncomputable def slBoundF2 (ξ : ℕ) : ℝ :=
  prfTerms ξ + itsrSlF2 (ξ + 1) + slColl dsprRow (.uniform (Vsl shrincs)) 0 ξ

/-- Theorem 4.2 at Section 6.3, with Lemma C.2 at the randomizer part of SM-rTCR and at the hop. -/
noncomputable def sfBoundC2 (L ξ : ℕ) : ℝ :=
  smRtcrHash (2 ^ 256) (ξ + 1) + smRtcrRandC2 (2 ^ 128) 1 L (ξ + 1) + diReproC2 (2 ^ 128) L ξ +
    sfColl (.uniform (Vsf shrincs)) 0 ξ

/-- Claim 6.3 Eq. (6) at Section 6.3 with the three places of the reprogramming step bounded by
`itsrT` (the itsr term, search and pull part), `randT` (the randomizer part of SM-rTCR) and `hopT`
(the hop). -/
noncomputable def fullWith (itsrT : ℕ → ℝ) (randT hopT : ℝ → ℝ) (ξ : ℕ) : ℝ :=
  prfTerms ξ + smRtcrHash (2 ^ 256) (ξ + 1) + randT (ξ + 1) + hopT ξ +
    sfColl (.uniform (Vsf shrincs)) 0 ξ + itsrT (ξ + 1) +
    slColl dsprRow (.uniform (Vsl shrincs)) 0 ξ + epsDs

theorem fullBound_eq_fullWith (L : ℕ) :
    fullBound L = fullWith itsrSl (smRtcrRand (2 ^ 128) 1 L) hop := by
  funext ξ
  unfold fullBound fullSum fullWith sfRtcr smRtcrBound
  simp only [SfCharge.uniform, SlCharge.uniform]
  push_cast
  ring

/-- Claim 6.4 with the itsr term bounded by Theorem F.2. -/
noncomputable def fullBoundF2 (L : ℕ) : ℕ → ℝ := fullWith itsrSlF2 (smRtcrRand (2 ^ 128) 1 L) hop

/-- Claim 6.4 with Lemma C.2 at the randomizer part of SM-rTCR and at the shared hop. -/
noncomputable def fullBoundC2 (L : ℕ) : ℕ → ℝ :=
  fullWith itsrSl (smRtcrRandC2 (2 ^ 128) 1 L) (diReproC2 (2 ^ 128) L)

/-- Claim 6.4 with Theorem F.2 and Lemma C.2 (all classical results of Remark 6.1 switched
back). -/
noncomputable def fullBoundF2C2 (L : ℕ) : ℕ → ℝ :=
  fullWith itsrSlF2 (smRtcrRandC2 (2 ^ 128) 1 L) (diReproC2 (2 ^ 128) L)

/-! ## Closed forms -/

theorem slBoundF2_eq (ξ : ℕ) :
    slBoundF2 ξ = (54 * ξ + 98687) / 2 ^ 128 + 2 ^ 40 * (ξ + 2 + 2 ^ 40) / 2 ^ 128 +
      (ξ + 2) * Gam := by
  rw [slBoundF2, prfTerms_eq, itsrSlF2_eq, slColl_eq, Vsl_shrincs]
  simp only [SlCharge.uniform]
  push_cast
  ring

theorem sfBoundC2_eq (L ξ : ℕ) :
    sfBoundC2 L ξ = (36 * ξ + 13426) / 2 ^ 128 + (ξ + 2) / 2 ^ 256 +
      L * (ξ + 1 + L + 1) / 2 ^ 128 + L * (L + ξ + 1) / 2 ^ 128 := by
  rw [sfBoundC2, sfColl_eq, Vsf_shrincs, smRtcrHash, smRtcrRandC2, diReproC2]
  simp only [SfCharge.uniform]
  push_cast
  ring

theorem fullWith_eq (itsrT : ℕ → ℝ) (randT hopT : ℝ → ℝ) (ξ : ℕ) :
    fullWith itsrT randT hopT ξ = (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 +
      randT (ξ + 1) + hopT ξ + itsrT (ξ + 1) := by
  rw [fullWith, prfTerms_eq, sfColl_eq, slColl_eq, Vsf_shrincs, Vsl_shrincs, smRtcrHash, epsDs]
  simp only [SfCharge.uniform, SlCharge.uniform]
  push_cast
  ring

theorem fullBoundF2_eq (L ξ : ℕ) :
    fullBoundF2 L ξ = (92 * ξ + 112115) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 +
      2 ^ 40 * (ξ + 2 + 2 ^ 40) / 2 ^ 128 + (ξ + 2) * Gam := by
  rw [fullBoundF2, fullWith_eq, itsrSlF2_eq, smRtcrRand, hop, diReproBound]
  push_cast
  ring

theorem fullBoundC2_eq (L ξ : ℕ) :
    fullBoundC2 L ξ = (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 +
      L * (ξ + 1 + L + 1) / 2 ^ 128 + L * (L + ξ + 1) / 2 ^ 128 + itsrSl (ξ + 1) := by
  rw [fullBoundC2, fullWith_eq, smRtcrRandC2, diReproC2]
  ring

theorem fullBoundF2C2_eq (L ξ : ℕ) :
    fullBoundF2C2 L ξ = (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 +
      L * (ξ + 1 + L + 1) / 2 ^ 128 + L * (L + ξ + 1) / 2 ^ 128 +
      2 ^ 40 * (ξ + 2 + 2 ^ 40) / 2 ^ 128 + (ξ + 2) * Gam := by
  rw [fullBoundF2C2, fullWith_eq, itsrSlF2_eq, smRtcrRandC2, diReproC2]
  push_cast
  ring

/-! ## Monotonicity -/

theorem slBoundF2_mono : Monotone slBoundF2 := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  have := Gam_nonneg
  rw [slBoundF2_eq, slBoundF2_eq]
  gcongr

theorem sfBoundC2_mono (L : ℕ) : Monotone (sfBoundC2 L) := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [sfBoundC2_eq, sfBoundC2_eq]
  gcongr

theorem fullBoundF2_mono (L : ℕ) : Monotone (fullBoundF2 L) := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  have := Gam_nonneg
  rw [fullBoundF2_eq, fullBoundF2_eq]
  gcongr

theorem fullBoundC2_mono (L : ℕ) : Monotone (fullBoundC2 L) := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [fullBoundC2_eq, fullBoundC2_eq]
  gcongr ?_ + ?_
  · gcongr
  · exact itsrSl_mono (by omega)

theorem fullBoundF2C2_mono (L : ℕ) : Monotone (fullBoundF2C2 L) := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  have := Gam_nonneg
  rw [fullBoundF2C2_eq, fullBoundF2C2_eq]
  gcongr

/-! ## Rational enclosures -/

/-- The Theorem F.2 part `2^40 (ξ + 2 + 2^40)/2^128` (rational). -/
def f2Q (ξ : ℕ) : ℚ := 2 ^ 40 * (ξ + 2 + 2 ^ 40) / 2 ^ 128

/-- The two Lemma C.2 parts `L(ξ + 1 + L + 1)/2^128 + L(L + ξ + 1)/2^128` (rational). -/
def c2Q (L ξ : ℕ) : ℚ := L * (ξ + 1 + L + 1) / 2 ^ 128 + L * (L + ξ + 1) / 2 ^ 128

def slF2HiQ (ξ : ℕ) : ℚ := (54 * ξ + 98687) / 2 ^ 128 + f2Q ξ + (ξ + 2) * gamHiQ
def slF2LoQ (ξ : ℕ) : ℚ := (54 * ξ + 98687) / 2 ^ 128 + f2Q ξ + (ξ + 2) * gamLoQ

theorem slBoundF2_le_Q (ξ : ℕ) : slBoundF2 ξ ≤ slF2HiQ ξ := by
  have : ((ξ : ℝ) + 2) * Gam ≤ ((ξ : ℝ) + 2) * (gamHiQ : ℝ) := by
    have := Gam_le_hi
    gcongr
  rw [slBoundF2_eq, slF2HiQ, f2Q]; push_cast; linarith

theorem Q_le_slBoundF2 (ξ : ℕ) : (slF2LoQ ξ : ℝ) ≤ slBoundF2 ξ := by
  rw [slBoundF2_eq, slF2LoQ, f2Q]; push_cast; linarith [add_two_mul_lo_le ξ]

def sfC2Q (L ξ : ℕ) : ℚ := (36 * ξ + 13426) / 2 ^ 128 + (ξ + 2) / 2 ^ 256 + c2Q L ξ

theorem sfBoundC2_eq_Q (L ξ : ℕ) : sfBoundC2 L ξ = sfC2Q L ξ := by
  rw [sfBoundC2_eq, sfC2Q, c2Q]; push_cast; ring

def fullF2HiQ (ξ : ℕ) : ℚ :=
  (92 * ξ + 112115) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 + f2Q ξ + (ξ + 2) * gamHiQ
def fullF2LoQ (ξ : ℕ) : ℚ :=
  (92 * ξ + 112115) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 + f2Q ξ + (ξ + 2) * gamLoQ

theorem fullBoundF2_le_Q (L ξ : ℕ) : fullBoundF2 L ξ ≤ fullF2HiQ ξ := by
  have : ((ξ : ℝ) + 2) * Gam ≤ ((ξ : ℝ) + 2) * (gamHiQ : ℝ) := by
    have := Gam_le_hi
    gcongr
  rw [fullBoundF2_eq, fullF2HiQ, f2Q]; push_cast; linarith

theorem Q_le_fullBoundF2 (L ξ : ℕ) : (fullF2LoQ ξ : ℝ) ≤ fullBoundF2 L ξ := by
  rw [fullBoundF2_eq, fullF2LoQ, f2Q]; push_cast; linarith [add_two_mul_lo_le ξ]

def fullC2HiQ (L ξ : ℕ) : ℚ :=
  (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 + c2Q L ξ + itsrSlQ (ξ + 1)
def fullC2LoQ (L ξ : ℕ) : ℚ :=
  (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 + c2Q L ξ + (ξ + 2) * gamLoQ

theorem fullBoundC2_le_Q (L ξ : ℕ) : fullBoundC2 L ξ ≤ fullC2HiQ L ξ := by
  rw [fullBoundC2_eq, fullC2HiQ, c2Q]; push_cast; linarith [itsrSl_le_Q (ξ + 1)]

theorem Q_le_fullBoundC2 (L ξ : ℕ) : (fullC2LoQ L ξ : ℝ) ≤ fullBoundC2 L ξ := by
  rw [fullBoundC2_eq, fullC2LoQ, c2Q]; push_cast
  linarith [add_two_mul_Gam_le_itsrSl ξ, add_two_mul_lo_le ξ]

def fullF2C2HiQ (L ξ : ℕ) : ℚ :=
  (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 + c2Q L ξ + f2Q ξ + (ξ + 2) * gamHiQ
def fullF2C2LoQ (L ξ : ℕ) : ℚ :=
  (90 * ξ + 112114) / 2 ^ 128 + (ξ + 12) / 2 ^ 256 + c2Q L ξ + f2Q ξ + (ξ + 2) * gamLoQ

theorem fullBoundF2C2_le_Q (L ξ : ℕ) : fullBoundF2C2 L ξ ≤ fullF2C2HiQ L ξ := by
  have : ((ξ : ℝ) + 2) * Gam ≤ ((ξ : ℝ) + 2) * (gamHiQ : ℝ) := by
    have := Gam_le_hi
    gcongr
  rw [fullBoundF2C2_eq, fullF2C2HiQ, c2Q, f2Q]; push_cast; linarith

theorem Q_le_fullBoundF2C2 (L ξ : ℕ) : (fullF2C2LoQ L ξ : ℝ) ≤ fullBoundF2C2 L ξ := by
  rw [fullBoundF2C2_eq, fullF2C2LoQ, c2Q, f2Q]; push_cast; linarith [add_two_mul_lo_le ξ]

/-! ## Locating `ξ*` -/

theorem slF2_xiStar_mem :
    309485009806084641753611416 < xiStar slBoundF2 ∧
      xiStar slBoundF2 ≤ 309485009806084671507867645 :=
  xiStar_bracket slBoundF2_mono (lt_one_of_Q (slBoundF2_le_Q _) (by decide +kernel))
    (one_le_of_Q (Q_le_slBoundF2 _) (by decide +kernel))

theorem fullF2_xiStar_mem (L : ℕ) :
    309485009795388592640030939 < xiStar (fullBoundF2 L) ∧
      xiStar (fullBoundF2 L) ≤ 309485009795388622394287166 :=
  xiStar_bracket (fullBoundF2_mono L) (lt_one_of_Q (fullBoundF2_le_Q L _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullBoundF2 L _) (by decide +kernel))

theorem sfC2BX_xiStar_mem :
    162256491511938111158071954079816 < xiStar (sfBoundC2 (2 ^ 20)) ∧
      xiStar (sfBoundC2 (2 ^ 20)) ≤ 162256491511938111158071954079817 :=
  xiStar_bracket (sfBoundC2_mono _) (lt_one_of_Q (sfBoundC2_eq_Q _ _).le (by decide +kernel))
    (one_le_of_Q (sfBoundC2_eq_Q _ _).ge (by decide +kernel))

theorem sfC2UX_xiStar_mem :
    620953224308281867633895269036073113 < xiStar (sfBoundC2 (2 ^ 8)) ∧
      xiStar (sfBoundC2 (2 ^ 8)) ≤ 620953224308281867633895269036073114 :=
  xiStar_bracket (sfBoundC2_mono _) (lt_one_of_Q (sfBoundC2_eq_Q _ _).le (by decide +kernel))
    (one_le_of_Q (sfBoundC2_eq_Q _ _).ge (by decide +kernel))

theorem fullC2BX_xiStar_mem :
    162252297312346682889961725028116 < xiStar (fullBoundC2 (2 ^ 20)) ∧
      xiStar (fullBoundC2 (2 ^ 20)) ≤ 162252297320543391641728052400385 :=
  xiStar_bracket (fullBoundC2_mono _) (lt_one_of_Q (fullBoundC2_le_Q _ _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullBoundC2 _ _) (by decide +kernel))

theorem fullC2UX_xiStar_mem :
    565053304298334836803474015977191234 < xiStar (fullBoundC2 (2 ^ 8)) ∧
      xiStar (fullBoundC2 (2 ^ 8)) ≤ 565054191150539400443829497065063823 :=
  xiStar_bracket (fullBoundC2_mono _) (lt_one_of_Q (fullBoundC2_le_Q _ _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullBoundC2 _ _) (by decide +kernel))

theorem fullF2C2BX_xiStar_mem :
    309484419501267178513310613 < xiStar (fullBoundF2C2 (2 ^ 20)) ∧
      xiStar (fullBoundF2C2 (2 ^ 20)) ≤ 309484419501267208267453337 :=
  xiStar_bracket (fullBoundF2C2_mono _) (lt_one_of_Q (fullBoundF2C2_le_Q _ _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullBoundF2C2 _ _) (by decide +kernel))

theorem fullF2C2UX_xiStar_mem :
    309485009651836354608260892 < xiStar (fullBoundF2C2 (2 ^ 8)) ∧
      xiStar (fullBoundF2C2 (2 ^ 8)) ≤ 309485009651836384362517091 :=
  xiStar_bracket (fullBoundF2C2_mono _) (lt_one_of_Q (fullBoundF2C2_le_Q _ _) (by decide +kernel))
    (one_le_of_Q (Q_le_fullBoundF2C2 _ _) (by decide +kernel))

/-! ## Remark 6.1, first item: Theorem F.2 -/

/-- **Remark 6.1**: with Theorem F.2 the classical entry is `88.00 (−48.0)` on the stateless path;
Theorem F.1 adds `34.23` bits. -/
theorem remark_6_1_F2_sl :
    (87.995 ≤ Real.logb 2 (xiStar slBoundF2) ∧ Real.logb 2 (xiStar slBoundF2) ≤ 88.005) ∧
    (-48.05 ≤ Real.logb 2 (slBoundF2 0) ∧ Real.logb 2 (slBoundF2 0) ≤ -47.95) ∧
    (34.23 ≤ Real.logb 2 (xiStar slBound) - Real.logb 2 (xiStar slBoundF2) ∧
      Real.logb 2 (xiStar slBound) - Real.logb 2 (xiStar slBoundF2) ≤ 34.24) :=
  ⟨logb_xiStar_bracket slF2_xiStar_mem (N := 200) (by norm_num) 17599 17601 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-4805) (-4795) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_slBoundF2 0) (slBoundF2_le_Q 0) (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_sub_bracket sl_xiStar_mem slF2_xiStar_mem (N := 100) (by norm_num) 3423 3424
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Remark 6.1**: with Theorem F.2 the classical entry is `88.00 (−48.0)` for the full scheme
with either shape (every `L`); Theorem F.1 adds `33.47` bits. -/
theorem remark_6_1_F2_full (L : ℕ) :
    (87.995 ≤ Real.logb 2 (xiStar (fullBoundF2 L)) ∧
      Real.logb 2 (xiStar (fullBoundF2 L)) ≤ 88.005) ∧
    (-48.05 ≤ Real.logb 2 (fullBoundF2 L 0) ∧ Real.logb 2 (fullBoundF2 L 0) ≤ -47.95) ∧
    (33.47 ≤ Real.logb 2 (xiStar (fullBound L)) - Real.logb 2 (xiStar (fullBoundF2 L)) ∧
      Real.logb 2 (xiStar (fullBound L)) - Real.logb 2 (xiStar (fullBoundF2 L)) ≤ 33.48) :=
  ⟨logb_xiStar_bracket (fullF2_xiStar_mem L) (N := 200) (by norm_num) 17599 17601 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-4805) (-4795) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_fullBoundF2 L 0) (fullBoundF2_le_Q L 0) (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_sub_bracket (full_xiStar_mem L) (fullF2_xiStar_mem L) (N := 100) (by norm_num)
      3347 3348 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-! ## Remark 6.1, second item: Lemma C.2 -/

/-- **Remark 6.1**: with Lemma C.2 at the randomizer part of SM-rTCR and at the hop, the classical
entries on the stateful path are `107.00 (−87.0)` (BXMSS-20) and `118.90 (−110.9)` (UXMSS-256);
the bounds of Section 6.5 add `15.75` and `3.85` bits. -/
theorem remark_6_1_C2_sf :
    (106.995 ≤ Real.logb 2 (xiStar (sfBoundC2 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfBoundC2 (2 ^ 20))) ≤ 107.005) ∧
    (-87.05 ≤ Real.logb 2 (sfBoundC2 (2 ^ 20) 0) ∧ Real.logb 2 (sfBoundC2 (2 ^ 20) 0) ≤ -86.95) ∧
    (118.895 ≤ Real.logb 2 (xiStar (sfBoundC2 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfBoundC2 (2 ^ 8))) ≤ 118.905) ∧
    (-110.95 ≤ Real.logb 2 (sfBoundC2 (2 ^ 8) 0) ∧ Real.logb 2 (sfBoundC2 (2 ^ 8) 0) ≤ -110.85) ∧
    (15.75 ≤ Real.logb 2 (xiStar (sfBound (2 ^ 20))) -
        Real.logb 2 (xiStar (sfBoundC2 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (sfBound (2 ^ 20))) - Real.logb 2 (xiStar (sfBoundC2 (2 ^ 20))) ≤
        15.76) ∧
    (3.85 ≤ Real.logb 2 (xiStar (sfBound (2 ^ 8))) - Real.logb 2 (xiStar (sfBoundC2 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (sfBound (2 ^ 8))) - Real.logb 2 (xiStar (sfBoundC2 (2 ^ 8))) ≤
        3.86) :=
  ⟨logb_xiStar_bracket sfC2BX_xiStar_mem (N := 200) (by norm_num) 21399 21401 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-8705) (-8695) (by norm_num) (by norm_num)
      (by decide +kernel) (sfBoundC2_eq_Q _ 0).ge (sfBoundC2_eq_Q _ 0).le (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_bracket sfC2UX_xiStar_mem (N := 200) (by norm_num) 23779 23781 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-11095) (-11085) (by norm_num) (by norm_num)
      (by decide +kernel) (sfBoundC2_eq_Q _ 0).ge (sfBoundC2_eq_Q _ 0).le (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_sub_bracket (sf_xiStar_mem _) sfC2BX_xiStar_mem (N := 100) (by norm_num) 1575
      1576 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket (sf_xiStar_mem _) sfC2UX_xiStar_mem (N := 100) (by norm_num) 385 386
      (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-- **Remark 6.1**: with Lemma C.2 at the randomizer part of SM-rTCR and at the hop, the classical
entries for the full scheme are `107.00 (−87.0)` (BXMSS-20) and `118.77 (−110.1)` (UXMSS-256); the
bounds of Section 6.5 add `14.47` and `2.70` bits. -/
theorem remark_6_1_C2_full :
    (106.995 ≤ Real.logb 2 (xiStar (fullBoundC2 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullBoundC2 (2 ^ 20))) ≤ 107.005) ∧
    (-87.05 ≤ Real.logb 2 (fullBoundC2 (2 ^ 20) 0) ∧
      Real.logb 2 (fullBoundC2 (2 ^ 20) 0) ≤ -86.95) ∧
    (118.765 ≤ Real.logb 2 (xiStar (fullBoundC2 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullBoundC2 (2 ^ 8))) ≤ 118.775) ∧
    (-110.15 ≤ Real.logb 2 (fullBoundC2 (2 ^ 8) 0) ∧
      Real.logb 2 (fullBoundC2 (2 ^ 8) 0) ≤ -110.05) ∧
    (14.47 ≤ Real.logb 2 (xiStar (fullBound (2 ^ 20))) -
        Real.logb 2 (xiStar (fullBoundC2 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullBound (2 ^ 20))) - Real.logb 2 (xiStar (fullBoundC2 (2 ^ 20))) ≤
        14.48) ∧
    (2.70 ≤ Real.logb 2 (xiStar (fullBound (2 ^ 8))) -
        Real.logb 2 (xiStar (fullBoundC2 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullBound (2 ^ 8))) - Real.logb 2 (xiStar (fullBoundC2 (2 ^ 8))) ≤
        2.71) :=
  ⟨logb_xiStar_bracket fullC2BX_xiStar_mem (N := 200) (by norm_num) 21399 21401 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-8705) (-8695) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_fullBoundC2 _ 0) (fullBoundC2_le_Q _ 0) (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_bracket fullC2UX_xiStar_mem (N := 200) (by norm_num) 23753 23755 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-11015) (-11005) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_fullBoundC2 _ 0) (fullBoundC2_le_Q _ 0) (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_sub_bracket (full_xiStar_mem _) fullC2BX_xiStar_mem (N := 100) (by norm_num) 1447
      1448 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_xiStar_sub_bracket (full_xiStar_mem _) fullC2UX_xiStar_mem (N := 100) (by norm_num) 270
      271 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)⟩

/-! ## Remark 6.1, all classical results switched back -/

/-- **Remark 6.1**: with all results switched back, the classical entry of the full scheme is
`88.00 (−48.0)` with either shape (the stateless entry is `remark_6_1_F2_sl`, the stateful entries
are `remark_6_1_C2_sf`). -/
theorem remark_6_1_all_full :
    (87.995 ≤ Real.logb 2 (xiStar (fullBoundF2C2 (2 ^ 20))) ∧
      Real.logb 2 (xiStar (fullBoundF2C2 (2 ^ 20))) ≤ 88.005) ∧
    (-48.05 ≤ Real.logb 2 (fullBoundF2C2 (2 ^ 20) 0) ∧
      Real.logb 2 (fullBoundF2C2 (2 ^ 20) 0) ≤ -47.95) ∧
    (87.995 ≤ Real.logb 2 (xiStar (fullBoundF2C2 (2 ^ 8))) ∧
      Real.logb 2 (xiStar (fullBoundF2C2 (2 ^ 8))) ≤ 88.005) ∧
    (-48.05 ≤ Real.logb 2 (fullBoundF2C2 (2 ^ 8) 0) ∧
      Real.logb 2 (fullBoundF2C2 (2 ^ 8) 0) ≤ -47.95) :=
  ⟨logb_xiStar_bracket fullF2C2BX_xiStar_mem (N := 200) (by norm_num) 17599 17601 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-4805) (-4795) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_fullBoundF2C2 _ 0) (fullBoundF2C2_le_Q _ 0) (by decide +kernel)
      (by decide +kernel),
    logb_xiStar_bracket fullF2C2UX_xiStar_mem (N := 200) (by norm_num) 17599 17601 (by norm_num)
      (by norm_num) (by decide +kernel) (by decide +kernel),
    logb_bracket_of_Q (N := 100) (by norm_num) (-4805) (-4795) (by norm_num) (by norm_num)
      (by decide +kernel) (Q_le_fullBoundF2C2 _ 0) (fullBoundF2C2_le_Q _ 0) (by decide +kernel)
      (by decide +kernel)⟩

end ShrincsSecurity.Concrete

end
