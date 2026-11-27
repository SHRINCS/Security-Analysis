module

public import ShrincsSecurity.Concrete.Conventions

/-!
# Theorems 4.1–4.3 at the proposed parameters (classical): the sums and their closed forms

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): the statements of **Theorem 4.1**
(lines 2874–2935), **Theorem 4.2** (lines 2949–2998) and **Theorem 4.3** (lines 3027–3059), the
classical line Eq. (6) of **Claim 6.3** (lines 5320–5358), instantiated as in **Section 6.3**
(lines 4942–4988), **Section 6.4** (lines 4990–5045) and **Section 6.6** (lines 5141–5233), with
the closed forms of **Claim 6.1** Eq. (1), **Claim 6.2** Eq. (3) and **Claim 6.4** Eq. (9).

## The sums

Every term of the theorems is replaced by its classical bound from Table 6 / Table 7
(`Concrete.Generic`), at the spaces of Section 6.3 (`2^128`, and `|N| = 2^256` for the hash part of
the SM-rTCR term of `H^sf_msg`) and `w = 16`, with the query counts of Section 6.3:

* the PRF terms at `q := ξ`;
* every collection term at `q := ξ + V^f + B` in its `|N|`, `|M|` summands and at `q₁ := ξ + B` in
  its `|P|` summand, where `V^f` is the verification charge of the term (`SfCharge`, `SlCharge`)
  and `B` the collection budget charged under Convention M (Section 6.8; `B = 0` under
  Convention I);
* the itsr and SM-rTCR terms at `q := ξ + V^msg` (`V^msg = 1`);
* the reprogramming hop at `q := q_h := ξ` (Remark C.6).

The SM-rTCR term is taken with `K = 1` and `p = q_s^sf = L`; the itsr term with `p = 2^40`. Under
Convention I with the verification free to the forger (`SfCharge.uniform`, `SlCharge.uniform`)
every collection term carries the whole verification `Vsf = 497` or `Vsl = 2741`; the
per-function charges of footnote 15 are `SfCharge.perFunction`, `SlCharge.perFunction`.

`sfSum`, `slSum` and `fullSum` are these sums for Theorem 4.2, Theorem 4.3 and Claim 6.3 Eq. (6)
(Theorem 4.1 with the shared hop bounded through `B₄`). **The SM-DSPR term** enters `slSum` and
`fullSum` as an argument `dspr : ℝ → ℝ`, the bound substituted for its insecurity as a function
of the query count. The figures of Section 6 use the conjectured row of Table 6, `dsprRow`; every
statement about `slBound` or `fullBound` therefore rests on that conjecture, which is made
explicit by `slSum_le_slBound` / `fullSum_le_fullBound`: any `dspr` below the row gives a sum
below the certified bound.

## Main statements

* `sfSum_eq`, `sfBound_eq` (**Claim 6.2**, Eq. (3)): `(38 ξ + 13427)/2^128 + (ξ + 2)/2^256`, for
  every `L`.
* `slColl_eq`, `slBound_eq` (**Claim 6.1**, Eq. (1)): `(54 ξ + 98687)/2^128 + ν(ξ)` with
  `ν(ξ) = (ξ + 2) Γ + P_{45,10,2^13}(ξ + 1, 2^40)`.
* `fullBound_eq` (**Claim 6.4**, Eq. (9)): `(92 ξ + 112115)/2^128 + ν(ξ) + (ξ + 12)/2^256`.
* `sfCore_eq`, `slCore_eq`, `fullCore_eq` (Sections 6.1, 6.6, 6.7): the core terms
  `(36 ξ + 13426)/2^128`, `(54 ξ + 98687)/2^128 + (ξ + 2) Γ`, `(90 ξ + 112114)/2^128 + (ξ + 2) Γ`
  (up to summands of scale `2^-256`), and `*_eq_core_add_repro`: each bound is its core plus its
  reprogramming terms.
* `sfSum_budget`, `slSum_budget` (Section 6.8): Convention M adds exactly `36 B/2^128` and
  `52 B/2^128`.
* Section 6.4: `sfBound_zero`, `slBound_zero`, `fullBound_zero`, the decomposition `c = c₀ + c_V`.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete

open ShrincsSecurity.ITSR ShrincsSecurity.ITSR.Concrete ShrincsSecurity.Scheme

/-! ## Charges -/

/-- The evaluations charged to the terms of Theorem 4.2 on top of the forger's `ξ`: `msg` to the
SM-rTCR term (`H^sf_msg`), the others to the collection terms of `H_grind`, `F`, `Th_lsf`, `H` and
`Th_{2∪lsf}`. -/
structure SfCharge where
  msg : ℕ
  grind : ℕ
  F : ℕ
  thl : ℕ
  H : ℕ
  th2 : ℕ

/-- The evaluations charged to the terms of Theorem 4.3 on top of the forger's `ξ`: `msg` to the
itsr term (`H^sl_msg`), the others to the collection terms of `F`, `H`, `Th_k` and `Th_lsl`. -/
structure SlCharge where
  msg : ℕ
  F : ℕ
  H : ℕ
  thk : ℕ
  thl : ℕ

/-- **Section 6.3**: every collection term at `q := ξ + V`, the message hash at `q := ξ + 1`. -/
def SfCharge.uniform (V : ℕ) : SfCharge := ⟨1, V, V, V, V, V⟩

/-- No verification charged: the constant `c₀` of Section 6.4. -/
def SfCharge.zero : SfCharge := ⟨0, 0, 0, 0, 0, 0⟩

/-- Footnote 15: each term charged with the evaluations of its own function (Lemma 5.1). -/
def SfCharge.perFunction (P : Scheme.Params) : SfCharge := ⟨1, 1, VsfF P, 1, VsfH P, VsfTh2 P⟩

/-- **Section 6.3**: every collection term at `q := ξ + V`, the message hash at `q := ξ + 1`. -/
def SlCharge.uniform (V : ℕ) : SlCharge := ⟨1, V, V, V, V⟩

/-- No verification charged: the constant `c₀` of Section 6.4. -/
def SlCharge.zero : SlCharge := ⟨0, 0, 0, 0, 0⟩

/-- Footnote 15: each term charged with the evaluations of its own function (Lemma 5.1). -/
def SlCharge.perFunction (P : Scheme.Params) : SlCharge := ⟨1, VslF P, VslH P, 1, P.d⟩

/-! ## Theorem 4.2 (stateful path) -/

/-- The seven collection terms of **Theorem 4.2** under the classical rows of Table 6, in the
order of the theorem: S-TCR(Prop) for `H_grind`, `w · `SM-UD for `F` (`w = 16`), SM-TCR for `F`,
SM-PRE for `F`, SM-TCR for `Th_lsf`, SM-TCR for `H`, SM-TCR-EXCL for `Th_{2∪lsf}`. -/
noncomputable def sfColl (c : SfCharge) (B : ℝ) (ξ : ℕ) : ℝ :=
  sTcrPropBound (2 ^ 128) (2 ^ 128) (ξ + c.grind + B) (ξ + B) +
  16 * smUdBound (2 ^ 128) (ξ + c.F + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.F + B) (ξ + B) +
  smPreBound (2 ^ 128) (2 ^ 128) (ξ + c.F + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.thl + B) (ξ + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.H + B) (ξ + B) +
  smTcrExclBound (2 ^ 128) (2 ^ 128) (ξ + c.th2 + B) (ξ + B)

/-- The SM-rTCR term of Theorems 4.1 and 4.2 (`K = 1`, `p = L`, `|N| = 2^256`, `|R| = 2^128`). -/
noncomputable def sfRtcr (L : ℕ) (q : ℝ) : ℝ := smRtcrBound (2 ^ 256) (2 ^ 128) 1 L q

/-- The reprogramming hop of Theorems 4.1 and 4.2 (Corollary C.3, `|R| = 2^128`, `q := q_h`). -/
noncomputable def hop (qh : ℝ) : ℝ := diReproBound (2 ^ 128) qh

/-- **Theorem 4.2** with `K = 1` at `q_s := L`, every term replaced by its classical bound. -/
noncomputable def sfSum (c : SfCharge) (B : ℝ) (L ξ : ℕ) : ℝ :=
  sfRtcr L (ξ + c.msg) + hop ξ + sfColl c B ξ

/-- **Claim 6.2** (classical): Theorem 4.2 instantiated as in Section 6.3 (Convention I,
`Vsf = 497`). -/
noncomputable def sfBound (L ξ : ℕ) : ℝ := sfSum (.uniform (Vsf shrincs)) 0 L ξ

theorem sfColl_eq (c : SfCharge) (B : ℝ) (ξ : ℕ) :
    sfColl c B ξ = (36 * (ξ + B) + 7 + 2 * c.grind + 20 * c.F + 2 * c.thl + 2 * c.H + c.th2) /
      2 ^ 128 := by
  unfold sfColl sTcrPropBound smUdBound smTcrBound smPreBound smTcrExclBound
  ring

theorem sfRtcr_eq (L : ℕ) (q : ℝ) : sfRtcr L q = (q + 1) / 2 ^ 256 + q / 2 ^ 128 := by
  unfold sfRtcr smRtcrBound smRtcrHash smRtcrRand
  ring

theorem sfSum_eq (c : SfCharge) (B : ℝ) (L ξ : ℕ) :
    sfSum c B L ξ = (38 * ξ + 36 * B + 7 + c.msg + 2 * c.grind + 20 * c.F + 2 * c.thl +
      2 * c.H + c.th2) / 2 ^ 128 + (ξ + c.msg + 1) / 2 ^ 256 := by
  rw [sfSum, sfRtcr_eq, sfColl_eq, hop, diReproBound]
  ring

theorem Vsf_shrincs : Vsf shrincs = 497 := by decide +kernel

theorem Vsl_shrincs : Vsl shrincs = 2741 := by decide +kernel

/-- **Claim 6.2**, Eq. (3), exact form: `(38 ξ + 13427)/2^128 + ν^sf_c(ξ)` with
`ν^sf_c(ξ) = (ξ+2)/2^256`, for every `L`. -/
theorem sfBound_eq (L ξ : ℕ) :
    sfBound L ξ = (38 * ξ + 13427) / 2 ^ 128 + (ξ + 2) / 2 ^ 256 := by
  rw [sfBound, sfSum_eq, Vsf_shrincs]
  simp only [SfCharge.uniform]
  push_cast
  ring

theorem sfBound_mono (L : ℕ) : Monotone (sfBound L) := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [sfBound_eq, sfBound_eq]
  gcongr

/-! ## Theorem 4.3 (stateless path) -/

/-- The conjectured **SM-DSPR row** of Table 6 at `|N| = 2^128`: `(2q + 1)/2^128`. -/
noncomputable def dsprRow (q : ℝ) : ℝ := smDsprBound (2 ^ 128) q

/-- The nine collection summands of **Theorem 4.3** (ten with the factor `3`), in the order of the
theorem: `w · `SM-UD for `F`, SM-TCR for `F` (`q₃`), SM-TCR for `F` (`q₇`), SM-PRE for `F`,
SM-TCR for `H`, `Th_k`, `Th_lsl`, `3 · `SM-TCR for `F` (`q₈`), and SM-DSPR for `F` (`q₈`), the
last given by `dspr`. -/
noncomputable def slColl (dspr : ℝ → ℝ) (c : SlCharge) (B : ℝ) (ξ : ℕ) : ℝ :=
  16 * smUdBound (2 ^ 128) (ξ + c.F + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.F + B) (ξ + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.F + B) (ξ + B) +
  smPreBound (2 ^ 128) (2 ^ 128) (ξ + c.F + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.H + B) (ξ + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.thk + B) (ξ + B) +
  smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.thl + B) (ξ + B) +
  3 * smTcrBound (2 ^ 128) (2 ^ 128) (ξ + c.F + B) (ξ + B) +
  dspr (ξ + c.F + B)

/-- The two PRF terms (`PRF` and the randomizer function), each `ξ/2^128`. -/
noncomputable def prfTerms (ξ : ℕ) : ℝ := prfBound (2 ^ 128) ξ + prfBound (2 ^ 128) ξ

/-- **Theorem 4.3** at `q_s = 2^40`, every term replaced by its classical bound, the SM-DSPR term
by `dspr`. -/
noncomputable def slSum (dspr : ℝ → ℝ) (c : SlCharge) (B : ℝ) (ξ : ℕ) : ℝ :=
  prfTerms ξ + itsrSl (ξ + c.msg) + slColl dspr c B ξ

/-- **Claim 6.1** (classical): Theorem 4.3 instantiated as in Section 6.3 (Convention I,
`Vsl = 2741`) with the **conjectured** SM-DSPR row. -/
noncomputable def slBound (ξ : ℕ) : ℝ := slSum dsprRow (.uniform (Vsl shrincs)) 0 ξ

/-- The certified figures for `slBound` hold for every SM-DSPR bound below the conjectured row. -/
theorem slSum_le_slSum {dspr : ℝ → ℝ} (h : ∀ q, dspr q ≤ dsprRow q) (c : SlCharge) (B : ℝ)
    (ξ : ℕ) : slSum dspr c B ξ ≤ slSum dsprRow c B ξ := by
  unfold slSum slColl
  linarith [h (ξ + c.F + B)]

theorem slSum_le_slBound {dspr : ℝ → ℝ} (h : ∀ q, dspr q ≤ dsprRow q) (ξ : ℕ) :
    slSum dspr (.uniform (Vsl shrincs)) 0 ξ ≤ slBound ξ :=
  slSum_le_slSum h _ _ ξ

theorem slColl_eq (c : SlCharge) (B : ℝ) (ξ : ℕ) :
    slColl dsprRow c B ξ =
      (52 * (ξ + B) + 11 + 30 * c.F + 2 * c.H + 2 * c.thk + 2 * c.thl) / 2 ^ 128 := by
  unfold slColl dsprRow smDsprBound smUdBound smTcrBound smPreBound
  ring

/-- **Section 6.6**: the stateful collection terms have slope `36`, of which `27` units are
charged with the verification (the other `9` are the `|P|` summands), and constant `7`
(`c₀,sf` without the `2^-256` part). -/
theorem sfColl_uniform (V : ℕ) (ξ : ℕ) :
    sfColl (.uniform V) 0 ξ = (36 * ξ + 7 + 27 * V) / 2 ^ 128 := by
  rw [sfColl_eq]; simp only [SfCharge.uniform]; ring

/-- **Section 6.6**: the stateless collection terms (SM-DSPR by its conjectured row) have slope
`52`, of which `36` units are charged with the verification (the other `16` are the `|P|`
summands), and constant `11`. -/
theorem slColl_uniform (V : ℕ) (ξ : ℕ) :
    slColl dsprRow (.uniform V) 0 ξ = (52 * ξ + 11 + 36 * V) / 2 ^ 128 := by
  rw [slColl_eq]; simp only [SlCharge.uniform]; ring

theorem prfTerms_eq (ξ : ℕ) : prfTerms ξ = 2 * ξ / 2 ^ 128 := by
  unfold prfTerms prfBound; ring

theorem slSum_eq (c : SlCharge) (B : ℝ) (ξ : ℕ) :
    slSum dsprRow c B ξ =
      (54 * ξ + 52 * B + 11 + 30 * c.F + 2 * c.H + 2 * c.thk + 2 * c.thl) / 2 ^ 128 +
        itsrSl (ξ + c.msg) := by
  rw [slSum, slColl_eq, prfTerms_eq]
  ring

/-- **Claim 6.1**, Eq. (1), exact form: `(54 ξ + 98687)/2^128 + ν^sl_c(ξ)` with
`ν^sl_c(ξ) = (ξ + 2) Γ + P_{45,10,2^13}(ξ + 1, 2^40)` (`itsrSl_eq`). -/
theorem slBound_eq (ξ : ℕ) : slBound ξ = (54 * ξ + 98687) / 2 ^ 128 + itsrSl (ξ + 1) := by
  rw [slBound, slSum_eq, Vsl_shrincs]
  simp only [SlCharge.uniform]
  push_cast
  ring

theorem slBound_mono : Monotone slBound := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [slBound_eq, slBound_eq]
  gcongr ?_ + ?_
  · gcongr
  · exact itsrSl_mono (by omega)

/-! ## Theorem 4.1 (full scheme), Claim 6.3 Eq. (6) -/

/-- **Claim 6.3**, Eq. (6): `T₀ + q_h/2^n + Σsf + Σsl + ε_ds`, with `T₀` the two PRF terms and
the SM-rTCR term, the shared hop bounded through `B₄`, `Σsf` the seven stateful collection terms,
`Σsl` the ten stateless summands other than the PRF terms (the itsr term and `slColl`), every term
replaced by its classical bound, the SM-DSPR term by `dspr`, and `ε_ds` by `eds`. -/
noncomputable def fullSum (dspr : ℝ → ℝ) (eds : ℝ) (cs : SfCharge) (cl : SlCharge) (L ξ : ℕ) :
    ℝ :=
  prfTerms ξ + sfRtcr L (ξ + cs.msg) + hop ξ + sfColl cs 0 ξ + itsrSl (ξ + cl.msg) +
    slColl dspr cl 0 ξ + eds

/-- **Claim 6.4** (classical): Claim 6.3 Eq. (6) instantiated as in Section 6.3, with the
**conjectured** SM-DSPR row and `ε_ds ≤ 2^-128 + 10 · 2^-256`. -/
noncomputable def fullBound (L ξ : ℕ) : ℝ :=
  fullSum dsprRow epsDs (.uniform (Vsf shrincs)) (.uniform (Vsl shrincs)) L ξ

theorem fullSum_le_fullBound {dspr : ℝ → ℝ} (h : ∀ q, dspr q ≤ dsprRow q) {eds : ℝ}
    (he : eds ≤ epsDs) (L ξ : ℕ) :
    fullSum dspr eds (.uniform (Vsf shrincs)) (.uniform (Vsl shrincs)) L ξ ≤ fullBound L ξ := by
  unfold fullBound fullSum slColl
  linarith [h (ξ + (SlCharge.uniform (Vsl shrincs)).F + 0)]

theorem fullSum_eq (eds : ℝ) (cs : SfCharge) (cl : SlCharge) (L ξ : ℕ) :
    fullSum dsprRow eds cs cl L ξ =
      (92 * ξ + 7 + cs.msg + 2 * cs.grind + 20 * cs.F + 2 * cs.thl + 2 * cs.H + cs.th2 +
        11 + 30 * cl.F + 2 * cl.H + 2 * cl.thk + 2 * cl.thl) / 2 ^ 128 +
        itsrSl (ξ + cl.msg) + (ξ + cs.msg + 1) / 2 ^ 256 + eds := by
  rw [fullSum, prfTerms_eq, sfRtcr_eq, hop, diReproBound, sfColl_eq, slColl_eq]
  ring

/-- **Claim 6.4**, Eq. (9), exact form: `(92 ξ + 112115)/2^128 + ν^full_c(ξ)` with
`ν^full_c(ξ) = (ξ + 2) Γ + P_{45,10,2^13}(ξ + 1, 2^40) + (ξ + 12)/2^256`, for every `L`. -/
theorem fullBound_eq (L ξ : ℕ) :
    fullBound L ξ = (92 * ξ + 112115) / 2 ^ 128 + itsrSl (ξ + 1) + (ξ + 12) / 2 ^ 256 := by
  rw [fullBound, fullSum_eq, Vsf_shrincs, Vsl_shrincs, epsDs]
  simp only [SfCharge.uniform, SlCharge.uniform]
  push_cast
  ring

theorem fullBound_mono (L : ℕ) : Monotone (fullBound L) := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [fullBound_eq, fullBound_eq]
  gcongr ?_ + ?_ + ?_
  · gcongr
  · exact itsrSl_mono (by omega)
  · gcongr

/-! ## Core terms and reprogramming terms (Sections 6.1, 6.6, 6.7) -/

/-- The core terms of Theorem 4.2: the seven collection terms and the hash part of SM-rTCR. -/
noncomputable def sfCore (ξ : ℕ) : ℝ :=
  smRtcrHash (2 ^ 256) (ξ + 1) + sfColl (.uniform (Vsf shrincs)) 0 ξ

/-- The reprogramming terms of Theorem 4.2: the randomizer part of SM-rTCR and the hop. -/
noncomputable def sfRepro (L ξ : ℕ) : ℝ := smRtcrRand (2 ^ 128) 1 L (ξ + 1) + hop ξ

theorem sfBound_eq_core_add_repro (L ξ : ℕ) : sfBound L ξ = sfCore ξ + sfRepro L ξ := by
  unfold sfBound sfSum sfCore sfRepro sfRtcr smRtcrBound
  simp only [SfCharge.uniform]
  push_cast
  ring

/-- Section 6.6: the core terms give `(36 ξ + 13426)/2^128`, up to the hash part `(ξ+2)/2^256`. -/
theorem sfCore_eq (ξ : ℕ) : sfCore ξ = (36 * ξ + 13426) / 2 ^ 128 + (ξ + 2) / 2 ^ 256 := by
  rw [sfCore, sfColl_eq, Vsf_shrincs, smRtcrHash]
  simp only [SfCharge.uniform]
  push_cast
  ring

theorem sfCore_mono : Monotone sfCore := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [sfCore_eq, sfCore_eq]
  gcongr

/-- The core terms of Theorem 4.3: the PRF terms, the search part of itsr, and the collection
terms (SM-DSPR by its conjectured row). -/
noncomputable def slCore (ξ : ℕ) : ℝ :=
  prfTerms ξ + searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (ξ + 1) +
    slColl dsprRow (.uniform (Vsl shrincs)) 0 ξ

theorem slBound_eq_core_add_repro (ξ : ℕ) :
    slBound ξ = slCore ξ + pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (ξ + 1) (2 ^ 128) := by
  unfold slBound slSum slCore
  rw [itsrSl, itsrBound, mainBound_eq]
  simp only [SlCharge.uniform]
  ring

/-- Section 6.1: the stateless core terms, `(54 ξ + 98687)/2^128 + (ξ + 2) Γ`. -/
theorem slCore_eq (ξ : ℕ) : slCore ξ = (54 * ξ + 98687) / 2 ^ 128 + (ξ + 2) * Gam := by
  rw [slCore, slColl_eq, prfTerms_eq, searchTerm_Gam, Vsl_shrincs]
  simp only [SlCharge.uniform]
  push_cast
  ring

theorem slCore_mono : Monotone slCore := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  have := Gam_nonneg
  rw [slCore_eq, slCore_eq]
  gcongr

/-- The core terms of Theorem 4.1: all terms but the pull part of itsr, the randomizer part of
SM-rTCR and the shared hop; `ε_ds` included. -/
noncomputable def fullCore (ξ : ℕ) : ℝ :=
  prfTerms ξ + smRtcrHash (2 ^ 256) (ξ + 1) + sfColl (.uniform (Vsf shrincs)) 0 ξ +
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (ξ + 1) +
    slColl dsprRow (.uniform (Vsl shrincs)) 0 ξ + epsDs

theorem fullBound_eq_core_add_repro (L ξ : ℕ) :
    fullBound L ξ = fullCore ξ + smRtcrRand (2 ^ 128) 1 L (ξ + 1) + hop ξ +
      pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) (ξ + 1) (2 ^ 128) := by
  unfold fullBound fullSum fullCore sfRtcr smRtcrBound
  rw [itsrSl, itsrBound, mainBound_eq]
  simp only [SfCharge.uniform, SlCharge.uniform]
  push_cast
  ring

/-- Section 6.7: the core terms give `(90 ξ + 112114)/2^128 + (ξ + 2) Γ`, with `ε_ds` and up to
summands of scale `2^-256`. -/
theorem fullCore_eq (ξ : ℕ) :
    fullCore ξ = (90 * ξ + 112114) / 2 ^ 128 + (ξ + 2) * Gam + (ξ + 12) / 2 ^ 256 := by
  rw [fullCore, sfColl_eq, slColl_eq, prfTerms_eq, searchTerm_Gam, Vsf_shrincs, Vsl_shrincs,
    smRtcrHash, epsDs]
  simp only [SfCharge.uniform, SlCharge.uniform]
  push_cast
  ring

theorem fullCore_mono : Monotone fullCore := by
  intro a b h
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  have := Gam_nonneg
  rw [fullCore_eq, fullCore_eq]
  gcongr

/-! ## Convention M (Section 6.8) -/

/-- **Section 6.8**: charging a collection budget `B` to every collection term of Theorem 4.2 adds
exactly `36 B/2^128` (`c = 36`). -/
theorem sfSum_budget (c : SfCharge) (B : ℝ) (L ξ : ℕ) :
    sfSum c B L ξ = sfSum c 0 L ξ + 36 * B / 2 ^ 128 := by
  rw [sfSum_eq, sfSum_eq]; ring

/-- **Section 6.8**: charging a collection budget `B` to every collection term of Theorem 4.3 adds
exactly `52 B/2^128` (`c = 52`). -/
theorem slSum_budget (c : SlCharge) (B : ℝ) (ξ : ℕ) :
    slSum dsprRow c B ξ = slSum dsprRow c 0 ξ + 52 * B / 2 ^ 128 := by
  rw [slSum_eq, slSum_eq]; ring

/-! ## The additive constants (Section 6.4) -/

/-- `c₀,sf = 7/2^128 + 2^-256`. -/
noncomputable def c0Sf : ℝ := 7 / 2 ^ 128 + 1 / 2 ^ 256

/-- `c_V,sf = (27 · 497 + 1)/2^128 + 2^-256 = 13420/2^128 + 2^-256`. -/
noncomputable def cVSf : ℝ := (27 * 497 + 1) / 2 ^ 128 + 1 / 2 ^ 256

/-- `c₀,sl = 11/2^128 + Γ`. -/
noncomputable def c0Sl : ℝ := 11 / 2 ^ 128 + Gam

/-- `c_V,sl = 36 · 2741/2^128 + Γ + P_{45,10,2^13}(1, 2^40)`. -/
noncomputable def cVSl : ℝ :=
  36 * 2741 / 2 ^ 128 + Gam + pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128)

/-- `c₀ = 18/2^128 + Γ + 2^-256` (full scheme). -/
noncomputable def c0Full : ℝ := 18 / 2 ^ 128 + Gam + 1 / 2 ^ 256

/-- `c_V = c_V,sf + c_V,sl` (full scheme). -/
noncomputable def cVFull : ℝ := cVSf + cVSl

/-- **Section 6.4**, stateful: the value at `ξ = 0` without the verification is `c₀,sf`. -/
theorem sfSum_zero_charge (L : ℕ) : sfSum .zero 0 L 0 = c0Sf := by
  rw [sfSum_eq, c0Sf]; simp only [SfCharge.zero]; push_cast; ring

/-- **Section 6.4**, stateful: `c = c₀,sf + c_V,sf`. -/
theorem sfBound_zero (L : ℕ) : sfBound L 0 = c0Sf + cVSf := by
  rw [sfBound_eq, c0Sf, cVSf]; push_cast; ring

/-- **Section 6.4**, stateless: the value at `ξ = 0` without the verification is `c₀,sl`. -/
theorem slSum_zero_charge : slSum dsprRow .zero 0 0 = c0Sl := by
  rw [slSum_eq, c0Sl]
  simp only [SlCharge.zero]
  push_cast
  simp only [itsrSl_zero]
  ring

/-- **Section 6.4**, stateless: `c = c₀,sl + c_V,sl`. -/
theorem slBound_zero : slBound 0 = c0Sl + cVSl := by
  rw [slBound_eq, c0Sl, cVSl, zero_add, itsrSl_eq]
  push_cast
  ring

/-- **Section 6.4**, full scheme: the value at `ξ = 0` without the verification is `c₀ + ε_ds`. -/
theorem fullSum_zero_charge (L : ℕ) :
    fullSum dsprRow epsDs .zero .zero L 0 = c0Full + epsDs := by
  rw [fullSum_eq, c0Full]
  simp only [SfCharge.zero, SlCharge.zero]
  push_cast
  simp only [add_zero, itsrSl_zero]
  ring

/-- **Section 6.4**, full scheme: `c = c₀ + c_V + ε_ds`. -/
theorem fullBound_zero (L : ℕ) : fullBound L 0 = c0Full + cVFull + epsDs := by
  rw [fullBound_eq, c0Full, cVFull, cVSf, cVSl, epsDs, zero_add, itsrSl_eq]
  push_cast
  ring

end ShrincsSecurity.Concrete

end
