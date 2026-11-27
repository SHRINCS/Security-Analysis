module

public import ShrincsSecurity.Concrete.Quantum.Enc
public import ShrincsSecurity.Concrete.Paths

/-!
# Theorems 4.1–4.3 at the proposed parameters (quantum): the sums, their closed forms, and the
rounded forms of Claims 6.1, 6.2 and 6.4

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Section 6.3** (lines 4942–4988),
the quantum part of **Section 6.4** (lines 5048–5089), **Section 6.5** (lines 5091–5138),
**Section 6.6** with **Claims 6.1 and 6.2** (Eqs. (2), (4), (5); lines 5141–5309, pages 81–83) and
**Section 6.7** with **Claims 6.3 and 6.4** (Eqs. (7), (8), (10), (11); lines 5311–5428,
pages 83–85).

## The sums

Every term of Theorems 4.1–4.3 is replaced by its quantum row of Table 6 (`Quantum.Generic`) at the
spaces of Section 6.3 (`2^128`, and `|N| = 2^256` for the hash part of the SM-rTCR term), with the
counts of the classical files (`Concrete.Paths`): collection terms at `q := ξ + V^f`, their `|P|`
summands at `q₁ := ξ`, the itsr and SM-rTCR terms at `q := ξ + 1` and the hop at `q_h := ξ`. Each of
the three places of the reprogramming step carries a `Form` (`ei` itsr, `er` SM-rTCR, `eh` hop);
with `eh = half` the terms behind the hop are doubled (Corollary 4.2, Claim 6.3 Eq. (8)), the
SM-rTCR term and `ε_ds` are not. The sm-ud and sm-pre rows are chosen by `Rows`; the SM-DSPR term
is an argument `dspr`, the figures use the conjectured row `dsprRowQ`.

* `slSumQ`: Theorem 4.3; `sfSumQ`: Theorem 4.2; `fullSumQ`: Claim 6.3, Eqs. (7) (`eh = one`) and
  (8) (`eh = half`).
* `slQ`, `sfQ`, `fullQ`: Section 6.3 (Convention I, `V = 2741`, `497`); `slMin`, `sfMin`,
  `fullMin`: the column "minimum" of Table 5 (pointwise minimum over the forms `e = 1`, `e = 1/2`
  at every place).

## Closed forms

* `slQ_half_eq` (**Claim 6.1**, Eq. (2)), `sfQ_half_half_eq` (**Claim 6.2**, Eq. (4)),
  `sfQ_half_one_le` (Eq. (5)), `fullQ_half_half_half_eq` (**Claim 6.4**, Eq. (10)),
  `fullQ_half_half_one_le` (Eq. (11)); Eqs. (5) and (11) split the square root of the hop by
  `√(a + b) ≤ √a + √b`, as printed.
* `claim_6_1_rounded`, `claim_6_2_rounded_*`, `claim_6_4_rounded_*`: the rounded forms.

## Enclosures

`slEnc`, `sfEnc`, `fullEnc` (and `eq5Enc`, `eq11Enc`) give every sum as `Enc` (`Quantum.Enc`):
`slSumQ_eq_enc`, `sfSumQ_eq_enc`, `fullSumQ_eq_enc`.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete.Quantum

open ShrincsSecurity.Concrete ShrincsSecurity.Scheme

/-! ## The terms at the parameters of Section 6.3 -/

/-- The two PRF terms (quantum), each `2ξ/√2^128`. -/
noncomputable def prfTermsQ (ξ : ℕ) : ℝ := prfQ (2 ^ 128) ξ + prfQ (2 ^ 128) ξ

/-- The itsr term of Theorem 4.3: `p = 2^40`, `|K| = 2^128`, `Γ = Γ_{45,10,2^13}(2^40)`. -/
noncomputable def itsrSlQ (e : Form) (q : ℕ) : ℝ := itsrQ e Gam (2 ^ 128) (2 ^ 40) q

/-- The SM-rTCR term of Theorems 4.1 and 4.2: `K = 1`, `p = L`, `|N| = 2^256`, `|R| = 2^128`. -/
noncomputable def rtcrQ (e : Form) (L q : ℕ) : ℝ := smRtcrQ e (2 ^ 256) (2 ^ 128) 1 L q

/-- The reprogramming hop of Theorems 4.1 and 4.2 (`B₁`, `B₄`): `q_s = L`, `q_h = ξ`,
`|X₁| = |R| = 2^128`. -/
noncomputable def hopQ (e : Form) (L ξ : ℕ) : ℝ := diReproQ e (2 ^ 128) L ξ

/-- The seven collection terms of **Theorem 4.2** (quantum), in the order of the theorem:
S-TCR(Prop) for `H_grind`, `w · `SM-UD for `F`, SM-TCR for `F`, SM-PRE for `F`, SM-TCR for `Th_lsf`,
SM-TCR for `H`, SM-TCR-EXCL for `Th_{2∪lsf}`. -/
noncomputable def collSfQ (rw : Rows) (c : SfCharge) (ξ : ℕ) : ℝ :=
  sTcrPropQ (2 ^ 128) (2 ^ 128) (ξ + c.grind) ξ + 16 * rw.ud (2 ^ 128) (ξ + c.F) +
  smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.F) ξ + rw.pre (2 ^ 128) (2 ^ 128) (ξ + c.F) +
  smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.thl) ξ + smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.H) ξ +
  smTcrExclQ (2 ^ 128) (2 ^ 128) (ξ + c.th2) ξ

/-- The conjectured **SM-DSPR row** of Table 6 (quantum) at `|N| = 2^128`. -/
noncomputable def dsprRowQ (q : ℝ) : ℝ := smDsprQ (2 ^ 128) q

/-- The nine collection summands of **Theorem 4.3** (quantum), in the order of the theorem, the
SM-DSPR term given by `dspr`. -/
noncomputable def collSlQ (rw : Rows) (dspr : ℝ → ℝ) (c : SlCharge) (ξ : ℕ) : ℝ :=
  16 * rw.ud (2 ^ 128) (ξ + c.F) +
  smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.F) ξ + smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.F) ξ +
  rw.pre (2 ^ 128) (2 ^ 128) (ξ + c.F) +
  smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.H) ξ + smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.thk) ξ +
  smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.thl) ξ + 3 * smTcrQ (2 ^ 128) (2 ^ 128) (ξ + c.F) ξ +
  dspr (ξ + c.F)

/-- **Theorem 4.3** (quantum) at `q_s = 2^40`, form `ei` in the itsr proof. -/
noncomputable def slSumQ (rw : Rows) (dspr : ℝ → ℝ) (c : SlCharge) (ei : Form) (ξ : ℕ) : ℝ :=
  prfTermsQ ξ + itsrSlQ ei (ξ + c.msg) + collSlQ rw dspr c ξ

/-- **Theorem 4.2** (quantum) with `K = 1` at `q_s = L`, form `er` in the SM-rTCR proof and `eh`
at the hop; with `eh = half` the collection terms are doubled (Corollary 4.2). -/
noncomputable def sfSumQ (rw : Rows) (c : SfCharge) (er eh : Form) (L ξ : ℕ) : ℝ :=
  rtcrQ er L (ξ + c.msg) + hopQ eh L ξ + (eh.factor : ℝ) * collSfQ rw c ξ

/-- **Claim 6.3**, Eqs. (7) and (8): `T₀ + hop + f (Σsf + Σsl) + ε_ds`, with `f = 2` for
`e = 1/2` at the shared hop and `1` otherwise. -/
noncomputable def fullSumQ (rw : Rows) (dspr : ℝ → ℝ) (eds : ℝ) (cs : SfCharge) (cl : SlCharge)
    (ei er eh : Form) (L ξ : ℕ) : ℝ :=
  prfTermsQ ξ + rtcrQ er L (ξ + cs.msg) + hopQ eh L ξ +
    (eh.factor : ℝ) * (collSfQ rw cs ξ + itsrSlQ ei (ξ + cl.msg) + collSlQ rw dspr cl ξ) + eds

/-- Theorem 4.3 (quantum) instantiated as in Section 6.3, with the **conjectured** SM-DSPR row. -/
noncomputable def slQ (ei : Form) (ξ : ℕ) : ℝ :=
  slSumQ .quad dsprRowQ (.uniform (Vsl shrincs)) ei ξ

/-- Theorem 4.2 (quantum) instantiated as in Section 6.3. -/
noncomputable def sfQ (er eh : Form) (L ξ : ℕ) : ℝ :=
  sfSumQ .quad (.uniform (Vsf shrincs)) er eh L ξ

/-- Theorem 4.1 (quantum, Claim 6.3) instantiated as in Section 6.3, with the **conjectured**
SM-DSPR row and `ε_ds ≤ 2^-128 + 10 · 2^-256`. -/
noncomputable def fullQ (ei er eh : Form) (L ξ : ℕ) : ℝ :=
  fullSumQ .quad dsprRowQ epsDs (.uniform (Vsf shrincs)) (.uniform (Vsl shrincs)) ei er eh L ξ

/-- Table 5, column "minimum", stateless. -/
noncomputable def slMin (ξ : ℕ) : ℝ := minF fun ei => slQ ei ξ

/-- Table 5, column "minimum", stateful. -/
noncomputable def sfMin (L ξ : ℕ) : ℝ := minF fun er => minF fun eh => sfQ er eh L ξ

/-- Table 5, column "minimum", full scheme. -/
noncomputable def fullMin (L ξ : ℕ) : ℝ :=
  minF fun ei => minF fun er => minF fun eh => fullQ ei er eh L ξ

/-- The certified figures for the stateless sums hold for every SM-DSPR bound below the
conjectured row. -/
theorem slSumQ_le_slSumQ {dspr : ℝ → ℝ} (h : ∀ q, dspr q ≤ dsprRowQ q) (rw : Rows)
    (c : SlCharge) (ei : Form) (ξ : ℕ) : slSumQ rw dspr c ei ξ ≤ slSumQ rw dsprRowQ c ei ξ := by
  unfold slSumQ collSlQ
  linarith [h (ξ + c.F)]

theorem Form.factor_nonneg (e : Form) : (0 : ℝ) ≤ e.factor := by
  cases e <;> norm_num [Form.factor]

theorem fullSumQ_le_fullSumQ {dspr : ℝ → ℝ} (h : ∀ q, dspr q ≤ dsprRowQ q) {eds : ℝ}
    (he : eds ≤ epsDs) (rw : Rows) (cs : SfCharge) (cl : SlCharge) (ei er eh : Form) (L ξ : ℕ) :
    fullSumQ rw dspr eds cs cl ei er eh L ξ ≤ fullSumQ rw dsprRowQ epsDs cs cl ei er eh L ξ := by
  unfold fullSumQ collSlQ
  have := h (ξ + cl.F)
  have := Form.factor_nonneg eh
  nlinarith

/-! ## Enclosures -/

/-- `S = pq + p(p−1)/2 + 1` over `ℕ`. -/
def reproSN (p q : ℕ) : ℕ := p * q + p * (p - 1) / 2 + 1

theorem cast_reproSN (p q : ℕ) : (reproSN p q : ℝ) = reproS p q := by
  unfold reproSN reproS
  have h2 : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_div h2 (by norm_num), Nat.cast_mul]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · rw [Nat.cast_sub hp]; push_cast; ring

/-- The two PRF terms. -/
def prfEnc (ξ : ℕ) : Enc := .ofQ (4 * ξ / 2 ^ 64)

/-- The itsr term at `q`. -/
def itsrEnc : Form → ℕ → Enc
  | .one, q => ⟨0, 8 * ((q : ℚ) + 1) ^ 2, [(4 / 2 ^ 64, reproSN (2 ^ 40) q)]⟩
  | .half, q => ⟨32 * (reproSN (2 ^ 40) q : ℚ) / 2 ^ 128, 16 * ((q : ℚ) + 1) ^ 2, []⟩
  | .ghhm, q => ⟨0, 8 * ((q : ℚ) + 1) ^ 2, [(3 * 2 ^ 40 / 2 / 2 ^ 64, q + 2 ^ 40 + 1)]⟩

/-- The SM-rTCR term at `q`. -/
def rtcrEnc : Form → ℕ → ℕ → Enc
  | .one, L, q => ⟨8 * ((q : ℚ) + 1) ^ 2 / 2 ^ 256, 0, [(4 / 2 ^ 64, reproSN L q)]⟩
  | .half, L, q =>
    .ofQ (16 * ((q : ℚ) + 1) ^ 2 / 2 ^ 256 + 32 * (reproSN L q : ℚ) / 2 ^ 128)
  | .ghhm, L, q => ⟨8 * ((q : ℚ) + 1) ^ 2 / 2 ^ 256, 0, [(3 * L / 2 / 2 ^ 64, q + L + 1)]⟩

/-- The hop at `q_h = ξ`. -/
def hopEnc : Form → ℕ → ℕ → Enc
  | .one, L, ξ => ⟨0, 0, [(4 / 2 ^ 64, reproSN L ξ)]⟩
  | .half, L, ξ => .ofQ (32 * (reproSN L ξ : ℚ) / 2 ^ 128)
  | .ghhm, L, ξ => ⟨0, 0, [(3 / 2 * L / 2 ^ 64, L + ξ + 1)]⟩

/-- `smTcrQ` at `|N| = |P| = 2^128`, rational. -/
def tcrR (q q₁ : ℚ) : ℚ := 32 * (q + 1) ^ 2 / 2 ^ 128 + 4 * q₁ / 2 ^ 64

/-- `smTcrExclQ` at `|N| = |P| = 2^128`, rational. -/
def exclR (q q₁ : ℚ) : ℚ := 8 * (q + 1) ^ 2 / 2 ^ 128 + 2 * q₁ / 2 ^ 64

/-- The sm-ud row at `|M| = 2^128`, rational. -/
def Rows.udR : Rows → ℚ → ℚ
  | .quad, q => 4 * q ^ 2 / 2 ^ 128
  | .earlier, q => 12 * q / 2 ^ 64

/-- The sm-pre row at `|N| = |M| = 2^128`, rational. -/
def Rows.preR : Rows → ℚ → ℚ
  | .quad, q => 8 * (q + 1) ^ 2 / 2 ^ 128 + 4 * (q + 1) ^ 2 / 2 ^ 128
  | .earlier, q => 8 * (q + 1) ^ 2 / 2 ^ 128 + 12 * (q + 1) / 2 ^ 64

/-- The stateful collection terms, rational. -/
def collSfR (rw : Rows) (c : SfCharge) (ξ : ℕ) : ℚ :=
  tcrR (ξ + c.grind) ξ + 16 * rw.udR (ξ + c.F) + tcrR (ξ + c.F) ξ + rw.preR (ξ + c.F) +
    tcrR (ξ + c.thl) ξ + tcrR (ξ + c.H) ξ + exclR (ξ + c.th2) ξ

/-- The stateless collection terms with the conjectured SM-DSPR row, rational. -/
def collSlR (rw : Rows) (c : SlCharge) (ξ : ℕ) : ℚ :=
  16 * rw.udR (ξ + c.F) + tcrR (ξ + c.F) ξ + tcrR (ξ + c.F) ξ + rw.preR (ξ + c.F) +
    tcrR (ξ + c.H) ξ + tcrR (ξ + c.thk) ξ + tcrR (ξ + c.thl) ξ + 3 * tcrR (ξ + c.F) ξ +
    32 * ((ξ : ℚ) + c.F + 1) ^ 2 / 2 ^ 128

/-- `ε_ds = 2^-128 + 10 · 2^-256`. -/
def epsDsQ : ℚ := 1 / 2 ^ 128 + 10 / 2 ^ 256

def slEnc (rw : Rows) (c : SlCharge) (ei : Form) (ξ : ℕ) : Enc :=
  prfEnc ξ + itsrEnc ei (ξ + c.msg) + .ofQ (collSlR rw c ξ)

def sfEnc (rw : Rows) (c : SfCharge) (er eh : Form) (L ξ : ℕ) : Enc :=
  rtcrEnc er L (ξ + c.msg) + hopEnc eh L ξ + (Enc.ofQ (collSfR rw c ξ)).smul eh.factor

def fullEnc (rw : Rows) (cs : SfCharge) (cl : SlCharge) (ei er eh : Form) (L ξ : ℕ) : Enc :=
  prfEnc ξ + rtcrEnc er L (ξ + cs.msg) + hopEnc eh L ξ +
    (Enc.ofQ (collSfR rw cs ξ) + itsrEnc ei (ξ + cl.msg) + .ofQ (collSlR rw cl ξ)).smul
      eh.factor + .ofQ epsDsQ

theorem sqSum_nil : sqSum [] = 0 := by simp [sqSum]

theorem sqSum_cons (x : ℚ × ℕ) (s : List (ℚ × ℕ)) :
    sqSum (x :: s) = x.1 * √(x.2 : ℝ) + sqSum s := by simp [sqSum]

theorem sqSum_one (c : ℚ) (n : ℕ) : sqSum [(c, n)] = c * √(n : ℝ) := by simp [sqSum]

theorem prfTermsQ_eq (ξ : ℕ) : prfTermsQ ξ = (prfEnc ξ).val := by
  rw [prfEnc, Enc.val_ofQ, prfTermsQ, prfQ, sqrt_two_pow_128]; push_cast; ring

theorem itsrSlQ_eq (e : Form) (q : ℕ) : itsrSlQ e q = (itsrEnc e q).val := by
  cases e <;> simp only [itsrSlQ, itsrQ, itsrEnc, Enc.val, sqSum_one, sqSum_nil,
    sqrt_div_two_pow_128, cast_reproSN] <;> push_cast <;> (try simp only [cast_reproSN]) <;>
    push_cast <;> ring_nf

theorem rtcrQ_eq (e : Form) (L q : ℕ) : rtcrQ e L q = (rtcrEnc e L q).val := by
  cases e <;> simp only [rtcrQ, smRtcrQ, rtcrEnc, Enc.val, Enc.ofQ, sqSum_one, sqSum_nil,
    sqrt_div_two_pow_128, mul_one, cast_reproSN] <;> push_cast <;> (try simp only [cast_reproSN]) <;>
    ring

theorem hopQ_eq (e : Form) (L ξ : ℕ) : hopQ e L ξ = (hopEnc e L ξ).val := by
  cases e <;> simp only [hopQ, diReproQ, hopEnc, Enc.val, Enc.ofQ, sqSum_one, sqSum_nil,
    sqrt_div_two_pow_128, cast_reproSN] <;> push_cast <;> (try simp only [cast_reproSN]) <;> ring

theorem collSfQ_eq (rw : Rows) (c : SfCharge) (ξ : ℕ) : collSfQ rw c ξ = collSfR rw c ξ := by
  cases rw <;> simp only [collSfQ, collSfR, Rows.ud, Rows.pre, Rows.udR, Rows.preR, smUdQ, smPreQ,
    smUdQOld, smPreQOld, smTcrQ, sTcrPropQ, smTcrExclQ, tcrR, exclR, sqrt_two_pow_128] <;>
    push_cast <;> ring

theorem collSlQ_eq (rw : Rows) (c : SlCharge) (ξ : ℕ) :
    collSlQ rw dsprRowQ c ξ = collSlR rw c ξ := by
  cases rw <;> simp only [collSlQ, collSlR, Rows.ud, Rows.pre, Rows.udR, Rows.preR, smUdQ, smPreQ,
    smUdQOld, smPreQOld, smTcrQ, smDsprQ, dsprRowQ, tcrR, sqrt_two_pow_128] <;>
    push_cast <;> ring

theorem slSumQ_eq_enc (rw : Rows) (c : SlCharge) (ei : Form) (ξ : ℕ) :
    slSumQ rw dsprRowQ c ei ξ = (slEnc rw c ei ξ).val := by
  rw [slEnc, Enc.val_add, Enc.val_add, Enc.val_ofQ, slSumQ, prfTermsQ_eq, itsrSlQ_eq, collSlQ_eq]

theorem sfSumQ_eq_enc (rw : Rows) (c : SfCharge) (er eh : Form) (L ξ : ℕ) :
    sfSumQ rw c er eh L ξ = (sfEnc rw c er eh L ξ).val := by
  rw [sfEnc, Enc.val_add, Enc.val_add, Enc.val_smul, Enc.val_ofQ, sfSumQ, rtcrQ_eq, hopQ_eq,
    collSfQ_eq]

theorem fullSumQ_eq_enc (rw : Rows) (cs : SfCharge) (cl : SlCharge) (ei er eh : Form) (L ξ : ℕ) :
    fullSumQ rw dsprRowQ epsDs cs cl ei er eh L ξ = (fullEnc rw cs cl ei er eh L ξ).val := by
  rw [fullEnc, Enc.val_add, Enc.val_add, Enc.val_add, Enc.val_add, Enc.val_smul, Enc.val_add,
    Enc.val_add, Enc.val_ofQ, Enc.val_ofQ, Enc.val_ofQ, fullSumQ, prfTermsQ_eq, rtcrQ_eq, hopQ_eq,
    collSfQ_eq, itsrSlQ_eq, collSlQ_eq, epsDs, epsDsQ]
  push_cast; ring

theorem slQ_eq_enc (ei : Form) (ξ : ℕ) :
    slQ ei ξ = (slEnc .quad (.uniform 2741) ei ξ).val := by
  rw [slQ, Vsl_shrincs, slSumQ_eq_enc]

theorem sfQ_eq_enc (er eh : Form) (L ξ : ℕ) :
    sfQ er eh L ξ = (sfEnc .quad (.uniform 497) er eh L ξ).val := by
  rw [sfQ, Vsf_shrincs, sfSumQ_eq_enc]

theorem fullQ_eq_enc (ei er eh : Form) (L ξ : ℕ) :
    fullQ ei er eh L ξ = (fullEnc .quad (.uniform 497) (.uniform 2741) ei er eh L ξ).val := by
  rw [fullQ, Vsf_shrincs, Vsl_shrincs, fullSumQ_eq_enc]

/-! ## Monotonicity in the query count -/

theorem reproS_mono {p : ℝ} (hp : 0 ≤ p) {q q' : ℝ} (h : q ≤ q') : reproS p q ≤ reproS p q' := by
  unfold reproS; gcongr

theorem itsrSlQ_mono (e : Form) : Monotone (itsrSlQ e) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hG := Gam_nonneg
  have hS := reproS_mono (p := 2 ^ 40) (by positivity) h
  cases e <;> simp only [itsrSlQ, itsrQ]
  · exact add_le_add (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hS (by positivity))) (by norm_num))
      (mul_le_mul_of_nonneg_right (by gcongr) hG)
  · exact add_le_add (by gcongr) (mul_le_mul_of_nonneg_right (by gcongr) hG)
  · exact add_le_add (by gcongr) (mul_le_mul_of_nonneg_right (by gcongr) hG)

theorem rtcrQ_mono (e : Form) (L : ℕ) : Monotone (rtcrQ e L) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hS := reproS_mono (p := (L : ℝ) * 1) (by positivity) h
  cases e <;> simp only [rtcrQ, smRtcrQ]
  · exact add_le_add (by gcongr) (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hS (by positivity))) (by norm_num))
  · exact add_le_add (by gcongr) (by gcongr)
  · exact add_le_add (by gcongr) (by gcongr)

theorem hopQ_mono (e : Form) (L : ℕ) : Monotone (hopQ e L) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hS := reproS_mono (p := (L : ℝ)) (by positivity) h
  cases e <;> simp only [hopQ, diReproQ]
  · exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hS (by positivity))) (by norm_num)
  · gcongr
  · gcongr

theorem collSfQ_mono (rw : Rows) (c : SfCharge) : Monotone (collSfQ rw c) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  rw [collSfQ_eq, collSfQ_eq]
  have : (collSfR rw c a : ℝ) ≤ collSfR rw c b := by
    cases rw <;> simp only [collSfR, Rows.udR, Rows.preR, tcrR, exclR] <;> push_cast <;> gcongr
  exact this

theorem collSlQ_mono (rw : Rows) (c : SlCharge) : Monotone (collSlQ rw dsprRowQ c) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  rw [collSlQ_eq, collSlQ_eq]
  have : (collSlR rw c a : ℝ) ≤ collSlR rw c b := by
    cases rw <;> simp only [collSlR, Rows.udR, Rows.preR, tcrR] <;> push_cast <;> gcongr
  exact this

theorem prfTermsQ_mono : Monotone prfTermsQ := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [prfTermsQ, prfQ]; gcongr

theorem slSumQ_mono (rw : Rows) (c : SlCharge) (ei : Form) :
    Monotone (slSumQ rw dsprRowQ c ei) := fun a b h =>
  add_le_add (add_le_add (prfTermsQ_mono h) (itsrSlQ_mono ei (by omega))) (collSlQ_mono rw c h)

theorem sfSumQ_mono (rw : Rows) (c : SfCharge) (er eh : Form) (L : ℕ) :
    Monotone (sfSumQ rw c er eh L) := fun a b h =>
  add_le_add (add_le_add (rtcrQ_mono er L (by omega)) (hopQ_mono eh L h))
    (mul_le_mul_of_nonneg_left (collSfQ_mono rw c h) (Form.factor_nonneg eh))

theorem fullSumQ_mono (rw : Rows) (cs : SfCharge) (cl : SlCharge) (ei er eh : Form) (L : ℕ) :
    Monotone (fullSumQ rw dsprRowQ epsDs cs cl ei er eh L) := fun a b h =>
  add_le_add (add_le_add (add_le_add (add_le_add (prfTermsQ_mono h)
    (rtcrQ_mono er L (by omega))) (hopQ_mono eh L h))
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (collSfQ_mono rw cs h)
      (itsrSlQ_mono ei (by omega))) (collSlQ_mono rw cl h)) (Form.factor_nonneg eh))) le_rfl

theorem slQ_mono (ei : Form) : Monotone (slQ ei) := slSumQ_mono _ _ _

theorem sfQ_mono (er eh : Form) (L : ℕ) : Monotone (sfQ er eh L) := sfSumQ_mono _ _ _ _ _

theorem fullQ_mono (ei er eh : Form) (L : ℕ) : Monotone (fullQ ei er eh L) :=
  fullSumQ_mono _ _ _ _ _ _ _

theorem minF_mono' {B : Form → ℕ → ℝ} (h : ∀ e, Monotone (B e)) :
    Monotone fun ξ => minF fun e => B e ξ :=
  fun _ _ hab => minF_mono fun e => h e hab

theorem slMin_mono : Monotone slMin := minF_mono' slQ_mono

theorem sfMin_mono (L : ℕ) : Monotone (sfMin L) :=
  minF_mono' fun er => minF_mono' fun eh => sfQ_mono er eh L

theorem fullMin_mono (L : ℕ) : Monotone (fullMin L) :=
  minF_mono' fun ei => minF_mono' fun er => minF_mono' fun eh => fullQ_mono ei er eh L

/-! ## Claims 6.1, 6.2 and 6.4: closed forms -/

/-- `ν^q_sl(ξ) = 16(ξ + 2)² Γ` (Claim 6.1). -/
noncomputable def nuSl (ξ : ℕ) : ℝ := 16 * ((ξ : ℝ) + 2) ^ 2 * Gam

/-- `ν^q_sf(ξ) = 16(ξ + 2)²/2^256` (Claim 6.2). -/
noncomputable def nuSf (ξ : ℕ) : ℝ := 16 * ((ξ : ℝ) + 2) ^ 2 / 2 ^ 256

/-- `ν^q_f(ξ) = 16 f (ξ + 2)² Γ + (16(ξ + 2)² + 10)/2^256` (Claim 6.4). -/
noncomputable def nuFull (f : ℝ) (ξ : ℕ) : ℝ :=
  16 * f * ((ξ : ℝ) + 2) ^ 2 * Gam + (16 * ((ξ : ℝ) + 2) ^ 2 + 10) / 2 ^ 256

/-- **Claim 6.1**, Eq. (2), exact form: the stateless bound with `e = 1/2` in the itsr proof is
`36ξ/2^64 + (364ξ² + (2^45 + 1996048)ξ + 2^84 + 2^44 + 2736406416)/2^128 + ν^q_sl(ξ)`. -/
theorem slQ_half_eq (ξ : ℕ) :
    slQ .half ξ = 36 * ξ / 2 ^ 64 +
      (364 * (ξ : ℝ) ^ 2 + (2 ^ 45 + 1996048) * ξ + 2 ^ 84 + 2 ^ 44 + 2736406416) / 2 ^ 128 +
      nuSl ξ := by
  rw [slQ, Vsl_shrincs]
  simp only [slSumQ, prfTermsQ, prfQ, itsrSlQ, itsrQ, collSlQ, Rows.ud, Rows.pre, smUdQ, smPreQ,
    smTcrQ, dsprRowQ, smDsprQ, SlCharge.uniform, reproS, sqrt_two_pow_128, nuSl]
  push_cast; ring

/-- **Eq. (4)** of Claim 6.2 as printed. -/
noncomputable def eq4 (L ξ : ℕ) : ℝ :=
  36 * ξ / 2 ^ 64 + (424 * (ξ : ℝ) ^ 2 + (64 * L + 422048) * ξ + 32 * (L : ℝ) ^ 2 + 105026400) /
    2 ^ 128 + nuSf ξ

/-- **Eq. (5)** of Claim 6.2 as printed (the square root of the hop split). -/
noncomputable def eq5 (L ξ : ℕ) : ℝ :=
  18 * ξ / 2 ^ 64 + (212 * (ξ : ℝ) ^ 2 + (32 * L + 211024) * ξ + 16 * (L : ℝ) ^ 2 + 16 * L +
    52513200) / 2 ^ 128 + 4 * √(L : ℝ) * √(ξ : ℝ) / 2 ^ 64 +
    4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128) + nuSf ξ

/-- **Claim 6.2**, Eq. (4): `e = 1/2` at both places. -/
theorem sfQ_half_half_eq (L ξ : ℕ) : sfQ .half .half L ξ = eq4 L ξ := by
  rw [sfQ, Vsf_shrincs]
  simp only [sfSumQ, rtcrQ, smRtcrQ, hopQ, diReproQ, collSfQ, Rows.ud, Rows.pre, smUdQ, smPreQ,
    smTcrQ, sTcrPropQ, smTcrExclQ, SfCharge.uniform, reproS, sqrt_two_pow_128, Form.factor, eq4,
    nuSf]
  push_cast; ring

/-- The hop with `e = 1`, split as in Section 6.6:
`4√(S_L(ξ)/2^128) ≤ 4√L √ξ/2^64 + 4√((L(L−1)/2 + 1)/2^128)`. -/
theorem hop_one_le (L ξ : ℕ) :
    hopQ .one L ξ ≤ 4 * √(L : ℝ) * √(ξ : ℝ) / 2 ^ 64 +
      4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128) := by
  have hc : (0 : ℝ) ≤ (L : ℝ) * (L - 1) / 2 + 1 := by
    have := cast_reproSN L 0
    simp only [reproS, Nat.cast_zero, mul_zero, zero_add] at this
    rw [← this]; positivity
  simp only [hopQ, diReproQ, reproS, sqrt_div_two_pow_128]
  have := sqrt_add_le_add_sqrt (a := (L : ℝ) * ξ) (by positivity) hc
  rw [Real.sqrt_mul (by positivity)] at this
  rw [show (L : ℝ) * ξ + L * (L - 1) / 2 + 1 = L * ξ + (L * (L - 1) / 2 + 1) by ring]
  have h64 : (0 : ℝ) < 2 ^ 64 := by positivity
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  exact div_le_div_of_nonneg_right (by linarith) h64.le

/-- **Claim 6.2**, Eq. (5): `e = 1` at the hop and `e = 1/2` in the SM-rTCR proof. -/
theorem sfQ_half_one_le (L ξ : ℕ) : sfQ .half .one L ξ ≤ eq5 L ξ := by
  have hh := hop_one_le L ξ
  have : sfQ .half .one L ξ = 18 * ξ / 2 ^ 64 + (212 * (ξ : ℝ) ^ 2 + (32 * L + 211024) * ξ +
      16 * (L : ℝ) ^ 2 + 16 * L + 52513200) / 2 ^ 128 + hopQ .one L ξ + nuSf ξ := by
    rw [sfQ, Vsf_shrincs]
    simp only [sfSumQ, rtcrQ, smRtcrQ, collSfQ, Rows.ud, Rows.pre, smUdQ, smPreQ,
      smTcrQ, sTcrPropQ, smTcrExclQ, SfCharge.uniform, reproS, sqrt_two_pow_128, Form.factor, nuSf]
    push_cast; ring
  rw [this, eq5]; linarith

/-- **Eq. (10)** of Claim 6.4 as printed. -/
noncomputable def eq10 (L ξ : ℕ) : ℝ :=
  104 * ξ / 2 ^ 64 + (1152 * (ξ : ℝ) ^ 2 + (2 ^ 46 + 64 * L + 4414144) * ξ) / 2 ^ 128 +
    (2 ^ 85 + 2 ^ 45 + 32 * (L : ℝ) ^ 2 + 5577839233) / 2 ^ 128 + nuFull 2 ξ

/-- **Eq. (11)** of Claim 6.4 as printed (the square root of the hop split). -/
noncomputable def eq11 (L ξ : ℕ) : ℝ :=
  54 * ξ / 2 ^ 64 + (576 * (ξ : ℝ) ^ 2 + (2 ^ 45 + 32 * L + 2207072) * ξ + 2 ^ 84 + 2 ^ 44 +
    16 * (L : ℝ) ^ 2 + 16 * L + 2788919617) / 2 ^ 128 + 4 * √(L : ℝ) * √(ξ : ℝ) / 2 ^ 64 +
    4 * √(((L : ℝ) * (L - 1) / 2 + 1) / 2 ^ 128) + nuFull 1 ξ

/-- **Claim 6.4**, Eq. (10): `e = 1/2` at the hop and inside both property proofs. -/
theorem fullQ_half_half_half_eq (L ξ : ℕ) : fullQ .half .half .half L ξ = eq10 L ξ := by
  rw [fullQ, Vsf_shrincs, Vsl_shrincs]
  simp only [fullSumQ, prfTermsQ, prfQ, rtcrQ, smRtcrQ, hopQ, diReproQ, collSfQ, collSlQ,
    itsrSlQ, itsrQ, Rows.ud, Rows.pre, smUdQ, smPreQ, smTcrQ, sTcrPropQ, smTcrExclQ, dsprRowQ,
    smDsprQ, SfCharge.uniform, SlCharge.uniform, reproS, sqrt_two_pow_128, Form.factor, eq10,
    nuFull, epsDs]
  push_cast; ring

/-- **Claim 6.4**, Eq. (11): `e = 1` at the hop, `e = 1/2` inside both property proofs. -/
theorem fullQ_half_half_one_le (L ξ : ℕ) : fullQ .half .half .one L ξ ≤ eq11 L ξ := by
  have hh := hop_one_le L ξ
  have : fullQ .half .half .one L ξ = 54 * ξ / 2 ^ 64 + (576 * (ξ : ℝ) ^ 2 +
      (2 ^ 45 + 32 * L + 2207072) * ξ + 2 ^ 84 + 2 ^ 44 + 16 * (L : ℝ) ^ 2 + 16 * L +
      2788919617) / 2 ^ 128 + hopQ .one L ξ + nuFull 1 ξ := by
    rw [fullQ, Vsf_shrincs, Vsl_shrincs]
    simp only [fullSumQ, prfTermsQ, prfQ, rtcrQ, smRtcrQ, collSfQ, collSlQ,
      itsrSlQ, itsrQ, Rows.ud, Rows.pre, smUdQ, smPreQ, smTcrQ, sTcrPropQ, smTcrExclQ, dsprRowQ,
      smDsprQ, SfCharge.uniform, SlCharge.uniform, reproS, sqrt_two_pow_128, Form.factor,
      nuFull, epsDs]
    push_cast; ring
  rw [this, eq11]; linarith

/-- The quantum bound of **Claim 6.2**: the minimum of Eqs. (4) and (5). -/
noncomputable def claimSf (L ξ : ℕ) : ℝ := min (eq4 L ξ) (eq5 L ξ)

/-- The quantum bound of **Claim 6.4**: the minimum of Eqs. (10) and (11). -/
noncomputable def claimFull (L ξ : ℕ) : ℝ := min (eq10 L ξ) (eq11 L ξ)

/-- The bound of Claim 6.2 bounds the column "minimum" of Table 5 from above. -/
theorem sfMin_le_claimSf (L ξ : ℕ) : sfMin L ξ ≤ claimSf L ξ :=
  le_min ((minF_le_half _).trans ((minF_le_half _).trans (sfQ_half_half_eq L ξ).le))
    ((minF_le_half _).trans ((minF_le_one _).trans (sfQ_half_one_le L ξ)))

/-- The bound of Claim 6.4 bounds the column "minimum" of Table 5 from above. -/
theorem fullMin_le_claimFull (L ξ : ℕ) : fullMin L ξ ≤ claimFull L ξ :=
  le_min ((minF_le_half _).trans ((minF_le_half _).trans ((minF_le_half _).trans
      (fullQ_half_half_half_eq L ξ).le)))
    ((minF_le_half _).trans ((minF_le_half _).trans ((minF_le_one _).trans
      (fullQ_half_half_one_le L ξ))))

/-! ## Enclosures of Eqs. (5) and (11) -/

theorem cast_half_pred (L : ℕ) : ((L * (L - 1) / 2 + 1 : ℕ) : ℝ) = (L : ℝ) * (L - 1) / 2 + 1 := by
  have := cast_reproSN L 0
  simp only [reproSN, reproS, mul_zero, zero_add, Nat.cast_zero] at this
  exact this

theorem eq4_eq_enc (L ξ : ℕ) : eq4 L ξ = (sfEnc .quad (.uniform 497) .half .half L ξ).val := by
  rw [← sfQ_half_half_eq, sfQ_eq_enc]

/-- Eq. (5) as `Enc`. -/
def eq5Enc (L ξ : ℕ) : Enc :=
  ⟨18 * ξ / 2 ^ 64 + (212 * (ξ : ℚ) ^ 2 + (32 * L + 211024) * ξ + 16 * (L : ℚ) ^ 2 + 16 * L +
    52513200) / 2 ^ 128 + 16 * ((ξ : ℚ) + 2) ^ 2 / 2 ^ 256, 0,
    [(4 / 2 ^ 64, L * ξ), (4 / 2 ^ 64, L * (L - 1) / 2 + 1)]⟩

theorem eq5_eq_enc (L ξ : ℕ) : eq5 L ξ = (eq5Enc L ξ).val := by
  simp only [eq5, eq5Enc, Enc.val, sqSum_cons, sqSum_nil, nuSf, sqrt_div_two_pow_128,
    cast_half_pred, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg L)]
  push_cast; ring

/-- Eq. (10) as `Enc`. -/
def eq10Enc (L ξ : ℕ) : Enc := fullEnc .quad (.uniform 497) (.uniform 2741) .half .half .half L ξ

theorem eq10_eq_enc (L ξ : ℕ) : eq10 L ξ = (eq10Enc L ξ).val := by
  rw [← fullQ_half_half_half_eq, fullQ_eq_enc, eq10Enc]

/-- Eq. (11) as `Enc`. -/
def eq11Enc (L ξ : ℕ) : Enc :=
  ⟨54 * ξ / 2 ^ 64 + (576 * (ξ : ℚ) ^ 2 + (2 ^ 45 + 32 * L + 2207072) * ξ + 2 ^ 84 + 2 ^ 44 +
    16 * (L : ℚ) ^ 2 + 16 * L + 2788919617) / 2 ^ 128 + (16 * ((ξ : ℚ) + 2) ^ 2 + 10) / 2 ^ 256,
    16 * ((ξ : ℚ) + 2) ^ 2, [(4 / 2 ^ 64, L * ξ), (4 / 2 ^ 64, L * (L - 1) / 2 + 1)]⟩

theorem eq11_eq_enc (L ξ : ℕ) : eq11 L ξ = (eq11Enc L ξ).val := by
  simp only [eq11, eq11Enc, Enc.val, sqSum_cons, sqSum_nil, nuFull, sqrt_div_two_pow_128,
    cast_half_pred, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg L)]
  push_cast; ring

theorem eq4_mono (L : ℕ) : Monotone (eq4 L) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [eq4, nuSf]; gcongr

theorem eq5_mono (L : ℕ) : Monotone (eq5 L) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [eq5, nuSf]; gcongr

theorem nuFull_mono {f : ℝ} (hf : 0 ≤ f) : Monotone (nuFull f) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [nuFull]
  exact add_le_add (mul_le_mul_of_nonneg_right (by gcongr) Gam_nonneg) (by gcongr)

theorem eq10_mono (L : ℕ) : Monotone (eq10 L) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [eq10]
  exact add_le_add (add_le_add (add_le_add (by gcongr) (by gcongr)) le_rfl)
    (nuFull_mono (by norm_num) hab)

theorem eq11_mono (L : ℕ) : Monotone (eq11 L) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  simp only [eq11]
  exact add_le_add (add_le_add (add_le_add (add_le_add (by gcongr) (by gcongr)) (by gcongr))
    le_rfl) (nuFull_mono (by norm_num) hab)

theorem claimSf_mono (L : ℕ) : Monotone (claimSf L) :=
  fun _ _ h => min_le_min (eq4_mono L h) (eq5_mono L h)

theorem claimFull_mono (L : ℕ) : Monotone (claimFull L) :=
  fun _ _ h => min_le_min (eq10_mono L h) (eq11_mono L h)

end ShrincsSecurity.Concrete.Quantum

end
