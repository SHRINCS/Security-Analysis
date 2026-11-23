module

public import ShrincsSecurity.Concrete.Generic
public import ShrincsSecurity.Undetectability.Theorems.SmPre

/-!
# Quantum generic bounds (Tables 6 and 7, quantum columns) and the earlier quantum bounds

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), **Section 6.2, Table 6** (quantum column,
lines 4873–4939, read on the rendered page 77), **Section 6.5, Table 7** (quantum columns,
lines 5091–5116, page 80), the earlier quantum bounds of the `‡` note of Table 6 and of
**Remark 6.1** (Lemma C.1 [GHHM21] in Theorem F.2, Theorem G.1 Eq. (16) and Corollary C.3).

## The rows

Each row is a real function of the space sizes and the query counts, as in the classical
`Concrete.Generic`. For the two-stage properties `q` counts both stages (in the `|N|` and `|M|`
summands) and `q₁` the first stage only (in the `|P|` summands, Lemma C.8).

* `prfQ`: `2q/√|K|`;
* `smTcrQ`, `sTcrPropQ`: `32(q+1)²/|N| + 4q₁/√|P|` (corrected bounds, Remark C.7);
* `smPreQ`: `8(q+1)²/|N| + 4(q+1)²/|M|` (**Undetectability, Corollary 12**; `smPreQ_corollary12`);
* `smUdQ`: `4q²/|M|` (**Undetectability, Theorem 16**; `smUdQ_theorem16`);
* `smTcrExclQ`: `8(q+1)²/|N| + 2q₁/√|P|` (Theorem E.1);
* `smDsprQ`: `32(q+1)²/|N|`, **conjectured** ([BHK+19, BH19]); as in the classical files the
  sums take the bound substituted for the SM-DSPR term as an argument;
* `smRtcrQ`: Theorem G.1, `e = 1` Eq. (17): `8(q+1)²/|N| + 4√(S'/|R|)`; `e = 1/2` Eq. (18):
  `16(q+1)²/|N| + 32 S'/|R|`; with Lemma C.1 Eq. (16): `8(q+1)²/|N| + (3pK/2)√((q+pK+1)/|R|)`;
* `itsrQ`: Theorem F.3, `e = 1` Eq. (14): `4√(S/|K|) + 8(q+1)²Γ`; `e = 1/2` Eq. (15):
  `32 S/|K| + 16(q+1)²Γ`; with Lemma C.1 (Theorem F.2, quantum line):
  `(3p/2)√((q+p+1)/|K|) + 8(q+1)²Γ`;
* `diReproQ` (Corollary C.3, distinguishers `B₁`, `B₄`): `e = 1`: `4√(S/|X₁|)`; `e = 1/2`: the
  additive part `32 S/|X₁|` of `Succⁱ ≤ 2 Succⁱ⁺¹ + 32 S/|X₁|`, whose factor `2` falls on the later
  terms (`Form.factor`); with Lemma C.1: `(3/2) q_s √((q_s+q_h+1)/|X₁|)`.

Here `S = reproS p q = pq + p(p−1)/2 + 1` (Table 6 caption, Table 7: `S_sl`, `S_L`), and
`S' = reproS (pK) q`.

The earlier bounds of the `‡` note: `smUdQOld = 12q/√|M|` ([HK22, Lemma 3]) and
`smPreQOld = 8(q+1)²/|N| + 12(q+1)/√|M|` ([Kud25, Theorem 6.2.10]).

## Forms

`Form` names the bound used at each of the three places of the reprogramming step (Section 6.5):
`one` (Lemma C.3, `e = 1`), `half` (Corollary C.1, `e = 1/2`) and `ghhm` (Lemma C.1, used only for
the comparison of Remark 6.1). `minF f` is the minimum over the forms `one` and `half`, the
column "minimum" of Table 5 at one place.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete.Quantum

/-! ## Table 6, quantum column -/

/-- **Table 6**, PRF row (quantum): `Adv^prf ≤ 2q/√|K|`. -/
noncomputable def prfQ (K q : ℝ) : ℝ := 2 * q / √K

/-- **Table 6**, SM-TCR row (quantum, corrected by Remark C.7): `32(q+1)²/|N| + 4q₁/√|P|`. -/
noncomputable def smTcrQ (N P q q₁ : ℝ) : ℝ := 32 * (q + 1) ^ 2 / N + 4 * q₁ / √P

/-- **Table 6**, SM-PRE row (quantum, [Kud26b] = Undetectability Corollary 12):
`8(q+1)²/|N| + 4(q+1)²/|M|`. -/
noncomputable def smPreQ (N M q : ℝ) : ℝ := 8 * (q + 1) ^ 2 / N + 4 * (q + 1) ^ 2 / M

/-- **Table 6**, SM-UD row (quantum, [Kud26b] = Undetectability Theorem 16): `4q²/|M|`. -/
noncomputable def smUdQ (M q : ℝ) : ℝ := 4 * q ^ 2 / M

/-- **Table 6**, SM-TCR-EXCL row (quantum, Section E): `8(q+1)²/|N| + 2q₁/√|P|`. -/
noncomputable def smTcrExclQ (N P q q₁ : ℝ) : ℝ := 8 * (q + 1) ^ 2 / N + 2 * q₁ / √P

/-- **Table 6**, S-TCR(+C) row (quantum, corrected by Remark C.7): `32(q+1)²/|N| + 4q₁/√|P|`. -/
noncomputable def sTcrPropQ (N P q q₁ : ℝ) : ℝ := 32 * (q + 1) ^ 2 / N + 4 * q₁ / √P

/-- **Table 6**, SM-DSPR row (quantum): `32(q+1)²/|N|`. **Conjectured** ([BHK+19, BH19]). -/
noncomputable def smDsprQ (N q : ℝ) : ℝ := 32 * (q + 1) ^ 2 / N

/-- `S = pq + p(p−1)/2 + 1` (Table 6 caption; Table 7: `S_sl = reproS 2^40`, `S_L = reproS L`;
Corollary C.3 with `p = q_s`, `q = q_h`). -/
noncomputable def reproS (p q : ℝ) : ℝ := p * q + p * (p - 1) / 2 + 1

/-- The bound used at a place of the reprogramming step (Section 6.5). -/
inductive Form
  /-- Lemma C.3 with `e = 1`. -/
  | one
  /-- Corollary C.1 (Lemma C.3 with `e = 1/2`). -/
  | half
  /-- Lemma C.1 [GHHM21], the earlier bound of Remark 6.1. -/
  | ghhm
  deriving DecidableEq

/-- The factor that a form at a hop puts on the terms bounded after it: `2` for `e = 1/2`
(Corollary C.1, Remark C.5), `1` otherwise. -/
def Form.factor : Form → ℚ
  | .one => 1
  | .half => 2
  | .ghhm => 1

/-- The minimum over the forms `e = 1` and `e = 1/2` at one place. -/
noncomputable def minF (f : Form → ℝ) : ℝ := min (f .one) (f .half)

theorem minF_le_one (f : Form → ℝ) : minF f ≤ f .one := min_le_left _ _

theorem minF_le_half (f : Form → ℝ) : minF f ≤ f .half := min_le_right _ _

theorem le_minF {f : Form → ℝ} {c : ℝ} (h₁ : c ≤ f .one) (h₂ : c ≤ f .half) : c ≤ minF f :=
  le_min h₁ h₂

theorem minF_mono {f g : Form → ℝ} (h : ∀ e, f e ≤ g e) : minF f ≤ minF g :=
  min_le_min (h _) (h _)

/-- **Table 6**, SM-rTCR rows (quantum), Theorem G.1: `e = 1` is Eq. (17), `e = 1/2` Eq. (18),
and `ghhm` Eq. (16) (Lemma C.1, the earlier bound of Remark 6.1); `S' = pKq + pK(pK−1)/2 + 1`,
`q' = q + pK`. -/
noncomputable def smRtcrQ : Form → (N R K p q : ℝ) → ℝ
  | .one, N, R, K, p, q => 8 * (q + 1) ^ 2 / N + 4 * √(reproS (p * K) q / R)
  | .half, N, R, K, p, q => 16 * (q + 1) ^ 2 / N + 32 * reproS (p * K) q / R
  | .ghhm, N, R, K, p, q => 8 * (q + 1) ^ 2 / N + 3 * p * K / 2 * √((q + p * K + 1) / R)

/-- **Table 6**, itsr rows (quantum): Theorem F.3, `e = 1` Eq. (14), `e = 1/2` Eq. (15); `ghhm`
is the quantum line of Theorem F.2 (Lemma C.1), the earlier bound of Remark 6.1. `Γ = Γ_{h,k,t}(p)`,
`|K| = nK`. -/
noncomputable def itsrQ : Form → (Γ nK p q : ℝ) → ℝ
  | .one, Γ, nK, p, q => 4 * √(reproS p q / nK) + 8 * (q + 1) ^ 2 * Γ
  | .half, Γ, nK, p, q => 32 * reproS p q / nK + 16 * (q + 1) ^ 2 * Γ
  | .ghhm, Γ, nK, p, q => 3 * p / 2 * √((q + p + 1) / nK) + 8 * (q + 1) ^ 2 * Γ

/-- **Table 7**, reprogramming hop (Corollary C.3, distinguishers `B₁`, `B₄`): `e = 1`:
`4√(S/|X₁|)`; `e = 1/2`: the additive part `32 S/|X₁|` (the factor `2` on the later terms is
`Form.factor`); `ghhm`: `(3/2) q_s √((q_s + q_h + 1)/|X₁|)` (Lemma C.1). -/
noncomputable def diReproQ : Form → (X₁ qs qh : ℝ) → ℝ
  | .one, X₁, qs, qh => 4 * √(reproS qs qh / X₁)
  | .half, X₁, qs, qh => 32 * reproS qs qh / X₁
  | .ghhm, X₁, qs, qh => 3 / 2 * qs * √((qs + qh + 1) / X₁)

/-! ## The earlier sm-ud and sm-pre bounds (`‡` note of Table 6) -/

/-- Earlier quantum sm-ud bound `12q/√|M|` ([HK22, Lemma 3]). -/
noncomputable def smUdQOld (M q : ℝ) : ℝ := 12 * q / √M

/-- Earlier quantum sm-pre bound `8(q+1)²/|N| + 12(q+1)/√|M|` ([Kud25, Theorem 6.2.10]). -/
noncomputable def smPreQOld (N M q : ℝ) : ℝ := 8 * (q + 1) ^ 2 / N + 12 * (q + 1) / √M

/-- The sm-ud and sm-pre rows used: `quad` the quadratic rows of Table 6 ([Kud26b]), `earlier`
those of the `‡` note (Remark 6.1). -/
inductive Rows
  | quad
  | earlier
  deriving DecidableEq

/-- The sm-ud row. -/
noncomputable def Rows.ud : Rows → (M q : ℝ) → ℝ
  | .quad => smUdQ
  | .earlier => smUdQOld

/-- The sm-pre row. -/
noncomputable def Rows.pre : Rows → (N M q : ℝ) → ℝ
  | .quad => smPreQ
  | .earlier => smPreQOld

/-! ## The quadratic rows are the theorems of the Undetectability paper -/

section Undetectability

open ShrincsSecurity.Undetectability

variable {Pp T M N : Type*} [Fintype Pp] [DecidableEq Pp] [Fintype T] [DecidableEq T]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N] [AddCommGroup N]
  [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace M] [MeasurableSingletonClass M]
  {E : Type*} [Fintype E] {q₁ q₂ : ℕ}

omit [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace M]
  [MeasurableSingletonClass M] in
/-- The SM-UD row of Table 6 is **Theorem 16** of the Undetectability paper
(`TwoStageAdversary.smUdAdv_le`), with `q = q₁ + q₂`. -/
theorem smUdQ_theorem16 [AddGroup M] [Nonempty Pp]
    (A : TwoStageAdversary (Pp × T × M) N E (T → N) Pp Bool q₁ q₂) :
    smUdAdv A.smUdAccept ≤ smUdQ (Fintype.card M) (q₁ + q₂ : ℕ) :=
  A.smUdAdv_le

/-- The SM-PRE row of Table 6 is **Corollary 12** of the Undetectability paper
(`TwoStageAdversary.corollary12`), given Lemma 10 (quoted there from [11]). -/
theorem smPreQ_corollary12 [AddGroup M] [Nonempty Pp]
    (A : TwoStageAdversary (Pp × T × M) N E (T → N) Pp (T × M) q₁ q₂)
    (lemma10 : A.succOw ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N) :
    A.succPre ≤ smPreQ (Fintype.card N) (Fintype.card M) (q₁ + q₂ : ℕ) :=
  A.corollary12 lemma10

end Undetectability

/-! ## Square roots -/

theorem sqrt_two_pow_128 : √((2 : ℝ) ^ 128) = 2 ^ 64 := by
  rw [show (2 : ℝ) ^ 128 = (2 ^ 64) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]

/-- `√(x/2^128) = √x/2^64`. -/
theorem sqrt_div_two_pow_128 (x : ℝ) : √(x / 2 ^ 128) = √x / 2 ^ 64 := by
  rw [Real.sqrt_div' _ (by positivity), sqrt_two_pow_128]

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0` (the split of Section 6.6). -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

end ShrincsSecurity.Concrete.Quantum

end
