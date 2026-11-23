module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Evidence: the sm-ud hop (`Undetectability.pdf`, Lemma 11 and Corollary 12)

`Undetectability.pdf`, p. 8, **Definition 4** prints the advantage with absolute-value bars,
`Adv^{sm-ud} := |Pr[SM-UD ⇒ 1 | b = 1] − Pr[SM-UD ⇒ 1 | b = 0]|`, and p. 13, **Lemma 11** prints
`|Succ^{sm-pre}(A) − Succ^{sm-ow}(A)| = Adv^{sm-ud}(C)`. The text extraction drops both pairs of
bars. This file evaluates every probability of the three games, and of the reduction `C` of
Section 5.1 including its final classical query, on two small instances:

* a **fixed** function `Th : M → N` with `M = Fin 4`, `N = Fin 2`, one tweak, `p = 1`
  (`Fixed`);
* the **random-oracle** version with `Th` uniform over all `16` functions `Fin 4 → Fin 2` and an
  adversary that queries `Th` on all of `M` (`Rom`).

In both, `Succ^{sm-ow} > Succ^{sm-pre}`. The printed (absolute) Lemma 11 holds, Corollary 12's
step `Succ^{sm-pre} ≤ Succ^{sm-ow} + Adv^{sm-ud}(C)` holds, and the **signed** reading
`Succ^{sm-pre} − Succ^{sm-ow} = Adv^{sm-ud}(C)` (the reading of the extraction) fails.

With a single tweak and `p = 1`, every run makes exactly one admitted challenge query, so the list
`Q` (and `Q_C`) has exactly one entry and the only valid index is `j = 1`. The public parameter is
irrelevant (one value). All probabilities are exact counts over the uniform choices.
-/

@[expose] public section

namespace ShrincsSecurity.Evidence.SmUdHop

/-- The number of `true` entries of a list. -/
def countTrue (l : List Bool) : ℕ := l.count true

/-! ## Fixed `Th` -/

namespace Fixed

/-- `Th(x) = 0` iff `x = 0`, else `1` (one tweak, one public parameter). -/
def th (x : Fin 4) : Fin 2 := if x = 0 then 0 else 1

/-- The adversary `A`: one challenge query, then output `(j, x*) = (1, 0)`. -/
def advX : Fin 4 := 0

/-- `C₂` on challenge answer `y`: run `A₂`, make the classical query `Th(P, T₁, x*)`, output `1`
iff it equals `y₁`. -/
def cOut (y : Fin 2) : Bool := decide (th advX = y)

/-- `SM-PRE`: `y = Th(x)` for uniform `x ∈ M`; win iff `Th(x*) = y`. -/
def succPre : ℚ := (countTrue ((List.finRange 4).map fun x => decide (th advX = th x)) : ℚ) / 4

/-- `SM-OW`: `y` uniform in `N`; win iff `Th(x*) = y`. -/
def succOw : ℚ := (countTrue ((List.finRange 2).map fun y => decide (th advX = y)) : ℚ) / 2

/-- `Pr[SM-UD(C) ⇒ 1 | b]`: for `b = 0` the challenge oracle returns `Th(x)`, `x ←$ M`; for
`b = 1` it returns `y ←$ N`. -/
def prC : Bool → ℚ
  | false => (countTrue ((List.finRange 4).map fun x => cOut (th x)) : ℚ) / 4
  | true => (countTrue ((List.finRange 2).map fun y => cOut y) : ℚ) / 2

/-- **Definition 4** (p. 8), as printed: `|Pr[⇒1 | b=1] − Pr[⇒1 | b=0]|`. -/
def advUd : ℚ := |prC true - prC false|

theorem succPre_eq : succPre = 1 / 4 := by
  have : countTrue ((List.finRange 4).map fun x => decide (th advX = th x)) = 1 := by decide
  simp only [succPre, this]; norm_num

theorem succOw_eq : succOw = 1 / 2 := by
  have : countTrue ((List.finRange 2).map fun y => decide (th advX = y)) = 1 := by decide
  simp only [succOw, this]; norm_num

/-- The proof of Lemma 11: `Pr[⇒1 | b=0] = Succ^{sm-pre}`, `Pr[⇒1 | b=1] = Succ^{sm-ow}`. -/
theorem prC_eq : prC false = succPre ∧ prC true = succOw := ⟨rfl, rfl⟩

theorem advUd_eq : advUd = 1 / 4 := by
  rw [advUd, prC_eq.1, prC_eq.2, succPre_eq, succOw_eq]; norm_num [abs_of_pos]

/-- **Lemma 11 as printed** (p. 13, with bars) holds on the instance. -/
theorem lemma11_printed : |succPre - succOw| = advUd := by
  rw [advUd_eq, succPre_eq, succOw_eq]; norm_num [abs_of_neg]

/-- The **signed** reading `Succ^{sm-pre} − Succ^{sm-ow} = Adv^{sm-ud}(C)` fails: the left side is
`−1/4`, the right side `1/4`. -/
theorem lemma11_signed_false : succPre - succOw ≠ advUd := by
  rw [advUd_eq, succPre_eq, succOw_eq]; norm_num

/-- Even with Definition 4's bars removed (`Pr[b=1] − Pr[b=0]`), the signed difference is
`Succ^{sm-ow} − Succ^{sm-pre}`, the negative of the extracted Lemma 11's left side. -/
theorem signed_adv_eq : prC true - prC false = succOw - succPre := rfl

/-- **Corollary 12**'s step `Succ^{sm-pre} ≤ Succ^{sm-ow} + Adv^{sm-ud}(C)`. -/
theorem corollary12_step : succPre ≤ succOw + advUd := by
  rw [advUd_eq, succPre_eq, succOw_eq]; norm_num

end Fixed

/-! ## Random oracle `Th` -/

namespace Rom

/-- The `16` functions `Fin 4 → Fin 2`, encoded by `k : Fin 16` (bit `x` of `k`). -/
def th (k : Fin 16) (x : Fin 4) : Fin 2 := ⟨k.val / 2 ^ x.val % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The adversary `A` (classical, queries `Th` on all of `M`): if the challenge `y` has exactly one
preimage, output it; otherwise output the first `x` with `Th(x) ≠ y`, or `0` if there is none. -/
def adv (k : Fin 16) (y : Fin 2) : Fin 4 :=
  let pre := (List.finRange 4).filter fun x => th k x = y
  if pre.length = 1 then pre.headD 0
  else ((List.finRange 4).find? fun x => th k x ≠ y).getD 0

/-- The win condition of `SM-PRE`/`SM-OW` at the single entry, and the output of `C₂` after its
classical verification query `Th(P, T₁, x*)`. -/
def win (k : Fin 16) (y : Fin 2) : Bool := decide (th k (adv k y) = y)

/-- `SM-PRE` with `Th` uniform: average over `Th` and `x ←$ M`, challenge `y = Th(x)`. -/
def countPre : ℕ :=
  countTrue ((List.finRange 16).flatMap fun k => (List.finRange 4).map fun x => win k (th k x))

/-- `SM-OW` with `Th` uniform: average over `Th` and `y ←$ N`. -/
def countOw : ℕ :=
  countTrue ((List.finRange 16).flatMap fun k => (List.finRange 2).map fun y => win k y)

def succPre : ℚ := (countPre : ℚ) / 64
def succOw : ℚ := (countOw : ℚ) / 32

/-- `C₂` in world `(Th, y)`: run `A₂`, make the classical query `Th(P, T₁, x*)` on `A`'s output,
output `1` iff it equals the recorded `y₁`. -/
def cOut (k : Fin 16) (y : Fin 2) : Bool := decide (th k (adv k y) = y)

/-- `Pr[SM-UD(C) ⇒ 1 | b]` with `Th` uniform: for `b = 0` the challenge oracle returns
`Th(P, T, x)`, `x ←$ M`; for `b = 1` it returns `y ←$ N`. -/
def prC : Bool → ℚ
  | false => (countTrue ((List.finRange 16).flatMap fun k =>
      (List.finRange 4).map fun x => cOut k (th k x)) : ℚ) / 64
  | true => (countTrue ((List.finRange 16).flatMap fun k =>
      (List.finRange 2).map fun y => cOut k y) : ℚ) / 32

/-- The proof of Lemma 11: `Pr[⇒1 | b=0] = Succ^{sm-pre}`, `Pr[⇒1 | b=1] = Succ^{sm-ow}`. -/
theorem prC_eq : prC false = succPre ∧ prC true = succOw := ⟨rfl, rfl⟩

/-- **Definition 4** (p. 8), as printed. -/
def advUd : ℚ := |prC true - prC false|

theorem countPre_eq : countPre = 16 := by decide
theorem countOw_eq : countOw = 10 := by decide

theorem succPre_eq : succPre = 1 / 4 := by simp only [succPre, countPre_eq]; norm_num
theorem succOw_eq : succOw = 5 / 16 := by simp only [succOw, countOw_eq]; norm_num

theorem advUd_eq : advUd = 1 / 16 := by
  rw [advUd, prC_eq.1, prC_eq.2, succPre_eq, succOw_eq]; norm_num [abs_of_pos]

/-- `Succ^{sm-ow} > Succ^{sm-pre}` in the random-oracle model as well. -/
theorem ow_gt_pre : succPre < succOw := by rw [succPre_eq, succOw_eq]; norm_num

theorem lemma11_printed : |succPre - succOw| = advUd := by
  rw [advUd_eq, succPre_eq, succOw_eq]; norm_num [abs_of_neg]

theorem lemma11_signed_false : succPre - succOw ≠ advUd := by
  rw [advUd_eq, succPre_eq, succOw_eq]; norm_num

theorem corollary12_step : succPre ≤ succOw + advUd := by
  rw [advUd_eq, succPre_eq, succOw_eq]; norm_num

end Rom

/-- The deduction of Corollary 12 from the printed Lemma 11, for arbitrary rationals. -/
theorem corollary12_of_lemma11 {pre ow adv : ℚ} (h : |pre - ow| = adv) : pre ≤ ow + adv := by
  have := le_abs_self (pre - ow); linarith

end ShrincsSecurity.Evidence.SmUdHop

end
