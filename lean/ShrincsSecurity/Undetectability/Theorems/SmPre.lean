module

public import ShrincsSecurity.Undetectability.Theorems.SmUd

/-!
# The sm-ud hop and the quadratic sm-pre bound

Undetectability paper (`notes/txt/Undetectability.txt`), Section 5:

* **Definitions 5 and 6** (sm-pre, sm-ow, lines 399–414): `succPre`, `succOw`, for a two-stage
  comb adversary whose final measurement outputs a tweak and a preimage candidate `(T, x*)`.
* **Lemma 11** (The sm-ud hop, lines 727–770): from the sm-pre adversary `A`, the sm-ud adversary
  `C` runs `A` with its challenge answers, then checks `Th(P, T, x*) = y_T` with one classical
  query. `hopAccept A` is the acceptance probability of `C`;
  `lemma11 : |Succ^{sm-pre}(A) - Succ^{sm-ow}(A)| = Adv^{sm-ud}(C)`, from
  `Pr[C ⇒ 1 | b = 0] = Succ^{sm-pre}(A)` and `Pr[C ⇒ 1 | b = 1] = Succ^{sm-ow}(A)`.
  The query count of `C` enters Corollary 12 only through Lemma 1:
  `isMarginalLinear_hopAccept` shows that the acceptance probability of `C` is linear in the
  `2(q + 1)`-point marginals of `Th` for `q = q₁ + q₂`, as for a `(q + 1)`-query algorithm.
* **Lemma 10** (sm-ow, lines 701–712) is quoted by the paper from [11] and not proved there; it
  enters `corollary12` as the explicit hypothesis `lemma10`.
* **Corollary 12** (lines 773–792): `corollary12`,
  `Succ^{sm-pre}(A) ≤ 8(q + 1)² / |N| + 4(q + 1)² / |M|`, for every additive commutative group
  `N` given Lemma 10 (via Theorem 16), and `corollary12_xor` for `N = (ZMod 2)^n` as printed.

## Modelling choices

As in `Theorems/SmUd.lean`, the adversary is described for each table `ch : T → N` of challenge
answers, which it may consult classically; the targets are `y_T = ch(T)`, and the output `(T, x*)`
names the tweak whose target it inverts (the index `j` into the list `Q` of Definition 5). `C` is
given by its acceptance probability: the classical check `Th(P, T, x*) = y_T` is evaluated on the
measured output of `A`. We do not build `C` as a comb with a `(q₂ + 1)`-th query slot; what the
paper uses about `C` beyond Lemma 11 is that Theorem 16 applies to it with `q + 1` queries, and
that is `isMarginalLinear_hopAccept` (a classical query on a basis state contributes the factor
`1[Th(w) = y] = 1[Th(w) = y]²`, two points, exactly as one quantum query).
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Finset

variable {Pp T M N : Type*} [Fintype Pp] [DecidableEq Pp] [Fintype T] [DecidableEq T]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N] [AddCommGroup N]
  [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace M] [MeasurableSingletonClass M]
  {E : Type*} [Fintype E] {q₁ q₂ : ℕ}

namespace TwoStageAdversary

variable (A : TwoStageAdversary (Pp × T × M) N E (T → N) Pp (T × M) q₁ q₂)

/-- `Succ^{sm-pre}(A)` (Definition 5): `P ←$ P`, `Th` uniform, `x_T ←$ M` per tweak, targets
`y_T = Th(P, T, x_T)`; the experiment outputs `1` if the output `(T, x*)` of `A` satisfies
`Th(P, T, x*) = y_T`. -/
noncomputable def succPre : ℝ :=
  uexp fun P : Pp => uexp fun Th : Pp × T × M → N => uexp fun x : T → M =>
    ∑ o : T × M, A.outProb (fun τ => Th (P, τ, x τ)) P Th o *
      if Th (P, o.1, o.2) = Th (P, o.1, x o.1) then 1 else 0

/-- `Succ^{sm-ow}(A)` (Definition 6): as `succPre` with uniform targets `y_T ←$ N`. -/
noncomputable def succOw : ℝ :=
  uexp fun P : Pp => uexp fun Th : Pp × T × M → N => uexp fun y : T → N =>
    ∑ o : T × M, A.outProb y P Th o * if Th (P, o.1, o.2) = y o.1 then 1 else 0

/-- The acceptance probability of the sm-ud adversary `C` of Section 5.1 with challenge answers
`ch`, second-stage input `P` and oracle `Th`: `C` runs `A` with challenge answers `ch` and
outputs `1` if the output `(T, x*)` of `A` satisfies `Th(P, T, x*) = ch(T)`. -/
noncomputable def hopAccept (ch : T → N) (P : Pp) (Th : Pp × T × M → N) : ℝ :=
  ∑ o : T × M, A.outProb ch P Th o * if Th (P, o.1, o.2) = ch o.1 then 1 else 0

omit [MeasurableSingletonClass T] [MeasurableSingletonClass M] in
/-- Proof of Lemma 11: with `b = 0`, `C` wins exactly when `A` wins the sm-pre game. -/
theorem smUdReal_hopAccept : smUdReal A.hopAccept = A.succPre := rfl

omit [MeasurableSingletonClass T] [MeasurableSingletonClass M] in
/-- Proof of Lemma 11: with `b = 1`, `C` wins exactly when `A` wins the sm-ow game. -/
theorem smUdRand_hopAccept : smUdRand A.hopAccept = A.succOw := rfl

omit [MeasurableSingletonClass T] [MeasurableSingletonClass M] in
/-- **Lemma 11** (The sm-ud hop, lines 744–747):
`|Succ^{sm-pre}(A) - Succ^{sm-ow}(A)| = Adv^{sm-ud}(C)`. -/
theorem lemma11 : |A.succPre - A.succOw| = smUdAdv A.hopAccept := by
  rw [smUdAdv, smUdReal_hopAccept, smUdRand_hopAccept, abs_sub_comm]

theorem hopAccept_mem_Icc (ch : T → N) (P : Pp) (Th : Pp × T × M → N) :
    A.hopAccept ch P Th ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sum_nonneg fun o _ => mul_nonneg (A.outProb_nonneg ch P Th o) (by split_ifs <;> simp),
    ?_⟩
  calc A.hopAccept ch P Th ≤ ∑ o : T × M, A.outProb ch P Th o :=
        sum_le_sum fun o _ => mul_le_of_le_one_right (A.outProb_nonneg ch P Th o)
          (by split_ifs <;> simp)
    _ ≤ 1 := A.sum_outProb_le_one ch P Th

/-- **Query count of `C`** (Lemma 11): the acceptance probability of `C` is linear in the
`2(q₁ + q₂ + 1)`-point marginals of `Th`, as for an algorithm with `q₁ + q₂ + 1` queries. -/
theorem isMarginalLinear_hopAccept (ch : T → N) (P : Pp) :
    IsMarginalLinear (A.hopAccept ch P) (2 * (q₁ + q₂ + 1)) := by
  rw [← isMarginalPoly_iff_isMarginalLinear]
  refine (IsMarginalPoly.sum univ fun o _ => ((IsMarginalPoly.indicator_two (P, o.1, o.2)
    (ch o.1)).smul (A.isMarginalPoly_outProb ch P o)).cast (by ring)).congr fun Th => ?_
  simp only [hopAccept, smul_eq_mul, mul_comm]

/-- **Corollary 12** (Quadratic sm-pre bound, lines 773–792) for every additive commutative group
`N`, given **Lemma 10** for `A` (`8(q + 1)² / |N|`, quoted from [11]) as the hypothesis
`lemma10`: `Succ^{sm-pre}(A) ≤ 8(q + 1)² / |N| + 4(q + 1)² / |M|` with `q = q₁ + q₂`. -/
theorem corollary12 [AddGroup M] [Nonempty Pp]
    (lemma10 : A.succOw ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N) :
    A.succPre ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N +
      4 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card M := by
  have h16 : smUdAdv A.hopAccept ≤ 4 * ((q₁ + q₂ + 1 : ℕ) : ℝ) ^ 2 / Fintype.card M :=
    smUdAdv_le_of_marginalLinear (A.hopAccept_mem_Icc) fun ch P => A.isMarginalLinear_hopAccept ch P
  rw [Nat.cast_add_one] at h16
  calc A.succPre ≤ A.succOw + |A.succPre - A.succOw| := by
        linarith [le_abs_self (A.succPre - A.succOw)]
    _ = A.succOw + smUdAdv A.hopAccept := by rw [lemma11]
    _ ≤ _ := add_le_add lemma10 h16

end TwoStageAdversary

/-- **Corollary 12** as printed, for `N = {0, 1}ⁿ` with bitwise XOR (`Fin n → ZMod 2`), given
Lemma 10. -/
theorem TwoStageAdversary.corollary12_xor [AddGroup M] [Nonempty Pp] {n : ℕ}
    (A : TwoStageAdversary (Pp × T × M) (Fin n → ZMod 2) E (T → Fin n → ZMod 2) Pp (T × M) q₁ q₂)
    (lemma10 : A.succOw ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card (Fin n → ZMod 2)) :
    A.succPre ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card (Fin n → ZMod 2) +
      4 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card M :=
  A.corollary12 lemma10

end ShrincsSecurity.Undetectability
