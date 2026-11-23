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
* **Lemma 10** (sm-ow, lines 701–712): `TwoStageAdversary.lemma10`, proved directly via the
  polynomial method (`smOw_le_of_marginalLinear`: planted target/non-target product distribution +
  Lemma 15 + rescaled endpoint Markov inequality + MVT), giving
  `Succ^{sm-ow}(A) ≤ 8(q + 1)² / |N|` for every finite abelian group `N`.
* **Corollary 12** (lines 773–792): `corollary12` (unconditional),
  `Succ^{sm-pre}(A) ≤ 8(q + 1)² / |N| + 4(q + 1)² / |M|`, for every additive commutative group
  `N` (via Lemma 10, Lemma 11, and Theorem 16), and `corollary12_xor` for `N = (ZMod 2)^n` as
  printed.

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

/-- **Lemma 10 (polynomial-method core)**: for any finite domain `X`, target function `tgt : X → N`,
and acceptance function `acc : (X → N) → ℝ` with values in `[0, 1]` that is linear in the
`2 q'`-point marginals of the oracle (`q' ≥ 1`) and vanishes whenever `∀ x, Th x ≠ tgt x`, the
uniform expectation over `Th : X → N` satisfies `uexp acc ≤ 8 q'² / |N|`. -/
theorem smOw_le_of_marginalLinear {X N : Type*} [Fintype X] [DecidableEq X] [Fintype N]
    [DecidableEq N] (hN : 1 ≤ Fintype.card N) (tgt : X → N) {acc : (X → N) → ℝ} {q' : ℕ}
    (hq : 1 ≤ q') (h01 : ∀ Th, acc Th ∈ Set.Icc (0 : ℝ) 1) (hlin : IsMarginalLinear acc (2 * q'))
    (hvan : ∀ Th, (∀ x, Th x ≠ tgt x) → acc Th = 0) :
    uexp acc ≤ 8 * (q' : ℝ) ^ 2 / Fintype.card N := by
  by_cases hN2 : Fintype.card N < 2
  · have hN1 : Fintype.card N = 1 := by omega
    have hle1 : uexp acc ≤ 1 := (uexp_mem_Icc h01).2
    have hq1 : (1 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq
    rw [hN1, Nat.cast_one, div_one]
    nlinarith
  push Not at hN2
  have hNpos : (0 : ℝ) < Fintype.card N := by exact_mod_cast (by omega : 0 < Fintype.card N)
  have hNm1_pos : (0 : ℝ) < (Fintype.card N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card N := by exact_mod_cast hN2
    linarith
  let Sub (x : X) := {r : N // r ≠ tgt x}
  let : ∀ x : X, Fintype (Sub x) := fun x => inferInstanceAs (Fintype {r : N // r ≠ tgt x})
  let : ∀ x : X, Nonempty (Sub x) := fun x => by
    have hcard : Fintype.card (Sub x) = Fintype.card N - 1 := Fintype.card_subtype_compl _
    exact Fintype.card_pos_iff.mp (by omega)
  let NonTgt := ∀ x : X, Sub x
  let Φ : NonTgt → OneBitPlanting X X N := fun Th₀ =>
    ⟨id, fun x b => if b then tgt x else (Th₀ x).1⟩
  let g : ℝ → ℝ := fun lam =>
    uexp fun Th₀ : NonTgt => boolExpect lam fun f : X → Bool => acc ((Φ Th₀).apply f)
  have hpoly : IsPolyOnUnitInterval g (2 * q') := by
    have h1 := isPolyOnUnitInterval_planted_of_marginalLinear (univ : Finset NonTgt)
      (fun _ => (Fintype.card NonTgt : ℝ)⁻¹) Φ (acc := fun _ => acc) (fun _ _ => hlin)
    refine h1.congr fun lam _ => ?_
    simp only [g, uexp, mul_sum]
  obtain ⟨Q, hQdeg, hQg⟩ := hpoly
  have hQbnd : ∀ u ∈ Set.Icc (0 : ℝ) 1, Q.eval u ∈ Set.Icc 0 1 := by
    intro u hu
    rw [← hQg u hu]
    exact uexp_mem_Icc fun Th₀ => boolExpect_mem_Icc hu fun f => h01 _
  have hQ0 : Q.eval 0 = 0 := by
    rw [← hQg 0 ⟨le_rfl, zero_le_one⟩]
    have hzero : ∀ Th₀ : NonTgt,
        boolExpect 0 (fun f : X → Bool => acc ((Φ Th₀).apply f)) = 0 := by
      intro Th₀
      unfold boolExpect
      refine sum_eq_zero fun f _ => ?_
      by_cases hf : ∃ x : X, f x = true
      · obtain ⟨x, hx⟩ := hf
        have hw : boolWeight 0 f = 0 := by
          unfold boolWeight
          exact prod_eq_zero (mem_univ x) (by simp [hx])
        simp [hw]
      · push Not at hf
        have hne : ∀ x : X, (Φ Th₀).apply f x ≠ tgt x := by
          intro x
          have hfx : f x = false := Bool.eq_false_iff.mpr (hf x)
          simp [Φ, OneBitPlanting.apply, hfx, (Th₀ x).2]
        dsimp only
        rw [hvan _ hne, mul_zero]
    simp [g, uexp, hzero]
  have hlam : (Fintype.card N : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    refine ⟨inv_nonneg.mpr hNpos.le, ?_⟩
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hN2)
  have hQg_lam : g (Fintype.card N : ℝ)⁻¹ = uexp acc := by
    have hcardSub : ∀ x : X, (Fintype.card (Sub x) : ℝ) = (Fintype.card N : ℝ) - 1 := by
      intro x
      have hc : Fintype.card (Sub x) = Fintype.card N - 1 := Fintype.card_subtype_compl _
      rw [hc, Nat.cast_sub (by omega), Nat.cast_one]
    have hcardNonTgt : (Fintype.card NonTgt : ℝ) = ((Fintype.card N : ℝ) - 1) ^ Fintype.card X := by
      rw [Fintype.card_pi, Nat.cast_prod]
      simp only [hcardSub, prod_const, card_univ]
    have hpoint : ∀ Th : X → N,
        ∑ Th₀ : NonTgt, ∑ f : X → Bool,
          (if (Φ Th₀).apply f = Th then boolWeight (Fintype.card N : ℝ)⁻¹ f else 0) =
        ((Fintype.card N : ℝ) - 1) ^ Fintype.card X * ((Fintype.card N : ℝ) ^ Fintype.card X)⁻¹ := by
      intro Th
      let e : (NonTgt × (X → Bool)) ≃ (∀ x : X, Sub x × Bool) :=
        { toFun := fun p x => (p.1 x, p.2 x)
          invFun := fun q => (fun x => (q x).1, fun x => (q x).2)
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
      rw [← Fintype.sum_prod_type']
      rw [← Equiv.sum_comp e.symm]
      have hfactor : ∀ q : (∀ x : X, Sub x × Bool),
          (if (Φ (e.symm q).1).apply (e.symm q).2 = Th
            then boolWeight (Fintype.card N : ℝ)⁻¹ (e.symm q).2 else 0) =
          ∏ x : X, (if (if (q x).2 then tgt x else (q x).1.1) = Th x
            then (if (q x).2 then (Fintype.card N : ℝ)⁻¹ else 1 - (Fintype.card N : ℝ)⁻¹)
            else 0) := by
        intro q
        by_cases hEq : (Φ (e.symm q).1).apply (e.symm q).2 = Th
        · rw [ite_eq_left hEq]
          unfold boolWeight
          refine prod_congr rfl fun x _ => ?_
          have hx : (if (q x).2 then tgt x else (q x).1.1) = Th x := congrFun hEq x
          simp [e, hx]
        · rw [ite_eq_right hEq]
          have hne : ∃ x : X, (if (q x).2 then tgt x else (q x).1.1) ≠ Th x := by
            by_contra hall
            push Not at hall
            exact hEq (funext hall)
          obtain ⟨x, hx⟩ := hne
          exact (prod_eq_zero (mem_univ x) (ite_eq_right hx)).symm
      simp_rw [hfactor]
      rw [← Fintype.prod_sum (κ := fun x => Sub x × Bool)
        (f := fun x r => if (if r.2 then tgt x else r.1.1) = Th x
          then (if r.2 then (Fintype.card N : ℝ)⁻¹ else 1 - (Fintype.card N : ℝ)⁻¹) else 0)]
      have hcoord : ∀ x : X,
          ∑ r : Sub x × Bool,
            (if (if r.2 then tgt x else r.1.1) = Th x
              then (if r.2 then (Fintype.card N : ℝ)⁻¹ else 1 - (Fintype.card N : ℝ)⁻¹) else 0) =
          ((Fintype.card N : ℝ) - 1) * (Fintype.card N : ℝ)⁻¹ := by
        intro x
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
        by_cases hTh : Th x = tgt x
        · simp only [hTh, ↓reduceIte]
          have hfalse : ∀ r : Sub x,
              (if r.1 = tgt x then 1 - (Fintype.card N : ℝ)⁻¹ else 0) = 0 :=
            fun r => ite_eq_right r.2
          simp only [hfalse, add_zero, sum_const, card_univ, nsmul_eq_mul, hcardSub]
        · have hne' : tgt x ≠ Th x := Ne.symm hTh
          simp only [hne', ↓reduceIte, zero_add]
          rw [sum_eq_single (⟨Th x, hTh⟩ : Sub x)]
          · simp only [↓reduceIte]
            field_simp [hNpos.ne']
          · intro b _ hb
            have : b.1 ≠ Th x := fun h => hb (Subtype.ext h)
            simp [this]
          · intro h; exact (h (mem_univ _)).elim
      simp_rw [hcoord, prod_const, card_univ, mul_pow, inv_pow]
    have hsum : ∑ Th₀ : NonTgt, ∑ f : X → Bool,
        boolWeight (Fintype.card N : ℝ)⁻¹ f * acc ((Φ Th₀).apply f) =
        ((Fintype.card N : ℝ) - 1) ^ Fintype.card X *
          (((Fintype.card N : ℝ) ^ Fintype.card X)⁻¹ * ∑ Th : X → N, acc Th) := by
      have hsplit : ∀ (Th₀ : NonTgt) (f : X → Bool),
          boolWeight (Fintype.card N : ℝ)⁻¹ f * acc ((Φ Th₀).apply f) =
          ∑ Th : X → N, (if (Φ Th₀).apply f = Th
            then boolWeight (Fintype.card N : ℝ)⁻¹ f else 0) * acc Th := by
        intro Th₀ f
        rw [sum_eq_single ((Φ Th₀).apply f)]
        · simp
        · intro Th _ hne; simp [Ne.symm hne]
        · intro h; exact (h (mem_univ _)).elim
      simp_rw [hsplit]
      trans ∑ Th : X → N, (∑ Th₀ : NonTgt, ∑ f : X → Bool,
          (if (Φ Th₀).apply f = Th then boolWeight (Fintype.card N : ℝ)⁻¹ f else 0)) * acc Th
      · simp_rw [sum_comm (s := (univ : Finset (X → Bool))) (t := (univ : Finset (X → N)))]
        rw [sum_comm]
        refine sum_congr rfl fun Th _ => ?_
        simp_rw [sum_mul]
      · simp_rw [hpoint, mul_assoc, ← mul_sum]
    simp only [g, uexp, boolExpect, hsum, hcardNonTgt, Fintype.card_fun, Nat.cast_pow]
    have hpow_ne : (((Fintype.card N : ℝ) - 1) ^ Fintype.card X) ≠ 0 :=
      pow_ne_zero _ hNm1_pos.ne'
    rw [inv_mul_cancel_left₀ hpow_ne]
  have hbound := eval_le_two_mul_sq_mul_of_unitInterval hQdeg hQbnd hQ0 hlam
  rw [← hQg _ ⟨hlam.1, hlam.2.trans (by norm_num)⟩, hQg_lam] at hbound
  refine hbound.trans_eq ?_
  push_cast
  ring

/-- **Lemma 10** (Undetectability, lines 701–712): for any two-stage quantum comb adversary `A`
making `q = q₁ + q₂` queries to a random oracle `Th : P × T × M → N` (`N` any finite additive
commutative group), `Succ^{sm-ow}(A) ≤ 8 (q + 1)² / |N|`. -/
theorem lemma10 :
    A.succOw ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N := by
  have hN : 1 ≤ Fintype.card N := Fintype.card_pos
  have hnonneg : (0 : ℝ) ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N := by positivity
  rcases isEmpty_or_nonempty Pp with hP | hP
  · simp only [succOw, uexp, Fintype.card_eq_zero, Nat.cast_zero, inv_zero, zero_mul]
    exact hnonneg
  have hpt : ∀ (P : Pp) (y : T → N),
      uexp (A.hopAccept y P) ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N := by
    intro P y
    have h := smOw_le_of_marginalLinear hN (fun x : Pp × T × M => y x.2.1)
      (q' := q₁ + q₂ + 1) (by omega) (A.hopAccept_mem_Icc y P)
      (A.isMarginalLinear_hopAccept y P) fun Th hTh => by
        unfold hopAccept
        refine sum_eq_zero fun o _ => ?_
        simp [hTh (P, o.1, o.2)]
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hsucc : A.succOw = uexp fun P : Pp => uexp fun y : T → N => uexp (A.hopAccept y P) := by
    unfold succOw hopAccept
    refine uexp_congr fun P => ?_
    exact uexp_comm _
  rw [hsucc]
  have hY : Nonempty (T → N) := ⟨fun _ => 0⟩
  calc (uexp fun P : Pp => uexp fun y : T → N => uexp (A.hopAccept y P))
      ≤ uexp fun _ : Pp => uexp fun _ : T → N =>
          8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N := by
        unfold uexp
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun P _ => ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => hpt P y) (by positivity)
    _ = 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N := by
        simp [uexp_const]

/-- **Corollary 12** (Quadratic sm-pre bound, lines 773–792) for every additive commutative group
`N`, combining Lemma 10, Lemma 11, and Theorem 16:
`Succ^{sm-pre}(A) ≤ 8(q + 1)² / |N| + 4(q + 1)² / |M|` with `q = q₁ + q₂`. -/
theorem corollary12 [AddGroup M] [Nonempty Pp] :
    A.succPre ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card N +
      4 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card M := by
  have h16 : smUdAdv A.hopAccept ≤ 4 * ((q₁ + q₂ + 1 : ℕ) : ℝ) ^ 2 / Fintype.card M :=
    smUdAdv_le_of_marginalLinear (A.hopAccept_mem_Icc) fun ch P => A.isMarginalLinear_hopAccept ch P
  rw [Nat.cast_add_one] at h16
  calc A.succPre ≤ A.succOw + |A.succPre - A.succOw| := by
        linarith [le_abs_self (A.succPre - A.succOw)]
    _ = A.succOw + smUdAdv A.hopAccept := by rw [lemma11]
    _ ≤ _ := add_le_add A.lemma10 h16

end TwoStageAdversary

/-- **Corollary 12** as printed, for `N = {0, 1}ⁿ` with bitwise XOR (`Fin n → ZMod 2`). -/
theorem TwoStageAdversary.corollary12_xor [AddGroup M] [Nonempty Pp] {n : ℕ}
    (A : TwoStageAdversary (Pp × T × M) (Fin n → ZMod 2) E (T → Fin n → ZMod 2) Pp (T × M) q₁ q₂) :
    A.succPre ≤ 8 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card (Fin n → ZMod 2) +
      4 * (((q₁ + q₂ : ℕ) : ℝ) + 1) ^ 2 / Fintype.card M :=
  A.corollary12

end ShrincsSecurity.Undetectability
