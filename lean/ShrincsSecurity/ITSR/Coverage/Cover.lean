module

public import ShrincsSecurity.ITSR.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Counting covered positions (Lemma 1)

`ITSR-Classical.pdf`, Lemma 1. For a fixed digest `u` and a set `F` of positions, the number of
challenge tapes `V : Fin r → Digest ι k t` whose position sets cover `u` at every position of `F`
is `N'^r Γ_{|F|}(r)`, where `N' = |ι| t^k`. In particular the conditional coverage probability does
not depend on `u`.

The proof is inclusion–exclusion over `A ⊆ F` on the positions that fail to be covered, against
the binomial expansion `Γ_j(r) = ∑_s C(j, s) (-1)^s (1 - θ + θ (1 - 1/t)^s)^r`.
-/

@[expose] public section

open Finset

namespace ShrincsSecurity.ITSR

variable {ι : Type} [DecidableEq ι] {k t : ℕ}

/-- Membership in the position set of the image of a tape. -/
theorem mem_posSet_image {r : ℕ} (V : Fin r → Digest ι k t) (I : ι) (i : Fin k) (x : Fin t) :
    x ∈ posSet (univ.image V) I i ↔ ∃ l, (V l).1 = I ∧ (V l).2 i = x := by
  simp only [posSet, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨⟨l, rfl⟩, h1⟩, h2⟩
    exact ⟨l, h1, h2⟩
  · rintro ⟨l, h1, h2⟩
    exact ⟨V l, ⟨⟨l, rfl⟩, h1⟩, h2⟩

/-- Binomial expansion of `Γ_j(r)` (the inclusion–exclusion form used in the proof of Lemma 1):
`Γ_j(r) = ∑_{s=0}^{j} C(j, s) (-1)^s (θ (1 - 1/t)^s + 1 - θ)^r`. -/
theorem gamma_eq_sum (θ : ℝ) (t r j : ℕ) :
    gamma θ t r j = ∑ s ∈ range (j + 1),
      (j.choose s : ℝ) * (-1) ^ s * (θ * (1 - 1 / (t : ℝ)) ^ s + (1 - θ)) ^ r := by
  have hexp : ∀ (y : ℝ) (g : ℕ), (1 - y ^ g) ^ j =
      ∑ s ∈ range (j + 1), (j.choose s : ℝ) * (-1) ^ s * (y ^ s) ^ g := by
    intro y g
    rw [sub_eq_neg_add, add_pow]
    refine sum_congr rfl fun s _ => ?_
    rw [one_pow, mul_one, neg_pow, ← pow_mul, ← pow_mul, mul_comm g s]
    ring
  simp only [gamma]
  simp_rw [hexp, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [add_pow, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [mul_pow]
  ring

variable [Fintype ι]

/-- The number of tapes `V : Fin r → Digest` avoiding, for every position `i ∈ A`, the digests in
instance `I` with `i`-th coordinate `J i`. -/
theorem sum_avoid (I : ι) (J : Fin k → Fin t) (A : Finset (Fin k)) :
    ∑ v : Digest ι k t, ∏ i ∈ A, (1 - if v.1 = I ∧ v.2 i = J i then (1 : ℝ) else 0) =
      ((t : ℝ) - 1) ^ A.card * (t : ℝ) ^ (k - A.card) +
        ((Fintype.card ι : ℝ) - 1) * (t : ℝ) ^ k := by
  rw [Fintype.sum_prod_type]
  have hI : ∀ I' : ι, ∑ c : Fin k → Fin t,
      ∏ i ∈ A, (1 - if (I', c).1 = I ∧ (I', c).2 i = J i then (1 : ℝ) else 0) =
        if I' = I then ((t : ℝ) - 1) ^ A.card * (t : ℝ) ^ (k - A.card) else (t : ℝ) ^ k := by
    intro I'
    have hprod : ∀ c : Fin k → Fin t,
        ∏ i ∈ A, (1 - if (I', c).1 = I ∧ (I', c).2 i = J i then (1 : ℝ) else 0) =
          ∏ i, (if i ∈ A then (1 - if I' = I ∧ c i = J i then (1 : ℝ) else 0) else 1) := by
      intro c
      rw [prod_ite_mem, univ_inter]
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun i (x : Fin t) =>
      if i ∈ A then (1 - if I' = I ∧ x = J i then (1 : ℝ) else 0) else 1)]
    have hsum : ∀ i : Fin k, ∑ x : Fin t,
        (if i ∈ A then (1 - if I' = I ∧ x = J i then (1 : ℝ) else 0) else 1) =
          if i ∈ A then (if I' = I then (t : ℝ) - 1 else t) else t := by
      intro i
      split_ifs with hA hII
      · simp [sum_sub_distrib, hII]
      · simp [hII]
      · simp
    simp_rw [hsum]
    split_ifs with hII
    · rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter]
      congr 2
      rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ _),
        card_univ, Fintype.card_fin]
    · simp
  simp_rw [hI]
  rw [sum_ite, sum_const, sum_const, filter_eq', filter_ne']
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨I⟩
  simp [card_erase_of_mem, Nat.cast_sub hpos]

/-- An existential indicator as one minus a product of complementary indicators. -/
theorem ite_exists_eq_one_sub_prod {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    [Decidable (∃ a, P a)] :
    (if ∃ a, P a then (1 : ℝ) else 0) = 1 - ∏ a, (1 - if P a then (1 : ℝ) else 0) := by
  have h : ∀ a, (1 - if P a then (1 : ℝ) else 0) = if ¬ P a then 1 else 0 := by
    intro a; split_ifs <;> simp
  simp_rw [h, Fintype.prod_boole]
  by_cases hP : ∃ a, P a
  · obtain ⟨a, ha⟩ := hP
    simp only [show ∃ a, P a from ⟨a, ha⟩, show ¬ ∀ a, ¬ P a from fun h' => h' a ha]
    simp
  · simp only [show ∀ a, ¬ P a from fun a ha => hP ⟨a, ha⟩]
    simp

variable [NeZero t]

/-- **Lemma 1** (counting form): for every digest `u` and positions `F`, the tapes
`V : Fin r → Digest` covering `u` at the positions `F` number `N'^r Γ_{|F|}(r)`, where
`N' = |ι| t^k`. -/
theorem sum_cover (r : ℕ) (u : Digest ι k t) (F : Finset (Fin k)) :
    ∑ V : Fin r → Digest ι k t,
        (if ∀ i ∈ F, u.2 i ∈ posSet (univ.image V) u.1 i then (1 : ℝ) else 0) =
      ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r * gamma (theta ι) t r F.card := by
  obtain ⟨I, J⟩ := u
  set q : Fin k → Digest ι k t → ℝ := fun i v => if v.1 = I ∧ v.2 i = J i then 1 else 0
  have hind : ∀ V : Fin r → Digest ι k t,
      (if ∀ i ∈ F, J i ∈ posSet (univ.image V) I i then (1 : ℝ) else 0) =
        ∑ A ∈ F.powerset, (-1) ^ A.card * ∏ l, ∏ i ∈ A, (1 - q i (V l)) := by
    intro V
    have hb : (if ∀ i ∈ F, J i ∈ posSet (univ.image V) I i then (1 : ℝ) else 0) =
        ∏ i ∈ F, (if ∃ l, (V l).1 = I ∧ (V l).2 i = J i then (1 : ℝ) else 0) := by
      rw [prod_boole]
      split_ifs <;> simp_all [mem_posSet_image]
    rw [hb]
    have h1 : ∀ i ∈ F, (if ∃ l, (V l).1 = I ∧ (V l).2 i = J i then (1 : ℝ) else 0) =
        -(∏ l, (1 - q i (V l))) + 1 := fun i _ =>
      (ite_exists_eq_one_sub_prod (fun l => (V l).1 = I ∧ (V l).2 i = J i)).trans (by ring)
    rw [prod_congr rfl h1, prod_add]
    refine sum_congr rfl fun A _ => ?_
    rw [prod_const_one, mul_one, prod_neg, prod_comm]
  simp_rw [hind]
  rw [sum_comm]
  have hA : ∀ A ∈ F.powerset, ∑ V : Fin r → Digest ι k t,
      (-1) ^ A.card * ∏ l, ∏ i ∈ A, (1 - q i (V l)) =
        (-1) ^ A.card * (((t : ℝ) - 1) ^ A.card * (t : ℝ) ^ (k - A.card) +
          ((Fintype.card ι : ℝ) - 1) * (t : ℝ) ^ k) ^ r := by
    intro A _
    rw [← mul_sum, ← Fintype.sum_pow (fun v => ∏ i ∈ A, (1 - q i v)), sum_avoid]
  rw [sum_congr rfl hA,
    sum_powerset_apply_card (fun s => (-1) ^ s * (((t : ℝ) - 1) ^ s * (t : ℝ) ^ (k - s) +
      ((Fintype.card ι : ℝ) - 1) * (t : ℝ) ^ k) ^ r),
    gamma_eq_sum, mul_sum]
  refine sum_congr rfl fun s hs => ?_
  have hsk : s ≤ k := (Nat.lt_succ_iff.mp (mem_range.mp hs)).trans (card_le_univ F |>.trans
    (by simp))
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hι : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨I⟩
    positivity
  have hkey : (Fintype.card ι : ℝ) * (t : ℝ) ^ k *
      (theta ι * (1 - 1 / (t : ℝ)) ^ s + (1 - theta ι)) =
        ((t : ℝ) - 1) ^ s * (t : ℝ) ^ (k - s) + ((Fintype.card ι : ℝ) - 1) * (t : ℝ) ^ k := by
    have htk : (t : ℝ) ^ k = (t : ℝ) ^ (k - s) * (t : ℝ) ^ s := by
      rw [← pow_add, Nat.sub_add_cancel hsk]
    rw [theta, htk, one_sub_div ht, div_pow]
    field_simp
  rw [nsmul_eq_mul, ← hkey, mul_pow]
  ring

end ShrincsSecurity.ITSR

end
