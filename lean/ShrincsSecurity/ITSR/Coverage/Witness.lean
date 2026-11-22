module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Witness maps and their count (Lemma 8)

`ITSR-Classical.pdf`, Lemma 8. A pull structure `(B, (W_b))` of Lemma 4 is encoded as a witness
map `β : Fin k → Option (Fin n)`: `β i = none` puts position `i` in `F`, `β i = some b` puts `i`
in `W_b`. The pulled set is `B = witnessSet β` and the certified positions are
`W = pulledPositions β`.

The number of witness maps with `|B| = m` and `|W| = ω` is `C(k, ω) (n)_m St(ω, m)`, i.e.
`C(k, ω) C(n, m) m! St(ω, m)`: choose `W`, then a map of `W` onto an `m`-subset of `Fin n`.
We prove it by induction on `k`, peeling off position `0` with `Fin.cons`, which reproduces the
recursion `St(ω + 1, m + 1) = (m + 1) St(ω, m + 1) + St(ω, m)` of the Stirling numbers.
-/

@[expose] public section

open Finset

namespace ShrincsSecurity.ITSR

variable {k n : ℕ}

/-- The pulled set `B` of a witness map: the indices it uses. -/
def witnessSet (β : Fin k → Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun b => ∃ i, β i = some b

/-- The positions `W` certified by pulled digests. -/
def pulledPositions (β : Fin k → Option (Fin n)) : Finset (Fin k) :=
  Finset.univ.filter fun i => (β i).isSome

theorem witnessSet_cons_none (β : Fin k → Option (Fin n)) :
    witnessSet (Fin.cons none β : Fin (k + 1) → Option (Fin n)) = witnessSet β := by
  ext b
  simp [witnessSet, Fin.exists_fin_succ]

theorem witnessSet_cons_some (x : Fin n) (β : Fin k → Option (Fin n)) :
    witnessSet (Fin.cons (some x) β : Fin (k + 1) → Option (Fin n)) =
      insert x (witnessSet β) := by
  ext b
  simp [witnessSet, Fin.exists_fin_succ, eq_comm]

theorem card_pulledPositions_cons (o : Option (Fin n)) (β : Fin k → Option (Fin n)) :
    (pulledPositions (Fin.cons o β : Fin (k + 1) → Option (Fin n))).card =
      (pulledPositions β).card + if o.isSome then 1 else 0 := by
  simp only [pulledPositions, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- `|B| ≤ |W|`: every pulled index certifies at least one position. -/
theorem card_witnessSet_le (β : Fin k → Option (Fin n)) :
    (witnessSet β).card ≤ (pulledPositions β).card := by
  calc (witnessSet β).card
      ≤ ((pulledPositions β).biUnion fun i => (β i).toFinset).card := by
        refine card_le_card fun b hb => ?_
        obtain ⟨i, hi⟩ := (mem_filter.mp hb).2
        exact mem_biUnion.mpr ⟨i, by simp [pulledPositions, hi], by simp [hi]⟩
    _ ≤ ∑ i ∈ pulledPositions β, (β i).toFinset.card := card_biUnion_le
    _ ≤ ∑ _i ∈ pulledPositions β, 1 := sum_le_sum fun i _ => by cases β i <;> simp
    _ = (pulledPositions β).card := by simp

theorem card_pulledPositions_le (β : Fin k → Option (Fin n)) :
    (pulledPositions β).card ≤ k :=
  (card_le_univ _).trans (by simp)

/-- One step of the induction: peeling off position `0` of a witness map. -/
theorem sum_witnessMaps_succ {M : Type} [AddCommMonoid M] (g : ℕ → ℕ → M) :
    ∑ β : Fin (k + 1) → Option (Fin n), g (witnessSet β).card (pulledPositions β).card =
      ∑ β : Fin k → Option (Fin n), (g (witnessSet β).card (pulledPositions β).card +
        ((witnessSet β).card • g (witnessSet β).card ((pulledPositions β).card + 1) +
          (n - (witnessSet β).card) •
            g ((witnessSet β).card + 1) ((pulledPositions β).card + 1))) := by
  rw [← (Fin.consEquiv fun _ => Option (Fin n)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_option]
  simp only [Fin.consEquiv_apply, witnessSet_cons_none, witnessSet_cons_some,
    card_pulledPositions_cons, Option.isSome_none, Option.isSome_some]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [sum_comm, ← sum_add_distrib]
  refine sum_congr rfl fun β _ => ?_
  congr 1
  have hx : ∀ x : Fin n, g (insert x (witnessSet β)).card ((pulledPositions β).card + 1) =
      if x ∈ witnessSet β then g (witnessSet β).card ((pulledPositions β).card + 1)
      else g ((witnessSet β).card + 1) ((pulledPositions β).card + 1) := by
    intro x
    split_ifs with h
    · rw [card_insert_of_mem h]
    · rw [card_insert_of_notMem h]
  simp_rw [hx]
  rw [sum_ite, sum_const, sum_const, filter_mem_eq_inter, univ_inter, filter_not,
    filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ _), card_univ,
    Fintype.card_fin]

/-- **Lemma 8** (counting, fibre form): the witness maps `β : Fin k → Option (Fin n)` with
`|B| = m` and `|W| = ω` number `C(k, ω) (n)_m St(ω, m)`. -/
theorem card_witnessMaps (n : ℕ) : ∀ (k m ω : ℕ),
    (univ.filter fun β : Fin k → Option (Fin n) =>
        (witnessSet β).card = m ∧ (pulledPositions β).card = ω).card =
      k.choose ω * n.descFactorial m * Nat.stirlingSecond ω m
  | 0, m, ω => by
    rw [card_filter]
    have hW : ∀ β : Fin 0 → Option (Fin n), witnessSet β = ∅ := fun β => by
      ext b; simp [witnessSet]
    have hP : ∀ β : Fin 0 → Option (Fin n), pulledPositions β = ∅ := fun β => by
      ext i; exact i.elim0
    simp only [hW, hP, card_empty, Fintype.sum_unique]
    rcases ω with _ | w <;> rcases m with _ | j <;> simp
  | k + 1, m, ω => by
    rw [card_filter, sum_witnessMaps_succ (fun a b => if a = m ∧ b = ω then 1 else 0),
      sum_add_distrib, sum_add_distrib]
    have h1 := card_witnessMaps n k m ω
    rw [card_filter] at h1
    rw [h1]
    rcases ω with _ | w
    · simp only [Nat.add_one_ne_zero, and_false, ↓reduceIte, smul_zero, sum_const_zero,
        add_zero, Nat.choose_zero_right]
    have h2 : ∑ β : Fin k → Option (Fin n), (witnessSet β).card •
        (if (witnessSet β).card = m ∧ (pulledPositions β).card + 1 = w + 1 then 1 else 0) =
          m * k.choose w * n.descFactorial m * Nat.stirlingSecond w m := by
      have := card_witnessMaps n k m w
      rw [card_filter] at this
      rw [mul_assoc, mul_assoc, ← mul_assoc (k.choose w), ← this, mul_sum]
      refine sum_congr rfl fun β _ => ?_
      simp only [Nat.add_right_cancel_iff, smul_eq_mul]
      split_ifs with h
      · rw [h.1]
      · rfl
    rw [h2]
    rcases m with _ | j
    · simp only [Nat.add_one_ne_zero, false_and, ↓reduceIte, smul_zero, sum_const_zero,
        add_zero, Nat.stirlingSecond_succ_zero, mul_zero, zero_mul]
    have h3 : ∑ β : Fin k → Option (Fin n), (n - (witnessSet β).card) •
        (if (witnessSet β).card + 1 = j + 1 ∧ (pulledPositions β).card + 1 = w + 1 then 1
          else 0) =
          (n - j) * (k.choose w * n.descFactorial j * Nat.stirlingSecond w j) := by
      have := card_witnessMaps n k j w
      rw [card_filter] at this
      rw [← this, mul_sum]
      refine sum_congr rfl fun β _ => ?_
      simp only [Nat.add_right_cancel_iff, smul_eq_mul]
      split_ifs with h
      · rw [h.1]
      · rfl
    rw [h3, Nat.choose_succ_succ, Nat.descFactorial_succ, Nat.stirlingSecond_succ_succ]
    ring

/-- **Lemma 8** (counting): the witness maps into `Fin n` with `|B| = m` and `|W| = ω` number
`C(k, ω) · C(n, m) · m! · St(ω, m)`; summed against any weight depending on `(m, ω)` only. -/
theorem sum_witnessMaps_eq (n : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ β : Fin k → Option (Fin n), f (witnessSet β).card (pulledPositions β).card =
      ∑ m ∈ Finset.range (k + 1), ∑ ω ∈ Finset.range (k + 1),
        (k.choose ω : ℝ) * (n.choose m : ℝ) * (m.factorial : ℝ) * (Nat.stirlingSecond ω m : ℝ) *
          f m ω := by
  have hβ : ∀ β : Fin k → Option (Fin n), f (witnessSet β).card (pulledPositions β).card =
      ∑ m ∈ range (k + 1), ∑ ω ∈ range (k + 1),
        (if (witnessSet β).card = m ∧ (pulledPositions β).card = ω then (1 : ℝ) else 0) *
          f m ω := by
    intro β
    have hW := card_pulledPositions_le β
    have hB := (card_witnessSet_le β).trans hW
    simp only [ite_and, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_range,
      Nat.lt_succ_iff.mpr hW, Nat.lt_succ_iff.mpr hB, ↓reduceIte, sum_ite_irrel, sum_const_zero]
  simp_rw [hβ]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [← sum_mul]
  congr 1
  have := card_witnessMaps n k m ω
  rw [card_filter] at this
  have hc : ∑ β : Fin k → Option (Fin n),
      (if (witnessSet β).card = m ∧ (pulledPositions β).card = ω then (1 : ℝ) else 0) =
        ((k.choose ω * n.descFactorial m * Nat.stirlingSecond ω m : ℕ) : ℝ) := by
    rw [← this]
    push_cast
    rfl
  rw [hc, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

end ShrincsSecurity.ITSR

end
