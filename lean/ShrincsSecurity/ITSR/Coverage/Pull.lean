module

public import ShrincsSecurity.ITSR.Coverage.Witness
public import ShrincsSecurity.ITSR.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Counting pulled witnesses (Lemma 7)

`ITSR-Classical.pdf`, Lemma 7, the tape part. For a witness map `β` and an output entry `a ∉ B`,
the direct-query tapes `U : Fin n → Digest ι k t` in which every pulled witness `U b` lies in the
instance of `U a` and agrees with it at the positions `W_b` it certifies number
`N'^n θ^m t^{-ω}`, where `N' = |ι| t^k`, `m = |B|` and `ω = |W|`. The witnesses are independent of
`U a` since `a ∉ B`.
-/

@[expose] public section

open Finset

namespace ShrincsSecurity.ITSR

/-- Summing a product over a tape whose factors may depend on one entry `U a` of the tape:
condition on the value `u` of `U a`. -/
theorem sum_prod_eval {D : Type} [Fintype D] [DecidableEq D] {n : ℕ} (a : Fin n)
    (h : D → Fin n → D → ℝ) :
    ∑ U : Fin n → D, ∏ b, h (U a) b (U b) =
      ∑ u, ∏ b, (if b = a then h u a u else ∑ v, h u b v) := by
  have hU : ∀ U : Fin n → D, ∏ b, h (U a) b (U b) =
      ∑ u, ∏ b, (if b = a then (if U b = u then h u a (U b) else 0) else h u b (U b)) := by
    intro U
    rw [sum_eq_single (U a)]
    · refine prod_congr rfl fun b _ => ?_
      split_ifs with h1 <;> simp_all
    · intro u _ hu
      exact prod_eq_zero (mem_univ a) (by simp [Ne.symm hu])
    · simp
  simp_rw [hU]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← Fintype.prod_sum (fun b v => if b = a then (if v = u then h u a v else 0) else h u b v)]
  refine prod_congr rfl fun b _ => ?_
  split_ifs with hb
  · simp
  · rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k t n : ℕ}

/-- The digests `v` agreeing with `u` as a witness `b` of the witness map `β`. -/
theorem sum_witness_agree (β : Fin k → Option (Fin n)) (u : Digest ι k t) (b : Fin n) :
    ∑ v : Digest ι k t,
        (if ∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i then (1 : ℝ) else 0) =
      (if b ∈ witnessSet β then 1 else (Fintype.card ι : ℝ)) *
        ∏ i, (if β i = some b then 1 else (t : ℝ)) := by
  have hsplit : ∀ v : Digest ι k t,
      (if ∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i then (1 : ℝ) else 0) =
        (if b ∈ witnessSet β → v.1 = u.1 then (1 : ℝ) else 0) *
          ∏ i, (if β i = some b → v.2 i = u.2 i then (1 : ℝ) else 0) := by
    intro v
    rw [Fintype.prod_boole, ite_zero_mul_ite_zero, one_mul]
    have hiff : (∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i) ↔
        ((b ∈ witnessSet β → v.1 = u.1) ∧ ∀ i, β i = some b → v.2 i = u.2 i) := by
      simp only [witnessSet, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        exact ⟨fun ⟨i, hi⟩ => (h i hi).1, fun i hi => (h i hi).2⟩
      · intro h i hi
        exact ⟨h.1 ⟨i, hi⟩, h.2 i hi⟩
    by_cases hP : ∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i
    · rw [ite_eq_left hP, ite_eq_left (hiff.mp hP)]
    · rw [ite_eq_right hP, ite_eq_right (mt hiff.mpr hP)]
  simp_rw [hsplit]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum (fun x : ι => if b ∈ witnessSet β → x = u.1 then (1 : ℝ) else 0)
    (fun y : Fin k → Fin t => ∏ i, if β i = some b → y i = u.2 i then (1 : ℝ) else 0)]
  congr 1
  · split_ifs with hb
    · simp [hb]
    · simp [hb]
  · rw [← Fintype.prod_sum
      (fun i (x : Fin t) => if β i = some b → x = u.2 i then (1 : ℝ) else 0)]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · simp [hi]
    · simp [hi]

/-- **Lemma 7** (tape part, counting form): for `a ∉ B`, the tapes in which the pulled witnesses
agree with `U a` number `N'^n θ^m t^{-ω}`. -/
theorem sum_pulled [Nonempty ι] [NeZero t] (a : Fin n) (β : Fin k → Option (Fin n))
    (ha : a ∉ witnessSet β) :
    ∑ U : Fin n → Digest ι k t,
        (if ∀ i b, β i = some b → (U b).1 = (U a).1 ∧ (U b).2 i = (U a).2 i
          then (1 : ℝ) else 0) =
      ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ n * theta ι ^ (witnessSet β).card *
        ((t : ℝ)⁻¹) ^ (pulledPositions β).card := by
  have hι : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this.ne'
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have h1 : ∀ U : Fin n → Digest ι k t,
      (if ∀ i b, β i = some b → (U b).1 = (U a).1 ∧ (U b).2 i = (U a).2 i
        then (1 : ℝ) else 0) =
        ∏ b, (if ∀ i, β i = some b → (U b).1 = (U a).1 ∧ (U b).2 i = (U a).2 i
          then (1 : ℝ) else 0) := by
    intro U
    rw [Fintype.prod_boole]
    by_cases hP : ∀ i b, β i = some b → (U b).1 = (U a).1 ∧ (U b).2 i = (U a).2 i
    · rw [ite_eq_left hP, ite_eq_left (fun b i => hP i b)]
    · rw [ite_eq_right hP, ite_eq_right (fun h => hP fun i b => h b i)]
  simp_rw [h1]
  rw [sum_prod_eval a (fun (u : Digest ι k t) (b : Fin n) (v : Digest ι k t) =>
    if ∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i then (1 : ℝ) else 0)]
  set N' : ℝ := (Fintype.card ι : ℝ) * (t : ℝ) ^ k with hN'
  set w : Fin n → ℝ := fun b => (if b ∈ witnessSet β then theta ι else 1) *
    ∏ i, (if β i = some b then (t : ℝ)⁻¹ else 1) with hw_def
  have hw : ∀ (u : Digest ι k t) (b : Fin n),
      ∑ v : Digest ι k t,
        (if ∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i then (1 : ℝ) else 0) = N' * w b := by
    intro u b
    rw [sum_witness_agree]
    have hprod : ∏ i, (if β i = some b then (1 : ℝ) else t) =
        (t : ℝ) ^ k * ∏ i, (if β i = some b then (t : ℝ)⁻¹ else 1) := by
      rw [show (t : ℝ) ^ k = ∏ _i : Fin k, (t : ℝ) by simp, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      split_ifs
      · field_simp
      · ring
    rw [hprod, hN', hw_def]
    dsimp only
    split_ifs
    · simp only [theta]
      field_simp
    · ring
  have hwa : w a = 1 := by
    have hne : ∀ i, β i ≠ some a := fun i hi =>
      ha (mem_filter.mpr ⟨mem_univ _, i, hi⟩)
    simp [w, ha, hne]
  have hfac : ∀ u : Digest ι k t,
      ∏ b, (if b = a then
          (if ∀ i, β i = some a → u.1 = u.1 ∧ u.2 i = u.2 i then (1 : ℝ) else 0)
        else ∑ v : Digest ι k t,
          (if ∀ i, β i = some b → v.1 = u.1 ∧ v.2 i = u.2 i then (1 : ℝ) else 0)) =
        N' ^ (n - 1) * ∏ b, w b := by
    intro u
    calc _ = ∏ b, ((if b = a then 1 else N') * w b) := by
          refine prod_congr rfl fun b _ => ?_
          by_cases hb : b = a
          · rw [ite_eq_left hb, ite_eq_left hb, hb, hwa,
              ite_eq_left (fun _ _ => ⟨rfl, rfl⟩), one_mul]
          · rw [ite_eq_right hb, ite_eq_right hb, hw]
      _ = (∏ b : Fin n, (if b = a then 1 else N')) * ∏ b, w b := prod_mul_distrib
      _ = N' ^ (n - 1) * ∏ b, w b := by
          rw [prod_ite, filter_eq', filter_ne', prod_const_one, one_mul, prod_const,
            card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [sum_congr rfl fun u _ => hfac u]
  have hW : ∏ b, w b = theta ι ^ (witnessSet β).card * ((t : ℝ)⁻¹) ^ (pulledPositions β).card := by
    rw [hw_def, prod_mul_distrib, prod_ite_mem, univ_inter, prod_const, prod_comm]
    congr 1
    have hb : ∀ i, ∏ b, (if β i = some b then (t : ℝ)⁻¹ else 1) =
        if (β i).isSome then (t : ℝ)⁻¹ else 1 := by
      intro i
      cases β i <;> simp
    simp_rw [hb]
    rw [← prod_filter, prod_const]
    rfl
  rw [hW, sum_const, card_univ, nsmul_eq_mul]
  have hD : (Fintype.card (Digest ι k t) : ℝ) = N' := by
    simp [N', Digest, Fintype.card_prod]
  rw [hD]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos a.pos).symm⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring

end ShrincsSecurity.ITSR

end
