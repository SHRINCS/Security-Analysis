module

public import ShrincsSecurity.ITSR.Coverage.Cover
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The one-pull form (Corollary 1)

`ITSR-Classical.pdf`, Corollary 1 and Eq. (3). For a uniform instance `I` and an independent
uniform challenge tape `V : Fin r → Digest ι k t`,
`Δ*(I, V) = ∏_i (|S_i(I)(V)| + 1) - ∏_i |S_i(I)(V)|` (Eq. (3)) counts the digests of instance `I`
that are one coordinate away from being covered, in the sense of the proof of Corollary 1. We
prove the identity used there,

`θ Γ⁺(r) = E[Δ*] / N'`, with `N' = |ι| t^k`,

the evaluation `T₁ = (q + 1) q r |K|⁻¹ θ Γ⁺(r)` of the summand `m = 1` of Theorem 2, and hence the
exact rewriting of the bound of Theorem 2 as

`(q + 1) Γ_k(r) + r q (q + 1) E[Δ*] / (|K| N') + R₂`,

for all parameters (when `min(k, q, r) = 0` the middle term vanishes, as in the paper's proof).

The expectation `E[Δ*]` is the finite average over `ι × (Fin r → Digest ι k t)` (`expectedDelta`).
Its evaluation rests on Lemma 1 in counting form (`sum_cover`): `E ∏_{i ∈ F} |S_i(I)(V)| =
t^{|F|} Γ_{|F|}(r)`.
-/

@[expose] public section

open Finset

namespace ShrincsSecurity.ITSR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k t : ℕ}

/-- **`Δ*(I, V)`** (Eq. (3)): `∏_i (|S_i(I)(V)| + 1) - ∏_i |S_i(I)(V)|`. -/
noncomputable def deltaStar {r : ℕ} (I : ι) (V : Fin r → Digest ι k t) : ℝ :=
  ∏ i, (((posSet (univ.image V) I i).card : ℝ) + 1) - ∏ i, ((posSet (univ.image V) I i).card : ℝ)

variable (ι k t) in
/-- **`E[Δ*]`** (Corollary 1): the expectation of `Δ*(I, V)` over a uniform instance `I` and an
independent uniform tape `V` of `r` digests, as a finite average. -/
noncomputable def expectedDelta (r : ℕ) : ℝ :=
  (∑ I : ι, ∑ V : Fin r → Digest ι k t, deltaStar I V) /
    ((Fintype.card ι : ℝ) * (Fintype.card (Fin r → Digest ι k t) : ℝ))

/-- Counting coordinate vectors inside a box: `#{J | ∀ i ∈ F, J i ∈ S i} = ∏_{i ∈ F} |S i| ·
t^{k - |F|}`. -/
theorem sum_mem_box (F : Finset (Fin k)) (S : Fin k → Finset (Fin t)) :
    ∑ J : Fin k → Fin t, (if ∀ i ∈ F, J i ∈ S i then (1 : ℝ) else 0) =
      (∏ i ∈ F, ((S i).card : ℝ)) * (t : ℝ) ^ (k - F.card) := by
  have hJ : ∀ J : Fin k → Fin t, (if ∀ i ∈ F, J i ∈ S i then (1 : ℝ) else 0) =
      ∏ i, (if i ∈ F then (if J i ∈ S i then (1 : ℝ) else 0) else 1) := by
    intro J
    rw [prod_ite_mem, univ_inter, prod_boole]
    by_cases h : ∀ i ∈ F, J i ∈ S i
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  simp_rw [hJ]
  rw [← Fintype.prod_sum (fun i (x : Fin t) =>
    if i ∈ F then (if x ∈ S i then (1 : ℝ) else 0) else 1)]
  have hi : ∀ i : Fin k, ∑ x : Fin t, (if i ∈ F then (if x ∈ S i then (1 : ℝ) else 0) else 1) =
      if i ∈ F then ((S i).card : ℝ) else t := by
    intro i
    split_ifs
    · simp
    · simp
  simp_rw [hi]
  rw [prod_ite, filter_mem_eq_inter, univ_inter, prod_const, filter_not, filter_mem_eq_inter,
    univ_inter, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]

variable [NeZero t]

/-- **Lemma 1** (moment form): `∑_{I, V} ∏_{i ∈ F} |S_i(I)(V)| = |ι| N'^r t^{|F|} Γ_{|F|}(r)`,
i.e. `E ∏_{i ∈ F} y_i = Γ_{|F|}(r)` with `y_i = |S_i(I)(V)| / t`. -/
theorem sum_prod_posSet [Nonempty ι] (r : ℕ) (F : Finset (Fin k)) :
    ∑ I : ι, ∑ V : Fin r → Digest ι k t, ∏ i ∈ F, ((posSet (univ.image V) I i).card : ℝ) =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r * (t : ℝ) ^ F.card *
        gamma (theta ι) t r F.card := by
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hFk : F.card ≤ k := (card_le_univ F).trans (by simp)
  have hcount : (∑ I : ι, ∑ V : Fin r → Digest ι k t,
      ∏ i ∈ F, ((posSet (univ.image V) I i).card : ℝ)) * (t : ℝ) ^ (k - F.card) =
        (Fintype.card ι : ℝ) * (t : ℝ) ^ k *
          (((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r * gamma (theta ι) t r F.card) := by
    rw [sum_mul]
    simp_rw [sum_mul]
    simp_rw [← sum_mem_box F (fun i => posSet (univ.image _) _ i)]
    have hsw : ∀ I : ι, ∑ V : Fin r → Digest ι k t, ∑ J : Fin k → Fin t,
        (if ∀ i ∈ F, J i ∈ posSet (univ.image V) I i then (1 : ℝ) else 0) =
          ∑ J : Fin k → Fin t, ∑ V : Fin r → Digest ι k t,
            (if ∀ i ∈ F, (I, J).2 i ∈ posSet (univ.image V) (I, J).1 i then (1 : ℝ) else 0) :=
      fun I => sum_comm
    rw [sum_congr rfl fun I _ => hsw I, ← Fintype.sum_prod_type']
    simp_rw [sum_cover]
    rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have htk : (t : ℝ) ^ k = (t : ℝ) ^ F.card * (t : ℝ) ^ (k - F.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hFk]
  have htk' : (t : ℝ) ^ (k - F.card) ≠ 0 := pow_ne_zero _ ht
  apply mul_right_cancel₀ htk'
  rw [hcount, htk]
  ring

/-- The binomial sum of the moments: `∑_{j=0}^{k} C(k, j) t^j Γ_j(r) = t^k (Γ_k(r) + Γ⁺(r))`. -/
theorem sum_choose_gamma (θ : ℝ) (r : ℕ) :
    ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (t : ℝ) ^ j * gamma θ t r j =
      (t : ℝ) ^ k * (gamma θ t r k + gammaPlus θ t k r) := by
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  rw [← sum_range_reflect]
  have hrefl : ∀ ω ∈ range (k + 1),
      (k.choose (k + 1 - 1 - ω) : ℝ) * (t : ℝ) ^ (k + 1 - 1 - ω) * gamma θ t r (k + 1 - 1 - ω) =
        (t : ℝ) ^ k * ((k.choose ω : ℝ) * ((t : ℝ)⁻¹) ^ ω * gamma θ t r (k - ω)) := by
    intro ω hω
    have hωk : ω ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hω)
    rw [Nat.add_sub_cancel, Nat.choose_symm hωk]
    have htk : (t : ℝ) ^ k = (t : ℝ) ^ (k - ω) * (t : ℝ) ^ ω := by
      rw [← pow_add, Nat.sub_add_cancel hωk]
    rw [htk, inv_pow]
    field_simp
  rw [sum_congr rfl hrefl, ← mul_sum]
  congr 1
  have hrange : range (k + 1) = insert 0 (Icc 1 k) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp), gammaPlus]
  simp

/-- **Corollary 1** (the identity of its proof): `θ Γ⁺(r) = E[Δ*] / N'`, with `N' = |ι| t^k`. -/
theorem theta_mul_gammaPlus [Nonempty ι] (r : ℕ) :
    theta ι * gammaPlus (theta ι) t k r =
      expectedDelta ι k t r / ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) := by
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hι : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ I : ι, ∑ V : Fin r → Digest ι k t, deltaStar I V =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r *
        ((t : ℝ) ^ k * gammaPlus (theta ι) t k r) := by
    have hprod : ∀ (I : ι) (V : Fin r → Digest ι k t),
        ∏ i, (((posSet (univ.image V) I i).card : ℝ) + 1) =
          ∑ F ∈ (univ : Finset (Fin k)).powerset,
            ∏ i ∈ F, ((posSet (univ.image V) I i).card : ℝ) := by
      intro I V
      rw [prod_add]
      simp
    simp only [deltaStar, hprod, sum_sub_distrib]
    rw [sum_congr rfl fun I _ => sum_comm, sum_comm]
    simp_rw [sum_prod_posSet]
    rw [sum_powerset_apply_card (fun j => (Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r * (t : ℝ) ^ j * gamma (theta ι) t r j),
      card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    have hs := sum_choose_gamma (k := k) (t := t) (theta ι) r
    have hs' : ∑ j ∈ range (k + 1), (k.choose j : ℝ) * ((Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r * (t : ℝ) ^ j * gamma (theta ι) t r j) =
          (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r *
            ((t : ℝ) ^ k * (gamma (theta ι) t r k + gammaPlus (theta ι) t k r)) := by
      rw [← hs, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    rw [hs']
    ring
  rw [expectedDelta, hsum, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hD : (Fintype.card (Digest ι k t) : ℝ) = (Fintype.card ι : ℝ) * (t : ℝ) ^ k := by
    simp [Digest, Fintype.card_prod]
  rw [hD, theta]
  field_simp

omit [Fintype ι] [DecidableEq ι] [NeZero t] in
/-- `A₁ = Γ⁺(r)` (Eq. (19), using `1! St(ω, 1) = 1` for `ω ≥ 1`). -/
theorem pullHarm_one (θ : ℝ) (r : ℕ) : pullHarm θ t k r 1 = gammaPlus θ t k r := by
  refine sum_congr rfl fun ω hω => ?_
  obtain ⟨w, rfl⟩ : ∃ w, ω = w + 1 := ⟨ω - 1, by have := (mem_Icc.mp hω).1; omega⟩
  rw [Nat.stirlingSecond_one_right]
  simp

omit [Fintype ι] [DecidableEq ι] [NeZero t] in
/-- **Corollary 1** (the summand `m = 1` of Theorem 2):
`T₁ = (q + 1) q r |K|⁻¹ θ Γ⁺(r)`. -/
theorem pullTerm_one (θ : ℝ) (r q nK : ℕ) :
    pullTerm θ t k r q nK 1 =
      (q + 1 : ℝ) * q * r / nK * θ * gammaPlus θ t k r := by
  rw [pullTerm, pullHarm_one, Nat.choose_one_right, Nat.descFactorial_one]
  ring

omit [Fintype ι] [DecidableEq ι] [NeZero t] in
/-- `T₁ = 0` when `min(k, q, r) = 0`. -/
theorem pullTerm_one_eq_zero (θ : ℝ) (r q nK : ℕ) (h : min k (min q r) = 0) :
    pullTerm θ t k r q nK 1 = 0 := by
  rw [pullTerm_one]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [gammaPlus]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · simp [hq]
  have hr : r = 0 := by omega
  simp [hr]

omit [Fintype ι] [DecidableEq ι] [NeZero t] in
/-- Splitting off the summand `m = 1`: the bound of Theorem 2 is `(q + 1) Γ_k(r) + T₁ + R₂`. -/
theorem mainBound_eq_pullTerm_one (θ : ℝ) (r q nK : ℕ) :
    mainBound θ t k r q nK =
      searchTerm θ t k r q + pullTerm θ t k r q nK 1 + remainderTwo θ t k r q nK := by
  rw [mainBound, remainderTwo, add_assoc]
  congr 1
  rcases Nat.eq_zero_or_pos (min k (min q r)) with h | h
  · rw [pullTerm_one_eq_zero θ r q nK h, h]
    simp
  · have hIcc : Icc 1 (min k (min q r)) = insert 1 (Icc 2 (min k (min q r))) := by
      ext m
      simp only [mem_Icc, mem_insert]
      omega
    rw [hIcc, sum_insert (by simp)]

/-- **Corollary 1** (one-pull form of Theorem 2): the bound of Theorem 2 equals
`(q + 1) Γ_k(r) + r q (q + 1) E[Δ*] / (|K| N') + R₂`, with `N' = |ι| t^k`. For
`min(k, q, r) = 0` both the middle term and `R₂` vanish. -/
theorem mainBound_eq_onePull [Nonempty ι] (r q nK : ℕ) :
    mainBound (theta ι) t k r q nK =
      searchTerm (theta ι) t k r q +
        (r : ℝ) * q * (q + 1) * expectedDelta ι k t r /
          ((nK : ℝ) * ((Fintype.card ι : ℝ) * (t : ℝ) ^ k)) +
        remainderTwo (theta ι) t k r q nK := by
  rw [mainBound_eq_pullTerm_one, pullTerm_one]
  congr 2
  have h := theta_mul_gammaPlus (ι := ι) (k := k) (t := t) r
  rw [mul_assoc ((q + 1 : ℝ) * q * r / nK), h, div_mul_div_comm, mul_comm (nK : ℝ)]
  ring

end ShrincsSecurity.ITSR

end
