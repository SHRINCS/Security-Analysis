module

public import ShrincsSecurity.ITSR.Theorem1

/-!
# Theorem 2: the main bound

`ITSR-Classical.pdf`, Theorem 2 and its proof, Lemma 9 (Section 5.5), assembling Lemma 2,
Lemma 4, Lemma 6, Lemma 7 and Lemma 8.

A structure is an output entry `a : Fin (q + 1)` and a witness map `β : Fin k → Option (Fin q)`
(the encoding of `(B, (W_b))` of `Coverage.lean`); the witness map with no pulled position is the
search structure `E_0(a)`, so the search term is the summand `m = 0`. Step 1 of the proof is the
union bound over the structures with `a ∉ B` given by Lemma 4 (`advantage_le_sum_structures`);
Step 3 prices one structure by Lemma 6 and Lemma 7 (`prob_structure_le`, Eq. (17)); Steps 4–5
count the structures with Lemma 8 and sum (`sum_structures_eq`). Since the summands are
nonnegative, the sum over the structures with `a ∉ B` is bounded by the sum over all witness
maps, which is the over-count of Eq. (18).
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

/-! ## The summation (Steps 4–5 of Lemma 9) -/

/-- The weight `β(m, ω) = (r)_m |K|^{-m} θ^m t^{-ω} Γ_{k-ω}(r)` of a pull structure with
parameters `(m, ω)`, Eq. (17), for a key space of size `nK`. -/
noncomputable def structWeight (θ : ℝ) (t k r nK m ω : ℕ) : ℝ :=
  (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m * θ ^ m * ((t : ℝ)⁻¹) ^ ω * gamma θ t r (k - ω)

/-- **Lemma 9**, Step 5: the counted sum of the structure weights is the bound of Theorem 2. -/
theorem mainBound_eq_sum (θ : ℝ) (t k r q nK : ℕ) :
    (q + 1 : ℝ) * ∑ m ∈ Finset.range (k + 1), ∑ ω ∈ Finset.range (k + 1),
        (k.choose ω : ℝ) * (q.choose m : ℝ) * (m.factorial : ℝ) *
          (Nat.stirlingSecond ω m : ℝ) * structWeight θ t k r nK m ω =
      mainBound θ t k r q nK := by
  set F : ℕ → ℝ := fun m => ∑ ω ∈ Finset.range (k + 1),
    (k.choose ω : ℝ) * (q.choose m : ℝ) * (m.factorial : ℝ) *
      (Nat.stirlingSecond ω m : ℝ) * structWeight θ t k r nK m ω with hF
  -- the summand `m = 0` is the search term
  have hF0 : F 0 = gamma θ t r k := by
    rw [hF]
    dsimp only
    rw [Finset.sum_eq_single 0]
    · simp [structWeight]
    · intro ω _ hω
      obtain ⟨ω, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hω
      simp [Nat.stirlingSecond_succ_zero]
    · simp
  -- the summands `m ≥ 1` are the pull terms
  have hFm : ∀ m ∈ Finset.Icc 1 k, (q + 1 : ℝ) * F m = pullTerm θ t k r q nK m := by
    intro m _
    rw [hF, pullTerm, pullHarm]
    dsimp only
    rw [← Finset.sum_subset (s₁ := Finset.Icc m k) (s₂ := Finset.range (k + 1))
      (fun ω hω => by simp only [Finset.mem_Icc] at hω; simp only [Finset.mem_range]; omega) ?_,
      Finset.mul_sum,
      Finset.mul_sum]
    · refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [structWeight]
      ring
    · intro ω hω hω'
      have : ω < m := by
        simp only [Finset.mem_range, Finset.mem_Icc, not_and_or, not_le] at hω hω'
        omega
      simp [Nat.stirlingSecond_eq_zero_of_lt this]
  have hvanish : ∀ m ∈ Finset.Icc 1 k, m ∉ Finset.Icc 1 (min k (min q r)) → F m = 0 := by
    intro m hm hm'
    simp only [Finset.mem_Icc] at hm hm'
    have : q < m ∨ r < m := by omega
    rw [hF]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rcases this with h | h
    · simp [Nat.choose_eq_zero_of_lt h]
    · simp [structWeight, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  have hsplit : ∑ m ∈ Finset.range (k + 1), F m = F 0 + ∑ m ∈ Finset.Icc 1 k, F m := by
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < k + 1), Finset.Ico_add_one_right_eq_Icc]
  change (q + 1 : ℝ) * ∑ m ∈ Finset.range (k + 1), F m = _
  rw [hsplit, mul_add, hF0, mainBound, searchTerm,
    ← Finset.sum_subset (Finset.Icc_subset_Icc_right (min_le_left _ _)) hvanish, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun m hm =>
    hFm m (Finset.Icc_subset_Icc_right (min_le_left _ _) hm)

variable {K M : Type} [DecidableEq K] [DecidableEq M] [SampleableType K] [Fintype K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [SampleableType ι] {k t : ℕ} [NeZero t]

omit [DecidableEq ι] in
/-- The structure weights are nonnegative. -/
theorem structWeight_nonneg (r nK m ω : ℕ) :
    0 ≤ structWeight (theta ι) t k r nK m ω := by
  have := gamma_nonneg_of_le_one (t := t) theta_nonneg (theta_le_one (ι := ι)) r (k - ω)
  have := theta_nonneg (ι := ι)
  unfold structWeight
  positivity

/-! ## One structure (Step 3 of Lemma 9) -/

/-- **Lemma 9**, Step 3 (Eq. (17)), from Lemma 6 and Lemma 7: for `a ∉ B`, the event
`E(a, B, (W_b))` has probability at most `(r)_m |K|^{-m} θ^m t^{-ω} Γ_{k-ω}(r)`. -/
theorem prob_structure_le {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) (a : Fin (q + 1))
    (β : Fin k → Option (Fin q)) (ha : a ∉ witnessSet (castWitness β)) :
    Pr{let w ← presampled A}[DigestEvent a (castWitness β) w.1.1 w.1.2 ∧
        (witnessSet β).map Fin.valEmbedding ⊆ w.2.2.pulled] ≤
      ENNReal.ofReal (structWeight (theta ι) t k r (Fintype.card K) (witnessSet β).card
        (pulledPositions β).card) := by
  set B : Finset ℕ := (witnessSet β).map Fin.valEmbedding
  refine (prob_presampled_and_le A (fun uv => DigestEvent a (castWitness β) uv.1 uv.2)
    (fun z => B ⊆ z.2.pulled) (ε := pullFactor (Fintype.card K) r (witnessSet β).card)
    fun uv _ => ?_).trans ?_
  · -- Lemma 6
    refine (prob_withVerify_pulled_le A.run _ fun P => B ⊆ P).trans ?_
    refine (prob_pulled_le A.run r A.chalBound B _ (OriginInv.init _ _)).trans (le_of_eq ?_)
    simp [TapeState.init, B]
  · -- Lemma 7
    rw [prob_drawTapes (fun U V => DigestEvent a (castWitness β) U V), prob_digestEvent a _ ha,
      card_witnessSet_castWitness, pulledPositions_castWitness]
    have hθ := theta_nonneg (ι := ι)
    have hΓ := gamma_nonneg_of_le_one (t := t) theta_nonneg (theta_le_one (ι := ι)) r
      (k - (pulledPositions β).card)
    have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
    rw [structWeight, pullFactor, mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_inv_of_pos hK, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))

/-! ## The union bound (Steps 1–3 of Lemma 9) -/

/-- **Lemma 9**, Steps 1–3: by Lemma 4 every win lies in some structure event, and the union
bound with Eq. (17) bounds the success probability by the sum of the structure weights over all
output entries and witness maps. -/
theorem advantage_le_sum_structures {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    advantage A ≤ ∑ _a : Fin (q + 1), ∑ β : Fin k → Option (Fin q),
      ENNReal.ofReal (structWeight (theta ι) t k r (Fintype.card K) (witnessSet β).card
        (pulledPositions β).card) := by
  rw [advantage_eq_presampled_win]
  calc _ ≤ Pr{let w ← presampled A}[∃ a ∈ (Finset.univ : Finset (Fin (q + 1))),
          ∃ β ∈ Finset.univ.filter fun β : Fin k → Option (Fin q) =>
            a ∉ witnessSet (castWitness β),
          DigestEvent a (castWitness β) w.1.1 w.1.2 ∧
            (witnessSet β).map Fin.valEmbedding ⊆ w.2.2.pulled] := by
        refine prEvent_mono_of_support _ _ _ fun w hw hwin => ?_
        obtain ⟨a, β, ha, hD, hB⟩ := exists_witness_of_wins w.1.1 w.1.2 A.run A.hashBound
          A.chalBound (mem_support_presampled hw) hwin
        refine ⟨a, Finset.mem_univ a, β, by simpa using ha, hD, fun b hb => ?_⟩
        simp only [Finset.mem_map, Fin.valEmbedding_apply] at hb
        obtain ⟨b, hb, rfl⟩ := hb
        exact hB b hb
    _ ≤ ∑ a : Fin (q + 1), ∑ β ∈ Finset.univ.filter fun β : Fin k → Option (Fin q) =>
          a ∉ witnessSet (castWitness β),
          Pr{let w ← presampled A}[DigestEvent a (castWitness β) w.1.1 w.1.2 ∧
            (witnessSet β).map Fin.valEmbedding ⊆ w.2.2.pulled] :=
        (prEvent_exists_finset_le _ _ _).trans
          (Finset.sum_le_sum fun a _ => prEvent_exists_finset_le _ _ _)
    _ ≤ ∑ a : Fin (q + 1), ∑ β ∈ Finset.univ.filter fun β : Fin k → Option (Fin q) =>
          a ∉ witnessSet (castWitness β),
          ENNReal.ofReal (structWeight (theta ι) t k r (Fintype.card K) (witnessSet β).card
            (pulledPositions β).card) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun β hβ =>
          prob_structure_le A a β (Finset.mem_filter.mp hβ).2
    _ ≤ _ := Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

omit [Fintype K] [DecidableEq ι] in
/-- **Lemma 9**, Steps 4–5: by Lemma 8 the sum of the structure weights is the bound of
Theorem 2. -/
theorem sum_structures_eq (q r nK : ℕ) :
    ∑ _a : Fin (q + 1), ∑ β : Fin k → Option (Fin q),
      ENNReal.ofReal (structWeight (theta ι) t k r nK (witnessSet β).card
        (pulledPositions β).card) =
      ENNReal.ofReal (mainBound (theta ι) t k r q nK) := by
  rw [← mainBound_eq_sum, ← sum_witnessMaps q (structWeight (theta ι) t k r nK),
    ← ENNReal.ofReal_sum_of_nonneg fun β _ => structWeight_nonneg r nK _ _, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (by positivity)]
  norm_cast

/-- **Theorem 2** (main bound), proved as Lemma 9: in the classical random-oracle model, an
ITSR adversary making at most `q` direct queries and at most `r` challenge queries has
`Succ^ITSR_{H'}(A) ≤ (q + 1) Γ_k(r) + ∑_{m=1}^{min(k,q,r)} T_m`, where
`T_m = (q + 1) C(q, m) (r)_m |K|^{-m} θ^m ∑_{ω=m}^{k} C(k, ω) m! St(ω, m) t^{-ω} Γ_{k-ω}(r)`. -/
theorem advantage_le_mainBound {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    advantage A ≤ ENNReal.ofReal (mainBound (theta ι) t k r q (Fintype.card K)) :=
  (advantage_le_sum_structures A).trans (le_of_eq (sum_structures_eq q r _))

end ShrincsSecurity.ITSR

end
