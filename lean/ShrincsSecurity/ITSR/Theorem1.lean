module

public import ShrincsSecurity.ITSR.Assembly

/-!
# Theorem 1: the crude bound

`ITSR-Classical.pdf`, Theorem 1 and its proof, Lemma 10 (Section 5.6), using Lemma 2, Lemma 4,
and Lemma 5.

`Bad` is the event that some challenge pulls a direct point (Lemma 3), read off the final state
as "the pulled set is nonempty". Lemma 10 bounds it by `r · min(q, |K|) / |K|`
(`prob_bad_le`), and off `Bad` a win needs a search structure `E_0(a)` (`prob_win_not_bad_le`),
of probability `Γ_k(r)` each (Lemma 5).
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

variable {K M : Type} [DecidableEq K] [DecidableEq M] [SampleableType K] [Fintype K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [SampleableType ι] {k t : ℕ} [NeZero t]

omit [DecidableEq ι] [SampleableType ι] in
/-- `θ ≥ 0`. -/
theorem theta_nonneg : 0 ≤ theta ι := by
  unfold theta
  positivity

omit [DecidableEq ι] in
/-- `θ ≤ 1`. -/
theorem theta_le_one : theta ι ≤ 1 := by
  unfold theta
  have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact (div_le_one (by linarith)).mpr this

omit [Fintype ι] [DecidableEq ι] [SampleableType ι] in
/-- `Γ_j(r) ≥ 0` for `0 ≤ θ ≤ 1` and `t ≥ 1`. -/
theorem gamma_nonneg_of_le_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (r j : ℕ) :
    0 ≤ gamma θ t r j := by
  unfold gamma
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne t)
  have hq0 : 0 ≤ 1 - 1 / (t : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact ht
  have hq1 : 1 - 1 / (t : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (t : ℝ) := by positivity
    linarith
  refine Finset.sum_nonneg fun g _ => ?_
  have hθ : 0 ≤ 1 - θ := by linarith
  have hpow : 0 ≤ 1 - (1 - 1 / (t : ℝ)) ^ g := sub_nonneg.mpr (pow_le_one₀ hq0 hq1)
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- **Lemma 10**, first part: `Pr[Bad] ≤ r · min(q, |K|) / |K|`. -/
theorem prob_bad_le {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    Pr{let w ← presampled A}[w.2.2.pulled.Nonempty] ≤
      r * ((min q (Fintype.card K) : ℕ) * (Fintype.card K : ℝ≥0∞)⁻¹) := by
  refine prEvent_bind_le_of_forall_le _ _ _ fun uv => ?_
  simp only [Functor.map_map]
  refine (prob_withVerify_pulled_le A.run _ fun P => P.Nonempty).trans ?_
  exact prob_pulled_nonempty_le A.run q r q A.hashBound A.chalBound _ (OriginInv.init _ _) rfl
    (by simp [TapeState.init])

omit [Fintype K] [Fintype ι] in
/-- A win of the pre-sampled game with nothing pulled is a search event `E_0(a)` (Lemma 4 with
`W = ∅`). -/
theorem exists_covered_of_wins_not_bad {q r : ℕ} (A : Adversary K M (Digest ι k t) q r)
    {w : Tapes ι k t q r × Outcome K M ι k t} (hw : w ∈ support (presampled A))
    (hwin : Wins w.2.2.toGame w.2.1.1 w.2.1.2) (hbad : ¬ w.2.2.pulled.Nonempty) :
    ∃ a : Fin (q + 1), Covered (Finset.univ.image w.1.2) (w.1.1 a) := by
  obtain ⟨a, β, -, ⟨-, hF⟩, hB⟩ := exists_witness_of_wins w.1.1 w.1.2 A.run A.hashBound
    A.chalBound (mem_support_presampled hw) hwin
  refine ⟨a, fun i => hF i ?_⟩
  rw [Finset.not_nonempty_iff_eq_empty] at hbad
  simp only [castWitness, Option.map_eq_none_iff]
  rcases hβ : β i with _ | b
  · rfl
  · have hb : b ∈ witnessSet β := by
      simp only [witnessSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hβ⟩
    have := hB b hb
    simp [hbad] at this

omit [Fintype K] in
/-- **Lemma 10**, second part: `Pr[Win ∧ ¬Bad] ≤ (q + 1) Γ_k(r)`, by Lemma 4 and Lemma 5. -/
theorem prob_win_not_bad_le {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    Pr{let w ← presampled A}[Wins w.2.2.toGame w.2.1.1 w.2.1.2 ∧ ¬ w.2.2.pulled.Nonempty] ≤
      (q + 1 : ℕ) * ENNReal.ofReal (gamma (theta ι) t r k) := by
  calc _ ≤ Pr{let w ← presampled A}[∃ a ∈ (Finset.univ : Finset (Fin (q + 1))),
          Covered (Finset.univ.image w.1.2) (w.1.1 a) ∧ True] := by
        refine prEvent_mono_of_support _ _ _ fun w hw h => ?_
        obtain ⟨a, ha⟩ := exists_covered_of_wins_not_bad A hw h.1 h.2
        exact ⟨a, Finset.mem_univ a, ha, trivial⟩
    _ ≤ ∑ a : Fin (q + 1), Pr{let w ← presampled A}[
          Covered (Finset.univ.image w.1.2) (w.1.1 a) ∧ True] :=
        prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _a : Fin (q + 1), ENNReal.ofReal (gamma (theta ι) t r k) := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (prob_presampled_and_le A (fun uv => Covered (Finset.univ.image uv.2) (uv.1 a))
          (fun _ => True) (ε := 1) fun _ _ => prEvent_le_one _).trans ?_
        rw [mul_one, prob_drawTapes (fun U V => Covered (Finset.univ.image V) (U a)),
          prob_covered_tape]
    _ = (q + 1 : ℕ) * ENNReal.ofReal (gamma (theta ι) t r k) := by
        simp

/-- **Theorem 1** (crude bound), proved as Lemma 10: in the classical random-oracle model, an
ITSR adversary making at most `q` direct queries and at most `r` challenge queries has
`Succ^ITSR_{H'}(A) ≤ (q + 1) Γ_k(r) + r · min(q, |K|) / |K|`. -/
theorem advantage_le_crudeBound {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    advantage A ≤ ENNReal.ofReal (crudeBound (theta ι) t k r q (Fintype.card K)) := by
  have hΓ := gamma_nonneg_of_le_one (t := t) theta_nonneg (theta_le_one (ι := ι)) r k
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [advantage_eq_presampled_win]
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _ fun w => w.2.2.pulled.Nonempty).trans ?_
  rw [add_comm]
  refine (add_le_add (prob_win_not_bad_le A) (prob_bad_le A)).trans (le_of_eq ?_)
  rw [crudeBound, searchTerm, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hK,
    ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.ofReal_natCast, div_eq_mul_inv, mul_assoc]
  norm_cast

end ShrincsSecurity.ITSR

end
