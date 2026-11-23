module

public import VCVio.Quantum.Comp.HybridIndex
public import VCVio.Quantum.Oracle.Model
public import QuantumFoundations.MatrixMap.Pinching
public import ShrincsSecurity.Undetectability.Quantum.EventHybrid

/-!
# Quantum `ZeroDist` for adaptive programs (Lemma C.8, general program model)

`SHRINCS-Security-Analysis.pdf`, Appendix C, **Definition C.4** and **Lemma C.8**, for VCVio's
general quantum programs (`Quantum.QuantumComp`): adaptive, with intermediate measurements,
mixed states and classical outcomes selecting the continuation, and any interpretation of the
local operations.

* `Adaptive.advantage_le_of_lossless`: **Lemma C.8 as stated**, `Adv ≤ 2q / √|P|`, for a lossless
  first stage (`x.Lossless I`: every local operation on every path is lossless, i.e. the program
  halts with probability one) and a second stage that measures with a complete two-outcome
  measurement.
* `Adaptive.advantage_le`: `Adv ≤ 4q / √|P|` without the losslessness hypothesis (the first stage
  may abort, i.e. post-select) and for any contraction as the accepting operator.

## Model

* The oracle signature is `qromSpec P (ZMod 2)`: one port on the query register `P × ZMod 2`.
  The runtime of a fixed function `f` is VCVio's `additiveOracleRuntime f`: every call applies
  `oracleUnitary f`, the XOR oracle of the Boolean function `f`.
* The first stage is a program `x : QuantumComp L (qromSpec P (ZMod 2)) X A` with
  `x.IsQueryBound fun _ ↦ q` (at most `q` calls on every path), started from a substate
  `ρ : SubState A` of its register.
* The second stage receives `P'` and the leaf `p` reached by the first stage (its classical
  outcomes and its final register `p.1`, quantum state included), and has no oracle. It accepts
  through an operator `O P' p` on the leaf register, beside the trivial runtime register: the
  probability of output `1` is `∑' p, tr (O P' p ρ_p (O P' p)ᴴ)` (`acceptWeight`). The sharp
  theorem asks for a rejecting operator `O' P' p` with `Oᴴ O + O'ᴴ O' = 1`. A second stage with
  acceptance effect `E_p` is the measurement `O = √E_p`, `O' = √(1 - E_p)`, so this loses no
  generality for the probability of output `1`; the reduction of a second-stage *program* to its
  effect is not formalised here.
* `winProb … b` is `Pr[ZeroDist(A) ⇒ 1 | b]`, averaging over the uniform `P'`, and `advantage`
  the absolute difference.

## Proof

1. The coherent index of the query input: `pointProj k = |k⟩⟨k| ⊗ 1` on `P × ZMod 2`
   (`isCoherentIndex`). The difference of the Kraus operators of the oracles of `f₀ = 0` and
   `f_{P'}` respects it, vanishes on the blocks `k ≠ P'` and has norm at most `2` on the block
   `P'` (`respectsIndex_sub`, `oracleKraus_sub_mul_index_eq_zero`, `norm_oracleKraus_sub_mul_le`).
   With VCVio's bound of Kraus weights by index masses
   (`QuantumRuntime.queryWeight_krausWeight_le_tsum_mul_indexMassAt`), the hybrid sum of the calls
   is at most `δ(P') = 2 ∑_{j<q} √(m_j(P'))`, where `m_j(P')` is the index mass on `P'` of the
   `j`-th call of the run against `f₀`, independent of `P'` (`tsum_rpow_queryWeight_le`).
2. *Sharp form.* For lossless programs and complete measurements, the event probabilities differ
   by at most `δ(P')` (`abs_acceptWeight_sub_le`, from
   `ShrincsSecurity.Undetectability.ZeroDist.abs_toReal_sub_le_of_lossless`).
   *General form.* VCVio's square-root hybrid bound
   (`QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le`, ePrint 2025/2166 Lemma 5.7) gives
   `|√p₀ - √p₁| ≤ δ(P')` (`rpow_acceptWeight_le`), hence `|p₀ - p₁| ≤ 2 δ(P')`
   (`mul_self_le_add`, `acceptWeight_le_add`).
3. Averaging (`sum_rpow_pointMass_le`, `sum_hybridBound_le`):
   `∑_{P'} √(m_j(P')) ≤ √|P| · √(∑_{P'} m_j(P')) ≤ √|P|`, since the index masses on the points add
   up to the query mass of the call, at most one (`sum_pointMass_le_one`).
-/

@[expose] public section

open Matrix Quantum Quantum.Hybrid
open scoped ENNReal ComplexOrder Kronecker Matrix.Norms.L2Operator

universe u v w w'

namespace ShrincsSecurity.Undetectability.ZeroDist

namespace Adaptive

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## The coherent index of the query input -/

/-- The projector of the query register onto the input `k`: `|k⟩⟨k| ⊗ 1`. -/
noncomputable def pointProj (k : P) : Matrix (P × ZMod 2) (P × ZMod 2) ℂ :=
  labelProjector (fun a : P × ZMod 2 ↦ a.1) k

/-- The projectors onto the query inputs are a coherent index of the Boolean oracle. -/
theorem isCoherentIndex :
    IsCoherentIndex (spec := qromSpec P (ZMod 2)) (κ := fun _ ↦ P) (fun _ k ↦ pointProj k)
      (fun _ k ↦ pointProj k) where
  sum_eq_one _ := sum_labelProjector _
  mul_self _ k := (isStarProjection_labelProjector (α := ℂ) _ k).isIdempotentElem.eq
  conjTranspose_mul_of_ne _ a b hab := by
    change (pointProj b)ᴴ * pointProj a = 0
    rw [pointProj, conjTranspose_labelProjector]
    exact labelProjector_mul_labelProjector_of_ne _ (Ne.symm hab)

/-- The Kraus operator of a call to the oracle runtime of `f`: the oracle unitary, beside the
trivial runtime register. -/
noncomputable def oracleKraus (f : P → ZMod 2) :
    ∀ i : (qromSpec P (ZMod 2)).Port, (qromSpec P (ZMod 2)).Result i →
      Matrix ((qromSpec P (ZMod 2)).Out i × QReg.of Unit)
        ((qromSpec P (ZMod 2)).In i × QReg.of Unit) ℂ :=
  fun _ _ ↦ oracleUnitary f ⊗ₖ (1 : Matrix Unit Unit ℂ)

/-- The steps of the oracle runtime are the Kraus maps of `oracleKraus`. -/
theorem branch_step (f : P → ZMod 2) (i : Unit) (r : Unit) :
    ((additiveOracleRuntime f).step i).branch r = MatrixMap.conj (oracleKraus f i r) := by
  rw [additiveOracleRuntime_step]
  change ((oracleQuery f).branch r).amplify Unit = _
  rw [branch_oracleQuery_apply, MatrixMap.amplify_conj]
  rfl

omit [Fintype P] in
/-- The block projector `pointProj k ⊗ 1` on the query and runtime registers is the label
projector of the query input. -/
theorem pointProj_kronecker_one (k : P) :
    pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ) =
      labelProjector (fun a : (P × ZMod 2) × Unit ↦ a.1.1) k := by
  rw [pointProj, labelProjector_kronecker_one]

omit [Fintype P] in
/-- The oracle unitary preserves the query input. -/
theorem oracleUnitary_kronecker_one_ne_zero {f : P → ZMod 2} {a b : (P × ZMod 2) × Unit}
    (h : (oracleUnitary f ⊗ₖ (1 : Matrix Unit Unit ℂ)) a b ≠ 0) : a.1.1 = b.1.1 := by
  rw [kronecker_apply, oracleUnitary_apply] at h
  by_contra hne
  exact h (by rw [ite_eq_right_iff.mpr fun he ↦ absurd (by rw [he]) hne]; simp)

/-- The oracle unitary commutes with the projectors onto the query inputs. -/
theorem oracleUnitary_kronecker_one_mul_comm (f : P → ZMod 2) (k : P) :
    (oracleUnitary f ⊗ₖ (1 : Matrix Unit Unit ℂ)) * (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
      (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) * (oracleUnitary f ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
  rw [pointProj_kronecker_one]
  exact mul_labelProjector_eq_labelProjector_mul _ _
    (fun _ _ h ↦ oracleUnitary_kronecker_one_ne_zero h) k

/-- The oracle of `f₀` and the oracle of `f_{P'}` differ by an operator that respects the index
of the query input. -/
theorem respectsIndex_sub (P' : P) :
    RespectsIndex (spec := qromSpec P (ZMod 2)) (κ := fun _ ↦ P) (fun _ k ↦ pointProj k)
      (fun _ k ↦ pointProj k)
      (fun i r ↦ oracleKraus 0 i r - oracleKraus (marked P') i r) := fun i r k ↦ by
  change (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
      (oracleKraus 0 i r - oracleKraus (marked P') i r) * (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
    (oracleKraus 0 i r - oracleKraus (marked P') i r) * (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ))
  have hcomm : (oracleKraus 0 i r - oracleKraus (marked P') i r) *
      (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
        (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
          (oracleKraus 0 i r - oracleKraus (marked P') i r) := by
    simp only [oracleKraus, Matrix.sub_mul, Matrix.mul_sub, oracleUnitary_kronecker_one_mul_comm]
  have hidem : (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) * (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
      pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ) := by
    rw [pointProj_kronecker_one]
    exact (isStarProjection_labelProjector (α := ℂ) _ k).isIdempotentElem.eq
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hidem]

/-- Away from the marked point the two oracles agree: on the block `k ≠ P'` the difference of
their Kraus operators vanishes. -/
theorem oracleKraus_sub_mul_index_eq_zero {P' k : P} (hk : k ≠ P') (i r : Unit) :
    (oracleKraus 0 i r - oracleKraus (marked P') i r) * (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)) =
      0 := by
  rw [pointProj_kronecker_one]
  ext a b
  rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.zero_apply, sub_eq_zero, labelProjector,
    mul_diagonal, mul_diagonal]
  by_cases hb : b.1.1 = k
  · congr 1
    simp only [oracleKraus, Matrix.kroneckerMap_apply, oracleUnitary_apply, hb, marked,
      Pi.single_eq_of_ne hk, Pi.zero_apply]
  · simp [hb]

/-- On the block of the marked point the difference of the Kraus operators has norm at most
two. -/
theorem norm_oracleKraus_sub_mul_le (P' k : P) (i r : Unit) :
    ‖(oracleKraus 0 i r - oracleKraus (marked P') i r) *
      (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ))‖ ≤ 2 := by
  have hU : ∀ f : P → ZMod 2, ‖oracleKraus f i r‖ ≤ 1 := fun f ↦
    l2_opNorm_le_one_of_mem_unitaryGroup
      (kronecker_mem_unitary (oracleUnitary_mem_unitaryGroup f) (one_mem _))
  have hB : ‖pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)‖ ≤ 1 := by
    rw [pointProj_kronecker_one]
    exact l2_opNorm_labelProjector_le_one _ k
  calc ‖(oracleKraus 0 i r - oracleKraus (marked P') i r) *
        (pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ))‖
      ≤ ‖oracleKraus 0 i r - oracleKraus (marked P') i r‖ *
          ‖pointProj k ⊗ₖ (1 : Matrix Unit Unit ℂ)‖ := norm_mul_le _ _
    _ ≤ (1 + 1) * 1 :=
        mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hU 0) (hU _))) hB (norm_nonneg _)
          (by norm_num)
    _ = 2 := by norm_num

/-! ## The square-root hybrid bound for one marked point -/

variable {L : LocalSig.{u, v}} (I : L.Interp) {X : QReg → Type w} {A : QReg}
  {Z : (Σ u, X u) → Type w'} [∀ p, Fintype (Z p)]

/-- The joint initial operator: the program register in `ρ`, the trivial runtime register in its
basis state. -/
noncomputable def jointInit (ρ : SubState A) : Matrix (A × QReg.of Unit) (A × QReg.of Unit) ℂ :=
  ρ.matrix ⊗ₖ (SubState.basis () : SubState Unit).matrix

theorem posSemidef_jointInit (ρ : SubState A) : (jointInit ρ).PosSemidef :=
  (ρ.prod (SubState.basis () : SubState Unit)).posSemidef

theorem trace_re_jointInit_le_one (ρ : SubState A) : (jointInit ρ).trace.re ≤ 1 :=
  (ρ.prod (SubState.basis () : SubState Unit)).trace_re_le_one

/-- The probability that the second stage, accepting through the contraction `O p` at the leaf
`p`, outputs `1` after the first stage `x` has run from `ρ` against the oracle of `f`. -/
noncomputable def acceptWeight (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ) (f : P → ZMod 2) : ℝ≥0∞ :=
  ∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
    (((additiveOracleRuntime f).run I x).branch p (jointInit ρ))).trace.re

/-- Acceptance is a probability. -/
theorem acceptWeight_le_one (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    {O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ}
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) (f : P → ZMod 2) :
    acceptWeight I x ρ O f ≤ 1 := by
  have hρ := posSemidef_jointInit ρ
  calc acceptWeight I x ρ O f
      ≤ ∑' p, ENNReal.ofReal (((additiveOracleRuntime f).run I x).branch p (jointInit ρ)).trace.re :=
        tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal <| MatrixMap.isTNI_conj (hO p) _
          (((additiveOracleRuntime f).run I x).posSemidef_branch_apply p hρ)
    _ ≤ ENNReal.ofReal (jointInit ρ).trace.re :=
        ((additiveOracleRuntime f).run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr (trace_re_jointInit_le_one ρ)

/-- The index mass on the input `P'` of the `j`-th call of the first stage, run against the oracle
of `f₀ = 0`. It does not depend on the marked point except through the block. -/
noncomputable def pointMass (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (P' : P) (j : ℕ) : ℝ≥0∞ :=
  (additiveOracleRuntime (0 : P → ZMod 2)).indexMassAt I (κ := fun _ ↦ P)
    (fun _ k ↦ pointProj k) x (jointInit ρ) ⟨(), P'⟩ j

/-- The Kraus weight of the `j`-th call is at most four times the mass on the marked point. -/
theorem queryWeight_le_four_mul_pointMass (x : QuantumComp L (qromSpec P (ZMod 2)) X A)
    (ρ : SubState A) (P' : P) (j : ℕ) :
    (additiveOracleRuntime (0 : P → ZMod 2)).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ oracleKraus 0 i r - oracleKraus (marked P') i r)
        x (jointInit ρ) j ≤ 4 * pointMass I x ρ P' j := by
  refine ((additiveOracleRuntime (0 : P → ZMod 2)).queryWeight_krausWeight_le_tsum_mul_indexMassAt
    I isCoherentIndex (respectsIndex_sub P') x (posSemidef_jointInit ρ) j).trans ?_
  rw [pointMass, tsum_eq_single (⟨(), P'⟩ : Σ _ : Unit, P) fun c hc ↦ ?_]
  · gcongr
    rw [tsum_fintype, Fintype.sum_unique]
    refine (ENNReal.ofReal_le_ofReal ?_).trans_eq (by norm_num : ENNReal.ofReal (2 ^ 2) = 4)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_oracleKraus_sub_mul_le P' P' () ()) 2
  · obtain ⟨⟨⟩, k⟩ := c
    have hk : k ≠ P' := fun h ↦ hc (by rw [h])
    refine mul_eq_zero_of_left (tsum_eq_zero_iff.mpr fun r ↦ ?_) _
    refine ENNReal.ofReal_eq_zero.mpr (le_of_eq ?_)
    exact (pow_eq_zero_iff two_ne_zero).mpr
      (norm_eq_zero.mpr (oracleKraus_sub_mul_index_eq_zero hk () r))

/-- The first stage makes no call beyond its budget: the masses of the calls `j ≥ q` vanish. -/
theorem pointMass_eq_zero {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A) (P' : P) {j : ℕ} (hj : q ≤ j) :
    pointMass I x ρ P' j = 0 := by
  unfold pointMass QuantumRuntime.indexMassAt
  exact (additiveOracleRuntime (0 : P → ZMod 2)).queryWeight_eq_zero_of_isQueryBound I hx
    Finset.univ (fun i hi ↦ absurd (Finset.mem_univ i) hi) (by simpa using hj) _

/-- `(4 m)^(1/2) = 2 m^(1/2)`. -/
theorem rpow_four_mul (m : ℝ≥0∞) : (4 * m) ^ (2⁻¹ : ℝ) = 2 * m ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by rw [ENNReal.rpow_two]; norm_num,
    ENNReal.rpow_rpow_inv two_ne_zero]

/-- The hybrid sum over the calls is at most `2 ∑_{j<q} √(m_j(P'))`. -/
theorem tsum_rpow_queryWeight_le {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A) (P' : P) :
    ∑' j, (additiveOracleRuntime (0 : P → ZMod 2)).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ oracleKraus 0 i r - oracleKraus (marked P') i r)
        x (jointInit ρ) j ^ (2⁻¹ : ℝ) ≤
      2 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) := by
  calc _ ≤ ∑' j, 2 * pointMass I x ρ P' j ^ (2⁻¹ : ℝ) :=
        tsum_le_tsum fun j ↦ (ENNReal.rpow_le_rpow
          (queryWeight_le_four_mul_pointMass I x ρ P' j) (by norm_num)).trans_eq (rpow_four_mul _)
    _ = ∑ j ∈ Finset.range q, 2 * pointMass I x ρ P' j ^ (2⁻¹ : ℝ) := by
        refine tsum_eq_sum fun j hj ↦ ?_
        rw [pointMass_eq_zero I hx ρ P' (by simpa using hj), ENNReal.zero_rpow_of_pos (by norm_num),
          mul_zero]
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- **The square-root hybrid bound for one marked point**, in both directions. -/
theorem rpow_acceptWeight_le {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A)
    {O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ}
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) (P' : P) :
    acceptWeight I x ρ O 0 ^ (2⁻¹ : ℝ) ≤ acceptWeight I x ρ O (marked P') ^ (2⁻¹ : ℝ) +
        2 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) ∧
      acceptWeight I x ρ O (marked P') ^ (2⁻¹ : ℝ) ≤ acceptWeight I x ρ O 0 ^ (2⁻¹ : ℝ) +
        2 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) := by
  have hρ := posSemidef_jointInit ρ
  have h₀ := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le I
    (SubState.basis () : SubState (QReg.of Unit)) (SubState.basis () : SubState (QReg.of Unit))
    (branch_step 0) (branch_step (marked P')) x O hO hρ
  have h₁ := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le' I
    (SubState.basis () : SubState (QReg.of Unit)) (SubState.basis () : SubState (QReg.of Unit))
    (branch_step 0) (branch_step (marked P')) x O hO hρ
  have hw := tsum_rpow_queryWeight_le I hx ρ P'
  exact ⟨h₀.trans (add_le_add le_rfl hw), h₁.trans (add_le_add le_rfl hw)⟩

/-- From square roots back to probabilities: if `α ≤ β + δ` with `α, β ≤ 1`, then
`α² ≤ β² + 2δ`. -/
theorem mul_self_le_add {α β δ : ℝ≥0∞} (h : α ≤ β + δ) (hα : α ≤ 1) (hβ : β ≤ 1) :
    α * α ≤ β * β + 2 * δ :=
  calc α * α ≤ α * (β + δ) := by gcongr
    _ = α * β + α * δ := mul_add _ _ _
    _ ≤ (β + δ) * β + 1 * δ := by gcongr
    _ = β * β + δ * β + δ := by ring
    _ ≤ β * β + δ * 1 + δ := by gcongr
    _ = β * β + 2 * δ := by ring

theorem self_eq_rpow_mul_rpow (a : ℝ≥0∞) : a = a ^ (2⁻¹ : ℝ) * a ^ (2⁻¹ : ℝ) := by
  conv_lhs => rw [← rpow_inv_two_rpow_two a]
  rw [ENNReal.rpow_two, sq]

/-- **One marked point.** The acceptance probabilities under `f₀` and `f_{P'}` differ by at most
`4 ∑_{j<q} √(m_j(P'))`. -/
theorem acceptWeight_le_add {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A)
    {O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ}
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) (P' : P) :
    acceptWeight I x ρ O 0 ≤ acceptWeight I x ρ O (marked P') +
        4 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) ∧
      acceptWeight I x ρ O (marked P') ≤ acceptWeight I x ρ O 0 +
        4 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) := by
  obtain ⟨h₀, h₁⟩ := rpow_acceptWeight_le I hx ρ hO P'
  have hle : ∀ f, acceptWeight I x ρ O f ^ (2⁻¹ : ℝ) ≤ 1 := fun f ↦
    ENNReal.rpow_le_one (acceptWeight_le_one I x ρ hO f) (by norm_num)
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  constructor
  · conv_lhs => rw [self_eq_rpow_mul_rpow (acceptWeight I x ρ O 0)]
    conv_rhs => rw [self_eq_rpow_mul_rpow (acceptWeight I x ρ O (marked P')), h4, mul_assoc]
    exact mul_self_le_add h₀ (hle _) (hle _)
  · conv_lhs => rw [self_eq_rpow_mul_rpow (acceptWeight I x ρ O (marked P'))]
    conv_rhs => rw [self_eq_rpow_mul_rpow (acceptWeight I x ρ O 0), h4, mul_assoc]
    exact mul_self_le_add h₁ (hle _) (hle _)

/-- The masses of a call on the points of `P` add up to at most one: they refine the query mass
of the call (`QuantumRuntime.tsum_indexMassAt_eq_queryMassAt`), which is at most the trace of the
initial state (`QuantumRuntime.tsum_queryMassAt_le`). -/
theorem sum_pointMass_le_one (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (j : ℕ) : ∑ P' : P, pointMass I x ρ P' j ≤ 1 := by
  have h := (additiveOracleRuntime (0 : P → ZMod 2)).tsum_indexMassAt_eq_queryMassAt I
    (κ := fun _ ↦ P) (fun _ k ↦ pointProj k) () (sum_conjTranspose_mul_labelProjector _) x
    (posSemidef_jointInit ρ) j
  rw [tsum_fintype] at h
  calc ∑ P' : P, pointMass I x ρ P' j
      = (additiveOracleRuntime (0 : P → ZMod 2)).queryMassAt I x (jointInit ρ) () j := h
    _ ≤ ∑' i, (additiveOracleRuntime (0 : P → ZMod 2)).queryMassAt I x (jointInit ρ) i j :=
        le_tsum (fun i ↦ (additiveOracleRuntime (0 : P → ZMod 2)).queryMassAt I x
          (jointInit ρ) i j) ()
    _ ≤ ENNReal.ofReal (jointInit ρ).trace.re :=
        (additiveOracleRuntime (0 : P → ZMod 2)).tsum_queryMassAt_le I x
          (posSemidef_jointInit ρ) j
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr (trace_re_jointInit_le_one ρ)

/-- **Averaging over the marked point** (Cauchy–Schwarz): at every call, the square roots of the
masses on the points of `P` add up to at most `√|P|`. -/
theorem sum_rpow_pointMass_le (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (j : ℕ) : ∑ P' : P, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) ≤
      (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
  have hmass := sum_pointMass_le_one I x ρ j
  rw [ENNReal.le_rpow_inv_iff (by norm_num)]
  calc (∑ P' : P, pointMass I x ρ P' j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
      ≤ ((Finset.univ : Finset P).card : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ∑ P' : P, (pointMass I x ρ P' j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by norm_num)
    _ = (Fintype.card P : ℝ≥0∞) * ∑ P' : P, pointMass I x ρ P' j := by
        simp only [Finset.card_univ, rpow_inv_two_rpow_two]
        norm_num
    _ ≤ (Fintype.card P : ℝ≥0∞) * 1 := by gcongr
    _ = _ := mul_one _

/-! ## The experiment -/

/-- `Pr[ZeroDist(A) ⇒ 1 | b]` for the first stage `x` from `ρ` and the second stage `O`:
`P'` uniform on `P`, the first stage runs against `f_{P'}` if `b = 1` and `f₀` if `b = 0`, and the
second stage, given `P'`, accepts through `O P'`. -/
noncomputable def winProb (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (O : P → ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ) (b : Bool) : ℝ :=
  (Fintype.card P : ℝ)⁻¹ *
    ∑ P', (acceptWeight I x ρ (O P') (if b then marked P' else 0)).toReal

/-- `Adv^{ZeroDist}` of the two-stage adversary `(x, ρ, O)`. -/
noncomputable def advantage (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (O : P → ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ) : ℝ :=
  |winProb I x ρ O true - winProb I x ρ O false|

/-- The sums over the marked point of the acceptance probabilities under `f₀` and `f_{P'}`
differ by at most `4 q √|P|`, in both directions. -/
theorem sum_acceptWeight_le {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A)
    {O : P → ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ}
    (hO : ∀ P' p, (1 - (O P' p)ᴴ * O P' p).PosSemidef) (f g : P → P → ZMod 2)
    (hfg : ∀ P', (f P' = 0 ∧ g P' = marked P') ∨ (f P' = marked P' ∧ g P' = 0)) :
    ∑ P', acceptWeight I x ρ (O P') (f P') ≤ ∑ P', acceptWeight I x ρ (O P') (g P') +
      4 * q * (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
  have hpt : ∀ P', acceptWeight I x ρ (O P') (f P') ≤ acceptWeight I x ρ (O P') (g P') +
      4 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ) := fun P' ↦ by
    obtain ⟨hf, hg⟩ | ⟨hf, hg⟩ := hfg P'
    · rw [hf, hg]; exact (acceptWeight_le_add I hx ρ (hO P') P').1
    · rw [hf, hg]; exact (acceptWeight_le_add I hx ρ (hO P') P').2
  calc ∑ P', acceptWeight I x ρ (O P') (f P')
      ≤ ∑ P', (acceptWeight I x ρ (O P') (g P') +
          4 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ)) :=
        Finset.sum_le_sum fun P' _ ↦ hpt P'
    _ = ∑ P', acceptWeight I x ρ (O P') (g P') +
          4 * ∑ j ∈ Finset.range q, ∑ P', pointMass I x ρ P' j ^ (2⁻¹ : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ∑ P', acceptWeight I x ρ (O P') (g P') +
          4 * ∑ _j ∈ Finset.range q, (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
        gcongr with j _
        exact sum_rpow_pointMass_le I x ρ j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- **Lemma C.8 for adaptive programs, with constant 4.** A first stage that makes at most `q`
calls to its Boolean oracle on every path, followed by any second stage that gets `P'` and no
oracle, has `ZeroDist` advantage at most `4q / √|P|`. -/
theorem advantage_le [Nonempty P] {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A)
    {O : P → ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ}
    (hO : ∀ P' p, (1 - (O P' p)ᴴ * O P' p).PosSemidef) :
    advantage I x ρ O ≤ 4 * q / √(Fintype.card P) := by
  set N : ℝ := (Fintype.card P : ℝ) with hN
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hfin : ∀ P' f, acceptWeight I x ρ (O P') f ≠ ⊤ := fun P' f ↦
    ne_top_of_le_ne_top ENNReal.one_ne_top (acceptWeight_le_one I x ρ (hO P') f)
  have hc : (4 * q * (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ)).toReal = 4 * q * √N := by
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast, Real.sqrt_eq_rpow,
      ENNReal.toReal_mul, ENNReal.toReal_natCast, one_div]
    norm_num [hN]
  have hcfin : 4 * q * (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top q))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top _))
  have hreal : ∀ f g : P → P → ZMod 2,
      (∀ P', (f P' = 0 ∧ g P' = marked P') ∨ (f P' = marked P' ∧ g P' = 0)) →
      ∑ P', (acceptWeight I x ρ (O P') (f P')).toReal ≤
        ∑ P', (acceptWeight I x ρ (O P') (g P')).toReal + 4 * q * √N := fun f g hfg ↦ by
    have hsfin : ∑ P', acceptWeight I x ρ (O P') (g P') ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun P' _ ↦ hfin P' _
    rw [← ENNReal.toReal_sum fun P' _ ↦ hfin P' _, ← ENNReal.toReal_sum fun P' _ ↦ hfin P' _,
      ← hc, ← ENNReal.toReal_add hsfin hcfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsfin, hcfin⟩)
      (sum_acceptWeight_le I hx ρ hO f g hfg)
  have h₁ := hreal (fun _ ↦ 0) marked fun _ ↦ Or.inl ⟨rfl, rfl⟩
  have h₂ := hreal marked (fun _ ↦ 0) fun _ ↦ Or.inr ⟨rfl, rfl⟩
  have hdiff : winProb I x ρ O true - winProb I x ρ O false =
      N⁻¹ * (∑ P', (acceptWeight I x ρ (O P') (marked P')).toReal -
        ∑ P', (acceptWeight I x ρ (O P') 0).toReal) := by
    simp [winProb, hN, mul_sub]
  rw [advantage, hdiff, abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
  calc N⁻¹ * |∑ P', (acceptWeight I x ρ (O P') (marked P')).toReal -
        ∑ P', (acceptWeight I x ρ (O P') 0).toReal|
      ≤ N⁻¹ * (4 * q * √N) := by
        gcongr
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ = 4 * q / √N := by
        have hs : 0 < √N := Real.sqrt_pos.mpr hNpos
        field_simp
        rw [Real.sq_sqrt hNpos.le, mul_comm]

/-! ## The sharp bound for lossless programs -/

/-- The hybrid bound `δ(P') = 2 ∑_{j<q} √(m_j(P'))` for the marked point `P'`. -/
noncomputable def hybridBound (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (q : ℕ) (P' : P) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range q, pointMass I x ρ P' j ^ (2⁻¹ : ℝ)

theorem hybridBound_ne_top (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (q : ℕ) (P' : P) : hybridBound I x ρ q P' ≠ ⊤ :=
  ENNReal.mul_ne_top (by norm_num) <| ENNReal.sum_ne_top.mpr fun j _ ↦ rpow_inv_two_ne_top <|
    ne_top_of_le_ne_top ENNReal.one_ne_top <|
      (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ P')).trans
        (sum_pointMass_le_one I x ρ j)

/-- **Averaging the hybrid bound over the marked point**: `∑_{P'} δ(P') ≤ 2 q √|P|`. -/
theorem sum_hybridBound_le (x : QuantumComp L (qromSpec P (ZMod 2)) X A) (ρ : SubState A)
    (q : ℕ) : ∑ P', hybridBound I x ρ q P' ≤ 2 * q * (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
  unfold hybridBound
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc 2 * ∑ j ∈ Finset.range q, ∑ P', pointMass I x ρ P' j ^ (2⁻¹ : ℝ)
      ≤ 2 * ∑ _j ∈ Finset.range q, (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
        gcongr with j _
        exact sum_rpow_pointMass_le I x ρ j
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- **One marked point, sharp.** For a lossless first stage and a complete two-outcome second
measurement `O, O'`, the acceptance probabilities under `f₀` and `f_{P'}` differ by at most
`δ(P') = 2 ∑_{j<q} √(m_j(P'))` (`abs_toReal_sub_le_of_lossless`). -/
theorem abs_acceptWeight_sub_le {x : QuantumComp L (qromSpec P (ZMod 2)) X A} {q : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (hxl : x.Lossless I) (ρ : SubState A)
    {Z' : (Σ u, X u) → Type w'} [∀ p, Fintype (Z' p)]
    (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ)
    (O' : ∀ p : Σ u, X u, Matrix (Z' p) (p.1 × QReg.of Unit) ℂ)
    (hOO : ∀ p, (O p)ᴴ * O p + (O' p)ᴴ * O' p = 1) (P' : P) :
    |(acceptWeight I x ρ O 0).toReal - (acceptWeight I x ρ O (marked P')).toReal| ≤
      (hybridBound I x ρ q P').toReal :=
  abs_toReal_sub_le_of_lossless I (SubState.basis ()) (SubState.basis ()) (branch_step 0)
    (branch_step (marked P')) x O O' hOO (posSemidef_jointInit ρ) (trace_re_jointInit_le_one ρ)
    (lossless_run_additiveOracleRuntime I hxl 0)
    (lossless_run_additiveOracleRuntime I hxl (marked P')) ENNReal.toReal_nonneg
    (by
      rw [ENNReal.ofReal_toReal (hybridBound_ne_top I x ρ q P')]
      exact tsum_rpow_queryWeight_le I hx ρ P')

/-- **Lemma C.8** (quantum `ZeroDist`, adaptive programs). A lossless first stage that makes at
most `q` calls to its Boolean oracle on every path, followed by a second stage that gets `P'`, has
no oracle, and outputs `1` on the outcome `O P'` of a complete two-outcome measurement
`O P', O' P'`, has `ZeroDist` advantage at most `2q / √|P|`. -/
theorem advantage_le_of_lossless [Nonempty P] {x : QuantumComp L (qromSpec P (ZMod 2)) X A}
    {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) (hxl : x.Lossless I) (ρ : SubState A)
    {O : P → ∀ p : Σ u, X u, Matrix (Z p) (p.1 × QReg.of Unit) ℂ}
    {Z' : (Σ u, X u) → Type w'} [∀ p, Fintype (Z' p)]
    (O' : P → ∀ p : Σ u, X u, Matrix (Z' p) (p.1 × QReg.of Unit) ℂ)
    (hOO : ∀ P' p, (O P' p)ᴴ * O P' p + (O' P' p)ᴴ * O' P' p = 1) :
    advantage I x ρ O ≤ 2 * q / √(Fintype.card P) := by
  set N : ℝ := (Fintype.card P : ℝ) with hN
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (2 * q * (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ)).toReal = 2 * q * √N := by
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast, Real.sqrt_eq_rpow,
      ENNReal.toReal_mul, ENNReal.toReal_natCast, one_div]
    norm_num [hN]
  have hcfin : 2 * q * (Fintype.card P : ℝ≥0∞) ^ (2⁻¹ : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top q))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top _))
  have hsum : ∑ P', (hybridBound I x ρ q P').toReal ≤ 2 * q * √N := by
    rw [← ENNReal.toReal_sum fun P' _ ↦ hybridBound_ne_top I x ρ q P', ← hc]
    exact ENNReal.toReal_mono hcfin (sum_hybridBound_le I x ρ q)
  have hdiff : winProb I x ρ O true - winProb I x ρ O false =
      N⁻¹ * ∑ P', ((acceptWeight I x ρ (O P') (marked P')).toReal -
        (acceptWeight I x ρ (O P') 0).toReal) := by
    simp [winProb, hN, mul_sub, Finset.sum_sub_distrib]
  rw [advantage, hdiff, abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
  calc N⁻¹ * |∑ P', ((acceptWeight I x ρ (O P') (marked P')).toReal -
        (acceptWeight I x ρ (O P') 0).toReal)|
      ≤ N⁻¹ * ∑ P', (hybridBound I x ρ q P').toReal := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun P' _ ↦ ?_)
        rw [abs_sub_comm]
        exact abs_acceptWeight_sub_le I hx hxl ρ (O P') (O' P') (hOO P') P'
    _ ≤ N⁻¹ * (2 * q * √N) := by gcongr
    _ = 2 * q / √N := by
        have hs : 0 < √N := Real.sqrt_pos.mpr hNpos
        field_simp
        rw [Real.sq_sqrt hNpos.le, mul_comm]

end Adaptive

end ShrincsSecurity.Undetectability.ZeroDist
