module

public import VCVio.Quantum.Comp.Hybrid
public import ShrincsSecurity.Undetectability.Quantum.ZeroDist

/-!
# The sharp event form of the hybrid bound for lossless programs

VCVio's square-root hybrid bound (`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le`,
ePrint 2025/2166 Lemma 5.7) bounds `|√p₀ - √p₁|` by the sum `δ = ∑ⱼ √wⱼ` of the square roots of
the Kraus weights of the calls. Turned into a bound on `|p₀ - p₁|` it loses a factor two:
`|p₀ - p₁| ≤ (√p₀ + √p₁) δ ≤ 2δ`.

For a lossless program, run against two lossless runtimes from the same state of trace at most
one, and an event given by a complete two-outcome measurement `O, O'` at the leaves
(`(O p)ᴴ O p + (O' p)ᴴ O' p = 1`), this file proves the sharp bound `|p₀ - p₁| ≤ δ`
(`abs_toReal_sub_le_of_lossless`). It is the mixed-state, adaptive analogue of the pure-state fact
that two states of the same norm at distance `δ` give event probabilities differing by at most
`δ` (`ShrincsSecurity.Undetectability.ZeroDist.abs_acceptProb_sub_le`), and is what makes the
constant of Lemma C.8 (`2q / √|P|`) available for general programs.

## Proof

The two runs are the two branches of VCVio's controlled runtime (`QuantumRuntime.ctrlRuntime`),
whose leaves `G p` carry both runs coherently: the leaves of the runs are `S_b G_p S_bᴴ` for the
branch selectors `S_b = sel p.1 b`, and `QuantumRuntime.rpow_inv_two_tsum_dist_run_le` bounds the
total squared distance `∑ₚ tr ((S₀ - S₁) G_p (S₀ - S₁)ᴴ)` of the branches by `δ²`. For the
accepting and rejecting parts of the event, the triangle inequality for the weights
`K ↦ ∑ₚ tr (K_p G_p K_pᴴ)` (`rpow_leafWeight_add_le`) gives
`|√p₀ - √p₁| ≤ e₁` and `|√(1-p₀) - √(1-p₁)| ≤ e₀` (normalising the total weight to `n²`) with
`e₁² + e₀² ≤ δ²` (`leafWeight_add_leafWeight`), and the real inequality
`ShrincsSecurity.Undetectability.ZeroDist.abs_sq_sub_sq_le_of_branches` concludes.
-/

@[expose] public section

open Matrix Quantum Quantum.Hybrid
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w w₁ w₂

namespace ShrincsSecurity.Undetectability.ZeroDist

/-! ## Weights of families of operators on the leaves -/

section LeafWeight

variable {ι : Type*} {Y Y' Y'' n : ι → Type*} [∀ i, Fintype (Y i)] [∀ i, Fintype (Y' i)]
  [∀ i, Fintype (Y'' i)] [∀ i, Fintype (n i)] {G : ∀ i, Matrix (n i) (n i) ℂ}

/-- The total weight `∑ᵢ tr (K i · G i · (K i)ᴴ)` of a family of operators on a family of leaf
operators. -/
noncomputable def leafWeight (K : ∀ i, Matrix (Y i) (n i) ℂ) (G : ∀ i, Matrix (n i) (n i) ℂ) :
    ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (MatrixMap.conj (K i) (G i)).trace.re

/-- The triangle inequality for square roots of leaf weights, for a sum of operators. -/
theorem rpow_leafWeight_add_le (K₁ K₂ : ∀ i, Matrix (Y i) (n i) ℂ) (hG : ∀ i, (G i).PosSemidef) :
    leafWeight (fun i ↦ K₁ i + K₂ i) G ^ (2⁻¹ : ℝ) ≤
      leafWeight K₁ G ^ (2⁻¹ : ℝ) + leafWeight K₂ G ^ (2⁻¹ : ℝ) :=
  rpow_inv_two_tsum_le_of_le_add fun i ↦ MatrixMap.ofReal_trace_conj_add_rpow_le (hG i) _ _

/-- The triangle inequality for square roots of leaf weights, for a difference of operators. -/
theorem rpow_leafWeight_sub_le (K₁ K₂ : ∀ i, Matrix (Y i) (n i) ℂ) (hG : ∀ i, (G i).PosSemidef) :
    leafWeight (fun i ↦ K₁ i - K₂ i) G ^ (2⁻¹ : ℝ) ≤
      leafWeight K₁ G ^ (2⁻¹ : ℝ) + leafWeight K₂ G ^ (2⁻¹ : ℝ) :=
  rpow_inv_two_tsum_le_of_le_add fun i ↦ MatrixMap.ofReal_trace_conj_sub_rpow_le (hG i) _ _

/-- Leaf weights add over a decomposition `Kᴴ K + K'ᴴ K' = Mᴴ M`. -/
theorem leafWeight_add_leafWeight (K : ∀ i, Matrix (Y i) (n i) ℂ)
    (K' : ∀ i, Matrix (Y' i) (n i) ℂ) (M : ∀ i, Matrix (Y'' i) (n i) ℂ)
    (h : ∀ i, (K i)ᴴ * K i + (K' i)ᴴ * K' i = (M i)ᴴ * M i) (hG : ∀ i, (G i).PosSemidef) :
    leafWeight K G + leafWeight K' G = leafWeight M G := by
  rw [leafWeight, leafWeight, leafWeight, ← tsum_add]
  refine tsum_congr fun i ↦ ?_
  have h₁ : (MatrixMap.conj (K i) (G i)).PosSemidef := (hG i).mul_mul_conjTranspose_same (K i)
  have h₂ : (MatrixMap.conj (K' i) (G i)).PosSemidef := (hG i).mul_mul_conjTranspose_same (K' i)
  rw [← ENNReal.ofReal_add h₁.trace_re_nonneg h₂.trace_re_nonneg]
  congr 1
  rw [MatrixMap.trace_conj_apply, MatrixMap.trace_conj_apply, MatrixMap.trace_conj_apply,
    ← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, h i]

end LeafWeight

/-- A lossless dependent subinstrument keeps the total weight of a positive semidefinite input. -/
theorem tsum_ofReal_trace_branch_eq {A : Type*} [Fintype A] {κ : Type*} {B : κ → Type*}
    [∀ i, Fintype (B i)] {p : DSubInstrument A κ B} (hp : p.Lossless) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) :
    ∑' i, ENNReal.ofReal (p.branch i ρ).trace.re = ENNReal.ofReal ρ.trace.re := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ p.isCPTNIFamily.trace_re_apply_nonneg i hρ)
    (p.isCPTNIFamily.summable_trace_re_apply hρ), ← p.isCPTNIFamily.re_tsum_trace_apply,
    hp.tsum_trace_eq ρ]

/-! ## From extended reals to reals -/

/-- `(√x)² = x` through `toReal`. -/
theorem toReal_rpow_inv_two_sq (x : ℝ≥0∞) : ((x ^ (2⁻¹ : ℝ)).toReal) ^ 2 = x.toReal := by
  rw [← ENNReal.toReal_rpow, show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt ENNReal.toReal_nonneg]

theorem toReal_le_add {x y z : ℝ≥0∞} (h : x ≤ y + z) (hy : y ≠ ⊤) (hz : z ≠ ⊤) :
    x.toReal ≤ y.toReal + z.toReal := by
  rw [← ENNReal.toReal_add hy hz]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hy, hz⟩) h

theorem rpow_inv_two_ne_top {x : ℝ≥0∞} (hx : x ≠ ⊤) : x ^ (2⁻¹ : ℝ) ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num) hx

/-! ## The sharp event bound -/

section Sharp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg} {D : QReg}
  {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  (σ₀ σ₁ : SubState D)
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))

/-- The zero substate, used as the (never read) initial state of the controlled runtime. -/
noncomputable def ctrlInit (D : QReg) : SubState (QReg.of (D × Bool)) :=
  ⟨0, Matrix.PosSemidef.zero, by simp⟩

include hU hW in
/-- The leaves of the runs against the two runtimes are the two branches of the leaves of the
controlled runtime, started from `T ρ Tᴴ` with `T = (sel A false)ᴴ + (sel A true)ᴴ`. -/
theorem run_branch_eq_conj_sel (x : QuantumComp L spec X A) (ρ : Matrix (A × D) (A × D) ℂ)
    (p : Σ u, X u) :
    ((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ =
        MatrixMap.conj (sel p.1 false)
          (((QuantumRuntime.ctrlRuntime (ctrlInit D) hU hW).run I x).branch p
            (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)) ∧
      ((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ =
        MatrixMap.conj (sel p.1 true)
          (((QuantumRuntime.ctrlRuntime (ctrlInit D) hU hW).run I x).branch p
            (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)) := by
  have h₀ := LinearMap.congr_fun
    (QuantumRuntime.simulation I (R₁ := QuantumRuntime.ctrlRuntime (ctrlInit D) hU hW)
      (R₂ := QuantumRuntime.mk D σ₀ s₀) (V := MatrixMap.conj (inj D false)ᴴ)
      (QuantumRuntime.ctrlRuntime_simulation_false (ctrlInit D) σ₀ hU hW) x p)
    (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)
  have h₁ := LinearMap.congr_fun
    (QuantumRuntime.simulation I (R₁ := QuantumRuntime.ctrlRuntime (ctrlInit D) hU hW)
      (R₂ := QuantumRuntime.mk D σ₁ s₁) (V := MatrixMap.conj (inj D true)ᴴ)
      (QuantumRuntime.ctrlRuntime_simulation_true (ctrlInit D) σ₁ hU hW) x p)
    (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)
  simp only [LinearMap.comp_apply, ← conj_sel, conj_sel_conj_add] at h₀ h₁
  exact ⟨h₀, h₁⟩

include hU hW in
/-- **The sharp event bound for lossless programs.** Let two runtimes on the same register `D`
have steps the Kraus maps of `U i r` and `W i r`, let the program `x` run losslessly against both
from a positive semidefinite `ρ` of trace at most one, and let `O, O'` be a complete two-outcome
measurement at every leaf. If the hybrid sum `∑ⱼ √wⱼ` of the Kraus weights of `U - W` on the calls
of the run against the first runtime is at most `δ`, the weights of the event `O` in the two runs
differ by at most `δ`. -/
theorem abs_toReal_sub_le_of_lossless (x : QuantumComp L spec X A)
    {Z Z' : (Σ u, X u) → Type w₂} [∀ p, Fintype (Z p)] [∀ p, Fintype (Z' p)]
    (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ) (O' : ∀ p : Σ u, X u, Matrix (Z' p) (p.1 × D) ℂ)
    (hOO : ∀ p, (O p)ᴴ * O p + (O' p)ᴴ * O' p = 1)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef) (hρ1 : ρ.trace.re ≤ 1)
    (h₀ : ((QuantumRuntime.mk D σ₀ s₀).run I x).Lossless)
    (h₁ : ((QuantumRuntime.mk D σ₁ s₁).run I x).Lossless) {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ U i r - W i r) x ρ j ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal δ) :
    |(∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re).toReal -
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re).toReal| ≤ δ := by
  set Γ := MatrixMap.conj ((sel (D := D) A false)ᴴ + (sel A true)ᴴ) ρ with hΓdef
  have hΓ : Γ.PosSemidef := hρ.mul_mul_conjTranspose_same _
  set G : ∀ p : Σ u, X u, Matrix (p.1 × (D × Bool)) (p.1 × (D × Bool)) ℂ :=
    fun p ↦ ((QuantumRuntime.ctrlRuntime (ctrlInit D) hU hW).run I x).branch p Γ with hGdef
  have hG : ∀ p, (G p).PosSemidef := fun p ↦
    ((QuantumRuntime.ctrlRuntime (ctrlInit D) hU hW).run I x).posSemidef_branch_apply p hΓ
  have hb := fun p ↦ run_branch_eq_conj_sel I σ₀ σ₁ hU hW x ρ p
  -- The event weights of the two runs as leaf weights of the controlled run.
  have hev : ∀ (b : Bool) {Z : (Σ u, X u) → Type w₂} [∀ p, Fintype (Z p)]
      (K : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ),
      leafWeight (fun p : (Σ u, X u) ↦ K p * sel p.1 b) G =
        ∑' p, ENNReal.ofReal (MatrixMap.conj (K p) (MatrixMap.conj (sel p.1 b) (G p))).trace.re :=
    fun b Z _ K ↦ tsum_congr fun p ↦ by rw [MatrixMap.conj_mul, LinearMap.comp_apply]
  have hselOO : ∀ (b : Bool) (p : Σ u, X u),
      (O p * sel p.1 b)ᴴ * (O p * sel p.1 b) + (O' p * sel p.1 b)ᴴ * (O' p * sel p.1 b) =
        (sel (D := D) p.1 b)ᴴ * sel p.1 b := fun b p ↦ by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_add, ← Matrix.mul_assoc (O p)ᴴ, ← Matrix.mul_assoc (O' p)ᴴ, ← Matrix.add_mul,
      hOO p, Matrix.one_mul]
  have hseldOO : ∀ p : Σ u, X u,
      (O p * seld (D := D) p.1)ᴴ * (O p * seld p.1) + (O' p * seld p.1)ᴴ * (O' p * seld p.1) =
        (seld (D := D) p.1)ᴴ * seld p.1 := fun p ↦ by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_add, ← Matrix.mul_assoc (O p)ᴴ, ← Matrix.mul_assoc (O' p)ᴴ, ← Matrix.add_mul,
      hOO p, Matrix.one_mul]
  -- Total weights.
  have htot : ∀ b : Bool, leafWeight (fun p : (Σ u, X u) ↦ sel (D := D) p.1 b) G = ENNReal.ofReal ρ.trace.re := by
    intro b
    cases b
    · calc leafWeight (fun p : (Σ u, X u) ↦ sel (D := D) p.1 false) G
          = ∑' p, ENNReal.ofReal (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ).trace.re :=
            tsum_congr fun p ↦ by rw [(hb p).1]
        _ = _ := tsum_ofReal_trace_branch_eq h₀ hρ
    · calc leafWeight (fun p : (Σ u, X u) ↦ sel (D := D) p.1 true) G
          = ∑' p, ENNReal.ofReal (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ).trace.re :=
            tsum_congr fun p ↦ by rw [(hb p).2]
        _ = _ := tsum_ofReal_trace_branch_eq h₁ hρ
  have hsum : ∀ b : Bool, leafWeight (fun p : (Σ u, X u) ↦ O p * sel p.1 b) G +
      leafWeight (fun p : (Σ u, X u) ↦ O' p * sel p.1 b) G = ENNReal.ofReal ρ.trace.re := fun b ↦
    (leafWeight_add_leafWeight _ _ _ (hselOO b) hG).trans (htot b)
  -- The distance of the branches.
  have hdist : leafWeight (fun p : (Σ u, X u) ↦ seld (D := D) p.1) G ≤ ENNReal.ofReal δ ^ (2 : ℝ) := by
    have h := QuantumRuntime.rpow_inv_two_tsum_dist_run_le I (ctrlInit D) σ₀ hU hW x hΓ
    rw [hΓdef, branchDist, conj_seld_conj_add, conj_sel_conj_add] at h
    simp only [Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), zero_add] at h
    rw [← ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)]
    exact h.trans hw
  have hE : leafWeight (fun p : (Σ u, X u) ↦ O p * seld (D := D) p.1) G +
      leafWeight (fun p : (Σ u, X u) ↦ O' p * seld (D := D) p.1) G ≤ ENNReal.ofReal δ ^ (2 : ℝ) :=
    (leafWeight_add_leafWeight _ _ _ hseldOO hG).trans_le hdist
  -- Triangle inequalities for the accepting and rejecting parts.
  have htri : ∀ {Z : (Σ u, X u) → Type w₂} [∀ p, Fintype (Z p)]
      (K : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ),
      leafWeight (fun p : (Σ u, X u) ↦ K p * sel p.1 false) G ^ (2⁻¹ : ℝ) ≤
          leafWeight (fun p : (Σ u, X u) ↦ K p * sel p.1 true) G ^ (2⁻¹ : ℝ) +
            leafWeight (fun p : (Σ u, X u) ↦ K p * seld (D := D) p.1) G ^ (2⁻¹ : ℝ) ∧
        leafWeight (fun p : (Σ u, X u) ↦ K p * sel p.1 true) G ^ (2⁻¹ : ℝ) ≤
          leafWeight (fun p : (Σ u, X u) ↦ K p * sel p.1 false) G ^ (2⁻¹ : ℝ) +
            leafWeight (fun p : (Σ u, X u) ↦ K p * seld (D := D) p.1) G ^ (2⁻¹ : ℝ) := by
    intro Z _ K
    constructor
    · have he : (fun p ↦ K p * sel (D := D) p.1 false) =
          fun p ↦ K p * sel p.1 true + K p * seld p.1 := funext fun p ↦ by
        rw [seld_eq, Matrix.mul_sub]; abel
      rw [he]
      exact rpow_leafWeight_add_le _ _ hG
    · have he : (fun p ↦ K p * sel (D := D) p.1 true) =
          fun p ↦ K p * sel p.1 false - K p * seld p.1 := funext fun p ↦ by
        rw [seld_eq, Matrix.mul_sub]; abel
      rw [he]
      exact rpow_leafWeight_sub_le _ _ hG
  -- Pass to real numbers.
  set α := leafWeight (fun p : (Σ u, X u) ↦ O p * sel (D := D) p.1 false) G
  set α' := leafWeight (fun p : (Σ u, X u) ↦ O' p * sel (D := D) p.1 false) G
  set β := leafWeight (fun p : (Σ u, X u) ↦ O p * sel (D := D) p.1 true) G
  set β' := leafWeight (fun p : (Σ u, X u) ↦ O' p * sel (D := D) p.1 true) G
  set ε := leafWeight (fun p : (Σ u, X u) ↦ O p * seld (D := D) p.1) G
  set ε' := leafWeight (fun p : (Σ u, X u) ↦ O' p * seld (D := D) p.1) G
  have hδtop : ENNReal.ofReal δ ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hρtop : ENNReal.ofReal ρ.trace.re ≠ ⊤ := ENNReal.ofReal_ne_top
  have hα : α ≠ ⊤ := ne_top_of_le_ne_top hρtop (le_self_add.trans_eq (hsum false))
  have hα' : α' ≠ ⊤ := ne_top_of_le_ne_top hρtop (le_add_self.trans_eq (hsum false))
  have hβ : β ≠ ⊤ := ne_top_of_le_ne_top hρtop (le_self_add.trans_eq (hsum true))
  have hβ' : β' ≠ ⊤ := ne_top_of_le_ne_top hρtop (le_add_self.trans_eq (hsum true))
  have hε : ε ≠ ⊤ := ne_top_of_le_ne_top hδtop (le_self_add.trans hE)
  have hε' : ε' ≠ ⊤ := ne_top_of_le_ne_top hδtop (le_add_self.trans hE)
  have hn : 0 ≤ ρ.trace.re := hρ.trace_re_nonneg
  have hsumR : ∀ {a b : ℝ≥0∞}, a + b = ENNReal.ofReal ρ.trace.re → a ≠ ⊤ → b ≠ ⊤ →
      ((a ^ (2⁻¹ : ℝ)).toReal) ^ 2 + ((b ^ (2⁻¹ : ℝ)).toReal) ^ 2 = √(ρ.trace.re) ^ 2 :=
    fun h ha hb ↦ by
      rw [toReal_rpow_inv_two_sq, toReal_rpow_inv_two_sq, ← ENNReal.toReal_add ha hb, h,
        ENNReal.toReal_ofReal hn, Real.sq_sqrt hn]
  have hER : ((ε ^ (2⁻¹ : ℝ)).toReal) ^ 2 + ((ε' ^ (2⁻¹ : ℝ)).toReal) ^ 2 ≤ δ ^ 2 := by
    rw [toReal_rpow_inv_two_sq, toReal_rpow_inv_two_sq, ← ENNReal.toReal_add hε hε']
    refine (ENNReal.toReal_mono hδtop hE).trans_eq ?_
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hδ, Real.rpow_two]
  have habs : ∀ {a b e : ℝ≥0∞}, a ^ (2⁻¹ : ℝ) ≤ b ^ (2⁻¹ : ℝ) + e ^ (2⁻¹ : ℝ) →
      b ^ (2⁻¹ : ℝ) ≤ a ^ (2⁻¹ : ℝ) + e ^ (2⁻¹ : ℝ) → a ≠ ⊤ → b ≠ ⊤ → e ≠ ⊤ →
      |(a ^ (2⁻¹ : ℝ)).toReal - (b ^ (2⁻¹ : ℝ)).toReal| ≤ (e ^ (2⁻¹ : ℝ)).toReal :=
    fun h₁ h₂ ha hb he ↦ abs_sub_le_iff.mpr
      ⟨by linarith [toReal_le_add h₁ (rpow_inv_two_ne_top hb) (rpow_inv_two_ne_top he)],
        by linarith [toReal_le_add h₂ (rpow_inv_two_ne_top ha) (rpow_inv_two_ne_top he)]⟩
  have hmain := abs_sq_sub_sq_le_of_branches ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _) hδ
    (habs (htri O).1 (htri O).2 hα hβ hε) (habs (htri O').1 (htri O').2 hα' hβ' hε')
    (hsumR (hsum false) hα hα') (hsumR (hsum true) hβ hβ') hER
  rw [toReal_rpow_inv_two_sq, toReal_rpow_inv_two_sq] at hmain
  have hα_eq : α = ∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
      (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re := by
    exact (hev false O).trans (tsum_congr fun p ↦ by rw [(hb p).1])
  have hβ_eq : β = ∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
      (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re := by
    exact (hev true O).trans (tsum_congr fun p ↦ by rw [(hb p).2])
  rw [← hα_eq, ← hβ_eq]
  refine hmain.trans ?_
  calc √(ρ.trace.re) * δ ≤ 1 * δ := by
        gcongr
        exact Real.sqrt_le_one.mpr hρ1
    _ = δ := one_mul δ

end Sharp

end ShrincsSecurity.Undetectability.ZeroDist
