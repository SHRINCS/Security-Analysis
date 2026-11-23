module

public import VCVio.Quantum.Oracle.Compressed.Phase
public import ShrincsSecurity.Undetectability.Rest.ReproHalf

/-!
# Quantum adaptive reprogramming in the QROM: Lemmas C.1, C.3, C.5 and Corollaries C.1, C.3

`SHRINCS-Security-Analysis.pdf`, Appendix C:

* **Definitions C.1 and C.2** (`Repro_b` and `DI-Repro_b` in the QROM): a multi-stage quantum
  adversary makes superposition queries `|x, y⟩ ↦ |x, y + O_b(x)⟩` to a uniformly sampled random
  oracle `O_b : X₁ × X₂ → Y` (`Y` any finite additive commutative group, in particular
  `{0, 1}^ν` with bitwise XOR) interleaved with `R` classical calls `Reprogram(x₂)`. On each
  call, `(x₁, y') ←$ X₁ × Y` is sampled uniformly; in `Repro₁` (`b = true`) the oracle is updated
  at `(x₁, x₂)` to `y'`, while in `Repro₀` (`b = false`) the oracle is unchanged. In `DI-Repro_b`,
  repeated `x₂` values are refused (`none`) without reprogramming.
* **Lemma C.3** ([LGX25, Theorem 7], lines 5916–5938): with `q̂_j` the cumulative number of
  quantum queries issued before the `j`-th call to `Reprogram`, for `e ∈ {1, 1/2}`,
  `|Pr[Repro₀(A) ⇒ 1]^e − Pr[Repro₁(A) ⇒ 1]^e| ≤ 4 √(∑_j q̂_j / |X₁|)`
  (`lemmaC3_one`, `lemmaC3_half`). Our Fourier-basis fidelity proof yields the sharper constant
  `√2` for both `e = 1` and `e = 1/2` (`lemmaC3_sharp`, `lemmaC3_sqrt_sharp`), which implies
  both Remark C.3's `2√2` and Lemma C.3's `4`.
* **Lemma C.1** ([GHHM21], lines 5875–5881): for total query budget `q` (`∀ j, q̂_j ≤ q`),
  `|Pr[Repro₀(A) ⇒ 1] − Pr[Repro₁(A) ⇒ 1]| ≤ (3 R / 2) √(q / |X₁|)` (`lemmaC1`, since `√2 < 3/2`).
* **Quantum Lemma C.5** (`DI-Repro → Repro`): `diReproProb_eq_reproProb_filterRun`, together with
  `diRepro_lemmaC3_one`, `diRepro_lemmaC3_half`, `diRepro_lemmaC1`.
* **Unconditional Quantum Corollaries C.1 and C.3** (`corollaryC1`, `diRepro_corollaryC1`,
  `diRepro_corollaryC3_one`, `diRepro_corollaryC3_half`, `diRepro_corollaryC3_min`): combining the
  proved QROM Lemmas C.1 and C.3 with the arithmetic of `Undetectability.Rest.ReproHalf`.

## Proof overview

1. Represent the joint adversary-and-oracle state in the coordinatewise Fourier basis
   `D : X₁ × X₂ → AddChar Y ℂ` using VCVio's unitary `Quantum.fourierMatrix Y`.
2. Initially `H` is uniform, so the Fourier state is supported on `D = 0` (`suppCard D = 0`).
   Each quantum query `|x, y⟩|H⟩ ↦ |x, y + H(x)⟩|H⟩` changes `D` at the single queried
   coordinate `x`, increasing `suppCard D` by at most `1` (`suppLe_jointQuery`).
3. In `Repro₁`, replacing `H(z)` by fresh uniform `y' ←$ Y` satisfies the exact Fourier Parseval
   identity `∑_χ ∑_H reproProbFrom (reproBranch z χ v) = |Y|⁻¹ ∑_{y', H} reproProbFrom (update H z y')`
   because `reproProbFrom` is a nonnegative quadratic form (`isQuadForm_reproProbFrom`). Keeping
   only the `χ = 0` branch (`Π_z`, projecting `D z = 0`) gives a lower bound on `Repro₁` for both
   `out = true` and `out = false` (`sum_reproProbFrom_reproBranch_zero_le`).
4. By induction over the `R` stages, the real inner product `Re⟨φ | ψ_good⟩` drops at stage `j`
   by at most `q̂_j / |X₁|` (Cauchy-Schwarz over `x₁ ∈ X₁` and `(x₂, flag)`), yielding the
   Bernoulli fidelity bound `1 − (∑_j q̂_j) / |X₁| ≤ √p₀ √p₁ + √(1 − p₀) √(1 − p₁)`, from which
   both `|√p₀ − √p₁| ≤ √(2ε)` and `|p₀ − p₁| ≤ √(2ε)` follow by elementary real algebra.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability.ReproQrom

open Finset Matrix Quantum
open scoped ComplexConjugate

/-! ## Elementary complex inner products and real fidelity inequalities -/

section Inner

variable {ι : Type*} [Fintype ι]

/-- Standard complex inner product `⟨u, v⟩ = ∑ i, conj (u i) * v i`. -/
def cInner (u v : ι → ℂ) : ℂ := ∑ i : ι, star (u i) * v i

/-- Squared Euclidean norm `‖u‖² = ∑ i, ‖u i‖²`. -/
noncomputable def normSq (u : ι → ℂ) : ℝ := ∑ i : ι, ‖u i‖ ^ 2

lemma normSq_nonneg (u : ι → ℂ) : 0 ≤ normSq u :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma cInner_self (u : ι → ℂ) : cInner u u = ((normSq u : ℝ) : ℂ) := by
  unfold cInner normSq
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul', Complex.ofReal_pow]

lemma cInner_self_re (u : ι → ℂ) : (cInner u u).re = normSq u := by
  rw [cInner_self, Complex.ofReal_re]

/-- Cauchy-Schwarz inequality `Re⟨u, v⟩ ≤ √‖u‖² · √‖v‖²`. -/
theorem re_cInner_le_sqrt_mul_sqrt (u v : ι → ℂ) :
    (cInner u v).re ≤ Real.sqrt (normSq u) * Real.sqrt (normSq v) := by
  have h1 : (cInner u v).re ≤ ‖cInner u v‖ := Complex.re_le_norm _
  have h2 : ‖cInner u v‖ ≤ ∑ i : ι, ‖u i‖ * ‖v i‖ := by
    calc ‖cInner u v‖ ≤ ∑ i : ι, ‖star (u i) * v i‖ := norm_sum_le _ _
      _ = ∑ i : ι, ‖u i‖ * ‖v i‖ := by
          refine sum_congr rfl fun i _ => ?_
          rw [norm_mul, RCLike.star_def, Complex.norm_conj]
  have hcs : (∑ i : ι, ‖u i‖ * ‖v i‖) ^ 2 ≤ normSq u * normSq v :=
    sum_mul_sq_le_sq_mul_sq univ (fun i => ‖u i‖) (fun i => ‖v i‖)
  have h3 : ∑ i : ι, ‖u i‖ * ‖v i‖ ≤ Real.sqrt (normSq u) * Real.sqrt (normSq v) := by
    rw [← Real.sqrt_mul (normSq_nonneg u)]
    exact Real.le_sqrt_of_sq_le hcs
  exact h1.trans (h2.trans h3)

/-- Unitary matrices preserve `cInner`. -/
theorem cInner_unitary_mulVec [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (u v : ι → ℂ) :
    cInner (U.1.mulVec u) (U.1.mulVec v) = cInner u v := by
  have hU : U.1ᴴ * U.1 = 1 := (Matrix.mem_unitaryGroup_iff'.mp U.2)
  have hdot : ∀ a b : ι → ℂ, cInner a b = star a ⬝ᵥ b := fun _ _ => rfl
  rw [hdot, hdot]
  have hstar : star (U.1 *ᵥ u) = star u ᵥ* U.1ᴴ := by
    funext i
    simp only [Pi.star_apply, mulVec, vecMul, dotProduct, conjTranspose_apply, star_sum,
      star_mul', mul_comm]
  rw [hstar, dotProduct_mulVec, vecMul_vecMul, hU, vecMul_one]

/-- Unitary matrices preserve `normSq`. -/
theorem normSq_unitary_mulVec [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (u : ι → ℂ) :
    normSq (U.1.mulVec u) = normSq u := by
  rw [← cInner_self_re, cInner_unitary_mulVec, cInner_self_re]

lemma cInner_comp_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ) (u v : κ → ℂ) :
    cInner (fun i => u (e i)) (fun i => v (e i)) = cInner u v :=
  Equiv.sum_comp e fun k => star (u k) * v k

lemma normSq_comp_equiv {κ : Type*} [Fintype κ] (e : ι ≃ κ) (u : κ → ℂ) :
    normSq (fun i => u (e i)) = normSq u :=
  Equiv.sum_comp e fun k => ‖u k‖ ^ 2

end Inner

/-- Cauchy-Schwarz for sums of square roots: `∑ a, √(f a) √(g a) ≤ √(∑ a, f a) √(∑ a, g a)`. -/
lemma sum_sqrt_mul_sqrt_le {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, Real.sqrt (f i) * Real.sqrt (g i) ≤
      Real.sqrt (∑ i ∈ s, f i) * Real.sqrt (∑ i ∈ s, g i) := by
  have hcs := sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (f i)) (fun i => Real.sqrt (g i))
  have hsf : ∑ i ∈ s, Real.sqrt (f i) ^ 2 = ∑ i ∈ s, f i :=
    sum_congr rfl fun i hi => Real.sq_sqrt (hf i hi)
  have hsg : ∑ i ∈ s, Real.sqrt (g i) ^ 2 = ∑ i ∈ s, g i :=
    sum_congr rfl fun i hi => Real.sq_sqrt (hg i hi)
  rw [hsf, hsg] at hcs
  rw [← Real.sqrt_mul (sum_nonneg hf)]
  exact Real.le_sqrt_of_sq_le hcs

/-- Elementary Bernoulli fidelity inequality: if `p₀, p₁ ∈ [0, 1]` and
`1 − ε ≤ √p₀ √p₁ + √(1 − p₀) √(1 − p₁)` with `0 ≤ ε`, then BOTH
`|√p₀ − √p₁| ≤ √(2ε)` AND `|p₀ − p₁| ≤ √(2ε)`. -/
theorem abs_sqrt_sub_and_abs_sub_le_of_fidelity {p₀ p₁ ε : ℝ}
    (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (hp₁ : p₁ ∈ Set.Icc (0 : ℝ) 1) (_hε : 0 ≤ ε)
    (hfid : 1 - ε ≤ Real.sqrt p₀ * Real.sqrt p₁ + Real.sqrt (1 - p₀) * Real.sqrt (1 - p₁)) :
    |Real.sqrt p₀ - Real.sqrt p₁| ≤ Real.sqrt (2 * ε) ∧
      |p₀ - p₁| ≤ Real.sqrt (2 * ε) := by
  have hs0 : Real.sqrt p₀ ^ 2 = p₀ := Real.sq_sqrt hp₀.1
  have hs1 : Real.sqrt p₁ ^ 2 = p₁ := Real.sq_sqrt hp₁.1
  have hq0 : Real.sqrt (1 - p₀) ^ 2 = 1 - p₀ := Real.sq_sqrt (by linarith [hp₀.2])
  have hq1 : Real.sqrt (1 - p₁) ^ 2 = 1 - p₁ := Real.sq_sqrt (by linarith [hp₁.2])
  constructor
  · have hsq : (Real.sqrt p₀ - Real.sqrt p₁) ^ 2 ≤ 2 * ε := by
      have hnonneg : 0 ≤ (Real.sqrt (1 - p₀) - Real.sqrt (1 - p₁)) ^ 2 := sq_nonneg _
      nlinarith [hs0, hs1, hq0, hq1, hfid, hnonneg]
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  · by_cases hε1 : 1 ≤ ε
    · have habs : |p₀ - p₁| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hp₀.1, hp₀.2, hp₁.1, hp₁.2]
      have h1le : (1 : ℝ) ≤ Real.sqrt (2 * ε) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith)
      exact habs.trans h1le
    · push Not at hε1
      have hF_sq : (1 - ε) ^ 2 ≤
          (Real.sqrt p₀ * Real.sqrt p₁ + Real.sqrt (1 - p₀) * Real.sqrt (1 - p₁)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hfid 2
      have hident :
          (Real.sqrt p₀ * Real.sqrt p₁ + Real.sqrt (1 - p₀) * Real.sqrt (1 - p₁)) ^ 2 +
          (Real.sqrt p₀ * Real.sqrt (1 - p₁) - Real.sqrt (1 - p₀) * Real.sqrt p₁) ^ 2 = 1 := by
        nlinarith [hs0, hs1, hq0, hq1]
      have hdiff_factor :
          p₀ - p₁ = (Real.sqrt p₀ * Real.sqrt (1 - p₁) - Real.sqrt (1 - p₀) * Real.sqrt p₁) *
            (Real.sqrt p₀ * Real.sqrt (1 - p₁) + Real.sqrt (1 - p₀) * Real.sqrt p₁) := by
        nlinarith [hs0, hs1, hq0, hq1]
      have hsum_sq :
          (Real.sqrt p₀ * Real.sqrt (1 - p₁) + Real.sqrt (1 - p₀) * Real.sqrt p₁) ^ 2 ≤ 1 := by
        have hcs : 0 ≤ (Real.sqrt p₀ * Real.sqrt p₁ - Real.sqrt (1 - p₀) * Real.sqrt (1 - p₁)) ^ 2 :=
          sq_nonneg _
        nlinarith [hs0, hs1, hq0, hq1, hcs]
      have hsq : (p₀ - p₁) ^ 2 ≤ 2 * ε := by
        have h1 : (p₀ - p₁) ^ 2 ≤
            (Real.sqrt p₀ * Real.sqrt (1 - p₁) - Real.sqrt (1 - p₀) * Real.sqrt p₁) ^ 2 := by
          rw [hdiff_factor, mul_pow]
          exact mul_le_of_le_one_right (sq_nonneg _) hsum_sq
        nlinarith [h1, hident, hF_sq, sq_nonneg ε]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq

/-! ## Multi-stage quantum `Repro` and `DI-Repro` experiments in the QROM -/

section ReproGame

variable (X₁ X₂ Y E : Type*) [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E]

/-- The adversary's quantum register: query input `(x₁, x₂)`, response `y`, and workspace `E`. -/
abbrev Reg := ((X₁ × X₂) × Y) × E

/-- A multi-stage quantum reprogramming program making at most `R` classical reprogramming calls
interleaved with quantum query stages, where stage `j` makes `q j` superposition queries to `O_b`.
At each `call`, `callX2 r = (x₂, doRepro)`: when `doRepro = true` the challenger executes
`Reprogram(x₂)` and hands `some x₁` to `cont x₂`; when `doRepro = false` the call is skipped
(no reprogramming in either world, passing `none` to `cont x₂`). -/
inductive ReproProg : (R : ℕ) → (Fin (R + 1) → ℕ) → Type _ where
  /-- Final query stage (`m` oracle queries) followed by a projective output-bit measurement. -/
  | done (m : ℕ)
      (stage : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (accept : Reg X₁ X₂ Y E → Bool) :
      ReproProg 0 ![m]
  /-- Query stage (`m` oracle queries), classical readout `callX2 : Reg → X₂ × Bool`,
  and continuation receiving `(x₂, optX1)`. -/
  | call {R : ℕ} {q : Fin (R + 1) → ℕ} (m : ℕ)
      (stage : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (callX2 : Reg X₁ X₂ Y E → X₂ × Bool)
      (cont : X₂ → Option X₁ → ReproProg R q) :
      ReproProg (R + 1) (Fin.cons m q)

/-- A standard Definition C.1 `Repro` program: every `call` invokes `Reprogram(x₂)`
(`(callX2 r).2 = true`). -/
def ReproProg.IsStandard : ∀ {R : ℕ} {q : Fin (R + 1) → ℕ}, ReproProg X₁ X₂ Y E R q → Prop
  | _, _, .done _ _ _ => True
  | _, _, .call _ _ callX2 cont =>
      (∀ r, (callX2 r).2 = true) ∧ ∀ x₂ x₁, (cont x₂ (some x₁)).IsStandard

/-- A Definition C.2 `DI-Repro` quantum program: submits `x₂ : X₂` at each of `R` calls and
receives `some x₁` on fresh `x₂`, or `none` (`⊥`) on repeated `x₂`. -/
inductive DIReproProg : (R : ℕ) → (Fin (R + 1) → ℕ) → Type _ where
  | done (m : ℕ)
      (stage : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (accept : Reg X₁ X₂ Y E → Bool) :
      DIReproProg 0 ![m]
  | call {R : ℕ} {q : Fin (R + 1) → ℕ} (m : ℕ)
      (stage : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (callX2 : Reg X₁ X₂ Y E → X₂)
      (cont : X₂ → Option X₁ → DIReproProg R q) :
      DIReproProg (R + 1) (Fin.cons m q)

variable {X₁ X₂ Y E}

/-- Cumulative query count `q̂_j = ∑_{i ≤ j} q_i` issued before the `j`-th `Reprogram` call. -/
def qhat {R : ℕ} (q : Fin (R + 1) → ℕ) (j : Fin R) : ℕ :=
  ∑ i : Fin (j.val + 1), q ⟨i.val, by omega⟩

lemma qhat_cons_zero {R : ℕ} (m : ℕ) (q : Fin (R + 1) → ℕ) :
    qhat (Fin.cons m q) 0 = m := by
  unfold qhat
  exact Fin.sum_univ_one _

lemma qhat_cons_succ {R : ℕ} (m : ℕ) (q : Fin (R + 1) → ℕ) (j : Fin R) :
    qhat (Fin.cons m q) j.succ = m + qhat q j := by
  unfold qhat
  simp only [Fin.val_succ]
  rw [Fin.sum_univ_succ]
  congr 1

lemma sum_qhat_cons {R : ℕ} (k m : ℕ) (q : Fin (R + 1) → ℕ) :
    ∑ j : Fin (R + 1), ((k + qhat (Fin.cons m q) j : ℕ) : ℝ) =
      ((k + m : ℕ) : ℝ) + ∑ j : Fin R, (((k + m) + qhat q j : ℕ) : ℝ) := by
  rw [Fin.sum_univ_succ]
  simp only [qhat_cons_zero, qhat_cons_succ, Nat.add_assoc]

/-- One standard quantum oracle query `|x, y⟩|e⟩ ↦ |x, y + H x⟩|e⟩` on `Reg → ℂ`:
`(U_H ⊗ I_E) ψ ((x, y), e) = ψ ((x, y - H x), e)`. -/
def queryVec (H : X₁ × X₂ → Y) (ψ : Reg X₁ X₂ Y E → ℂ) : Reg X₁ X₂ Y E → ℂ :=
  fun r => ψ ((r.1.1, r.1.2 - H r.1.1), r.2)

/-- The index bijection underlying `queryVec H`. -/
def queryEquiv (H : X₁ × X₂ → Y) : Reg X₁ X₂ Y E ≃ Reg X₁ X₂ Y E where
  toFun r := ((r.1.1, r.1.2 - H r.1.1), r.2)
  invFun r := ((r.1.1, r.1.2 + H r.1.1), r.2)
  left_inv r := by rcases r with ⟨⟨x, y⟩, e⟩; simp
  right_inv r := by rcases r with ⟨⟨x, y⟩, e⟩; simp

omit [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y] [DecidableEq E] in
lemma cInner_queryVec (H : X₁ × X₂ → Y) (u v : Reg X₁ X₂ Y E → ℂ) :
    cInner (queryVec H u) (queryVec H v) = cInner u v :=
  cInner_comp_equiv (queryEquiv H) u v

omit [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y] [DecidableEq E] in
lemma normSq_queryVec (H : X₁ × X₂ → Y) (u : Reg X₁ X₂ Y E → ℂ) :
    normSq (queryVec H u) = normSq u :=
  normSq_comp_equiv (queryEquiv H) u

/-- Execute one query stage: `U_0`, then `m` interleaved pairs `(queryVec H, U_{k+1})`. -/
noncomputable def applyStage (H : X₁ × X₂ → Y) :
    ∀ (m : ℕ), (Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ) →
      (Reg X₁ X₂ Y E → ℂ) → (Reg X₁ X₂ Y E → ℂ)
  | 0, U, ψ => (U 0).1.mulVec ψ
  | m + 1, U, ψ =>
      (U (Fin.last (m + 1))).1.mulVec
        (queryVec H (applyStage H m (fun k => U k.castSucc) ψ))

lemma applyStage_add (H : X₁ × X₂ → Y) :
    ∀ (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (u v : Reg X₁ X₂ Y E → ℂ),
      applyStage H m U (fun r => u r + v r) =
        fun r => applyStage H m U u r + applyStage H m U v r
  | 0, U, u, v => by
      funext r; simp only [applyStage, mulVec, dotProduct, mul_add, sum_add_distrib]
  | m + 1, U, u, v => by
      simp only [applyStage]
      have hq : queryVec H (applyStage H m (fun k => U k.castSucc) (fun r => u r + v r)) =
          fun r => queryVec H (applyStage H m (fun k => U k.castSucc) u) r +
            queryVec H (applyStage H m (fun k => U k.castSucc) v) r := by
        funext r; simp only [queryVec, applyStage_add]
      rw [hq]
      funext r
      simp only [mulVec, dotProduct, mul_add, sum_add_distrib]

lemma applyStage_smul (H : X₁ × X₂ → Y) :
    ∀ (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (c : ℂ) (u : Reg X₁ X₂ Y E → ℂ),
      applyStage H m U (fun r => c * u r) = fun r => c * applyStage H m U u r
  | 0, U, c, u => by
      funext r
      simp only [applyStage, mulVec, dotProduct, mul_sum]
      refine sum_congr rfl fun r' _ => by ring
  | m + 1, U, c, u => by
      simp only [applyStage]
      have hq : queryVec H (applyStage H m (fun k => U k.castSucc) (fun r => c * u r)) =
          fun r => c * queryVec H (applyStage H m (fun k => U k.castSucc) u) r := by
        funext r; simp only [queryVec, applyStage_smul]
      rw [hq]
      funext r
      simp only [mulVec, dotProduct, mul_sum]
      refine sum_congr rfl fun r' _ => by ring

lemma cInner_applyStage (H : X₁ × X₂ → Y) :
    ∀ (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      (u v : Reg X₁ X₂ Y E → ℂ),
      cInner (applyStage H m U u) (applyStage H m U v) = cInner u v
  | 0, U, u, v => cInner_unitary_mulVec (U 0) u v
  | m + 1, U, u, v => by
      simp only [applyStage]
      rw [cInner_unitary_mulVec, cInner_queryVec, cInner_applyStage]

lemma normSq_applyStage (H : X₁ × X₂ → Y) (m : ℕ)
    (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ) (u : Reg X₁ X₂ Y E → ℂ) :
    normSq (applyStage H m U u) = normSq u := by
  rw [← cInner_self_re, cInner_applyStage, cInner_self_re]

/-- Project a state vector onto the subspace `{r | f r = a}`. -/
def projBy {α : Type*} [DecidableEq α] (f : Reg X₁ X₂ Y E → α) (a : α)
    (ψ : Reg X₁ X₂ Y E → ℂ) : Reg X₁ X₂ Y E → ℂ :=
  fun r => if f r = a then ψ r else 0

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E] in
lemma projBy_add {α : Type*} [DecidableEq α] (f : Reg X₁ X₂ Y E → α) (a : α)
    (u v : Reg X₁ X₂ Y E → ℂ) :
    projBy f a (fun r => u r + v r) = fun r => projBy f a u r + projBy f a v r := by
  funext r; unfold projBy; split_ifs <;> simp

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E] in
lemma projBy_smul {α : Type*} [DecidableEq α] (f : Reg X₁ X₂ Y E → α) (a : α)
    (c : ℂ) (u : Reg X₁ X₂ Y E → ℂ) :
    projBy f a (fun r => c * u r) = fun r => c * projBy f a u r := by
  funext r; unfold projBy; split_ifs <;> simp

omit [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y] [AddCommGroup Y] [DecidableEq E] in
lemma sum_normSq_projBy {α : Type*} [Fintype α] [DecidableEq α]
    (f : Reg X₁ X₂ Y E → α) (ψ : Reg X₁ X₂ Y E → ℂ) :
    ∑ a : α, normSq (projBy f a ψ) = normSq ψ := by
  simp only [normSq, projBy]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_eq_single (f r)]
  · simp
  · intro a _ hne; simp [Ne.symm hne]
  · intro h; exact (h (mem_univ _)).elim

/-- Output probability of `out : Bool` for a `ReproProg` in world `b : Bool` starting from
fixed oracle `H` and subnormalized state `ψ`. -/
noncomputable def reproProbFrom (b : Bool) (out : Bool) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ}, ReproProg X₁ X₂ Y E R q →
      (X₁ × X₂ → Y) → (Reg X₁ X₂ Y E → ℂ) → ℝ
  | _, _, .done m stage accept, H, ψ =>
      let ψ' := applyStage H m stage ψ
      ∑ r : Reg X₁ X₂ Y E, if accept r = out then ‖ψ' r‖ ^ 2 else 0
  | _, _, .call m stage callX2 cont, H, ψ =>
      let ψ' := applyStage H m stage ψ
      ∑ x₂ : X₂,
        (reproProbFrom b out (cont x₂ none) H (projBy callX2 (x₂, false) ψ') +
         (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁,
           (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
             reproProbFrom b out (cont x₂ (some x₁))
               (if b then Function.update H (x₁, x₂) y' else H)
               (projBy callX2 (x₂, true) ψ'))

/-- **`Pr[Repro_b(A) ⇒ out]`** (Definition C.1, in the QROM): uniform initial oracle `H ←$`,
starting from unit initial state `init`. -/
noncomputable def reproProb [Nonempty X₁] (b : Bool) (out : Bool) {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) (init : Reg X₁ X₂ Y E → ℂ) : ℝ :=
  (Fintype.card (X₁ × X₂ → Y) : ℝ)⁻¹ * ∑ H : X₁ × X₂ → Y, reproProbFrom b out prog H init

/-- Output probability of `out : Bool` for a `DIReproProg` in world `b : Bool` (**Definition C.2**),
tracking the set `seen : Finset X₂` of previously submitted second inputs. -/
noncomputable def diReproProbFrom (b : Bool) (out : Bool) (seen : Finset X₂) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ}, DIReproProg X₁ X₂ Y E R q →
      (X₁ × X₂ → Y) → (Reg X₁ X₂ Y E → ℂ) → ℝ
  | _, _, .done m stage accept, H, ψ =>
      let ψ' := applyStage H m stage ψ
      ∑ r : Reg X₁ X₂ Y E, if accept r = out then ‖ψ' r‖ ^ 2 else 0
  | _, _, .call m stage callX2 cont, H, ψ =>
      let ψ' := applyStage H m stage ψ
      ∑ x₂ : X₂,
        if x₂ ∈ seen then
          diReproProbFrom b out seen (cont x₂ none) H (projBy callX2 x₂ ψ')
        else
          (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁,
            (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
              diReproProbFrom b out (insert x₂ seen) (cont x₂ (some x₁))
                (if b then Function.update H (x₁, x₂) y' else H)
                (projBy callX2 x₂ ψ')

/-- **`Pr[DI-Repro_b(A) ⇒ out]`** (Definition C.2, in the QROM). -/
noncomputable def diReproProb [Nonempty X₁] (b : Bool) (out : Bool) {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : DIReproProg X₁ X₂ Y E R q) (init : Reg X₁ X₂ Y E → ℂ) : ℝ :=
  (Fintype.card (X₁ × X₂ → Y) : ℝ)⁻¹ * ∑ H : X₁ × X₂ → Y, diReproProbFrom b out ∅ prog H init

lemma reproProbFrom_zero (b out : Bool) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ} (prog : ReproProg X₁ X₂ Y E R q) (H : X₁ × X₂ → Y),
      reproProbFrom b out prog H 0 = 0
  | _, _, .done m stage accept, H => by
      have hz : applyStage H m stage 0 = 0 := by
        calc applyStage H m stage 0
            = applyStage H m stage (fun r => 0 * (0 : Reg X₁ X₂ Y E → ℂ) r) := by
              congr 1; funext r; simp
          _ = fun r => 0 * applyStage H m stage 0 r := applyStage_smul H m stage 0 0
          _ = 0 := by funext r; simp
      simp [reproProbFrom, hz]
  | _, _, .call m stage callX2 cont, H => by
      have hz : applyStage H m stage 0 = 0 := by
        calc applyStage H m stage 0
            = applyStage H m stage (fun r => 0 * (0 : Reg X₁ X₂ Y E → ℂ) r) := by
              congr 1; funext r; simp
          _ = fun r => 0 * applyStage H m stage 0 r := applyStage_smul H m stage 0 0
          _ = 0 := by funext r; simp
      have hp : ∀ a, projBy callX2 a (0 : Reg X₁ X₂ Y E → ℂ) = 0 := fun a => by
        funext r; simp [projBy]
      simp [reproProbFrom, hz, hp, reproProbFrom_zero]

lemma reproProbFrom_nonneg (b out : Bool) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ} (prog : ReproProg X₁ X₂ Y E R q)
      (H : X₁ × X₂ → Y) (ψ : Reg X₁ X₂ Y E → ℂ),
      0 ≤ reproProbFrom b out prog H ψ
  | _, _, .done _ _ _, _, _ =>
      sum_nonneg fun _ _ => by split_ifs <;> positivity
  | _, _, .call _ _ _ cont, H, ψ =>
      sum_nonneg fun x₂ _ => add_nonneg (reproProbFrom_nonneg b out (cont x₂ none) _ _)
        (mul_nonneg (by positivity) (sum_nonneg fun x₁ _ => mul_nonneg (by positivity)
          (sum_nonneg fun y' _ => reproProbFrom_nonneg b out (cont x₂ (some x₁)) _ _)))

lemma reproProbFrom_true_add_false [Nonempty X₁] (b : Bool) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ} (prog : ReproProg X₁ X₂ Y E R q)
      (H : X₁ × X₂ → Y) (ψ : Reg X₁ X₂ Y E → ℂ),
      reproProbFrom b true prog H ψ + reproProbFrom b false prog H ψ = normSq ψ
  | _, _, .done m stage accept, H, ψ => by
      simp only [reproProbFrom, ← sum_add_distrib]
      have hterm : ∀ r : Reg X₁ X₂ Y E,
          (if accept r = true then ‖applyStage H m stage ψ r‖ ^ 2 else 0) +
          (if accept r = false then ‖applyStage H m stage ψ r‖ ^ 2 else 0) =
          ‖applyStage H m stage ψ r‖ ^ 2 := fun r => by cases accept r <;> simp
      simp_rw [hterm]
      exact normSq_applyStage H m stage ψ
  | _, _, .call m stage callX2 cont, H, ψ => by
      simp only [reproProbFrom, ← sum_add_distrib]
      have hX1 : (Fintype.card X₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hY : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hterm : ∀ x₂ : X₂,
          (reproProbFrom b true (cont x₂ none) H (projBy callX2 (x₂, false) (applyStage H m stage ψ)) +
            (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
              reproProbFrom b true (cont x₂ (some x₁))
                (if b then Function.update H (x₁, x₂) y' else H)
                (projBy callX2 (x₂, true) (applyStage H m stage ψ))) +
          (reproProbFrom b false (cont x₂ none) H (projBy callX2 (x₂, false) (applyStage H m stage ψ)) +
            (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
              reproProbFrom b false (cont x₂ (some x₁))
                (if b then Function.update H (x₁, x₂) y' else H)
                (projBy callX2 (x₂, true) (applyStage H m stage ψ))) =
          normSq (projBy callX2 (x₂, false) (applyStage H m stage ψ)) +
          normSq (projBy callX2 (x₂, true) (applyStage H m stage ψ)) := by
        intro x₂
        have hfalse := reproProbFrom_true_add_false b (cont x₂ none) H
          (projBy callX2 (x₂, false) (applyStage H m stage ψ))
        have htrue :
            (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
              reproProbFrom b true (cont x₂ (some x₁))
                (if b then Function.update H (x₁, x₂) y' else H)
                (projBy callX2 (x₂, true) (applyStage H m stage ψ)) +
            (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
              reproProbFrom b false (cont x₂ (some x₁))
                (if b then Function.update H (x₁, x₂) y' else H)
                (projBy callX2 (x₂, true) (applyStage H m stage ψ)) =
            normSq (projBy callX2 (x₂, true) (applyStage H m stage ψ)) := by
          rw [← mul_add, ← sum_add_distrib]
          simp_rw [← mul_add, ← sum_add_distrib, reproProbFrom_true_add_false]
          simp only [sum_const, card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hY,
            inv_mul_cancel_left₀ hX1]
        linarith
      simp_rw [hterm]
      have htot := sum_normSq_projBy callX2 (applyStage H m stage ψ)
      rw [Fintype.sum_prod_type] at htot
      simp only [Fintype.sum_bool, add_comm] at htot
      rwa [normSq_applyStage] at htot

lemma reproProb_nonneg [Nonempty X₁] (b out : Bool) {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) (init : Reg X₁ X₂ Y E → ℂ) :
    0 ≤ reproProb b out prog init :=
  mul_nonneg (by positivity) (sum_nonneg fun H _ => reproProbFrom_nonneg b out prog H init)

lemma reproProb_true_add_false [Nonempty X₁] (b : Bool) {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    reproProb b true prog init + reproProb b false prog init = 1 := by
  unfold reproProb
  rw [← mul_add, ← sum_add_distrib]
  simp_rw [reproProbFrom_true_add_false, hinit, sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hH : (Fintype.card (X₁ × X₂ → Y) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact inv_mul_cancel₀ hH

lemma reproProb_mem_Icc [Nonempty X₁] (b : Bool) {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    reproProb b true prog init ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨reproProb_nonneg b true prog init, by
    linarith [reproProb_true_add_false b prog hinit, reproProb_nonneg b false prog init]⟩

/-! ## Quantum Lemma C.5 (`DI-Repro` → `Repro` filtering) -/

/-- **Quantum Lemma C.5's filter wrapper (`filterRun`)**: given a `DI-Repro` adversary `prog`
and the set `seen` of previously submitted second inputs, produce the equivalent `ReproProg`
that skips repeated `x₂` calls (`doRepro = false`) and forwards fresh ones (`doRepro = true`). -/
def filterRun (seen : Finset X₂) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ}, DIReproProg X₁ X₂ Y E R q → ReproProg X₁ X₂ Y E R q
  | _, _, .done m stage accept => .done m stage accept
  | _, _, .call m stage callX2 cont =>
      .call m stage (fun r => (callX2 r, decide (callX2 r ∉ seen)))
        (fun x₂ ox₁ =>
          match ox₁ with
          | none => filterRun seen (cont x₂ none)
          | some x₁ => filterRun (insert x₂ seen) (cont x₂ (some x₁)))

/-- **Quantum Lemma C.5 (pointwise)**: `DI-Repro_b` on `prog` equals `Repro_b` on
`filterRun seen prog`, with identical query counts `q`. -/
theorem diReproProbFrom_eq_reproProbFrom_filterRun (b out : Bool) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ} (seen : Finset X₂) (prog : DIReproProg X₁ X₂ Y E R q)
      (H : X₁ × X₂ → Y) (ψ : Reg X₁ X₂ Y E → ℂ),
      diReproProbFrom b out seen prog H ψ =
        reproProbFrom b out (filterRun seen prog) H ψ
  | _, _, _, .done _ _ _, _, _ => rfl
  | _, _, seen, .call m stage callX2 cont, H, ψ => by
      simp only [diReproProbFrom, filterRun, reproProbFrom]
      refine sum_congr rfl fun x₂ _ => ?_
      by_cases hmem : x₂ ∈ seen
      · have hpF : projBy (fun r => (callX2 r, decide (callX2 r ∉ seen))) (x₂, false)
            (applyStage H m stage ψ) = projBy callX2 x₂ (applyStage H m stage ψ) := by
          funext r; unfold projBy
          by_cases h : callX2 r = x₂ <;> simp [h, hmem]
        have hpT : projBy (fun r => (callX2 r, decide (callX2 r ∉ seen))) (x₂, true)
            (applyStage H m stage ψ) = 0 := by
          funext r; unfold projBy
          by_cases h : callX2 r = x₂ <;> simp [h, hmem]
        simp only [hmem, ↓reduceIte, hpF, hpT, reproProbFrom_zero, sum_const_zero, mul_zero,
          add_zero]
        exact diReproProbFrom_eq_reproProbFrom_filterRun b out seen (cont x₂ none) H _
      · have hpF : projBy (fun r => (callX2 r, decide (callX2 r ∉ seen))) (x₂, false)
            (applyStage H m stage ψ) = 0 := by
          funext r; unfold projBy
          by_cases h : callX2 r = x₂ <;> simp [h, hmem]
        have hpT : projBy (fun r => (callX2 r, decide (callX2 r ∉ seen))) (x₂, true)
            (applyStage H m stage ψ) = projBy callX2 x₂ (applyStage H m stage ψ) := by
          funext r; unfold projBy
          by_cases h : callX2 r = x₂ <;> simp [h, hmem]
        simp only [hmem, ↓reduceIte, hpF, hpT, reproProbFrom_zero, zero_add]
        congr 1
        refine sum_congr rfl fun x₁ _ => ?_
        congr 1
        refine sum_congr rfl fun y' _ => ?_
        exact diReproProbFrom_eq_reproProbFrom_filterRun b out (insert x₂ seen)
          (cont x₂ (some x₁)) _ _

/-- **Quantum Lemma C.5**: `Pr[DI-Repro_b(A) ⇒ out] = Pr[Repro_b(filterRun ∅ A) ⇒ out]`. -/
theorem diReproProb_eq_reproProb_filterRun [Nonempty X₁] (b out : Bool)
    {R : ℕ} {q : Fin (R + 1) → ℕ} (prog : DIReproProg X₁ X₂ Y E R q)
    (init : Reg X₁ X₂ Y E → ℂ) :
    diReproProb b out prog init = reproProb b out (filterRun ∅ prog) init := by
  unfold diReproProb reproProb
  congr 1
  refine sum_congr rfl fun H _ => diReproProbFrom_eq_reproProbFrom_filterRun b out ∅ prog H init

/-! ## Coordinatewise Fourier transform on the oracle register `X₁ × X₂ → Y` -/

section Fourier

variable (X₁ X₂ Y E)

/-- The Pontryagin dual of `Y`. -/
abbrev Yhat := AddChar Y ℂ

/-- A Fourier-basis oracle table `D : X₁ × X₂ → Ŷ`. -/
abbrev FTbl := (X₁ × X₂) → Yhat Y

/-- Joint register + computational-basis oracle table. -/
abbrev Joint := Reg X₁ X₂ Y E × (X₁ × X₂ → Y)

/-- Joint register + Fourier-basis oracle table. -/
abbrev FJoint := Reg X₁ X₂ Y E × FTbl X₁ X₂ Y

variable {X₁ X₂ Y E}

/-- Entry of VCVio's Fourier matrix as an ordinary function `Yhat Y → Y → ℂ` (avoids
semireducible `Matrix` unfolding issues during rewrites). -/
noncomputable def fEntry (χ : Yhat Y) (y : Y) : ℂ := fourierMatrix Y χ y

/-- Coordinatewise Fourier transform on the oracle register. -/
noncomputable def ftVec (v : Joint X₁ X₂ Y E → ℂ) : FJoint X₁ X₂ Y E → ℂ :=
  fun p => ∑ H : X₁ × X₂ → Y, (∏ z : X₁ × X₂, fEntry (p.2 z) (H z)) * v (p.1, H)

/-- Inverse coordinatewise Fourier transform on the oracle register. -/
noncomputable def iftVec (w : FJoint X₁ X₂ Y E → ℂ) : Joint X₁ X₂ Y E → ℂ :=
  fun p => ∑ D : FTbl X₁ X₂ Y, (∏ z : X₁ × X₂, star (fEntry (D z) (p.2 z))) * w (p.1, D)

lemma sum_fourier_conj_mul (y₁ y₂ : Y) :
    ∑ χ : Yhat Y, star (fEntry χ y₁) * fEntry χ y₂ =
      if y₁ = y₂ then 1 else 0 := by
  have h := congrFun (congrFun (conjTranspose_fourierMatrix_mul Y) y₁) y₂
  simpa [fEntry, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] using h

omit [DecidableEq Y] in
lemma sum_fourier_mul_conj (χ₁ χ₂ : Yhat Y) :
    ∑ y : Y, fEntry χ₁ y * star (fEntry χ₂ y) =
      if χ₁ = χ₂ then 1 else 0 := by
  have h := congrFun (congrFun (fourierMatrix_mul_conjTranspose Y) χ₁) χ₂
  simpa [fEntry, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] using h

lemma sum_prod_fourier_conj_mul (H₁ H₂ : X₁ × X₂ → Y) :
    ∑ D : FTbl X₁ X₂ Y,
        star (∏ z : X₁ × X₂, fEntry (D z) (H₁ z)) *
        (∏ z : X₁ × X₂, fEntry (D z) (H₂ z)) =
      if H₁ = H₂ then 1 else 0 := by
  simp_rw [star_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (κ := fun _ : X₁ × X₂ => Yhat Y)
    (f := fun z χ => star (fEntry χ (H₁ z)) * fEntry χ (H₂ z))]
  simp_rw [sum_fourier_conj_mul]
  by_cases hEq : H₁ = H₂
  · subst hEq; simp
  · rw [ite_eq_right hEq]
    have hex : ∃ z, H₁ z ≠ H₂ z := by
      by_contra hall; push Not at hall; exact hEq (funext hall)
    obtain ⟨z, hz⟩ := hex
    exact prod_eq_zero (mem_univ z) (ite_eq_right hz)

omit [DecidableEq Y] in
lemma sum_prod_fourier_mul_conj (D₁ D₂ : FTbl X₁ X₂ Y) :
    ∑ H : X₁ × X₂ → Y,
        (∏ z : X₁ × X₂, fEntry (D₁ z) (H z)) *
        star (∏ z : X₁ × X₂, fEntry (D₂ z) (H z)) =
      if D₁ = D₂ then 1 else 0 := by
  simp_rw [star_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (κ := fun _ : X₁ × X₂ => Y)
    (f := fun z y => fEntry (D₁ z) y * star (fEntry (D₂ z) y))]
  simp_rw [sum_fourier_mul_conj]
  by_cases hEq : D₁ = D₂
  · subst hEq; simp
  · rw [ite_eq_right hEq]
    have hex : ∃ z, D₁ z ≠ D₂ z := by
      by_contra hall; push Not at hall; exact hEq (funext hall)
    obtain ⟨z, hz⟩ := hex
    exact prod_eq_zero (mem_univ z) (ite_eq_right hz)

omit [DecidableEq E] in
/-- `ftVec` preserves inner products (Parseval / unitarity). -/
theorem cInner_ftVec (u v : Joint X₁ X₂ Y E → ℂ) :
    cInner (ftVec u) (ftVec v) = cInner u v := by
  unfold cInner
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun r _ => ?_
  simp only [ftVec, star_sum, star_mul']
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  trans ∑ H₁ : X₁ × X₂ → Y, ∑ H₂ : X₁ × X₂ → Y,
      (∑ D : FTbl X₁ X₂ Y,
        star (∏ z : X₁ × X₂, fEntry (D z) (H₁ z)) *
        (∏ z : X₁ × X₂, fEntry (D z) (H₂ z))) *
      (star (u (r, H₁)) * v (r, H₂))
  · refine sum_congr rfl fun H₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun H₂ _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun D _ => by ring
  · simp_rw [sum_prod_fourier_conj_mul]
    refine sum_congr rfl fun H₁ _ => ?_
    rw [sum_eq_single H₁]
    · simp
    · intro H₂ _ hne; simp [Ne.symm hne]
    · intro h; exact (h (mem_univ _)).elim

omit [DecidableEq E] in
theorem normSq_ftVec (u : Joint X₁ X₂ Y E → ℂ) : normSq (ftVec u) = normSq u := by
  rw [← cInner_self_re, cInner_ftVec, cInner_self_re]

omit [Fintype E] [DecidableEq E] in
theorem iftVec_ftVec (v : Joint X₁ X₂ Y E → ℂ) : iftVec (ftVec v) = v := by
  funext ⟨r, H⟩
  simp only [iftVec, ftVec, mul_sum]
  rw [sum_comm]
  trans ∑ H' : X₁ × X₂ → Y,
      (∑ D : FTbl X₁ X₂ Y,
        star (∏ z : X₁ × X₂, fEntry (D z) (H z)) *
        (∏ z : X₁ × X₂, fEntry (D z) (H' z))) * v (r, H')
  · refine sum_congr rfl fun H' _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun D _ => by rw [star_prod]; ring
  · simp_rw [sum_prod_fourier_conj_mul]
    rw [sum_eq_single H]
    · simp
    · intro H' _ hne; simp [Ne.symm hne]
    · intro h; exact (h (mem_univ _)).elim

omit [DecidableEq Y] in
lemma sum_fourier_mul_cellAmp (χ : Yhat Y) :
    ∑ y : Y, fEntry χ y * cellAmp Y = if χ = 0 then 1 else 0 := by
  have h1 : ∀ y : Y, fEntry χ y * cellAmp Y =
      fEntry χ y * star (fEntry (0 : Yhat Y) y) := by
    intro y
    simp [fEntry, fourierMatrix_apply, star_cellAmp]
  simp_rw [h1]
  exact sum_fourier_mul_conj χ 0

/-- Support size `|supp(D)|` of a Fourier oracle table `D : X₁ × X₂ → Ŷ`. -/
noncomputable def suppCard (D : FTbl X₁ X₂ Y) : ℕ :=
  (univ.filter fun z : X₁ × X₂ => D z ≠ 0).card

/-- A Fourier state `w` is supported on tables `D` of support size at most `k`. -/
def SuppLe (k : ℕ) (w : FJoint X₁ X₂ Y E → ℂ) : Prop :=
  ∀ r D, w (r, D) ≠ 0 → suppCard D ≤ k

/-- Initial uniform oracle superposition `v₀ (r, H) = |Y|^{-|X|/2} · init r`. -/
noncomputable def initJoint (init : Reg X₁ X₂ Y E → ℂ) : Joint X₁ X₂ Y E → ℂ :=
  fun p => (cellAmp Y ^ Fintype.card (X₁ × X₂)) * init p.1

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma ftVec_initJoint (init : Reg X₁ X₂ Y E → ℂ) (r : Reg X₁ X₂ Y E) (D : FTbl X₁ X₂ Y) :
    ftVec (initJoint init) (r, D) = if D = 0 then init r else 0 := by
  unfold ftVec initJoint
  have h1 : ∀ H : X₁ × X₂ → Y,
      (∏ z : X₁ × X₂, fEntry (D z) (H z)) *
        (cellAmp Y ^ Fintype.card (X₁ × X₂) * init r) =
      (∏ z : X₁ × X₂, fEntry (D z) (H z) * cellAmp Y) * init r := by
    intro H
    rw [prod_mul_distrib, prod_const, card_univ]
    ring
  simp_rw [h1, ← sum_mul]
  rw [← Fintype.prod_sum (κ := fun _ : X₁ × X₂ => Y)
    (f := fun z y => fEntry (D z) y * cellAmp Y)]
  simp_rw [sum_fourier_mul_cellAmp]
  by_cases hD : D = 0
  · subst hD; simp
  · rw [ite_eq_right hD]
    have hex : ∃ z, D z ≠ 0 := by
      by_contra hall; push Not at hall; exact hD (funext hall)
    obtain ⟨z, hz⟩ := hex
    rw [prod_eq_zero (mem_univ z) (ite_eq_right hz), zero_mul]

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma suppLe_ftVec_initJoint (init : Reg X₁ X₂ Y E → ℂ) :
    SuppLe 0 (ftVec (initJoint init)) := by
  intro r D hne
  rw [ftVec_initJoint] at hne
  have hD : D = 0 := by
    by_contra h
    exact hne (ite_eq_right h)
  subst hD
  simp [suppCard]

omit [DecidableEq E] in
lemma normSq_initJoint (init : Reg X₁ X₂ Y E → ℂ) :
    normSq (initJoint init) = normSq init := by
  rw [← normSq_ftVec]
  unfold normSq
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_eq_single (0 : FTbl X₁ X₂ Y)]
  · simp [ftVec_initJoint]
  · intro D _ hD; simp [ftVec_initJoint, hD]
  · intro h; exact (h (mem_univ _)).elim

/-- Lift a stage operator `applyStage` to `Joint`. -/
noncomputable def jointStage (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
    (v : Joint X₁ X₂ Y E → ℂ) : Joint X₁ X₂ Y E → ℂ :=
  fun p => applyStage p.2 m U (fun r => v (r, p.2)) p.1

/-- Lift a single unitary `U` on `Reg` to `Joint`. -/
noncomputable def jointUnitary (U : Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
    (v : Joint X₁ X₂ Y E → ℂ) : Joint X₁ X₂ Y E → ℂ :=
  fun p => U.1.mulVec (fun r => v (r, p.2)) p.1

/-- Lift a single query `queryVec` to `Joint`. -/
def jointQuery (v : Joint X₁ X₂ Y E → ℂ) : Joint X₁ X₂ Y E → ℂ :=
  fun p => queryVec p.2 (fun r => v (r, p.2)) p.1

/-- Lift a diagonal projection on `Reg` to `Joint`. -/
def jointProj {α : Type*} [DecidableEq α] (f : Reg X₁ X₂ Y E → α) (a : α)
    (v : Joint X₁ X₂ Y E → ℂ) : Joint X₁ X₂ Y E → ℂ :=
  fun p => if f p.1 = a then v p else 0

lemma cInner_jointStage (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
    (u v : Joint X₁ X₂ Y E → ℂ) :
    cInner (jointStage m U u) (jointStage m U v) = cInner u v := by
  unfold cInner
  conv_lhs => rw [Fintype.sum_prod_type_right]
  conv_rhs => rw [Fintype.sum_prod_type_right]
  refine sum_congr rfl fun H _ =>
    cInner_applyStage H m U (fun r => u (r, H)) (fun r => v (r, H))

lemma normSq_jointStage (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
    (u : Joint X₁ X₂ Y E → ℂ) :
    normSq (jointStage m U u) = normSq u := by
  rw [← cInner_self_re, cInner_jointStage, cInner_self_re]

omit [DecidableEq Y] [AddCommGroup Y] [DecidableEq E] in
lemma sum_cInner_jointProj {α : Type*} [Fintype α] [DecidableEq α] (f : Reg X₁ X₂ Y E → α)
    (u v : Joint X₁ X₂ Y E → ℂ) :
    ∑ a : α, cInner (jointProj f a u) (jointProj f a v) = cInner u v := by
  simp only [cInner, jointProj]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_eq_single (f p.1)]
  · simp
  · intro a _ hne; simp [Ne.symm hne]
  · intro h; exact (h (mem_univ _)).elim

omit [DecidableEq Y] [AddCommGroup Y] [DecidableEq E] in
lemma sum_normSq_jointProj {α : Type*} [Fintype α] [DecidableEq α] (f : Reg X₁ X₂ Y E → α)
    (u : Joint X₁ X₂ Y E → ℂ) :
    ∑ a : α, normSq (jointProj f a u) = normSq u := by
  have h := congrArg Complex.re (sum_cInner_jointProj f u u)
  simpa only [Complex.re_sum, cInner_self_re] using h

lemma ftVec_jointUnitary (U : Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
    (v : Joint X₁ X₂ Y E → ℂ) (r : Reg X₁ X₂ Y E) (D : FTbl X₁ X₂ Y) :
    ftVec (jointUnitary U v) (r, D) = U.1.mulVec (fun r' => ftVec v (r', D)) r := by
  simp only [ftVec, jointUnitary, mulVec, dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r' _ => sum_congr rfl fun H _ => by ring

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma ftVec_jointProj {α : Type*} [DecidableEq α] (f : Reg X₁ X₂ Y E → α) (a : α)
    (v : Joint X₁ X₂ Y E → ℂ) (r : Reg X₁ X₂ Y E) (D : FTbl X₁ X₂ Y) :
    ftVec (jointProj f a v) (r, D) = if f r = a then ftVec v (r, D) else 0 := by
  unfold ftVec jointProj
  by_cases h : f r = a <;> simp [h]

lemma suppLe_jointUnitary {k : ℕ} (U : Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
    {v : Joint X₁ X₂ Y E → ℂ} (hv : SuppLe k (ftVec v)) :
    SuppLe k (ftVec (jointUnitary U v)) := by
  intro r D hne
  rw [ftVec_jointUnitary] at hne
  by_contra hgt
  have hzero : ∀ r', ftVec v (r', D) = 0 := fun r' => by
    by_contra hne'
    exact hgt (hv r' D hne')
  exact hne (by simp [mulVec, dotProduct, hzero])

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma suppLe_jointProj {k : ℕ} {α : Type*} [DecidableEq α] (f : Reg X₁ X₂ Y E → α) (a : α)
    {v : Joint X₁ X₂ Y E → ℂ} (hv : SuppLe k (ftVec v)) :
    SuppLe k (ftVec (jointProj f a v)) := by
  intro r D hne
  rw [ftVec_jointProj] at hne
  split_ifs at hne with h
  · exact hv r D hne
  · exact absurd rfl hne

omit [Fintype E] [DecidableEq E] in
/-- **Support growth of one quantum query**: `jointQuery` increases Fourier support size by at
most `1`, because for every `z ≠ x` (the queried coordinate) the Fourier coefficients at `z`
must agree. -/
theorem suppLe_jointQuery {k : ℕ} {v : Joint X₁ X₂ Y E → ℂ} (hv : SuppLe k (ftVec v)) :
    SuppLe (k + 1) (ftVec (jointQuery v)) := by
  intro r D hne
  rcases r with ⟨⟨x, y⟩, e⟩
  have hexp : ftVec (jointQuery v) (((x, y), e), D) =
      ∑ D' : FTbl X₁ X₂ Y, ∑ H : X₁ × X₂ → Y,
        (∏ z : X₁ × X₂, fEntry (D z) (H z) * star (fEntry (D' z) (H z))) *
          ftVec v (((x, y - H x), e), D') := by
    have hinv := congrFun (iftVec_ftVec v)
    conv_lhs => unfold ftVec jointQuery queryVec; dsimp only
    trans ∑ H : X₁ × X₂ → Y, ∑ D' : FTbl X₁ X₂ Y,
        (∏ z : X₁ × X₂, fEntry (D z) (H z) * star (fEntry (D' z) (H z))) *
          ftVec v (((x, y - H x), e), D')
    · refine sum_congr rfl fun H _ => ?_
      rw [← hinv (((x, y - H x), e), H)]
      simp only [iftVec, mul_sum, prod_mul_distrib]
      refine sum_congr rfl fun D' _ => by ring
    · rw [sum_comm]
  rw [hexp] at hne
  obtain ⟨D', -, hD'ne⟩ := exists_ne_zero_of_sum_ne_zero hne
  have hagree : ∀ z₀ : X₁ × X₂, z₀ ≠ x → D z₀ = D' z₀ := by
    intro z₀ hz₀
    by_contra hdiff
    apply hD'ne
    let eSplit : (X₁ × X₂ → Y) ≃ Y × ({z : X₁ × X₂ // z ≠ z₀} → Y) :=
      { toFun := fun H => (H z₀, fun z => H z.1)
        invFun := fun p z => if hz : z = z₀ then p.1 else p.2 ⟨z, hz⟩
        left_inv := fun H => by funext z; by_cases hz : z = z₀ <;> simp [hz]
        right_inv := fun ⟨h₀, Hrest⟩ => by
          ext
          · simp
          · rename_i z; simp [z.2] }
    rw [← Equiv.sum_comp eSplit.symm, Fintype.sum_prod_type_right]
    refine sum_eq_zero fun Hrest _ => ?_
    have hconst : ∀ h₀ : Y, (eSplit.symm (h₀, Hrest)) x = Hrest ⟨x, Ne.symm hz₀⟩ := fun h₀ => by
      dsimp only [eSplit]; simp [Ne.symm hz₀]
    have hprod : ∀ h₀ : Y,
        ∏ z : X₁ × X₂,
          fEntry (D z) ((eSplit.symm (h₀, Hrest)) z) *
          star (fEntry (D' z) ((eSplit.symm (h₀, Hrest)) z)) =
        (fEntry (D z₀) h₀ * star (fEntry (D' z₀) h₀)) *
        ∏ z ∈ univ.erase z₀,
          fEntry (D z) ((eSplit.symm (h₀, Hrest)) z) *
          star (fEntry (D' z) ((eSplit.symm (h₀, Hrest)) z)) := by
      intro h₀
      rw [← mul_prod_erase univ _ (mem_univ z₀)]
      dsimp only [eSplit]; simp
    have hrest_indep : ∀ h₀ : Y,
        ∏ z ∈ univ.erase z₀,
          fEntry (D z) ((eSplit.symm (h₀, Hrest)) z) *
          star (fEntry (D' z) ((eSplit.symm (h₀, Hrest)) z)) =
        ∏ z ∈ univ.erase z₀,
          if hz : z = z₀ then 1 else
            fEntry (D z) (Hrest ⟨z, hz⟩) * star (fEntry (D' z) (Hrest ⟨z, hz⟩)) := by
      intro h₀
      refine prod_congr rfl fun z hz => ?_
      have hne_z : z ≠ z₀ := (mem_erase.mp hz).1
      dsimp only [eSplit]; simp [hne_z]
    have h1 : ∀ h₀ : Y,
        (∏ z : X₁ × X₂, fEntry (D z) ((eSplit.symm (h₀, Hrest)) z) *
          star (fEntry (D' z) ((eSplit.symm (h₀, Hrest)) z))) *
          ftVec v (((x, y - (eSplit.symm (h₀, Hrest)) x), e), D') =
        (fEntry (D z₀) h₀ * star (fEntry (D' z₀) h₀)) *
          ((∏ z ∈ univ.erase z₀,
            if hz : z = z₀ then 1 else
              fEntry (D z) (Hrest ⟨z, hz⟩) * star (fEntry (D' z) (Hrest ⟨z, hz⟩))) *
           ftVec v (((x, y - Hrest ⟨x, Ne.symm hz₀⟩), e), D')) := by
      intro h₀; rw [hprod, hrest_indep, hconst, mul_assoc]
    simp_rw [h1, ← sum_mul, sum_fourier_mul_conj, ite_eq_right hdiff, zero_mul]
  obtain ⟨H, -, hHne⟩ := exists_ne_zero_of_sum_ne_zero hD'ne
  have hv_ne : ftVec v (((x, y - H x), e), D') ≠ 0 := right_ne_zero_of_mul hHne
  have hk : suppCard D' ≤ k := hv _ D' hv_ne
  have hsub : (univ.filter fun z : X₁ × X₂ => D z ≠ 0) ⊆
      insert x (univ.filter fun z : X₁ × X₂ => D' z ≠ 0) := by
    intro z hz
    rw [mem_filter] at hz
    by_cases hzx : z = x
    · subst hzx; exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, by rw [← hagree z hzx]; exact hz.2⟩)
  calc suppCard D ≤ (insert x (univ.filter fun z : X₁ × X₂ => D' z ≠ 0)).card :=
        card_le_card hsub
    _ ≤ suppCard D' + 1 := card_insert_le _ _
    _ ≤ k + 1 := Nat.add_le_add_right hk 1

/-- An `m`-query stage `jointStage m U` increases Fourier support size by at most `m`. -/
theorem suppLe_jointStage :
    ∀ {k : ℕ} (m : ℕ) (U : Fin (m + 1) → Matrix.unitaryGroup (Reg X₁ X₂ Y E) ℂ)
      {v : Joint X₁ X₂ Y E → ℂ},
      SuppLe k (ftVec v) → SuppLe (k + m) (ftVec (jointStage m U v))
  | k, 0, U, v, hv => suppLe_jointUnitary (U 0) hv
  | k, m + 1, U, v, hv => by
      have hstep : jointStage (m + 1) U v =
          jointUnitary (U (Fin.last (m + 1)))
            (jointQuery (jointStage m (fun i => U i.castSucc) v)) := by
        funext ⟨r, H⟩; rfl
      rw [hstep, show k + (m + 1) = (k + m) + 1 by omega]
      exact suppLe_jointUnitary _ (suppLe_jointQuery (suppLe_jointStage m _ hv))

/-! ## Reprogramming channel in the Fourier basis -/

/-- The `χ`-th Fourier Kraus branch of reprogramming coordinate `z`:
`reproBranch z χ v (r, H) = ∑ h : Y, fEntry χ h * cellAmp Y * v (r, update H z h)`. -/
noncomputable def reproBranch (z : X₁ × X₂) (χ : Yhat Y) (v : Joint X₁ X₂ Y E → ℂ) :
    Joint X₁ X₂ Y E → ℂ :=
  fun p => ∑ h : Y, fEntry χ h * (cellAmp Y * v (p.1, Function.update p.2 z h))

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
/-- In the Fourier basis, `reproBranch z χ v` projects coordinate `z` onto `0` and reads the
old Fourier coefficient `χ` at `z`. -/
theorem ftVec_reproBranch (z : X₁ × X₂) (χ : Yhat Y) (v : Joint X₁ X₂ Y E → ℂ)
    (r : Reg X₁ X₂ Y E) (D : FTbl X₁ X₂ Y) :
    ftVec (reproBranch z χ v) (r, D) =
      if D z = 0 then ftVec v (r, Function.update D z χ) else 0 := by
  unfold ftVec reproBranch
  simp_rw [mul_sum]
  let e : ((X₁ × X₂ → Y) × Y) ≃ ((X₁ × X₂ → Y) × Y) :=
    { toFun := fun p => (Function.update p.1 z p.2, p.1 z)
      invFun := fun q => (Function.update q.1 z q.2, q.1 z)
      left_inv := fun ⟨H, h⟩ => by
        ext z'
        · by_cases hz : z' = z <;> simp [hz]
        · simp
      right_inv := fun ⟨H, h⟩ => by
        ext z'
        · by_cases hz : z' = z <;> simp [hz]
        · simp }
  let g : ((X₁ × X₂ → Y) × Y) → ℂ := fun p =>
    (∏ z' : X₁ × X₂, fEntry (D z') (p.1 z')) *
      (fEntry χ p.2 * (cellAmp Y * v (r, Function.update p.1 z p.2)))
  change ∑ H : X₁ × X₂ → Y, ∑ h : Y, g (H, h) = _
  rw [← Fintype.sum_prod_type g, ← Equiv.sum_comp e g, Fintype.sum_prod_type]
  dsimp only [g, e]
  have hterm : ∀ (H' : X₁ × X₂ → Y) (y' : Y),
      (∏ z' : X₁ × X₂, fEntry (D z') ((Function.update H' z y') z')) *
        (fEntry χ (H' z) * (cellAmp Y * v (r, Function.update (Function.update H' z y') z (H' z)))) =
      (fEntry (D z) y' * cellAmp Y) *
        ((∏ z' : X₁ × X₂, fEntry ((Function.update D z χ) z') (H' z')) * v (r, H')) := by
    intro H' y'
    have hupd : Function.update (Function.update H' z y') z (H' z) = H' := by
      funext z'; by_cases hz : z' = z <;> simp [hz]
    rw [hupd, ← mul_prod_erase univ _ (mem_univ z),
      ← mul_prod_erase univ (fun z' => fEntry ((Function.update D z χ) z') (H' z'))
        (mem_univ z)]
    have hrest :
        ∏ z' ∈ univ.erase z, fEntry (D z') ((Function.update H' z y') z') =
        ∏ z' ∈ univ.erase z, fEntry ((Function.update D z χ) z') (H' z') := by
      refine prod_congr rfl fun z' hz' => ?_
      have hne : z' ≠ z := (mem_erase.mp hz').1
      simp [hne]
    rw [hrest]
    simp only [Function.update_self]
    ring
  trans ∑ H' : X₁ × X₂ → Y, ∑ y' : Y,
      (fEntry (D z) y' * cellAmp Y) *
        ((∏ z' : X₁ × X₂, fEntry ((Function.update D z χ) z') (H' z')) * v (r, H'))
  · refine sum_congr rfl fun H' _ => sum_congr rfl fun y' _ => hterm H' y'
  · have hinner : ∀ H' : X₁ × X₂ → Y,
        ∑ y' : Y, (fEntry (D z) y' * cellAmp Y) *
          ((∏ z' : X₁ × X₂, fEntry ((Function.update D z χ) z') (H' z')) * v (r, H')) =
        (if D z = 0 then (1 : ℂ) else 0) *
          ((∏ z' : X₁ × X₂, fEntry ((Function.update D z χ) z') (H' z')) * v (r, H')) := by
      intro H'
      rw [← sum_mul, sum_fourier_mul_cellAmp]
    simp_rw [hinner]
    by_cases hDz : D z = 0 <;> simp [hDz]

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
/-- For `χ = 0`, `reproBranch z 0` is literally the Fourier projection `Π_z` (`D z = 0`). -/
theorem ftVec_reproBranch_zero (z : X₁ × X₂) (v : Joint X₁ X₂ Y E → ℂ)
    (r : Reg X₁ X₂ Y E) (D : FTbl X₁ X₂ Y) :
    ftVec (reproBranch z 0 v) (r, D) = if D z = 0 then ftVec v (r, D) else 0 := by
  rw [ftVec_reproBranch]
  by_cases hDz : D z = 0
  · simp only [hDz, ↓reduceIte]
    rw [← hDz, Function.update_eq_self]
  · simp [hDz]

omit [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma suppLe_reproBranch_zero {k : ℕ} (z : X₁ × X₂) {v : Joint X₁ X₂ Y E → ℂ}
    (hv : SuppLe k (ftVec v)) :
    SuppLe k (ftVec (reproBranch z 0 v)) := by
  intro r D hne
  rw [ftVec_reproBranch_zero] at hne
  split_ifs at hne with h
  · exact hv r D hne
  · exact absurd rfl hne

omit [DecidableEq E] in
lemma normSq_reproBranch_zero_le (z : X₁ × X₂) (v : Joint X₁ X₂ Y E → ℂ) :
    normSq (reproBranch z 0 v) ≤ normSq v := by
  rw [← normSq_ftVec, ← normSq_ftVec v]
  refine sum_le_sum fun p _ => ?_
  rw [ftVec_reproBranch_zero]
  split_ifs <;> simp

/-- A real functional `Q : (Reg → ℂ) → ℝ` satisfies the Fourier Parseval identity for
reprogramming (all Hermitian quadratic forms satisfy this). -/
def IsQuadForm (Q : (Reg X₁ X₂ Y E → ℂ) → ℝ) : Prop :=
  ∀ (f : Y → Reg X₁ X₂ Y E → ℂ),
    ∑ χ : Yhat Y, Q (fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * f h r)) =
      (Fintype.card Y : ℝ)⁻¹ * ∑ h : Y, Q (f h)

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] [Fintype E] [DecidableEq E] in
lemma isQuadForm_normSq_linear {ι : Type*} [Fintype ι]
    (L : (Reg X₁ X₂ Y E → ℂ) → (ι → ℂ))
    (hL_add : ∀ u v, L (fun r => u r + v r) = fun i => L u i + L v i)
    (hL_smul : ∀ (c : ℂ) u, L (fun r => c * u r) = fun i => c * L u i) :
    IsQuadForm (fun ψ => normSq (L ψ)) := by
  have hL_sum : ∀ (s : Finset Y) (g : Y → Reg X₁ X₂ Y E → ℂ),
      L (fun r => ∑ a ∈ s, g a r) = fun i => ∑ a ∈ s, L (g a) i := by
    intro s g
    induction s using Finset.induction_on with
    | empty =>
        have hz : L (fun _ => 0) = fun _ => 0 := by simpa using hL_smul 0 (fun _ => 0)
        simpa using hz
    | insert a s ha ih =>
        funext i
        have h1 : (fun r => ∑ x ∈ insert a s, g x r) = fun r => g a r + ∑ x ∈ s, g x r := by
          funext r; exact sum_insert ha
        rw [h1, hL_add, ih, sum_insert ha]
  intro f
  have hlin : ∀ χ : Yhat Y,
      L (fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * f h r)) =
        fun i => ∑ h : Y, (fEntry χ h * cellAmp Y) * L (f h) i := by
    intro χ
    have h1 : (fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * f h r)) =
        fun r => ∑ h : Y, (fEntry χ h * cellAmp Y) * f h r := by
      funext r; refine sum_congr rfl fun h _ => by ring
    rw [h1, hL_sum]
    funext i
    refine sum_congr rfl fun h _ => congrFun (hL_smul (fEntry χ h * cellAmp Y) (f h)) i
  have hcomplex :
      ((∑ χ : Yhat Y, normSq (L (fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * f h r))) : ℝ) : ℂ) =
      (((Fintype.card Y : ℝ)⁻¹ * ∑ h : Y, normSq (L (f h)) : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum, ← cInner_self, hlin, cInner]
    rw [sum_comm]
    trans ∑ i : ι, ∑ h₁ : Y, ∑ h₂ : Y,
        (∑ χ : Yhat Y, star (fEntry χ h₁) * fEntry χ h₂) *
        (cellAmp Y * cellAmp Y * (star (L (f h₁) i) * L (f h₂) i))
    · refine sum_congr rfl fun i _ => ?_
      simp_rw [star_sum, star_mul', star_cellAmp, sum_mul, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun h₁ _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun h₂ _ => ?_
      refine sum_congr rfl fun χ _ => by ring
    · simp_rw [sum_fourier_conj_mul]
      have hsum_i : ∀ i : ι,
          ∑ h₁ : Y, ∑ h₂ : Y,
            (if h₁ = h₂ then (1 : ℂ) else 0) *
            (cellAmp Y * cellAmp Y * (star (L (f h₁) i) * L (f h₂) i)) =
          (Fintype.card Y : ℂ)⁻¹ * ∑ h : Y, star (L (f h) i) * L (f h) i := by
        intro i
        rw [mul_sum]
        refine sum_congr rfl fun h₁ _ => ?_
        rw [sum_eq_single h₁]
        · simp [cellAmp_mul_self]
        · intro h₂ _ hne; simp [Ne.symm hne]
        · intro h; exact (h (mem_univ _)).elim
      simp_rw [hsum_i, ← mul_sum]
      rw [sum_comm]
  exact Complex.ofReal_injective hcomplex

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma isQuadForm_add {Q₁ Q₂ : (Reg X₁ X₂ Y E → ℂ) → ℝ}
    (h₁ : IsQuadForm Q₁) (h₂ : IsQuadForm Q₂) :
    IsQuadForm (fun ψ => Q₁ ψ + Q₂ ψ) := by
  intro f
  rw [sum_add_distrib, h₁ f, h₂ f, sum_add_distrib, mul_add]

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma isQuadForm_const_mul {Q : (Reg X₁ X₂ Y E → ℂ) → ℝ} (c : ℝ) (h : IsQuadForm Q) :
    IsQuadForm (fun ψ => c * Q ψ) := by
  intro f
  rw [← mul_sum, h f, ← mul_sum]
  ring

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [DecidableEq Y] [Fintype E] [DecidableEq E] in
lemma isQuadForm_sum {κ : Type*} (s : Finset κ) {Q : κ → (Reg X₁ X₂ Y E → ℂ) → ℝ}
    (h : ∀ a ∈ s, IsQuadForm (Q a)) :
    IsQuadForm (fun ψ => ∑ a ∈ s, Q a ψ) := by
  intro f
  rw [sum_comm]
  have h1 : ∑ a ∈ s, ∑ χ : Yhat Y, Q a (fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * f h r)) =
      ∑ a ∈ s, (Fintype.card Y : ℝ)⁻¹ * ∑ h : Y, Q a (f h) :=
    sum_congr rfl fun a ha => h a ha f
  rw [h1, ← mul_sum, sum_comm]

omit [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
  [Fintype E] [DecidableEq E] in
lemma isQuadForm_comp_linear {Q : (Reg X₁ X₂ Y E → ℂ) → ℝ} (hQ : IsQuadForm Q)
    (T : (Reg X₁ X₂ Y E → ℂ) → (Reg X₁ X₂ Y E → ℂ))
    (hT_add : ∀ u v, T (fun r => u r + v r) = fun r => T u r + T v r)
    (hT_smul : ∀ (c : ℂ) u, T (fun r => c * u r) = fun r => c * T u r) :
    IsQuadForm (fun ψ => Q (T ψ)) := by
  have hT_sum : ∀ (s : Finset Y) (g : Y → Reg X₁ X₂ Y E → ℂ),
      T (fun r => ∑ a ∈ s, g a r) = fun r => ∑ a ∈ s, T (g a) r := by
    intro s g
    induction s using Finset.induction_on with
    | empty =>
        have hz : T (fun _ => 0) = fun _ => 0 := by simpa using hT_smul 0 (fun _ => 0)
        simpa using hz
    | insert a s ha ih =>
        funext r
        have h1 : (fun r => ∑ x ∈ insert a s, g x r) = fun r => g a r + ∑ x ∈ s, g x r := by
          funext r; exact sum_insert ha
        rw [h1, hT_add, ih, sum_insert ha]
  intro f
  have hT_arg : ∀ χ : Yhat Y,
      T (fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * f h r)) =
        fun r => ∑ h : Y, fEntry χ h * (cellAmp Y * T (f h) r) := by
    intro χ
    rw [hT_sum]
    funext r
    refine sum_congr rfl fun h _ => ?_
    rw [hT_smul, hT_smul]
  simp_rw [hT_arg]
  exact hQ (fun h => T (f h))

/-- Every `reproProbFrom b out prog H` is a Hermitian quadratic form in `ψ`. -/
theorem isQuadForm_reproProbFrom (b out : Bool) :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ} (prog : ReproProg X₁ X₂ Y E R q) (H : X₁ × X₂ → Y),
      IsQuadForm (reproProbFrom b out prog H)
  | _, _, .done m stage accept, H => by
      let L : (Reg X₁ X₂ Y E → ℂ) → Reg X₁ X₂ Y E → ℂ :=
        fun ψ r => if accept r = out then applyStage H m stage ψ r else 0
      have hEq : reproProbFrom b out (.done m stage accept) H = fun ψ => normSq (L ψ) := by
        funext ψ
        simp only [reproProbFrom, normSq, L]
        refine sum_congr rfl fun r _ => by split_ifs <;> simp
      rw [hEq]
      exact isQuadForm_normSq_linear L
        (fun u v => by funext r; simp only [L, applyStage_add]; split_ifs <;> simp)
        (fun c u => by funext r; simp only [L, applyStage_smul]; split_ifs <;> simp)
  | _, _, .call m stage callX2 cont, H => by
      have hinner : IsQuadForm (fun ψ' =>
          ∑ x₂ : X₂,
            (reproProbFrom b out (cont x₂ none) H (projBy callX2 (x₂, false) ψ') +
             (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁,
               (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
                 reproProbFrom b out (cont x₂ (some x₁))
                   (if b then Function.update H (x₁, x₂) y' else H)
                   (projBy callX2 (x₂, true) ψ'))) := by
        refine isQuadForm_sum univ fun x₂ _ => isQuadForm_add ?_ ?_
        · exact isQuadForm_comp_linear (isQuadForm_reproProbFrom b out (cont x₂ none) H)
            (projBy callX2 (x₂, false)) (projBy_add _ _) (projBy_smul _ _)
        · refine isQuadForm_const_mul _ (isQuadForm_sum univ fun x₁ _ =>
            isQuadForm_const_mul _ (isQuadForm_sum univ fun y' _ => ?_))
          exact isQuadForm_comp_linear
            (isQuadForm_reproProbFrom b out (cont x₂ (some x₁)) _)
            (projBy callX2 (x₂, true)) (projBy_add _ _) (projBy_smul _ _)
      exact isQuadForm_comp_linear hinner (applyStage H m stage)
        (applyStage_add H m stage) (applyStage_smul H m stage)

/-- **Exact Parseval identity for `reproProbFrom` under the Fourier reprogramming branches**,
yielding monotonicity when keeping only the `χ = 0` (`Π_z`) branch. -/
theorem sum_reproProbFrom_reproBranch_zero_le (b out : Bool) {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) (z : X₁ × X₂) (v : Joint X₁ X₂ Y E → ℂ) :
    ∑ H : X₁ × X₂ → Y, reproProbFrom b out prog H (fun r => reproBranch z 0 v (r, H)) ≤
      (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y, ∑ H : X₁ × X₂ → Y,
        reproProbFrom b out prog (Function.update H z y') (fun r => v (r, H)) := by
  have hsum :
      ∑ χ : Yhat Y, ∑ H : X₁ × X₂ → Y,
        reproProbFrom b out prog H (fun r => reproBranch z χ v (r, H)) =
      (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y, ∑ H : X₁ × X₂ → Y,
        reproProbFrom b out prog (Function.update H z y') (fun r => v (r, H)) := by
    rw [sum_comm]
    have hH : ∀ H : X₁ × X₂ → Y,
        ∑ χ : Yhat Y, reproProbFrom b out prog H (fun r => reproBranch z χ v (r, H)) =
          (Fintype.card Y : ℝ)⁻¹ * ∑ h : Y,
            reproProbFrom b out prog H (fun r => v (r, Function.update H z h)) :=
      fun H => isQuadForm_reproProbFrom b out prog H (fun h r => v (r, Function.update H z h))
    simp_rw [hH, ← mul_sum]
    congr 1
    let e : ((X₁ × X₂ → Y) × Y) ≃ ((X₁ × X₂ → Y) × Y) :=
      { toFun := fun p => (Function.update p.1 z p.2, p.1 z)
        invFun := fun q => (Function.update q.1 z q.2, q.1 z)
        left_inv := fun ⟨H, h⟩ => by
          ext z'
          · by_cases hz : z' = z <;> simp [hz]
          · simp
        right_inv := fun ⟨H, h⟩ => by
          ext z'
          · by_cases hz : z' = z <;> simp [hz]
          · simp }
    let g : ((X₁ × X₂ → Y) × Y) → ℝ := fun p =>
      reproProbFrom b out prog p.1 (fun r => v (r, Function.update p.1 z p.2))
    change ∑ H : X₁ × X₂ → Y, ∑ h : Y, g (H, h) = _
    rw [← Fintype.sum_prod_type g, ← Equiv.sum_comp e g, Fintype.sum_prod_type, sum_comm]
    dsimp only [g, e]
    refine sum_congr rfl fun y' _ => sum_congr rfl fun H' _ => ?_
    have hupd : Function.update (Function.update H' z y') z (H' z) = H' := by
      funext z'; by_cases hz : z' = z <;> simp [hz]
    simp [hupd]
  rw [← hsum]
  exact single_le_sum
    (f := fun χ => ∑ H, reproProbFrom b out prog H (fun r => reproBranch z χ v (r, H)))
    (fun χ _ => sum_nonneg fun H _ => reproProbFrom_nonneg b out prog H _) (mem_univ (0 : Yhat Y))

/-! ## Single-step fidelity drop and multi-stage induction -/

omit [DecidableEq E] in
/-- **Single-step inner-product drop**: averaging `Π_{(x₁, x₂)}` (`reproBranch (x₁, x₂) 0`)
over uniform `x₁ ←$ X₁` drops `Re⟨u, v⟩` by at most `(k / |X₁|) √‖u‖² √‖v‖²` whenever both
`ftVec u` and `ftVec v` have Fourier support size at most `k`. -/
theorem re_cInner_sub_reproBranch_zero_le [Nonempty X₁] {k : ℕ} (x₂ : X₂)
    {u v : Joint X₁ X₂ Y E → ℂ} (hu : SuppLe k (ftVec u)) (hv : SuppLe k (ftVec v)) :
    (cInner u v).re -
      (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (cInner u (reproBranch (x₁, x₂) 0 v)).re ≤
      ((k : ℝ) / Fintype.card X₁) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
  have hX1pos : (0 : ℝ) < Fintype.card X₁ := Nat.cast_pos.mpr Fintype.card_pos
  have hX1ne : (Fintype.card X₁ : ℝ) ≠ 0 := hX1pos.ne'
  let uPerp (x₁ : X₁) : FJoint X₁ X₂ Y E → ℂ :=
    fun p => if p.2 (x₁, x₂) = 0 then 0 else ftVec u p
  let vPerp (x₁ : X₁) : FJoint X₁ X₂ Y E → ℂ :=
    fun p => if p.2 (x₁, x₂) = 0 then 0 else ftVec v p
  have hdiff : ∀ x₁ : X₁,
      (cInner u v).re - (cInner u (reproBranch (x₁, x₂) 0 v)).re =
        (cInner (uPerp x₁) (vPerp x₁)).re := by
    intro x₁
    rw [← cInner_ftVec u v, ← cInner_ftVec u (reproBranch (x₁, x₂) 0 v)]
    rw [← Complex.sub_re]
    congr 1
    simp only [cInner, ← sum_sub_distrib, uPerp, vPerp]
    refine sum_congr rfl fun p _ => ?_
    rcases p with ⟨r, D⟩
    rw [ftVec_reproBranch_zero]
    by_cases h0 : D (x₁, x₂) = 0 <;> simp [h0]
  have hsum_diff :
      (cInner u v).re -
        (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (cInner u (reproBranch (x₁, x₂) 0 v)).re =
      (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (cInner (uPerp x₁) (vPerp x₁)).re := by
    have hconst : (cInner u v).re = (Fintype.card X₁ : ℝ)⁻¹ * ∑ _x₁ : X₁, (cInner u v).re := by
      simp [sum_const, card_univ, nsmul_eq_mul]
    conv_lhs => rw [hconst]
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun x₁ _ => hdiff x₁
  have hsum_perp : ∀ {w : Joint X₁ X₂ Y E → ℂ} (hw : SuppLe k (ftVec w)),
      ∑ x₁ : X₁, normSq (fun p : FJoint X₁ X₂ Y E => if p.2 (x₁, x₂) = 0 then 0 else ftVec w p) ≤
        (k : ℝ) * normSq w := by
    intro w hw
    rw [← normSq_ftVec w]
    unfold normSq
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun p _ => ?_
    by_cases hwp : ftVec w p = 0
    · simp [hwp]
    · have hcard : (univ.filter fun x₁ : X₁ => p.2 (x₁, x₂) ≠ 0).card ≤ k := by
        have hinj : (univ.filter fun x₁ : X₁ => p.2 (x₁, x₂) ≠ 0).card ≤ suppCard p.2 := by
          unfold suppCard
          have hsub : (univ.filter fun x₁ : X₁ => p.2 (x₁, x₂) ≠ 0).image (fun x₁ => (x₁, x₂)) ⊆
              univ.filter fun z : X₁ × X₂ => p.2 z ≠ 0 := by
            intro z hz
            obtain ⟨x₁, hx₁, rfl⟩ := mem_image.mp hz
            exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx₁).2⟩
          calc (univ.filter fun x₁ : X₁ => p.2 (x₁, x₂) ≠ 0).card
              = ((univ.filter fun x₁ : X₁ => p.2 (x₁, x₂) ≠ 0).image (fun x₁ => (x₁, x₂))).card :=
                (card_image_of_injective _ fun a b h => (Prod.mk.inj h).1).symm
            _ ≤ (univ.filter fun z : X₁ × X₂ => p.2 z ≠ 0).card := card_le_card hsub
        exact hinj.trans (hw p.1 p.2 hwp)
      have hterm : ∑ x₁ : X₁, ‖if p.2 (x₁, x₂) = 0 then (0 : ℂ) else ftVec w p‖ ^ 2 =
          ((univ.filter fun x₁ : X₁ => p.2 (x₁, x₂) ≠ 0).card : ℝ) * ‖ftVec w p‖ ^ 2 := by
        have h1 : ∀ x₁ : X₁, ‖if p.2 (x₁, x₂) = 0 then (0 : ℂ) else ftVec w p‖ ^ 2 =
            if p.2 (x₁, x₂) ≠ 0 then ‖ftVec w p‖ ^ 2 else 0 := fun x₁ => by
          by_cases h : p.2 (x₁, x₂) = 0 <;> simp [h]
        simp_rw [h1, ← sum_filter, sum_const, nsmul_eq_mul]
      rw [hterm]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
  rw [hsum_diff, div_eq_inv_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hX1pos.le)
  calc ∑ x₁ : X₁, (cInner (uPerp x₁) (vPerp x₁)).re
      ≤ ∑ x₁ : X₁, Real.sqrt (normSq (uPerp x₁)) * Real.sqrt (normSq (vPerp x₁)) :=
        sum_le_sum fun x₁ _ => re_cInner_le_sqrt_mul_sqrt _ _
    _ ≤ Real.sqrt (∑ x₁ : X₁, normSq (uPerp x₁)) * Real.sqrt (∑ x₁ : X₁, normSq (vPerp x₁)) :=
        sum_sqrt_mul_sqrt_le univ (fun _ _ => normSq_nonneg _) (fun _ _ => normSq_nonneg _)
    _ ≤ Real.sqrt ((k : ℝ) * normSq u) * Real.sqrt ((k : ℝ) * normSq v) :=
        mul_le_mul (Real.sqrt_le_sqrt (hsum_perp hu)) (Real.sqrt_le_sqrt (hsum_perp hv))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (k : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_mul (Nat.cast_nonneg k)]
        have hk : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg k)
        calc Real.sqrt k * Real.sqrt (normSq u) * (Real.sqrt k * Real.sqrt (normSq v))
            = (Real.sqrt k * Real.sqrt k) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by ring
          _ = (k : ℝ) * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) := by rw [hk]

/-- **Main multi-stage fidelity induction**: for any `ReproProg`, initial Fourier support `≤ k`,
and states `u, v : Joint → ℂ`, the real inner product `Re⟨u, v⟩` minus
`(∑_j (k + q̂_j)) / |X₁| · √‖u‖² √‖v‖²` is bounded above by the Bernoulli fidelity between
`Repro₀` on `u` and `Repro₁` on `v`. -/
theorem repro_fidelity_from [Nonempty X₁] :
    ∀ {R : ℕ} {q : Fin (R + 1) → ℕ} (prog : ReproProg X₁ X₂ Y E R q)
      (k : ℕ) {u v : Joint X₁ X₂ Y E → ℂ},
      SuppLe k (ftVec u) → SuppLe k (ftVec v) →
      (cInner u v).re -
        ((∑ j : Fin R, ((k + qhat q j : ℕ) : ℝ)) / Fintype.card X₁) *
          (Real.sqrt (normSq u) * Real.sqrt (normSq v)) ≤
      Real.sqrt (∑ H : X₁ × X₂ → Y, reproProbFrom false true prog H (fun r => u (r, H))) *
        Real.sqrt (∑ H : X₁ × X₂ → Y, reproProbFrom true true prog H (fun r => v (r, H))) +
      Real.sqrt (∑ H : X₁ × X₂ → Y, reproProbFrom false false prog H (fun r => u (r, H))) *
        Real.sqrt (∑ H : X₁ × X₂ → Y, reproProbFrom true false prog H (fun r => v (r, H)))
  | _, _, .done m stage accept, k, u, v, _, _ => by
      simp only [Finset.univ_eq_empty, sum_empty, zero_div, zero_mul, sub_zero]
      let u' := jointStage m stage u
      let v' := jointStage m stage v
      have hprob : ∀ (b out : Bool) (w : Joint X₁ X₂ Y E → ℂ),
          ∑ H : X₁ × X₂ → Y, reproProbFrom b out (.done m stage accept) H (fun r => w (r, H)) =
            normSq (jointProj accept out (jointStage m stage w)) := by
        intro b out w
        unfold reproProbFrom normSq jointProj jointStage
        rw [Fintype.sum_prod_type_right]
        refine sum_congr rfl fun H _ => sum_congr rfl fun r _ => by split_ifs <;> simp
      rw [hprob false true u, hprob true true v, hprob false false u, hprob true false v]
      have hinner : (cInner u v).re =
          (cInner (jointProj accept true u') (jointProj accept true v')).re +
          (cInner (jointProj accept false u') (jointProj accept false v')).re := by
        rw [← cInner_jointStage m stage u v]
        have hsp := sum_cInner_jointProj accept u' v'
        rw [Fintype.sum_bool] at hsp
        simpa only [Complex.add_re] using (congrArg Complex.re hsp).symm
      rw [hinner]
      exact add_le_add (re_cInner_le_sqrt_mul_sqrt _ _) (re_cInner_le_sqrt_mul_sqrt _ _)
  | _, _, .call (R := R') (q := q') m stage callX2 cont, k, u, v, hu, hv => by
      have hX1pos : (0 : ℝ) < Fintype.card X₁ := Nat.cast_pos.mpr Fintype.card_pos
      have hYpos : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
      let u₁ := jointStage m stage u
      let v₁ := jointStage m stage v
      have hu₁ : SuppLe (k + m) (ftVec u₁) := suppLe_jointStage m stage hu
      have hv₁ : SuppLe (k + m) (ftVec v₁) := suppLe_jointStage m stage hv
      have hnu : normSq u₁ = normSq u := normSq_jointStage m stage u
      have hnv : normSq v₁ = normSq v := normSq_jointStage m stage v
      let uF (x₂ : X₂) := jointProj callX2 (x₂, false) u₁
      let vF (x₂ : X₂) := jointProj callX2 (x₂, false) v₁
      let uT (x₂ : X₂) := jointProj callX2 (x₂, true) u₁
      let vT (x₂ : X₂) := jointProj callX2 (x₂, true) v₁
      let Srem : ℝ := (∑ j : Fin R', (((k + m) + qhat q' j : ℕ) : ℝ)) / Fintype.card X₁
      have hSrem_nonneg : 0 ≤ Srem := by positivity
      -- Inner product splits across `(x₂, false)` and `(x₂, true)`
      have hsplit_inner : (cInner u v).re =
          ∑ x₂ : X₂, ((cInner (uF x₂) (vF x₂)).re + (cInner (uT x₂) (vT x₂)).re) := by
        rw [← cInner_jointStage m stage u v]
        have hsp := sum_cInner_jointProj callX2 u₁ v₁
        rw [Fintype.sum_prod_type] at hsp
        simp only [Fintype.sum_bool, add_comm] at hsp
        simpa only [Complex.re_sum, Complex.add_re] using (congrArg Complex.re hsp).symm
      -- Norm split across `(x₂, false)` and `(x₂, true)`
      have hsplit_u : ∑ x₂ : X₂, (normSq (uF x₂) + normSq (uT x₂)) = normSq u := by
        have hsp := sum_normSq_jointProj callX2 u₁
        rw [Fintype.sum_prod_type] at hsp
        simp only [Fintype.sum_bool, add_comm] at hsp
        rwa [hnu] at hsp
      have hsplit_v : ∑ x₂ : X₂, (normSq (vF x₂) + normSq (vT x₂)) = normSq v := by
        have hsp := sum_normSq_jointProj callX2 v₁
        rw [Fintype.sum_prod_type] at hsp
        simp only [Fintype.sum_bool, add_comm] at hsp
        rwa [hnv] at hsp
      -- Helper shorthand for the 4 probability sums on each `(x₂, false)` / `(x₂, true)` slice
      let p0F (out : Bool) (x₂ : X₂) : ℝ :=
        ∑ H : X₁ × X₂ → Y, reproProbFrom false out (cont x₂ none) H (fun r => uF x₂ (r, H))
      let p1F (out : Bool) (x₂ : X₂) : ℝ :=
        ∑ H : X₁ × X₂ → Y, reproProbFrom true out (cont x₂ none) H (fun r => vF x₂ (r, H))
      let p0T (out : Bool) (x₂ : X₂) : ℝ :=
        (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁,
          ∑ H : X₁ × X₂ → Y, reproProbFrom false out (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))
      let p1T (out : Bool) (x₂ : X₂) : ℝ :=
        (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (Fintype.card Y : ℝ)⁻¹ * ∑ y' : Y,
          ∑ H : X₁ × X₂ → Y, reproProbFrom true out (cont x₂ (some x₁))
            (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H))
      -- Bound for the skipped `(x₂, false)` branch (no reprogramming at this step!)
      have hF_bound : ∀ x₂ : X₂,
          (cInner (uF x₂) (vF x₂)).re - Srem * (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂))) ≤
            Real.sqrt (p0F true x₂) * Real.sqrt (p1F true x₂) +
            Real.sqrt (p0F false x₂) * Real.sqrt (p1F false x₂) := fun x₂ =>
        repro_fidelity_from (cont x₂ none) (k + m)
          (suppLe_jointProj _ _ hu₁) (suppLe_jointProj _ _ hv₁)
      -- Bound for the reprogrammed `(x₂, true)` branch
      have hT_bound : ∀ x₂ : X₂,
          (cInner (uT x₂) (vT x₂)).re -
            (((k + m : ℕ) : ℝ) / Fintype.card X₁ + Srem) *
              (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) ≤
            Real.sqrt (p0T true x₂) * Real.sqrt (p1T true x₂) +
            Real.sqrt (p0T false x₂) * Real.sqrt (p1T false x₂) := by
        intro x₂
        have hdrop := re_cInner_sub_reproBranch_zero_le x₂
          (suppLe_jointProj callX2 (x₂, true) hu₁) (suppLe_jointProj callX2 (x₂, true) hv₁)
        have hstep_x1 : ∀ x₁ : X₁,
            (cInner (uT x₂) (reproBranch (x₁, x₂) 0 (vT x₂))).re -
              Srem * (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) ≤
            Real.sqrt (∑ H, reproProbFrom false true (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))) *
              Real.sqrt ((Fintype.card Y : ℝ)⁻¹ * ∑ y', ∑ H, reproProbFrom true true (cont x₂ (some x₁))
                (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H))) +
            Real.sqrt (∑ H, reproProbFrom false false (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))) *
              Real.sqrt ((Fintype.card Y : ℝ)⁻¹ * ∑ y', ∑ H, reproProbFrom true false (cont x₂ (some x₁))
                (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H))) := by
          intro x₁
          have hih := repro_fidelity_from (cont x₂ (some x₁)) (k + m)
            (suppLe_jointProj callX2 (x₂, true) hu₁)
            (suppLe_reproBranch_zero (x₁, x₂) (suppLe_jointProj callX2 (x₂, true) hv₁))
          have hnv' : Real.sqrt (normSq (reproBranch (x₁, x₂) 0 (vT x₂))) ≤ Real.sqrt (normSq (vT x₂)) :=
            Real.sqrt_le_sqrt (normSq_reproBranch_zero_le (x₁, x₂) (vT x₂))
          have hmonoT := Real.sqrt_le_sqrt (sum_reproProbFrom_reproBranch_zero_le true true
            (cont x₂ (some x₁)) (x₁, x₂) (vT x₂))
          have hmonoF := Real.sqrt_le_sqrt (sum_reproProbFrom_reproBranch_zero_le true false
            (cont x₂ (some x₁)) (x₁, x₂) (vT x₂))
          have hSmono : Srem * (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (reproBranch (x₁, x₂) 0 (vT x₂)))) ≤
              Srem * (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hnv' (Real.sqrt_nonneg _)) hSrem_nonneg
          have hrhs :
              Real.sqrt (∑ H, reproProbFrom false true (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))) *
                Real.sqrt (∑ H, reproProbFrom true true (cont x₂ (some x₁)) H (fun r => reproBranch (x₁, x₂) 0 (vT x₂) (r, H))) +
              Real.sqrt (∑ H, reproProbFrom false false (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))) *
                Real.sqrt (∑ H, reproProbFrom true false (cont x₂ (some x₁)) H (fun r => reproBranch (x₁, x₂) 0 (vT x₂) (r, H))) ≤
              Real.sqrt (∑ H, reproProbFrom false true (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))) *
                Real.sqrt ((Fintype.card Y : ℝ)⁻¹ * ∑ y', ∑ H, reproProbFrom true true (cont x₂ (some x₁))
                  (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H))) +
              Real.sqrt (∑ H, reproProbFrom false false (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H))) *
                Real.sqrt ((Fintype.card Y : ℝ)⁻¹ * ∑ y', ∑ H, reproProbFrom true false (cont x₂ (some x₁))
                  (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H))) :=
            add_le_add (mul_le_mul_of_nonneg_left hmonoT (Real.sqrt_nonneg _))
              (mul_le_mul_of_nonneg_left hmonoF (Real.sqrt_nonneg _))
          linarith
        -- Average `hstep_x1` over `x₁ : X₁` and apply Cauchy-Schwarz over `x₁`
        have havg :
            (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (cInner (uT x₂) (reproBranch (x₁, x₂) 0 (vT x₂))).re -
              Srem * (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) ≤
            Real.sqrt (p0T true x₂) * Real.sqrt (p1T true x₂) +
            Real.sqrt (p0T false x₂) * Real.sqrt (p1T false x₂) := by
          have h1 := sum_le_sum fun x₁ (_ : x₁ ∈ univ) => hstep_x1 x₁
          rw [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at h1
          have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hX1pos.le)
          rw [mul_sub, mul_add, ← mul_assoc, inv_mul_cancel₀ hX1pos.ne', one_mul] at h2
          have hcsT := sum_sqrt_mul_sqrt_le univ
            (f := fun x₁ => ∑ H, reproProbFrom false true (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H)))
            (g := fun x₁ => (Fintype.card Y : ℝ)⁻¹ * ∑ y', ∑ H, reproProbFrom true true (cont x₂ (some x₁))
              (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H)))
            (fun _ _ => sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _)
            (fun _ _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
              reproProbFrom_nonneg _ _ _ _ _))
          have hcsF := sum_sqrt_mul_sqrt_le univ
            (f := fun x₁ => ∑ H, reproProbFrom false false (cont x₂ (some x₁)) H (fun r => uT x₂ (r, H)))
            (g := fun x₁ => (Fintype.card Y : ℝ)⁻¹ * ∑ y', ∑ H, reproProbFrom true false (cont x₂ (some x₁))
              (Function.update H (x₁, x₂) y') (fun r => vT x₂ (r, H)))
            (fun _ _ => sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _)
            (fun _ _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
              reproProbFrom_nonneg _ _ _ _ _))
          have hscale : ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
              (Fintype.card X₁ : ℝ)⁻¹ * (Real.sqrt A * Real.sqrt B) =
                Real.sqrt ((Fintype.card X₁ : ℝ)⁻¹ * A) * Real.sqrt ((Fintype.card X₁ : ℝ)⁻¹ * B) := by
            intro A B _ _
            rw [Real.sqrt_mul (inv_nonneg.mpr hX1pos.le), Real.sqrt_mul (inv_nonneg.mpr hX1pos.le)]
            have hsq : Real.sqrt (Fintype.card X₁ : ℝ)⁻¹ * Real.sqrt (Fintype.card X₁ : ℝ)⁻¹ =
                (Fintype.card X₁ : ℝ)⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr hX1pos.le)
            calc (Fintype.card X₁ : ℝ)⁻¹ * (Real.sqrt A * Real.sqrt B)
                = (Real.sqrt (Fintype.card X₁ : ℝ)⁻¹ * Real.sqrt (Fintype.card X₁ : ℝ)⁻¹) *
                    (Real.sqrt A * Real.sqrt B) := by rw [hsq]
              _ = Real.sqrt (Fintype.card X₁ : ℝ)⁻¹ * Real.sqrt A *
                    (Real.sqrt (Fintype.card X₁ : ℝ)⁻¹ * Real.sqrt B) := by ring
          have h2T := mul_le_mul_of_nonneg_left hcsT (inv_nonneg.mpr hX1pos.le)
          have h2F := mul_le_mul_of_nonneg_left hcsF (inv_nonneg.mpr hX1pos.le)
          rw [hscale _ _ (sum_nonneg fun _ _ => sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _)
            (sum_nonneg fun _ _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ =>
              sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _))] at h2T
          rw [hscale _ _ (sum_nonneg fun _ _ => sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _)
            (sum_nonneg fun _ _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ =>
              sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _))] at h2F
          exact h2.trans (add_le_add h2T h2F)
        have hdrop' : (cInner (uT x₂) (vT x₂)).re -
            (Fintype.card X₁ : ℝ)⁻¹ * ∑ x₁ : X₁, (cInner (uT x₂) (reproBranch (x₁, x₂) 0 (vT x₂))).re ≤
            (((k + m : ℕ) : ℝ) / Fintype.card X₁) *
              (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) := hdrop
        linarith
      -- Combine `(x₂, false)` and `(x₂, true)` summed over `x₂ : X₂`
      let coeff : ℝ := ((k + m : ℕ) : ℝ) / Fintype.card X₁ + Srem
      have hcoeff_eq : coeff =
          (∑ j : Fin (R' + 1), ((k + qhat (Fin.cons m q') j : ℕ) : ℝ)) / Fintype.card X₁ := by
        simp only [coeff, Srem, sum_qhat_cons, add_div]
      have hF_pad : ∀ x₂ : X₂,
          (cInner (uF x₂) (vF x₂)).re -
            coeff * (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂))) ≤
          Real.sqrt (p0F true x₂) * Real.sqrt (p1F true x₂) +
          Real.sqrt (p0F false x₂) * Real.sqrt (p1F false x₂) := by
        intro x₂
        have hkm : 0 ≤ (((k + m : ℕ) : ℝ) / Fintype.card X₁) *
            (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂))) := by positivity
        have := hF_bound x₂
        simp only [coeff]
        linarith
      -- Sum `hF_pad` + `hT_bound` over `x₂ : X₂`
      have hsum_all := sum_le_sum fun x₂ (_ : x₂ ∈ univ) => add_le_add (hF_pad x₂) (hT_bound x₂)
      -- Bound the subtracted norm sum by `coeff * √‖u‖² * √‖v‖²` via Cauchy-Schwarz over `X₂ × Bool`
      have hnorm_cs :
          ∑ x₂ : X₂, (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂)) +
            Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) ≤
          Real.sqrt (normSq u) * Real.sqrt (normSq v) := by
        have hcs := sum_sqrt_mul_sqrt_le (univ : Finset (X₂ × Bool))
          (f := fun p => if p.2 then normSq (uT p.1) else normSq (uF p.1))
          (g := fun p => if p.2 then normSq (vT p.1) else normSq (vF p.1))
          (fun p _ => by split_ifs <;> exact normSq_nonneg _)
          (fun p _ => by split_ifs <;> exact normSq_nonneg _)
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs
        simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at hcs
        simp_rw [add_comm (normSq (uT _)), add_comm (normSq (vT _)),
          add_comm (Real.sqrt (normSq (uT _)) * Real.sqrt (normSq (vT _)))] at hcs
        rwa [hsplit_u, hsplit_v] at hcs
      -- Bound the RHS sums by `√(P0 out) * √(P1 out)` via Cauchy-Schwarz over `X₂ × Bool`
      have hrhs_cs : ∀ out : Bool,
          ∑ x₂ : X₂, (Real.sqrt (p0F out x₂) * Real.sqrt (p1F out x₂) +
            Real.sqrt (p0T out x₂) * Real.sqrt (p1T out x₂)) ≤
          Real.sqrt (∑ x₂ : X₂, (p0F out x₂ + p0T out x₂)) *
            Real.sqrt (∑ x₂ : X₂, (p1F out x₂ + p1T out x₂)) := by
        intro out
        have hcs := sum_sqrt_mul_sqrt_le (univ : Finset (X₂ × Bool))
          (f := fun p => if p.2 then p0T out p.1 else p0F out p.1)
          (g := fun p => if p.2 then p1T out p.1 else p1F out p.1)
          (fun p _ => by
            split_ifs
            · exact mul_nonneg (by positivity) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
                reproProbFrom_nonneg _ _ _ _ _)
            · exact sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _)
          (fun p _ => by
            split_ifs
            · exact mul_nonneg (by positivity) (sum_nonneg fun _ _ => mul_nonneg (by positivity)
                (sum_nonneg fun _ _ => sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _))
            · exact sum_nonneg fun _ _ => reproProbFrom_nonneg _ _ _ _ _)
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs
        simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at hcs
        simp_rw [add_comm (p0T out _), add_comm (p1T out _),
          add_comm (Real.sqrt (p0T out _) * Real.sqrt (p1T out _))] at hcs
        exact hcs
      -- Identify `∑ x₂, (p0F out x₂ + p0T out x₂)` and `∑ x₂, (p1F out x₂ + p1T out x₂)` with `reproProbFrom`
      have hp0_eq' : ∀ out : Bool,
          ∑ x₂ : X₂, (p0F out x₂ + p0T out x₂) =
            ∑ H : X₁ × X₂ → Y, reproProbFrom false out (.call m stage callX2 cont) H (fun r => u (r, H)) := by
        intro out
        simp only [reproProbFrom, Bool.false_eq_true, ↓reduceIte, p0F, p0T, uF, uT, u₁,
          jointProj, jointStage]
        rw [sum_comm]
        refine sum_congr rfl fun x₂ _ => ?_
        rw [sum_add_distrib]
        congr 1
        simp only [sum_const, card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hYpos.ne', ← mul_sum]
        congr 1
        rw [sum_comm]
        rfl
      have hp1_eq : ∀ out : Bool,
          ∑ x₂ : X₂, (p1F out x₂ + p1T out x₂) =
            ∑ H : X₁ × X₂ → Y, reproProbFrom true out (.call m stage callX2 cont) H (fun r => v (r, H)) := by
        intro out
        simp only [reproProbFrom, ↓reduceIte, p1F, p1T, vF, vT, v₁, jointProj, jointStage]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun x₂ _ => ?_
        rw [sum_add_distrib]
        congr 1
        conv_rhs => rw [← mul_sum]
        congr 1
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun x₁ _ => ?_
        conv_rhs => rw [← mul_sum]
        congr 1
        conv_rhs => rw [sum_comm]
        rfl
      -- Assemble all pieces
      have hLHS :
          (cInner u v).re - coeff * (Real.sqrt (normSq u) * Real.sqrt (normSq v)) ≤
          ∑ x₂ : X₂,
            (((cInner (uF x₂) (vF x₂)).re - coeff * (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂)))) +
             ((cInner (uT x₂) (vT x₂)).re - coeff * (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))))) := by
        have hcoeff_nonneg : 0 ≤ coeff := by positivity
        have h1 :
            ∑ x₂ : X₂,
              (((cInner (uF x₂) (vF x₂)).re - coeff * (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂)))) +
               ((cInner (uT x₂) (vT x₂)).re - coeff * (Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))))) =
            (cInner u v).re - coeff * ∑ x₂ : X₂,
              (Real.sqrt (normSq (uF x₂)) * Real.sqrt (normSq (vF x₂)) +
               Real.sqrt (normSq (uT x₂)) * Real.sqrt (normSq (vT x₂))) := by
          rw [hsplit_inner, mul_sum, ← sum_sub_distrib]
          refine sum_congr rfl fun x₂ _ => by ring
        rw [h1]
        have := mul_le_mul_of_nonneg_left hnorm_cs hcoeff_nonneg
        linarith
      have hRHS_rearr :
          ∑ x₂ : X₂,
            ((Real.sqrt (p0F true x₂) * Real.sqrt (p1F true x₂) +
              Real.sqrt (p0F false x₂) * Real.sqrt (p1F false x₂)) +
             (Real.sqrt (p0T true x₂) * Real.sqrt (p1T true x₂) +
              Real.sqrt (p0T false x₂) * Real.sqrt (p1T false x₂))) =
          (∑ x₂ : X₂, (Real.sqrt (p0F true x₂) * Real.sqrt (p1F true x₂) +
            Real.sqrt (p0T true x₂) * Real.sqrt (p1T true x₂))) +
          (∑ x₂ : X₂, (Real.sqrt (p0F false x₂) * Real.sqrt (p1F false x₂) +
            Real.sqrt (p0T false x₂) * Real.sqrt (p1T false x₂))) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun x₂ _ => by ring
      rw [← hcoeff_eq, ← hp0_eq' true, ← hp1_eq true, ← hp0_eq' false, ← hp1_eq false]
      calc (cInner u v).re - coeff * (Real.sqrt (normSq u) * Real.sqrt (normSq v))
          ≤ _ := hLHS
        _ ≤ _ := hsum_all
        _ = _ := hRHS_rearr
        _ ≤ _ := add_le_add (hrhs_cs true) (hrhs_cs false)

end Fourier

/-! ## Main QROM Theorems: Lemmas C.3, C.1, C.5 and Corollaries C.1, C.3 -/

/-- **Bernoulli fidelity bound for `Repro₀` vs `Repro₁`**:
`1 − (∑_j q̂_j) / |X₁| ≤ √p₀ √p₁ + √(1 − p₀) √(1 − p₁)`. -/
theorem repro_fidelity [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    1 - (∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁ ≤
      Real.sqrt (reproProb false true prog init) * Real.sqrt (reproProb true true prog init) +
      Real.sqrt (1 - reproProb false true prog init) * Real.sqrt (1 - reproProb true true prog init) := by
  have hfid := repro_fidelity_from prog 0
    (suppLe_ftVec_initJoint init) (suppLe_ftVec_initJoint init)
  have hnorm : normSq (initJoint init) = 1 := by rw [normSq_initJoint, hinit]
  have hinner : (cInner (initJoint init) (initJoint init)).re = 1 := by
    rw [cInner_self_re, hnorm]
  have hprob : ∀ (b out : Bool),
      ∑ H : X₁ × X₂ → Y, reproProbFrom b out prog H (fun r => initJoint init (r, H)) =
        reproProb b out prog init := by
    intro b out
    have hscale : ∀ (H : X₁ × X₂ → Y) (c : ℂ) (ψ : Reg X₁ X₂ Y E → ℂ),
        reproProbFrom b out prog H (fun r => c * ψ r) = ‖c‖ ^ 2 * reproProbFrom b out prog H ψ := by
      intro H c ψ
      -- Derived directly from `reproProbFrom` scaling by induction on `prog`
      clear hfid hnorm hinner hinit
      induction prog generalizing H ψ with
      | done m stage accept =>
          simp only [reproProbFrom, applyStage_smul, mul_sum]
          refine sum_congr rfl fun r _ => by split_ifs <;> simp [mul_pow]
      | call m stage callX2 cont ih =>
          simp only [reproProbFrom, applyStage_smul, projBy_smul]
          rw [mul_sum]
          refine sum_congr rfl fun x₂ _ => ?_
          rw [mul_add, ih x₂ none H]
          congr 1
          rw [mul_left_comm]
          congr 1
          rw [mul_sum]
          refine sum_congr rfl fun x₁ _ => ?_
          rw [mul_left_comm]
          congr 1
          rw [mul_sum]
          refine sum_congr rfl fun y' _ => ih x₂ (some x₁) _ _
    have hnorm_amp : ‖cellAmp Y ^ Fintype.card (X₁ × X₂)‖ ^ 2 =
        (Fintype.card (X₁ × X₂ → Y) : ℝ)⁻¹ := by
      have hamp_sq : ‖cellAmp Y‖ ^ 2 = (Fintype.card Y : ℝ)⁻¹ := by
        have h1 : ((‖cellAmp Y‖ ^ 2 : ℝ) : ℂ) = (((Fintype.card Y : ℝ)⁻¹ : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, ← Complex.conj_mul', ← RCLike.star_def, star_cellAmp,
            cellAmp_mul_self]
          push_cast
          rfl
        exact Complex.ofReal_injective h1
      rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hamp_sq, inv_pow, Fintype.card_fun, Nat.cast_pow]
    unfold reproProb initJoint
    simp_rw [hscale, hnorm_amp, ← mul_sum]
  have hf0 : reproProb false false prog init = 1 - reproProb false true prog init := by
    linarith [reproProb_true_add_false false prog hinit]
  have hf1 : reproProb true false prog init = 1 - reproProb true true prog init := by
    linarith [reproProb_true_add_false true prog hinit]
  simpa only [hinner, hnorm, Real.sqrt_one, mul_one, zero_add, hprob, hf0, hf1] using hfid

/-- **Sharp Lemma C.3 (`e = 1/2` and `e = 1`)** with constant `√2`:
both `|√p₀ − √p₁|` and `|p₀ − p₁|` are at most `√(2 · (∑_j q̂_j) / |X₁|)`. -/
theorem lemmaC3_both_sharp [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    |Real.sqrt (reproProb false true prog init) - Real.sqrt (reproProb true true prog init)| ≤
        Real.sqrt 2 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) ∧
    |reproProb false true prog init - reproProb true true prog init| ≤
        Real.sqrt 2 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) := by
  have hε : 0 ≤ (∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁ := by positivity
  have h := abs_sqrt_sub_and_abs_sub_le_of_fidelity
    (reproProb_mem_Icc false prog hinit) (reproProb_mem_Icc true prog hinit) hε
    (repro_fidelity prog hinit)
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h

/-- **Main Paper Lemma C.3 (`e = 1/2`)** (lines 5916–5929):
`|√Pr[Repro₀(A) ⇒ 1] − √Pr[Repro₁(A) ⇒ 1]| ≤ 4 √(∑_j q̂_j / |X₁|)`. -/
theorem lemmaC3_half [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    |Real.sqrt (reproProb false true prog init) - Real.sqrt (reproProb true true prog init)| ≤
      4 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) := by
  have h := (lemmaC3_both_sharp prog hinit).1
  have h24 : Real.sqrt 2 ≤ 4 := by
    calc Real.sqrt 2 ≤ Real.sqrt ((4 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4 := Real.sqrt_sq (by norm_num)
  exact h.trans (mul_le_mul_of_nonneg_right h24 (Real.sqrt_nonneg _))

/-- **Main Paper Lemma C.3 (`e = 1`)** (lines 5916–5929):
`|Pr[Repro₀(A) ⇒ 1] − Pr[Repro₁(A) ⇒ 1]| ≤ 4 √(∑_j q̂_j / |X₁|)`. -/
theorem lemmaC3_one [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    |reproProb false true prog init - reproProb true true prog init| ≤
      4 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) := by
  have h := (lemmaC3_both_sharp prog hinit).2
  have h24 : Real.sqrt 2 ≤ 4 := by
    calc Real.sqrt 2 ≤ Real.sqrt ((4 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4 := Real.sqrt_sq (by norm_num)
  exact h.trans (mul_le_mul_of_nonneg_right h24 (Real.sqrt_nonneg _))

/-- **Main Paper Lemma C.1 ([GHHM21])** (lines 5875–5881): if every call occurs after at most
`q_tot` quantum queries (`∀ j, q̂_j ≤ q_tot`), then
`|Pr[Repro₀(A) ⇒ 1] − Pr[Repro₁(A) ⇒ 1]| ≤ (3 R / 2) √(q_tot / |X₁|)`. -/
theorem lemmaC1 [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1)
    {q_tot : ℕ} (hq : ∀ j : Fin R, qhat q j ≤ q_tot) :
    |reproProb false true prog init - reproProb true true prog init| ≤
      (3 * (R : ℝ) / 2) * Real.sqrt ((q_tot : ℝ) / Fintype.card X₁) := by
  have h := (lemmaC3_both_sharp prog hinit).2
  rcases Nat.eq_zero_or_pos R with rfl | hRpos
  · simp only [Finset.univ_eq_empty, sum_empty, zero_div, Real.sqrt_zero, mul_zero] at h
    simpa using h
  have hsum : ∑ j : Fin R, (qhat q j : ℝ) ≤ (R : ℝ) * (q_tot : ℝ) := by
    calc ∑ j : Fin R, (qhat q j : ℝ) ≤ ∑ _j : Fin R, (q_tot : ℝ) :=
          sum_le_sum fun j _ => by exact_mod_cast hq j
      _ = (R : ℝ) * (q_tot : ℝ) := by simp
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
  have hsqrtR : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
    calc Real.sqrt (R : ℝ) ≤ Real.sqrt ((R : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (R : ℝ) := Real.sqrt_sq (by linarith)
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 / 2 := Real.sqrt_sq (by norm_num)
  calc |reproProb false true prog init - reproProb true true prog init|
      ≤ Real.sqrt 2 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) := h
    _ ≤ Real.sqrt 2 * Real.sqrt (((R : ℝ) * (q_tot : ℝ)) / Fintype.card X₁) :=
        mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)))
          (Real.sqrt_nonneg _)
    _ = (Real.sqrt 2 * Real.sqrt (R : ℝ)) * Real.sqrt ((q_tot : ℝ) / Fintype.card X₁) := by
        rw [mul_div_assoc, Real.sqrt_mul (Nat.cast_nonneg R), mul_assoc]
    _ ≤ (3 * (R : ℝ) / 2) * Real.sqrt ((q_tot : ℝ) / Fintype.card X₁) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        have : Real.sqrt 2 * Real.sqrt (R : ℝ) ≤ (3 / 2 : ℝ) * (R : ℝ) :=
          mul_le_mul hsqrt2 hsqrtR (Real.sqrt_nonneg _) (by norm_num)
        linarith

/-- **Unconditional Quantum Corollary C.1** (Main Paper lines 6030–6042):
`p₀ ≤ 2 p₁ + 32 ∑_j q̂_j / |X₁|` and `p₁ ≤ 2 p₀ + 32 ∑_j q̂_j / |X₁|`. -/
theorem corollaryC1 [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : ReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    reproProb false true prog init ≤
        2 * reproProb true true prog init +
          32 * ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) ∧
      reproProb true true prog init ≤
        2 * reproProb false true prog init +
          32 * ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) :=
  ReproHalf.corollaryC1 (qhat q) (Fintype.card X₁)
    (reproProb_nonneg false true prog init) (reproProb_nonneg true true prog init)
    (lemmaC3_half prog hinit)

/-! ## Unconditional Quantum `DI-Repro` Bounds (Lemma C.5 + Corollaries C.1, C.3) -/

/-- **Quantum `DI-Repro` Lemma C.3 (`e = 1/2`)** via Quantum Lemma C.5 (`filterRun`). -/
theorem diRepro_lemmaC3_half [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : DIReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    |Real.sqrt (diReproProb false true prog init) - Real.sqrt (diReproProb true true prog init)| ≤
      4 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) := by
  rw [diReproProb_eq_reproProb_filterRun, diReproProb_eq_reproProb_filterRun]
  exact lemmaC3_half (filterRun ∅ prog) hinit

/-- **Quantum `DI-Repro` Lemma C.3 (`e = 1`)** via Quantum Lemma C.5 (`filterRun`). -/
theorem diRepro_lemmaC3_one [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : DIReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1) :
    |diReproProb false true prog init - diReproProb true true prog init| ≤
      4 * Real.sqrt ((∑ j : Fin R, (qhat q j : ℝ)) / Fintype.card X₁) := by
  rw [diReproProb_eq_reproProb_filterRun, diReproProb_eq_reproProb_filterRun]
  exact lemmaC3_one (filterRun ∅ prog) hinit

/-- **Quantum `DI-Repro` Lemma C.1** via Quantum Lemma C.5 (`filterRun`). -/
theorem diRepro_lemmaC1 [Nonempty X₁] {R : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : DIReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1)
    {q_tot : ℕ} (hq : ∀ j : Fin R, qhat q j ≤ q_tot) :
    |diReproProb false true prog init - diReproProb true true prog init| ≤
      (3 * (R : ℝ) / 2) * Real.sqrt ((q_tot : ℝ) / Fintype.card X₁) := by
  rw [diReproProb_eq_reproProb_filterRun, diReproProb_eq_reproProb_filterRun]
  exact lemmaC1 (filterRun ∅ prog) hinit hq

/-- **Unconditional Quantum Corollary C.3 (`e = 1` and `e = 1/2` and `min` with Lemma C.1)**
for a `DI-Repro` adversary with `R ≤ qs` calls and `q̂_j ≤ qh + j` (Remark C.4). -/
theorem diRepro_corollaryC3 [Nonempty X₁] {R qs qh : ℕ} {q : Fin (R + 1) → ℕ}
    (prog : DIReproProg X₁ X₂ Y E R q) {init : Reg X₁ X₂ Y E → ℂ} (hinit : normSq init = 1)
    (hR : R ≤ qs) (hq : ∀ j : Fin R, qhat q j ≤ qh + j.val) :
    |diReproProb false true prog init - diReproProb true true prog init| ≤
        min (4 * Real.sqrt (ReproHalf.corollaryC3S qs qh / Fintype.card X₁))
          ((3 * (qs : ℝ) / 2) * Real.sqrt (((qh + qs : ℕ) : ℝ) / Fintype.card X₁)) ∧
      diReproProb false true prog init ≤
        2 * diReproProb true true prog init +
          32 * (ReproHalf.corollaryC3S qs qh / Fintype.card X₁) := by
  have hsum : (∑ j : Fin R, (qhat q j : ℝ)) ≤ ReproHalf.corollaryC3S qs qh := by
    have hnat : ∑ j : Fin R, qhat q j ≤ ReproHalf.corollaryC3S qs qh := by
      have h1 := (ReproHalf.remarkC4 (qhat q) hq).1
      unfold ReproHalf.corollaryC3S
      have hm1 : R * qh ≤ qs * qh := Nat.mul_le_mul_right qh hR
      have hm2 : R * (R - 1) / 2 ≤ qs * (qs - 1) / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul hR (Nat.sub_le_sub_right hR 1))
      omega
    exact_mod_cast hnat
  have hcard : (0 : ℝ) ≤ Fintype.card X₁ := Nat.cast_nonneg _
  have hone : |diReproProb false true prog init - diReproProb true true prog init| ≤
      4 * Real.sqrt (ReproHalf.corollaryC3S qs qh / Fintype.card X₁) :=
    (diRepro_lemmaC3_one prog hinit).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum hcard))
        (by norm_num))
  have hc1 : |diReproProb false true prog init - diReproProb true true prog init| ≤
      (3 * (qs : ℝ) / 2) * Real.sqrt (((qh + qs : ℕ) : ℝ) / Fintype.card X₁) := by
    have hqtot : ∀ j : Fin R, qhat q j ≤ qh + qs := fun j => by
      have := hq j; omega
    have h := diRepro_lemmaC1 prog hinit hqtot
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have hR' : (R : ℝ) ≤ qs := by exact_mod_cast hR
    linarith
  have hhalf : diReproProb false true prog init ≤
      2 * diReproProb true true prog init +
        32 * (ReproHalf.corollaryC3S qs qh / Fintype.card X₁) := by
    rw [diReproProb_eq_reproProb_filterRun, diReproProb_eq_reproProb_filterRun]
    have h := (corollaryC1 (filterRun ∅ prog) hinit).1
    have hdiv := div_le_div_of_nonneg_right hsum hcard
    linarith
  exact ⟨le_min hone hc1, hhalf⟩

end ReproGame

end ShrincsSecurity.Undetectability.ReproQrom
