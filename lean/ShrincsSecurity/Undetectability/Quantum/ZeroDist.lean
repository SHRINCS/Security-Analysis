module

public import QuantumFoundations.Pure.Instrument
public import QuantumFoundations.Pure.Norm
public import QuantumFoundations.Oracle.Unitary

/-!
# Quantum `ZeroDist`: Lemma C.8 in the unitary query model

`SHRINCS-Security-Analysis.pdf`, Appendix C, **Definition C.4** (`ZeroDist`, distinguishing the
all-zero Boolean function `f₀` on `P` from the point function `f_{P'}` of a uniformly random
`P' ∈ P`, with `P'` revealed to the second stage only) and **Lemma C.8**: a first stage making
`q` quantum queries has advantage at most `2q / √|P|`.

## Model

* The Boolean oracle `f : P → ZMod 2` (`ZMod 2` is the additive group of the output bit, so the
  oracle unitary `oracleUnitary f : |x, y⟩ ↦ |x, y + f x⟩` is the XOR oracle) acts on the query
  register `P × ZMod 2`, beside a finite workspace `W`: `queryOp f = oracleUnitary f ⊗ 1_W`.
* The first stage is a unitary query algorithm in the standard circuit form: a unit initial
  vector `init`, then `U 0`, a query, `U 1`, …, a query, `U q` (`Quantum.queryState`). It makes
  exactly `q` queries; Lemma C.8 for *at most* `q` queries is `advantage_le_of_le`.
* The second stage receives `P'` and the full quantum state of the first stage, and has no
  oracle. It is an arbitrary two-outcome measurement depending on `P'`, given by Kraus operators
  `meas P' b : M ← Reg P W` with `∑ b, (meas P' b)ᴴ (meas P' b) = 1`; its output bit is `b`. Any
  quantum second stage reporting a bit is of this form (take `meas P' true = √E`,
  `meas P' false = √(1 - E)` for its acceptance effect `E`), so this loses no generality.
  Acceptance probabilities are the library's Born rule
  `(DSubInstrument.ofKraus …).outcomeMeasure (SubState.ofVector …)` of the outcome `true`.
* `winProb A q b` is `Pr[ZeroDist(A) ⇒ 1 | b]`, averaging over the uniform `P'`, and
  `advantage A q = |winProb A q true - winProb A q false|`.

Scope: a purely unitary first stage on a finite register, in vector form. Adaptive first stages
with intermediate measurements, mixed states and classical control are VCVio programs, treated in
`ShrincsSecurity.Undetectability.Quantum.ZeroDistAdaptive` (`Adaptive.advantage_le_of_lossless`,
same constant `2q / √|P|`).

## Proof

1. **Hybrid** (`norm_finalState_sub_le`, from BBBV `Quantum.norm_queryState_sub_queryState_le`
   with the zero oracle as reference): `‖ψ_q^{P'} - ψ_q^0‖ ≤ 2 ∑_{i<q} √(mass P' ψ_i⁰)`, where
   `ψ_i⁰` is the state before the `i`-th query under `f₀`, independent of `P'`, and `mass P' ψ`
   is the squared weight of `ψ` on query input `P'` (`norm_sub_queryOp_marked_le`).
2. **Averaging** (`sum_sqrt_mass_le`, from `sum_mass` and Cauchy–Schwarz):
   `∑_{P'} √(mass P' ψ_i⁰) ≤ √|P|`.
3. **Event bound** (`abs_acceptProb_sub_le`): two states of the same norm `≤ 1` give acceptance
   probabilities differing by at most their distance. This is the sharp conversion (constant 1);
   the library lemma `DSubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le_two_mul`
   has constant 2, which would only give `4q / √|P|`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Kronecker
open Matrix Quantum MeasureTheory

namespace ShrincsSecurity.Undetectability.ZeroDist

/-! ## Event probabilities of states of equal norm -/

section Event

/-- The real inequality behind `abs_norm_sq_sub_norm_sq_le`. With `a, c` the norms of the two
branches on the first vector, `b, d` on the second and `e₁, e₀` on the difference, the change
`a² - b² = d² - c²` of the accepting weight is at most `n δ`. -/
theorem abs_sq_sub_sq_le_of_branches {a b c d e₁ e₀ n δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he₁ : 0 ≤ e₁) (hn : 0 ≤ n) (hδ : 0 ≤ δ)
    (hab : |a - b| ≤ e₁) (hcd : |c - d| ≤ e₀) (hψ : a ^ 2 + c ^ 2 = n ^ 2)
    (hφ : b ^ 2 + d ^ 2 = n ^ 2) (he : e₁ ^ 2 + e₀ ^ 2 ≤ δ ^ 2) :
    |a ^ 2 - b ^ 2| ≤ n * δ := by
  have hX : |a ^ 2 - b ^ 2| ≤ e₁ * (a + b) := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
      abs_of_nonneg (add_nonneg ha hb)]
    exact mul_le_mul_of_nonneg_right hab (add_nonneg ha hb)
  have hY : |a ^ 2 - b ^ 2| ≤ e₀ * (c + d) := by
    rw [show a ^ 2 - b ^ 2 = -((c - d) * (c + d)) by linear_combination hψ - hφ, abs_neg,
      abs_mul, abs_of_nonneg (add_nonneg hc hd)]
    exact mul_le_mul_of_nonneg_right hcd (add_nonneg hc hd)
  have h1 : e₁ * e₀ ≤ δ ^ 2 / 2 := by nlinarith [sq_nonneg (e₁ - e₀)]
  have h2 : (a + b) * (c + d) ≤ 2 * n ^ 2 := by
    nlinarith [sq_nonneg (a + b - (c + d)), sq_nonneg (a - b), sq_nonneg (c - d)]
  have hsq : |a ^ 2 - b ^ 2| ^ 2 ≤ (n * δ) ^ 2 :=
    calc |a ^ 2 - b ^ 2| ^ 2 ≤ (e₁ * (a + b)) * (e₀ * (c + d)) := by
          rw [sq]; exact mul_le_mul hX hY (abs_nonneg _) (by positivity)
      _ = (e₁ * e₀) * ((a + b) * (c + d)) := by ring
      _ ≤ (δ ^ 2 / 2) * (2 * n ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (n * δ) ^ 2 := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hn hδ)).mp hsq

variable {A M : Type*} [Fintype A] [DecidableEq A] [Fintype M]

/-- **Sharp event bound for vectors of equal norm.** For a complete two-outcome Kraus family,
the squared norms of the accepting branches of `ψ` and `φ`, with `‖ψ‖ = ‖φ‖`, differ by at most
`‖ψ‖ · ‖ψ - φ‖`. (The general bound `(‖ψ‖ + ‖φ‖) ‖ψ - φ‖` loses a factor two.) -/
theorem abs_norm_sq_sub_norm_sq_le {K : Bool → Matrix M A ℂ} (hK : ∑ b, (K b)ᴴ * K b = 1)
    {ψ φ : EuclideanSpace ℂ A} (h : ‖ψ‖ = ‖φ‖) :
    |‖K true •ᵥ ψ‖ ^ 2 - ‖K true •ᵥ φ‖ ^ 2| ≤ ‖ψ‖ * ‖ψ - φ‖ := by
  have hψ := sum_norm_sq_applyVec hK ψ
  have hφ := sum_norm_sq_applyVec hK φ
  have hd := sum_norm_sq_applyVec hK (ψ - φ)
  simp only [Fintype.sum_bool] at hψ hφ hd
  rw [h] at hψ
  have hab : |‖K true •ᵥ ψ‖ - ‖K true •ᵥ φ‖| ≤ ‖K true •ᵥ (ψ - φ)‖ := by
    rw [map_sub]; exact abs_norm_sub_norm_le _ _
  have hcd : |‖K false •ᵥ ψ‖ - ‖K false •ᵥ φ‖| ≤ ‖K false •ᵥ (ψ - φ)‖ := by
    rw [map_sub]; exact abs_norm_sub_norm_le _ _
  rw [h]
  exact abs_sq_sub_sq_le_of_branches (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hab hcd hψ hφ hd.le

/-- The probability that the two-outcome measurement with Kraus operators `K` reports `true` on
the pure substate of `ψ`: the Born rule of `DSubInstrument.ofKraus`. -/
noncomputable def acceptProb (K : Bool → Matrix M A ℂ) (hK : ∑ b, (K b)ᴴ * K b = 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) : ℝ :=
  ((DSubInstrument.ofKraus (B := fun _ : Bool ↦ M) K hK).outcomeMeasure
    (.ofVector ψ hψ)).real {true}

/-- The acceptance probability is the squared norm of the accepting branch. -/
theorem acceptProb_eq (K : Bool → Matrix M A ℂ) (hK : ∑ b, (K b)ᴴ * K b = 1)
    (ψ : EuclideanSpace ℂ A) (hψ : ‖ψ‖ ≤ 1) : acceptProb K hK ψ hψ = ‖K true •ᵥ ψ‖ ^ 2 := by
  rw [acceptProb, Measure.real, DSubInstrument.outcomeMeasure_ofKraus_ofVector_singleton,
    ENNReal.toReal_ofReal (sq_nonneg _)]

/-- **State distance to acceptance probability, sharp form.** On subnormalized vectors of equal
norm, the acceptance probabilities of a two-outcome measurement differ by at most the distance of
the vectors. -/
theorem abs_acceptProb_sub_le (K : Bool → Matrix M A ℂ) (hK : ∑ b, (K b)ᴴ * K b = 1)
    {ψ φ : EuclideanSpace ℂ A} (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) (h : ‖ψ‖ = ‖φ‖) :
    |acceptProb K hK ψ hψ - acceptProb K hK φ hφ| ≤ ‖ψ - φ‖ := by
  rw [acceptProb_eq, acceptProb_eq]
  exact (abs_norm_sq_sub_norm_sq_le hK h).trans
    (mul_le_of_le_one_left (norm_nonneg _) hψ)

end Event

/-! ## The Boolean oracle -/

section Oracle

variable {P W : Type*} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]

/-- The register of the first stage: the query register `P × ZMod 2` (input, response bit) and a
workspace `W`. -/
abbrev Reg (P W : Type*) := (P × ZMod 2) × W

/-- One query to the Boolean function `f`: the XOR oracle unitary `oracleUnitary f` on the query
register, the identity on the workspace. -/
noncomputable def queryOp (f : P → ZMod 2) : Matrix (Reg P W) (Reg P W) ℂ :=
  oracleUnitary f ⊗ₖ (1 : Matrix W W ℂ)

/-- The Boolean function `f_{P'}` of Definition C.4: `1` at `P'`, `0` elsewhere. The function
`f₀` is `0`. -/
def marked (P' : P) : P → ZMod 2 :=
  Pi.single P' 1

/-- The query mass of `ψ` on the input `P'`: the squared norm of its component whose query input
register holds `P'`, `‖(|P'⟩⟨P'| ⊗ 1) ψ‖²`. -/
noncomputable def mass (P' : P) (ψ : EuclideanSpace ℂ (Reg P W)) : ℝ :=
  ∑ y : ZMod 2, ∑ w : W, ‖ψ ((P', y), w)‖ ^ 2

omit [Fintype P] [DecidableEq P] [DecidableEq W] in
theorem mass_nonneg (P' : P) (ψ : EuclideanSpace ℂ (Reg P W)) : 0 ≤ mass P' ψ :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [DecidableEq P] [DecidableEq W] in
/-- The query masses over all inputs add up to the squared norm. -/
theorem sum_mass (ψ : EuclideanSpace ℂ (Reg P W)) : ∑ P', mass P' ψ = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_prod_type]
  rfl

omit [DecidableEq P] [DecidableEq W] in
/-- **Averaging over the marked point** (Cauchy–Schwarz): the query masses of a unit vector on
the points of `P` have square roots summing to at most `√|P|`. -/
theorem sum_sqrt_mass_le (ψ : EuclideanSpace ℂ (Reg P W)) (hψ : ‖ψ‖ ≤ 1) :
    ∑ P' : P, √(mass P' ψ) ≤ √(Fintype.card P) := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ (f := fun _ : P ↦ (1 : ℝ))
    (g := fun P' ↦ mass P' ψ) (fun _ ↦ zero_le_one) (fun P' ↦ mass_nonneg P' ψ)
  simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sum_mass] at h
  refine h.trans ?_
  calc √(Fintype.card P) * √(‖ψ‖ ^ 2) ≤ √(Fintype.card P) * 1 := by
        gcongr
        rw [Real.sqrt_sq (norm_nonneg _)]
        exact hψ
    _ = √(Fintype.card P) := mul_one _

/-- The basis matrix of a permutation moves the entries of a vector. -/
theorem basisMatrix_equiv_applyVec {A : Type*} [Fintype A] [DecidableEq A] (e : A ≃ A)
    (ψ : EuclideanSpace ℂ A) (a : A) : (basisMatrix e •ᵥ ψ) a = ψ (e.symm a) := by
  change (basisMatrix e *ᵥ ψ.ofLp) a = ψ.ofLp (e.symm a)
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (e.symm a)]
  · simp
  · intro b _ hb
    rw [basisMatrix_apply, ite_eq_right_iff.mpr fun h ↦ absurd (by simp [h]) hb, zero_mul]
  · simp

omit [Fintype P] [Fintype W] in
/-- The query operator is the basis permutation `((x, y), w) ↦ ((x, y + f x), w)`. -/
theorem queryOp_eq (f : P → ZMod 2) :
    queryOp (W := W) f = basisMatrix ⇑((oracleEquiv f).prodCongr (Equiv.refl W)) := by
  rw [queryOp, oracleUnitary, basisMatrix_kronecker_one]
  rfl

/-- A query reads the response register shifted by `f x`. -/
theorem queryOp_applyVec (f : P → ZMod 2) (ψ : EuclideanSpace ℂ (Reg P W)) (x : P) (y : ZMod 2)
    (w : W) : (queryOp f •ᵥ ψ) ((x, y), w) = ψ ((x, y - f x), w) := by
  rw [queryOp_eq, basisMatrix_equiv_applyVec]
  rfl

/-- A query is unitary. -/
theorem queryOp_mem_unitaryGroup (f : P → ZMod 2) :
    queryOp (W := W) f ∈ Matrix.unitaryGroup (Reg P W) ℂ := by
  rw [queryOp_eq]
  exact basisMatrix_perm_mem_unitaryGroup _

/-- **One query to `f_{P'}` versus `f₀`.** The query to `f_{P'}` moves a state by at most twice
the square root of its query mass on `P'`: `‖ψ - O_{P'} ψ‖² ≤ 4 · mass P' ψ`. -/
theorem norm_sq_sub_queryOp_marked_le (P' : P) (ψ : EuclideanSpace ℂ (Reg P W)) :
    ‖ψ - queryOp (marked P') •ᵥ ψ‖ ^ 2 ≤ 4 * mass P' ψ := by
  have hpt : ∀ x y w, (ψ - queryOp (marked P') •ᵥ ψ) ((x, y), w) =
      ψ ((x, y), w) - ψ ((x, y - marked P' x), w) := fun x y w ↦ by
    rw [PiLp.sub_apply, queryOp_applyVec]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_eq_single P']
  · simp only [hpt]
    simp only [marked, Pi.single_eq_same]
    have hshift : ∑ y : ZMod 2, ∑ w : W, ‖ψ ((P', y - 1), w)‖ ^ 2 = mass P' ψ :=
      (Equiv.subRight (1 : ZMod 2)).sum_comp fun y ↦ ∑ w : W, ‖ψ ((P', y), w)‖ ^ 2
    calc ∑ y : ZMod 2, ∑ w : W, ‖ψ ((P', y), w) - ψ ((P', y - 1), w)‖ ^ 2
        ≤ ∑ y : ZMod 2, ∑ w : W,
            (2 * ‖ψ ((P', y), w)‖ ^ 2 + 2 * ‖ψ ((P', y - 1), w)‖ ^ 2) := by
          gcongr with y _ w _
          nlinarith [norm_sub_le (ψ ((P', y), w)) (ψ ((P', y - 1), w)),
            norm_nonneg (ψ ((P', y), w) - ψ ((P', y - 1), w)),
            sq_nonneg (‖ψ ((P', y), w)‖ - ‖ψ ((P', y - 1), w)‖)]
      _ = 2 * mass P' ψ + 2 * ∑ y : ZMod 2, ∑ w : W, ‖ψ ((P', y - 1), w)‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mass]
      _ = 4 * mass P' ψ := by rw [hshift]; ring
  · intro x _ hx
    simp only [hpt]
    simp [marked, Pi.single_eq_of_ne hx]
  · simp

/-- **One query to `f_{P'}` versus `f₀`**, in norm: `‖(O₀ - O_{P'}) ψ‖ ≤ 2 √(mass P' ψ)`. -/
theorem norm_sub_queryOp_marked_le (P' : P) (ψ : EuclideanSpace ℂ (Reg P W)) :
    ‖(queryOp 0 - queryOp (marked P')) •ᵥ ψ‖ ≤ 2 * √(mass P' ψ) := by
  have h0 : queryOp (W := W) (0 : P → ZMod 2) = 1 := by
    rw [queryOp, oracleUnitary_zero, one_kronecker_one]
  rw [h0, sub_applyVec, one_applyVec]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (mass_nonneg P' ψ)]
  norm_num
  exact norm_sq_sub_queryOp_marked_le P' ψ

end Oracle

/-! ## The experiment -/

section Game

variable {P W M : Type*} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W] [Fintype M]

/-- A two-stage quantum adversary against `ZeroDist` (Definition C.4) in the unitary query model.
The first stage starts from the unit vector `init` and applies `U 0, query, U 1, …, query, U q`;
the second stage, on input `P'`, measures the whole register with the complete two-outcome Kraus
family `meas P'` and outputs the outcome. -/
structure Adversary (P W M : Type*) [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]
    [Fintype M] where
  /-- The initial state of the first stage. -/
  init : EuclideanSpace ℂ (Reg P W)
  norm_init : ‖init‖ = 1
  /-- The unitaries of the first stage, between its queries. -/
  U : ℕ → Matrix (Reg P W) (Reg P W) ℂ
  mem_unitaryGroup : ∀ i, U i ∈ Matrix.unitaryGroup (Reg P W) ℂ
  /-- The measurement of the second stage on input `P'`: Kraus operators of the outputs. -/
  meas : P → Bool → Matrix M (Reg P W) ℂ
  meas_complete : ∀ P', ∑ b, (meas P' b)ᴴ * meas P' b = 1

namespace Adversary

variable (A : Adversary P W M)

/-- The state of the first stage after `q` queries to `f` (and the unitary `U q`). -/
noncomputable def finalState (q : ℕ) (f : P → ZMod 2) : EuclideanSpace ℂ (Reg P W) :=
  queryState A.U (fun _ ↦ queryOp f) A.init q

/-- The first stage is unitary: its states are unit vectors. -/
theorem norm_finalState (q : ℕ) (f : P → ZMod 2) : ‖A.finalState q f‖ = 1 := by
  induction q with
  | zero =>
    rw [finalState, queryState_zero, norm_applyVec_of_mem_unitaryGroup (A.mem_unitaryGroup 0),
      A.norm_init]
  | succ q ih =>
    rw [finalState, queryState_succ, norm_applyVec_of_mem_unitaryGroup (A.mem_unitaryGroup _),
      norm_applyVec_of_mem_unitaryGroup (queryOp_mem_unitaryGroup f)]
    exact ih

/-- The probability that the second stage outputs `1` on input `P'`, after `q` first-stage
queries to `f`. -/
noncomputable def accept (q : ℕ) (P' : P) (f : P → ZMod 2) : ℝ :=
  acceptProb (A.meas P') (A.meas_complete P') (A.finalState q f) (A.norm_finalState q f).le

/-- `Pr[ZeroDist(A) ⇒ 1 | b]`: `P'` uniform on `P`, the first stage runs with `q` queries to
`f_{P'}` if `b = 1` and to `f₀` if `b = 0`, the second stage gets `P'`. -/
noncomputable def winProb (q : ℕ) (b : Bool) : ℝ :=
  (Fintype.card P : ℝ)⁻¹ * ∑ P', A.accept q P' (if b then marked P' else 0)

/-- `Adv^{ZeroDist}(A) = |Pr[ZeroDist(A) ⇒ 1 | b = 1] - Pr[ZeroDist(A) ⇒ 1 | b = 0]|`. -/
noncomputable def advantage (q : ℕ) : ℝ :=
  |A.winProb q true - A.winProb q false|

/-- **The hybrid bound for one marked point.** The final states under `f_{P'}` and under `f₀` are
at distance at most `2 ∑_{i<q} √(mass P' ψ_i)`, where `ψ_i` is the state before the `i`-th query
of the run against `f₀` (BBBV, `Quantum.norm_queryState_sub_queryState_le`). -/
theorem norm_finalState_sub_le (q : ℕ) (P' : P) :
    ‖A.finalState q 0 - A.finalState q (marked P')‖ ≤
      2 * ∑ i ∈ Finset.range q, √(mass P' (queryState A.U (fun _ ↦ queryOp 0) A.init i)) := by
  refine (norm_queryState_sub_queryState_le A.U (fun _ ↦ queryOp 0)
    (fun _ ↦ queryOp (marked P')) A.init q
    (fun i _ ↦ l2_opNorm_le_one_of_mem_unitaryGroup (A.mem_unitaryGroup (i + 1)))
    (fun _ _ ↦ l2_opNorm_le_one_of_mem_unitaryGroup (queryOp_mem_unitaryGroup _))).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ norm_sub_queryOp_marked_le P' _

/-- **Lemma C.8** (quantum `ZeroDist`, unitary query model). A first stage making `q` quantum
queries to its Boolean oracle gives advantage at most `2q / √|P|`. -/
theorem advantage_le [Nonempty P] (q : ℕ) :
    A.advantage q ≤ 2 * q / √(Fintype.card P) := by
  set N : ℝ := (Fintype.card P : ℝ) with hN
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  set ψ : ℕ → EuclideanSpace ℂ (Reg P W) := queryState A.U (fun _ ↦ queryOp 0) A.init with hψ
  have hψn : ∀ i, ‖ψ i‖ ≤ 1 := fun i ↦ (A.norm_finalState i 0).le
  have hstep : ∀ P', |A.accept q P' (marked P') - A.accept q P' 0| ≤
      2 * ∑ i ∈ Finset.range q, √(mass P' (ψ i)) := fun P' ↦ by
    refine (abs_acceptProb_sub_le _ _ _ _ ?_).trans ?_
    · rw [A.norm_finalState, A.norm_finalState]
    · rw [norm_sub_rev]
      exact A.norm_finalState_sub_le q P'
  have hdiff : A.winProb q true - A.winProb q false =
      N⁻¹ * ∑ P', (A.accept q P' (marked P') - A.accept q P' 0) := by
    simp [winProb, hN, Finset.sum_sub_distrib, mul_sub]
  rw [advantage, hdiff, abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
  calc N⁻¹ * |∑ P', (A.accept q P' (marked P') - A.accept q P' 0)|
      ≤ N⁻¹ * ∑ P', 2 * ∑ i ∈ Finset.range q, √(mass P' (ψ i)) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun P' _ ↦ hstep P')
    _ = N⁻¹ * (2 * ∑ i ∈ Finset.range q, ∑ P', √(mass P' (ψ i))) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ N⁻¹ * (2 * ∑ _i ∈ Finset.range q, √N) := by
        gcongr with i _
        exact sum_sqrt_mass_le (ψ i) (hψn i)
    _ = 2 * q / √N := by
        have hs : 0 < √N := Real.sqrt_pos.mpr hNpos
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        rw [Real.sq_sqrt hNpos.le, mul_comm]

/-- **Lemma C.8** for a first stage making *at most* `q` queries. -/
theorem advantage_le_of_le [Nonempty P] {q' q : ℕ} (h : q' ≤ q) :
    A.advantage q' ≤ 2 * q / √(Fintype.card P) :=
  (A.advantage_le q').trans (by gcongr)

end Adversary

end Game

end ShrincsSecurity.Undetectability.ZeroDist
