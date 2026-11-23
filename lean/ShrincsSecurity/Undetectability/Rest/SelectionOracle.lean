module

public import QuantumFoundations.Oracle.Unitary
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 2: one query per selection

Undetectability paper (`notes/txt/Undetectability.txt`), **Lemma 2** (One query per selection,
lines 258–383; Remark C.2 of the main paper cites it as [Kud26b]): let `H : X → {0, 1}ⁿ` satisfy
`H(x) = h(x) ⊕ L_x(f(s(x)))` for functions `s : X → U`, `h : X → {0, 1}ⁿ` and GF(2)-linear maps
`L_x : {0, 1}ᵐ → {0, 1}ⁿ` that do not depend on `f : U → {0, 1}ᵐ`. Then a circuit that depends on
`s, h, L` but not on `f` makes exactly one query to the standard oracle of `f` and maps
`|x, y⟩|0⟩` to `|x, y ⊕ H(x)⟩|0⟩`.

## Model

Bit strings are `Bits k = Fin k → ZMod 2` with `⊕` the addition of `ZMod 2`-vectors; `L_x` is a
`ZMod 2`-matrix (`Matrix (Fin n) (Fin m) (ZMod 2)`, `L_x(β) = L_x *ᵥ β`, the transpose is
`Matrix.transpose`; `selection_one_query_linearMap` restates the result for linear maps). Oracles
are `Quantum.oracleUnitary` from QuantumFoundations, the permutation matrix of
`|x, y⟩ ↦ |x, y + H x⟩`. As in the paper (line 330), `U` carries an additive group law, used to
write `s(x)` into the ancilla register `u`.

The circuit acts on the register `Reg = (U × Bits m) × ((X × Bits n) × Bits m)`, in the order
`((u, t), ((x, y), c))`: the query register `(u, t)` of `f` first, as in the framing of oracle
calls of VCVio combs (`queryStep`), then the query register `(x, y)` of `H` and the ancilla `c`.
The ancilla registers `u, t, c` start at `0`, and the selection oracle is embedded by
`ancillaEmbed : |x, y⟩ ↦ |(0, 0), ((x, y), 0)⟩`. The circuit is `finish * fQuery f * prepare`:

* `prepare s h L = tHadamard * basisMatrix σ₂ * yHadamard * basisMatrix σ₁`: steps 1–3 of the
  paper (`σ₁`: `y ↦ y ⊕ h(x)`; `yHadamard`: `W_n` on `y`; `σ₂`: `c ↦ c ⊕ L_xᵀ z`, `u ↦ u + s(x)`,
  then `t ↦ t ⊕ c`; `tHadamard`: `W_m` on `t`);
* `fQuery f = oracleUnitary f ⊗ₖ 1`: one query to `f` on `(u, t)`, the identity elsewhere (step 4);
* `finish s L = yHadamard * basisMatrix σ₂⁻¹ * tHadamard`: undo steps 3 and 2, then `W_n` on `y`
  (step 5).

`prepare` and `finish` are unitary (`prepare_mem_unitaryGroup`, `finish_mem_unitaryGroup`) and do
not take `f` as an argument.

## Main results

* `hadamard_mul_phase_mul_hadamard`: the first fact of the proof, `W_n D_v W_n = X_v` (the shift
  `|y⟩ ↦ |y ⊕ v⟩`).
* `phase_kickback`: the second fact, `(1 ⊗ W_m) O_f (1 ⊗ W_m) = diag((u, t) ↦ (-1)^{⟨t, f(u)⟩})`.
* `selection_mulVec_single`: **Lemma 2** on basis states, the circuit maps `|(0,0),((x,y),0)⟩` to
  `|(0,0),((x, y ⊕ H x),0)⟩`.
* `selection_mul_ancillaEmbed`: **Lemma 2** as an operator identity,
  `finish * fQuery f * prepare * ancillaEmbed = ancillaEmbed * oracleUnitary H`.
* `selection_two_values`: the selection between two values (`m = 1`, lines 374–377).
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability.Selection

open Matrix Quantum Finset
open scoped Kronecker

/-! ### Signs and bit strings -/

/-- Bit strings of length `k`, with bitwise XOR as addition. -/
abbrev Bits (k : ℕ) := Fin k → ZMod 2

/-- The sign `(-1)^a` of a bit `a`. -/
def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

lemma zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

lemma zmod2_one_add_one : (1 + 1 : ZMod 2) = 0 := by decide

@[simp] lemma sgn_one : sgn 1 = -1 := by simp [sgn]

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [zmod2_one_add_one]

lemma star_sgn (a : ZMod 2) : star (sgn a) = sgn a := by
  rcases zmod2_cases a with rfl | rfl <;> simp

lemma sgn_sum {ι : Type*} (s : Finset ι) (g : ι → ZMod 2) :
    sgn (∑ i ∈ s, g i) = ∏ i ∈ s, sgn (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, sgn_add, ih]

lemma sum_sgn_mul (a : ZMod 2) : ∑ b : ZMod 2, sgn (a * b) = if a = 0 then 2 else 0 := by
  have huniv : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, sum_pair (by decide)]
  rcases zmod2_cases a with rfl | rfl
  · norm_num
  · simp

lemma bits_neg {k : ℕ} (a : Bits k) : -a = a :=
  funext fun i => (by decide : ∀ x : ZMod 2, -x = x) (a i)

lemma bits_add_eq_zero_iff {k : ℕ} {a b : Bits k} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, bits_neg]

/-- **Character orthogonality** on `{0, 1}ᵏ`: `∑_z (-1)^{⟨w, z⟩} = 2ᵏ [w = 0]`. -/
theorem sum_sgn_dotProduct {k : ℕ} (w : Bits k) :
    ∑ z : Bits k, sgn (w ⬝ᵥ z) = if w = 0 then 2 ^ k else 0 := by
  simp only [dotProduct, sgn_sum]
  rw [← Fintype.prod_sum (fun i b => sgn (w i * b))]
  simp only [sum_sgn_mul]
  split_ifs with hw
  · simp [hw]
  · obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (funext h)
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

/-! ### The Hadamard transform -/

/-- The normalisation `2^{-k/2}`. -/
noncomputable def hnorm (k : ℕ) : ℂ := ((Real.sqrt 2 ^ k)⁻¹ : ℝ)

lemma hnorm_mul_hnorm (k : ℕ) : hnorm k * hnorm k = ((2 : ℂ) ^ k)⁻¹ := by
  have : (Real.sqrt 2 ^ k)⁻¹ * (Real.sqrt 2 ^ k)⁻¹ = ((2 : ℝ) ^ k)⁻¹ := by
    rw [← mul_inv, ← mul_pow, Real.mul_self_sqrt (by norm_num)]
  rw [hnorm, ← Complex.ofReal_mul, this]
  push_cast
  rfl

lemma star_hnorm (k : ℕ) : star (hnorm k) = hnorm k := Complex.conj_ofReal _

/-- The Hadamard transform `W_k |v⟩ = 2^{-k/2} ∑_w (-1)^{⟨v, w⟩} |w⟩` on `k` qubits. -/
noncomputable def hadamard (k : ℕ) : Matrix (Bits k) (Bits k) ℂ :=
  Matrix.of fun a b => hnorm k * sgn (a ⬝ᵥ b)

lemma hadamard_apply {k : ℕ} (a b : Bits k) : hadamard k a b = hnorm k * sgn (a ⬝ᵥ b) := rfl

/-- Shifting the column of `W_k` by `r` multiplies the entry by `(-1)^{⟨a, r⟩}`. -/
lemma hadamard_apply_add {k : ℕ} (a b r : Bits k) :
    hadamard k a (b + r) = sgn (a ⬝ᵥ r) * hadamard k a b := by
  rw [hadamard_apply, hadamard_apply, dotProduct_add, sgn_add]
  ring

/-- The sum behind `W_k D_v W_k`: `∑_z W(w, z) (-1)^{⟨z, v⟩} W(z, y) = [w = y ⊕ v]`. -/
lemma sum_hadamard_sgn_hadamard {k : ℕ} (w y v : Bits k) :
    ∑ z, hadamard k w z * (sgn (z ⬝ᵥ v) * hadamard k z y) = if w = y + v then 1 else 0 := by
  have hterm : ∀ z, hadamard k w z * (sgn (z ⬝ᵥ v) * hadamard k z y) =
      hnorm k * hnorm k * sgn ((w + y + v) ⬝ᵥ z) := fun z => by
    rw [hadamard_apply, hadamard_apply, add_dotProduct, add_dotProduct, sgn_add, sgn_add,
      dotProduct_comm z v, dotProduct_comm z y]
    ring
  simp_rw [hterm, ← mul_sum, sum_sgn_dotProduct, hnorm_mul_hnorm]
  have hiff : w + y + v = 0 ↔ w = y + v := by
    rw [add_assoc, bits_add_eq_zero_iff]
  by_cases h : w = y + v
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, mul_zero]

/-- `W_k` is its own inverse. -/
theorem hadamard_mul_self (k : ℕ) : hadamard k * hadamard k = 1 := by
  ext a b
  have := sum_hadamard_sgn_hadamard a b 0
  simp only [dotProduct_zero, sgn_zero, one_mul, add_zero] at this
  rw [Matrix.mul_apply, this, Matrix.one_apply]

theorem conjTranspose_hadamard (k : ℕ) : (hadamard k)ᴴ = hadamard k := by
  ext a b
  rw [conjTranspose_apply, hadamard_apply, hadamard_apply, star_mul', star_hnorm, star_sgn,
    dotProduct_comm]

theorem hadamard_mem_unitaryGroup (k : ℕ) : hadamard k ∈ unitaryGroup (Bits k) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_hadamard, hadamard_mul_self]

/-- **First fact** of the proof of Lemma 2 (lines 280–289): `W_k D_v W_k` is the shift
`|y⟩ ↦ |y ⊕ v⟩`, where `D_v |z⟩ = (-1)^{⟨v, z⟩} |z⟩`. -/
theorem hadamard_mul_phase_mul_hadamard {k : ℕ} (v : Bits k) :
    hadamard k * diagonal (fun z => sgn (v ⬝ᵥ z)) * hadamard k = basisMatrix (· + v) := by
  ext w y
  rw [Matrix.mul_apply, basisMatrix_apply, ← sum_hadamard_sgn_hadamard w y v]
  refine sum_congr rfl fun z _ => ?_
  rw [Matrix.mul_diagonal, dotProduct_comm]
  ring

/-- **Second fact** of the proof of Lemma 2 (lines 290–303), phase kickback: conjugating the
standard oracle of `f : U → {0, 1}ᵐ` by `W_m` on the target register gives the phase oracle
`|u, t⟩ ↦ (-1)^{⟨t, f(u)⟩} |u, t⟩`. -/
theorem phase_kickback {U : Type*} [Fintype U] [DecidableEq U] {m : ℕ} (f : U → Bits m) :
    ((1 : Matrix U U ℂ) ⊗ₖ hadamard m) * oracleUnitary f * ((1 : Matrix U U ℂ) ⊗ₖ hadamard m) =
      diagonal fun ut => sgn (ut.2 ⬝ᵥ f ut.1) := by
  ext ⟨u, t⟩ ⟨u', t'⟩
  rw [oracleUnitary, Matrix.mul_apply]
  simp only [mul_basisMatrix_apply, kroneckerMap_apply, oracleEquiv_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Matrix.diagonal_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single u (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  by_cases hu : u = u'
  · subst hu
    simp only [ite_true, true_and, one_mul, hadamard_apply_add, mul_assoc, ← mul_sum]
    rw [← Matrix.mul_apply, hadamard_mul_self, Matrix.one_apply]
    split_ifs <;> simp_all
  · simp [hu]

/-! ### The circuit -/

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [AddCommGroup U]
  {n m : ℕ}

/-- The register `((u, t), ((x, y), c))`: the query register `(u, t)` of `f`, the query register
`(x, y)` of `H`, and the ancilla `c`. -/
abbrev Reg (X U : Type*) (n m : ℕ) := (U × Bits m) × ((X × Bits n) × Bits m)

/-- The selection oracle `H(x) = h(x) ⊕ L_x(f(s(x)))`, equation (1) of the paper. -/
def selectionOracle (s : X → U) (h : X → Bits n) (L : X → Matrix (Fin n) (Fin m) (ZMod 2))
    (f : U → Bits m) : X → Bits n := fun x => h x + L x *ᵥ f (s x)

/-- Step 1, first half: `y ↦ y ⊕ h(x)`. -/
def σ₁ (h : X → Bits n) : Equiv.Perm (Reg X U n m) where
  toFun r := (r.1, ((r.2.1.1, r.2.1.2 + h r.2.1.1), r.2.2))
  invFun r := (r.1, ((r.2.1.1, r.2.1.2 - h r.2.1.1), r.2.2))
  left_inv r := by simp
  right_inv r := by simp

/-- Steps 2 and 3, first half: `c ↦ c ⊕ L_xᵀ z`, `u ↦ u + s(x)`, then `t ↦ t ⊕ c`. -/
def σ₂ (s : X → U) (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) : Equiv.Perm (Reg X U n m) where
  toFun r := ((r.1.1 + s r.2.1.1, r.1.2 + (r.2.2 + (L r.2.1.1)ᵀ *ᵥ r.2.1.2)),
    ((r.2.1.1, r.2.1.2), r.2.2 + (L r.2.1.1)ᵀ *ᵥ r.2.1.2))
  invFun r := ((r.1.1 - s r.2.1.1, r.1.2 - r.2.2),
    ((r.2.1.1, r.2.1.2), r.2.2 - (L r.2.1.1)ᵀ *ᵥ r.2.1.2))
  left_inv r := by simp
  right_inv r := by simp

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [AddCommGroup U] in
lemma σ₁_apply (h : X → Bits n) (r : Reg X U n m) :
    σ₁ h r = (r.1, ((r.2.1.1, r.2.1.2 + h r.2.1.1), r.2.2)) := rfl

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] in
lemma σ₂_apply (s : X → U) (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) (r : Reg X U n m) :
    σ₂ s L r = ((r.1.1 + s r.2.1.1, r.1.2 + (r.2.2 + (L r.2.1.1)ᵀ *ᵥ r.2.1.2)),
      ((r.2.1.1, r.2.1.2), r.2.2 + (L r.2.1.1)ᵀ *ᵥ r.2.1.2)) := rfl

/-- `W_n` on the register `y`, the identity elsewhere. -/
noncomputable def yHadamard : Matrix (Reg X U n m) (Reg X U n m) ℂ :=
  (1 : Matrix (U × Bits m) (U × Bits m) ℂ) ⊗ₖ
    (((1 : Matrix X X ℂ) ⊗ₖ hadamard n) ⊗ₖ (1 : Matrix (Bits m) (Bits m) ℂ))

/-- `W_m` on the register `t`, the identity elsewhere. -/
noncomputable def tHadamard : Matrix (Reg X U n m) (Reg X U n m) ℂ :=
  ((1 : Matrix U U ℂ) ⊗ₖ hadamard m) ⊗ₖ (1 : Matrix ((X × Bits n) × Bits m) _ ℂ)

/-- One query to `f` on the register `(u, t)`, the identity on `((x, y), c)`. -/
noncomputable def fQuery (f : U → Bits m) : Matrix (Reg X U n m) (Reg X U n m) ℂ :=
  oracleUnitary f ⊗ₖ (1 : Matrix ((X × Bits n) × Bits m) _ ℂ)

/-- Steps 1–3 of the circuit; does not depend on `f`. -/
noncomputable def prepare (s : X → U) (h : X → Bits n) (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) :
    Matrix (Reg X U n m) (Reg X U n m) ℂ :=
  tHadamard * basisMatrix (σ₂ s L) * yHadamard * basisMatrix (σ₁ h)

/-- Step 5 of the circuit (undo steps 3 and 2, then `W_n` on `y`); does not depend on `f`. -/
noncomputable def finish (s : X → U) (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) :
    Matrix (Reg X U n m) (Reg X U n m) ℂ :=
  yHadamard * basisMatrix (σ₂ s L).symm * tHadamard

/-- The embedding `|x, y⟩ ↦ |(0, 0), ((x, y), 0)⟩` with the ancilla registers at `0`. -/
noncomputable def ancillaEmbed : Matrix (Reg X U n m) (X × Bits n) ℂ :=
  basisMatrix fun a => ((0, 0), (a, 0))

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] in
lemma ancillaEmbed_injective :
    Function.Injective fun a : X × Bits n => (((0 : U), (0 : Bits m)), (a, (0 : Bits m))) :=
  fun a b h => by simpa using h

/-- The embedding is an isometry. -/
theorem conjTranspose_ancillaEmbed_mul_self :
    (ancillaEmbed (X := X) (U := U) (n := n) (m := m))ᴴ *
      ancillaEmbed (X := X) (U := U) (n := n) (m := m) = 1 :=
  conjTranspose_basisMatrix_mul_self (ancillaEmbed_injective (U := U) (m := m))

omit [AddCommGroup U] in
theorem yHadamard_mem_unitaryGroup :
    (yHadamard : Matrix (Reg X U n m) _ ℂ) ∈ unitaryGroup (Reg X U n m) ℂ :=
  kronecker_mem_unitary (one_mem _) (kronecker_mem_unitary
    (kronecker_mem_unitary (one_mem _) (hadamard_mem_unitaryGroup n)) (one_mem _))

omit [AddCommGroup U] in
theorem tHadamard_mem_unitaryGroup :
    (tHadamard : Matrix (Reg X U n m) _ ℂ) ∈ unitaryGroup (Reg X U n m) ℂ :=
  kronecker_mem_unitary (kronecker_mem_unitary (one_mem _) (hadamard_mem_unitaryGroup m))
    (one_mem _)

theorem prepare_mem_unitaryGroup (s : X → U) (h : X → Bits n)
    (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) :
    prepare s h L ∈ unitaryGroup (Reg X U n m) ℂ :=
  mul_mem (mul_mem (mul_mem tHadamard_mem_unitaryGroup (basisMatrix_perm_mem_unitaryGroup _))
    yHadamard_mem_unitaryGroup) (basisMatrix_perm_mem_unitaryGroup _)

theorem finish_mem_unitaryGroup (s : X → U) (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) :
    finish s L ∈ unitaryGroup (Reg X U n m) ℂ :=
  mul_mem (mul_mem yHadamard_mem_unitaryGroup (basisMatrix_perm_mem_unitaryGroup _))
    tHadamard_mem_unitaryGroup

/-! ### Proof of Lemma 2 -/

omit [AddCommGroup U] in
/-- Steps 3–4 and the undoing of step 3: `W_m O_f W_m` on `(u, t)` is the phase
`(-1)^{⟨t, f(u)⟩}` (second fact). -/
lemma tHadamard_mul_fQuery_mul_tHadamard (f : U → Bits m) :
    (tHadamard * fQuery f * tHadamard : Matrix (Reg X U n m) _ ℂ) =
      diagonal fun r => sgn (r.1.2 ⬝ᵥ f r.1.1) := by
  rw [tHadamard, fQuery, ← mul_kronecker_mul, ← mul_kronecker_mul, phase_kickback, mul_one,
    mul_one, ← diagonal_one, diagonal_kronecker_diagonal]
  simp

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [AddCommGroup U] in
/-- Conjugating a diagonal matrix by a permutation relabels its entries. -/
lemma basisMatrix_symm_mul_diagonal_mul_basisMatrix {R : Type*} [Fintype R] [DecidableEq R]
    (σ : Equiv.Perm R) (d : R → ℂ) :
    basisMatrix σ.symm * diagonal d * basisMatrix σ = diagonal (d ∘ σ) := by
  ext a b
  rw [mul_basisMatrix_apply, basisMatrix_equiv_mul_apply, Equiv.symm_symm, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [ite_eq_right (σ.injective.ne hab), ite_eq_right hab]

omit [AddCommGroup U] in
lemma yHadamard_mulVec (v : Reg X U n m → ℂ) (r : Reg X U n m) :
    (yHadamard *ᵥ v) r = ∑ z, hadamard n r.2.1.2 z * v (r.1, ((r.2.1.1, z), r.2.2)) := by
  obtain ⟨⟨u, t⟩, ⟨⟨x, y⟩, c⟩⟩ := r
  rw [yHadamard, mulVec, dotProduct]
  simp [Matrix.one_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

/-- **Lemma 2** (One query per selection, Undetectability lines 262–269) on basis states: the
circuit `finish s L * fQuery f * prepare s h L`, whose only dependence on `f` is one query
`fQuery f`, maps `|x, y⟩|0⟩` to `|x, y ⊕ H(x)⟩|0⟩` for `H = selectionOracle s h L f`. -/
theorem selection_mulVec_single (s : X → U) (h : X → Bits n)
    (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) (f : U → Bits m) (x : X) (y : Bits n) :
    (finish s L * fQuery f * prepare s h L) *ᵥ (Pi.single ((0, 0), ((x, y), 0)) 1 : Reg X U n m → ℂ) =
      Pi.single ((0, 0), ((x, y + selectionOracle s h L f x), 0)) 1 := by
  have hC : finish s L * fQuery f * prepare s h L =
      yHadamard * (basisMatrix (σ₂ s L).symm * (tHadamard * fQuery f * tHadamard) *
        basisMatrix (σ₂ s L)) * yHadamard * basisMatrix (σ₁ (U := U) (m := m) h) := by
    simp only [finish, prepare, Matrix.mul_assoc]
  rw [hC, tHadamard_mul_fQuery_mul_tHadamard, basisMatrix_symm_mul_diagonal_mul_basisMatrix,
    ← mulVec_mulVec, basisMatrix_mulVec_single, ← mulVec_mulVec, ← mulVec_mulVec]
  ext ⟨⟨u, t⟩, ⟨⟨x', w⟩, c⟩⟩
  simp only [yHadamard_mulVec, mulVec_diagonal, Function.comp_apply, σ₁_apply]
  by_cases hr : u = 0 ∧ t = 0 ∧ x = x' ∧ c = 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
    have hin : ∀ z, ∑ z', hadamard n z z' *
        (Pi.single (((0 : U), (0 : Bits m)), ((x, y + h x), (0 : Bits m))) (1 : ℂ) :
          Reg X U n m → ℂ) ((0, 0), ((x, z'), 0)) = hadamard n z (y + h x) := fun z => by
      simp [Pi.single_apply]
    have hphase : ∀ z : Bits n,
        ((σ₂ s L) (((0 : U), (0 : Bits m)), ((x, z), (0 : Bits m)))).1.2 ⬝ᵥ
          f ((σ₂ s L) (((0 : U), (0 : Bits m)), ((x, z), (0 : Bits m)))).1.1 =
        z ⬝ᵥ (L x *ᵥ f (s x)) := fun z => by
      rw [σ₂_apply]
      simp only [zero_add, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    simp only [hin, hphase]
    rw [sum_hadamard_sgn_hadamard]
    simp [Pi.single_apply, selectionOracle, add_assoc]
  · have hne : ∀ z' : Bits n, ((u, t), ((x', z'), c)) ≠
        ((((0 : U), (0 : Bits m)), ((x, y + h x), (0 : Bits m))) : Reg X U n m) := by
      intro z' he
      simp only [Prod.mk.injEq] at he
      exact hr ⟨he.1.1, he.1.2, he.2.1.1.symm, he.2.2⟩
    have hin : ∀ z, ∑ z', hadamard n z z' *
        (Pi.single (((0 : U), (0 : Bits m)), ((x, y + h x), (0 : Bits m))) (1 : ℂ) :
          Reg X U n m → ℂ) ((u, t), ((x', z'), c)) = 0 := fun z =>
      sum_eq_zero fun z' _ => by rw [Pi.single_apply, ite_eq_right (hne z'), mul_zero]
    simp only [hin, mul_zero, sum_const_zero]
    rw [Pi.single_apply, ite_eq_right]
    intro he
    simp only [Prod.mk.injEq] at he
    exact hr ⟨he.1.1, he.1.2, he.2.1.1.symm, he.2.2⟩

/-- **Lemma 2** (One query per selection) as an operator identity: on the subspace where the
ancilla registers are `0`, the circuit with one query to `f` is the standard oracle of
`H = selectionOracle s h L f`, and it returns the ancillas to `0`. -/
theorem selection_mul_ancillaEmbed (s : X → U) (h : X → Bits n)
    (L : X → Matrix (Fin n) (Fin m) (ZMod 2)) (f : U → Bits m) :
    finish s L * fQuery f * prepare s h L * ancillaEmbed =
      (ancillaEmbed : Matrix (Reg X U n m) (X × Bits n) ℂ) *
        oracleUnitary (selectionOracle s h L f) := by
  ext r ⟨x, y⟩
  have hcol := congrFun (selection_mulVec_single s h L f x y) r
  rw [Matrix.mulVec_single_one] at hcol
  rw [ancillaEmbed, mul_basisMatrix_apply, oracleUnitary, ← basisMatrix_comp]
  refine hcol.trans ?_
  rw [Pi.single_apply, basisMatrix_apply]
  congr 1

/-- **Lemma 2** for GF(2)-linear maps `L_x : {0, 1}ᵐ → {0, 1}ⁿ`, through their matrices. -/
theorem selection_one_query_linearMap (s : X → U) (h : X → Bits n)
    (L : X → (Bits m →ₗ[ZMod 2] Bits n)) (f : U → Bits m) :
    finish s (fun x => LinearMap.toMatrix' (L x)) * fQuery f *
        prepare s h (fun x => LinearMap.toMatrix' (L x)) * ancillaEmbed =
      (ancillaEmbed : Matrix (Reg X U n m) (X × Bits n) ℂ) *
        oracleUnitary fun x => h x + L x (f (s x)) := by
  have hH : selectionOracle s h (fun x => LinearMap.toMatrix' (L x)) f =
      fun x => h x + L x (f (s x)) :=
    funext fun x => congrArg (h x + ·) (LinearMap.toMatrix'_mulVec (L x) (f (s x)))
  rw [selection_mul_ancillaEmbed, hH]

/-- **Selection between two values** (lines 374–377): `H(x) = a(x)` if `f(s(x)) = 1` and
`H(x) = b(x)` otherwise is the case `m = 1`, `h = b`, `L_x β = β · (a(x) ⊕ b(x))`. -/
theorem selection_two_values (s : X → U) (a b : X → Bits n) (f : U → Bits 1) :
    finish s (fun x => Matrix.of fun i _ => a x i + b x i) * fQuery f *
        prepare s b (fun x => Matrix.of fun i _ => a x i + b x i) * ancillaEmbed =
      (ancillaEmbed : Matrix (Reg X U n 1) (X × Bits n) ℂ) *
        oracleUnitary fun x => if f (s x) 0 = 1 then a x else b x := by
  have hH : selectionOracle s b (fun x => Matrix.of fun i _ => a x i + b x i) f =
      fun x => if f (s x) 0 = 1 then a x else b x := by
    funext x i
    simp only [selectionOracle, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Fin.sum_univ_one]
    rw [ite_apply]
    exact (by decide : ∀ p q β : ZMod 2, q + (p + q) * β = if β = 1 then p else q) _ _ _
  rw [selection_mul_ancillaEmbed, hH]

end ShrincsSecurity.Undetectability.Selection
