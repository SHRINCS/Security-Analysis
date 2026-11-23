module

public import ShrincsSecurity.Undetectability.Poly.PlantedFamily

/-!
# The Boolean planted family and events on few points

Undetectability paper (`notes/txt/Undetectability.txt`):

* Section 4.1 (lines 528–553): for a finite set `M` with `N := |M|`, the distribution `D_λ` of a
  random `f : M → {0, 1}` marking every point independently with probability `λ`, the uniform
  distributions `E_k` on the slices `S_k` of functions of Hamming weight `k`, and the mixture
  identity (3), `D_λ = ∑_k b_{N,k}(λ) E_k`.
* **Lemma 14** (Events on few points, lines 880–922): for points `x₁, …, x_t ∈ M`, not necessarily
  distinct, and `B ⊆ {0, 1}^t`, `Pr_{f ← D_λ}[(f(x₁), …, f(x_t)) ∈ B]` is a real polynomial in `λ`
  of degree at most `t`.
* **Lemma 7 for the Boolean family**: `boolean_planted_family`, the step of **Lemma 8**
  (lines 556–600) after its polynomial-degree argument.

## Modelling choices

Bits are `Bool`. Distributions on the finite set `M → Bool` are given by explicit weights:
`boolWeight x f = x^{|f|} (1 - x)^{N - |f|}` is `Pr_{D_x}[f]` and `sliceWeight k f` is
`Pr_{E_k}[f]`; `boolExpect x F` and `sliceExpect k F` are the corresponding expectations of a
real function `F` (the acceptance probability of a possibly randomised algorithm on oracle `f`).

Lemma 14 is proved for every real `λ` (not only `[0, 1]`), and in the stronger form
`natDegree_boolExpectPoly_comp_le`: the expectation of any function of `(f(x_i))_{i ∈ ι}` is a
polynomial of degree at most `|ι|`. The proof factors the product measure over the points of `M`
instead of enumerating consistent assignments on the distinct points as in the paper; points
outside `{x_i}` contribute the factor `λ + (1 - λ) = 1`, a point of `{x_i}` a factor of degree at
most `1`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Polynomial Finset

variable {M : Type*} [Fintype M] [DecidableEq M]

/-! ### `D_λ` -/

/-- The factor `λ` (marked) or `1 - λ` (unmarked) of one point, as a polynomial in `λ`. -/
noncomputable def bitPoly (v : Bool) : ℝ[X] := if v then X else 1 - X

/-- `Pr_{f ← D_λ}[f]` as a polynomial in `λ`: `∏_y (λ if f(y) = 1 else 1 - λ)`. -/
noncomputable def boolWeightPoly (f : M → Bool) : ℝ[X] := ∏ y, bitPoly (f y)

/-- `Pr_{f ← D_x}[f] = ∏_y (x if f(y) = 1 else 1 - x)` (line 536). -/
noncomputable def boolWeight (x : ℝ) (f : M → Bool) : ℝ := ∏ y, if f y then x else 1 - x

omit [DecidableEq M] in
lemma eval_boolWeightPoly (x : ℝ) (f : M → Bool) :
    (boolWeightPoly f).eval x = boolWeight x f := by
  simp only [boolWeightPoly, boolWeight, eval_prod, bitPoly]
  exact prod_congr rfl fun y _ => by cases f y <;> simp

omit [DecidableEq M] in
lemma boolWeight_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (f : M → Bool) :
    0 ≤ boolWeight x f :=
  prod_nonneg fun y _ => by split <;> linarith [hx.1, hx.2]

lemma sum_boolWeight (x : ℝ) : ∑ f : M → Bool, boolWeight x f = 1 := by
  have := Fintype.prod_sum (R := ℝ) (κ := fun _ : M => Bool) fun _ v => if v then x else 1 - x
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_sub_cancel,
    prod_const_one] at this
  exact this.symm

/-- `𝔼_{f ← D_x}[F(f)]`. -/
noncomputable def boolExpect (x : ℝ) (F : (M → Bool) → ℝ) : ℝ := ∑ f, boolWeight x f * F f

/-- `Pr_{f ← D_x}[f ∈ E]`. -/
noncomputable def boolProb (x : ℝ) (E : Set (M → Bool)) : ℝ := boolExpect x (E.indicator 1)

/-- `𝔼_{f ← D_λ}[F(f)]` as a polynomial in `λ`. -/
noncomputable def boolExpectPoly (F : (M → Bool) → ℝ) : ℝ[X] := ∑ f, C (F f) * boolWeightPoly f

lemma eval_boolExpectPoly (x : ℝ) (F : (M → Bool) → ℝ) :
    (boolExpectPoly F).eval x = boolExpect x F := by
  simp [boolExpectPoly, boolExpect, eval_finsetSum, eval_boolWeightPoly, mul_comm]

lemma boolExpect_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {F : (M → Bool) → ℝ} (hF : ∀ f, F f ∈ Set.Icc (0 : ℝ) 1) :
    boolExpect x F ∈ Set.Icc (0 : ℝ) 1 := by
  unfold boolExpect
  refine ⟨sum_nonneg fun f _ => mul_nonneg (boolWeight_nonneg hx f) (hF f).1, ?_⟩
  calc ∑ f, boolWeight x f * F f ≤ ∑ f, boolWeight x f :=
        sum_le_sum fun f _ => mul_le_of_le_one_right (boolWeight_nonneg hx f) (hF f).2
    _ = 1 := sum_boolWeight x

/-! ### Lemma 14 -/

section Lemma14

variable {ι : Type*} [Fintype ι]

/-- The indicator `∏_{i : x_i = y} 1[v = b_i]` that the value `v` of `f` at `y` is consistent with
the prescribed values `b` at the points `x_i = y`. -/
noncomputable def fiberInd (pts : ι → M) (b : ι → Bool) (y : M) (v : Bool) : ℝ :=
  ∏ i ∈ univ.filter (fun i => pts i = y), if v = b i then 1 else 0

/-- The contribution `∑_v 1[v consistent at y] · (λ or 1 - λ)` of the point `y`. -/
noncomputable def pointPoly (pts : ι → M) (b : ι → Bool) (y : M) : ℝ[X] :=
  ∑ v : Bool, C (fiberInd pts b y v) * bitPoly v

lemma prod_ind_eq_prod_fiberInd (pts : ι → M) (b : ι → Bool) (f : M → Bool) :
    (∏ i, if f (pts i) = b i then (1 : ℝ) else 0) = ∏ y, fiberInd pts b y (f y) := by
  rw [← prod_fiberwise univ pts]
  refine prod_congr rfl fun y _ => prod_congr rfl fun i hi => ?_
  rw [(mem_filter.mp hi).2]

/-- `Pr_{f ← D_λ}[f(x_i) = b_i for all i]` factors over the points of `M`. -/
lemma sum_ind_mul_boolWeightPoly (pts : ι → M) (b : ι → Bool) :
    ∑ f : M → Bool, C (∏ i, if f (pts i) = b i then (1 : ℝ) else 0) * boolWeightPoly f =
      ∏ y, pointPoly pts b y := by
  simp only [pointPoly, Fintype.prod_sum (κ := fun _ : M => Bool), prod_ind_eq_prod_fiberInd,
    boolWeightPoly, map_prod, ← prod_mul_distrib]

omit [Fintype M] in
lemma natDegree_pointPoly_le (pts : ι → M) (b : ι → Bool) (y : M) :
    (pointPoly pts b y).natDegree ≤ 1 := by
  have : pointPoly pts b y =
      C (fiberInd pts b y true - fiberInd pts b y false) * X + C (fiberInd pts b y false) := by
    simp only [pointPoly, Fintype.sum_bool, bitPoly, ite_true, Bool.false_eq_true, ite_false,
      map_sub]
    ring
  rw [this]
  exact natDegree_linear_le

omit [Fintype M] in
lemma pointPoly_eq_one (pts : ι → M) (b : ι → Bool) {y : M} (hy : y ∉ Set.range pts) :
    pointPoly pts b y = 1 := by
  have hfilter : univ.filter (fun i => pts i = y) = ∅ :=
    filter_eq_empty_iff.mpr fun i _ h => hy ⟨i, h⟩
  simp [pointPoly, fiberInd, hfilter, bitPoly]

/-- **Lemma 14, general form.** For points `x_i ∈ M` (`i ∈ ι`, not necessarily distinct) and any
`G : {0,1}^ι → ℝ`, `λ ↦ 𝔼_{f ← D_λ}[G((f(x_i))_i)]` is a polynomial of degree at most `|ι|`. -/
theorem natDegree_boolExpectPoly_comp_le (pts : ι → M) (G : (ι → Bool) → ℝ) :
    (boolExpectPoly fun f => G fun i => f (pts i)).natDegree ≤ Fintype.card ι := by
  classical
  -- `G (f ∘ x) = ∑_b G b · ∏_i 1[f(x_i) = b_i]`
  have hG : ∀ f : M → Bool, G (fun i => f (pts i)) =
      ∑ b : ι → Bool, G b * ∏ i, if f (pts i) = b i then (1 : ℝ) else 0 := fun f => by
    rw [sum_eq_single (fun i => f (pts i))]
    · simp
    · intro b _ hb
      obtain ⟨i, hi⟩ : ∃ i, f (pts i) ≠ b i := by
        by_contra! h; exact hb (funext fun i => (h i).symm)
      rw [prod_eq_zero (mem_univ i) (ite_eq_right hi), mul_zero]
    · simp
  have hpoly : (boolExpectPoly fun f => G fun i => f (pts i)) =
      ∑ b : ι → Bool, C (G b) * ∏ y, pointPoly pts b y := by
    simp only [boolExpectPoly, hG, map_sum, map_mul, sum_mul, ← sum_ind_mul_boolWeightPoly,
      mul_sum, mul_assoc]
    rw [sum_comm]
  rw [hpoly]
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  rw [← sum_subset (subset_univ (univ.image pts)) fun y _ hy => by
    rw [pointPoly_eq_one pts b fun ⟨i, hi⟩ => hy (mem_image.mpr ⟨i, mem_univ i, hi⟩),
      natDegree_one]]
  calc ∑ y ∈ univ.image pts, (pointPoly pts b y).natDegree
      ≤ ∑ _y ∈ univ.image pts, 1 := sum_le_sum fun y _ => natDegree_pointPoly_le pts b y
    _ = (univ.image pts).card := by simp
    _ ≤ Fintype.card ι := card_image_le

/-- **Lemma 14 (Events on few points)**, Undetectability lines 880–922. Let `x_i ∈ M` for `i ∈ ι`,
not necessarily distinct, and `B ⊆ {0, 1}^ι`. Then `Pr_{f ← D_λ}[(f(x_i))_i ∈ B]` is a real
polynomial in `λ` of degree at most `|ι|` (for every real `λ`). -/
theorem events_on_few_points (pts : ι → M) (B : Set (ι → Bool)) :
    ∃ Q : ℝ[X], Q.natDegree ≤ Fintype.card ι ∧
      ∀ x : ℝ, boolProb x {f | (fun i => f (pts i)) ∈ B} = Q.eval x := by
  refine ⟨_, natDegree_boolExpectPoly_comp_le pts (B.indicator 1), fun x => ?_⟩
  rw [eval_boolExpectPoly]
  rfl

/-- **Lemma 14** for a tuple `x₁, …, x_t` (`ι = Fin t`): degree at most `t`. -/
theorem events_on_few_points_fin {t : ℕ} (pts : Fin t → M) (B : Set (Fin t → Bool)) :
    ∃ Q : ℝ[X], Q.natDegree ≤ t ∧
      ∀ x : ℝ, boolProb x {f | (fun i => f (pts i)) ∈ B} = Q.eval x := by
  simpa using events_on_few_points pts B

end Lemma14

/-! ### The slices `E_k` and the mixture identity (3) -/

section Slices
/-- The Hamming weight `|f|`, the number of marked points. -/
def markCount (f : M → Bool) : ℕ := (univ.filter fun y => f y = true).card

omit [DecidableEq M] in
lemma markCount_le (f : M → Bool) : markCount f ≤ Fintype.card M :=
  card_filter_le _ _

/-- `Pr_{f ← E_k}[f]`: `E_k` is uniform on the slice `S_k` of functions of weight `k`, which has
`C(N, k)` elements (line 530). -/
noncomputable def sliceWeight (k : ℕ) (f : M → Bool) : ℝ :=
  if markCount f = k then ((Fintype.card M).choose k : ℝ)⁻¹ else 0

/-- `𝔼_{f ← E_k}[F(f)]`. -/
noncomputable def sliceExpect (k : ℕ) (F : (M → Bool) → ℝ) : ℝ := ∑ f, sliceWeight k f * F f

omit [DecidableEq M] in
lemma boolWeight_eq (x : ℝ) (f : M → Bool) :
    boolWeight x f = x ^ markCount f * (1 - x) ^ (Fintype.card M - markCount f) := by
  have hcard := card_filter_add_card_filter_not (s := univ) fun y => f y = true
  rw [card_univ] at hcard
  rw [boolWeight, prod_ite, prod_const, prod_const, markCount]
  congr 2
  omega

omit [DecidableEq M] in
/-- **Equation (3)** at the level of point masses (lines 540–546):
`Pr_{D_x}[f] = ∑_{k ≤ N} b_{N,k}(x) Pr_{E_k}[f]`. -/
theorem boolWeight_eq_mixture (x : ℝ) (f : M → Bool) :
    boolWeight x f = ∑ k ∈ range (Fintype.card M + 1), binomWeight (Fintype.card M) k x *
      sliceWeight k f := by
  rw [sum_eq_single (markCount f)]
  · have hpos : (0 : ℝ) < (Fintype.card M).choose (markCount f) := by
      exact_mod_cast Nat.choose_pos (markCount_le f)
    rw [binomWeight_eq, sliceWeight, ite_eq_left rfl, boolWeight_eq]
    field_simp
  · intro k _ hk
    rw [sliceWeight, ite_eq_right (Ne.symm hk), mul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_of_le (markCount_le f))) h

/-- **Equation (3)** for expectations: `𝔼_{D_x}[F] = ∑_{k ≤ N} b_{N,k}(x) 𝔼_{E_k}[F]`. -/
theorem boolExpect_eq_mixture (x : ℝ) (F : (M → Bool) → ℝ) :
    boolExpect x F = ∑ k ∈ range (Fintype.card M + 1), binomWeight (Fintype.card M) k x *
      sliceExpect k F := by
  simp only [boolExpect, sliceExpect, boolWeight_eq_mixture, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]

/-- `E₀` is the point mass at the all-zero function. -/
theorem sliceExpect_zero (F : (M → Bool) → ℝ) : sliceExpect 0 F = F fun _ => false := by
  rw [sliceExpect, sum_eq_single fun _ => false]
  · simp [sliceWeight, markCount]
  · intro f _ hf
    have : markCount f ≠ 0 := by
      intro h
      refine hf (funext fun y => ?_)
      have := card_eq_zero.mp h
      rw [filter_eq_empty_iff] at this
      simpa using this (mem_univ y)
    simp [sliceWeight, this]
  · simp

/-- The function with the single marked point `y`. -/
def singleMark (y : M) : M → Bool := fun z => decide (z = y)

omit [Fintype M] in
lemma singleMark_injective : Function.Injective (singleMark (M := M)) := fun y y' h => by
  simpa [singleMark] using congrFun h y

lemma markCount_eq_one_iff (f : M → Bool) : markCount f = 1 ↔ ∃ y, singleMark y = f := by
  rw [markCount, card_eq_one]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, funext fun z => ?_⟩
    have := congrArg (z ∈ ·) hy
    simp only [mem_filter, mem_univ, true_and, mem_singleton, eq_iff_iff] at this
    cases h : f z <;> simp_all [singleMark]
  · rintro ⟨y, rfl⟩
    exact ⟨y, by ext z; simp [singleMark]⟩

/-- `E₁` is the distribution of the function with one uniformly random marked point. -/
theorem sliceExpect_one (F : (M → Bool) → ℝ) :
    sliceExpect 1 F = (Fintype.card M : ℝ)⁻¹ * ∑ y, F (singleMark y) := by
  have hfilter : univ.filter (fun f : M → Bool => markCount f = 1) =
      univ.map ⟨singleMark, singleMark_injective⟩ := by
    ext f; simp [markCount_eq_one_iff]
  simp only [sliceExpect, sliceWeight, Nat.choose_one_right, ite_mul, zero_mul]
  rw [← sum_filter, hfilter, sum_map, mul_sum]
  rfl

/-- **Lemma 7 for the Boolean family** (the last step of the proof of Lemma 8, lines 573 and
600): let `N = |M| ≥ 1` and let `F(f) ∈ [0, 1]` be the acceptance probability of an algorithm with
oracle `f`. If `λ ↦ 𝔼_{f ← D_λ}[F(f)]` coincides on `[0, 1]` with a real polynomial of degree at
most `d`, then `|𝔼_{E₁}[F] - 𝔼_{E₀}[F]| ≤ d² / N`. -/
theorem boolean_planted_family {d : ℕ} (hM : 1 ≤ Fintype.card M) {F : (M → Bool) → ℝ}
    (hF : ∀ f, F f ∈ Set.Icc (0 : ℝ) 1)
    (hg : IsPolyOnUnitInterval (fun x => boolExpect x F) d) :
    |sliceExpect 1 F - sliceExpect 0 F| ≤ (d : ℝ) ^ 2 / Fintype.card M :=
  planted_family_of_bounded (p := fun k => sliceExpect k F) hM
    (fun x hx => by rw [← boolExpect_eq_mixture]; exact boolExpect_mem_Icc hx hF)
    (hg.congr fun x _ => boolExpect_eq_mixture x F)

end Slices

end ShrincsSecurity.Undetectability
