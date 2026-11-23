module

public import ShrincsSecurity.Undetectability.Poly.Acceptance

/-!
# Functions of an oracle that are linear in its `t`-point marginals

Undetectability paper (`notes/txt/Undetectability.txt`), proof of **Lemma 1** (lines 199–230).
The proof expands the state of a query algorithm as a combination of products of indicators
`δ_{x,r}(H) = 1[H(x) = r]` with coefficients that depend only on the algorithm. This file sets up
that bookkeeping for values in an arbitrary real vector space `V` (density matrices, their entries,
probabilities):

* `IsMarginalPoly F t`: `F H = ∑_{(x,r) ∈ s} 1[H(x_i) = r_i ∀ i ∈ [t]] • c_{x,r}` for a finite set
  `s ⊆ X^t × Y^t` and vectors `c_{x,r} ∈ V` independent of `H`. For `V = ℝ` this is
  `IsMarginalLinear` (`isMarginalPoly_iff_isMarginalLinear`).
* Closure properties: constants have `t = 0`; sums, real multiples and real-linear images keep `t`;
  the product of a scalar function with `a` points and a vector function with `b` points has
  `a + b` points (`IsMarginalPoly.smul`, the concatenation of the two index tuples, the step
  "each term is a product of `2q'` factors `δ`" of the proof); a single indicator has one point, or
  two points by `δ² = δ` (`isMarginalPoly_indicator_two`).
* `IsMarginalPoly.mono`: padding from `t` to `t' ≥ t` points (the last step of the proof). For
  `t ≥ 1` it repeats a pair; for `t = 0` it uses `1 = ∑_r δ_{x,r}(H)` and needs a point of `X` and
  finitely many values `Y`, as the paper does.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Finset

variable {X Y V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- `F : (X → Y) → V` is a fixed real combination of the `t`-point marginal indicators
`1[H(x_i) = r_i for all i ∈ [t]]`: there are finitely many tuples `(x, r) ∈ X^t × Y^t` and vectors
`c_{x,r} ∈ V`, independent of `H`, with `F H = ∑ 1[H(x_i) = r_i ∀ i] • c_{x,r}`. -/
def IsMarginalPoly (F : (X → Y) → V) (t : ℕ) : Prop :=
  ∃ (s : Finset ((Fin t → X) × (Fin t → Y))) (c : (Fin t → X) × (Fin t → Y) → V),
    ∀ H, F H = ∑ xr ∈ s, marginalInd xr.1 xr.2 H • c xr

/-- For real-valued functions, `IsMarginalPoly` is the conclusion of Lemma 1. -/
theorem isMarginalPoly_iff_isMarginalLinear {acc : (X → Y) → ℝ} {t : ℕ} :
    IsMarginalPoly acc t ↔ IsMarginalLinear acc t := by
  simp only [IsMarginalPoly, IsMarginalLinear, smul_eq_mul, mul_comm]

lemma marginalInd_append {a b : ℕ} (x : Fin a → X) (x' : Fin b → X) (r : Fin a → Y)
    (r' : Fin b → Y) (H : X → Y) :
    marginalInd (Fin.append x x') (Fin.append r r') H = marginalInd x r H * marginalInd x' r' H := by
  have : (∀ i, H (Fin.append x x' i) = Fin.append r r' i) ↔
      (∀ i, H (x i) = r i) ∧ ∀ j, H (x' j) = r' j := by
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (Fin.castAdd b i), fun j => by simpa using h (Fin.natAdd a j)⟩
    · rintro ⟨h₁, h₂⟩ i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa using h₁ i
      · simpa using h₂ j
  unfold marginalInd
  by_cases hall : ∀ i, H (Fin.append x x' i) = Fin.append r r' i
  · obtain ⟨h₁, h₂⟩ := this.mp hall
    rw [ite_eq_left hall, ite_eq_left h₁, ite_eq_left h₂, mul_one]
  · rw [ite_eq_right hall]
    by_cases h₁ : ∀ i, H (x i) = r i
    · rw [ite_eq_left h₁, ite_eq_right fun h₂ => hall (this.mpr ⟨h₁, h₂⟩), mul_zero]
    · rw [ite_eq_right h₁, zero_mul]

lemma marginalInd_snoc_zero {t : ℕ} (x : Fin (t + 1) → X) (r : Fin (t + 1) → Y) (H : X → Y) :
    marginalInd (Fin.snoc x (x 0) : Fin (t + 2) → X) (Fin.snoc r (r 0)) H = marginalInd x r H := by
  have : (∀ i : Fin (t + 2), H ((Fin.snoc x (x 0) : Fin (t + 2) → X) i) =
      (Fin.snoc r (r 0) : Fin (t + 2) → Y) i) ↔ ∀ i, H (x i) = r i := by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact ⟨fun h => h.1, fun h => ⟨h, h 0⟩⟩
  unfold marginalInd
  by_cases h : ∀ i, H (x i) = r i
  · rw [ite_eq_left (this.mpr h), ite_eq_left h]
  · rw [ite_eq_right fun h' => h (this.mp h'), ite_eq_right h]

namespace IsMarginalPoly

variable {F G : (X → Y) → V} {t : ℕ}

/-- A combination indexed by any finite family of tuples, possibly with repetitions, can be
regrouped by tuple. -/
theorem of_indexed {ι : Type*} (s : Finset ι) (pt : ι → (Fin t → X) × (Fin t → Y)) (c : ι → V)
    (h : ∀ H, F H = ∑ i ∈ s, marginalInd (pt i).1 (pt i).2 H • c i) : IsMarginalPoly F t := by
  classical
  refine ⟨s.image pt, fun xr => ∑ i ∈ s with pt i = xr, c i, fun H => ?_⟩
  rw [h, ← sum_fiberwise_of_maps_to (g := pt) (t := s.image pt) fun i hi => mem_image_of_mem pt hi]
  refine sum_congr rfl fun xr _ => ?_
  rw [smul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [(mem_filter.mp hi).2]

theorem congr (h : IsMarginalPoly F t) (hFG : ∀ H, F H = G H) : IsMarginalPoly G t := by
  obtain ⟨s, c, hc⟩ := h
  exact ⟨s, c, fun H => (hFG H).symm.trans (hc H)⟩

theorem cast {t' : ℕ} (h : IsMarginalPoly F t) (ht : t = t') : IsMarginalPoly F t' := ht ▸ h

/-- A function that does not depend on the oracle uses no points. -/
theorem const (v : V) : IsMarginalPoly (fun _ : X → Y => v) 0 :=
  ⟨{(Fin.elim0, Fin.elim0)}, fun _ => v, fun H => by
    simp [marginalInd]⟩

theorem zero : IsMarginalPoly (fun _ : X → Y => (0 : V)) t :=
  ⟨∅, fun _ => 0, fun _ => by simp⟩

theorem add (hF : IsMarginalPoly F t) (hG : IsMarginalPoly G t) :
    IsMarginalPoly (fun H => F H + G H) t := by
  classical
  obtain ⟨s, c, hc⟩ := hF
  obtain ⟨s', c', hc'⟩ := hG
  refine of_indexed (s.disjSum s') (Sum.elim id id) (Sum.elim c c') fun H => ?_
  rw [sum_disjSum, hc, hc']
  rfl

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (X → Y) → V}
    (h : ∀ i ∈ s, IsMarginalPoly (F i) t) : IsMarginalPoly (fun H => ∑ i ∈ s, F i H) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsMarginalPoly (fun _ : X → Y => (0 : V)) t)
  | insert i s hi ih =>
    refine ((h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))).congr
      fun H => ?_
    rw [sum_insert hi]

/-- Real-linear images keep the number of points. -/
theorem map (hF : IsMarginalPoly F t) (L : V →ₗ[ℝ] W) : IsMarginalPoly (fun H => L (F H)) t := by
  obtain ⟨s, c, hc⟩ := hF
  exact ⟨s, fun xr => L (c xr), fun H => by simp [hc, map_sum]⟩

theorem const_smul (hF : IsMarginalPoly F t) (a : ℝ) : IsMarginalPoly (fun H => a • F H) t :=
  hF.map (a • LinearMap.id)

/-- **Products** (proof of Lemma 1, line 222): a scalar function with `a` points times a vector
function with `b` points has `a + b` points; the index tuples are concatenated. -/
theorem smul {a b : ℕ} {f : (X → Y) → ℝ} (hf : IsMarginalPoly f a) (hF : IsMarginalPoly F b) :
    IsMarginalPoly (fun H => f H • F H) (a + b) := by
  obtain ⟨s, c, hc⟩ := hf
  obtain ⟨s', c', hc'⟩ := hF
  refine of_indexed (s ×ˢ s')
    (fun p => (Fin.append p.1.1 p.2.1, Fin.append p.1.2 p.2.2)) (fun p => c p.1 • c' p.2)
    fun H => ?_
  rw [hc, hc', sum_smul, sum_product]
  refine sum_congr rfl fun xr _ => ?_
  rw [smul_sum]
  refine sum_congr rfl fun xr' _ => ?_
  rw [marginalInd_append]
  simp only [smul_smul, smul_eq_mul]
  congr 1
  ring

/-- A single indicator `1[H(x) = y]` has one point. -/
theorem indicator [DecidableEq Y] (x : X) (y : Y) :
    IsMarginalPoly (fun H : X → Y => if H x = y then (1 : ℝ) else 0) 1 :=
  ⟨{(fun _ => x, fun _ => y)}, fun _ => 1, fun H => by
    rw [sum_singleton]; by_cases h : H x = y <;> simp [marginalInd, h]⟩

/-- A single indicator `1[H(x) = y] = 1[H(x) = y]²` also has two points (`δ² = δ`). -/
theorem indicator_two [DecidableEq Y] (x : X) (y : Y) :
    IsMarginalPoly (fun H : X → Y => if H x = y then (1 : ℝ) else 0) 2 :=
  ((indicator x y).smul (indicator x y)).congr fun H => by
    split_ifs <;> simp

/-- Repeating one pair adds a point without changing the function. -/
theorem succ (hF : IsMarginalPoly F (t + 1)) : IsMarginalPoly F (t + 2) := by
  obtain ⟨s, c, hc⟩ := hF
  refine of_indexed s (fun xr => (Fin.snoc xr.1 (xr.1 0), Fin.snoc xr.2 (xr.2 0))) c fun H => ?_
  rw [hc]
  simp only [marginalInd_snoc_zero]

/-- The constant `1 = ∑_r 1[H(x) = r]` has one point. -/
theorem one [Nonempty X] [Fintype Y] : IsMarginalPoly (fun _ : X → Y => (1 : ℝ)) 1 := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  refine of_indexed univ (fun y : Y => ((fun _ => x), (fun _ => y))) (fun _ => (1 : ℝ))
    fun H => ?_
  simp only [marginalInd, forall_const, smul_eq_mul, mul_one]
  rw [sum_ite_eq]
  simp

/-- **Padding** (proof of Lemma 1, lines 226–229): a function with `t` points has `t'` points for
every `t' ≥ t`. -/
theorem mono [Nonempty X] [Fintype Y] (hF : IsMarginalPoly F t) {t' : ℕ} (ht : t ≤ t') :
    IsMarginalPoly F t' := by
  induction t', ht using Nat.le_induction with
  | base => exact hF
  | succ n hn ih =>
    rcases n with _ | n
    · exact ((one (X := X) (Y := Y)).smul ih).congr fun H => one_smul ℝ _
    · exact ih.succ

end IsMarginalPoly

end ShrincsSecurity.Undetectability
