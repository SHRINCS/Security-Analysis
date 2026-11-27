module

public import ShrincsSecurity.Undetectability.Marginal.Comb

/-!
# Lemma 8 for quantum combs

Undetectability paper (`notes/txt/Undetectability.txt`), **Lemma 8** (lines 556–600): an
algorithm with `q` queries to the standard oracle of a function `f : M → {0, 1}` distinguishes the
all-zero function from a function with one uniformly random marked point with advantage at most
`4q² / |M|`.

`Poly/Acceptance.lean` proves this conditionally on the conclusion of Lemma 1
(`zero_vs_one_marked_of_marginalLinear`), and `Marginal/Comb.lean` proves Lemma 1 for VCVio
quantum combs (`QuantumComb.isMarginalLinear_outcome`). This file combines the two.

## Bits versus group elements

The conditional statement is about markings `f : M → Bool`, while the comb queries an oracle
`H : M → Y` into an additive group `Y` (`Quantum.oracleUnitary` needs `AddCommGroup`). A marking
`f` is queried through `H = markOracle a f`, the function that is `a` on the marked points and `0`
elsewhere. For `Y = ZMod 2` and `a = 1` this is the standard XOR oracle of `f` itself, the case of
the paper (`QuantumComb.zero_vs_one_marked_zmod2`). Lemma 1 for `H` transfers to `f` because
`b ↦ if b then a else 0` is injective for `a ≠ 0` (`IsMarginalLinear.comp_injective`).

## Main results

* `IsMarginalLinear.comp_injective`: the conclusion of Lemma 1 is preserved when the oracle values
  are encoded by an injective map.
* `QuantumComb.zero_vs_one_marked`: **Lemma 8** for `q`-query combs on `(M × Y) × E`, for any
  nonzero mark value `a : Y`.
* `QuantumComb.zero_vs_one_marked_zmod2`: the case `Y = ZMod 2`, `a = 1` of the paper.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Finset Quantum

/-! ### Encoding oracle values -/

section comp

variable {X Y Z : Type*}

/-- **Lemma 1 under an injective encoding of the values.** If the outcome probability on oracle
`H : X → Y` is linear in the `t`-point marginals of `H`, then the outcome probability on the
oracle `g ∘ f` is linear in the `t`-point marginals of `f : X → Z`, for every injective
`g : Z → Y`. A marginal event `g(f(x_i)) = r_i` is the event `f(x_i) = g⁻¹(r_i)` when every `r_i`
is in the range of `g`, and is empty otherwise. -/
theorem IsMarginalLinear.comp_injective [Nonempty Z] {acc : (X → Y) → ℝ} {t : ℕ}
    (h : IsMarginalLinear acc t) {g : Z → Y} (hg : Function.Injective g) :
    IsMarginalLinear (fun f : X → Z => acc (g ∘ f)) t := by
  classical
  obtain ⟨s, c, hc⟩ := h
  rw [← isMarginalPoly_iff_isMarginalLinear]
  refine IsMarginalPoly.of_indexed s (fun xr => (xr.1, fun i => Function.invFun g (xr.2 i)))
    (fun xr => if ∀ i, xr.2 i ∈ Set.range g then c xr else 0) fun f => ?_
  rw [hc]
  refine sum_congr rfl fun xr _ => ?_
  rw [smul_eq_mul]
  by_cases hr : ∀ i, xr.2 i ∈ Set.range g
  · rw [ite_eq_left hr, mul_comm]
    congr 1
    have : (∀ i, (g ∘ f) (xr.1 i) = xr.2 i) ↔ ∀ i, f (xr.1 i) = Function.invFun g (xr.2 i) :=
      forall_congr' fun i => by
        rw [Function.comp_apply, ← Function.invFun_eq (hr i), hg.eq_iff,
          Function.invFun_eq (hr i)]
    simp only [marginalInd, this]
  · rw [ite_eq_right hr, mul_zero]
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have : ¬ ∀ j, (g ∘ f) (xr.1 j) = xr.2 j := fun hall => hi ⟨f (xr.1 i), hall i⟩
    simp only [marginalInd, ite_eq_right this, mul_zero]

end comp

/-! ### Lemma 8 -/

section lemma8

variable {M Y E : Type*} [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E]

/-- The oracle of a marking `f : M → {0, 1}` with mark value `a`: `a` on the marked points, `0`
elsewhere. For `Y = ZMod 2` and `a = 1` it is `f` read as a function into `ZMod 2`. -/
def markOracle (a : Y) (f : M → Bool) : M → Y := fun x => if f x then a else 0

omit [Fintype M] [DecidableEq M] [Fintype Y] [DecidableEq Y] in
lemma markOracle_false (a : Y) : markOracle a (fun _ : M => false) = 0 := by
  ext x
  simp [markOracle]

omit [Fintype M] [Fintype Y] [DecidableEq Y] in
lemma markOracle_singleMark (a : Y) (y : M) : markOracle a (singleMark y) = Pi.single y a := by
  ext x
  by_cases h : x = y
  · subst h
    simp [markOracle, singleMark]
  · simp [markOracle, singleMark, h]

/-- The probability that the comb `c` outputs `z` with oracle `H`. -/
noncomputable def combOutProb {α : Type*} [MeasurableSpace α] {q : ℕ}
    (c : QuantumComb ((M × Y) × E) α q) (z : α) (H : M → Y) : ℝ :=
  ((c.run (queryStep E H)).outcomeMeasure c.init {z}).toReal

omit [DecidableEq M] [DecidableEq Y] [AddCommGroup Y] in
lemma combOutProb_mem_Icc {α : Type*} [MeasurableSpace α] {q : ℕ}
    (c : QuantumComb ((M × Y) × E) α q) (z : α) (Q : SubInstrument ((M × Y) × E) ((M × Y) × E) Unit) :
    ((c.run Q).outcomeMeasure c.init {z}).toReal ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by
    have h := (MeasureTheory.measure_mono (Set.subset_univ {z})).trans
      (DSubInstrument.outcomeMeasure_apply_univ_le_one (c.run Q) c.init)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h⟩

/-- **Lemma 8** (Undetectability, lines 556–600) for a `q`-query quantum comb on the register
`(M × Y) × E` with the standard oracle `|x, y⟩ ↦ |x, y + H x⟩`: for every outcome `z` and every
mark value `a ≠ 0`, the probability of `z` with one uniformly random marked point
(`H = Pi.single y a` for uniform `y`) differs from that with the zero oracle by at most
`4q² / |M|`. Lemma 1 for combs (`QuantumComb.isMarginalLinear_outcome`) discharges the hypothesis
of `zero_vs_one_marked_of_marginalLinear`. -/
theorem QuantumComb.zero_vs_one_marked {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (hM : 1 ≤ Fintype.card M) {q : ℕ}
    (c : QuantumComb ((M × Y) × E) α q) (z : α) {a : Y} (ha : a ≠ 0) :
    |(Fintype.card M : ℝ)⁻¹ * ∑ y, combOutProb c z (Pi.single y a) - combOutProb c z 0| ≤
      4 * (q : ℝ) ^ 2 / Fintype.card M := by
  have hg : Function.Injective fun b : Bool => if b then a else 0 := by
    intro b b' h
    cases b <;> cases b' <;> simp_all [eq_comm]
  have hlin := (QuantumComb.isMarginalLinear_outcome (E := E) c z).comp_injective hg
  have := zero_vs_one_marked_of_marginalLinear hM
    (acc := fun f => combOutProb c z (markOracle a f))
    (fun f => combOutProb_mem_Icc c z _) hlin
  simpa only [markOracle_singleMark, markOracle_false] using this

/-- **Lemma 8** as printed: `f : M → {0, 1}` with the standard XOR oracle, `Y = ZMod 2`. The
all-zero function and the indicator `Pi.single y 1` of one uniform point `y` are distinguished
with advantage at most `4q² / |M|` by every `q`-query comb. -/
theorem QuantumComb.zero_vs_one_marked_zmod2 {E α : Type*} [Fintype E] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hM : 1 ≤ Fintype.card M) {q : ℕ}
    (c : QuantumComb ((M × ZMod 2) × E) α q) (z : α) :
    |(Fintype.card M : ℝ)⁻¹ * ∑ y, combOutProb c z (Pi.single y 1) - combOutProb c z 0| ≤
      4 * (q : ℝ) ^ 2 / Fintype.card M :=
  QuantumComb.zero_vs_one_marked hM c z one_ne_zero

end lemma8

end ShrincsSecurity.Undetectability
