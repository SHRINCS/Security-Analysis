module

public import ShrincsSecurity.Undetectability.Poly.Boolean

/-!
# The acceptance hypothesis supplied by the quantum degree bound

Undetectability paper (`notes/txt/Undetectability.txt`). This file states, as a predicate, what
the quantum part of the argument must supply, and proves everything downstream of it:

* **Lemma 1** (lines 187–230), for a fixed `q`-query algorithm and outcome: the acceptance
  probability on oracle `H : X → Y` is `∑_{x,r} c_{x,r} 1[H(x_i) = r_i for all i ∈ [2q]]` with
  real coefficients that depend only on the algorithm. This is `IsMarginalLinear acc (2 * q)`.
  Averaging over any finitely supported distribution of `H` gives the printed form
  (`IsMarginalLinear.expect_eq`).
* The oracle of the planted family depends on the random marking `f : M → {0, 1}` through one bit
  per point: `Th(w) = v_w(f(π(w)))` (equation (5), line 930; for Lemma 8 the oracle is `f` itself).
  This is `OneBitPlanting`.
* **Lemma 15** (Degree, lines 923–986) and the polynomial step of **Lemma 8** (lines 581–600):
  under `IsMarginalLinear` with `t = 2q` points, `λ ↦ Pr_{f ← D_λ}[B = 1]` is a polynomial of
  degree at most `2q`, also after averaging over auxiliary randomness `κ` with weights independent
  of `λ` (`isPolyOnUnitInterval_planted_of_marginalLinear`). The proof is Lemma 14.
* **Theorem 16 / Lemma 8, conditional on Lemma 1**: `planted_bound_of_marginalLinear`,
  `|p₁ - p₀| ≤ (2q)² / |M| = 4q² / |M|`, where `p_k` is the acceptance probability when the marked
  set is a uniform `k`-subset of `M`. The remaining inputs of Theorem 16 are Lemma 13 (identifying
  `p₀, p₁` with the two sm-ud worlds) and Lemma 1 itself for the quantum adversary.

## Modelling choices

* An oracle algorithm `B` with a fixed final outcome is represented by its acceptance probability
  `acc : (X → Y) → ℝ` as a function of the (classical, fixed) oracle; the quantum side has to
  prove `IsMarginalLinear acc (2 * q)` for the acceptance probability of its `q`-query programs.
* The sum over `(x, r) ∈ X^{2q} × Y^{2q}` is over a `Finset`, so `X`, `Y` need not be finite.
* Auxiliary randomness `κ` (Lemma 15: `κ = (P', e, e_y, Th')`) is a finitely supported family of
  weights `w κ`, nonnegative and summing to `1`, that do not depend on `λ`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Polynomial Finset

/-! ### Lemma 1 as a predicate -/

section MarginalLinear

variable {X Y : Type*}

/-- The indicator `1[H(x_i) = r_i for all i ∈ [t]]` of a `t`-point marginal event. -/
noncomputable def marginalInd {t : ℕ} (x : Fin t → X) (r : Fin t → Y) (H : X → Y) : ℝ :=
  open Classical in if ∀ i, H (x i) = r i then 1 else 0

/-- **Conclusion of Lemma 1** (Undetectability, lines 187–195) for one algorithm and one final
outcome: the outcome probability `acc H` on oracle `H` is a fixed real linear combination of the
`t`-point marginal indicators `1[H(x_i) = r_i for all i ∈ [t]]`, with coefficients `c_{x,r}` that
do not depend on `H`. Lemma 1 provides this with `t = 2q` for a `q`-query quantum algorithm. -/
def IsMarginalLinear (acc : (X → Y) → ℝ) (t : ℕ) : Prop :=
  ∃ (s : Finset ((Fin t → X) × (Fin t → Y))) (c : (Fin t → X) × (Fin t → Y) → ℝ),
    ∀ H, acc H = ∑ xr ∈ s, c xr * marginalInd xr.1 xr.2 H

/-- The printed form of Lemma 1: for every finitely supported distribution `w` of the oracle,
`Pr_{H ← w}[A outputs z] = ∑_{x,r} c_{x,r} Pr_{H ← w}[H(x_i) = r_i for all i]`, with the same
coefficients for every distribution. -/
theorem IsMarginalLinear.expect_eq {acc : (X → Y) → ℝ} {t : ℕ} (h : IsMarginalLinear acc t) :
    ∃ (s : Finset ((Fin t → X) × (Fin t → Y))) (c : (Fin t → X) × (Fin t → Y) → ℝ),
      ∀ (S : Finset (X → Y)) (w : (X → Y) → ℝ),
        ∑ H ∈ S, w H * acc H = ∑ xr ∈ s, c xr * ∑ H ∈ S, w H * marginalInd xr.1 xr.2 H := by
  obtain ⟨s, c, hc⟩ := h
  refine ⟨s, c, fun S w => ?_⟩
  simp only [hc, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end MarginalLinear

/-! ### One-bit plantings -/

/-- An oracle `W → Y` that depends on the marking `f : M → {0, 1}` through one bit per point:
`(apply f)(w) = val w (f (pt w))`. For the planted family of Appendix A.1 (equation (5),
line 930), `pt (P, T, z) = z - e(T)` and `val (P, T, z) 1 = e_y(T)` if `P = P'`, otherwise
`val (P, T, z) b = Th'(P, T, z)`. -/
structure OneBitPlanting (W M Y : Type*) where
  /-- The point of `M` whose bit the value at `w` reads. -/
  pt : W → M
  /-- The value at `w` as a function of that bit. -/
  val : W → Bool → Y

namespace OneBitPlanting

variable {W M Y : Type*}

/-- The oracle determined by the marking `f`. -/
def apply (Φ : OneBitPlanting W M Y) (f : M → Bool) : W → Y := fun w => Φ.val w (f (Φ.pt w))

/-- The oracle is the marking itself (Section 4.1, Lemma 8). -/
def self (M : Type*) : OneBitPlanting M M Bool := ⟨id, fun _ b => b⟩

@[simp] lemma apply_self (f : M → Bool) : (self M).apply f = f := rfl

end OneBitPlanting

/-! ### Lemma 15 -/

section Degree

variable {W M Y : Type*} [Fintype M] [DecidableEq M]

lemma boolExpect_sum_mul {K : Type*} (s : Finset K) (w : K → ℝ) (F : K → (M → Bool) → ℝ)
    (x : ℝ) : boolExpect x (fun f => ∑ κ ∈ s, w κ * F κ f) = ∑ κ ∈ s, w κ * boolExpect x (F κ) := by
  simp only [boolExpect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma sliceExpect_sum_mul {K : Type*} (s : Finset K) (w : K → ℝ) (F : K → (M → Bool) → ℝ)
    (k : ℕ) : sliceExpect k (fun f => ∑ κ ∈ s, w κ * F κ f) = ∑ κ ∈ s, w κ * sliceExpect k (F κ) := by
  simp only [sliceExpect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- **Lemma 15 for fixed auxiliary randomness** (lines 941–975; also the polynomial step of
Lemma 8, lines 581–600): if the acceptance probability is linear in the `t`-point marginals of
the oracle (Lemma 1) and the oracle depends on the marking through one bit per point, then
`λ ↦ 𝔼_{f ← D_λ}[acc(Th_f)]` is a polynomial of degree at most `t`. -/
theorem isPolyOnUnitInterval_of_marginalLinear {acc : (W → Y) → ℝ} {t : ℕ}
    (hacc : IsMarginalLinear acc t) (Φ : OneBitPlanting W M Y) :
    IsPolyOnUnitInterval (fun x => boolExpect x fun f => acc (Φ.apply f)) t := by
  classical
  obtain ⟨s, c, hc⟩ := hacc
  -- each marginal event `Th(w_i) = r_i ∀ i` is the event `(f(x_i))_i ∈ B` of Lemma 14
  have hpoly : ∀ xr ∈ s, IsPolyOnUnitInterval
      (fun x => boolExpect x fun f => marginalInd xr.1 xr.2 (Φ.apply f)) t := fun xr _ => by
    have h := natDegree_boolExpectPoly_comp_le (fun i => Φ.pt (xr.1 i))
      (fun b => if ∀ i, Φ.val (xr.1 i) (b i) = xr.2 i then (1 : ℝ) else 0)
    rw [Fintype.card_fin] at h
    refine (IsPolyOnUnitInterval.of_poly h).congr fun x _ => ?_
    rw [eval_boolExpectPoly]
    rfl
  refine (IsPolyOnUnitInterval.sum s c hpoly).congr fun x _ => ?_
  rw [← boolExpect_sum_mul]
  simp only [hc]

/-- **Lemma 15 (Degree)**, Undetectability lines 923–986: averaging over the auxiliary randomness
`κ` (with weights `w κ` independent of `λ`, line 980) of acceptance probabilities that are linear
in the `t`-point marginals of one-bit planted oracles gives a polynomial of degree at most `t`. -/
theorem isPolyOnUnitInterval_planted_of_marginalLinear {K : Type*} (s : Finset K) (w : K → ℝ)
    (Φ : K → OneBitPlanting W M Y) {acc : K → (W → Y) → ℝ} {t : ℕ}
    (hacc : ∀ κ ∈ s, IsMarginalLinear (acc κ) t) :
    IsPolyOnUnitInterval
      (fun x => ∑ κ ∈ s, w κ * boolExpect x fun f => acc κ ((Φ κ).apply f)) t :=
  IsPolyOnUnitInterval.sum s w fun κ hκ => isPolyOnUnitInterval_of_marginalLinear (hacc κ hκ) _

/-! ### Theorem 16 and Lemma 8, conditional on Lemma 1 -/

/-- **Theorem 16 (and Lemma 8) conditional on Lemma 1**, Undetectability lines 990–1004. Let
`|M| ≥ 1`, let `κ` be auxiliary randomness with weights `w κ ≥ 0` summing to `1`, and for each `κ`
let `Φ κ` be a one-bit planting and `acc κ H ∈ [0, 1]` the acceptance probability on oracle `H`,
linear in the `t`-point marginals (Lemma 1). With `p_k := ∑_κ w κ 𝔼_{f ← E_k}[acc κ (Th_f)]`
(the marked set a uniform `k`-subset of `M`), `|p₁ - p₀| ≤ t² / |M|`. -/
theorem planted_bound_of_marginalLinear (hM : 1 ≤ Fintype.card M) {K : Type*} (s : Finset K)
    {w : K → ℝ} (hw0 : ∀ κ ∈ s, 0 ≤ w κ) (hw1 : ∑ κ ∈ s, w κ = 1) (Φ : K → OneBitPlanting W M Y)
    {acc : K → (W → Y) → ℝ} {t : ℕ} (hacc01 : ∀ κ ∈ s, ∀ H, acc κ H ∈ Set.Icc (0 : ℝ) 1)
    (hlin : ∀ κ ∈ s, IsMarginalLinear (acc κ) t) :
    |∑ κ ∈ s, w κ * sliceExpect 1 (fun f => acc κ ((Φ κ).apply f)) -
        ∑ κ ∈ s, w κ * sliceExpect 0 (fun f => acc κ ((Φ κ).apply f))| ≤
      (t : ℝ) ^ 2 / Fintype.card M := by
  have hF : ∀ f, ∑ κ ∈ s, w κ * acc κ ((Φ κ).apply f) ∈ Set.Icc (0 : ℝ) 1 := fun f =>
    ⟨sum_nonneg fun κ hκ => mul_nonneg (hw0 κ hκ) (hacc01 κ hκ _).1, by
      calc ∑ κ ∈ s, w κ * acc κ ((Φ κ).apply f) ≤ ∑ κ ∈ s, w κ :=
            sum_le_sum fun κ hκ => mul_le_of_le_one_right (hw0 κ hκ) (hacc01 κ hκ _).2
        _ = 1 := hw1⟩
  have := boolean_planted_family hM hF ((isPolyOnUnitInterval_planted_of_marginalLinear s w Φ
    hlin).congr fun x _ => (boolExpect_sum_mul s w _ x).symm)
  rwa [sliceExpect_sum_mul, sliceExpect_sum_mul] at this

/-- **Theorem 16 conditional on Lemma 1**, with `t = 2q` marginal points for `q` queries:
`|p₁ - p₀| ≤ 4q² / |M|`. -/
theorem planted_bound_of_marginalLinear_two_mul (hM : 1 ≤ Fintype.card M) {K : Type*}
    (s : Finset K) {w : K → ℝ} (hw0 : ∀ κ ∈ s, 0 ≤ w κ) (hw1 : ∑ κ ∈ s, w κ = 1)
    (Φ : K → OneBitPlanting W M Y) {acc : K → (W → Y) → ℝ} {q : ℕ}
    (hacc01 : ∀ κ ∈ s, ∀ H, acc κ H ∈ Set.Icc (0 : ℝ) 1)
    (hlin : ∀ κ ∈ s, IsMarginalLinear (acc κ) (2 * q)) :
    |∑ κ ∈ s, w κ * sliceExpect 1 (fun f => acc κ ((Φ κ).apply f)) -
        ∑ κ ∈ s, w κ * sliceExpect 0 (fun f => acc κ ((Φ κ).apply f))| ≤
      4 * (q : ℝ) ^ 2 / Fintype.card M := by
  have := planted_bound_of_marginalLinear hM s hw0 hw1 Φ hacc01 hlin
  convert this using 2
  push_cast
  ring

/-- **Lemma 8 conditional on Lemma 1** (lines 556–600): an algorithm with oracle `f : M → {0, 1}`
whose acceptance probability `acc f ∈ [0, 1]` is linear in the `2q_f`-point marginals of `f`
distinguishes the all-zero function from a function with one uniformly random marked point with
advantage at most `4 q_f² / |M|`. -/
theorem zero_vs_one_marked_of_marginalLinear (hM : 1 ≤ Fintype.card M) {acc : (M → Bool) → ℝ}
    {q : ℕ} (hacc01 : ∀ f, acc f ∈ Set.Icc (0 : ℝ) 1) (hlin : IsMarginalLinear acc (2 * q)) :
    |(Fintype.card M : ℝ)⁻¹ * ∑ y, acc (singleMark y) - acc fun _ => false| ≤
      4 * (q : ℝ) ^ 2 / Fintype.card M := by
  have := planted_bound_of_marginalLinear_two_mul hM {()} (w := fun _ => 1) (by simp) (by simp)
    (fun _ => OneBitPlanting.self M) (acc := fun _ => acc) (fun _ _ => hacc01) fun _ _ => hlin
  simpa [sliceExpect_one, sliceExpect_zero] using this

end Degree

end ShrincsSecurity.Undetectability
