module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic

/-!
# Interleaved target subset resilience: digests, covered sets, and the quantities `Γ`

`ITSR-Classical.pdf`, Section 2.1 and Section 3 (Definitions 1, 2, 3, 5, 6).

A digest is a pair `(I, J)` of an instance `I : ι` and `k` coordinates `J : Fin k → Fin t`. The
paper fixes `ι = {0,1}^h`, so that `θ = 2^-h`; we keep `ι` an arbitrary finite type and write
`θ = 1 / |ι|` (`theta`). The covered set of a finite set of digests is, per instance, the
Cartesian product of the coordinate sets that the digests of that instance reveal.

The bounds of Theorems 1 and 2 are stated in `ℝ`; the game files transport them into `ℝ≥0∞`.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR

/-- **Digest** (Definition 1): an instance and `k` coordinates in `[t]`. -/
abbrev Digest (ι : Type) (k t : ℕ) := ι × (Fin k → Fin t)

variable {ι : Type} {k t : ℕ}

section Covered

variable [DecidableEq ι]

/-- **Position set** `S_i(I)(G)` (Definition 2): the `i`-th coordinates of the digests of `G` in
instance `I`. -/
def posSet (G : Finset (Digest ι k t)) (I : ι) (i : Fin k) : Finset (Fin t) :=
  (G.filter fun u => u.1 = I).image fun u => u.2 i

/-- **Covered** (Definition 2): `u ∈ S(G)`, i.e. every coordinate of `u` is revealed in the
instance of `u` by some digest of `G`. -/
def Covered (G : Finset (Digest ι k t)) (u : Digest ι k t) : Prop :=
  ∀ i, u.2 i ∈ posSet G u.1 i

instance (G : Finset (Digest ι k t)) (u : Digest ι k t) : Decidable (Covered G u) :=
  inferInstanceAs (Decidable (∀ i, u.2 i ∈ posSet G u.1 i))

theorem posSet_mono {G G' : Finset (Digest ι k t)} (h : G ⊆ G') (I : ι) (i : Fin k) :
    posSet G I i ⊆ posSet G' I i :=
  Finset.image_subset_image (Finset.filter_subset_filter _ h)

/-- The covered set is monotone (remark after Definition 2). -/
theorem Covered.mono {G G' : Finset (Digest ι k t)} (h : G ⊆ G') {u : Digest ι k t}
    (hu : Covered G u) : Covered G' u :=
  fun i => posSet_mono h u.1 i (hu i)

/-- **Load** (Definition 3): the number of entries of a list of digests in instance `I`. -/
def load (G : List (Digest ι k t)) (I : ι) : ℕ :=
  G.countP fun u => u.1 = I

end Covered

/-! ## The quantities `Γ_j(r)` and `Γ⁺(r)` -/

/-- `θ = 1 / |ι|`, the probability that a uniform digest lies in a given instance. -/
noncomputable def theta (ι : Type) [Fintype ι] : ℝ := 1 / (Fintype.card ι : ℝ)

/-- **`Γ_j(r)`** (Definition 5), at instance probability `θ` and `t` leaves:
`E_{g ∼ Bin(r, θ)} [(1 - (1 - 1/t)^g)^j]`. -/
noncomputable def gamma (θ : ℝ) (t r j : ℕ) : ℝ :=
  ∑ g ∈ Finset.range (r + 1),
    (r.choose g : ℝ) * θ ^ g * (1 - θ) ^ (r - g) * (1 - (1 - 1 / (t : ℝ)) ^ g) ^ j

/-- **`Γ⁺(r)`** (Definition 6): `∑_{ω=1}^{k} C(k, ω) t^{-ω} Γ_{k-ω}(r)`. -/
noncomputable def gammaPlus (θ : ℝ) (t k r : ℕ) : ℝ :=
  ∑ ω ∈ Finset.Icc 1 k, (k.choose ω : ℝ) * ((t : ℝ)⁻¹) ^ ω * gamma θ t r (k - ω)

/-- The inner sum of Theorem 2 at `m` pulled witnesses:
`A_m = ∑_{ω=m}^{k} C(k, ω) m! St(ω, m) t^{-ω} Γ_{k-ω}(r)` (the `A_m` of Lemma 11). -/
noncomputable def pullHarm (θ : ℝ) (t k r m : ℕ) : ℝ :=
  ∑ ω ∈ Finset.Icc m k,
    (k.choose ω : ℝ) * (m.factorial : ℝ) * (Nat.stirlingSecond ω m : ℝ) * ((t : ℝ)⁻¹) ^ ω *
      gamma θ t r (k - ω)

/-- The summand `m` of Theorem 2 (the `T_m` of Lemma 11), for a key space of size `nK`:
`(q + 1) C(q, m) (r)_m nK^{-m} θ^m A_m`. -/
noncomputable def pullTerm (θ : ℝ) (t k r q nK m : ℕ) : ℝ :=
  (q + 1 : ℝ) * (q.choose m : ℝ) * (r.descFactorial m : ℝ) * ((nK : ℝ)⁻¹) ^ m * θ ^ m *
    pullHarm θ t k r m

/-- **The search term** `(q + 1) Γ_k(r)`, common to Theorems 1 and 2. -/
noncomputable def searchTerm (θ : ℝ) (t k r q : ℕ) : ℝ :=
  (q + 1 : ℝ) * gamma θ t r k

/-- **The bound of Theorem 1** (crude bound): `(q + 1) Γ_k(r) + r · min(q, nK) / nK`. -/
noncomputable def crudeBound (θ : ℝ) (t k r q nK : ℕ) : ℝ :=
  searchTerm θ t k r q + (r : ℝ) * (min q nK : ℕ) / (nK : ℝ)

/-- **The bound of Theorem 2** (main bound):
`(q + 1) Γ_k(r) + ∑_{m=1}^{min(k,q,r)} T_m`. -/
noncomputable def mainBound (θ : ℝ) (t k r q nK : ℕ) : ℝ :=
  searchTerm θ t k r q + ∑ m ∈ Finset.Icc 1 (min k (min q r)), pullTerm θ t k r q nK m

/-- **`R₂`** (Eq. (4)): the summands `m ≥ 2` of Theorem 2. -/
noncomputable def remainderTwo (θ : ℝ) (t k r q nK : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (min k (min q r)), pullTerm θ t k r q nK m

end ShrincsSecurity.ITSR

end
