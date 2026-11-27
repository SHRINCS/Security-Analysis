module

public import ShrincsSecurity.Undetectability.Marginal.Comb

/-!
# The sm-ud experiment, the planted family, and Theorem 16

Undetectability paper (`notes/txt/Undetectability.txt`):

* **Definition 4** (sm-ud, lines 386–398): `smUdReal` (`b = 0`), `smUdRand` (`b = 1`) and
  `smUdAdv = |Pr[⇒ 1 | b = 1] - Pr[⇒ 1 | b = 0]|`, in the form with one input `x_T` sampled
  before the run for every tweak (lines 420–423).
* **Appendix A.1** (lines 806–835): the planted oracle `plantedOracle` with key
  `κ = (P', e, e_y, Th')`, the run `B(ω)` (`plantedRun`), `p_k` (`plantedEndpoint`) and `g(λ)`
  (`plantedFamily`), with `g = ∑_k b_{|M|,k} p_k` (`plantedFamily_eq_mixture`).
* **Lemma 13** (Endpoints, lines 836–862): `plantedEndpoint_zero`, `plantedEndpoint_one`.
* **Lemma 15** (Degree, lines 923–986) in game form: `isPolyOnUnitInterval_plantedFamily`.
* **Theorem 16** (lines 990–1004): `smUdAdv_le_of_marginalLinear` for every acceptance family
  linear in the `2q`-point marginals of `Th`, and `TwoStageAdversary.smUdAdv_le` for two-stage
  comb adversaries with `q₁ + q₂ = q` queries (Lemma 1, `Marginal/Comb.lean`).
* **Theorem 9** (lines 674–689): `TwoStageAdversary.smUdAdv_le_xor`, the case
  `N = (ZMod 2)^n` of Theorem 16.

## Modelling choices

* `Th : P × T × M → N` with `N` an additive commutative group (VCVio's `oracleUnitary` needs
  `AddCommGroup`; the paper fixes an arbitrary group law, line 152) and `M` an additive group
  (the paper identifies `M` with `ℤ_{|M|}`, used only for the offsets `z - e(T)`).
* **The challenge oracle.** In each world the answer of the classical challenge oracle on a fresh
  tweak `T` is a value `ch(T)` fixed before the run: `Th(P, T, x_T)` for `b = 0`, a uniform `y_T`
  for `b = 1`. The adversary is described by its acceptance probability `acc ch P Th` for each
  table `ch : T → N` of challenge answers, second-stage input `P` and oracle `Th`. The rule of
  Definition 4 (at most `p` distinct tweaks, `⊥` on repeats) only restricts which entries of `ch`
  the adversary reads, and the stateful oracle with list `Q` is a deterministic function of `ch`
  that the adversary can run itself (as in `B`, lines 949–951). An adversary that reads entries of
  `ch` freely, as the families here may, is therefore at least as strong as every adversary of
  Definition 4 for every `p`; the bound does not depend on `p` (line 1004).
* Uniform sampling of finite sets is the normalised sum `uexp`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Finset

/-! ### Uniform expectations -/

section uexp

variable {α β : Type*} [Fintype α] [Fintype β]

/-- `𝔼_{a ←$ α} f(a)` for a finite type `α`. -/
noncomputable def uexp (f : α → ℝ) : ℝ := (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

lemma uexp_eq_sum (f : α → ℝ) : uexp f = ∑ a, (Fintype.card α : ℝ)⁻¹ * f a := by
  rw [uexp, mul_sum]

lemma uexp_const [Nonempty α] (c : ℝ) : uexp (fun _ : α => c) = c := by
  have : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [uexp, sum_const, card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ this]

lemma uexp_congr {f g : α → ℝ} (h : ∀ a, f a = g a) : uexp f = uexp g := by
  simp only [uexp, h]

lemma uexp_prod (f : α × β → ℝ) : uexp f = uexp fun a => uexp fun b => f (a, b) := by
  simp only [uexp, Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type, mul_sum,
    mul_assoc]

lemma uexp_comm (f : α → β → ℝ) :
    (uexp fun a => uexp fun b => f a b) = uexp fun b => uexp fun a => f a b := by
  simp only [uexp, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

lemma uexp_equiv (e : α ≃ β) (f : β → ℝ) : uexp (fun a => f (e a)) = uexp f := by
  rw [uexp, uexp, Fintype.card_congr e, Equiv.sum_comp e f]

lemma uexp_mem_Icc {f : α → ℝ} (h : ∀ a, f a ∈ Set.Icc (0 : ℝ) 1) :
    uexp f ∈ Set.Icc (0 : ℝ) 1 := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [uexp]
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨mul_nonneg (inv_nonneg.mpr hc.le) (sum_nonneg fun a _ => (h a).1), ?_⟩
  rw [uexp, inv_mul_le_iff₀ hc]
  calc ∑ a, f a ≤ ∑ _a : α, (1 : ℝ) := sum_le_sum fun a _ => (h a).2
    _ = Fintype.card α * 1 := by simp

end uexp

variable {Pp T M N : Type*} [Fintype Pp] [DecidableEq Pp] [Fintype T] [DecidableEq T]
  [Fintype M] [DecidableEq M] [AddGroup M] [Fintype N]

/-! ### Definition 4 -/

section Definition4

/-- `Pr[SM-UD(A) ⇒ 1 | b = 0]` (Definition 4): `P ←$ P`, `Th` uniform, one input `x_T ←$ M` per
tweak sampled before the run (lines 420–423), challenge answers `Th(P, T, x_T)`. Here
`acc ch P Th` is the probability that the adversary outputs `1` with challenge answers `ch`,
second-stage input `P` and oracle `Th`. -/
noncomputable def smUdReal (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) : ℝ :=
  uexp fun P : Pp => uexp fun Th : Pp × T × M → N => uexp fun x : T → M =>
    acc (fun τ => Th (P, τ, x τ)) P Th

/-- `Pr[SM-UD(A) ⇒ 1 | b = 1]` (Definition 4): challenge answers uniform in `N`. -/
noncomputable def smUdRand (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) : ℝ :=
  uexp fun P : Pp => uexp fun Th : Pp × T × M → N => uexp fun y : T → N => acc y P Th

/-- `Adv^{sm-ud} = |Pr[⇒ 1 | b = 1] - Pr[⇒ 1 | b = 0]|` (Definition 4, line 398). -/
noncomputable def smUdAdv (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) : ℝ :=
  |smUdRand acc - smUdReal acc|

end Definition4

/-! ### The planted family (Appendix A.1) -/

section Planted

/-- The key `κ = (P', e, e_y, Th')` of the planted family, sampled uniformly (step 1). -/
abbrev PlantKey (Pp T M N : Type*) := Pp × (T → M) × (T → N) × (Pp × T × M → N)

/-- The planted oracle (step 3, equation (5)): `Th(P, T, z) = e_y(T)` if `P = P'` and
`f(z - e(T)) = 1`, otherwise `Th'(P, T, z)`. The marking `f = 1[· ∈ S]`. -/
def plantedOracle (κ : PlantKey Pp T M N) (f : M → Bool) : Pp × T × M → N := fun w =>
  if w.1 = κ.1 ∧ f (w.2.2 - κ.2.1 w.2.1) = true then κ.2.2.1 w.2.1 else κ.2.2.2 w

/-- The planted oracle reads one bit of the marking per point (proof of Lemma 15). -/
def planting (κ : PlantKey Pp T M N) : OneBitPlanting (Pp × T × M) M N :=
  ⟨fun w => w.2.2 - κ.2.1 w.2.1, fun w b => if w.1 = κ.1 ∧ b = true then κ.2.2.1 w.2.1 else κ.2.2.2 w⟩

omit [Fintype Pp] [Fintype T] [DecidableEq T] [Fintype M] [DecidableEq M] [Fintype N] in
lemma planting_apply (κ : PlantKey Pp T M N) (f : M → Bool) :
    (planting κ).apply f = plantedOracle κ f := rfl

/-- The run `B(ω)`: the adversary with oracle `Th`, challenge answers `e_y(T)` and second-stage
input `P'`. -/
def plantedRun (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) (κ : PlantKey Pp T M N)
    (f : M → Bool) : ℝ :=
  acc κ.2.2.1 κ.1 (plantedOracle κ f)

/-- `p_k = Pr_{ω ← E_k}[B(ω) = 1]`: the marked set `S` uniform of size `k`. -/
noncomputable def plantedEndpoint (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) (k : ℕ) : ℝ :=
  uexp fun κ : PlantKey Pp T M N => sliceExpect k (plantedRun acc κ)

/-- `g(λ) = Pr_{ω ← D_λ}[B(ω) = 1]`: every element of `M` in `S` independently with
probability `λ`. -/
noncomputable def plantedFamily (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) (x : ℝ) : ℝ :=
  uexp fun κ : PlantKey Pp T M N => boolExpect x (plantedRun acc κ)

/-- `D_λ = ∑_k b_{|M|,k}(λ) E_k` (line 822). -/
theorem plantedFamily_eq_mixture (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) (x : ℝ) :
    plantedFamily acc x = ∑ k ∈ range (Fintype.card M + 1),
      binomWeight (Fintype.card M) k x * plantedEndpoint acc k := by
  simp only [plantedFamily, plantedEndpoint, uexp, boolExpect_eq_mixture, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- The oracle planted at the positions `u_T`: `e_y(T)` at `(P', T, u_T)`, `Th'` elsewhere. -/
def plantAt (P' : Pp) (u : T → M) (ey : T → N) (Th' : Pp × T × M → N) : Pp × T × M → N :=
  fun w => if w.1 = P' ∧ w.2.2 = u w.2.1 then ey w.2.1 else Th' w

omit [Fintype Pp] [Fintype T] [DecidableEq T] [Fintype M] [Fintype N] in
/-- With `S = {x*}`, the planted oracle is planted at `u_T = x* + e(T)`. -/
lemma plantedOracle_singleMark (P' : Pp) (e : T → M) (ey : T → N) (Th' : Pp × T × M → N)
    (xs : M) :
    plantedOracle (P', e, ey, Th') (singleMark xs) = plantAt P' (fun τ => xs + e τ) ey Th' := by
  funext w
  simp [plantedOracle, plantAt, singleMark, sub_eq_iff_eq_add]

/-- Planting at fixed positions is a bijection: `(e_y, Th') ↦ (Th, (Th'(P', T, u_T))_T)`. -/
def plantEquiv (P' : Pp) (u : T → M) :
    (T → N) × (Pp × T × M → N) ≃ (Pp × T × M → N) × (T → N) where
  toFun p := (plantAt P' u p.1 p.2, fun τ => p.2 (P', τ, u τ))
  invFun p := (fun τ => p.1 (P', τ, u τ), plantAt P' u p.2 p.1)
  left_inv p := by
    obtain ⟨ey, Th'⟩ := p
    ext w
    · simp [plantAt]
    · obtain ⟨P, τ, z⟩ := w
      by_cases h : P = P' ∧ z = u τ
      · obtain ⟨rfl, rfl⟩ := h
        simp [plantAt]
      · simp [plantAt, h]
  right_inv p := by
    obtain ⟨Th, j⟩ := p
    ext w
    · obtain ⟨P, τ, z⟩ := w
      by_cases h : P = P' ∧ z = u τ
      · obtain ⟨rfl, rfl⟩ := h
        simp [plantAt]
      · simp [plantAt, h]
    · simp [plantAt]

omit [AddGroup M] in
/-- At fixed positions `u_T`, `Th` planted with uniform `e_y` is uniform, and the challenge
answers `e_y(T)` are `Th(P', T, u_T)` (proof of Lemma 13, lines 851–857). -/
lemma uexp_plantAt [Nonempty N] (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) (P' : Pp)
    (u : T → M) :
    (uexp fun ey : T → N => uexp fun Th' : Pp × T × M → N => acc ey P' (plantAt P' u ey Th')) =
      uexp fun Th : Pp × T × M → N => acc (fun τ => Th (P', τ, u τ)) P' Th := by
  have key := uexp_equiv (plantEquiv P' u)
    (fun p : (Pp × T × M → N) × (T → N) => acc (fun τ => p.1 (P', τ, u τ)) P' p.1)
  rw [uexp_prod, uexp_prod] at key
  simp only [uexp_const] at key
  rw [← key]
  refine uexp_congr fun ey => uexp_congr fun Th' => ?_
  congr 1
  funext τ
  simp [plantEquiv, plantAt]

/-- **Lemma 13** (Endpoints), `k = 0`: `p₀ = Pr[SM-UD(A) ⇒ 1 | b = 1]`. -/
theorem plantedEndpoint_zero (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) :
    plantedEndpoint acc 0 = smUdRand acc := by
  simp only [plantedEndpoint, sliceExpect_zero, plantedRun]
  have h0 : ∀ κ : PlantKey Pp T M N, plantedOracle κ (fun _ => false) = κ.2.2.2 := fun κ => by
    funext w
    simp [plantedOracle]
  simp only [h0, smUdRand]
  rw [uexp_prod]
  refine uexp_congr fun P => ?_
  rw [uexp_prod]
  simp only [uexp_prod (α := T → N), uexp_const]
  exact uexp_comm _

/-- **Lemma 13** (Endpoints), `k = 1`: `p₁ = Pr[SM-UD(A) ⇒ 1 | b = 0]`. -/
theorem plantedEndpoint_one [Nonempty N] (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) :
    plantedEndpoint acc 1 = smUdReal acc := by
  simp only [plantedEndpoint, sliceExpect_one, plantedRun]
  rw [uexp_prod]
  refine uexp_congr fun P' => ?_
  rw [uexp_prod]
  simp only [uexp_prod (α := T → N)]
  -- `(card M)⁻¹ ∑_{x*}` is the uniform expectation over `x*`; bring it to the front
  have hx : ∀ e : T → M, ∀ ey : T → N, ∀ Th' : Pp × T × M → N,
      (Fintype.card M : ℝ)⁻¹ * ∑ xs, acc ey P' (plantedOracle (P', e, ey, Th') (singleMark xs)) =
        uexp fun xs : M => acc ey P' (plantAt P' (fun τ => xs + e τ) ey Th') := fun e ey Th' => by
    simp only [uexp, plantedOracle_singleMark]
  simp only [hx]
  simp only [uexp_comm (α := Pp × T × M → N) (β := M), uexp_comm (α := T → N) (β := M)]
  rw [uexp_comm]
  -- for fixed `x*`, `e ↦ u = x* + e` is a bijection
  have hshift : ∀ xs : M, (uexp fun e : T → M => uexp fun ey : T → N =>
      uexp fun Th' : Pp × T × M → N => acc ey P' (plantAt P' (fun τ => xs + e τ) ey Th')) =
      uexp fun u : T → M => uexp fun ey : T → N =>
        uexp fun Th' : Pp × T × M → N => acc ey P' (plantAt P' u ey Th') := fun xs =>
    uexp_equiv (Equiv.piCongrRight fun _ => Equiv.addLeft xs) (fun u => uexp fun ey : T → N =>
      uexp fun Th' : Pp × T × M → N => acc ey P' (plantAt P' u ey Th'))
  refine (uexp_congr hshift).trans ?_
  rw [uexp_const]
  exact (uexp_congr fun u => uexp_plantAt acc P' u).trans (uexp_comm _)

end Planted

/-! ### Lemma 15 and Theorem 16 -/

section Theorem16

lemma uexp_planted_eq (acc : (T → N) → Pp → (Pp × T × M → N) → ℝ) (k : ℕ) :
    plantedEndpoint acc k = ∑ κ : PlantKey Pp T M N,
      (Fintype.card (PlantKey Pp T M N) : ℝ)⁻¹ *
        sliceExpect k (fun f => acc κ.2.2.1 κ.1 ((planting κ).apply f)) :=
  uexp_eq_sum _

/-- **Lemma 15** (Degree) in game form: if for fixed challenge answers and second-stage input
the acceptance probability is linear in the `2q`-point marginals of `Th` (Lemma 1), then `g(λ)`
is a polynomial of degree at most `2q` on `[0, 1]`. -/
theorem isPolyOnUnitInterval_plantedFamily {acc : (T → N) → Pp → (Pp × T × M → N) → ℝ} {q : ℕ}
    (hlin : ∀ ch P, IsMarginalLinear (acc ch P) (2 * q)) :
    IsPolyOnUnitInterval (plantedFamily acc) (2 * q) :=
  (isPolyOnUnitInterval_planted_of_marginalLinear univ
    (fun _ => (Fintype.card (PlantKey Pp T M N) : ℝ)⁻¹) planting
    (acc := fun κ => acc κ.2.2.1 κ.1) fun κ _ => hlin _ _).congr fun x _ => by
      rw [plantedFamily, uexp_eq_sum]
      rfl

/-- **Theorem 16** for acceptance families: if `acc ch P Th ∈ [0, 1]` and for fixed `ch`, `P`
the acceptance probability is linear in the `2q`-point marginals of `Th` (Lemma 1), then
`Adv^{sm-ud} ≤ 4q² / |M|`. Proof: Lemma 13, Lemma 15 and Lemma 7. -/
theorem smUdAdv_le_of_marginalLinear [Nonempty Pp] [Nonempty N]
    {acc : (T → N) → Pp → (Pp × T × M → N) → ℝ} {q : ℕ}
    (h01 : ∀ ch P Th, acc ch P Th ∈ Set.Icc (0 : ℝ) 1)
    (hlin : ∀ ch P, IsMarginalLinear (acc ch P) (2 * q)) :
    smUdAdv acc ≤ 4 * (q : ℝ) ^ 2 / Fintype.card M := by
  have hM : 1 ≤ Fintype.card M := Fintype.card_pos
  have hK : (Fintype.card (PlantKey Pp T M N) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key := planted_bound_of_marginalLinear_two_mul hM (univ : Finset (PlantKey Pp T M N))
    (w := fun _ => (Fintype.card (PlantKey Pp T M N) : ℝ)⁻¹) (fun _ _ => by positivity)
    (by rw [sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀ hK]) planting
    (acc := fun κ => acc κ.2.2.1 κ.1) (q := q) (fun κ _ => h01 _ _) fun κ _ => hlin _ _
  rw [smUdAdv, ← plantedEndpoint_zero, ← plantedEndpoint_one, uexp_planted_eq,
    uexp_planted_eq]
  rw [abs_sub_comm]
  exact key

end Theorem16

/-! ### Theorem 16 and Theorem 9 for two-stage comb adversaries -/

section Comb

variable [Nonempty Pp] [DecidableEq N] [AddCommGroup N] {E : Type*} [Fintype E] {q₁ q₂ : ℕ}

/-- The acceptance probability `Pr[b' = 1]` of a two-stage sm-ud adversary in comb form, with
challenge answers `ch`, second-stage input `P` and oracle `Th`. -/
noncomputable def TwoStageAdversary.smUdAccept
    (A : TwoStageAdversary (Pp × T × M) N E (T → N) Pp Bool q₁ q₂) (ch : T → N) (P : Pp)
    (Th : Pp × T × M → N) : ℝ :=
  A.outProb ch P Th true

/-- **Theorem 16** (Quadratic sm-ud bound for every group law, lines 990–1004), for every
additive commutative group `N`: a two-stage adversary in comb form making `q₁` queries to `Th` in
stage one and `q₂` in stage two has `Adv^{sm-ud} ≤ 4(q₁ + q₂)² / |M|`. -/
theorem TwoStageAdversary.smUdAdv_le
    (A : TwoStageAdversary (Pp × T × M) N E (T → N) Pp Bool q₁ q₂) :
    smUdAdv A.smUdAccept ≤ 4 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card M :=
  smUdAdv_le_of_marginalLinear
    (fun ch P Th => ⟨A.outProb_nonneg ch P Th true, A.outProb_le_one ch P Th true⟩)
    fun ch P => A.isMarginalLinear_outProb ch P true

/-- **Theorem 9** (Quadratic sm-ud bound, lines 674–689): `N = {0, 1}ⁿ` with bitwise XOR is the
additive group `Fin n → ZMod 2`, so this is the case of Theorem 16. The paper's proof via the
Boolean reduction and Lemma 2 is not needed for the statement. -/
theorem TwoStageAdversary.smUdAdv_le_xor {n : ℕ}
    (A : TwoStageAdversary (Pp × T × M) (Fin n → ZMod 2) E (T → Fin n → ZMod 2) Pp Bool q₁ q₂) :
    smUdAdv A.smUdAccept ≤ 4 * ((q₁ + q₂ : ℕ) : ℝ) ^ 2 / Fintype.card M :=
  A.smUdAdv_le

end Comb

end ShrincsSecurity.Undetectability
