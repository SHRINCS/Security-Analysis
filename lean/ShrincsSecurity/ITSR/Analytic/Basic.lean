module

public import ShrincsSecurity.ITSR.Defs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

/-!
# Binomial expectations and basic facts about `Γ_j(r)` and `A_m`

`ITSR-Classical.pdf`, Sections 6 and 7 (preliminaries shared by Lemmas 11, 12 and 13).

* `binomWeight θ r g` is the binomial weight `P_g = C(r, g) θ^g (1 - θ)^(r - g)` of Lemma 13, and
  `binomExp θ r f = ∑_{g = 0}^{r} P_g f(g)` is the expectation `E_{g ∼ Bin(r, θ)}[f(g)]`, written
  as a finite sum.
* `leafReveal t g = 1 - (1 - 1/t)^g` is the `u_g = μ_g / t` of Remark 4 and Lemma 13, so that
  `Γ_j(r) = E[u_g^j]` (`gamma_eq_binomExp`).
* `gamma_zero` (`Γ_0 = 1`), `gamma_nonneg`, `pullHarm_nonneg`, `pullHarm_pos` and
  `pullTerm_nonneg` are the positivity facts used in the proof of Lemma 11.
* `factorial_mul_stirlingSecond_le_pow` is the surjection bound `m! St(ω, m) ≤ m^ω` of the proof of
  Lemma 11(a), and `stirlingSecond_pos` is `St(k, m) ≥ 1` for `1 ≤ m ≤ k` (proof of Lemma 11(c)).
-/

@[expose] public section

namespace ShrincsSecurity.ITSR

open Finset

/-! ## Binomial expectations -/

/-- The binomial weight `P_g = C(r, g) θ^g (1 - θ)^(r - g)` (Lemma 13), i.e. `Pr[g ∼ Bin(r, θ)]`. -/
noncomputable def binomWeight (θ : ℝ) (r g : ℕ) : ℝ :=
  (r.choose g : ℝ) * θ ^ g * (1 - θ) ^ (r - g)

/-- The binomial expectation `E_{g ∼ Bin(r, θ)}[f(g)] = ∑_{g=0}^{r} P_g f(g)` (Remark 4, Lemma 12),
written as a finite sum. -/
noncomputable def binomExp (θ : ℝ) (r : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ g ∈ range (r + 1), binomWeight θ r g * f g

/-- `u_g = 1 - (1 - 1/t)^g` (Remark 4, Lemma 13): the probability that one fixed leaf is revealed
by `g` uniform leaves of a tree with `t` leaves. -/
noncomputable def leafReveal (t g : ℕ) : ℝ := 1 - (1 - 1 / (t : ℝ)) ^ g

theorem binomWeight_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (r g : ℕ) :
    0 ≤ binomWeight θ r g := by
  unfold binomWeight
  have : 0 ≤ 1 - θ := by linarith
  positivity

/-- The binomial weights sum to one. -/
theorem sum_binomWeight (θ : ℝ) (r : ℕ) : ∑ g ∈ range (r + 1), binomWeight θ r g = 1 := by
  have h := (add_pow θ (1 - θ) r).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine sum_congr rfl fun g _ => ?_
  unfold binomWeight
  ring

theorem binomExp_mono {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {r : ℕ} {f f' : ℕ → ℝ}
    (h : ∀ g ≤ r, f g ≤ f' g) : binomExp θ r f ≤ binomExp θ r f' := by
  unfold binomExp
  refine sum_le_sum fun g hg => ?_
  exact mul_le_mul_of_nonneg_left (h g (Nat.lt_succ_iff.mp (mem_range.mp hg)))
    (binomWeight_nonneg h0 h1 r g)

theorem binomExp_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {r : ℕ} {f : ℕ → ℝ}
    (h : ∀ g ≤ r, 0 ≤ f g) : 0 ≤ binomExp θ r f := by
  have := binomExp_mono h0 h1 (f := fun _ => 0) h
  simpa [binomExp] using this

theorem binomExp_add (θ : ℝ) (r : ℕ) (f f' : ℕ → ℝ) :
    binomExp θ r (fun g => f g + f' g) = binomExp θ r f + binomExp θ r f' := by
  simp [binomExp, mul_add, sum_add_distrib]

theorem binomExp_const_mul (θ : ℝ) (r : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomExp θ r (fun g => c * f g) = c * binomExp θ r f := by
  simp [binomExp, mul_sum, mul_left_comm]

theorem binomExp_sum {α : Type*} (θ : ℝ) (r : ℕ) (s : Finset α) (f : α → ℕ → ℝ) :
    binomExp θ r (fun g => ∑ a ∈ s, f a g) = ∑ a ∈ s, binomExp θ r (f a) := by
  simp only [binomExp, mul_sum]
  exact sum_comm

/-! ## The revealed-leaf probability `u_g` -/

theorem leafReveal_nonneg (t g : ℕ) : 0 ≤ leafReveal t g := by
  unfold leafReveal
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hb0 : 0 ≤ 1 - 1 / (t : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact h1
  have hb1 : 1 - 1 / (t : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (t : ℝ) := by positivity
    linarith
  linarith [pow_le_one₀ hb0 hb1 (n := g)]

theorem leafReveal_le_one (t g : ℕ) : leafReveal t g ≤ 1 := by
  unfold leafReveal
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have hb0 : 0 ≤ 1 - 1 / (t : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact_mod_cast ht
  linarith [pow_nonneg hb0 g]

/-- `u_g ≤ g / t`, i.e. `μ_g ≤ g` (Bernoulli's inequality, proof of Lemma 12(i)). -/
theorem leafReveal_le_div (t g : ℕ) : leafReveal t g ≤ (g : ℝ) / t := by
  unfold leafReveal
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hle : -2 ≤ -(1 / (t : ℝ)) := by
    have : 1 / (t : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
    linarith
  have := one_add_mul_le_pow hle g
  rw [← sub_eq_add_neg] at this
  have e : (g : ℝ) / t = g * (1 / t) := by ring
  rw [e]
  linarith

/-- `Γ_j(r) = E_{g ∼ Bin(r, θ)}[u_g^j]` (Definition 5, Step 1 of Remark 4). -/
theorem gamma_eq_binomExp (θ : ℝ) (t r j : ℕ) :
    gamma θ t r j = binomExp θ r fun g => leafReveal t g ^ j := rfl

/-- `Γ_0(r) = 1`. -/
theorem gamma_zero (θ : ℝ) (t r : ℕ) : gamma θ t r 0 = 1 := by
  rw [gamma_eq_binomExp]
  simpa [binomExp] using sum_binomWeight θ r

theorem gamma_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t r j : ℕ) : 0 ≤ gamma θ t r j := by
  rw [gamma_eq_binomExp]
  exact binomExp_nonneg h0 h1 fun g _ => pow_nonneg (leafReveal_nonneg t g) j

/-! ## Stirling numbers -/

/-- `St(n + 1, m + 1) ≥ 1` for `m ≤ n`. -/
theorem stirlingSecond_succ_pos : ∀ {n m : ℕ}, m ≤ n → 0 < Nat.stirlingSecond (n + 1) (m + 1)
  | n, 0, _ => by rw [Nat.stirlingSecond_one_right]; exact Nat.one_pos
  | 0, _ + 1, h => absurd h (by omega)
  | n + 1, m + 1, h => by
    rw [Nat.stirlingSecond_succ_succ]
    exact Nat.add_pos_right _ (stirlingSecond_succ_pos (by omega))

/-- `St(k, m) ≥ 1` for `1 ≤ m ≤ k` (proof of Lemma 11(c)). -/
theorem stirlingSecond_pos {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) : 0 < Nat.stirlingSecond k m := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (hm.trans hmk)
  exact stirlingSecond_succ_pos (by omega)

/-- The surjection bound `m! St(ω, m) ≤ m^ω` (proof of Lemma 11(a)): `m^ω = ∑_j St(ω, j) (m)_j`,
and the summand `j = m` is `St(ω, m) m!`. -/
theorem factorial_mul_stirlingSecond_le_pow (ω m : ℕ) :
    m.factorial * Nat.stirlingSecond ω m ≤ m ^ ω := by
  rcases lt_or_ge ω m with h | h
  · simp [Nat.stirlingSecond_eq_zero_of_lt h]
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  calc m.factorial * Nat.stirlingSecond ω m
      = Nat.stirlingSecond ω m * m.descFactorial m := by
        rw [Nat.descFactorial_self, mul_comm]
    _ ≤ _ := single_le_sum (f := fun j => Nat.stirlingSecond ω j * m.descFactorial j)
        (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le h))

/-! ## Positivity of `A_m` and `T_m` -/

theorem pullHarm_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r m : ℕ) :
    0 ≤ pullHarm θ t k r m := by
  unfold pullHarm
  refine sum_nonneg fun ω _ => ?_
  have := gamma_nonneg h0 h1 t r (k - ω)
  positivity

/-- `A_m > 0` for `1 ≤ m ≤ k` and `t ≥ 1` (proof of Lemma 11(c)): the summand `ω = k` is
`m! St(k, m) t^{-k} Γ_0(r) > 0`. -/
theorem pullHarm_pos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {t k r m : ℕ} (ht : 1 ≤ t) (hm : 1 ≤ m)
    (hmk : m ≤ k) : 0 < pullHarm θ t k r m := by
  unfold pullHarm
  have hk : k ∈ Icc m k := mem_Icc.mpr ⟨hmk, le_rfl⟩
  refine lt_of_lt_of_le ?_ (single_le_sum (fun ω _ => ?_) hk)
  · rw [Nat.sub_self, gamma_zero, Nat.choose_self]
    have : (0 : ℝ) < Nat.stirlingSecond k m := by exact_mod_cast stirlingSecond_pos hm hmk
    have : (0 : ℝ) < t := by exact_mod_cast ht
    positivity
  · have := gamma_nonneg h0 h1 t r (k - ω)
    positivity

theorem pullTerm_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (t k r q nK m : ℕ) :
    0 ≤ pullTerm θ t k r q nK m := by
  unfold pullTerm
  have := pullHarm_nonneg h0 h1 t k r m
  positivity

end ShrincsSecurity.ITSR

end
