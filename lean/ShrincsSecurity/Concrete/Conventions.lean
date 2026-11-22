module

public import ShrincsSecurity.Concrete.Generic
public import ShrincsSecurity.ITSR.Concrete.ShrincsSl
public import ShrincsSecurity.Scheme.Params

/-!
# The conventions of Section 6.3 and the verification counts of Lemma 5.1

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Section 6.3** (lines 4942–4988),
**Lemma 5.1** (lines 4532–4579), the budgets of **Theorems 4.2 and 4.3** (lines 2981–2989,
3047–3059), **Table 4** (line 4517) and **Remark F.2** (lines 7501–7505).

* Verification counts (Lemma 5.1), as functions of the parameters (`Scheme.Params`):
  `Vsf = lsf (w − 1) − Swn + 2 + hsf` and `Vsl = k(a+1) + 1 + d(smax + h' + 1)`, split per
  function. `smax` is the largest chain work `C + Σ_{j<l2} (w − 1 − C_j)` of a WOTS-TW layer over
  the checksum values `C ≤ l1 (w − 1)`, `C_j` the base-`w` digits of `C`. At the parameters of
  Table 1 (`Scheme.shrincs`): `Vsf = 497`, `smax = 510`, `Vsl = 2741`, and the per-function counts
  `V^F = 240`, `V^H = 255`, `V^{Th_lsf} = V^{grind} = 1`, `V^{Th_{2∪lsf}} = 256` (stateful) and
  `V^F = 2560`, `V^H = 175`, `V^{Th_k} = 1`, `V^{Th_lsl} = 5` (stateless).
* Budgets: `Q^sl_Λ = 2^(hsl+1)(lsl w + 2) + 2^hsl (2kt + 1) = 2^45 · 164965` (Theorem 4.3);
  the stateless key generation `qkg = 2^h' (lsl w + 1) + 2^h' − 1 = 287743` (Table 4); the
  stateful budget `L (lsf w + 1) + I + qkg + qg` (Theorem 4.2, Section 6.8).
* Spaces: every space has `2^n = 2^128` elements, except the output of `H^sf_msg`
  (`|N| = 2^256`); these appear as literals in `Concrete.Paths`.
* `Γ = Γ_{45,10,2^13}(2^40)` (`Gam`): `2^-130.24 ≤ Γ ≤ 2^-130.23` (the upper bound is
  `ITSR.Concrete.ShrincsSl.table7_gamma`; the lower bound `gammaLoQ_le` is new and only used to
  show that the printed figures are not too conservative).
* `epsDs = 2^-128 + 10 · 2^-256`, the bound on `ε_ds` of Theorem 4.1 used in Section 6.3.
* The pull part at one query, `P_{45,10,2^13}(1, 2^40) < 2^-255.9` (Section 6.4), and the leading
  summand of the pull part, `T₁ ≤ q(q+1)/2^256.98` (Remark F.2, quoted in Claim 6.1).
-/

@[expose] public section

namespace ShrincsSecurity.Concrete

open Finset ShrincsSecurity.ITSR ShrincsSecurity.ITSR.Concrete ShrincsSecurity.Scheme

/-! ## Lemma 5.1: verification counts -/

section Params

variable (P : Scheme.Params)

/-- The chain work of one WOTS-TW layer whose checksum is `C`: the message chains contribute
`C = Σ_i (w − 1 − a_i)`, the checksum chains `Σ_{j<l2} (w − 1 − C_j)` (proof of Lemma 5.1). -/
def chainWorkSl (C : ℕ) : ℕ := C + ∑ j ∈ range P.l2, (P.w - 1 - C / P.w ^ j % P.w)

/-- `smax` (Lemma 5.1): the largest chain work of a WOTS-TW encoding, over all checksum values
`C ∈ {0, …, l1 (w − 1)}`. -/
def smax : ℕ := (range (P.l1 * (P.w - 1) + 1)).sup (chainWorkSl P)

/-- Stateful `V^F = lsf (w − 1) − Swn` (Lemma 5.1). -/
def VsfF : ℕ := P.lsf * (P.w - 1) - P.Swn

/-- Stateful `V^H = hsf` (Lemma 5.1; worst anchor depth `δ* = hsf`). -/
def VsfH : ℕ := P.hsf

/-- Stateful `V^{Th_{2∪lsf}} = 1 + hsf` (Lemma 5.1). -/
def VsfTh2 : ℕ := 1 + P.hsf

/-- **Lemma 5.1**, stateful path: `Vsf = lsf (w − 1) − Swn + 2 + hsf` tweakable-hash evaluations
(one `H_grind`, `V^F` calls to `F`, one `Th_lsf`, `hsf` calls to `H`). -/
def Vsf : ℕ := P.lsf * (P.w - 1) - P.Swn + 2 + P.hsf

theorem Vsf_eq_sum : Vsf P = 1 + VsfF P + 1 + VsfH P := by
  unfold Vsf VsfF VsfH; omega

/-- Stateless `V^F ≤ k + d smax` (Lemma 5.1). -/
def VslF : ℕ := P.k + P.d * smax P

/-- Stateless `V^H = ka + d h'` (Lemma 5.1). -/
def VslH : ℕ := P.k * P.a + P.d * P.hp

/-- **Lemma 5.1**, stateless path: `Vsl = k(a+1) + 1 + d(smax + h' + 1)`. -/
def Vsl : ℕ := P.k * (P.a + 1) + 1 + P.d * (smax P + P.hp + 1)

/-- `Vsl = V^F + V^H + V^{Th_k} + V^{Th_lsl}` with `V^{Th_k} = 1`, `V^{Th_lsl} = d`. -/
theorem Vsl_eq_sum : Vsl P = VslF P + VslH P + 1 + P.d := by
  unfold Vsl VslF VslH; ring

/-- `Q^sl_Λ := 2^(hsl+1)(lsl w + 2) + 2^hsl (2kt + 1)`, the collection budget of Theorem 4.3. -/
def QslLam : ℕ := 2 ^ (P.hsl + 1) * (P.lsl * P.w + 2) + 2 ^ P.hsl * (2 * P.k * P.t + 1)

/-- The honest stateless key generation (Table 4): `lsl w + 1` calls for each of the `2^h'`
WOTS-TW instances of the top XMSS tree and one per internal node. -/
def qkg : ℕ := 2 ^ P.hp * (P.lsl * P.w + 1) + (2 ^ P.hp - 1)

/-- The stateful collection budget `B = L (lsf w + 1) + I + qkg + qg` (Theorem 4.2, the maximum
of the `q_λ,i`; Section 6.8). -/
def budgetSf (L I qg : ℕ) : ℕ := L * (P.lsf * P.w + 1) + I + qkg P + qg

end Params

/-- **Lemma 5.1** at the parameters of Table 1. -/
theorem shrincs_verification :
    shrincs.w = 16 ∧ shrincs.lsf = 32 ∧ shrincs.Swn = 240 ∧ shrincs.l1 = 32 ∧ shrincs.l2 = 3 ∧
    shrincs.lsl = 35 ∧ Vsf shrincs = 497 ∧ VsfF shrincs = 240 ∧ VsfH shrincs = 255 ∧
    VsfTh2 shrincs = 256 ∧ smax shrincs = 510 ∧ chainWorkSl shrincs 480 = 510 ∧
    Vsl shrincs = 2741 ∧ VslF shrincs = 2560 ∧ VslH shrincs = 175 ∧ shrincs.d = 5 := by
  decide +kernel

/-- `smax = 510` is attained only at the checksum `480` (Lemma 5.1). -/
theorem shrincs_smax_attained_only :
    ∀ C ∈ range (shrincs.l1 * (shrincs.w - 1) + 1), chainWorkSl shrincs C = 510 → C = 480 := by
  decide +kernel

/-- The budgets at the parameters of Table 1: `Q^sl_Λ = 2^45 · 164965` (Section 6.8),
`qkg = 287743` (Table 4), `lsf w + 1 = 513`. -/
theorem shrincs_budgets :
    QslLam shrincs = 2 ^ 45 * 164965 ∧ qkg shrincs = 287743 ∧
      shrincs.lsf * shrincs.w + 1 = 513 := by
  decide +kernel

/-! ## `Γ` and the pull part at the stateless parameters -/

/-- `Γ = Γ_{45,10,2^13}(2^40)` (Lemma F.1), the `Γ` of Section 6.3. -/
noncomputable def Gam : ℝ := gamma (1 / 2 ^ 45) (2 ^ 13) (2 ^ 40) 10

/-- **Section 6.3**: `Γ ≤ 2^-130.23` (`ITSR-Classical.pdf`, Table 7). -/
theorem Gam_le : Gam ≤ (2 : ℝ) ^ (-130.23 : ℝ) := ShrincsSl.table7_gamma

/-- A rational lower bound for `Γ_10(2^40)`: the truncated sum of Lemma 13 with
`(1 − θ)^(r − g) ≥ 1 − rθ`. -/
def gammaLoQ (G : ℕ) : ℚ :=
  (1 - 2 ^ 40 / 2 ^ 45) * ∑ g ∈ range (G + 1), chooseQ (2 ^ 40) g * (1 / 2 ^ 45) ^ g *
    revealQ 13 g ^ 10

theorem gammaLoQ_le (G : ℕ) (hG : G ≤ 2 ^ 40) : (gammaLoQ G : ℝ) ≤ Gam := by
  have h0 : (0 : ℝ) ≤ 1 / 2 ^ 45 := by positivity
  have h1 : (1 / 2 ^ 45 : ℝ) ≤ 1 := by norm_num
  refine le_trans ?_ (truncated_le_gamma h0 h1 (2 ^ 13) (2 ^ 40) 10 G)
  rw [min_eq_left hG]
  unfold gammaLoQ
  push_cast
  rw [mul_sum]
  refine sum_le_sum fun g hg => ?_
  have hu : (revealQ 13 g : ℝ) = leafReveal (2 ^ 13) g := by
    unfold leafReveal revealQ; push_cast; ring
  have hgr : g ≤ 2 ^ 40 := by have := mem_range.mp hg; omega
  have hB : (1 - 2 ^ 40 / 2 ^ 45 : ℝ) ≤ (1 - 1 / 2 ^ 45) ^ (2 ^ 40 - g) := by
    have hb := one_add_mul_le_pow (a := -(1 / 2 ^ 45 : ℝ)) (by norm_num) (2 ^ 40 - g)
    have hc : ((2 ^ 40 - g : ℕ) : ℝ) ≤ 2 ^ 40 := by
      have : (2 ^ 40 - g : ℕ) ≤ 2 ^ 40 := Nat.sub_le _ _
      exact_mod_cast this
    have hd : ((2 ^ 40 - g : ℕ) : ℝ) * (1 / 2 ^ 45) ≤ 2 ^ 40 * (1 / 2 ^ 45) := by gcongr
    calc (1 - 2 ^ 40 / 2 ^ 45 : ℝ) ≤ 1 + ((2 ^ 40 - g : ℕ) : ℝ) * -(1 / 2 ^ 45) := by
          linarith
      _ ≤ (1 + -(1 / 2 ^ 45)) ^ (2 ^ 40 - g) := hb
      _ = (1 - 1 / 2 ^ 45) ^ (2 ^ 40 - g) := by ring
  have hpos : (0 : ℝ) ≤ ((2 ^ 40 : ℕ).choose g : ℝ) * (1 / 2 ^ 45) ^ g *
      leafReveal (2 ^ 13) g ^ 10 := by
    have := leafReveal_nonneg (2 ^ 13) g
    positivity
  rw [cast_chooseQ, hu, binomWeight]
  push_cast
  calc (1 - 2 ^ 40 / 2 ^ 45 : ℝ) * (((2 ^ 40 : ℕ).choose g : ℝ) * (1 / 2 ^ 45) ^ g *
        leafReveal (2 ^ 13) g ^ 10)
      ≤ (1 - 1 / 2 ^ 45) ^ (2 ^ 40 - g) * (((2 ^ 40 : ℕ).choose g : ℝ) * (1 / 2 ^ 45) ^ g *
        leafReveal (2 ^ 13) g ^ 10) := mul_le_mul_of_nonneg_right hB hpos
    _ = _ := by push_cast; ring

/-- `Γ ≥ 2^-130.24`, so `Γ ∈ [2^-130.24, 2^-130.23]`. -/
theorem le_Gam : (2 : ℝ) ^ (-130.24 : ℝ) ≤ Gam :=
  two_rpow_le_of_checkQ (N := 100) (by norm_num) (-13024) (by norm_num) (by decide +kernel)
    (gammaLoQ_le 12 (by norm_num)) (by decide +kernel)

theorem Gam_nonneg : 0 ≤ Gam := gamma_nonneg (by positivity) (by norm_num) _ _ _

/-- `Γ ≤ 7822208915061017503 / 2^193` (`ShrincsSl.gammaHi 10`). -/
theorem Gam_le_Q : Gam ≤ ((7822208915061017503 / 2 ^ 193 : ℚ) : ℝ) :=
  ShrincsSl.gamma_le 10 le_rfl

theorem gammaLo_le_Gam : ((gammaLoQ 12 : ℚ) : ℝ) ≤ Gam := gammaLoQ_le 12 (by norm_num)

/-- The itsr bound of Section 6.3: `itsrBound` at `h = 45`, `k = 10`, `t = 2^13`, `p = 2^40`,
`|K| = 2^128`, as a function of the query count. -/
noncomputable def itsrSl (q : ℕ) : ℝ := itsrBound 45 10 (2 ^ 13) (2 ^ 40) (2 ^ 128) q

/-- The rational upper bound on `itsrSl` from `ShrincsSl.gammaHi`. -/
def itsrSlQ (q : ℕ) : ℚ :=
  mainBoundQ ShrincsSl.gammaHi (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) q (2 ^ 128)

theorem itsrSl_le_Q (q : ℕ) : itsrSl q ≤ itsrSlQ q :=
  mainBound_le_Q ShrincsSl.theta_eq (by norm_num) ShrincsSl.gamma_le q _

theorem itsrSl_mono : Monotone itsrSl :=
  mainBound_mono (by positivity) (by norm_num) _ _ _ _

/-- The search part of the itsr term is `(q + 1) Γ`. -/
theorem searchTerm_Gam (q : ℕ) :
    searchTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) q = (q + 1) * Gam := rfl

theorem itsrSl_eq (q : ℕ) :
    itsrSl q = (q + 1) * Gam + pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) q (2 ^ 128) := rfl

theorem pullSl_nonneg (q : ℕ) : 0 ≤ pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) q (2 ^ 128) :=
  pullSum_nonneg (by positivity) (by norm_num) _ _ _ _ _

theorem mul_Gam_le_itsrSl (q : ℕ) : (q + 1) * Gam ≤ itsrSl q := by
  rw [itsrSl_eq]; linarith [pullSl_nonneg q]

/-- The pull part vanishes at `q = 0`: `itsrSl 0 = Γ`. -/
theorem itsrSl_zero : itsrSl 0 = Gam := by
  rw [itsrSl_eq]
  simp [pullSum]

/-- **Section 6.4**: `P_{45,10,2^13}(1, 2^40) < 2^-255.9`. -/
theorem pullSl_one_lt : pullSum (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 (2 ^ 128) <
    (2 : ℝ) ^ (-255.9 : ℝ) :=
  (ShrincsSl.table3_q1.2.1).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num))

/-- **Remark F.2** (quoted in Claim 6.1): the leading summand of the pull part is at most
`q(q+1)/2^256.98`, for every `q`. -/
theorem pullTerm_one_le (q : ℕ) :
    pullTerm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) q (2 ^ 128) 1 ≤
      (q : ℝ) * (q + 1) * (2 : ℝ) ^ (-256.98 : ℝ) := by
  have hA : pullHarm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1 ≤
      (pullHarmQ ShrincsSl.gammaHi (2 ^ 13) 10 1 : ℝ) :=
    pullHarm_le_Q ShrincsSl.gamma_le 1
  have hc : (2 : ℝ) ^ 40 * (2 ^ 128)⁻¹ * (1 / 2 ^ 45) *
      (pullHarmQ ShrincsSl.gammaHi (2 ^ 13) 10 1 : ℝ) ≤ (2 : ℝ) ^ (-256.98 : ℝ) := by
    refine le_two_rpow_of_check (x := 2 ^ 40 * (2 ^ 128)⁻¹ * (1 / 2 ^ 45) *
      pullHarmQ ShrincsSl.gammaHi (2 ^ 13) 10 1) (N := 100) (by norm_num) (-25698) (by norm_num)
      (le_of_eq (by push_cast; ring)) (by decide +kernel)
  have hA0 := pullHarm_nonneg (θ := 1 / 2 ^ 45) (by positivity) (by norm_num) (2 ^ 13) 10
    (2 ^ 40) 1
  unfold pullTerm
  simp only [Nat.choose_one_right, Nat.descFactorial_one, pow_one]
  have hq : (0 : ℝ) ≤ ((q : ℝ) + 1) * q := by positivity
  calc _ = ((q : ℝ) + 1) * q * (2 ^ 40 * (2 ^ 128)⁻¹ * (1 / 2 ^ 45) *
        pullHarm (1 / 2 ^ 45) (2 ^ 13) 10 (2 ^ 40) 1) := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]; ring
    _ ≤ ((q : ℝ) + 1) * q * (2 ^ 40 * (2 ^ 128)⁻¹ * (1 / 2 ^ 45) *
        (pullHarmQ ShrincsSl.gammaHi (2 ^ 13) 10 1 : ℝ)) := by gcongr
    _ ≤ ((q : ℝ) + 1) * q * (2 : ℝ) ^ (-256.98 : ℝ) := by gcongr
    _ = (q : ℝ) * (q + 1) * (2 : ℝ) ^ (-256.98 : ℝ) := by ring

/-! ## `ε_ds` -/

/-- The bound `ε_ds ≤ 2^-128 + 10 · 2^-256` of Theorem 4.1 (Assumption 4.1), as used in
Section 6.3. -/
noncomputable def epsDs : ℝ := 1 / 2 ^ 128 + 10 / 2 ^ 256

end ShrincsSecurity.Concrete

end
