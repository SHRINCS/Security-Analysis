module

public import ShrincsSecurity.ITSR.Concrete.Certify
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Classical generic bounds (Tables 6 and 7) and the query-counting figures

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), **Section 6.2, Table 6** (classical
column, lines 4873–4939), **Section 6.5, Table 7** (classical column, lines 5091–5116) and the
reading of the figures of **Section 6.1** (lines 4777–4783).

## The rows

Each row of Table 6 is a real function of the space sizes and of the query counts. For the
two-stage properties (SM-TCR, SM-TCR-EXCL, S-TCR(Prop)) the caption of Table 6 counts in the
`|P|` summands only the queries of the first stage; the rows therefore take two counts, `q` (both
stages, in the `|N|` and `|M|` summands) and `q₁` (first stage, in the `|P|` summand).

* `prfBound`: `q/|K|`;
* `smTcrBound`, `sTcrPropBound`: `(2q+1)/|N| + 2q₁/|P|`;
* `smPreBound`: `(q+1)/|N| + (q+1)/|M|`;
* `smUdBound`: `q/|M|`;
* `smTcrExclBound`: `(q+1)/|N| + q₁/|P|`;
* `smDsprBound`: `(2q+1)/|N|`, **conjectured** ([BHK+19, BH19]); it is never used as a theorem
  here: the stateless and full-scheme sums take the value substituted for the SM-DSPR insecurity
  as an argument, and the figures are stated for the conjectured row (`Paths`);
* `smRtcrBound = smRtcrHash + smRtcrRand`: `(q+1)/|N| + (Kq + pK(K-1)/2)/|R|` (Corollary G.1);
* `itsrBound`: `(q+1)Γ_k(p) + P_{h,k,t}(q, p)` (Theorem F.1 with Remark F.1), which is the bound
  `ITSR.mainBound` of `ITSR-Classical.pdf`, Theorem 2: its search part is `ITSR.searchTerm` and its
  pull part `ITSR.Concrete.pullSum`;
* `diReproBound`: `q_h/|X₁|` (Corollary C.3, classical line for the distinguishers `B₁`, `B₄`).

Table 7 (classical column) is the instance of these rows at the three places of the
reprogramming step: the pull part of `itsrBound`, the randomizer part `smRtcrRand` with `K = 1`,
and `diReproBound`.

The earlier classical bounds against which Remark 6.1 measures the gains are `itsrBoundF2`
(Theorem F.2, classical line) and the two instances of Lemma C.2, `smRtcrRandC2` (Lemma C.2 for
the algorithm `C` of the proof of Theorem G.1: `pK` calls and `q + pK + 1` queries) and
`diReproC2` (Lemma C.2 for the class of Corollary C.3: `q_s` calls, `q_s + q_h + 1` queries).

## The query-counting reading

Section 6.1 reports a classical bound `B(ξ)` by `log₂ ξ*`, where `ξ*` is the hash-query count at
which the bound reaches `1` (`xiStar B`, the least `ξ ∈ ℕ` with `1 ≤ B ξ`), and by `log₂ B(0)`.
`xiStar_bracket` turns two evaluations `B ξ₀ < 1 ≤ B ξ₁` of a monotone bound into
`ξ₀ < ξ* ≤ ξ₁`; the `check` lemmas turn natural-number and rational inequalities, decided by the
kernel, into statements about real powers of two and differences of base-2 logarithms.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete

open Finset ShrincsSecurity.ITSR ShrincsSecurity.ITSR.Concrete

/-! ## Table 6, classical column -/

/-- **Table 6**, PRF row: `Adv^prf ≤ q/|K|`. -/
noncomputable def prfBound (K q : ℝ) : ℝ := q / K

/-- **Table 6**, SM-TCR row: `Succ^sm-tcr ≤ (2q+1)/|N| + 2q₁/|P|`, with `q` the queries of both
stages and `q₁ ≤ q` those of the first stage (caption of Table 6). -/
noncomputable def smTcrBound (N P q q₁ : ℝ) : ℝ := (2 * q + 1) / N + 2 * q₁ / P

/-- **Table 6**, SM-PRE row: `Succ^sm-pre ≤ (q+1)/|N| + (q+1)/|M|`. -/
noncomputable def smPreBound (N M q : ℝ) : ℝ := (q + 1) / N + (q + 1) / M

/-- **Table 6**, SM-UD row: `Adv^sm-ud ≤ q/|M|`. -/
noncomputable def smUdBound (M q : ℝ) : ℝ := q / M

/-- **Table 6**, SM-TCR-EXCL row: `Succ^sm-tcr-excl ≤ (q+1)/|N| + q₁/|P|` (Theorem E.1). -/
noncomputable def smTcrExclBound (N P q q₁ : ℝ) : ℝ := (q + 1) / N + q₁ / P

/-- **Table 6**, S-TCR(Prop) row: `Succ^S-TCR(Prop) ≤ (2q+1)/|N| + 2q₁/|P|`. -/
noncomputable def sTcrPropBound (N P q q₁ : ℝ) : ℝ := (2 * q + 1) / N + 2 * q₁ / P

/-- **Table 6**, SM-DSPR row: `Adv^sm-dspr ≤ (2q+1)/|N|`. This row is **conjectured**
([BHK+19, BH19]; Section 7 of the paper), not proved. -/
noncomputable def smDsprBound (N q : ℝ) : ℝ := (2 * q + 1) / N

/-- **Table 6**, SM-rTCR row, hash part `(q+1)/|N|` (Corollary G.1). -/
noncomputable def smRtcrHash (N q : ℝ) : ℝ := (q + 1) / N

/-- **Table 6**, SM-rTCR row, randomizer part `(Kq + pK(K-1)/2)/|R|` (Corollary G.1); with
`K = 1` it is the second row of Table 7, `q/|R|`. -/
noncomputable def smRtcrRand (R K p q : ℝ) : ℝ := (K * q + p * K * (K - 1) / 2) / R

/-- **Table 6**, SM-rTCR row (Corollary G.1):
`Succ^SM-rTCR,K ≤ (q+1)/|N| + (Kq + pK(K-1)/2)/|R|`. -/
noncomputable def smRtcrBound (N R K p q : ℝ) : ℝ := smRtcrHash N q + smRtcrRand R K p q

/-- **Table 6**, itsr row (Theorem F.1 with Remark F.1): `(q+1) Γ_{h,k,t}(p) + P_{h,k,t}(q, p)`
for `θ = 2^-h`, `t` leaves, `k` trees, `p` challenges and `|K| = nK`. This is
`ITSR.mainBound` (`ITSR-Classical.pdf`, Theorem 2). -/
noncomputable def itsrBound (h k t p nK q : ℕ) : ℝ := mainBound (1 / 2 ^ h) t k p q nK

/-- **Corollary C.3**, ROM line for the distinguishers `B₁` and `B₄`: `Adv^DI-Repro ≤ q_h/|X₁|`;
the third row of Table 7. -/
noncomputable def diReproBound (X₁ qh : ℝ) : ℝ := qh / X₁

/-! ## The earlier classical bounds of Remark 6.1 -/

/-- **Theorem F.2**, classical line: `Succ^itsr ≤ p(q+p+1)/|K| + (q+1)Γ`. -/
noncomputable def itsrBoundF2 (h k t p nK q : ℕ) : ℝ :=
  (p : ℝ) * (q + p + 1) / nK + searchTerm (1 / 2 ^ h) t k p q

/-- **Lemma C.2** at the randomizer part of SM-rTCR: the algorithm `C` of the proof of
Theorem G.1 makes `pK` calls to `Reprogram` and `q + pK + 1` queries, so
`Adv^Repro ≤ pK(q + pK + 1)/|R|`. -/
noncomputable def smRtcrRandC2 (R K p q : ℝ) : ℝ := p * K * (q + p * K + 1) / R

/-- **Lemma C.2** at the reprogramming hop: `q_s` calls and `q_s + q_h + 1` queries give
`q_s(q_s + q_h + 1)/|X₁|` (proof of Corollary C.3). -/
noncomputable def diReproC2 (X₁ qs qh : ℝ) : ℝ := qs * (qs + qh + 1) / X₁

/-! ## Monotonicity of the bound of Theorem 2 in the query count -/

section Mono

variable {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
include h0 h1

theorem pullTerm_mono_q (t k r nK m : ℕ) {q q' : ℕ} (hq : q ≤ q') :
    pullTerm θ t k r q nK m ≤ pullTerm θ t k r q' nK m := by
  unfold pullTerm
  have := pullHarm_nonneg h0 h1 t k r m
  have hc : (q.choose m : ℝ) ≤ q'.choose m := by exact_mod_cast Nat.choose_le_choose m hq
  have hq' : (q : ℝ) ≤ q' := by exact_mod_cast hq
  gcongr

theorem pullSum_nonneg (t k r q nK : ℕ) : 0 ≤ pullSum θ t k r q nK :=
  sum_nonneg fun m _ => pullTerm_nonneg h0 h1 t k r q nK m

theorem searchTerm_nonneg (t k r q : ℕ) : 0 ≤ searchTerm θ t k r q := by
  unfold searchTerm
  have := gamma_nonneg h0 h1 t r k
  positivity

theorem searchTerm_le_mainBound (t k r q nK : ℕ) :
    searchTerm θ t k r q ≤ mainBound θ t k r q nK := by
  rw [mainBound_eq]
  linarith [pullSum_nonneg h0 h1 t k r q nK]

/-- The bound of Theorem 2 is nondecreasing in the query count `q`. -/
theorem mainBound_mono (t k r nK : ℕ) : Monotone fun q => mainBound θ t k r q nK := by
  intro q q' hq
  simp only [mainBound_eq, pullSum]
  have hg := gamma_nonneg h0 h1 t r k
  have hq' : (q : ℝ) ≤ q' := by exact_mod_cast hq
  refine add_le_add (by unfold searchTerm; gcongr) ?_
  calc ∑ m ∈ Icc 1 (min k (min q r)), pullTerm θ t k r q nK m
      ≤ ∑ m ∈ Icc 1 (min k (min q r)), pullTerm θ t k r q' nK m :=
        sum_le_sum fun m _ => pullTerm_mono_q h0 h1 t k r nK m hq
    _ ≤ ∑ m ∈ Icc 1 (min k (min q' r)), pullTerm θ t k r q' nK m :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (by omega))
          fun m _ _ => pullTerm_nonneg h0 h1 t k r q' nK m

end Mono

/-! ## `ξ*`: the query count at which a bound reaches `1` -/

/-- **`ξ*`** (Section 6.1): the least hash-query count `ξ` at which the bound `B` reaches `1`
(`0` if it never does). -/
noncomputable def xiStar (B : ℕ → ℝ) : ℕ := sInf {ξ | 1 ≤ B ξ}

theorem xiStar_le {B : ℕ → ℝ} {ξ : ℕ} (h : 1 ≤ B ξ) : xiStar B ≤ ξ := Nat.sInf_le h

/-- Two evaluations `B ξ₀ < 1 ≤ B ξ₁` of a nondecreasing bound locate `ξ*`: `ξ₀ < ξ* ≤ ξ₁`. -/
theorem xiStar_bracket {B : ℕ → ℝ} (hB : Monotone B) {ξ₀ ξ₁ : ℕ} (h₀ : B ξ₀ < 1)
    (h₁ : 1 ≤ B ξ₁) : ξ₀ < xiStar B ∧ xiStar B ≤ ξ₁ := by
  refine ⟨?_, xiStar_le h₁⟩
  by_contra hle
  have hmem : 1 ≤ B (xiStar B) := Nat.sInf_mem (s := {ξ | 1 ≤ B ξ}) ⟨ξ₁, h₁⟩
  linarith [hB (not_lt.mp hle)]

/-- Below `ξ*` the bound is below `1`. -/
theorem lt_one_of_lt_xiStar {B : ℕ → ℝ} {ξ : ℕ} (h : ξ < xiStar B) : B ξ < 1 := by
  by_contra hle
  exact absurd (xiStar_le (not_lt.mp hle)) (not_le.mpr h)

/-- A pointwise larger bound reaches `1` no later: `B ≤ B'` gives `ξ*(B') ≤ ξ*(B)`, provided `B`
reaches `1` at all. -/
theorem xiStar_anti {B B' : ℕ → ℝ} (h : ∀ ξ, B ξ ≤ B' ξ) {ξ₁ : ℕ} (h₁ : 1 ≤ B ξ₁) :
    xiStar B' ≤ xiStar B :=
  xiStar_le ((Nat.sInf_mem (s := {ξ | 1 ≤ B ξ}) ⟨ξ₁, h₁⟩).trans (h _))

theorem lt_one_of_Q {X : ℝ} {x : ℚ} (hX : X ≤ x) (h : x < 1) : X < 1 :=
  hX.trans_lt (by exact_mod_cast h)

theorem one_le_of_Q {X : ℝ} {x : ℚ} (hX : (x : ℝ) ≤ X) (h : 1 ≤ x) : 1 ≤ X :=
  le_trans (by exact_mod_cast h) hX

/-! ## Kernel checks -/

/-- If `y^N ≤ 2^B` for a natural number `y`, then `y ≤ 2^(B / N)`. -/
theorem le_two_rpow_of_check_nat {y : ℕ} {b : ℝ} {N : ℕ} (hN : 0 < N) (B : ℕ)
    (hb : b = (B : ℝ) / N) (hy : y ^ N ≤ 2 ^ B) : (y : ℝ) ≤ (2 : ℝ) ^ b := by
  by_contra hlt
  have h1 : ((2 : ℝ) ^ b) ^ N < (y : ℝ) ^ N :=
    pow_lt_pow_left₀ (not_le.mp hlt) (by positivity) (by omega)
  have h2 : ((2 : ℝ) ^ b) ^ N = (2 : ℝ) ^ B := by
    rw [← Real.rpow_mul_natCast (by norm_num), hb, div_mul_cancel₀ _ (by exact_mod_cast hN.ne'),
      Real.rpow_natCast]
  have h3 : ((y ^ N : ℕ) : ℝ) ≤ ((2 ^ B : ℕ) : ℝ) := by exact_mod_cast hy
  push_cast at h3
  linarith

/-- If `x ≤ X` and `2^B ≤ x^N` for a nonnegative rational `x`, then `2^(B / N) ≤ X`. -/
theorem two_rpow_le_of_checkQ {X : ℝ} {x : ℚ} {b : ℝ} {N : ℕ} (hN : 0 < N) (B : ℤ)
    (hb : b = (B : ℝ) / N) (hx0 : 0 ≤ x) (hX : (x : ℝ) ≤ X) (hx : (2 : ℚ) ^ B ≤ x ^ N) :
    (2 : ℝ) ^ b ≤ X := by
  refine le_trans ?_ hX
  by_contra hlt
  have h1 : (x : ℝ) ^ N < ((2 : ℝ) ^ b) ^ N :=
    pow_lt_pow_left₀ (not_le.mp hlt) (by exact_mod_cast hx0) (by omega)
  have h2 : ((2 : ℝ) ^ b) ^ N = (2 : ℝ) ^ B := by
    rw [← Real.rpow_mul_natCast (by norm_num), hb, div_mul_cancel₀ _ (by exact_mod_cast hN.ne'),
      Real.rpow_intCast]
  have h3 : (((2 : ℚ) ^ B : ℚ) : ℝ) ≤ ((x ^ N : ℚ) : ℝ) := by exact_mod_cast hx
  push_cast at h3
  linarith

/-- A two-sided bracket of a positive real by powers of two, from rational bounds:
`2^(B₀/N) ≤ X ≤ 2^(B₁/N)`. -/
theorem two_rpow_bracket {X : ℝ} {lo hi : ℚ} {b₀ b₁ : ℝ} {N : ℕ} (hN : 0 < N) (B₀ B₁ : ℤ)
    (hb₀ : b₀ = (B₀ : ℝ) / N) (hb₁ : b₁ = (B₁ : ℝ) / N) (hlo0 : 0 ≤ lo) (hlo : (lo : ℝ) ≤ X)
    (hhi : X ≤ (hi : ℝ)) (hclo : (2 : ℚ) ^ B₀ ≤ lo ^ N) (hchi : hi ^ N ≤ (2 : ℚ) ^ B₁) :
    (2 : ℝ) ^ b₀ ≤ X ∧ X ≤ (2 : ℝ) ^ b₁ :=
  ⟨two_rpow_le_of_checkQ hN B₀ hb₀ hlo0 hlo hclo, le_two_rpow_of_check hN B₁ hb₁ hhi hchi⟩

/-- `ξ*` bracketed by powers of two: from `ξ₀ < ξ* ≤ ξ₁`, `2^B₀ ≤ (ξ₀ + 1)^N` and
`ξ₁^N ≤ 2^B₁`, `2^(B₀/N) ≤ ξ* ≤ 2^(B₁/N)`. -/
theorem xiStar_two_rpow_bracket {B : ℕ → ℝ} {ξ₀ ξ₁ : ℕ} (h : ξ₀ < xiStar B ∧ xiStar B ≤ ξ₁)
    {y₀ y₁ : ℝ} {N : ℕ} (hN : 0 < N) (B₀ B₁ : ℕ) (hy₀ : y₀ = (B₀ : ℝ) / N)
    (hy₁ : y₁ = (B₁ : ℝ) / N) (h₀ : 2 ^ B₀ ≤ (ξ₀ + 1) ^ N) (h₁ : ξ₁ ^ N ≤ 2 ^ B₁) :
    (2 : ℝ) ^ y₀ ≤ xiStar B ∧ (xiStar B : ℝ) ≤ (2 : ℝ) ^ y₁ := by
  constructor
  · refine (ITSR.Concrete.two_rpow_le_of_check hN B₀ hy₀ h₀).trans ?_
    exact_mod_cast h.1
  · refine le_trans ?_ (le_two_rpow_of_check_nat hN B₁ hy₁ h₁)
    exact_mod_cast h.2

/-- Differences of base-2 logarithms from rational brackets: if `a_lo ≤ a ≤ a_hi`,
`b_lo ≤ b ≤ b_hi` (all positive), `2^G b_hi^N ≤ a_lo^N` and `a_hi^N ≤ 2^G' b_lo^N`, then
`G/N ≤ log₂ a - log₂ b ≤ G'/N`. -/
theorem logb_sub_bracket {a b : ℝ} {alo ahi blo bhi : ℚ} {g g' : ℝ} {N : ℕ} (hN : 0 < N)
    (G G' : ℤ) (hg : g = (G : ℝ) / N) (hg' : g' = (G' : ℝ) / N) (halo0 : 0 < alo)
    (hblo0 : 0 < blo) (halo : (alo : ℝ) ≤ a) (hahi : a ≤ (ahi : ℝ)) (hblo : (blo : ℝ) ≤ b)
    (hbhi : b ≤ (bhi : ℝ)) (hlo : (2 : ℚ) ^ G * bhi ^ N ≤ alo ^ N)
    (hhi : ahi ^ N ≤ (2 : ℚ) ^ G' * blo ^ N) :
    g ≤ Real.logb 2 a - Real.logb 2 b ∧ Real.logb 2 a - Real.logb 2 b ≤ g' := by
  have ha : (0 : ℝ) < a := lt_of_lt_of_le (by exact_mod_cast halo0) halo
  have hb : (0 : ℝ) < b := lt_of_lt_of_le (by exact_mod_cast hblo0) hblo
  have hbhi0 : (0 : ℝ) ≤ bhi := hb.le.trans hbhi
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : ∀ c : ℤ, ∀ e : ℝ, e = (c : ℝ) / N → ((2 : ℝ) ^ e) ^ N = (2 : ℝ) ^ c := by
    intro c e he
    rw [← Real.rpow_mul_natCast (by norm_num), he, div_mul_cancel₀ _ hNr, Real.rpow_intCast]
  rw [← Real.logb_div ha.ne' hb.ne']
  have hab : 0 < a / b := div_pos ha hb
  constructor
  · rw [Real.le_logb_iff_rpow_le (by norm_num) hab, le_div_iff₀ hb]
    have h1 : ((2 : ℝ) ^ g * bhi) ^ N ≤ (alo : ℝ) ^ N := by
      rw [mul_pow, hpow G g hg]
      have := (Rat.cast_le (K := ℝ)).mpr hlo
      push_cast at this
      exact this
    have h2 : (2 : ℝ) ^ g * bhi ≤ alo :=
      (pow_le_pow_iff_left₀ (by positivity) (by exact_mod_cast halo0.le) hN.ne').mp h1
    calc (2 : ℝ) ^ g * b ≤ 2 ^ g * bhi := by gcongr
      _ ≤ alo := h2
      _ ≤ a := halo
  · rw [Real.logb_le_iff_le_rpow (by norm_num) hab, div_le_iff₀ hb]
    have h1 : (ahi : ℝ) ^ N ≤ ((2 : ℝ) ^ g' * blo) ^ N := by
      rw [mul_pow, hpow G' g' hg']
      have := (Rat.cast_le (K := ℝ)).mpr hhi
      push_cast at this
      exact this
    have h2 : (ahi : ℝ) ≤ 2 ^ g' * blo :=
      (pow_le_pow_iff_left₀ (ha.le.trans hahi) (by positivity) hN.ne').mp h1
    calc a ≤ ahi := hahi
      _ ≤ 2 ^ g' * blo := h2
      _ ≤ 2 ^ g' * b := by gcongr

/-- `logb_sub_bracket` for two values of `ξ*` located by `xiStar_bracket`:
from `ξ₀ < ξ* ≤ ξ₁` and `ξ₀' < ξ'* ≤ ξ₁'`, `2^G ξ₁'^N ≤ (ξ₀ + 1)^N` and
`ξ₁^N ≤ 2^G' (ξ₀' + 1)^N` give `G/N ≤ log₂ ξ* - log₂ ξ'* ≤ G'/N`. -/
theorem logb_xiStar_sub_bracket {B B' : ℕ → ℝ} {ξ₀ ξ₁ ξ₀' ξ₁' : ℕ}
    (h : ξ₀ < xiStar B ∧ xiStar B ≤ ξ₁) (h' : ξ₀' < xiStar B' ∧ xiStar B' ≤ ξ₁') {g g' : ℝ}
    {N : ℕ} (hN : 0 < N) (G G' : ℤ) (hg : g = (G : ℝ) / N) (hg' : g' = (G' : ℝ) / N)
    (hlo : (2 : ℚ) ^ G * (ξ₁' : ℚ) ^ N ≤ ((ξ₀ : ℚ) + 1) ^ N)
    (hhi : (ξ₁ : ℚ) ^ N ≤ (2 : ℚ) ^ G' * ((ξ₀' : ℚ) + 1) ^ N) :
    g ≤ Real.logb 2 (xiStar B) - Real.logb 2 (xiStar B') ∧
      Real.logb 2 (xiStar B) - Real.logb 2 (xiStar B') ≤ g' :=
  logb_sub_bracket hN G G' hg hg' (by positivity) (by positivity)
    (by push_cast; exact_mod_cast h.1) (by exact_mod_cast h.2)
    (by push_cast; exact_mod_cast h'.1) (by exact_mod_cast h'.2) hlo hhi

/-- A bracket by powers of two is a bracket of the base-2 logarithm. -/
theorem logb_bracket {X a b : ℝ} (h : (2 : ℝ) ^ a ≤ X ∧ X ≤ (2 : ℝ) ^ b) :
    a ≤ Real.logb 2 X ∧ Real.logb 2 X ≤ b := by
  have hX : 0 < X := lt_of_lt_of_le (by positivity) h.1
  exact ⟨(Real.le_logb_iff_rpow_le (by norm_num) hX).2 h.1,
    (Real.logb_le_iff_le_rpow (by norm_num) hX).2 h.2⟩

/-- `A/N ≤ log₂ X ≤ B/N` from rational bounds `lo ≤ X ≤ hi` with `2^A ≤ lo^N`, `hi^N ≤ 2^B`. -/
theorem logb_bracket_of_Q {X : ℝ} {lo hi : ℚ} {a b : ℝ} {N : ℕ} (hN : 0 < N) (A B : ℤ)
    (ha : a = (A : ℝ) / N) (hb : b = (B : ℝ) / N) (hlo0 : 0 ≤ lo) (hlo : (lo : ℝ) ≤ X)
    (hhi : X ≤ (hi : ℝ)) (hcl : (2 : ℚ) ^ A ≤ lo ^ N) (hch : hi ^ N ≤ (2 : ℚ) ^ B) :
    a ≤ Real.logb 2 X ∧ Real.logb 2 X ≤ b :=
  logb_bracket (two_rpow_bracket hN A B ha hb hlo0 hlo hhi hcl hch)

/-- `A/N ≤ log₂ ξ* ≤ B/N` from `ξ₀ < ξ* ≤ ξ₁`, `2^A ≤ (ξ₀ + 1)^N` and `ξ₁^N ≤ 2^B`. -/
theorem logb_xiStar_bracket {B : ℕ → ℝ} {ξ₀ ξ₁ : ℕ} (h : ξ₀ < xiStar B ∧ xiStar B ≤ ξ₁)
    {a b : ℝ} {N : ℕ} (hN : 0 < N) (A B' : ℕ) (ha : a = (A : ℝ) / N) (hb : b = (B' : ℝ) / N)
    (h₀ : 2 ^ A ≤ (ξ₀ + 1) ^ N) (h₁ : ξ₁ ^ N ≤ 2 ^ B') :
    a ≤ Real.logb 2 (xiStar B) ∧ Real.logb 2 (xiStar B) ≤ b :=
  logb_bracket (xiStar_two_rpow_bracket h hN A B' ha hb h₀ h₁)

end ShrincsSecurity.Concrete

end
