module

public import ShrincsSecurity.Scheme.WotsC
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityBounds
import Mathlib.Data.List.GetD

/-!
# Grinding: the target-sum probability, signing failure, grind-completeness

`SHRINCS-Security-Analysis.pdf`, Section 3.1: Assumption 3.1 (grinding heuristic), Lemma 3.1 (ii)
(signing failure) with its concrete figures, Conjecture 3.1 (grind-completeness of `H_grind`) and
Lemma 3.2 (grind-completeness in the ideal model).

* **Counting.** `targetSumCount w l S` is the number of digit vectors in `[0, w)^l` with sum `S`
  (the coefficient of `x^S` in `(1 + ⋯ + x^{w−1})^l`). The dynamic program `targetSumCountDP`
  is proved equal to it, and evaluating it by `decide +kernel` gives `N = targetSumCount 16 32 240`
  (`targetSumCount_shrincs`), which also equals the paper's inclusion–exclusion closed form
  (`shrincsN_eq_closedForm`).
* **`p_sum`** is `N / w^lsf` (`pSum`). The encoding part of Assumption 3.1 (`NBitEncoding`: `Y`
  has `2^n` elements and an injective byte encoding) makes the digit vector a bijection onto
  `[0, w)^lsf`, so a uniform value meets the target sum with probability `p_sum`
  (`prob_targetSum`).
* **Ideal model.** The heuristic part of Assumption 3.1 (values of `H_grind` at pairwise distinct
  inputs are independent and uniform) is modelled by sampling `H_grind` restricted to the grinding
  inputs `(PK.seed, T, md, ctr)` as a uniform function (`withGrind`). A single search fails with
  probability exactly `(1 − p_sum)^(2^c)` (`prob_grind_fail`), `L` searches with probability at
  most `L (1 − p_sum)^(2^c)` (`prob_execution_fail_le`), and Conjecture 3.1 fails with probability
  at most `ε_gc = 2^n 2^72 2^(2n) (1 − p_sum)^(2^c)` (`prob_not_grindComplete_le_epsGc`).
* **Numbers.** At the SHRINCS parameters, `(1 − p_sum)^(2^16) < 2^−1450`, `2^64 (1 − p_sum)^(2^16)
  < 2^−1386`, `ε_gc < 2^−994` (certified by exact natural-number arithmetic in the kernel), and
  `65.6 < 1/p_sum < 65.8`.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.Grinding

/-! ## Counting target-sum digit vectors -/

/-- The number of digit vectors `(a_0, …, a_{l−1}) ∈ [0, w)^l` with `∑ a_i = S`: the coefficient
of `x^S` in `(1 + x + ⋯ + x^{w−1})^l`. -/
def targetSumCount (w l S : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin l → Fin w => ∑ i, (v i : ℕ) = S).card

theorem targetSumCount_zero (w S : ℕ) : targetSumCount w 0 S = if S = 0 then 1 else 0 := by
  unfold targetSumCount
  split_ifs with h
  · simp [h, Finset.filter_true_of_mem]
  · simp [Ne.symm h]

/-- The coefficient recurrence: condition on the first digit `a`. -/
theorem targetSumCount_succ (w l S : ℕ) :
    targetSumCount w (l + 1) S =
      ∑ a ∈ Finset.range w, if a ≤ S then targetSumCount w l (S - a) else 0 := by
  unfold targetSumCount
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ : Fin (l + 1) => Fin w).sum_comp,
    Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  split_ifs with ha
  · rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  · exact Finset.sum_eq_zero fun u _ => ite_eq_right_iff.2 fun h => by omega

/-! ### A verified dynamic program -/

/-- Add the row `prev`, shifted right by `a`, to the accumulator `acc` (truncating to `acc`). -/
def addShift (prev acc : List ℕ) (a : ℕ) : List ℕ :=
  List.zipWith (· + ·) acc (List.replicate a 0 ++ prev)

/-- One step of the dynamic program: multiply by `1 + x + ⋯ + x^{w−1}`, truncated to degree `M`. -/
def dpStep (w M : ℕ) (prev : List ℕ) : List ℕ :=
  (List.range w).foldl (addShift prev) (List.replicate (M + 1) 0)

/-- The coefficients of `x^0, …, x^M` in `(1 + x + ⋯ + x^{w−1})^l`. -/
def dpRow (w M : ℕ) : ℕ → List ℕ
  | 0 => (List.range (M + 1)).map fun S => if S = 0 then 1 else 0
  | l + 1 => dpStep w M (dpRow w M l)

/-- `targetSumCount` computed by the dynamic program. -/
def targetSumCountDP (w l S : ℕ) : ℕ := (dpRow w S l).getD S 0

theorem getD_zipWith_add {l₁ l₂ : List ℕ} {i : ℕ} (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    (List.zipWith (· + ·) l₁ l₂).getD i 0 = l₁.getD i 0 + l₂.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

theorem getD_replicate_append (prev : List ℕ) (a i : ℕ) :
    (List.replicate a 0 ++ prev).getD i 0 = if a ≤ i then prev.getD (i - a) 0 else 0 := by
  split_ifs with h
  · rw [List.getD_append_right _ _ _ _ (by simpa using h), List.length_replicate]
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp

theorem foldl_addShift {M : ℕ} (prev : List ℕ) (hprev : prev.length = M + 1) :
    ∀ (as : List ℕ) (acc : List ℕ), acc.length = M + 1 →
      (as.foldl (addShift prev) acc).length = M + 1 ∧
        ∀ S ≤ M, (as.foldl (addShift prev) acc).getD S 0 =
          acc.getD S 0 + (as.map fun a => if a ≤ S then prev.getD (S - a) 0 else 0).sum
  | [], acc, h => ⟨h, fun S _ => by simp⟩
  | a :: as, acc, h => by
    have hlen : (addShift prev acc a).length = M + 1 := by
      simp [addShift, h, hprev]
    obtain ⟨ih₁, ih₂⟩ := foldl_addShift prev hprev as _ hlen
    refine ⟨ih₁, fun S hS => ?_⟩
    rw [List.foldl_cons, ih₂ S hS, addShift, getD_zipWith_add (by omega) (by simp; omega),
      getD_replicate_append, List.map_cons, List.sum_cons]
    ring

theorem sum_map_range (f : ℕ → ℕ) (w : ℕ) :
    ((List.range w).map f).sum = ∑ a ∈ Finset.range w, f a := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem dpRow_spec (w M : ℕ) :
    ∀ l, (dpRow w M l).length = M + 1 ∧ ∀ S ≤ M, (dpRow w M l).getD S 0 = targetSumCount w l S
  | 0 => ⟨by simp [dpRow], fun S hS => by
      rw [targetSumCount_zero, dpRow, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega)]
      rfl⟩
  | l + 1 => by
    obtain ⟨ih₁, ih₂⟩ := dpRow_spec w M l
    obtain ⟨h₁, h₂⟩ := foldl_addShift (dpRow w M l) ih₁ (List.range w) _ (List.length_replicate ..)
    refine ⟨h₁, fun S hS => ?_⟩
    rw [dpRow, dpStep, h₂ S hS, targetSumCount_succ, sum_map_range]
    have h0 : (List.replicate (M + 1) 0).getD S 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, hS]
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · exact ih₂ _ (by omega)
    · rfl

/-- The dynamic program computes `targetSumCount`. -/
theorem targetSumCountDP_eq (w l S : ℕ) : targetSumCountDP w l S = targetSumCount w l S :=
  (dpRow_spec w S l).2 S le_rfl

/-! ### The SHRINCS count -/

/-- `N`, the number of `128`-bit strings whose `32` base-`16` digits sum to `240` (Lemma 3.1). -/
def shrincsN : ℕ := 5181241160064611531897369560287267312

/-- **Lemma 3.1**: at the SHRINCS parameters there are exactly `N` target-sum digit vectors,
computed by the verified dynamic program. -/
theorem targetSumCount_shrincs : targetSumCount 16 32 240 = shrincsN := by
  rw [← targetSumCountDP_eq]
  decide +kernel

/-- The paper's closed form `N = ∑_{j=0}^{15} (−1)^j C(32, j) C(271 − 16j, 31)` (Lemma 3.1). -/
theorem shrincsN_eq_closedForm :
    (shrincsN : ℤ) = ∑ j ∈ Finset.range 16,
      (-1) ^ j * (Nat.choose 32 j : ℤ) * (Nat.choose (271 - 16 * j) 31 : ℤ) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- `N ≈ 2^121.96` (Lemma 3.1). -/
theorem shrincsN_bounds : 2 ^ 121 < shrincsN ∧ shrincsN < 2 ^ 122 := by
  decide +kernel

/-! ## The target-sum probability `p_sum` (Assumption 3.1) -/

/-- The fraction of digit vectors in `[0, w)^l` with digit sum `S`. -/
noncomputable def pSumOf (w l S : ℕ) : ℝ := targetSumCount w l S / (w : ℝ) ^ l

/-- **`p_sum`** (Assumption 3.1): the probability that a uniform `n`-bit value meets the target
sum, `|{x ∈ {0,1}^n : ∑ a_i(x) = Swn}| / 2^n`, written over the `w^lsf = 2^n` digit vectors. -/
noncomputable def pSum (P : Params) : ℝ := pSumOf P.w P.lsf P.Swn

theorem pSumOf_nonneg (w l S : ℕ) : 0 ≤ pSumOf w l S := by
  unfold pSumOf; positivity

theorem pSumOf_le_one (w l S : ℕ) : pSumOf w l S ≤ 1 := by
  unfold pSumOf
  have h : targetSumCount w l S ≤ w ^ l := by
    unfold targetSumCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact div_le_one_of_le₀ (by exact_mod_cast h) (by positivity)

/-- At the SHRINCS parameters, `p_sum = N / 2^128`. -/
theorem pSum_shrincs : pSum shrincs = (shrincsN : ℝ) / 2 ^ 128 := by
  have hw : shrincs.w = 16 := by decide
  have hl : shrincs.lsf = 32 := by decide
  have hS : shrincs.Swn = 240 := by decide
  rw [pSum, pSumOf, hw, hl, hS, targetSumCount_shrincs]
  norm_num

theorem one_sub_pSum_shrincs :
    1 - pSum shrincs = ((2 ^ 128 - shrincsN : ℕ) : ℝ) / ((2 ^ 128 : ℕ) : ℝ) := by
  have hle : shrincsN ≤ 2 ^ 128 := by decide +kernel
  rw [pSum_shrincs, Nat.cast_sub hle]
  field_simp
  ring

/-- `p_sum ≈ 0.015226` (Lemma 3.1). -/
theorem pSum_shrincs_bounds : 0.015226 < pSum shrincs ∧ pSum shrincs < 0.015227 := by
  rw [pSum_shrincs, shrincsN]
  norm_num

/-- `1 / p_sum ≈ 65.7`: one attempt in about `65.7` meets the target sum (Lemma 3.1). -/
theorem inv_pSum_shrincs_bounds : 65.6 < 1 / pSum shrincs ∧ 1 / pSum shrincs < 65.8 := by
  rw [pSum_shrincs, shrincsN]
  norm_num

/-! ## The encoding part of Assumption 3.1 -/

variable {P : Params}

/-- The encoding part of **Assumption 3.1**: `Y` models `{0, 1}^n`, i.e. it has `2^n` elements
and the byte encoding from which the digits are read is injective. Then the base-`w` digit
vector of `y ∈ Y` ranges bijectively over `[0, w)^lsf` (`digitVec_bijective`), so a uniform
`y` has uniform digits and meets the target sum with probability `p_sum`
(`prob_targetSum`). -/
structure NBitEncoding (pr : Primitives P) [Fintype pr.Y] : Prop where
  card_Y : Fintype.card pr.Y = 2 ^ P.n
  yToBytes_injective : Function.Injective pr.yToBytes

/-- The base-`w` digit vector `(a_0(y), …, a_{lsf−1}(y)) ∈ [0, w)^lsf`. -/
def digitVec (pr : Primitives P) (y : pr.Y) : Fin P.lsf → Fin P.w :=
  fun i => ⟨WotsC.digit pr y i, WotsC.digit_lt pr y i⟩

theorem digits_eq_ofFn (pr : Primitives P) (y : pr.Y) :
    WotsC.digits pr y = List.ofFn fun i : Fin P.lsf => (digitVec pr y i : ℕ) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [digitVec, WotsC.digit, List.getD_eq_getElem?_getD]

/-- The target-sum predicate in terms of the digit vector. -/
theorem targetSum_iff (pr : Primitives P) (y : pr.Y) :
    WotsC.TargetSum pr y ↔ ∑ i, (digitVec pr y i : ℕ) = P.Swn := by
  rw [WotsC.TargetSum, WotsC.digitSum, digits_eq_ofFn, List.sum_ofFn]

theorem digitVec_injective (hP : P.Valid) (pr : Primitives P)
    (hinj : Function.Injective pr.yToBytes) : Function.Injective (digitVec pr) := by
  intro y y' h
  refine WotsC.digits_injective pr hP hinj ?_
  rw [digits_eq_ofFn, digits_eq_ofFn, h]

theorem w_pow_lsf (hP : P.Valid) : P.w ^ P.lsf = 2 ^ P.n := by
  rw [Params.w, Params.lsf, ← pow_mul, Nat.mul_div_cancel' hP.lgw_dvd]

theorem digitVec_bijective (hP : P.Valid) (pr : Primitives P) [Fintype pr.Y]
    (henc : NBitEncoding pr) : Function.Bijective (digitVec pr) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨digitVec_injective hP pr henc.yToBytes_injective, by simp [henc.card_Y, w_pow_lsf hP]⟩

/-- Under the encoding part of Assumption 3.1, exactly `targetSumCount w lsf Swn` values of `Y`
meet the target sum. -/
theorem card_targetSum (hP : P.Valid) (pr : Primitives P) [Fintype pr.Y]
    (henc : NBitEncoding pr) :
    (Finset.univ.filter (WotsC.TargetSum pr)).card = targetSumCount P.w P.lsf P.Swn := by
  rw [targetSumCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    ((Equiv.ofBijective _ (digitVec_bijective hP pr henc)).subtypeEquiv fun y => targetSum_iff pr y)

/-- A uniform `n`-bit value meets the target sum with probability `p_sum`. -/
theorem prob_targetSum (hP : P.Valid) (pr : Primitives P) [Fintype pr.Y] [SampleableType pr.Y]
    (henc : NBitEncoding pr) :
    Pr{let y ← $ᵗ pr.Y}[WotsC.TargetSum pr y] = ENNReal.ofReal (pSum P) := by
  rw [SampleableType.prEvent_uniformSample_eq_ofReal, card_targetSum hP pr henc, henc.card_Y,
    ← w_pow_lsf hP, pSum, pSumOf]
  push_cast
  rfl

/-- A uniform `n`-bit value misses the target sum with probability `1 − p_sum`. -/
theorem prob_not_targetSum (hP : P.Valid) (pr : Primitives P) [Fintype pr.Y]
    [SampleableType pr.Y] (henc : NBitEncoding pr) :
    Pr{let y ← $ᵗ pr.Y}[¬ WotsC.TargetSum pr y] = ENNReal.ofReal (1 - pSum P) := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (WotsC.TargetSum pr)
  rw [Finset.card_univ, card_targetSum hP pr henc] at h
  have hY : (Fintype.card pr.Y : ℝ) = (P.w : ℝ) ^ P.lsf := by
    rw [henc.card_Y, ← w_pow_lsf hP]; push_cast; rfl
  have hY0 : (Fintype.card pr.Y : ℝ) ≠ 0 := by
    rw [henc.card_Y]; positivity
  rw [SampleableType.prEvent_uniformSample_eq_ofReal, pSum, pSumOf, ← hY]
  congr 1
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hY0]
  exact_mod_cast by omega

/-! ## The ideal model of `H_grind` (Assumption 3.1) -/

section Ideal

variable {Y : Type} [Fintype Y] [SampleableType Y] (T : Y → Prop) [DecidablePred T]

/-- A counter search over a table of `k` independent uniform values fails (no entry meets `T`)
with probability `Pr[¬ T]^k`. -/
theorem prob_table_all_not (k : ℕ) :
    Pr{let t ← $ᵗ (Fin k → Y)}[∀ j, ¬ T (t j)] = Pr{let y ← $ᵗ Y}[¬ T y] ^ k := by
  have hset : (Finset.univ.filter fun t : Fin k → Y => ∀ j, ¬ T (t j)) =
      Fintype.piFinset fun _ => Finset.univ.filter fun y => ¬ T y := by
    ext t
    simp
  rw [SampleableType.prEvent_uniformSample_eq_ofReal,
    SampleableType.prEvent_uniformSample_eq_ofReal,
    ← ENNReal.ofReal_pow (by positivity), hset, Fintype.card_piFinset_const, Fintype.card_pi_const]
  push_cast
  rw [div_pow]

/-- The value of a uniform function at a fixed point is uniform. -/
theorem prob_apply_uniform {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z] [SampleableType Z]
    [SampleableType (I → Z)] (x : I) (p : Z → Prop) [DecidablePred p] :
    Pr{let H ← $ᵗ (I → Z)}[p (H x)] = Pr{let z ← $ᵗ Z}[p z] := by
  have hset : (Finset.univ.filter fun H : I → Z => p (H x)) =
      Fintype.piFinset fun i => if i = x then Finset.univ.filter p else Finset.univ := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · subst hi; simpa using h
      · exact Finset.mem_univ _
    · intro h
      simpa using h x
  have hrest : ∏ i ∈ Finset.univ.erase x,
      (if i = x then Finset.univ.filter p else (Finset.univ : Finset Z)).card =
        ∏ i ∈ Finset.univ.erase x, Fintype.card Z :=
    Finset.prod_congr rfl fun i hi => by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (Finset.ne_of_mem_erase hi)), Finset.card_univ]
  rw [SampleableType.prEvent_uniformSample_eq_ofReal,
    SampleableType.prEvent_uniformSample_eq_ofReal,
    hset, Fintype.card_piFinset, Fintype.card_pi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ x), hrest, ite_eq_left_of_eq_true _ _ (eq_self x)]
  have hR : (∏ i ∈ Finset.univ.erase x, (Fintype.card Z : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => by
      have : 0 < Fintype.card Z := Fintype.card_pos_iff.2 inferInstance
      positivity
  push_cast
  rw [mul_div_mul_right _ _ hR]

/-- **Ideal grinding, one call**: for a uniform function `H : I → Fin k → Y` and any input `x`,
the counter search at `x` fails with probability `Pr[¬ T]^k`. -/
theorem prob_search_fail {I : Type} [Fintype I] [DecidableEq I] (k : ℕ)
    [SampleableType (I → Fin k → Y)] (x : I) :
    Pr{let H ← $ᵗ (I → Fin k → Y)}[∀ j, ¬ T (H x j)] = Pr{let y ← $ᵗ Y}[¬ T y] ^ k := by
  rw [prob_apply_uniform x fun t : Fin k → Y => ∀ j, ¬ T (t j), prob_table_all_not]

/-- **Ideal grinding, union bound**: some search among `L` calls at inputs `xs j` fails with
probability at most `L · Pr[¬ T]^k` (the inputs need not be distinct). -/
theorem prob_some_search_fail_le {I : Type} [Fintype I] [DecidableEq I] (k L : ℕ)
    [SampleableType (I → Fin k → Y)] (xs : Fin L → I) :
    Pr{let H ← $ᵗ (I → Fin k → Y)}[∃ l, ∀ j, ¬ T (H (xs l) j)] ≤
      L * Pr{let y ← $ᵗ Y}[¬ T y] ^ k := by
  have h := prEvent_exists_le_card_mul ($ᵗ (I → Fin k → Y))
    (fun l (H : I → Fin k → Y) => ∀ j, ¬ T (H (xs l) j))
    (ε := Pr{let y ← $ᵗ Y}[¬ T y] ^ k) fun l => (prob_search_fail T k (xs l)).le
  simpa using h

/-- **Ideal grinding, all inputs**: some input of a uniform `H : I → Fin k → Y` has no valid
counter with probability at most `|I| · Pr[¬ T]^k`. -/
theorem prob_exists_search_fail_le {I : Type} [Fintype I] [DecidableEq I] (k : ℕ)
    [SampleableType (I → Fin k → Y)] :
    Pr{let H ← $ᵗ (I → Fin k → Y)}[∃ x, ∀ j, ¬ T (H x j)] ≤
      Fintype.card I * Pr{let y ← $ᵗ Y}[¬ T y] ^ k :=
  prEvent_exists_le_card_mul _ (fun x (H : I → Fin k → Y) => ∀ j, ¬ T (H x j))
    fun x => (prob_search_fail T k x).le

end Ideal

/-! ## Lemma 3.1 (ii) and Lemma 3.2 for SHRINCS grinding -/

/-- The grinding tweaks `T_g` (Section 2.2, proof of Lemma 3.2): a grinding address is determined
by its `1`-byte node height and `8`-byte node index (its type byte is fixed and its payload is
zero), so there are `2^72` of them. -/
abbrev GrindTweak : Type := Fin 256 × Fin (2 ^ 64)

/-- The leaf identifier `(z, i)` of a grinding tweak. -/
def GrindTweak.leafId (T : GrindTweak) : LeafId := ⟨T.1, T.2⟩

theorem card_grindTweak : Fintype.card GrindTweak = 2 ^ 72 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  norm_num

/-- The inputs `(PK.seed, T, md)` of a counter search. -/
abbrev GrindInput (pr : Primitives P) : Type := pr.PkSeed × GrindTweak × pr.Digest

/-- The primitives `pr` with `H_grind` replaced, on the grinding tweak space, by the function
`H : (PK.seed, T, md) ↦ (ctr ↦ H_grind(PK.seed, T, md, ctr))`. `H_grind` absorbs only the first
`10` bytes of the grinding address (height, index, type), so the counter search of the WOTS+C
instance at `T` reads exactly `H (PK.seed, T, md)` (`encode_withGrind`). Sampling `H` uniformly
is the ideal model of Assumption 3.1 / Assumption 4.1: the values of `H_grind` at pairwise
distinct inputs are independent and uniform. -/
@[reducible] def withGrind (pr : Primitives P) (H : GrindInput pr → Fin (2 ^ P.c) → pr.Y) :
    Primitives P :=
  { pr with
    Hgrind := fun pk a md ctr =>
      if h : a.layer < 256 ∧ a.tree < 2 ^ 64 then H (pk, (⟨a.layer, h.1⟩, ⟨a.tree, h.2⟩), md) ctr
      else pr.Hgrind pk a md ctr }

theorem encode_withGrind (pr : Primitives P) (H : GrindInput pr → Fin (2 ^ P.c) → pr.Y)
    (pk : pr.PkSeed) (T : GrindTweak) (md : pr.Digest) (ctr : Fin (2 ^ P.c)) :
    WotsC.encode (withGrind pr H) pk T.leafId md ctr = H (pk, T, md) ctr := by
  simp [WotsC.encode, withGrind, SfAdrs.grindAdrs, SfAdrs.toAdrs, GrindTweak.leafId]

/-- Replacing `H_grind` does not change the target-sum predicate. -/
@[simp] theorem targetSum_withGrind (pr : Primitives P) (H : GrindInput pr → Fin (2 ^ P.c) → pr.Y)
    (y : pr.Y) : WotsC.TargetSum (withGrind pr H) y ↔ WotsC.TargetSum pr y := Iff.rfl

/-- The counter search of the WOTS+C instance at `T` fails exactly when no counter of
`H (PK.seed, T, md)` meets the target sum. -/
theorem grind_withGrind_eq_none_iff (pr : Primitives P) (H : GrindInput pr → Fin (2 ^ P.c) → pr.Y)
    (x : GrindInput pr) :
    WotsC.grind (withGrind pr H) x.1 x.2.1.leafId x.2.2 = none ↔
      ∀ ctr, ¬ WotsC.TargetSum pr (H x ctr) := by
  exact (WotsC.grind_eq_none_iff _).trans <| forall_congr' fun ctr => by
    rw [encode_withGrind, targetSum_withGrind]

/-- **Conjecture 3.1** (grind-completeness of `H_grind`): for every public seed, every grinding
tweak `T ∈ T_g`, and every digest `md`, some counter `ctr < 2^c` gives an encoded digest
`H_grind(PK.seed, T, md, ctr)` whose base-`w` digits sum to `Swn`. -/
def GrindComplete (pr : Primitives P) : Prop :=
  ∀ (pk : pr.PkSeed) (T : GrindTweak) (md : pr.Digest),
    ∃ ctr, WotsC.TargetSum pr (WotsC.encode pr pk T.leafId md ctr)

/-- Conjecture 3.1 says that the counter search of WOTS+C never returns `⊥`. -/
theorem grindComplete_iff (pr : Primitives P) :
    GrindComplete pr ↔ ∀ pk (T : GrindTweak) md, WotsC.grind pr pk T.leafId md ≠ none := by
  simp only [GrindComplete, ne_eq, WotsC.grind_eq_none_iff, not_forall, not_not]

theorem not_grindComplete_withGrind_iff (pr : Primitives P)
    (H : GrindInput pr → Fin (2 ^ P.c) → pr.Y) :
    ¬ GrindComplete (withGrind pr H) ↔ ∃ x, ∀ ctr, ¬ WotsC.TargetSum pr (H x ctr) := by
  simp only [GrindComplete, not_forall, not_exists]
  constructor
  · rintro ⟨pk, T, md, h⟩
    exact ⟨(pk, T, md), fun ctr => by have h' := h ctr; rw [encode_withGrind] at h'; exact h'⟩
  · rintro ⟨⟨pk, T, md⟩, h⟩
    exact ⟨pk, T, md, fun ctr => by rw [encode_withGrind]; exact h ctr⟩

theorem one_sub_pSum_nonneg : 0 ≤ 1 - pSum P := sub_nonneg.2 (pSumOf_le_one _ _ _)

section Probability

variable (hP : P.Valid) (pr : Primitives P) [Fintype pr.Y] [SampleableType pr.Y]
  (henc : NBitEncoding pr) [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest]
include hP henc

/-- **Lemma 3.1 (ii)**, one signing call: under Assumption 3.1, the counter search at any
`(PK.seed, T, md)` returns `⊥` with probability exactly `(1 − p_sum)^(2^c)`. -/
theorem prob_grind_fail (x : GrindInput pr) :
    Pr{let H ← $ᵗ (GrindInput pr → Fin (2 ^ P.c) → pr.Y)}[
      WotsC.grind (withGrind pr H) x.1 x.2.1.leafId x.2.2 = none] =
      ENNReal.ofReal ((1 - pSum P) ^ 2 ^ P.c) := by
  refine (prEvent_congr _ _ _ fun H => grind_withGrind_eq_none_iff pr H x).trans ?_
  rw [prob_search_fail, prob_not_targetSum hP pr henc,
    ENNReal.ofReal_pow one_sub_pSum_nonneg]

/-- **Lemma 3.1 (ii)**, execution: an execution with at most `L` stateful signing calls, at inputs
`calls l = (PK.seed, T_l, md_l)` (fixed by the messages, contexts and keys, which `H_grind` does
not influence), fails with probability at most `L · (1 − p_sum)^(2^c)`. -/
theorem prob_execution_fail_le (L : ℕ) (calls : Fin L → GrindInput pr) :
    Pr{let H ← $ᵗ (GrindInput pr → Fin (2 ^ P.c) → pr.Y)}[
      ∃ l, WotsC.grind (withGrind pr H) (calls l).1 (calls l).2.1.leafId (calls l).2.2 = none] ≤
      L * ENNReal.ofReal ((1 - pSum P) ^ 2 ^ P.c) := by
  refine (prEvent_congr _ _ (fun H => ∃ l, ∀ ctr, ¬ WotsC.TargetSum pr (H (calls l) ctr))
    fun H => exists_congr fun l => grind_withGrind_eq_none_iff pr H (calls l)).trans_le ?_
  refine (prob_some_search_fail_le (WotsC.TargetSum pr) _ L calls).trans_eq ?_
  rw [prob_not_targetSum hP pr henc, ENNReal.ofReal_pow one_sub_pSum_nonneg]

/-- **Lemma 3.2** (grind-completeness in the ideal model): Conjecture 3.1 fails for a uniformly
random `H_grind` with probability at most `|seeds| · 2^72 · |digests| · (1 − p_sum)^(2^c)`. -/
theorem prob_not_grindComplete_le :
    Pr{let H ← $ᵗ (GrindInput pr → Fin (2 ^ P.c) → pr.Y)}[¬ GrindComplete (withGrind pr H)] ≤
      ENNReal.ofReal (Fintype.card pr.PkSeed * 2 ^ 72 * Fintype.card pr.Digest *
        (1 - pSum P) ^ 2 ^ P.c) := by
  refine (prEvent_congr _ _ _ fun H => not_grindComplete_withGrind_iff pr H).trans_le ?_
  refine (prob_exists_search_fail_le (WotsC.TargetSum pr) _).trans_eq ?_
  rw [prob_not_targetSum hP pr henc, ← ENNReal.ofReal_pow one_sub_pSum_nonneg,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), Fintype.card_prod,
    Fintype.card_prod, card_grindTweak]
  push_cast
  ring_nf

end Probability

/-- `ε_gc = 2^n · 2^72 · 2^(2n) · (1 − p_sum)^(2^c)` (Lemma 3.2). -/
noncomputable def epsGc (P : Params) : ℝ :=
  2 ^ P.n * 2 ^ 72 * 2 ^ (2 * P.n) * (1 - pSum P) ^ 2 ^ P.c

/-- **Lemma 3.2** with `2^n` public seeds and `2^(2n)` digests: the failure probability of
Conjecture 3.1 in the ideal model is at most `ε_gc`. -/
theorem prob_not_grindComplete_le_epsGc (hP : P.Valid) (pr : Primitives P) [Fintype pr.Y]
    [SampleableType pr.Y] (henc : NBitEncoding pr) [Fintype pr.PkSeed] [DecidableEq pr.PkSeed]
    [Fintype pr.Digest] [DecidableEq pr.Digest] (hseed : Fintype.card pr.PkSeed = 2 ^ P.n)
    (hdig : Fintype.card pr.Digest = 2 ^ (2 * P.n)) :
    Pr{let H ← $ᵗ (GrindInput pr → Fin (2 ^ P.c) → pr.Y)}[¬ GrindComplete (withGrind pr H)] ≤
      ENNReal.ofReal (epsGc P) := by
  refine (prob_not_grindComplete_le hP pr henc).trans_eq ?_
  rw [hseed, hdig, epsGc]
  push_cast
  rfl

/-! ## The concrete bounds at the SHRINCS parameters -/

theorem pow_div_lt_one_div {A B c k : ℕ} (hB : 0 < B) (hc : 0 < c) (h : A ^ k * c < B ^ k) :
    ((A : ℝ) / B) ^ k < 1 / c := by
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast h

/-- **Lemma 3.1**: at the SHRINCS parameters a stateful signing call fails with probability
`(1 − p_sum)^(2^16) < 2^−1450`. -/
theorem shrincs_call_fail_lt : (1 - pSum shrincs) ^ 2 ^ shrincs.c < 1 / 2 ^ 1450 := by
  have h := pow_div_lt_one_div (A := 2 ^ 128 - shrincsN) (B := 2 ^ 128) (c := 2 ^ 1450)
    (k := 2 ^ 16) (by positivity) (by positivity) (by decide +kernel)
  rw [one_sub_pSum_shrincs, show shrincs.c = 16 from rfl]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- **Lemma 3.1**: at the SHRINCS parameters an execution with `L ≤ 2^64` stateful calls fails
with probability at most `L (1 − p_sum)^(2^16) < 2^−1386`. -/
theorem shrincs_execution_fail_lt {L : ℕ} (hL : L ≤ 2 ^ 64) :
    L * (1 - pSum shrincs) ^ 2 ^ shrincs.c < 1 / 2 ^ 1386 := by
  have h := shrincs_call_fail_lt
  have h0 : 0 ≤ (1 - pSum shrincs) ^ 2 ^ shrincs.c := pow_nonneg one_sub_pSum_nonneg _
  have hL' : (L : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hL
  calc (L : ℝ) * (1 - pSum shrincs) ^ 2 ^ shrincs.c
      ≤ 2 ^ 64 * (1 - pSum shrincs) ^ 2 ^ shrincs.c := mul_le_mul_of_nonneg_right hL' h0
    _ < 2 ^ 64 * (1 / 2 ^ 1450) := by gcongr
    _ = 1 / 2 ^ 1386 := by
      rw [show (2 : ℝ) ^ 1450 = 2 ^ 64 * 2 ^ 1386 by rw [← pow_add]]
      field_simp

/-- **Lemma 3.2**: at the SHRINCS parameters `ε_gc < 2^−994`. -/
theorem epsGc_shrincs_lt : epsGc shrincs < 1 / 2 ^ 994 := by
  have h := shrincs_call_fail_lt
  calc epsGc shrincs = 2 ^ 456 * (1 - pSum shrincs) ^ 2 ^ shrincs.c := by
        rw [epsGc, show shrincs.n = 128 from rfl, ← pow_add, ← pow_add]
    _ < 2 ^ 456 * (1 / 2 ^ 1450) := by gcongr
    _ = 1 / 2 ^ 994 := by
      rw [show (2 : ℝ) ^ 1450 = 2 ^ 456 * 2 ^ 994 by rw [← pow_add]]
      field_simp

/-- **Lemma 3.1 (ii)** at the SHRINCS parameters, as a probability statement. -/
theorem prob_execution_fail_shrincs (pr : Primitives shrincs) [Fintype pr.Y] [SampleableType pr.Y]
    (henc : NBitEncoding pr) [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [Fintype pr.Digest]
    [DecidableEq pr.Digest] {L : ℕ} (hL : L ≤ 2 ^ 64) (calls : Fin L → GrindInput pr) :
    Pr{let H ← $ᵗ (GrindInput pr → Fin (2 ^ shrincs.c) → pr.Y)}[
      ∃ l, WotsC.grind (withGrind pr H) (calls l).1 (calls l).2.1.leafId (calls l).2.2 = none] <
      ENNReal.ofReal (1 / 2 ^ 1386) := by
  refine (prob_execution_fail_le shrincs_valid pr henc L calls).trans_lt ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact shrincs_execution_fail_lt hL

/-- **Lemma 3.2** at the SHRINCS parameters, as a probability statement: Conjecture 3.1 fails for
a uniformly random `H_grind` with probability below `2^−994`. -/
theorem prob_not_grindComplete_shrincs (pr : Primitives shrincs) [Fintype pr.Y]
    [SampleableType pr.Y] (henc : NBitEncoding pr) [Fintype pr.PkSeed] [DecidableEq pr.PkSeed]
    [Fintype pr.Digest] [DecidableEq pr.Digest] (hseed : Fintype.card pr.PkSeed = 2 ^ shrincs.n)
    (hdig : Fintype.card pr.Digest = 2 ^ (2 * shrincs.n)) :
    Pr{let H ← $ᵗ (GrindInput pr → Fin (2 ^ shrincs.c) → pr.Y)}[¬ GrindComplete (withGrind pr H)] <
      ENNReal.ofReal (1 / 2 ^ 994) := by
  refine (prob_not_grindComplete_le_epsGc shrincs_valid pr henc hseed hdig).trans_lt ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact epsGc_shrincs_lt

end ShrincsSecurity.Scheme.Grinding
