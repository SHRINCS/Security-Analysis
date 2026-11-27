module

public import ShrincsSecurity.Scheme.Shrincs
public import HashSig.SLHDSA.GeneralSchemeQueryBound
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Lemma 5.1: verification query counts on the actual scheme algorithms

`SHRINCS-Security-Analysis.pdf`, **Lemma 5.1** (Section 5.2, lines 4532–4579): bounds on the number
of tweakable-hash evaluations performed by Algorithm 3 (`SHRINCS.Verify`) on both paths:

* **Stateful path** (`fxmssPkFromSigM`, proved equal to `Scheme.Fxmss.pkFromSig` under
  `simulateQ (sfVerifyImpl pr)`): at most
  - `1` call to `H_grind`,
  - `P.lsf * (P.w - 1) - P.Swn` calls to `F` (`240` at SHRINCS parameters),
  - `1` call to `Th_lsf`,
  - `P.hsf` calls to `H` (`255` at SHRINCS parameters),
  and hence at most `Vsf = P.lsf * (P.w - 1) - P.Swn + 2 + P.hsf` (`497`) tweakable-hash calls in
  total (`fxmssPkFromSigM_totalBound`).
* **Stateless path** (`SLHDSA.GeneralScheme.verifyInternalM`, whose deterministic simulation
  `simulateQ (PublicHash.impl pr.toSLHDSA)` is `Scheme.Stateless.verify` under `|ctx| ≤ 255`):
  - every WOTS-TW recovery performs at most `smax = max_{C ≤ l1(w−1)} (C + ∑_{j<l2} (w − 1 − C_j))`
    calls to `F` (`sum_complement_chainStepsCore_le_smax`, `510` at SHRINCS parameters),
  - at most `k(a + 1) + 1 + d(smax + h' + 1)` (`Vsl = 2741` at SHRINCS parameters) tweakable-hash
    (`thash`) calls in total (`verifyInternalM_thashBound`), and `1` call to `H_msg^sl`
    (`verifyInternalM_isTotalQueryBound_smax`, `1 + Vsl = 2742`).
-/

@[expose] public section

open OracleComp OracleSpec Finset

namespace ShrincsSecurity.Scheme.VerifyCount

/-! ## Helper -/

private theorem sum_fin_getD_eq_list_sum :
    ∀ (l : List ℕ) (n : ℕ), l.length = n → ∑ i : Fin n, l.getD i.val 0 = l.sum
  | [], 0, _ => by simp
  | a :: l, n + 1, h => by
    have hl : l.length = n := by simpa using h
    rw [Fin.sum_univ_succ, List.sum_cons, ← sum_fin_getD_eq_list_sum l n hl]
    rfl

/-! ## Stateful path: explicit-query `Fxmss.pkFromSigM` and exact Lemma 5.1 bounds -/

section Stateful

variable {P : Params} (pr : Primitives P)

/-- The four tweakable-hash calls issued by stateful verification (`FXMSS.pkFromSig`). -/
inductive SfVerifyQuery (pr : Primitives P) where
  | hgrind (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) (ctr : Fin (2 ^ P.c))
  | f (pk : pr.PkSeed) (a : SLHDSA.Adrs) (x : pr.Y)
  | thLsf (pk : pr.PkSeed) (a : SLHDSA.Adrs) (xs : Vector pr.Y P.lsf)
  | h (pk : pr.PkSeed) (a : SLHDSA.Adrs) (l r : pr.Y)

/-- The oracle specification for stateful verification's tweakable-hash queries. -/
@[reducible] def sfVerifySpec (pr : Primitives P) : OracleSpec (SfVerifyQuery pr) :=
  fun _ => pr.Y

/-- Deterministic interpretation of `sfVerifySpec` by the functions of `pr`. -/
def sfVerifyImpl (pr : Primitives P) : QueryImpl (sfVerifySpec pr) Id
  | .hgrind pk id md ctr => WotsC.encode pr pk id md ctr
  | .f pk a x => pr.F pk a x
  | .thLsf pk a xs => pr.ThLsf pk a xs
  | .h pk a l r => pr.H pk a l r

/-- Explicit-query WOTS+C chain. -/
def wotsChainM (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j : ℕ) :
    ℕ → OracleComp (sfVerifySpec pr) pr.Y
  | 0 => pure x
  | k + 1 => do
    let y ← wotsChainM pk id ch x j k
    (sfVerifySpec pr).query (.f pk (SfAdrs.chainAdrs id ch (j + k)).toAdrs y)

theorem simulateQ_wotsChainM (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j k : ℕ) :
    simulateQ (sfVerifyImpl pr) (wotsChainM pr pk id ch x j k) =
      WotsC.chain pr pk id ch x j k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [wotsChainM, simulateQ_bind, simulateQ_spec_query, ih, WotsC.chain_succ,
      sfVerifyImpl]
    rfl

/-- Explicit-query WOTS+C chain-top recovery. -/
def wotsTopsFromSigM (pk : pr.PkSeed) (id : LeafId) (d : pr.Y) (σ : WotsC.Sig pr) :
    OracleComp (sfVerifySpec pr) (Vector pr.Y P.lsf) :=
  Vector.ofFnM fun ch : Fin P.lsf =>
    wotsChainM pr pk id ch.val σ.chains[ch.val] (WotsC.digit pr d ch.val)
      (P.w - 1 - WotsC.digit pr d ch.val)

theorem simulateQ_ofFnM {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec Id) :
    ∀ {k : ℕ} (g : Fin k → OracleComp spec α),
      simulateQ impl (Vector.ofFnM g) = Vector.ofFn fun i => simulateQ impl (g i)
  | 0, _ => by
    rw [Vector.ofFnM_zero, simulateQ_pure]
    apply Vector.ext
    intro i hi
    omega
  | k + 1, g => by
    rw [Vector.ofFnM_succ, simulateQ_bind, simulateQ_ofFnM impl]
    change simulateQ impl ((g (Fin.last k)) >>= fun a =>
      pure ((Vector.ofFn fun j : Fin k => simulateQ impl (g j.castSucc)).push a)) = _
    rw [simulateQ_bind]
    simp only [simulateQ_pure]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    change ((Vector.ofFn fun j : Fin k => simulateQ impl (g j.castSucc)).push
      (simulateQ impl (g (Fin.last k))))[i] = simulateQ impl (g ⟨i, hi⟩)
    by_cases h : i < k
    · simp [Vector.getElem_push_lt h]
    · have hk : i = k := by omega
      subst hk
      simp [Vector.getElem_push_eq]
      rfl

theorem simulateQ_wotsTopsFromSigM (pk : pr.PkSeed) (id : LeafId) (d : pr.Y) (σ : WotsC.Sig pr) :
    simulateQ (sfVerifyImpl pr) (wotsTopsFromSigM pr pk id d σ) =
      WotsC.topsFromSig pr pk id d σ := by
  unfold wotsTopsFromSigM WotsC.topsFromSig
  rw [simulateQ_ofFnM]
  congr 1
  funext ch
  exact simulateQ_wotsChainM pr pk id ch.val _ _ _

/-- Explicit-query `WotsC.pkFromSig`. -/
def wotsPkFromSigM (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) (σ : WotsC.Sig pr) :
    OracleComp (sfVerifySpec pr) (Option pr.Y) := do
  let d ← (sfVerifySpec pr).query (.hgrind pk id md σ.ctr)
  if WotsC.TargetSum pr d then
    let tops ← wotsTopsFromSigM pr pk id d σ
    let y ← (sfVerifySpec pr).query (.thLsf pk (SfAdrs.pkAdrs id).toAdrs tops)
    return some y
  else
    return none

theorem simulateQ_wotsPkFromSigM (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest)
    (σ : WotsC.Sig pr) :
    simulateQ (sfVerifyImpl pr) (wotsPkFromSigM pr pk id md σ) =
      WotsC.pkFromSig pr pk id md σ := by
  unfold wotsPkFromSigM WotsC.pkFromSig
  rw [simulateQ_bind, simulateQ_spec_query]
  change simulateQ (sfVerifyImpl pr)
    (if WotsC.TargetSum pr (WotsC.encode pr pk id md σ.ctr) then
      wotsTopsFromSigM pr pk id (WotsC.encode pr pk id md σ.ctr) σ >>= fun tops =>
        (sfVerifySpec pr).query (.thLsf pk (SfAdrs.pkAdrs id).toAdrs tops) >>= fun y => pure (some y)
    else pure none) = _
  by_cases hts : WotsC.TargetSum pr (WotsC.encode pr pk id md σ.ctr)
  · simp only [hts, ↓reduceIte, simulateQ_bind, simulateQ_wotsTopsFromSigM, simulateQ_spec_query,
      simulateQ_pure]
    rfl
  · simp only [hts, ↓reduceIte, simulateQ_pure]
    rfl

/-- Explicit-query FXMSS authentication-path climb. -/
def treeClimbM (pk : pr.PkSeed) :
    ℕ → ℕ → pr.Y → List pr.Y → OracleComp (sfVerifySpec pr) pr.Y
  | _, _, acc, [] => pure acc
  | z, i, acc, s :: rest => do
    let parent ←
      if i % 2 = 0 then
        (sfVerifySpec pr).query (.h pk (SfAdrs.treeAdrs ⟨z + 1, i / 2⟩).toAdrs acc s)
      else
        (sfVerifySpec pr).query (.h pk (SfAdrs.treeAdrs ⟨z + 1, i / 2⟩).toAdrs s acc)
    treeClimbM pk (z + 1) (i / 2) parent rest

theorem simulateQ_treeClimbM (pk : pr.PkSeed) :
    ∀ (z i : ℕ) (acc : pr.Y) (auth : List pr.Y),
      simulateQ (sfVerifyImpl pr) (treeClimbM pr pk z i acc auth) =
        Tree.climb (Fxmss.node pr pk) z i acc auth
  | _, _, _, [] => rfl
  | z, i, acc, s :: rest => by
    simp only [treeClimbM, Tree.climb]
    split_ifs
    · rw [simulateQ_bind, simulateQ_spec_query]
      exact simulateQ_treeClimbM pk (z + 1) (i / 2) _ rest
    · rw [simulateQ_bind, simulateQ_spec_query]
      exact simulateQ_treeClimbM pk (z + 1) (i / 2) _ rest

/-- **Explicit-query `Fxmss.pkFromSig`** (Algorithm 3, stateful branch). -/
def fxmssPkFromSigM (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId) (σ : Fxmss.Sig pr) :
    OracleComp (sfVerifySpec pr) (Option pr.Y) :=
  if id.height < P.hsf ∧ σ.auth.length = P.hsf - id.height ∧
      id.index < 2 ^ min 64 (P.hsf - id.height) then do
    match ← wotsPkFromSigM pr pk id md σ.wots with
    | none => return none
    | some N =>
      let r ← treeClimbM pr pk id.height id.index N σ.auth
      return some r
  else
    return none

/-- The deterministic interpretation of `fxmssPkFromSigM` is `Fxmss.pkFromSig`. -/
theorem simulateQ_fxmssPkFromSigM (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId)
    (σ : Fxmss.Sig pr) :
    simulateQ (sfVerifyImpl pr) (fxmssPkFromSigM pr pk md id σ) =
      Fxmss.pkFromSig pr pk md id σ := by
  unfold fxmssPkFromSigM Fxmss.pkFromSig
  split_ifs
  · rw [simulateQ_bind, simulateQ_wotsPkFromSigM]
    change simulateQ (sfVerifyImpl pr)
      (match WotsC.pkFromSig pr pk id md σ.wots with
       | none => pure none
       | some N => treeClimbM pr pk id.height id.index N σ.auth >>= fun r => pure (some r)) = _
    cases WotsC.pkFromSig pr pk id md σ.wots with
    | none => rfl
    | some N =>
      rw [simulateQ_bind, simulateQ_treeClimbM]
      rfl
  · rfl

/-! ### Per-function predicates and query-bound helpers -/

def SfVerifyQuery.isHgrind : SfVerifyQuery pr → Prop
  | .hgrind _ _ _ _ => True | _ => False

def SfVerifyQuery.isF : SfVerifyQuery pr → Prop
  | .f _ _ _ => True | _ => False

def SfVerifyQuery.isThLsf : SfVerifyQuery pr → Prop
  | .thLsf _ _ _ => True | _ => False

def SfVerifyQuery.isH : SfVerifyQuery pr → Prop
  | .h _ _ _ _ => True | _ => False

instance : DecidablePred (SfVerifyQuery.isHgrind pr) := fun q => by
  cases q <;> dsimp [SfVerifyQuery.isHgrind] <;> infer_instance

instance : DecidablePred (SfVerifyQuery.isF pr) := fun q => by
  cases q <;> dsimp [SfVerifyQuery.isF] <;> infer_instance

instance : DecidablePred (SfVerifyQuery.isThLsf pr) := fun q => by
  cases q <;> dsimp [SfVerifyQuery.isThLsf] <;> infer_instance

instance : DecidablePred (SfVerifyQuery.isH pr) := fun q => by
  cases q <;> dsimp [SfVerifyQuery.isH] <;> infer_instance

private theorem isQueryBoundP_ofFnM {ι α : Type} {spec : OracleSpec ι} (qpred : ι → Prop)
    [DecidablePred qpred] :
    ∀ {k : ℕ} (g : Fin k → OracleComp spec α) (budget : Fin k → ℕ),
      (∀ i, (g i).IsQueryBoundP qpred (budget i)) →
      (Vector.ofFnM g).IsQueryBoundP qpred (∑ i, budget i)
  | 0, _, _, _ => by simp [Vector.ofFnM_zero]
  | k + 1, g, budget, h => by
    rw [Vector.ofFnM_succ, Fin.sum_univ_castSucc]
    refine isQueryBoundP_bind (isQueryBoundP_ofFnM qpred (fun i => g i.castSucc)
      (fun i => budget i.castSucc) (fun i => h i.castSucc)) fun xs _ => ?_
    exact isQueryBoundP_bind (ob := fun a => pure (xs.push a)) (h (Fin.last k))
      fun a _ => isQueryBoundP_pure qpred (xs.push a) 0

private theorem isQueryBoundP_wotsChainM {qpred : SfVerifyQuery pr → Prop} [DecidablePred qpred]
    (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j : ℕ) :
    ∀ (k : ℕ) (b : ℕ), (∀ a y, ¬ qpred (.f pk a y)) ∨ k ≤ b →
      (wotsChainM pr pk id ch x j k).IsQueryBoundP qpred b
  | 0, b, _ => by simp [wotsChainM]
  | k + 1, b, hb => by
    simp only [wotsChainM]
    rcases hb with hnot | hle
    · refine (isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_wotsChainM pk id ch x j k 0 (Or.inl hnot)) fun y _ => ?_).mono
        (Nat.zero_le b)
      exact (isQueryBoundP_query_iff qpred _ 0).2 fun h => absurd h (hnot _ y)
    · refine (isQueryBoundP_bind (n := k) (m := 1)
        (isQueryBoundP_wotsChainM pk id ch x j k k (Or.inr le_rfl)) fun y _ => ?_).mono
        (by omega)
      exact (isQueryBoundP_query_iff qpred _ 1).2 fun _ => Nat.zero_lt_one

private theorem sum_complement_wotsC_digits (d : pr.Y) (hd : WotsC.TargetSum pr d) :
    ∑ ch : Fin P.lsf, (P.w - 1 - WotsC.digit pr d ch.val) = P.lsf * (P.w - 1) - P.Swn := by
  have hlen : (WotsC.digits pr d).length = P.lsf := WotsC.digits_length pr d
  have hsum : ∑ ch : Fin P.lsf, WotsC.digit pr d ch.val = P.Swn := by
    have h1 : (WotsC.digits pr d).sum = P.Swn := hd
    rw [← h1]
    exact sum_fin_getD_eq_list_sum (WotsC.digits pr d) P.lsf hlen
  have hle : ∀ ch : Fin P.lsf, WotsC.digit pr d ch.val ≤ P.w - 1 := fun ch => by
    have := WotsC.digit_lt pr d ch.val
    omega
  have hadd :
      (∑ ch : Fin P.lsf, (P.w - 1 - WotsC.digit pr d ch.val)) +
        (∑ ch : Fin P.lsf, WotsC.digit pr d ch.val) = P.lsf * (P.w - 1) := by
    rw [← Finset.sum_add_distrib]
    calc ∑ ch : Fin P.lsf, ((P.w - 1 - WotsC.digit pr d ch.val) + WotsC.digit pr d ch.val)
        = ∑ _ch : Fin P.lsf, (P.w - 1) :=
          Finset.sum_congr rfl fun ch _ => Nat.sub_add_cancel (hle ch)
      _ = P.lsf * (P.w - 1) := by simp
  omega

private theorem isQueryBoundP_treeClimbM {qpred : SfVerifyQuery pr → Prop} [DecidablePred qpred]
    (pk : pr.PkSeed) :
    ∀ (z i : ℕ) (acc : pr.Y) (auth : List pr.Y) (b : ℕ),
      (∀ a l r, ¬ qpred (.h pk a l r)) ∨ auth.length ≤ b →
      (treeClimbM pr pk z i acc auth).IsQueryBoundP qpred b
  | _, _, _, [], _, _ => by simp [treeClimbM]
  | z, i, acc, s :: rest, b, hb => by
    simp only [treeClimbM, List.length_cons] at hb ⊢
    rcases hb with hnot | hle
    · split_ifs
      · refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ fun parent _ =>
          isQueryBoundP_treeClimbM pk (z + 1) (i / 2) parent rest 0 (Or.inl hnot)).mono
          (Nat.zero_le b)
        exact (isQueryBoundP_query_iff qpred _ 0).2 fun h => absurd h (hnot _ _ _)
      · refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ fun parent _ =>
          isQueryBoundP_treeClimbM pk (z + 1) (i / 2) parent rest 0 (Or.inl hnot)).mono
          (Nat.zero_le b)
        exact (isQueryBoundP_query_iff qpred _ 0).2 fun h => absurd h (hnot _ _ _)
    · split_ifs
      · refine (isQueryBoundP_bind (n := 1) (m := rest.length) ?_ fun parent _ =>
          isQueryBoundP_treeClimbM pk (z + 1) (i / 2) parent rest rest.length (Or.inr le_rfl)).mono
          (by omega)
        exact (isQueryBoundP_query_iff qpred _ 1).2 fun _ => Nat.zero_lt_one
      · refine (isQueryBoundP_bind (n := 1) (m := rest.length) ?_ fun parent _ =>
          isQueryBoundP_treeClimbM pk (z + 1) (i / 2) parent rest rest.length (Or.inr le_rfl)).mono
          (by omega)
        exact (isQueryBoundP_query_iff qpred _ 1).2 fun _ => Nat.zero_lt_one

private theorem fxmssPkFromSigM_bound_generic {qpred : SfVerifyQuery pr → Prop}
    [DecidablePred qpred] (nG nF nT nH : ℕ)
    (hG : (∀ pk id md ctr, ¬ qpred (.hgrind pk id md ctr)) ∨ 1 ≤ nG)
    (hF : (∀ pk a y, ¬ qpred (.f pk a y)) ∨ P.lsf * (P.w - 1) - P.Swn ≤ nF)
    (hT : (∀ pk a xs, ¬ qpred (.thLsf pk a xs)) ∨ 1 ≤ nT)
    (hH : (∀ pk a l r, ¬ qpred (.h pk a l r)) ∨ P.hsf ≤ nH)
    (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId) (σ : Fxmss.Sig pr) :
    (fxmssPkFromSigM pr pk md id σ).IsQueryBoundP qpred (nG + nF + nT + nH) := by
  unfold fxmssPkFromSigM
  split_ifs with hval
  · refine (isQueryBoundP_bind (n := nG + nF + nT) (m := nH) ?_ fun opt _ => ?_).mono (by omega)
    · unfold wotsPkFromSigM
      refine (isQueryBoundP_bind (n := nG) (m := nF + nT) ?_ fun d _ => ?_).mono (by omega)
      · rcases hG with h0 | h1
        · exact (isQueryBoundP_query_iff qpred _ nG).2 fun h => absurd h (h0 _ _ _ _)
        · exact (isQueryBoundP_query_iff qpred _ nG).2 fun _ => by omega
      · split_ifs with hts
        · refine (isQueryBoundP_bind (n := nF) (m := nT) ?_ fun tops _ => ?_).mono (by omega)
          · unfold wotsTopsFromSigM
            rcases hF with h0 | h1
            · refine (isQueryBoundP_ofFnM (qpred := qpred) _ (fun _ => 0) fun ch =>
                isQueryBoundP_wotsChainM pr pk id ch.val _ _ _ 0 (Or.inl (h0 pk))).mono ?_
              simp
            · refine (isQueryBoundP_ofFnM (qpred := qpred) _
                (fun ch : Fin P.lsf => P.w - 1 - WotsC.digit pr d ch.val) fun ch =>
                isQueryBoundP_wotsChainM pr pk id ch.val _ _ _ _ (Or.inr le_rfl)).mono ?_
              rw [sum_complement_wotsC_digits pr d hts]
              exact h1
          · refine (isQueryBoundP_bind (n := nT) (m := 0) ?_ fun _ _ =>
              isQueryBoundP_pure _ _ 0).mono (by omega)
            rcases hT with h0 | h1
            · exact (isQueryBoundP_query_iff qpred _ nT).2 fun h => absurd h (h0 _ _ _)
            · exact (isQueryBoundP_query_iff qpred _ nT).2 fun _ => by omega
        · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
    · cases opt with
      | none => exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
      | some N =>
        refine (isQueryBoundP_bind (n := nH) (m := 0) ?_ fun _ _ =>
          isQueryBoundP_pure _ _ 0).mono (by omega)
        refine isQueryBoundP_treeClimbM pr pk id.height id.index N σ.auth nH ?_
        rcases hH with h0 | h1
        · exact Or.inl (h0 pk)
        · exact Or.inr (by omega)
  · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)

/-- **Lemma 5.1 (stateful, `H_grind`)**: at most `1` call to `H_grind`. -/
theorem fxmssPkFromSigM_hgrindBound (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId)
    (σ : Fxmss.Sig pr) :
    (fxmssPkFromSigM pr pk md id σ).IsQueryBoundP (SfVerifyQuery.isHgrind pr) 1 := by
  simpa using fxmssPkFromSigM_bound_generic (qpred := SfVerifyQuery.isHgrind pr) pr 1 0 0 0
    (Or.inr le_rfl) (Or.inl fun _ _ _ h => h) (Or.inl fun _ _ _ h => h)
    (Or.inl fun _ _ _ _ h => h) pk md id σ

/-- **Lemma 5.1 (stateful, `F`)**: at most `V^F = lsf(w − 1) − Swn` calls to `F` (`240` at SHRINCS). -/
theorem fxmssPkFromSigM_fBound (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId)
    (σ : Fxmss.Sig pr) :
    (fxmssPkFromSigM pr pk md id σ).IsQueryBoundP (SfVerifyQuery.isF pr)
      (P.lsf * (P.w - 1) - P.Swn) := by
  simpa using fxmssPkFromSigM_bound_generic (qpred := SfVerifyQuery.isF pr) pr 0
    (P.lsf * (P.w - 1) - P.Swn) 0 0
    (Or.inl fun _ _ _ _ h => h) (Or.inr le_rfl) (Or.inl fun _ _ _ h => h)
    (Or.inl fun _ _ _ _ h => h) pk md id σ

/-- **Lemma 5.1 (stateful, `Th_lsf`)**: at most `1` call to `Th_lsf`. -/
theorem fxmssPkFromSigM_thLsfBound (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId)
    (σ : Fxmss.Sig pr) :
    (fxmssPkFromSigM pr pk md id σ).IsQueryBoundP (SfVerifyQuery.isThLsf pr) 1 := by
  simpa using fxmssPkFromSigM_bound_generic (qpred := SfVerifyQuery.isThLsf pr) pr 0 0 1 0
    (Or.inl fun _ _ _ _ h => h) (Or.inl fun _ _ _ h => h) (Or.inr le_rfl)
    (Or.inl fun _ _ _ _ h => h) pk md id σ

/-- **Lemma 5.1 (stateful, `H`)**: at most `V^H = hsf` calls to `H` (`255` at SHRINCS). -/
theorem fxmssPkFromSigM_hBound (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId)
    (σ : Fxmss.Sig pr) :
    (fxmssPkFromSigM pr pk md id σ).IsQueryBoundP (SfVerifyQuery.isH pr) P.hsf := by
  simpa using fxmssPkFromSigM_bound_generic (qpred := SfVerifyQuery.isH pr) pr 0 0 0 P.hsf
    (Or.inl fun _ _ _ _ h => h) (Or.inl fun _ _ _ h => h) (Or.inl fun _ _ _ h => h)
    (Or.inr le_rfl) pk md id σ

/-- **Lemma 5.1 (stateful, total)**: `FXMSS.pkFromSig` makes at most
`Vsf = lsf(w − 1) − Swn + 2 + hsf` tweakable-hash calls (`497` at SHRINCS). -/
theorem fxmssPkFromSigM_totalBound (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId)
    (σ : Fxmss.Sig pr) :
    (fxmssPkFromSigM pr pk md id σ).IsTotalQueryBound
      (P.lsf * (P.w - 1) - P.Swn + 2 + P.hsf) := by
  have h := fxmssPkFromSigM_bound_generic (qpred := fun _ => True) pr 1
    (P.lsf * (P.w - 1) - P.Swn) 1 P.hsf
    (Or.inr le_rfl) (Or.inr le_rfl) (Or.inr le_rfl) (Or.inr le_rfl) pk md id σ
  exact (isQueryBoundP_true_iff _ _).1 (h.mono (by omega))

end Stateful

/-! ## Stateless path: `smax` bound on WOTS-TW and exact Lemma 5.1 bounds on `verifyInternalM` -/

section Stateless

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- The WOTS-TW verification chain work for checksum value `C`. -/
def wotsChainWork (P : Params) (C : ℕ) : ℕ :=
  C + ∑ j ∈ range P.l2, (P.w - 1 - C / P.w ^ j % P.w)

/-- `smax` (Lemma 5.1): maximum WOTS-TW verification chain work over `C ≤ l1 (w − 1)`. -/
def wotsSmax (P : Params) : ℕ :=
  (range (P.l1 * (P.w - 1) + 1)).sup (wotsChainWork P)

theorem l2_eq_slParams_len2 : vp.params.l2 = vp.sl.params.len2 := by
  have h1 : vp.params.l1 = vp.sl.params.len1 := vp.params.lsf_eq_len1 vp.valid
  show Nat.log vp.params.w (vp.params.l1 * (vp.params.w - 1)) + 1 =
    Nat.log vp.sl.params.w (vp.sl.params.len1 * (vp.sl.params.w - 1)) + 1
  rw [h1]
  rfl

/-- **WOTS-TW chain work bound (Lemma 5.1)**: for every `n`-bit message `msg`, the complementary
chain steps of FIPS 205 WOTS+ recovery sum to `wotsChainWork C ≤ wotsSmax` (`≤ 510` at SHRINCS). -/
theorem sum_complement_chainStepsCore_le_smax (msg : pr.Y) :
    ∑ i : Fin vp.sl.params.len,
      (vp.sl.params.w - 1 - SLHDSA.chainStepsCore pr.toSLHDSA.core msg i.val) ≤
      wotsSmax vp.params := by
  set p := vp.sl.params
  set d := SLHDSA.wotsMsgDigitsCore pr.toSLHDSA.core msg
  set C := SLHDSA.WotsChecksum.wotsChecksumValue p.w d
  have hdlen : d.length = p.len1 := SLHDSA.wotsMsgDigitsCore_length pr.toSLHDSA.core msg
  have hdlt : ∀ x ∈ d, x < p.w := SLHDSA.wotsMsgDigitsCore_mem_lt pr.toSLHDSA.core msg
  have hfull : SLHDSA.chainLengthsCore pr.toSLHDSA.core msg =
      d ++ VCVio.Algorithms.RadixEncoding.digitsOfBaseW C p.w p.len2 := by
    change SLHDSA.WotsEncoding.fullDigits p d = _
    exact SLHDSA.WotsEncoding.fullDigits_eq_wotsFullDigits vp.sl.valid d hdlen hdlt
  have hC_le : C ≤ vp.params.l1 * (vp.params.w - 1) := by
    have := SLHDSA.WotsChecksum.wotsChecksumValue_le hdlen hdlt
    have h1 : vp.params.l1 = p.len1 := vp.params.lsf_eq_len1 vp.valid
    rwa [← h1] at this
  have hsplit :
      ∑ i : Fin p.len, (p.w - 1 - SLHDSA.chainStepsCore pr.toSLHDSA.core msg i.val) =
      (∑ i : Fin p.len1, (p.w - 1 - d.getD i.val 0)) +
      (∑ j : Fin p.len2, (p.w - 1 -
        (VCVio.Algorithms.RadixEncoding.digitsOfBaseW C p.w p.len2).getD j.val 0)) := by
    change ∑ i : Fin (p.len1 + p.len2), _ = _
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hi : i.val < d.length := by omega
      simp [SLHDSA.chainStepsCore, hfull, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hi]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hj : d.length ≤ p.len1 + j.val := by omega
      simp [SLHDSA.chainStepsCore, hfull, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hj, hdlen]
  have hmsg_sum : ∑ i : Fin p.len1, (p.w - 1 - d.getD i.val 0) = C := by
    have hval := VCVio.Algorithms.ComplementaryChecksum.value_add_sum_eq p.w d hdlt
    have hsum_d : ∑ i : Fin p.len1, d.getD i.val 0 = d.sum :=
      sum_fin_getD_eq_list_sum d p.len1 hdlen
    have hle_d : ∀ i : Fin p.len1, d.getD i.val 0 ≤ p.w - 1 := fun i => by
      have hi : i.val < d.length := by omega
      have := hdlt _ (List.getElem_mem hi)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      omega
    have hadd : (∑ i : Fin p.len1, (p.w - 1 - d.getD i.val 0)) +
        (∑ i : Fin p.len1, d.getD i.val 0) = p.len1 * (p.w - 1) := by
      rw [← Finset.sum_add_distrib]
      calc ∑ i : Fin p.len1, ((p.w - 1 - d.getD i.val 0) + d.getD i.val 0)
          = ∑ _i : Fin p.len1, (p.w - 1) :=
            Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle_d i)
        _ = p.len1 * (p.w - 1) := by simp
    have hval' : C + d.sum = p.len1 * (p.w - 1) := by
      simpa [C, SLHDSA.WotsChecksum.wotsChecksumValue, hdlen] using hval
    omega
  have hchk_sum :
      ∑ j : Fin p.len2, (p.w - 1 -
        (VCVio.Algorithms.RadixEncoding.digitsOfBaseW C p.w p.len2).getD j.val 0) =
      ∑ j ∈ range vp.params.l2, (vp.params.w - 1 - C / vp.params.w ^ j % vp.params.w) := by
    have hl2 : p.len2 = vp.params.l2 := (l2_eq_slParams_len2 (vp := vp)).symm
    rw [Fin.sum_univ_eq_sum_range (fun j => p.w - 1 -
      (VCVio.Algorithms.RadixEncoding.digitsOfBaseW C p.w p.len2).getD j 0) p.len2]
    have hdig : ∀ j ∈ range p.len2,
        (VCVio.Algorithms.RadixEncoding.digitsOfBaseW C p.w p.len2).getD j 0 =
          C / p.w ^ (p.len2 - 1 - j) % p.w := fun j hj => by
      have hlt : j < p.len2 := Finset.mem_range.1 hj
      rw [VCVio.Algorithms.RadixEncoding.digitsOfBaseW_eq_range]
      simp [List.getD_eq_getElem?_getD, hlt]
    rw [Finset.sum_congr rfl fun j hj => by rw [hdig j hj]]
    rw [hl2]
    refine Finset.sum_nbij (fun j => vp.params.l2 - 1 - j)
      (fun j hj => Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega))
      (fun j₁ hj₁ j₂ hj₂ h => by
        dsimp only at h
        have := Finset.mem_range.1 hj₁; have := Finset.mem_range.1 hj₂; omega)
      (fun k hk => ⟨vp.params.l2 - 1 - k,
        Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega),
        by dsimp only; have := Finset.mem_range.1 hk; omega⟩)
      (fun j hj => rfl)
  rw [hsplit, hmsg_sum, hchk_sum]
  exact Finset.le_sup (f := wotsChainWork vp.params) (Finset.mem_range.2 (by omega))

/-- Tight `smax`-based XMSS recovery query bound (Lemma 5.1). -/
theorem xmssPkFromSigM_isTotalQueryBound_smax (idx : ℕ)
    (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) (msg : pr.Y) (pk : pr.PkSeed)
    (adrs : SLHDSA.Adrs) :
    IsTotalQueryBound
      (SLHDSA.xmssPkFromSigM pr.toSLHDSA.core idx sig msg pk adrs :
        OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) pr.Y)
      (wotsSmax vp.params + vp.params.hp + 1) := by
  refine (SLHDSA.xmssPkFromSigM_isTotalQueryBound pr.toSLHDSA.core idx sig msg pk adrs).mono ?_
  have h := sum_complement_chainStepsCore_le_smax pr msg
  change (∑ i : Fin vp.sl.params.len,
      (vp.sl.params.w - 1 - SLHDSA.chainStepsCore pr.toSLHDSA.core msg i.val)) + 1 +
      vp.params.hp ≤ wotsSmax vp.params + vp.params.hp + 1
  omega

/-- Tight `smax`-based hypertree recovery query bound (Lemma 5.1). -/
theorem recoverFromPositionM_isTotalQueryBound_smax (pk : pr.PkSeed)
    (pos : SLHDSA.LayerPosition vp.sl) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.sl.params.d) (msg : pr.Y)
    (sigs : Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers) :
    IsTotalQueryBound
      (SLHDSA.GeneralHypertree.recoverFromPositionM vp.sl pr.toSLHDSA.core pk pos layers
        hremaining msg sigs :
        OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) pr.Y)
      (layers * (wotsSmax vp.params + vp.params.hp + 1)) := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => trivial
  | one =>
    simpa [SLHDSA.GeneralHypertree.recoverFromPositionM,
      SLHDSA.GeneralHypertree.recoverFromPositionWith, SLHDSA.xmssPkFromSigM] using
      xmssPkFromSigM_isTotalQueryBound_smax pr pos.leaf.val sigs.head msg pk pos.toAdrs
  | more layers _ ih =>
    let next := pos.next (by omega)
    have hnext : next.layer.val + (layers + 1) = vp.sl.params.d := by
      dsimp only [next, SLHDSA.LayerPosition.next, ValidatedParams.sl] at hremaining ⊢
      omega
    have hbound := isTotalQueryBound_bind
      (xmssPkFromSigM_isTotalQueryBound_smax pr pos.leaf.val sigs.head msg pk pos.toAdrs)
      fun root => ih (pos := next) (hremaining := hnext)
        (msg := root) (sigs := sigs.tail)
    simpa [SLHDSA.GeneralHypertree.recoverFromPositionM,
      SLHDSA.GeneralHypertree.recoverFromPositionWith, SLHDSA.xmssPkFromSigM, next,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using hbound

/-- Predicate selecting tweakable-hash (`thash`) queries in `SLHDSA.publicHashSpec`. -/
def isSlThash {PkSeed AdrsKey Y : Type} : SLHDSA.PublicHashQuery PkSeed AdrsKey Y → Prop
  | .thash _ _ _ => True
  | .hmsg _ _ _ _ => False

/-- Predicate selecting `H_msg` queries in `SLHDSA.publicHashSpec`. -/
def isSlHmsg {PkSeed AdrsKey Y : Type} : SLHDSA.PublicHashQuery PkSeed AdrsKey Y → Prop
  | .thash _ _ _ => False
  | .hmsg _ _ _ _ => True

instance {PkSeed AdrsKey Y : Type} : DecidablePred (isSlThash (PkSeed := PkSeed) (AdrsKey := AdrsKey) (Y := Y)) :=
  fun q => by cases q <;> dsimp [isSlThash] <;> infer_instance

instance {PkSeed AdrsKey Y : Type} : DecidablePred (isSlHmsg (PkSeed := PkSeed) (AdrsKey := AdrsKey) (Y := Y)) :=
  fun q => by cases q <;> dsimp [isSlHmsg] <;> infer_instance

private theorem isQueryBoundP_of_isTotalQueryBound {ι α : Type} {spec : OracleSpec ι}
    {qpred : ι → Prop} [DecidablePred qpred] {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : oa.IsQueryBoundP qpred n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => exact trivial
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr h.1, fun u => ?_⟩
    by_cases ht : qpred t
    · simp only [ht, ↓reduceIte]
      exact ih u (h.2 u)
    · simp only [ht, ↓reduceIte]
      exact (ih u (h.2 u)).mono (Nat.sub_le n 1)

/-- **Lemma 5.1 (stateless, tweakable-hash count)**: `SLHDSA.GeneralScheme.verifyInternalM` makes
at most `Vsl = k(a + 1) + 1 + d(smax + h' + 1)` tweakable-hash (`thash`) queries (`2741` at
SHRINCS parameters). -/
theorem verifyInternalM_thashBound [DecidableEq pr.Y] (msg : List SLHDSA.Byte)
    (sig : Stateless.Sig pr) (pk : SLHDSA.PublicKeyCore pr.toSLHDSA.core) :
    (SLHDSA.GeneralScheme.verifyInternalM vp.sl pr.toSLHDSA.core msg sig pk :
      OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) Bool).IsQueryBoundP isSlThash
      (vp.params.k * (vp.params.a + 1) + 1 +
        vp.params.d * (wotsSmax vp.params + vp.params.hp + 1)) := by
  unfold SLHDSA.GeneralScheme.verifyInternalM SLHDSA.GeneralHypertree.verifyM
    SLHDSA.GeneralHypertree.pkFromSigM
  have hhmsg : (SLHDSA.PublicHash.hmsg pr.toSLHDSA.core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) _).IsQueryBoundP isSlThash 0 :=
    (isQueryBoundP_query_iff isSlThash _ 0).2 fun h => False.elim h
  refine (isQueryBoundP_bind (n := 0) (m := vp.params.k * (vp.params.a + 1) + 1 +
      vp.params.d * (wotsSmax vp.params + vp.params.hp + 1)) hhmsg fun digest _ => ?_).mono
      (by omega)
  let parts := SLHDSA.splitDigest vp.sl.params digest
  have hfors : (SLHDSA.forsPkFromSigM pr.toSLHDSA.core sig.fors parts.md.toList pk.pkSeed
      parts.forsAdrs : OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) pr.Y).IsQueryBoundP
      isSlThash (vp.params.k * (vp.params.a + 1) + 1) :=
    isQueryBoundP_of_isTotalQueryBound
      (SLHDSA.forsPkFromSigM_isTotalQueryBound pr.toSLHDSA.core sig.fors parts.md.toList pk.pkSeed
        parts.forsAdrs)
  refine isQueryBoundP_bind hfors fun forsPk _ => ?_
  have hht : (SLHDSA.GeneralHypertree.recoverFromPositionM vp.sl pr.toSLHDSA.core pk.pkSeed
      (SLHDSA.LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
      forsPk sig.hypertree : OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) pr.Y).IsQueryBoundP
      isSlThash (vp.params.d * (wotsSmax vp.params + vp.params.hp + 1)) :=
    isQueryBoundP_of_isTotalQueryBound
      (recoverFromPositionM_isTotalQueryBound_smax pr pk.pkSeed
        (SLHDSA.LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
        forsPk sig.hypertree)
  refine (isQueryBoundP_bind (m := 0) hht fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

/-- **Lemma 5.1 (stateless, total public-hash count)**: `verifyInternalM` makes at most
`1 + Vsl` public-hash queries (`1` call to `H_msg^sl` plus `Vsl = 2741` tweakable-hash calls). -/
theorem verifyInternalM_isTotalQueryBound_smax [DecidableEq pr.Y] (msg : List SLHDSA.Byte)
    (sig : Stateless.Sig pr) (pk : SLHDSA.PublicKeyCore pr.toSLHDSA.core) :
    IsTotalQueryBound
      (SLHDSA.GeneralScheme.verifyInternalM vp.sl pr.toSLHDSA.core msg sig pk :
        OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) Bool)
      (1 + (vp.params.k * (vp.params.a + 1) + 1 +
        vp.params.d * (wotsSmax vp.params + vp.params.hp + 1))) := by
  unfold SLHDSA.GeneralScheme.verifyInternalM SLHDSA.GeneralHypertree.verifyM
    SLHDSA.GeneralHypertree.pkFromSigM
  have h := isTotalQueryBound_bind
    (SLHDSA.PublicHash.hmsg_isTotalQueryBound pr.toSLHDSA.core sig.randomness pk.pkSeed pk.pkRoot
      msg) fun digest =>
    let parts := SLHDSA.splitDigest vp.sl.params digest
    isTotalQueryBound_bind
      (SLHDSA.forsPkFromSigM_isTotalQueryBound pr.toSLHDSA.core sig.fors parts.md.toList pk.pkSeed
        parts.forsAdrs) fun forsPk =>
      isTotalQueryBound_bind (n₂ := 0)
        (recoverFromPositionM_isTotalQueryBound_smax pr pk.pkSeed
          (SLHDSA.LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
          forsPk sig.hypertree) fun recovered =>
        show IsTotalQueryBound
          (pure (decide (recovered = pk.pkRoot)) :
            OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) Bool) 0 from trivial
  exact h.mono (by dsimp only [ValidatedParams.sl, Params.slParams]; omega)

/-- Connection to `Scheme.Shrincs.verify` (stateless branch): under `|ctx| ≤ 255`,
`Scheme.Shrincs.verify` is the deterministic simulation of `verifyInternalM` on the pure-mode
encoded message `0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ PK.sf ‖ M`. -/
theorem shrincs_verify_stateless_eq_simulateQ [DecidableEq pr.Y]
    (M ctx : List SLHDSA.Byte) (hctx : ctx.length ≤ 255) (σ' : Stateless.Sig pr)
    (pk : Shrincs.PublicKey pr) :
    Shrincs.verify pr M ctx (.stateless σ') pk =
      simulateQ (SLHDSA.PublicHash.impl pr.toSLHDSA)
        (SLHDSA.GeneralScheme.verifyInternalM vp.sl pr.toSLHDSA.core
          ([0, UInt8.ofNat ctx.length] ++ ctx ++ Shrincs.statelessMessage pr pk.pkSf M) σ'
          (Stateless.publicKey pr pk.pkSeed pk.pkSl) :
          OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) Bool) := by
  simp only [Shrincs.verify, Stateless.verify, SLHDSA.External.verifyPure,
    SLHDSA.External.encodePureMessage_eq_ok ctx _ hctx]
  rfl

end Stateless

end ShrincsSecurity.Scheme.VerifyCount

end
