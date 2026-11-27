module

public import ShrincsSecurity.Complexity.Defs
public import ShrincsSecurity.Scheme.VerifyCount
public import ShrincsSecurity.Fxmss.Theorem42
public import ShrincsSecurity.Shrincs.Claim415

/-!
# Single-Pass FXMSS Verification Trace Extractor and Stage-1 Full Precomputation Tables

Core building blocks for Stage-2 `Th_λ`-evaluation complexity bounds (`ξ̃_sf ≤ ξ + V_sf`,
`V_sf = 497`) on all seven stateful collection reductions of Theorem 4.2 (`B2Pre … B8Pre`)
and Theorem 4.1 (`B2SPre … B8SPre`):

1. **Single-pass explicit-`thSpec`-oracle FXMSS verifier + trace extractor (`fxmssExtractTableM`)**:
   computes `d*`, every forged WOTS+C chain value `chainVal ch p` (`a*_ch ≤ p < w`), the forged
   uncompressed key `fTops`, compressed leaf `fN0`, climb node values `fVal k`, climb pairs
   `fPair k`, and final root `finalRoot` in a single pass of at most
   `VerifyCount.Vsf P = P.lsf * (P.w - 1) - P.Swn + 2 + P.hsf` (`497`) `Th_λ` queries
   (`fxmssExtractTableM_queryBound`).
2. **Precomputed stateful table (`SfFullTable`) and zero-`Th_λ` Stage-2 runner (`stageHybPre`)**:
   replaces recomputation of `hon` in Stage 2 with table lookups from Stage 1, giving a single
   `Stage2ThBound ... (ξ + VerifyCount.Vsf P)` theorem (`stage2RunWithTrace_stage2Bound`) shared
   by all 14 stateful reductions (Theorem 4.2 and Theorem 4.1).
3. **Zero-extra-`Th_λ` trace extractors (`extract2Trace … extract8Trace`)**: extract every
   reduction's witness or distinguisher bit purely from `(FxmssTrace, SfFullTable, savedQ)` with
   zero additional `Th_λ` evaluations.
4. **Generic Stage-1 full-table builders (`buildSfTable0M`, `buildSfTableHybM`)**: build
   `SfFullTable` in Stage 1 through the game's collection and challenge oracles with full
   tweak-disjointness guarantees.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Complexity

open Scheme Slhdsa Fxmss Fxmss.Rom Notions
open ShrincsSecurity.Scheme.Structure (leafIds pkTweaks treeTweaks)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)
open SLHDSA (Adrs)

/-! ## 1. Single-pass explicit-`thSpec` FXMSS verifier and trace extractor -/

section TraceExtract

variable {P : Params} (pr : Primitives P) [Inhabited pr.Y]

/-- Structural and target-sum validity of a stateful FXMSS forgery `(id, md, w)`. -/
def fxmssValid (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) (w : Scheme.Fxmss.Sig pr) : Prop :=
  id.height < P.hsf ∧ w.auth.length = P.hsf - id.height ∧
    id.index < 2 ^ min 64 (P.hsf - id.height) ∧
    WotsC.TargetSum pr (WotsC.encode pr pk id md w.wots.ctr)

/-- Complete verification trace recorded during one pass of stateful verification. -/
structure FxmssTrace where
  /-- Forged encoded digest `d* = H_grind(pk, ADRS^g, y*, c*)`. -/
  dStar : pr.Y
  /-- Forged chain values `chainVal ch p` for `a*_ch ≤ p < w`. -/
  chainVal : Fin P.lsf → ℕ → pr.Y
  /-- Forged uncompressed WOTS+C public key `topsFromSig`. -/
  fTops : Vector pr.Y P.lsf
  /-- Forged compressed leaf value `N₀ = Th_lsf(pk, ADRS^pk, fTops)`. -/
  fN0 : pr.Y
  /-- Recomputed climb values `N_k` for `0 ≤ k ≤ |auth|`. -/
  fVal : ℕ → pr.Y
  /-- Sibling pairs `(left, right)` hashed at step `k < |auth|`. -/
  fPair : ℕ → pr.Y × pr.Y
  /-- Final recovered root `N_{|auth|}`. -/
  finalRoot : pr.Y

/-- **Lemma 5.1 stateful verification `Th_λ` query budget**:
`Vsf P = lsf(w − 1) − Swn + 2 + hsf` (`497` at SHRINCS parameters). -/
def Vsf (P : Params) : ℕ :=
  P.lsf * (P.w - 1) - P.Swn + 2 + P.hsf

/-- Walk `k` steps of WOTS+C chain `ch` from position `start`, querying `thSpec pr` once per step
and recording every reached position `start … start + k`. -/
def sfChainTraceM (id : LeafId) (ch : ℕ) (start : ℕ) (x : pr.Y) :
    ℕ → OracleComp (thSpec pr) (pr.Y × (ℕ → pr.Y))
  | 0 => pure (x, fun _ => x)
  | k + 1 => do
    let (y, tbl) ← sfChainTraceM id ch start x k
    let y' ← (thSpec pr).query ⟨.F, (SfAdrs.chainAdrs id ch (start + k)).toAdrs, y⟩
    return (y', fun p => if p = start + k + 1 then y' else tbl p)

omit [Inhabited pr.Y] in
private theorem sfChainTraceM_queryBound (id : LeafId) (ch start : ℕ) (x : pr.Y) :
    ∀ k, IsTotalQueryBound (sfChainTraceM pr id ch start x k) k
  | 0 => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | k + 1 => by
    unfold sfChainTraceM
    refine (isTotalQueryBound_bind (n₁ := k) (n₂ := 1)
      (sfChainTraceM_queryBound id ch start x k) fun p => ?_).mono (by omega)
    refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) ?_ fun _ =>
      (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
      (by omega)
    exact (isQueryBoundP_true_iff _ _).1
      ((isQueryBoundP_query_iff (fun _ => True) _ 1).2 fun _ => Nat.zero_lt_one)

omit [Inhabited pr.Y] in
private theorem simulateQ_sfChainTraceM (pk : pr.PkSeed) (id : LeafId) (ch start : ℕ) (x : pr.Y) :
    ∀ k,
      let res := Id.run (simulateQ (thRealImpl pr pk) (sfChainTraceM pr id ch start x k))
      res.1 = WotsC.chain pr pk id ch x start k ∧
        ∀ p, start ≤ p → p ≤ start + k → res.2 p = WotsC.chain pr pk id ch x start (p - start)
  | 0 => by
    refine ⟨rfl, fun p h1 h2 => ?_⟩
    have hp : p - start = 0 := by omega
    simp [sfChainTraceM, hp, WotsC.chain]
  | k + 1 => by
    have ih := simulateQ_sfChainTraceM pk id ch start x k
    set prev := Id.run (simulateQ (thRealImpl pr pk) (sfChainTraceM pr id ch start x k))
    have hrun : Id.run (simulateQ (thRealImpl pr pk) (sfChainTraceM pr id ch start x (k + 1))) =
        (pr.F pk (SfAdrs.chainAdrs id ch (start + k)).toAdrs prev.1,
         fun p => if p = start + k + 1 then
           pr.F pk (SfAdrs.chainAdrs id ch (start + k)).toAdrs prev.1
         else prev.2 p) := by
      simp only [sfChainTraceM, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        Id.run_bind, Id.run_pure]
      rfl
    rw [hrun]
    refine ⟨by simp [ih.1, WotsC.chain_succ], fun p h1 h2 => ?_⟩
    dsimp only
    by_cases htop : p = start + k + 1
    · subst htop
      have hsub : start + k + 1 - start = k + 1 := by omega
      simp only [↓reduceIte, hsub, WotsC.chain_succ, ih.1]
    · simp only [htop, ↓reduceIte]
      exact ih.2 p h1 (by omega)

/-- Climb `auth` from step `k` with accumulator `acc`, querying `thSpec pr` once per step and
recording `fVal` and `fPair`. -/
def sfClimbTraceM (id : LeafId) :
    ℕ → pr.Y → List pr.Y → (ℕ → pr.Y) → (ℕ → pr.Y × pr.Y) →
    OracleComp (thSpec pr) (pr.Y × (ℕ → pr.Y) × (ℕ → pr.Y × pr.Y))
  | _, acc, [], vTbl, pTbl => pure (acc, vTbl, pTbl)
  | k, acc, s :: rest, vTbl, pTbl => do
    let pair := if (id.index / 2 ^ k) % 2 = 0 then (acc, s) else (s, acc)
    let next ← (thSpec pr).query
      ⟨.H, (SfAdrs.treeAdrs ⟨id.height + k + 1, id.index / 2 ^ (k + 1)⟩).toAdrs, pair⟩
    sfClimbTraceM id (k + 1) next rest
      (fun j => if j = k + 1 then next else vTbl j)
      (fun j => if j = k then pair else pTbl j)

omit [Inhabited pr.Y] in
private theorem sfClimbTraceM_queryBound (id : LeafId) :
    ∀ (k : ℕ) (acc : pr.Y) (auth : List pr.Y) (vTbl : ℕ → pr.Y) (pTbl : ℕ → pr.Y × pr.Y),
      IsTotalQueryBound (sfClimbTraceM pr id k acc auth vTbl pTbl) auth.length
  | _, _, [], _, _ => (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | k, acc, s :: rest, vTbl, pTbl => by
    unfold sfClimbTraceM
    refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := rest.length) ?_ fun next =>
      sfClimbTraceM_queryBound id (k + 1) next rest _ _).mono (by simp; omega)
    exact (isQueryBoundP_true_iff _ _).1
      ((isQueryBoundP_query_iff (fun _ => True) _ 1).2 fun _ => Nat.zero_lt_one)

private theorem climb_append_one {Y : Type} (node : LeafId → Y → Y → Y) :
    ∀ (z i : ℕ) (acc : Y) (l : List Y) (s : Y),
      Tree.climb node z i acc (l ++ [s]) =
        let v := Tree.climb node z i acc l
        let z' := z + l.length
        let i' := i / 2 ^ l.length
        if i' % 2 = 0 then node ⟨z' + 1, i' / 2⟩ v s else node ⟨z' + 1, i' / 2⟩ s v
  | z, i, acc, [], s => by simp [Tree.climb]
  | z, i, acc, a :: l, s => by
    simp only [List.cons_append, Tree.climb_cons, List.length_cons]
    rw [climb_append_one node (z + 1) (i / 2) _ l s]
    have h1 : z + 1 + l.length = z + (l.length + 1) := by omega
    have h2 : i / 2 / 2 ^ l.length = i / 2 ^ (l.length + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    simp only [h1, h2]

private theorem take_succ_eq_append {α : Type} :
    ∀ (l : List α) (k : ℕ) (_hk : k < l.length) (d : α),
      l.take (k + 1) = l.take k ++ [l.getD k d]
  | [], _, hk, _ => (Nat.not_lt_zero _ hk).elim
  | a :: l, 0, _, _ => by simp
  | a :: l, k + 1, hk, d => by
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    exact congrArg (a :: ·) (take_succ_eq_append l k (Nat.lt_of_succ_lt_succ hk) d)

private theorem simulateQ_sfClimbTraceM (pk : pr.PkSeed) (id : LeafId) (fN0 : pr.Y)
    (fullAuth : List pr.Y) :
    ∀ (k : ℕ) (rest : List pr.Y) (vTbl : ℕ → pr.Y) (pTbl : ℕ → pr.Y × pr.Y),
      fullAuth.drop k = rest → k ≤ fullAuth.length →
      (∀ j ≤ k, vTbl j = Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0
        (fullAuth.take j)) →
      (∀ j < k, pTbl j =
        if (id.index / 2 ^ j) % 2 = 0 then
          (Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j),
            fullAuth.getD j default)
        else
          (fullAuth.getD j default,
            Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j))) →
      let res := Id.run (simulateQ (thRealImpl pr pk)
        (sfClimbTraceM pr id k (vTbl k) rest vTbl pTbl))
      res.1 = Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 fullAuth ∧
      (∀ j ≤ fullAuth.length, res.2.1 j =
        Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j)) ∧
      (∀ j < fullAuth.length, res.2.2 j =
        if (id.index / 2 ^ j) % 2 = 0 then
          (Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j),
            fullAuth.getD j default)
        else
          (fullAuth.getD j default,
            Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j)))
  | k, [], vTbl, pTbl, hdrop, hkle, hv, hp => by
    have hklen : k = fullAuth.length := by
      have := List.drop_eq_nil_iff.1 hdrop
      omega
    subst hklen
    simp only [sfClimbTraceM, simulateQ_pure, Id.run_pure]
    refine ⟨?_, hv, hp⟩
    rw [hv fullAuth.length le_rfl, List.take_length]
  | k, s :: rest, vTbl, pTbl, hdrop, hkle, hv, hp => by
    have hklt : k < fullAuth.length := by
      by_contra h
      have hnil : fullAuth.drop k = [] := List.drop_eq_nil_iff.2 (by omega)
      rw [hnil] at hdrop
      cases hdrop
    have hs_eq : fullAuth.getD k default = s := by
      have h1 : fullAuth[k]? = some s := by
        have h0 := congrArg (fun l => l[0]?) hdrop
        simpa [List.getElem?_drop] using h0
      simp [List.getD_eq_getElem?_getD, h1]
    have hdrop' : fullAuth.drop (k + 1) = rest := by
      have := congrArg List.tail hdrop
      simpa [List.tail_drop] using this
    set acc := vTbl k
    set pair := if (id.index / 2 ^ k) % 2 = 0 then (acc, s) else (s, acc)
    set next := pr.H pk (SfAdrs.treeAdrs ⟨id.height + k + 1, id.index / 2 ^ (k + 1)⟩).toAdrs
      pair.1 pair.2
    have hnext : next =
        Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take (k + 1)) := by
      rw [take_succ_eq_append fullAuth k hklt default, climb_append_one, hs_eq]
      have hlen : (fullAuth.take k).length = k := List.length_take_of_le (by omega)
      have hdiv : id.index / 2 ^ k / 2 = id.index / 2 ^ (k + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      simp only [hlen, hdiv, next, pair, acc, hv k le_rfl]
      split_ifs <;> rfl
    set vTbl' : ℕ → pr.Y := fun j => if j = k + 1 then next else vTbl j
    set pTbl' : ℕ → pr.Y × pr.Y := fun j => if j = k then pair else pTbl j
    have hv' : ∀ j ≤ k + 1, vTbl' j =
        Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j) := by
      intro j hj
      dsimp only [vTbl']
      by_cases hjk : j = k + 1
      · subst hjk; simp [hnext]
      · simp only [hjk, ↓reduceIte]; exact hv j (by omega)
    have hp' : ∀ j < k + 1, pTbl' j =
        if (id.index / 2 ^ j) % 2 = 0 then
          (Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j),
            fullAuth.getD j default)
        else
          (fullAuth.getD j default,
            Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 (fullAuth.take j)) := by
      intro j hj
      dsimp only [pTbl']
      by_cases hjk : j = k
      · subst hjk
        dsimp only [pair, acc]
        simp only [↓reduceIte, hv j le_rfl, hs_eq]
      · simp only [hjk, ↓reduceIte]; exact hp j (by omega)
    have hrun : Id.run (simulateQ (thRealImpl pr pk)
        (sfClimbTraceM pr id k (vTbl k) (s :: rest) vTbl pTbl)) =
        Id.run (simulateQ (thRealImpl pr pk)
          (sfClimbTraceM pr id (k + 1) (vTbl' (k + 1)) rest vTbl' pTbl')) := by
      simp only [sfClimbTraceM, simulateQ_bind, simulateQ_spec_query, Id.run_bind]
      change Id.run (simulateQ (thRealImpl pr pk) (sfClimbTraceM pr id (k + 1) next rest vTbl' pTbl')) = _
      simp [vTbl']
    rw [hrun]
    exact simulateQ_sfClimbTraceM pk id fN0 fullAuth (k + 1) rest vTbl' pTbl' hdrop' (by omega) hv' hp'

private theorem isTotalQueryBound_ofFnM {ι α : Type} {spec : OracleSpec ι} :
    ∀ {k : ℕ} (g : Fin k → OracleComp spec α) (budget : Fin k → ℕ),
      (∀ i, IsTotalQueryBound (g i) (budget i)) →
      IsTotalQueryBound (Vector.ofFnM g) (∑ i, budget i)
  | 0, _, _, _ => by
    rw [Vector.ofFnM_zero, Fin.sum_univ_zero]
    exact (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)
  | k + 1, g, budget, h => by
    rw [Vector.ofFnM_succ, Fin.sum_univ_castSucc]
    refine isTotalQueryBound_bind (isTotalQueryBound_ofFnM (fun i => g i.castSucc)
      (fun i => budget i.castSucc) (fun i => h i.castSucc)) fun xs => ?_
    refine (isTotalQueryBound_bind (h (Fin.last k)) fun a =>
      (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
      (by omega)

private theorem sum_fin_getD_eq_list_sum' :
    ∀ (l : List ℕ) (n : ℕ), l.length = n → ∑ i : Fin n, l.getD i.val 0 = l.sum
  | [], 0, _ => by simp
  | a :: l, n + 1, h => by
    have hl : l.length = n := by simpa using h
    rw [Fin.sum_univ_succ, List.sum_cons, ← sum_fin_getD_eq_list_sum' l n hl]
    rfl

omit [Inhabited pr.Y] in
private theorem sum_complement_digits (d : pr.Y) (hd : WotsC.TargetSum pr d) :
    ∑ ch : Fin P.lsf, (P.w - 1 - WotsC.digit pr d ch.val) = P.lsf * (P.w - 1) - P.Swn := by
  have hlen : (WotsC.digits pr d).length = P.lsf := WotsC.digits_length pr d
  have hsum : ∑ ch : Fin P.lsf, WotsC.digit pr d ch.val = P.Swn := by
    have h1 : (WotsC.digits pr d).sum = P.Swn := hd
    rw [← h1]
    exact sum_fin_getD_eq_list_sum' (WotsC.digits pr d) P.lsf hlen
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

/-- **Single-pass explicit-`thSpec`-oracle FXMSS verifier and trace extractor**: performs at most
`VerifyCount.Vsf P = P.lsf * (P.w - 1) - P.Swn + 2 + P.hsf` (`497`) `Th_λ` queries and records
every intermediate value needed by `B2Pre … B8Pre` and `B2SPre … B8SPre`. -/
def fxmssExtractTableM (id : LeafId) (md : pr.Digest) (w : Scheme.Fxmss.Sig pr) :
    OracleComp (thSpec pr) (Option (FxmssTrace pr)) :=
  if id.height < P.hsf ∧ w.auth.length = P.hsf - id.height ∧
      id.index < 2 ^ min 64 (P.hsf - id.height) then do
    let dStar ← (thSpec pr).query ⟨.grind, (SfAdrs.grindAdrs id).toAdrs, (md, w.wots.ctr)⟩
    if WotsC.TargetSum pr dStar then do
      let chRes ← Vector.ofFnM fun ch : Fin P.lsf =>
        let a := WotsC.digit pr dStar ch.val
        sfChainTraceM pr id ch.val a w.wots.chains[ch.val] (P.w - 1 - a)
      let fTops : Vector pr.Y P.lsf := Vector.ofFn fun ch => (chRes[ch.val]).1
      let chainVal : Fin P.lsf → ℕ → pr.Y := fun ch p => (chRes[ch.val]).2 p
      let fN0 ← (thSpec pr).query ⟨.thLsf, (SfAdrs.pkAdrs id).toAdrs, fTops⟩
      let (finalRoot, fVal, fPair) ←
        sfClimbTraceM pr id 0 fN0 w.auth (fun _ => fN0) (fun _ => default)
      return some ⟨dStar, chainVal, fTops, fN0, fVal, fPair, finalRoot⟩
    else
      return none
  else
    return none

/-- Deterministic evaluation of `fxmssExtractTableM` against `thRealImpl pr pk`. -/
def fxmssExtractTable (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) (w : Scheme.Fxmss.Sig pr) :
    Option (FxmssTrace pr) :=
  Id.run (simulateQ (thRealImpl pr pk) (fxmssExtractTableM pr id md w))

/-- **Exact Lemma 5.1 stateful query bound** for `fxmssExtractTableM`: at most
`Vsf P` (`497` at SHRINCS parameters) `Th_λ` queries on every execution path. -/
theorem fxmssExtractTableM_queryBound (id : LeafId) (md : pr.Digest) (w : Scheme.Fxmss.Sig pr) :
    IsTotalQueryBound (fxmssExtractTableM pr id md w) (Vsf P) := by
  unfold fxmssExtractTableM Vsf
  split_ifs with hval
  · refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := P.lsf * (P.w - 1) - P.Swn + 1 + P.hsf) ?_
      fun dStar => ?_).mono (by omega)
    · exact (isQueryBoundP_true_iff _ _).1
        ((isQueryBoundP_query_iff (fun _ => True) _ 1).2 fun _ => Nat.zero_lt_one)
    · split_ifs with hts
      · refine (isTotalQueryBound_bind
          (n₁ := P.lsf * (P.w - 1) - P.Swn) (n₂ := 1 + P.hsf) ?_ fun chRes => ?_).mono (by omega)
        · have hb := isTotalQueryBound_ofFnM
            (fun ch : Fin P.lsf => sfChainTraceM pr id ch.val (WotsC.digit pr dStar ch.val)
              w.wots.chains[ch.val] (P.w - 1 - WotsC.digit pr dStar ch.val))
            (fun ch : Fin P.lsf => P.w - 1 - WotsC.digit pr dStar ch.val)
            (fun ch => sfChainTraceM_queryBound pr id ch.val _ _ _)
          rwa [sum_complement_digits pr dStar hts] at hb
        · refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := P.hsf) ?_ fun fN0 => ?_).mono (by omega)
          · exact (isQueryBoundP_true_iff _ _).1
              ((isQueryBoundP_query_iff (fun _ => True) _ 1).2 fun _ => Nat.zero_lt_one)
          · refine (isTotalQueryBound_bind (n₁ := w.auth.length) (n₂ := 0)
              (sfClimbTraceM_queryBound pr id 0 fN0 w.auth _ _) fun _ =>
              (isQueryBoundP_true_iff _ _).1 (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono
              (by omega)
      · exact ((isQueryBoundP_true_iff _ _).1
          (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (Nat.zero_le _)
  · exact ((isQueryBoundP_true_iff _ _).1
      (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (Nat.zero_le _)

private theorem idRun_simulateQ_ofFnM {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec Id) :
    ∀ {k : ℕ} (g : Fin k → OracleComp spec α),
      Id.run (simulateQ impl (Vector.ofFnM g)) = Vector.ofFn fun i => Id.run (simulateQ impl (g i)) :=
  fun g => VerifyCount.simulateQ_ofFnM impl g

/-- Exact correctness specification of `fxmssExtractTable`: returns `some ft` iff `fxmssValid`,
and every field of `ft` agrees identically with `Honest`'s verifier functions and `Fxmss.pkFromSig`. -/
theorem fxmssExtractTable_eq_some (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest)
    (w : Scheme.Fxmss.Sig pr) (hv : fxmssValid pr pk id md w) :
    ∃ ft : FxmssTrace pr,
      fxmssExtractTable pr pk id md w = some ft ∧
      ft.dStar = WotsC.encode pr pk id md w.wots.ctr ∧
      (∀ (ch : Fin P.lsf) (p : ℕ),
        WotsC.digit pr ft.dStar ch.val ≤ p → p < P.w →
        ft.chainVal ch p =
          WotsC.chain pr pk id ch.val w.wots.chains[ch.val]
            (WotsC.digit pr ft.dStar ch.val) (p - WotsC.digit pr ft.dStar ch.val)) ∧
      ft.fTops = WotsC.topsFromSig pr pk id ft.dStar w.wots ∧
      ft.fN0 = pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs ft.fTops ∧
      (∀ k ≤ w.auth.length, ft.fVal k =
        Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index ft.fN0 (w.auth.take k)) ∧
      (∀ k < w.auth.length, ft.fPair k =
        if (id.index / 2 ^ k) % 2 = 0 then (ft.fVal k, w.auth.getD k default)
        else (w.auth.getD k default, ft.fVal k)) ∧
      Scheme.Fxmss.pkFromSig pr pk md id w = some ft.finalRoot := by
  obtain ⟨h1, h2, h3, hts⟩ := hv
  have hcond : id.height < P.hsf ∧ w.auth.length = P.hsf - id.height ∧
      id.index < 2 ^ min 64 (P.hsf - id.height) := ⟨h1, h2, h3⟩
  set dStar := WotsC.encode pr pk id md w.wots.ctr
  set chRes : Vector (pr.Y × (ℕ → pr.Y)) P.lsf :=
    Vector.ofFn fun ch : Fin P.lsf =>
      Id.run (simulateQ (thRealImpl pr pk)
        (sfChainTraceM pr id ch.val (WotsC.digit pr dStar ch.val) w.wots.chains[ch.val]
          (P.w - 1 - WotsC.digit pr dStar ch.val)))
  set fTops : Vector pr.Y P.lsf := Vector.ofFn fun ch => (chRes[ch.val]).1
  set chainVal : Fin P.lsf → ℕ → pr.Y := fun ch p => (chRes[ch.val]).2 p
  set fN0 := pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs fTops
  set clRes := Id.run (simulateQ (thRealImpl pr pk)
    (sfClimbTraceM pr id 0 fN0 w.auth (fun _ => fN0) (fun _ => default)))
  have hres : fxmssExtractTable pr pk id md w =
      some ⟨dStar, chainVal, fTops, fN0, clRes.2.1, clRes.2.2, clRes.1⟩ := by
    unfold fxmssExtractTable fxmssExtractTableM
    rw [ite_eq_left hcond, simulateQ_bind, simulateQ_spec_query, Id.run_bind]
    have hch : Id.run (simulateQ (thRealImpl pr pk)
        (Vector.ofFnM fun ch : Fin P.lsf =>
          sfChainTraceM pr id ch.val (WotsC.digit pr dStar ch.val) w.wots.chains[ch.val]
            (P.w - 1 - WotsC.digit pr dStar ch.val))) = chRes :=
      idRun_simulateQ_ofFnM (thRealImpl pr pk) _
    change Id.run (simulateQ (thRealImpl pr pk)
      (if WotsC.TargetSum pr dStar then
        (Vector.ofFnM fun ch : Fin P.lsf =>
          sfChainTraceM pr id ch.val (WotsC.digit pr dStar ch.val) w.wots.chains[ch.val]
            (P.w - 1 - WotsC.digit pr dStar ch.val)) >>= fun chRes' =>
          (thSpec pr).query ⟨.thLsf, (SfAdrs.pkAdrs id).toAdrs,
              Vector.ofFn fun ch => (chRes'[ch.val]).1⟩ >>= fun fN0' =>
            sfClimbTraceM pr id 0 fN0' w.auth (fun _ => fN0') (fun _ => default) >>= fun p =>
              pure (some (FxmssTrace.mk dStar (fun ch q => (chRes'[ch.val]).2 q)
                (Vector.ofFn fun ch => (chRes'[ch.val]).1) fN0' p.2.1 p.2.2 p.1))
      else pure none)) = _
    rw [ite_eq_left hts, simulateQ_bind, Id.run_bind, hch, simulateQ_bind, simulateQ_spec_query,
      Id.run_bind]
    change Id.run (simulateQ (thRealImpl pr pk)
      (sfClimbTraceM pr id 0 fN0 w.auth (fun _ => fN0) (fun _ => default) >>= fun p =>
        pure (some (FxmssTrace.mk dStar chainVal fTops fN0 p.2.1 p.2.2 p.1)))) = _
    rw [simulateQ_bind, Id.run_bind]
    rfl
  have hcl := simulateQ_sfClimbTraceM pr pk id fN0 w.auth 0 w.auth
    (fun _ => fN0) (fun _ => default) rfl (Nat.zero_le _)
    (fun j hj => by cases j with | zero => rfl | succ _ => omega)
    (fun j hj => (Nat.not_lt_zero _ hj).elim)
  refine ⟨⟨dStar, chainVal, fTops, fN0, clRes.2.1, clRes.2.2, clRes.1⟩, hres, rfl, ?_, ?_, rfl,
    ?_, ?_, ?_⟩
  · intro ch p hp1 hp2
    have hc := simulateQ_sfChainTraceM pr pk id ch.val (WotsC.digit pr dStar ch.val)
      w.wots.chains[ch.val] (P.w - 1 - WotsC.digit pr dStar ch.val)
    have hlt := WotsC.digit_lt pr dStar ch.val
    simpa [chainVal, chRes] using hc.2 p hp1 (by omega)
  · apply Vector.ext; intro i hi
    have hc := simulateQ_sfChainTraceM pr pk id i (WotsC.digit pr dStar i)
      w.wots.chains[i] (P.w - 1 - WotsC.digit pr dStar i)
    simpa [fTops, chRes, WotsC.topsFromSig] using hc.1
  · exact hcl.2.1
  · intro k hk
    have h1' := hcl.2.2 k hk
    have h2' := hcl.2.1 k (Nat.le_of_lt hk)
    simpa only [clRes, h2'] using h1'
  · have htops : fTops = WotsC.topsFromSig pr pk id dStar w.wots := by
      apply Vector.ext; intro i hi
      have hc := simulateQ_sfChainTraceM pr pk id i (WotsC.digit pr dStar i)
        w.wots.chains[i] (P.w - 1 - WotsC.digit pr dStar i)
      simpa [fTops, chRes, WotsC.topsFromSig] using hc.1
    have hcl1 : clRes.1 = Tree.climb (Scheme.Fxmss.node pr pk) id.height id.index fN0 w.auth :=
      hcl.1
    simp only [Scheme.Fxmss.pkFromSig, hcond, ↓reduceIte, WotsC.pkFromSig,
      show WotsC.TargetSum pr (WotsC.encode pr pk id md w.wots.ctr) from hts, hcl1]
    exact congrArg some (congrArg (Tree.climb _ _ _ · _) (congrArg (pr.ThLsf pk _) htops.symm))

theorem fxmssExtractTable_eq_none (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest)
    (w : Scheme.Fxmss.Sig pr) (hv : ¬ fxmssValid pr pk id md w) :
    fxmssExtractTable pr pk id md w = none := by
  unfold fxmssExtractTable fxmssExtractTableM
  by_cases hg : id.height < P.hsf ∧ w.auth.length = P.hsf - id.height ∧
      id.index < 2 ^ min 64 (P.hsf - id.height)
  · have hnts : ¬ WotsC.TargetSum pr (WotsC.encode pr pk id md w.wots.ctr) :=
      fun hts => hv ⟨hg.1, hg.2.1, hg.2.2, hts⟩
    simp only [hg]
    change Id.run (simulateQ (thRealImpl pr pk)
      (if WotsC.TargetSum pr (WotsC.encode pr pk id md w.wots.ctr) then _ else pure none)) = none
    simp [hnts]
  · simp [hg]

omit [Inhabited pr.Y] in
/-- Winning verification (`verifyWith = true`) automatically implies `fxmssValid`. -/
theorem fxmssValid_of_verifyWith [DecidableEq pr.Y] {pk : pr.PkSeed} {pkSf : pr.Y}
    {id : LeafId} {w : Scheme.Fxmss.Sig pr} {yf : pr.Digest}
    (h : verifyWith pr pk pkSf id (some w) yf = true) :
    fxmssValid pr pk id yf w := by
  simp only [verifyWith, Scheme.Fxmss.pkFromSig] at h
  split_ifs at h with hg
  · cases hw : WotsC.pkFromSig pr pk id yf w.wots with
    | none => simp [hw] at h
    | some N =>
      rw [WotsC.pkFromSig_eq_some_iff] at hw
      exact ⟨hg.1, hg.2.1, hg.2.2, hw.1⟩

end TraceExtract

/-! ## 2. Precomputed stateful table `SfFullTable` and zero-`Th_λ` Stage-2 runner -/

section Stage2Runner

variable {P : Params} (pr : Primitives P) [Inhabited pr.Y]

/-- Complete Stage-1-precomputed stateful FXMSS table: contains `PK.sf`, every anchor signature,
encoded digest, block, chain values, uncompressed public key, leaf value, and tree node values.
Reading from `SfFullTable` requires **zero** `Th_λ` evaluations in Stage 2. -/
structure SfFullTable where
  /-- Precomputed stateful root `PK.sf`. -/
  pkSf : pr.Y
  /-- Precomputed FXMSS signature for each anchor. -/
  sig : LeafId → Option (Scheme.Fxmss.Sig pr)
  /-- Precomputed honest encoded digest `d_j` for each anchor. -/
  encoded : LeafId → pr.Y
  /-- Precomputed revealed block `σ_{j,ch}` for each anchor and chain. -/
  block : LeafId → Fin P.lsf → pr.Y
  /-- Precomputed honest chain values `chainValue j ch p`. -/
  chainVal : LeafId → Fin P.lsf → ℕ → pr.Y
  /-- Precomputed uncompressed WOTS+C public key `tops j`. -/
  tops : LeafId → Vector pr.Y P.lsf
  /-- Precomputed compressed leaf value `leafVal j`. -/
  leafVal : LeafId → pr.Y
  /-- Precomputed tree node values `nodeVal z i`. -/
  nodeVal : ℕ → ℕ → Option pr.Y

instance : Inhabited (SfFullTable pr) :=
  ⟨⟨default, fun _ => none, fun _ => default, fun _ _ => default, fun _ _ _ => default,
    fun _ => Vector.replicate _ default, fun _ => default, fun _ _ => none⟩⟩

/-- Agreement between a Stage-1-precomputed `SfFullTable` and the honest data `H : Honest pr`
at every position read during Stage 2 and witness extraction. -/
structure SfTableAgree (H : Honest pr) (tbl : SfFullTable pr) : Prop where
  pkSf : tbl.pkSf = H.pkSf
  sig : ∀ id ∈ leafIds P.hsf H.S, tbl.sig id = H.sig id
  encoded : ∀ id ∈ leafIds P.hsf H.S, tbl.encoded id = H.encoded id
  block : ∀ id ∈ leafIds P.hsf H.S, ∀ ch : Fin P.lsf, tbl.block id ch = H.block id ch
  chainVal : ∀ id ∈ leafIds P.hsf H.S, ∀ ch : Fin P.lsf, ∀ p,
    WotsC.digit pr (H.encoded id) ch.val ≤ p → p < P.w → tbl.chainVal id ch p = H.chainValue id ch p
  tops : ∀ id ∈ leafIds P.hsf H.S, tbl.tops id = H.tops id
  leafVal : ∀ id ∈ leafIds P.hsf H.S, tbl.leafVal id = H.leafVal id
  nodeVal : ∀ z i, z ≤ P.hsf → (⟨P.hsf - z, i⟩ : Node) ∈ H.S.nodes → tbl.nodeVal z i = H.value z i

variable (Msg : Type) [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- Signing-phase handler reading precomputed anchor signatures from `SfFullTable` (0 `Th_λ`
evaluations). -/
def implHybPre (K : Keys pr) (dig : LeafId → pr.Digest)
    (sig : LeafId → Option (Scheme.Fxmss.Sig pr)) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp) :=
  impl pr Msg K (fun id x => progStep pr Msg x (dig id)) (fun id _ => sig id)

/-- Stage-2 signing phase using a Stage-1-precomputed `SfFullTable` (zero `Th_λ` evaluations
beyond `A.forge` itself). -/
noncomputable def stageHybPre {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (tbl : SfFullTable pr) (d : Setup pr Msg A.State) (pk : pr.PkSeed) :
    ProbComp (Option (Transcript pr Msg)) :=
  if ¬ d.S.TreeValid P.hsf then pure none else do
    let pkSl ← slKeygen pk
    let K : Keys pr := ⟨d.S, pk, pkSl, tbl.pkSf⟩
    let r ← (simulateQ (implHybPre pr Msg K (digOf pr d.ys) tbl.sig)
      (stage2Prog pr Msg slKeygen A d.st K)).run (St.init pr Msg d.cache)
    return some (Transcript.ofRun pr Msg K r)

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- When `tbl` agrees with `hon pr d.S pk (digOf pr d.ys) β`, `stageHybPre` is identically
`Option.map Prod.fst <$> stageHyb`. -/
theorem stageHybPre_eq_map_stageHyb {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed)
    (tbl : SfFullTable pr)
    (htbl : d.S.TreeValid P.hsf → SfTableAgree pr (hon pr d.S pk (digOf pr d.ys) β) tbl) :
    stageHybPre pr Msg slKeygen A tbl d pk =
      Option.map Prod.fst <$> stageHyb pr Msg slKeygen A β d pk := by
  unfold stageHybPre stageHyb
  by_cases hS : d.S.TreeValid P.hsf
  · have ha := htbl hS
    simp only [hS, not_true_eq_false, ↓reduceIte, map_bind, map_pure]
    refine bind_congr fun pkSl => ?_
    have hK : (⟨d.S, pk, pkSl, tbl.pkSf⟩ : Keys pr) =
        ⟨d.S, pk, pkSl, (hon pr d.S pk (digOf pr d.ys) β).pkSf⟩ := by
      rw [ha.pkSf]
    rw [hK]
    have himpl : implHybPre pr Msg ⟨d.S, pk, pkSl, (hon pr d.S pk (digOf pr d.ys) β).pkSf⟩
          (digOf pr d.ys) tbl.sig =
        implHyb pr Msg ⟨d.S, pk, pkSl, (hon pr d.S pk (digOf pr d.ys) β).pkSf⟩
          (hon pr d.S pk (digOf pr d.ys) β) := by
      unfold implHybPre implHyb impl
      have hs := Hyb.signStep_congr (pr := pr) Msg
        ⟨d.S, pk, pkSl, (hon pr d.S pk (digOf pr d.ys) β).pkSf⟩
        (fun id x => progStep pr Msg x (digOf pr d.ys id))
        (fun id _ => tbl.sig id)
        (fun id _ => (hon pr d.S pk (digOf pr d.ys) β).sig id)
        (fun id hid _ => ha.sig id hid)
      exact congrArg _ hs
    rw [himpl]
    rfl
  · simp [hS]

/-- Explicit-`thSpec`-oracle version of `stage2Prog` for a `BudgetedFxmssForger`. -/
noncomputable def stage2ProgM {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedFxmssForger pr Msg slKeygen qs qh₁ qh₂ L ξ)
    (st : A.State) (K : Keys pr) :
    OracleComp (WithThSpec pr (fullSpec pr Msg)) (Msg × LeafId × Fxmss.Rom.Sig pr × pr.Digest) := do
  let out ← A.forgeM st K.S K.toPK
  let yf ← liftLeftWithTh pr
    ((fullSpec pr Msg).query (.inl (.inr (roIn pr Msg out.2.2.1 K.pk K.pkSf out.2.1 out.1))) :
      OracleComp (fullSpec pr Msg) pr.Digest)
  liftLeftWithTh pr (completion pr Msg (otherMsg Msg out.1) (anchorList P K.S))
  return (out.1, out.2.1, out.2.2, yf)

omit [Inhabited pr.Digest] in
private theorem simulateQ_eraseTh_stage2ProgM {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedFxmssForger pr Msg slKeygen qs qh₁ qh₂ L ξ)
    (st : A.State) (K : Keys pr) :
    simulateQ (eraseThImpl pr (fullSpec pr Msg) K.pk) (stage2ProgM pr Msg slKeygen A st K) =
      stage2Prog pr Msg slKeygen A.toFxmssAdversary st K := by
  unfold stage2ProgM stage2Prog
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_eraseThImpl_liftLeft]
  rw [show K.toPK = (K.pk, K.pkSl, K.pkSf) from rfl, A.forgeM_eq st K.S K.pk K.pkSl K.pkSf]

omit [Inhabited pr.Digest] in
private theorem isQueryBoundP_stage2ProgM {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedFxmssForger pr Msg slKeygen qs qh₁ qh₂ L ξ)
    (st : A.State) (K : Keys pr) :
    (stage2ProgM pr Msg slKeygen A st K).IsQueryBoundP
      (IsRightThQuery pr (fullSpec pr Msg)) ξ := by
  unfold stage2ProgM
  refine (isQueryBoundP_bind (n := ξ) (m := 0) (A.thBound st K.S K.toPK) fun out _ => ?_).mono
    (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftLeftWithTh pr _) fun yf _ =>
    ?_).mono (by omega)
  exact (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftLeftWithTh pr _) fun _ _ =>
    isQueryBoundP_pure _ _ 0).mono (by omega)

/-- **Zero-overhead Stage-2 `Th_λ` bound for `stageHybPre`**: running `stageHybPre` on a
`BudgetedFxmssForger` with budget `ξ` makes at most `ξ` `Th_λ` evaluations (zero from the
signing oracle or precomputed table). -/
noncomputable def stageHybPre_stage2Bound {S : Type} {qs qh₁ qh₂ L ξ : ℕ}
    (A : S → BudgetedFxmssForger pr Msg slKeygen qs qh₁ qh₂ L ξ)
    (tblOf : S → SfFullTable pr)
    (dOf : (st : S) → Setup pr Msg (A st).State) :
    Stage2ThBound pr (fun st pk =>
      stageHybPre pr Msg slKeygen (A st).toFxmssAdversary (tblOf st) (dOf st) pk) ξ where
  progM st pk :=
    let d := dOf st
    let tbl := tblOf st
    if ¬ d.S.TreeValid P.hsf then pure none else do
      let pkSl ← liftProb pr (slKeygen pk)
      let K : Keys pr := ⟨d.S, pk, pkSl, tbl.pkSf⟩
      let r ← (simulateQ (liftStateThImpl pr (implHybPre pr Msg K (digOf pr d.ys) tbl.sig))
        (stage2ProgM pr Msg slKeygen (A st) d.st K)).run (St.init pr Msg d.cache)
      return some (Transcript.ofRun pr Msg K r)
  simulate_eq st pk := by
    dsimp only
    unfold stageHybPre
    by_cases hS : (dOf st).S.TreeValid P.hsf
    · simp only [hS, not_true_eq_false, ↓reduceIte, simulateQ_bind, simulateQ_pure,
        simulateQ_stage2ThImpl_liftProb]
      refine bind_congr fun pkSl => ?_
      rw [simulateQ_stage2ThImpl_runStateTh]
      have he := simulateQ_eraseTh_stage2ProgM pr Msg slKeygen (A st) (dOf st).st
        ⟨(dOf st).S, pk, pkSl, (tblOf st).pkSf⟩
      exact congrArg (· >>= _) (congrArg (fun x =>
        (simulateQ (implHybPre pr Msg ⟨(dOf st).S, pk, pkSl, (tblOf st).pkSf⟩
          (digOf pr (dOf st).ys) (tblOf st).sig) x).run (St.init pr Msg (dOf st).cache)) he)
    · simp only [hS, not_false_eq_true, ↓reduceIte, simulateQ_pure]
  queryBound st pk := by
    dsimp only
    by_cases hS : (dOf st).S.TreeValid P.hsf
    · simp only [hS, not_true_eq_false, ↓reduceIte]
      refine (isQueryBoundP_bind (n := 0) (m := ξ) (isQueryBoundP_liftProb pr _) fun pkSl _ =>
        ?_).mono (by omega)
      refine (isQueryBoundP_bind (n := ξ) (m := 0)
        (isQueryBoundP_runStateTh pr _ (isQueryBoundP_stage2ProgM pr Msg slKeygen (A st) _ _) _)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
    · simp only [hS, not_false_eq_true, ↓reduceIte]
      exact isQueryBoundP_pure _ _ ξ

/-- Generic Stage-2 pattern for all seven stateful reductions (`B2Pre … B8Pre` and
`B2SPre … B8SPre`): run `stageHybPre`, run single-pass `fxmssExtractTable` at most once on the
forgery, and post-process `(tr, optTrace)` purely with **zero** extra `Th_λ` evaluations. -/
noncomputable def stage2RunWithTrace {S α : Type} {qs : ℕ}
    (A : S → Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (tblOf : S → SfFullTable pr)
    (dOf : (st : S) → Setup pr Msg (A st).State)
    (post : S → Option (Transcript pr Msg × Option (FxmssTrace pr)) → α)
    (st : S) (pk : pr.PkSeed) : ProbComp α := do
  let o ← stageHybPre pr Msg slKeygen (A st) (tblOf st) (dOf st) pk
  match o with
  | none => pure (post st none)
  | some tr =>
    match tr.σf.2 with
    | none => pure (post st (some (tr, none)))
    | some w => pure (post st (some (tr, fxmssExtractTable pr pk tr.idf tr.yf w)))

/-- **Unified `≤ ξ + V_sf` (`V_sf = 497`) Stage-2 `Th_λ` complexity bound** for every stateful
reduction structured as `stage2RunWithTrace`. -/
noncomputable def stage2RunWithTrace_stage2Bound {S α : Type} {qs qh₁ qh₂ L ξ : ℕ}
    (A : S → BudgetedFxmssForger pr Msg slKeygen qs qh₁ qh₂ L ξ)
    (tblOf : S → SfFullTable pr)
    (dOf : (st : S) → Setup pr Msg (A st).State)
    (post : S → Option (Transcript pr Msg × Option (FxmssTrace pr)) → α) :
    Stage2ThBound pr
      (stage2RunWithTrace pr Msg slKeygen (fun st => (A st).toFxmssAdversary) tblOf dOf post)
      (ξ + Vsf P) := by
  let hsim := stageHybPre_stage2Bound pr Msg slKeygen A tblOf dOf
  let extM : S → pr.PkSeed → Option (Transcript pr Msg) → OracleComp (thSpec pr) α :=
    fun st _ o =>
      match o with
      | none => pure (post st none)
      | some tr =>
        match tr.σf.2 with
        | none => pure (post st (some (tr, none)))
        | some w => (fun opt => post st (some (tr, opt))) <$> fxmssExtractTableM pr tr.idf tr.yf w
  have hext : ∀ st pk o, IsTotalQueryBound (extM st pk o) (Vsf P) := fun st _ o => by
    cases o with
    | none => exact ((isQueryBoundP_true_iff _ _).1
        (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (Nat.zero_le _)
    | some tr =>
      dsimp only [extM]
      cases hσ : tr.σf.2 with
      | none => exact ((isQueryBoundP_true_iff _ _).1
          (isQueryBoundP_pure (p := fun _ => True) _ 0)).mono (Nat.zero_le _)
      | some w =>
        exact (isQueryBoundP_true_iff _ _).1
          ((isQueryBoundP_map_iff (p := fun _ => True) _ _ _).2
            ((isQueryBoundP_true_iff _ _).2 (fxmssExtractTableM_queryBound pr tr.idf tr.yf w)))
  let hb := hsim.bindTh pr extM hext
  refine ⟨hb.progM, fun st pk => (hb.simulate_eq st pk).trans ?_, hb.queryBound⟩
  unfold stage2RunWithTrace
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun o => ?_
  cases o with
  | none => rfl
  | some tr =>
    cases hσ : tr.σf.2 with
    | none => simp [extM, hσ]
    | some w =>
      simp only [extM, hσ, fxmssExtractTable, map_eq_bind_pure_comp, simulateQ_bind,
        simulateQ_pure, Id.run_bind, Id.run_pure, Function.comp_apply]

end Stage2Runner

/-! ## 3. `HybEventValid` and zero-extra-`Th_λ` trace extractors -/

section TraceExtractors

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]

/-- `HybEvent` guarded by `fxmssValid`: automatically implied by `WinNotC1` and guarantees that
single-pass `fxmssExtractTable` succeeds (`some ft`). -/
def HybEventValid (E : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → Prop) :
    Option (Transcript pr Msg × Honest pr) → Prop
  | some (tr, H) => ∃ w, tr.σf.2 = some w ∧ fxmssValid pr H.pk tr.idf tr.yf w ∧ E H tr.idf tr.yf w
  | none => False

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
theorem stageHyb_events_valid (slKeygen : pr.PkSeed → ProbComp pr.Y)
    (hP : P.Valid) (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed) :
    ∀ o ∈ support (stageHyb pr Msg slKeygen A β d pk), WinNotC1 (o.map Prod.fst) →
      ((((HybEventValid pr Msg Honest.E3 o ∨ HybEventValid pr Msg Honest.E5 o) ∨
        HybEventValid pr Msg Honest.E6 o) ∨ HybEventValid pr Msg Honest.E7 o) ∨
        HybEventValid pr Msg Honest.E8 o) ∨ HybEventValid pr Msg Honest.E9 o := by
  intro o ho hwin
  have hev := stageHyb_events slKeygen hP hinj hgc A β d pk o ho hwin
  rcases o with _ | ⟨tr, H⟩
  · exact hwin.elim
  have hpk : tr.K.pk = H.pk := by
    unfold stageHyb at ho
    split_ifs at ho with hS
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at ho
      obtain ⟨_, -, _, -, rfl, rfl⟩ := ho
      rfl
    · simp at ho
  obtain ⟨⟨hver, -⟩, -⟩ := hwin
  cases hσ : tr.σf.2 with
  | none => simp [verifyWith, hσ] at hver
  | some w =>
    rw [hσ] at hver
    have hval : fxmssValid pr H.pk tr.idf tr.yf w := hpk ▸ fxmssValid_of_verifyWith pr hver
    have wrap : ∀ {E}, HybEvent E (some (tr, H)) → HybEventValid pr Msg E (some (tr, H)) := by
      intro E ⟨w', hw', hE⟩
      rw [hσ, Option.some.injEq] at hw'
      subst hw'
      exact ⟨w, hσ, hval, hE⟩
    rcases hev with ((((h | h) | h) | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (wrap h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (wrap h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (wrap h))))
    · exact Or.inl (Or.inl (Or.inr (wrap h)))
    · exact Or.inl (Or.inr (wrap h))
    · exact Or.inr (wrap h)

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
theorem gameHyb_winNotC1_le_valid (slKeygen : pr.PkSeed → ProbComp pr.Y)
    (hP : P.Valid) (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    (γ : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Pr{let o ← gameHyb pr Msg slKeygen γ A}[WinNotC1 (o.map Prod.fst)] ≤
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E3 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E5 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E6 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E7 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E8 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E9 o] := by
  have hsub : ∀ o ∈ support (gameHyb pr Msg slKeygen γ A), WinNotC1 (o.map Prod.fst) →
      ((((HybEventValid pr Msg Honest.E3 o ∨ HybEventValid pr Msg Honest.E5 o) ∨
        HybEventValid pr Msg Honest.E6 o) ∨ HybEventValid pr Msg Honest.E7 o) ∨
        HybEventValid pr Msg Honest.E8 o) ∨ HybEventValid pr Msg Honest.E9 o := by
    intro o ho hwin
    simp only [gameHyb, mem_support_bind_iff] at ho
    obtain ⟨pk, -, d, -, ho⟩ := ho
    exact stageHyb_events_valid pr Msg slKeygen hP hinj hgc A (betaOf pr γ pk d.u) d pk o ho hwin
  refine (prEvent_mono_of_support _ _ _ hsub).trans ?_
  calc _ ≤ Pr{let o ← gameHyb pr Msg slKeygen γ A}[(((HybEventValid pr Msg Honest.E3 o ∨
            HybEventValid pr Msg Honest.E5 o) ∨ HybEventValid pr Msg Honest.E6 o) ∨
            HybEventValid pr Msg Honest.E7 o) ∨ HybEventValid pr Msg Honest.E8 o] +
          Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEventValid pr Msg Honest.E9 o] :=
          prEvent_or_le _ _ _
    _ ≤ _ := by
          gcongr
          refine (prEvent_or_le _ _ _).trans ?_; gcongr
          refine (prEvent_or_le _ _ _).trans ?_; gcongr
          refine (prEvent_or_le _ _ _).trans ?_; gcongr
          exact prEvent_or_le _ _ _

/-! ### The seven zero-`Th_λ` trace extractors -/

/-- Zero-`Th_λ` extractor for `B2Pre` / `B2SPre` (S-TCR(Prop) of `H_grind`): compares `ft.dStar`
against `e.2.1` in Stage-1 recorded targets `savedQ`. -/
def extract2Trace (savedQ : List ((Adrs × pr.Digest) × (pr.Y × ℕ))) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → ℕ × pr.Digest × ℕ
  | some (tr, some ft) =>
    match tr.σf.2 with
    | some w =>
      match savedQ.findIdx? fun e =>
          decide (e.1.1 = (SfAdrs.grindAdrs tr.idf).toAdrs ∧ e.2.1 = ft.dStar ∧ tr.yf ≠ e.1.2) with
      | some j => (j, (tr.yf, w.wots.ctr.val))
      | none => (0, default)
    | none => (0, default)
  | _ => (0, default)

/-- Zero-`Th_λ` distinguisher for `B3Pre γ` / `B3SPre γ` (SM-UD of `F`): decides `E6Valid` purely
from `(ft, tbl)` using `ft.chainVal ch a = tbl.block idf ch`. -/
noncomputable def dist3Trace (S : Structure) (tbl : SfFullTable pr) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → Bool
  | some (tr, some ft) =>
    decide (tr.idf ∈ leafIds P.hsf S ∧ ∃ ch : Fin P.lsf,
      WotsC.digit pr ft.dStar ch.val < WotsC.digit pr (tbl.encoded tr.idf) ch.val ∧
      ft.chainVal ch (WotsC.digit pr (tbl.encoded tr.idf) ch.val) = tbl.block tr.idf ch)
  | _ => false

/-- Zero-`Th_λ` extractor for `B4Pre` / `B4SPre` (SM-TCR of `F`): finds `(ch, p)` where `ft.chainVal`
and `tbl.chainVal` differ at `p` and collide at `p + 1`, then looks up `savedQ`. -/
noncomputable def extract4Trace (S : Structure) (tbl : SfFullTable pr)
    (savedQ : List (Adrs × pr.Y)) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → ℕ × pr.Y
  | some (tr, some ft) =>
    if tr.idf ∈ leafIds P.hsf S then
      let cands := (List.finRange P.lsf).flatMap fun ch =>
        (List.range (P.w - 1)).filterMap fun p =>
          if WotsC.digit pr (tbl.encoded tr.idf) ch.val ≤ p ∧
             WotsC.digit pr ft.dStar ch.val ≤ p ∧
             ft.chainVal ch p ≠ tbl.chainVal tr.idf ch p ∧
             ft.chainVal ch (p + 1) = tbl.chainVal tr.idf ch (p + 1) then
            some ((SfAdrs.chainAdrs tr.idf ch.val p).toAdrs, ft.chainVal ch p)
          else none
      (cands.findSome? fun c =>
        (savedQ.findIdx? fun e => decide (e.1 = c.1 ∧ c.2 ≠ e.2)).map fun j => (j, c.2)).getD
        (0, default)
    else (0, default)
  | _ => (0, default)

/-- Zero-`Th_λ` inverter for `B5Pre` / `B5SPre` (SM-PRE of `F`): finds `ch` with `a* < a` and
`ft.chainVal ch a = tbl.block idf ch`, outputting `(targetIdx, ft.chainVal ch (a - 1))`. -/
noncomputable def extract5Trace {S : Structure} (tbl : SfFullTable pr)
    (tgs : List (SkIdx P S × Adrs)) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → ℕ × pr.Y
  | some (tr, some ft) =>
    if hid : tr.idf ∈ leafIds P.hsf S then
      match (List.finRange P.lsf).find? fun ch =>
          decide (WotsC.digit pr ft.dStar ch.val < WotsC.digit pr (tbl.encoded tr.idf) ch.val ∧
            ft.chainVal ch (WotsC.digit pr (tbl.encoded tr.idf) ch.val) = tbl.block tr.idf ch) with
      | some ch =>
        let a := WotsC.digit pr (tbl.encoded tr.idf) ch.val
        (tgs.idxOf ((⟨tr.idf, hid⟩, ch), (SfAdrs.chainAdrs tr.idf ch.val (a - 1)).toAdrs),
          ft.chainVal ch (a - 1))
      | none => (0, default)
    else (0, default)
  | _ => (0, default)

/-- Zero-`Th_λ` extractor for `B6Pre` / `B6SPre` (SM-TCR of `Th_lsf`): compares `ft.fTops` and
`ft.fN0` against `tbl.tops` and `tbl.leafVal`, looking up `ADRS^pk` in `savedQ`. -/
noncomputable def extract6Trace (S : Structure) (tbl : SfFullTable pr)
    (savedQ : List (Adrs × Vector pr.Y P.lsf)) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → ℕ × Vector pr.Y P.lsf
  | some (tr, some ft) =>
    if tr.idf ∈ leafIds P.hsf S ∧ ft.fTops ≠ tbl.tops tr.idf ∧ ft.fN0 = tbl.leafVal tr.idf then
      match savedQ.findIdx? fun e =>
          decide (e.1 = (SfAdrs.pkAdrs tr.idf).toAdrs ∧ ft.fTops ≠ e.2) with
      | some j => (j, ft.fTops)
      | none => (0, default)
    else (0, default)
  | _ => (0, default)

/-- Zero-`Th_λ` extractor for `B7Pre` / `B7SPre` (SM-TCR of `H`): scans climb steps `k < |auth|`
comparing `ft.fPair k` against `e.2` and `some (ft.fVal (k + 1))` against `tbl.nodeVal`. -/
def extract7Trace (tbl : SfFullTable pr) (savedQ : List (Adrs × (pr.Y × pr.Y))) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → ℕ × (pr.Y × pr.Y)
  | some (tr, some ft) =>
    match tr.σf.2 with
    | some w =>
      ((List.range w.auth.length).findSome? fun k =>
        let pos := Honest.fPos tr.idf (k + 1)
        if some (ft.fVal (k + 1)) = tbl.nodeVal pos.height pos.index then
          (savedQ.findIdx? fun e =>
            decide (e.1 = (SfAdrs.treeAdrs pos).toAdrs ∧ ft.fPair k ≠ e.2)).map
            fun j => (j, ft.fPair k)
        else none).getD (0, default)
    | none => (0, default)
  | _ => (0, default)

/-- Zero-`Th_λ` extractor for `B8Pre` / `B8SPre` (sm-tcr-excl of `Th_{2∪lsf}`): scans climb steps
against compression targets (`tbl.leafVal`) and the forged leaf against node targets
(`tbl.nodeVal`). -/
def extract8Trace (tbl : SfFullTable pr) (savedQ : List (Adrs × Msg9 pr)) :
    Option (Transcript pr Msg × Option (FxmssTrace pr)) → ℕ × Adrs × Msg9 pr
  | some (tr, some ft) =>
    match tr.σf.2 with
    | some w =>
      let climbHit := (List.range w.auth.length).findSome? fun k =>
        let pos := Honest.fPos tr.idf (k + 1)
        if ft.fVal (k + 1) = tbl.leafVal pos then
          (savedQ.findIdx? fun e => decide (e.1 = (SfAdrs.pkAdrs pos).toAdrs)).map fun j =>
            (j, (SfAdrs.treeAdrs pos).toAdrs, (.inl (ft.fPair k) : Msg9 pr))
        else none
      match climbHit with
      | some hit => hit
      | none =>
        if some ft.fN0 = tbl.nodeVal tr.idf.height tr.idf.index then
          match savedQ.findIdx? fun e => decide (e.1 = (SfAdrs.treeAdrs tr.idf).toAdrs) with
          | some j => (j, (SfAdrs.pkAdrs tr.idf).toAdrs, (.inr ft.fTops : Msg9 pr))
          | none => dflt9 pr
        else dflt9 pr
    | none => dflt9 pr
  | _ => dflt9 pr

/-! ### Pure correctness of the trace extractors -/

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg] in
private theorem fChain_step_eq (H : Honest pr) (idf : LeafId) (yf : pr.Digest)
    (w : Scheme.Fxmss.Sig pr) (ch : Fin P.lsf) {p : ℕ}
    (hp : WotsC.digit pr (H.fEnc idf yf w) ch.val ≤ p) :
    pr.F H.pk (SfAdrs.chainAdrs idf ch.val p).toAdrs (H.fChain idf yf w ch p) =
      H.fChain idf yf w ch (p + 1) := by
  unfold Honest.fChain
  rw [show p + 1 - WotsC.digit pr (H.fEnc idf yf w) ch.val =
      (p - WotsC.digit pr (H.fEnc idf yf w) ch.val) + 1 by omega,
    WotsC.chain_succ, Nat.add_sub_cancel' hp]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg] in
private theorem chainValue_step_eq (H : Honest pr) (idf : LeafId)
    (ch : Fin P.lsf) {p : ℕ} (hp : WotsC.digit pr (H.encoded idf) ch.val ≤ p) :
    pr.F H.pk (SfAdrs.chainAdrs idf ch.val p).toAdrs (H.chainValue idf ch p) =
      H.chainValue idf ch (p + 1) := by
  unfold Honest.chainValue
  rw [show p + 1 - WotsC.digit pr (H.encoded idf) ch.val =
      (p - WotsC.digit pr (H.encoded idf) ch.val) + 1 by omega,
    WotsC.chain_succ, Nat.add_sub_cancel' hp]

omit [Fintype pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg] in
/-- `dist3Trace` agrees pointwise with `decide (HybEventValid Honest.E6 (some (tr, H)))` whenever
`SfTableAgree H tbl`. -/
theorem dist3Trace_eq_decide (H : Honest pr) (tbl : SfFullTable pr) (htbl : SfTableAgree pr H tbl)
    (tr : Transcript pr Msg) :
    dist3Trace pr Msg H.S tbl
      (some (tr, match tr.σf.2 with
        | none => none
        | some w => fxmssExtractTable pr H.pk tr.idf tr.yf w)) =
      decide (HybEventValid pr Msg Honest.E6 (some (tr, H))) := by
  cases hσ : tr.σf.2 with
  | none =>
    simp [dist3Trace, HybEventValid, hσ]
  | some w =>
    by_cases hv : fxmssValid pr H.pk tr.idf tr.yf w
    · obtain ⟨ft, hft, hd, hch, -, -, -, -, -⟩ := fxmssExtractTable_eq_some pr H.pk tr.idf tr.yf w hv
      simp only [hft, dist3Trace, decide_eq_decide, HybEventValid, hσ, Option.some.injEq,
        exists_eq_left', hv, true_and, Honest.E6]
      refine and_congr_right fun hid => exists_congr fun ch => ?_
      rw [htbl.encoded tr.idf hid, htbl.block tr.idf hid ch]
      have hd' : ft.dStar = H.fEnc tr.idf tr.yf w := hd
      rw [hd']
      refine and_congr_right fun hlt => ?_
      have ha_lt : WotsC.digit pr (H.encoded tr.idf) ch.val < P.w := WotsC.digit_lt pr _ _
      have hval := hch ch (WotsC.digit pr (H.encoded tr.idf) ch.val)
        (by rw [hd']; exact Nat.le_of_lt hlt) ha_lt
      rw [hd'] at hval
      have hstep := fChain_step_eq pr H tr.idf tr.yf w ch
        (p := WotsC.digit pr (H.encoded tr.idf) ch.val - 1) (by omega)
      rw [show WotsC.digit pr (H.encoded tr.idf) ch.val - 1 + 1 =
        WotsC.digit pr (H.encoded tr.idf) ch.val by omega] at hstep
      have hval' : ft.chainVal ch (WotsC.digit pr (H.encoded tr.idf) ch.val) =
          H.fChain tr.idf tr.yf w ch (WotsC.digit pr (H.encoded tr.idf) ch.val) := hval
      rw [hval', ← hstep]
    · dsimp only
      rw [fxmssExtractTable_eq_none pr H.pk tr.idf tr.yf w hv]
      simp [dist3Trace, HybEventValid, hσ, hv]

end TraceExtractors

/-! ## 4. Stage-1 full-table builders and permissive oracle simulation -/

section Stage1Builders

variable {P : Params} (pr : Primitives P) [Inhabited pr.Y]

/-- Authentication path read purely from a precomputed node-value table (0 `Th_λ` queries). -/
def authPathFromTable {Y : Type} (nodeVal : ℕ → ℕ → Option Y) : ℕ → ℕ → ℕ → Option (List Y)
  | _, _, 0 => some []
  | z, i, s + 1 =>
    (nodeVal z (Node.sibIdx i)).bind fun a =>
      (authPathFromTable nodeVal (z + 1) (i / 2) s).map (a :: ·)

/-- Whenever `nodeVal` agrees with `Tree.treeNode` on every node of a valid structure `S`,
`authPathFromTable` equals `Tree.authPath` at every node `v ∈ S.nodes`. -/
theorem authPathFromTable_eq {Y : Type} {S : Structure} (hS : S.TreeValid P.hsf)
    {leaf : LeafId → Y} {node : LeafId → Y → Y → Y} {nodeVal : ℕ → ℕ → Option Y}
    (hnode : ∀ z i, z ≤ P.hsf → (⟨P.hsf - z, i⟩ : Node) ∈ S.nodes →
      nodeVal z i = Tree.treeNode P.hsf S leaf node z i) :
    ∀ (s z i : ℕ), z + s = P.hsf → (⟨P.hsf - z, i⟩ : Node) ∈ S.nodes →
      authPathFromTable nodeVal z i s = Tree.authPath P.hsf S leaf node z i s
  | 0, _, _, _, _ => rfl
  | s + 1, z, i, hzs, hv => by
    have hpar : (⟨P.hsf - (z + 1), i / 2⟩ : Node) ∈ S.internal := by
      have h1 := hS.ancestor_mem_internal hv (k := 1) (by omega) (by dsimp; omega)
      simpa [Node.ancestor, show P.hsf - z - 1 = P.hsf - (z + 1) by omega] using h1
    have hsib : (⟨P.hsf - z, Node.sibIdx i⟩ : Node) ∈ S.nodes := by
      have hc := hS.child_mem _ hpar (decide (i % 2 = 0))
      simp only [Node.child] at hc
      convert hc using 2
      · omega
      · unfold Node.sibIdx; split_ifs with h2 <;> simp [h2] <;> omega
    simp only [authPathFromTable, Tree.authPath]
    rw [hnode z (Node.sibIdx i) (by omega) hsib,
      authPathFromTable_eq hS hnode s (z + 1) (i / 2) (by omega)
        (Structure.internal_subset_nodes hpar)]

/-- Accumulated table state threaded during bottom-up `treeTableM` precomputation. -/
structure SfTreeState where
  chainVal : LeafId → Fin P.lsf → ℕ → pr.Y
  tops : LeafId → Vector pr.Y P.lsf
  leafVal : LeafId → pr.Y
  nodeVal : ℕ → ℕ → Option pr.Y

instance : Inhabited (SfTreeState pr) :=
  ⟨⟨fun _ _ _ => default, fun _ => Vector.replicate _ default, fun _ => default, fun _ _ => none⟩⟩

/-- Walk `k` steps of chain `ch` at `id` starting at position `start` with value `x` using `fOp`,
recording every intermediate value `start … start + k`. -/
def chainRecM {m : Type → Type} [Monad m] (fOp : Adrs → pr.Y → m pr.Y)
    (id : LeafId) (ch start : ℕ) (x : pr.Y) : ℕ → m (pr.Y × (ℕ → pr.Y))
  | 0 => pure (x, fun _ => x)
  | k + 1 => do
    let (y, tbl) ← chainRecM fOp id ch start x k
    let y' ← fOp (SfAdrs.chainAdrs id ch (start + k)).toAdrs y
    return (y', fun p => if p = start + k + 1 then y' else tbl p)

/-- Evaluate all `P.lsf` chains at `id` from starting positions `startFn id ch` and starting values
`xFn id ch`, returning `(chainTbl, tops)`. -/
def topsRecM {m : Type → Type} [Monad m] (fOp : Adrs → pr.Y → m pr.Y)
    (startFn : LeafId → Fin P.lsf → ℕ) (xFn : LeafId → Fin P.lsf → pr.Y) (id : LeafId) :
    m ((Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf) := do
  let l ← (List.finRange P.lsf).mapM fun ch =>
    chainRecM pr fOp id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)
  return (fun ch p => (l.getD ch.val (default, fun _ => default)).2 p,
    Vector.ofFn fun ch => (l.getD ch.val (default, fun _ => default)).1)

/-- Evaluate one anchor `id`: chains via `fOp` and compression via `cOp`, returning
`(chainTbl, tops, leafVal)`. -/
def leafRecM {m : Type → Type} [Monad m] (fOp : Adrs → pr.Y → m pr.Y)
    (cOp : Adrs → Vector pr.Y P.lsf → m pr.Y)
    (startFn : LeafId → Fin P.lsf → ℕ) (xFn : LeafId → Fin P.lsf → pr.Y) (id : LeafId) :
    m ((Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y) := do
  let (cTbl, tops) ← topsRecM pr fOp startFn xFn id
  let lv ← cOp (SfAdrs.pkAdrs id).toAdrs tops
  return (cTbl, tops, lv)

/-- Bottom-up traversal of `S` computing the tree root while filling `SfTreeState` at every visited
anchor and internal node in exact `treeOrder`. -/
def treeTableM {m : Type → Type} [Monad m] (S : Structure)
    (leafOp : LeafId → m ((Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y))
    (nodeOp : LeafId → pr.Y → pr.Y → m pr.Y) :
    ℕ → ℕ → SfTreeState pr → m (Option pr.Y × SfTreeState pr)
  | 0, i, st =>
    if (⟨P.hsf, i⟩ : Node) ∈ S.anchors then do
      let (cTbl, tops, lv) ← leafOp ⟨0, i⟩
      return (some lv, {
        chainVal := fun id => if id = ⟨0, i⟩ then cTbl else st.chainVal id
        tops := fun id => if id = ⟨0, i⟩ then tops else st.tops id
        leafVal := fun id => if id = ⟨0, i⟩ then lv else st.leafVal id
        nodeVal := fun z' i' => if z' = 0 ∧ i' = i then some lv else st.nodeVal z' i' })
    else pure (none, st)
  | z + 1, i, st =>
    if z + 1 ≤ P.hsf ∧ (⟨P.hsf - (z + 1), i⟩ : Node) ∈ S.anchors then do
      let (cTbl, tops, lv) ← leafOp ⟨z + 1, i⟩
      return (some lv, {
        chainVal := fun id => if id = ⟨z + 1, i⟩ then cTbl else st.chainVal id
        tops := fun id => if id = ⟨z + 1, i⟩ then tops else st.tops id
        leafVal := fun id => if id = ⟨z + 1, i⟩ then lv else st.leafVal id
        nodeVal := fun z' i' => if z' = z + 1 ∧ i' = i then some lv else st.nodeVal z' i' })
    else if z + 1 ≤ P.hsf ∧ (⟨P.hsf - (z + 1), i⟩ : Node) ∈ S.internal then do
      let (l, st₁) ← treeTableM S leafOp nodeOp z (2 * i) st
      let (r, st₂) ← treeTableM S leafOp nodeOp z (2 * i + 1) st₁
      let vOpt ← combineM (nodeOp ⟨z + 1, i⟩) l r
      return (vOpt, { st₂ with
        nodeVal := fun z' i' => if z' = z + 1 ∧ i' = i then vOpt else st₂.nodeVal z' i' })
    else pure (none, st)

/-- Assemble a `SfFullTable` purely from grinding results `gf` and a populated `SfTreeState`. -/
def assembleSfTable (gf : LeafId → Option (pr.Y × Fin (2 ^ P.c)))
    (st : SfTreeState pr) (fallback : LeafId → Fin P.lsf → pr.Y) : SfFullTable pr where
  pkSf := (st.nodeVal P.hsf 0).getD default
  sig id := (gf id).bind fun (d, c) =>
    (authPathFromTable st.nodeVal id.height id.index (P.hsf - id.height)).map fun auth =>
      ⟨⟨c, Vector.ofFn fun ch => st.chainVal id ch (WotsC.digit pr d ch.val)⟩, auth⟩
  encoded id := match gf id with | some (d, _) => d | none => default
  block id ch := match gf id with
    | some (d, _) => st.chainVal id ch (WotsC.digit pr d ch.val)
    | none => fallback id ch
  chainVal := st.chainVal
  tops := st.tops
  leafVal := st.leafVal
  nodeVal := st.nodeVal

/-- Grind a list of anchors using `grindOp`, recording the results into a function. -/
def grindListM {m : Type → Type} [Monad m]
    (grindOp : LeafId → pr.Digest → m (Option (pr.Y × Fin (2 ^ P.c))))
    (dig : LeafId → pr.Digest) :
    List LeafId → m (LeafId → Option (pr.Y × Fin (2 ^ P.c)))
  | [] => pure fun _ => none
  | id :: ids => do
    let g ← grindOp id (dig id)
    let rest ← grindListM grindOp dig ids
    return fun id' => if id' = id then g else rest id'

/-- **Stage-1 full table builder at `γ = 0`** (shared by `B2Pre`, `B4Pre`, `B6Pre`, `B7Pre`,
`B8Pre` and their Theorem 4.1 counterparts): grinds every anchor via `grindOp`, traverses the
structure in post-order computing all chains (`fOp`), compressions (`cOp`), and internal nodes
(`hOp`), and assembles `SfFullTable`. -/
noncomputable def buildSfTable0M {m : Type → Type} [Monad m]
    (grindOp : LeafId → pr.Digest → m (Option (pr.Y × Fin (2 ^ P.c))))
    (fOp : Adrs → pr.Y → m pr.Y)
    (cOp : Adrs → Vector pr.Y P.lsf → m pr.Y)
    (hOp : Adrs → pr.Y → pr.Y → m pr.Y)
    (S : Structure) (dig : LeafId → pr.Digest) (x : LeafId → ℕ → pr.Y) :
    m (SfFullTable pr) :=
  if S.TreeValid P.hsf then do
    let gf ← grindListM pr grindOp dig (anchorList P S)
    let (_, st) ← treeTableM pr S
      (leafRecM pr fOp cOp (fun _ _ => 0) (fun id ch => x id ch.val))
      (fun id a b => hOp (SfAdrs.treeAdrs id).toAdrs a b)
      P.hsf 0 default
    return assembleSfTable pr gf st (fun id ch => x id ch.val)
  else
    pure default

/-! ### Simulation commutes with `chainRecM`, `treeTableM`, `grindListM`, `buildSfTable0M` -/

section SimComm

variable {ι : Type} {spec : OracleSpec ι} {n : Type → Type} [Monad n] [LawfulMonad n]
  (impl : QueryImpl spec n)

omit [Inhabited pr.Y] in
theorem simulateQ_chainRecM (fOp : Adrs → pr.Y → OracleComp spec pr.Y)
    (id : LeafId) (ch start : ℕ) (x : pr.Y) :
    ∀ k, simulateQ impl (chainRecM pr fOp id ch start x k) =
      chainRecM pr (fun t y => simulateQ impl (fOp t y)) id ch start x k
  | 0 => by simp [chainRecM]
  | k + 1 => by simp [chainRecM, simulateQ_chainRecM fOp id ch start x k]

theorem simulateQ_leafRecM (fOp : Adrs → pr.Y → OracleComp spec pr.Y)
    (cOp : Adrs → Vector pr.Y P.lsf → OracleComp spec pr.Y)
    (startFn : LeafId → Fin P.lsf → ℕ) (xFn : LeafId → Fin P.lsf → pr.Y) (id : LeafId) :
    simulateQ impl (leafRecM pr fOp cOp startFn xFn id) =
      leafRecM pr (fun t y => simulateQ impl (fOp t y))
        (fun t v => simulateQ impl (cOp t v)) startFn xFn id := by
  simp [leafRecM, topsRecM, simulateQ_chainRecM]

omit [Inhabited pr.Y] in
theorem simulateQ_treeTableM (S : Structure)
    (leafOp : LeafId → OracleComp spec ((Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y))
    (nodeOp : LeafId → pr.Y → pr.Y → OracleComp spec pr.Y) :
    ∀ z i st, simulateQ impl (treeTableM pr S leafOp nodeOp z i st) =
      treeTableM pr S (fun id => simulateQ impl (leafOp id))
        (fun id a b => simulateQ impl (nodeOp id a b)) z i st
  | 0, i, st => by unfold treeTableM; split_ifs <;> simp
  | z + 1, i, st => by
    unfold treeTableM
    split_ifs <;>
      simp [simulateQ_treeTableM S leafOp nodeOp z, simulateQ_combineM]

omit [Inhabited pr.Y] in
theorem simulateQ_grindListM
    (grindOp : LeafId → pr.Digest → OracleComp spec (Option (pr.Y × Fin (2 ^ P.c))))
    (dig : LeafId → pr.Digest) :
    ∀ ids, simulateQ impl (grindListM pr grindOp dig ids) =
      grindListM pr (fun id md => simulateQ impl (grindOp id md)) dig ids
  | [] => by simp [grindListM]
  | id :: ids => by simp [grindListM, simulateQ_grindListM grindOp dig ids]

theorem simulateQ_buildSfTable0M
    (grindOp : LeafId → pr.Digest → OracleComp spec (Option (pr.Y × Fin (2 ^ P.c))))
    (fOp : Adrs → pr.Y → OracleComp spec pr.Y)
    (cOp : Adrs → Vector pr.Y P.lsf → OracleComp spec pr.Y)
    (hOp : Adrs → pr.Y → pr.Y → OracleComp spec pr.Y)
    (S : Structure) (dig : LeafId → pr.Digest) (x : LeafId → ℕ → pr.Y) :
    simulateQ impl (buildSfTable0M pr grindOp fOp cOp hOp S dig x) =
      buildSfTable0M pr
        (fun id md => simulateQ impl (grindOp id md))
        (fun t y => simulateQ impl (fOp t y))
        (fun t v => simulateQ impl (cOp t v))
        (fun t a b => simulateQ impl (hOp t a b)) S dig x := by
  unfold buildSfTable0M
  split_ifs
  · simp [simulateQ_grindListM, simulateQ_treeTableM, simulateQ_leafRecM]
  · simp

end SimComm

/-! ### Deterministic `IsLog` semantics and exact `SfTableAgree` for `buildSfTable0M` -/

section LogSemantics

variable {α : Type}

/-- Exact deterministic value of `chainRecM` when `fOp = pr.F pk`. -/
def chainRecDet (pk : pr.PkSeed) (id : LeafId) (ch start : ℕ) (x : pr.Y) :
    ℕ → pr.Y × (ℕ → pr.Y)
  | 0 => (x, fun _ => x)
  | k + 1 =>
    let (y, tbl) := chainRecDet pk id ch start x k
    let y' := pr.F pk (SfAdrs.chainAdrs id ch (start + k)).toAdrs y
    (y', fun p => if p = start + k + 1 then y' else tbl p)

omit [Inhabited pr.Y] in
theorem chainRecDet_spec (pk : pr.PkSeed) (id : LeafId) (ch start : ℕ) (x : pr.Y) :
    ∀ k,
      (chainRecDet pr pk id ch start x k).1 = WotsC.chain pr pk id ch x start k ∧
      ∀ p, start ≤ p → p ≤ start + k →
        (chainRecDet pr pk id ch start x k).2 p = WotsC.chain pr pk id ch x start (p - start)
  | 0 => ⟨rfl, fun p h1 h2 => by
      have : p - start = 0 := by omega
      simp [chainRecDet, this, WotsC.chain]⟩
  | k + 1 => by
    have ih := chainRecDet_spec pk id ch start x k
    simp only [chainRecDet]
    refine ⟨by simp [ih.1, WotsC.chain_succ], fun p h1 h2 => ?_⟩
    by_cases htop : p = start + k + 1
    · subst htop
      have hsub : start + k + 1 - start = k + 1 := by omega
      simp [hsub, WotsC.chain_succ, ih.1]
    · simp only [htop, ↓reduceIte]
      exact ih.2 p h1 (by omega)

omit [Inhabited pr.Y] in
theorem chainRecM_isLog (pk : pr.PkSeed)
    {fOp : Adrs → pr.Y → StateM (List α × List Adrs) pr.Y}
    {fq : Adrs → pr.Y → List α} {fc : Adrs → List Adrs}
    (hF : ∀ t y, IsLog (fOp t y) (pr.F pk t y) (fq t y) (fc t))
    (id : LeafId) (ch start : ℕ) (x : pr.Y) :
    ∀ k, IsLog (chainRecM pr fOp id ch start x k) (chainRecDet pr pk id ch start x k)
      ((List.range k).flatMap fun j =>
        fq (SfAdrs.chainAdrs id ch (start + j)).toAdrs (WotsC.chain pr pk id ch x start j))
      ((List.range k).flatMap fun j => fc (SfAdrs.chainAdrs id ch (start + j)).toAdrs)
  | 0 => (IsLog.pure _).of_eq rfl rfl rfl
  | k + 1 => by
    have ih := chainRecM_isLog pk hF id ch start x k
    have h1 := (chainRecDet_spec pr pk id ch start x k).1
    refine (ih.bind ((hF _ _).bind
      (f := fun y' => pure (y', fun p => if p = start + k + 1 then y' else
        (chainRecDet pr pk id ch start x k).2 p)) (IsLog.pure _))).of_eq ?_ ?_ ?_
    · simp [chainRecDet]
    · simp [List.range_succ, h1]
    · simp [List.range_succ]

/-- Deterministic leaf computation for `leafRecM`. -/
def leafRecDet (pk : pr.PkSeed) (startFn : LeafId → Fin P.lsf → ℕ)
    (xFn : LeafId → Fin P.lsf → pr.Y) (id : LeafId) :
    (Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y :=
  let cTbl : Fin P.lsf → ℕ → pr.Y := fun ch p =>
    (chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).2 p
  let tops : Vector pr.Y P.lsf := Vector.ofFn fun ch =>
    (chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).1
  (cTbl, tops, pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs tops)

omit [Inhabited pr.Y] in
theorem leafRecDet_zero (pk : pr.PkSeed) (x : LeafId → ℕ → pr.Y) (id : LeafId) :
    (leafRecDet pr pk (fun _ _ => 0) (fun id ch => x id ch.val) id).2.1 =
      WotsC.pkTops pr pk id (x id) ∧
    (leafRecDet pr pk (fun _ _ => 0) (fun id ch => x id ch.val) id).2.2 =
      Scheme.Fxmss.leaf pr pk x id := by
  have ht : (leafRecDet pr pk (fun _ _ => 0) (fun id ch => x id ch.val) id).2.1 =
      WotsC.pkTops pr pk id (x id) := by
    apply Vector.ext; intro i hi
    simp only [leafRecDet, Vector.getElem_ofFn, Nat.sub_zero, WotsC.pkTops]
    exact (chainRecDet_spec pr pk id i 0 (x id i) (P.w - 1)).1
  refine ⟨ht, ?_⟩
  simp only [leafRecDet, Scheme.Fxmss.leaf, WotsC.pkGen]
  exact congrArg (pr.ThLsf pk _) ht

theorem leafRecM_isLog (pk : pr.PkSeed)
    {fOp : Adrs → pr.Y → StateM (List α × List Adrs) pr.Y}
    {cOp : Adrs → Vector pr.Y P.lsf → StateM (List α × List Adrs) pr.Y}
    {fq : Adrs → pr.Y → List α} {fc : Adrs → List Adrs}
    {cq : Adrs → Vector pr.Y P.lsf → List α} {cc : Adrs → List Adrs}
    (hF : ∀ t y, IsLog (fOp t y) (pr.F pk t y) (fq t y) (fc t))
    (hC : ∀ t v, IsLog (cOp t v) (pr.ThLsf pk t v) (cq t v) (cc t))
    (startFn : LeafId → Fin P.lsf → ℕ) (xFn : LeafId → Fin P.lsf → pr.Y) (id : LeafId) :
    IsLog (leafRecM pr fOp cOp startFn xFn id) (leafRecDet pr pk startFn xFn id)
      (((List.finRange P.lsf).flatMap fun ch =>
          (List.range (P.w - 1 - startFn id ch)).flatMap fun j =>
            fq (SfAdrs.chainAdrs id ch.val (startFn id ch + j)).toAdrs
              (WotsC.chain pr pk id ch.val (xFn id ch) (startFn id ch) j)) ++
        cq (SfAdrs.pkAdrs id).toAdrs (leafRecDet pr pk startFn xFn id).2.1)
      (((List.finRange P.lsf).flatMap fun ch =>
          (List.range (P.w - 1 - startFn id ch)).flatMap fun j =>
            fc (SfAdrs.chainAdrs id ch.val (startFn id ch + j)).toAdrs) ++
        cc (SfAdrs.pkAdrs id).toAdrs) := by
  unfold leafRecM topsRecM
  have hm := IsLog.mapM (l := List.finRange P.lsf) fun (ch : Fin P.lsf) _ =>
    chainRecM_isLog pr pk hF id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)
  have hget : ∀ ch : Fin P.lsf,
      ((List.finRange P.lsf).map fun ch : Fin P.lsf =>
        chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).getD
        ch.val (default, fun _ => default) =
      chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch) := by
    intro ch
    simp [List.getD_eq_getElem?_getD]
  have htops : (Vector.ofFn fun ch : Fin P.lsf =>
      (((List.finRange P.lsf).map fun ch : Fin P.lsf =>
        chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).getD
        ch.val (default, fun _ => default)).1) = (leafRecDet pr pk startFn xFn id).2.1 := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn, leafRecDet]
    exact congrArg Prod.fst (hget ⟨i, hi⟩)
  have hctbl : (fun (ch : Fin P.lsf) (p : ℕ) =>
      (((List.finRange P.lsf).map fun ch : Fin P.lsf =>
        chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).getD
        ch.val (default, fun _ => default)).2 p) = (leafRecDet pr pk startFn xFn id).1 := by
    funext ch p
    simp only [leafRecDet]
    exact congrFun (congrArg Prod.snd (hget ch)) p
  have htopsStep : IsLog (topsRecM pr fOp startFn xFn id)
      ((leafRecDet pr pk startFn xFn id).1, (leafRecDet pr pk startFn xFn id).2.1)
      ((List.finRange P.lsf).flatMap fun ch =>
        (List.range (P.w - 1 - startFn id ch)).flatMap fun j =>
          fq (SfAdrs.chainAdrs id ch.val (startFn id ch + j)).toAdrs
            (WotsC.chain pr pk id ch.val (xFn id ch) (startFn id ch) j))
      ((List.finRange P.lsf).flatMap fun ch =>
        (List.range (P.w - 1 - startFn id ch)).flatMap fun j =>
          fc (SfAdrs.chainAdrs id ch.val (startFn id ch + j)).toAdrs) := by
    unfold topsRecM
    refine (hm.bind (f := fun l => pure (fun (ch : Fin P.lsf) p =>
        (l.getD ch.val (default, fun _ => default)).2 p,
      Vector.ofFn fun ch : Fin P.lsf => (l.getD ch.val (default, fun _ => default)).1))
      (IsLog.pure _)).of_eq ?_ ?_ ?_
    · exact Prod.ext hctbl htops
    · simp
    · simp
  refine (htopsStep.bind (f := fun p => do
      let lv ← cOp (SfAdrs.pkAdrs id).toAdrs p.2
      pure (p.1, p.2, lv))
    ((hC _ _).bind
      (f := fun lv => pure ((leafRecDet pr pk startFn xFn id).1,
        (leafRecDet pr pk startFn xFn id).2.1, lv))
      (IsLog.pure _))).of_eq rfl ?_ ?_
  · simp
  · simp

/-- Deterministic `treeTableM` (no oracle queries). -/
def treeTableDet (S : Structure)
    (leafDet : LeafId → (Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y)
    (node : LeafId → pr.Y → pr.Y → pr.Y) :
    ℕ → ℕ → SfTreeState pr → Option pr.Y × SfTreeState pr
  | 0, i, st =>
    if (⟨P.hsf, i⟩ : Node) ∈ S.anchors then
      let (cTbl, tops, lv) := leafDet ⟨0, i⟩
      (some lv, {
        chainVal := fun id => if id = ⟨0, i⟩ then cTbl else st.chainVal id
        tops := fun id => if id = ⟨0, i⟩ then tops else st.tops id
        leafVal := fun id => if id = ⟨0, i⟩ then lv else st.leafVal id
        nodeVal := fun z' i' => if z' = 0 ∧ i' = i then some lv else st.nodeVal z' i' })
    else (none, st)
  | z + 1, i, st =>
    if z + 1 ≤ P.hsf ∧ (⟨P.hsf - (z + 1), i⟩ : Node) ∈ S.anchors then
      let (cTbl, tops, lv) := leafDet ⟨z + 1, i⟩
      (some lv, {
        chainVal := fun id => if id = ⟨z + 1, i⟩ then cTbl else st.chainVal id
        tops := fun id => if id = ⟨z + 1, i⟩ then tops else st.tops id
        leafVal := fun id => if id = ⟨z + 1, i⟩ then lv else st.leafVal id
        nodeVal := fun z' i' => if z' = z + 1 ∧ i' = i then some lv else st.nodeVal z' i' })
    else if z + 1 ≤ P.hsf ∧ (⟨P.hsf - (z + 1), i⟩ : Node) ∈ S.internal then
      let (l, st₁) := treeTableDet S leafDet node z (2 * i) st
      let (r, st₂) := treeTableDet S leafDet node z (2 * i + 1) st₁
      let vOpt := Option.map₂ (node ⟨z + 1, i⟩) l r
      (vOpt, { st₂ with
        nodeVal := fun z' i' => if z' = z + 1 ∧ i' = i then vOpt else st₂.nodeVal z' i' })
    else (none, st)

omit [Inhabited pr.Y] in
theorem treeTableDet_fst (S : Structure)
    (leafDet : LeafId → (Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y)
    (node : LeafId → pr.Y → pr.Y → pr.Y) :
    ∀ z i st, (treeTableDet pr S leafDet node z i st).1 =
      Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node z i
  | 0, i, st => by unfold treeTableDet Tree.treeNode; split_ifs <;> rfl
  | z + 1, i, st => by
    unfold treeTableDet Tree.treeNode
    split_ifs
    · rfl
    · rw [← treeTableDet_fst S leafDet node z (2 * i) st,
        ← treeTableDet_fst S leafDet node z (2 * i + 1) (treeTableDet pr S leafDet node z (2 * i) st).2]
    · rfl

omit [Inhabited pr.Y] in
/-- `treeTableDet` populates every visited anchor and internal node, and preserves every unvisited
position. -/
theorem treeTableDet_spec (S : Structure)
    (leafDet : LeafId → (Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y)
    (node : LeafId → pr.Y → pr.Y → pr.Y) :
    ∀ z i st,
      let st' := (treeTableDet pr S leafDet node z i st).2
      (∀ id, .inl id ∈ treeOrder P.hsf S z i →
        st'.chainVal id = (leafDet id).1 ∧
        st'.tops id = (leafDet id).2.1 ∧
        st'.leafVal id = (leafDet id).2.2 ∧
        st'.nodeVal id.height id.index = some (leafDet id).2.2) ∧
      (∀ id, .inr id ∈ treeOrder P.hsf S z i →
        st'.nodeVal id.height id.index =
          Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node id.height id.index) ∧
      (∀ id, id ∉ (treeOrder P.hsf S z i).map posOf →
        st'.chainVal id = st.chainVal id ∧
        st'.tops id = st.tops id ∧
        st'.leafVal id = st.leafVal id ∧
        st'.nodeVal id.height id.index = st.nodeVal id.height id.index)
  | 0, i, st => by
    unfold treeTableDet treeOrder
    split_ifs with ha
    · refine ⟨fun id hid => ?_, fun id hid => by simp at hid, fun id hid => ?_⟩
      · simp only [List.mem_singleton, Sum.inl.injEq] at hid; subst hid; simp
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, posOf] at hid
        have hne : ¬ (id.height = 0 ∧ id.index = i) := fun ⟨h1, h2⟩ => hid (LeafId.ext h1 h2)
        simp [hid, hne]
    · refine ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  | z + 1, i, st => by
    have hnd := nodup_treeOrder (hsf := P.hsf) (S := S) (z + 1) i
    unfold treeTableDet treeOrder
    split_ifs with ha hi
    · refine ⟨fun id hid => ?_, fun id hid => by simp at hid, fun id hid => ?_⟩
      · simp only [List.mem_singleton, Sum.inl.injEq] at hid; subst hid; simp
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, posOf] at hid
        have hne : ¬ (id.height = z + 1 ∧ id.index = i) := fun ⟨h1, h2⟩ => hid (LeafId.ext h1 h2)
        simp [hid, hne]
    · rw [treeOrder, ite_eq_right ha, ite_eq_left hi] at hnd
      simp only [List.map_append, List.map_cons, List.map_nil, posOf] at hnd
      have hdisLR : ∀ x ∈ (treeOrder P.hsf S z (2 * i)).map posOf,
          x ∉ (treeOrder P.hsf S z (2 * i + 1)).map posOf :=
        fun x hx hy => (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 x hx x hy rfl
      have hrootNotL : (⟨z + 1, i⟩ : LeafId) ∉ (treeOrder P.hsf S z (2 * i)).map posOf :=
        fun h => (List.nodup_append.1 hnd).2.2 _ (List.mem_append_left _ h) _ (by simp) rfl
      have hrootNotR : (⟨z + 1, i⟩ : LeafId) ∉ (treeOrder P.hsf S z (2 * i + 1)).map posOf :=
        fun h => (List.nodup_append.1 hnd).2.2 _ (List.mem_append_right _ h) _ (by simp) rfl
      set p₁ := treeTableDet pr S leafDet node z (2 * i) st
      set p₂ := treeTableDet pr S leafDet node z (2 * i + 1) p₁.2
      have hspec1 := treeTableDet_spec S leafDet node z (2 * i) st
      have hspec2 := treeTableDet_spec S leafDet node z (2 * i + 1) p₁.2
      have hp1_fst : p₁.1 = Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node z (2 * i) :=
        treeTableDet_fst pr S leafDet node z (2 * i) st
      have hp2_fst : p₂.1 = Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node z (2 * i + 1) :=
        treeTableDet_fst pr S leafDet node z (2 * i + 1) p₁.2
      have hroot_eq : Option.map₂ (node ⟨z + 1, i⟩) p₁.1 p₂.1 =
          Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node (z + 1) i := by
        rw [hp1_fst, hp2_fst, Tree.treeNode, ite_eq_right ha, ite_eq_left hi]
      refine ⟨fun id hid => ?_, fun id hid => ?_, fun id hid => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hid
        rcases hid with (hL | hR) | hrt
        · have hnotR : id ∉ (treeOrder P.hsf S z (2 * i + 1)).map posOf :=
            hdisLR id (List.mem_map.2 ⟨.inl id, hL, rfl⟩)
          have hne : ¬ (id.height = z + 1 ∧ id.index = i) := fun ⟨h1, h2⟩ => by
            have heq : id = ⟨z + 1, i⟩ := LeafId.ext h1 h2
            rw [← heq] at hrootNotL
            exact hrootNotL (List.mem_map.2 ⟨.inl id, hL, rfl⟩)
          obtain ⟨a1, a2, a3, a4⟩ := hspec1.1 id hL
          obtain ⟨b1, b2, b3, b4⟩ := hspec2.2.2 id hnotR
          exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, by
            dsimp only; rw [ite_eq_right hne, b4, a4]⟩
        · have hne : ¬ (id.height = z + 1 ∧ id.index = i) := fun ⟨h1, h2⟩ => by
            have heq : id = ⟨z + 1, i⟩ := LeafId.ext h1 h2
            rw [← heq] at hrootNotR
            exact hrootNotR (List.mem_map.2 ⟨.inl id, hR, rfl⟩)
          obtain ⟨a1, a2, a3, a4⟩ := hspec2.1 id hR
          exact ⟨a1, a2, a3, by dsimp only; rw [ite_eq_right hne, a4]⟩
        · cases hrt
      · simp only [List.mem_append, List.mem_singleton] at hid
        rcases hid with (hL | hR) | hrt
        · have hnotR : id ∉ (treeOrder P.hsf S z (2 * i + 1)).map posOf :=
            hdisLR id (List.mem_map.2 ⟨.inr id, hL, rfl⟩)
          have hne : ¬ (id.height = z + 1 ∧ id.index = i) := fun ⟨h1, h2⟩ => by
            have heq : id = ⟨z + 1, i⟩ := LeafId.ext h1 h2
            rw [← heq] at hrootNotL
            exact hrootNotL (List.mem_map.2 ⟨.inr id, hL, rfl⟩)
          dsimp only; rw [ite_eq_right hne]
          exact (hspec2.2.2 id hnotR).2.2.2.trans (hspec1.2.1 id hL)
        · have hne : ¬ (id.height = z + 1 ∧ id.index = i) := fun ⟨h1, h2⟩ => by
            have heq : id = ⟨z + 1, i⟩ := LeafId.ext h1 h2
            rw [← heq] at hrootNotR
            exact hrootNotR (List.mem_map.2 ⟨.inr id, hR, rfl⟩)
          dsimp only; rw [ite_eq_right hne]
          exact hspec2.2.1 id hR
        · cases hrt
          dsimp only; rw [ite_eq_left ⟨rfl, rfl⟩, hroot_eq]
      · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, posOf, not_or] at hid
        have hne : ¬ (id.height = z + 1 ∧ id.index = i) := fun ⟨h1, h2⟩ => hid.2 (LeafId.ext h1 h2)
        obtain ⟨a1, a2, a3, a4⟩ := hspec1.2.2 id hid.1.1
        obtain ⟨b1, b2, b3, b4⟩ := hspec2.2.2 id hid.1.2
        exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, by
          dsimp only; rw [ite_eq_right hne, b4, a4]⟩
    · refine ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

omit [Inhabited pr.Y] in
theorem treeTableM_isLog (S : Structure)
    {leafOp : LeafId → StateM (List α × List Adrs) ((Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y)}
    {nodeOp : LeafId → pr.Y → pr.Y → StateM (List α × List Adrs) pr.Y}
    {leafDet : LeafId → (Fin P.lsf → ℕ → pr.Y) × Vector pr.Y P.lsf × pr.Y}
    {node : LeafId → pr.Y → pr.Y → pr.Y}
    {lq : LeafId → List α} {lc : LeafId → List Adrs}
    {nq : LeafId → pr.Y → pr.Y → List α} {nc : LeafId → List Adrs}
    (hl : ∀ id, IsLog (leafOp id) (leafDet id) (lq id) (lc id))
    (hn : ∀ id a b, IsLog (nodeOp id a b) (node id a b) (nq id a b) (nc id)) :
    ∀ z i st, IsLog (treeTableM pr S leafOp nodeOp z i st)
      (treeTableDet pr S leafDet node z i st)
      ((treeOrder P.hsf S z i).flatMap
        (entryQ P.hsf S (fun id => (leafDet id).2.2) node lq nq))
      ((treeOrder P.hsf S z i).flatMap fun
        | .inl id => lc id
        | .inr id =>
          combineLog (fun _ _ => nc id)
            (Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node (id.height - 1) (2 * id.index))
            (Tree.treeNode P.hsf S (fun id => (leafDet id).2.2) node (id.height - 1) (2 * id.index + 1)))
  | 0, i, st => by
    rw [treeTableM, treeTableDet, treeOrder]
    split_ifs
    · refine ((hl ⟨0, i⟩).bind
        (f := fun p => pure (some p.2.2, SfTreeState.mk
          (fun id => if id = ⟨0, i⟩ then p.1 else st.chainVal id)
          (fun id => if id = ⟨0, i⟩ then p.2.1 else st.tops id)
          (fun id => if id = ⟨0, i⟩ then p.2.2 else st.leafVal id)
          (fun z' i' => if z' = 0 ∧ i' = i then some p.2.2 else st.nodeVal z' i')))
        (IsLog.pure _)).of_eq rfl ?_ ?_
      · simp [entryQ]
      · simp
    · exact (IsLog.pure _).of_eq rfl (by simp) (by simp)
  | z + 1, i, st => by
    rw [treeTableM, treeTableDet, treeOrder]
    split_ifs
    · refine ((hl ⟨z + 1, i⟩).bind
        (f := fun p => pure (some p.2.2, SfTreeState.mk
          (fun id => if id = ⟨z + 1, i⟩ then p.1 else st.chainVal id)
          (fun id => if id = ⟨z + 1, i⟩ then p.2.1 else st.tops id)
          (fun id => if id = ⟨z + 1, i⟩ then p.2.2 else st.leafVal id)
          (fun z' i' => if z' = z + 1 ∧ i' = i then some p.2.2 else st.nodeVal z' i')))
        (IsLog.pure _)).of_eq rfl ?_ ?_
      · simp [entryQ]
      · simp
    · have ih1 := treeTableM_isLog S hl hn z (2 * i) st
      have ih2 := treeTableM_isLog S hl hn z (2 * i + 1)
        (treeTableDet pr S leafDet node z (2 * i) st).2
      have h1 := treeTableDet_fst pr S leafDet node z (2 * i) st
      have h2 := treeTableDet_fst pr S leafDet node z (2 * i + 1)
        (treeTableDet pr S leafDet node z (2 * i) st).2
      have hcomb : IsLog
          (combineM (nodeOp ⟨z + 1, i⟩)
            (treeTableDet pr S leafDet node z (2 * i) st).1
            (treeTableDet pr S leafDet node z (2 * i + 1)
              (treeTableDet pr S leafDet node z (2 * i) st).2).1)
          (Option.map₂ (node ⟨z + 1, i⟩)
            (treeTableDet pr S leafDet node z (2 * i) st).1
            (treeTableDet pr S leafDet node z (2 * i + 1)
              (treeTableDet pr S leafDet node z (2 * i) st).2).1)
          (combineLog (nq ⟨z + 1, i⟩)
            (treeTableDet pr S leafDet node z (2 * i) st).1
            (treeTableDet pr S leafDet node z (2 * i + 1)
              (treeTableDet pr S leafDet node z (2 * i) st).2).1)
          (combineLog (fun _ _ => nc ⟨z + 1, i⟩)
            (treeTableDet pr S leafDet node z (2 * i) st).1
            (treeTableDet pr S leafDet node z (2 * i + 1)
              (treeTableDet pr S leafDet node z (2 * i) st).2).1) := by
        cases (treeTableDet pr S leafDet node z (2 * i) st).1 <;>
          cases (treeTableDet pr S leafDet node z (2 * i + 1)
            (treeTableDet pr S leafDet node z (2 * i) st).2).1
        · exact IsLog.pure _
        · exact IsLog.pure _
        · exact IsLog.pure _
        · exact (hn ⟨z + 1, i⟩ _ _).map some
      refine (ih1.bind (ih2.bind (hcomb.bind (f := fun vOpt => pure (vOpt, _))
        (IsLog.pure _)))).of_eq rfl ?_ ?_
      · simp [entryQ, h1, h2]
      · simp [h1, h2]
    · exact (IsLog.pure _).of_eq rfl (by simp) (by simp)

omit [Inhabited pr.Y] in
theorem grindListM_isLog
    {grindOp : LeafId → pr.Digest → StateM (List α × List Adrs) (Option (pr.Y × Fin (2 ^ P.c)))}
    {grindDet : LeafId → pr.Digest → Option (pr.Y × Fin (2 ^ P.c))}
    {gq : LeafId → pr.Digest → List α} {gc : LeafId → pr.Digest → List Adrs}
    (hG : ∀ id md, IsLog (grindOp id md) (grindDet id md) (gq id md) (gc id md))
    (dig : LeafId → pr.Digest) :
    ∀ ids, IsLog (grindListM pr grindOp dig ids)
      (fun id' => if id' ∈ ids then grindDet id' (dig id') else none)
      (ids.flatMap fun id => gq id (dig id))
      (ids.flatMap fun id => gc id (dig id))
  | [] => (IsLog.pure _).of_eq rfl rfl rfl
  | id :: ids => by
    have ih := grindListM_isLog hG dig ids
    refine ((hG id (dig id)).bind (ih.bind
      (f := fun rest => pure (fun id' => if id' = id then _ else rest id'))
      (IsLog.pure _))).of_eq ?_ ?_ ?_
    · funext id'
      by_cases h : id' = id
      · subst h; simp
      · simp [h]
    · simp
    · simp

/-- Deterministic `SfFullTable` produced by `buildSfTable0M` at `γ = 0`. -/
noncomputable def buildSfTable0Det (pk : pr.PkSeed) (S : Structure) (dig : LeafId → pr.Digest)
    (x : LeafId → ℕ → pr.Y) : SfFullTable pr :=
  if S.TreeValid P.hsf then
    let gf : LeafId → Option (pr.Y × Fin (2 ^ P.c)) :=
      fun id => if id ∈ anchorList P S then WotsC.grind pr pk id (dig id) else none
    let st := (treeTableDet pr S
      (leafRecDet pr pk (fun _ _ => 0) (fun id ch => x id ch.val))
      (Scheme.Fxmss.node pr pk) P.hsf 0 default).2
    assembleSfTable pr gf st (fun id ch => x id ch.val)
  else
    default

/-- Exact `SfTableAgree` for `buildSfTable0Det` against `hon pr S pk dig (betaOf pr 0 pk u)` on
any valid structure (under Conjecture 3.1 `hgc`). -/
theorem buildSfTable0Det_agree (hP : P.Valid) (hgc : GrindComplete pr) {S : Structure}
    (hS : S.TreeValid P.hsf) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (u : SkIdx P S → pr.Y) :
    SfTableAgree pr (hon pr S pk dig (betaOf pr 0 pk u))
      (buildSfTable0Det pr pk S dig (skOf pr S u)) := by
  set x := skOf pr S u
  set H := hon pr S pk dig (betaOf pr 0 pk u)
  set leafDet := leafRecDet pr pk (fun _ _ => 0) (fun id ch => x id ch.val)
  set st := (treeTableDet pr S leafDet (Scheme.Fxmss.node pr pk) P.hsf 0 default).2
  have hspec := treeTableDet_spec pr S leafDet (Scheme.Fxmss.node pr pk) P.hsf 0 default
  have hleafEq : (fun id => (leafDet id).2.2) = Scheme.Fxmss.leaf pr pk x := by
    funext id; exact (leafRecDet_zero pr pk x id).2
  have hHleaf : H.leafVal = Scheme.Fxmss.leaf pr pk x := Claim42.hon_leafVal S pk dig u
  have hvisitA : ∀ id ∈ leafIds P.hsf S, .inl id ∈ treeOrder P.hsf S P.hsf 0 := fun id hid => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
    have hle := hS.anchor_depth_le v hv
    exact visit_mem_treeOrder hS (e := .inl (v.toLeafId P.hsf))
      ⟨by simp [Node.toLeafId], by rwa [Node.ofLeafId_toLeafId hle]⟩
  have hnodeEq : ∀ z i, z ≤ P.hsf → (⟨P.hsf - z, i⟩ : Node) ∈ S.nodes →
      st.nodeVal z i = H.value z i := by
    intro z i hz hmem
    change st.nodeVal z i = Tree.treeNode P.hsf S H.leafVal (Scheme.Fxmss.node pr pk) z i
    rw [hHleaf]
    rcases Structure.mem_nodes.1 hmem with hA | hI
    · have hid : (⟨z, i⟩ : LeafId) ∈ leafIds P.hsf S :=
        Finset.mem_image.2 ⟨⟨P.hsf - z, i⟩, hA, by simp [Node.toLeafId, Nat.sub_sub_self hz]⟩
      have hv := (hspec.1 ⟨z, i⟩ (hvisitA _ hid)).2.2.2
      rw [hv, (leafRecDet_zero pr pk x ⟨z, i⟩).2, Tree.treeNode_anchor hz hA]
    · have h1 : 1 ≤ z := by have hlt := hS.internal_depth_lt hI; dsimp at hlt; omega
      have hvis : Visit P.hsf S (.inr ⟨z, i⟩) := ⟨h1, hz, hI⟩
      have hv := hspec.2.1 ⟨z, i⟩ (visit_mem_treeOrder hS hvis)
      rw [hv, hleafEq]
  have hroot : st.nodeVal P.hsf 0 = H.value P.hsf 0 :=
    hnodeEq P.hsf 0 le_rfl (by simpa [Node.root] using Structure.internal_subset_nodes hS.root_mem)
  have hpkSf : (st.nodeVal P.hsf 0).getD default = H.pkSf := by
    simp only [Honest.pkSf, hroot]
  have hgf_eq : ∀ id ∈ leafIds P.hsf S,
      (if id ∈ anchorList P S then WotsC.grind pr pk id (dig id) else none) =
        WotsC.grind pr pk id (dig id) := fun id hid => by
    simp [mem_anchorList.2 hid]
  have hTblDef : buildSfTable0Det pr pk S dig x =
      assembleSfTable pr (fun id => if id ∈ anchorList P S then WotsC.grind pr pk id (dig id) else none)
        st (fun id ch => x id ch.val) := by
    simp [buildSfTable0Det, hS, st, leafDet]
  rw [hTblDef]
  refine ⟨hpkSf, ?_, ?_, ?_, ?_, ?_, ?_, hnodeEq⟩
  · -- sig
    intro id hid
    simp only [assembleSfTable, hgf_eq id hid, Honest.sig]
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (dig id)
    have hHgrind : WotsC.grind pr H.pk id (H.dig id) =
        some (WotsC.encode pr pk id (dig id) c, c) := hg
    rw [hg, hHgrind]
    simp only [Option.bind_some]
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
    have hle := hS.anchor_depth_le v hv
    have hmem : (⟨P.hsf - (v.toLeafId P.hsf).height, (v.toLeafId P.hsf).index⟩ : Node) ∈ S.nodes := by
      have : (⟨P.hsf - (v.toLeafId P.hsf).height, (v.toLeafId P.hsf).index⟩ : Node) = v := by
        simp [Node.toLeafId, Nat.sub_sub_self hle]
      rw [this]; exact Structure.anchors_subset_nodes hv
    have hauth : authPathFromTable st.nodeVal (v.toLeafId P.hsf).height (v.toLeafId P.hsf).index
          (P.hsf - (v.toLeafId P.hsf).height) =
        Tree.authPath P.hsf S H.leafVal (Scheme.Fxmss.node pr pk) (v.toLeafId P.hsf).height
          (v.toLeafId P.hsf).index (P.hsf - (v.toLeafId P.hsf).height) :=
      authPathFromTable_eq hS hnodeEq (P.hsf - (v.toLeafId P.hsf).height)
        (v.toLeafId P.hsf).height (v.toLeafId P.hsf).index
        (by simp [Node.toLeafId]) hmem
    rw [hauth]
    refine congrArg (Option.map · _) (funext fun auth => congrArg (Scheme.Fxmss.Sig.mk · auth) ?_)
    have hw := hon_wots pr (S := S) (β := betaOf pr 0 pk u) hg
    change _ = (hon pr S pk dig (betaOf pr 0 pk u)).wots (v.toLeafId P.hsf)
    rw [hw]; unfold blockSig; congr 1; apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn, Claim42.betaOf_zero]
    rw [(hspec.1 _ (hvisitA _ hid)).1]
    have hlt := WotsC.digit_lt pr (WotsC.encode pr pk (v.toLeafId P.hsf) (dig (v.toLeafId P.hsf)) c) i
    simpa [leafDet, leafRecDet, Nat.sub_zero, x] using
      (chainRecDet_spec pr pk (v.toLeafId P.hsf) i 0 (x (v.toLeafId P.hsf) i) (P.w - 1)).2
        (WotsC.digit pr (WotsC.encode pr pk (v.toLeafId P.hsf) (dig (v.toLeafId P.hsf)) c) i)
        (Nat.zero_le _) (by omega)
  · -- encoded
    intro id hid
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (dig id)
    dsimp only [assembleSfTable]
    rw [hgf_eq id hid, hg]
    exact (hon_encoded pr (S := S) (β := betaOf pr 0 pk u) hg).symm
  · -- block
    intro id hid ch
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (dig id)
    dsimp only [assembleSfTable]
    rw [hgf_eq id hid, hg]
    change st.chainVal id ch (WotsC.digit pr _ ch.val) =
      (hon pr S pk dig (betaOf pr 0 pk u)).block id ch
    rw [(hspec.1 id (hvisitA id hid)).1, hon_block pr (S := S) (β := betaOf pr 0 pk u) hg ch,
      Claim42.betaOf_zero]
    have hlt := WotsC.digit_lt pr (WotsC.encode pr pk id (dig id) c) ch.val
    simpa [leafDet, leafRecDet, Nat.sub_zero, x] using
      (chainRecDet_spec pr pk id ch.val 0 (x id ch.val) (P.w - 1)).2
        (WotsC.digit pr (WotsC.encode pr pk id (dig id) c) ch.val) (Nat.zero_le _) (by omega)
  · -- chainVal
    intro id hid ch p hp1 hp2
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (dig id)
    simp only [assembleSfTable]
    rw [(hspec.1 id (hvisitA id hid)).1]
    have henc := hon_encoded pr (S := S) (β := betaOf pr 0 pk u) hg
    rw [henc] at hp1
    rw [hon0_chainValue pr hg ch hp1]
    simpa [leafDet, leafRecDet, Nat.sub_zero, x] using
      (chainRecDet_spec pr pk id ch.val 0 (x id ch.val) (P.w - 1)).2 p (Nat.zero_le _) (by omega)
  · -- tops
    intro id hid
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (dig id)
    simp only [assembleSfTable]
    rw [(hspec.1 id (hvisitA id hid)).2.1, (leafRecDet_zero pr pk x id).1]
    exact (hon0_tops pr hg).symm
  · -- leafVal
    intro id hid
    simp only [assembleSfTable]
    rw [(hspec.1 id (hvisitA id hid)).2.2.1, (leafRecDet_zero pr pk x id).2, hHleaf]

/-! ### Permissive semantics for `S-TCR(Prop)` (`B2Pre`) -/

/-- State of S-TCR(Prop) permissive runs: recorded targets and collection tweaks. -/
abbrev STcrLogSt (T M N : Type) := List ((T × M) × (N × ℕ)) × List T

noncomputable def stcrPerm {ι P' T M N : Type} (prob : STCRProblem ι P' T M N) (pk : P') :
    QueryImpl (STCR_challengeSpec T M N + collectionSpec prob.thColl)
      (StateM (STcrLogSt T M N)) :=
  (fun tm => (StateT.mk fun s =>
    match leastCounter prob.th prob.prop pk tm.1 tm.2 with
    | none => pure (none, s)
    | some i =>
      let y := prob.th.eval pk tm.1 (tm.2, i)
      pure (some (y, i), (s.1 ++ [(tm, (y, i))], s.2)) :
    StateM (STcrLogSt T M N) (Option (N × ℕ))) : QueryImpl (STCR_challengeSpec T M N) _) +
  (fun q => (StateT.mk fun s =>
    pure (some (prob.thColl.eval q.1 pk q.2.1 q.2.2), (s.1, s.2 ++ [q.2.1])) :
    StateM (STcrLogSt T M N) (Option N)) : QueryImpl (collectionSpec prob.thColl) _)

def STcrGood {T M N : Type} (cap : ℕ) (s : STcrLogSt T M N) : Prop :=
  (s.1.map fun e => e.1.1).Nodup ∧ s.1.length ≤ cap ∧
    ∀ t ∈ s.2, t ∉ s.1.map fun e => e.1.1

theorem STcrGood.mono {T M N : Type} {cap : ℕ} {s s' : STcrLogSt T M N}
    (h : s.1 <+: s'.1 ∧ s.2 <+: s'.2) (hg : STcrGood cap s') : STcrGood cap s := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hn, hl, hc⟩ := hg
  refine ⟨hn.sublist (h1.sublist.map _), (h1.sublist.length_le).trans hl, fun t ht hq => ?_⟩
  exact hc t (h2.sublist.subset ht) ((h1.sublist.map _).subset hq)

theorem stcr_run_eq {ι P' T M N β : Type} [DecidableEq T]
    (prob : STCRProblem ι P' T M N) (pk : P')
    (oa : OracleComp (STCR_challengeSpec T M N + collectionSpec prob.thColl) β)
    (hgood : STcrGood prob.numTargets ((simulateQ (stcrPerm prob pk) oa).run ([], [])).2) :
    (simulateQ (STCR_oracles prob pk)
      (OracleComp.liftComp oa (unifSpec + (STCR_challengeSpec T M N +
        collectionSpec prob.thColl)))).run ([], []) =
      pure ((simulateQ (stcrPerm prob pk) oa).run ([], [])) := by
  rw [STCR_oracles, QueryImpl.simulateQ_add_liftComp_right]
  refine simulateQ_run_eq_pure_of_perm _ (stcrPerm prob pk) (STcrGood prob.numTargets)
    (fun s s' => s.1 <+: s'.1 ∧ s.2 <+: s'.2)
    (fun s => ⟨List.prefix_refl _, List.prefix_refl _⟩)
    (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)
    (fun _ _ h hg => hg.mono h) ?_ ?_ oa _ hgood
  · rintro (tm | q) s
    · simp only [stcrPerm, QueryImpl.add_apply_inl, StateT.run_mk]
      cases leastCounter prob.th prob.prop pk tm.1 tm.2 <;>
        exact ⟨by simp [id_pure_eq], by simp [id_pure_eq]⟩
    · exact ⟨List.prefix_refl _, List.prefix_append _ _⟩
  · rintro (⟨t, m⟩ | q) ⟨Q, C⟩ hg
    · obtain ⟨hn, hl, hc⟩ := hg
      simp only [stcrPerm, QueryImpl.add_apply_inl, StateT.run_mk] at hn hl hc ⊢
      cases hlc : leastCounter prob.th prob.prop pk t m with
      | none =>
        unfold STCR_challengeOracle
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        split_ifs
        · rfl
        · simp only [hlc, StateT.run_pure]; rfl
      | some i =>
        simp only [hlc, id_pure_eq, List.map_append, List.map_cons, List.map_nil,
          List.length_append, List.length_singleton] at hn hl hc ⊢
        have hnot : t ∉ Q.map (fun e => e.1.1) :=
          fun h => (List.nodup_append.1 hn).2.2 _ h _ (by simp) rfl
        have hfr : TweakFresh (fun e : (T × M) × (N × ℕ) => e.1.1) Q C t :=
          ⟨(not_tweakReserved_iff _ _ _).2 fun e he het => hnot (List.mem_map.2 ⟨e, he, het⟩),
            fun htC => hc t htC (by simp)⟩
        unfold STCR_challengeOracle
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        have hcap : ¬ (prob.numTargets ≤ Q.length ∨ ¬ TweakFresh (fun e => e.1.1) Q C t) := by
          push Not; exact ⟨by omega, hfr⟩
        simp only [hcap, ↓reduceIte, hlc]
        rfl
    · obtain ⟨-, -, hc⟩ := hg
      simp only [stcrPerm, QueryImpl.add_apply_inr, StateT.run_mk, id_pure_eq] at hc ⊢
      rw [collectionOracle_run_of_fresh _ _ (by
        rw [not_tweakReserved_iff]
        intro e he heq
        exact hc q.2.1 (by simp) (List.mem_map.2 ⟨e, he, heq⟩))]

/-! ### Stage-1 collection-only table builder for `B3Pre γ` and `B5Pre` -/

/-- `O_coll`-only tree+chain table builder in `Hyb.FSpec pr` given pre-computed grinding results `gf`,
chain starting positions `startOf a`, and starting values `u'` (used after `Hyb.pickProg` in
`B3Pre γ` and `B5Pre`). -/
noncomputable def buildSfTableHybM [SampleableType pr.PkSeed] [SampleableType pr.Y]
    (startOf : ℕ → ℕ) {S : Structure}
    (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c)))
    (u' : SkIdx P S → pr.Y) : OracleComp (Hyb.FSpec pr) (SfFullTable pr) :=
  let gfLeaf : LeafId → Option (pr.Y × Fin (2 ^ P.c)) :=
    fun id => if h : id ∈ leafIds P.hsf S then gf ⟨id, h⟩ else none
  let fOp : Adrs → pr.Y → OracleComp (Hyb.FSpec pr) pr.Y := fun t y => do
    let r ← ((Hyb.FSpec pr).query (.inr (.inr ⟨some .F, t, y⟩)) :
      OracleComp (Hyb.FSpec pr) (Option pr.Y))
    return r.getD default
  let cOp : Adrs → Vector pr.Y P.lsf → OracleComp (Hyb.FSpec pr) pr.Y := fun t v => do
    let r ← ((Hyb.FSpec pr).query (.inr (.inr ⟨some .thLsf, t, v⟩)) :
      OracleComp (Hyb.FSpec pr) (Option pr.Y))
    return r.getD default
  let hOp : Adrs → pr.Y → pr.Y → OracleComp (Hyb.FSpec pr) pr.Y := fun t a b => do
    let r ← ((Hyb.FSpec pr).query (.inr (.inr ⟨some .H, t, (a, b)⟩)) :
      OracleComp (Hyb.FSpec pr) (Option pr.Y))
    return r.getD default
  let startFn : LeafId → Fin P.lsf → ℕ := fun id ch =>
    startOf (Hyb.relDigOf pr (gfLeaf id) ch.val)
  let xFn : LeafId → Fin P.lsf → pr.Y := fun id ch => skOf pr S u' id ch.val
  do
    let (_, st) ← treeTableM pr S (leafRecM pr fOp cOp startFn xFn)
      (fun id a b => hOp (SfAdrs.treeAdrs id).toAdrs a b) P.hsf 0 default
    return assembleSfTable pr gfLeaf st xFn

/-- Deterministic `SfFullTable` produced by `buildSfTableHybM`. -/
noncomputable def buildSfTableHybDet (pk : pr.PkSeed) (startOf : ℕ → ℕ)
    {S : Structure} (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c)))
    (u' : SkIdx P S → pr.Y) : SfFullTable pr :=
  let gfLeaf : LeafId → Option (pr.Y × Fin (2 ^ P.c)) :=
    fun id => if h : id ∈ leafIds P.hsf S then gf ⟨id, h⟩ else none
  let startFn : LeafId → Fin P.lsf → ℕ := fun id ch =>
    startOf (Hyb.relDigOf pr (gfLeaf id) ch.val)
  let xFn : LeafId → Fin P.lsf → pr.Y := fun id ch => skOf pr S u' id ch.val
  let st := (treeTableDet pr S (leafRecDet pr pk startFn xFn) (Scheme.Fxmss.node pr pk)
    P.hsf 0 default).2
  assembleSfTable pr gfLeaf st xFn

/-- Running `buildSfTableHybM` against any `CollAnswers` handler when every `F`-tweak queried
avoids the reserved challenge log `qs` succeeds deterministically without modifying `qs`. -/
theorem run_buildSfTableHybM [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Digest]
    {Q : Type} {tweakOf : Q → Adrs} {pk : pr.PkSeed}
    {impl : QueryImpl (Hyb.FSpec pr) (StateT (List Q × List Adrs) ProbComp)}
    (hcoll : Hyb.CollAnswers pr tweakOf pk impl)
    (startOf : ℕ → ℕ) {S : Structure}
    (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c)))
    (u' : SkIdx P S → pr.Y) (qs : List Q) (tws : List Adrs)
    (hdisF : ∀ id (hid : id ∈ leafIds P.hsf S) (ch : Fin P.lsf) (j : ℕ),
      j < P.w - 1 - startOf (Hyb.relDigOf pr (gf ⟨id, hid⟩) ch.val) →
      ¬ TweakReserved tweakOf qs
        (SfAdrs.chainAdrs id ch.val (startOf (Hyb.relDigOf pr (gf ⟨id, hid⟩) ch.val) + j)).toAdrs)
    (hdisPk : ∀ id, ¬ TweakReserved tweakOf qs (SfAdrs.pkAdrs id).toAdrs)
    (hdisTr : ∀ id, ¬ TweakReserved tweakOf qs (SfAdrs.treeAdrs id).toAdrs) :
    ∃ tws',
      (simulateQ impl (buildSfTableHybM pr startOf gf u')).run (qs, tws) =
        pure (buildSfTableHybDet pr pk startOf gf u', (qs, tws')) := by
  set gfLeaf : LeafId → Option (pr.Y × Fin (2 ^ P.c)) :=
    fun id => if h : id ∈ leafIds P.hsf S then gf ⟨id, h⟩ else none
  set startFn : LeafId → Fin P.lsf → ℕ := fun id ch =>
    startOf (Hyb.relDigOf pr (gfLeaf id) ch.val)
  set xFn : LeafId → Fin P.lsf → pr.Y := fun id ch => skOf pr S u' id ch.val
  set fOp : Adrs → pr.Y → OracleComp (Hyb.FSpec pr) pr.Y := fun t y => do
    let r ← ((Hyb.FSpec pr).query (.inr (.inr ⟨some .F, t, y⟩)) :
      OracleComp (Hyb.FSpec pr) (Option pr.Y))
    return r.getD default
  set cOp : Adrs → Vector pr.Y P.lsf → OracleComp (Hyb.FSpec pr) pr.Y := fun t v => do
    let r ← ((Hyb.FSpec pr).query (.inr (.inr ⟨some .thLsf, t, v⟩)) :
      OracleComp (Hyb.FSpec pr) (Option pr.Y))
    return r.getD default
  set hOp : Adrs → pr.Y → pr.Y → OracleComp (Hyb.FSpec pr) pr.Y := fun t a b => do
    let r ← ((Hyb.FSpec pr).query (.inr (.inr ⟨some .H, t, (a, b)⟩)) :
      OracleComp (Hyb.FSpec pr) (Option pr.Y))
    return r.getD default
  have hfRun : ∀ t y tws₀, ¬ TweakReserved tweakOf qs t →
      (simulateQ impl (fOp t y)).run (qs, tws₀) = pure (pr.F pk t y, (qs, tws₀ ++ [t])) := by
    intro t y tws₀ hnr
    simp only [fOp, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, hcoll ⟨some .F, t, y⟩ qs tws₀ hnr, pure_bind, Option.getD_some]
    rfl
  have hcRun : ∀ t v tws₀, ¬ TweakReserved tweakOf qs t →
      (simulateQ impl (cOp t v)).run (qs, tws₀) = pure (pr.ThLsf pk t v, (qs, tws₀ ++ [t])) := by
    intro t v tws₀ hnr
    simp only [cOp, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, hcoll ⟨some .thLsf, t, v⟩ qs tws₀ hnr, pure_bind, Option.getD_some]
    rfl
  have hhRun : ∀ t a b tws₀, ¬ TweakReserved tweakOf qs t →
      (simulateQ impl (hOp t a b)).run (qs, tws₀) = pure (pr.H pk t a b, (qs, tws₀ ++ [t])) := by
    intro t a b tws₀ hnr
    simp only [hOp, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, hcoll ⟨some .H, t, (a, b)⟩ qs tws₀ hnr, pure_bind, Option.getD_some]
    rfl
  have hchain : ∀ id (hid : id ∈ leafIds P.hsf S) (ch : Fin P.lsf) (k : ℕ),
      k ≤ P.w - 1 - startFn id ch →
      ∀ tws₀, ∃ tws₁,
        (simulateQ impl (chainRecM pr fOp id ch.val (startFn id ch) (xFn id ch) k)).run (qs, tws₀) =
          pure (chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) k, (qs, tws₁)) := by
    intro id hid ch k
    induction k with
    | zero => intro _ tws₀; exact ⟨tws₀, by simp [chainRecM, chainRecDet]⟩
    | succ k ih =>
      intro hk tws₀
      obtain ⟨tws₁, hr1⟩ := ih (by omega) tws₀
      have hnr : ¬ TweakReserved tweakOf qs (SfAdrs.chainAdrs id ch.val (startFn id ch + k)).toAdrs := by
        have hgf' : gfLeaf id = gf ⟨id, hid⟩ := by simp [gfLeaf, hid]
        have := hdisF id hid ch k (by simpa [startFn, hgf'] using hk)
        simpa [startFn, hgf'] using this
      refine ⟨tws₁ ++ [(SfAdrs.chainAdrs id ch.val (startFn id ch + k)).toAdrs], ?_⟩
      simp only [chainRecM, chainRecDet, simulateQ_bind, StateT.run_bind, hr1, pure_bind,
        hfRun _ _ tws₁ hnr, simulateQ_pure, StateT.run_pure]
  have hmapM : ∀ (id : LeafId) (hid : id ∈ leafIds P.hsf S) (l : List (Fin P.lsf)) (tws₀ : List Adrs),
      ∃ tws₁,
        (simulateQ impl (l.mapM fun ch =>
          chainRecM pr fOp id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch))).run
          (qs, tws₀) =
          pure (l.map fun ch =>
            chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch),
            (qs, tws₁)) := by
    intro id hid l
    induction l with
    | nil => intro tws₀; exact ⟨tws₀, by simp⟩
    | cons ch rest ih =>
      intro tws₀
      obtain ⟨tws₁, hr1⟩ := hchain id hid ch (P.w - 1 - startFn id ch) le_rfl tws₀
      obtain ⟨tws₂, hr2⟩ := ih tws₁
      refine ⟨tws₂, ?_⟩
      simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2,
        simulateQ_pure, StateT.run_pure, List.map_cons]
  have hleaf : ∀ id (hid : id ∈ leafIds P.hsf S) tws₀, ∃ tws₁,
      (simulateQ impl (leafRecM pr fOp cOp startFn xFn id)).run (qs, tws₀) =
        pure (leafRecDet pr pk startFn xFn id, (qs, tws₁)) := by
    intro id hid tws₀
    obtain ⟨tws₁, hr1⟩ := hmapM id hid (List.finRange P.lsf) tws₀
    have hget : ∀ ch : Fin P.lsf,
        ((List.finRange P.lsf).map fun ch : Fin P.lsf =>
          chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).getD
          ch.val (default, fun _ => default) =
        chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch) := by
      intro ch; simp [List.getD_eq_getElem?_getD]
    have htops : (Vector.ofFn fun ch : Fin P.lsf =>
        (((List.finRange P.lsf).map fun ch : Fin P.lsf =>
          chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).getD
          ch.val (default, fun _ => default)).1) = (leafRecDet pr pk startFn xFn id).2.1 := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn, leafRecDet]
      exact congrArg Prod.fst (hget ⟨i, hi⟩)
    have hctbl : (fun (ch : Fin P.lsf) (p : ℕ) =>
        (((List.finRange P.lsf).map fun ch : Fin P.lsf =>
          chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch) (P.w - 1 - startFn id ch)).getD
          ch.val (default, fun _ => default)).2 p) = (leafRecDet pr pk startFn xFn id).1 := by
      funext ch p; simp only [leafRecDet]; exact congrFun (congrArg Prod.snd (hget ch)) p
    refine ⟨tws₁ ++ [(SfAdrs.pkAdrs id).toAdrs], ?_⟩
    simp only [leafRecM, topsRecM, simulateQ_bind, StateT.run_bind, hr1, pure_bind,
      simulateQ_pure, StateT.run_pure, htops, hctbl, hcRun _ _ tws₁ (hdisPk id)]
    rfl
  have htree : ∀ z i st tws₀, ∃ tws₁,
      (simulateQ impl (treeTableM pr S (leafRecM pr fOp cOp startFn xFn)
        (fun id a b => hOp (SfAdrs.treeAdrs id).toAdrs a b) z i st)).run (qs, tws₀) =
        pure (treeTableDet pr S (leafRecDet pr pk startFn xFn) (Scheme.Fxmss.node pr pk) z i st,
          (qs, tws₁)) := by
    intro z
    induction z with
    | zero =>
      intro i st tws₀
      unfold treeTableM treeTableDet
      split_ifs with hA
      · have hid : (⟨0, i⟩ : LeafId) ∈ leafIds P.hsf S :=
          Finset.mem_image.2 ⟨⟨P.hsf, i⟩, hA, by simp [Node.toLeafId]⟩
        obtain ⟨tws₁, hr1⟩ := hleaf ⟨0, i⟩ hid tws₀
        refine ⟨tws₁, ?_⟩
        simp only [simulateQ_bind, StateT.run_bind, hr1, pure_bind, simulateQ_pure, StateT.run_pure]
      · exact ⟨tws₀, by simp⟩
    | succ z ih =>
      intro i st tws₀
      unfold treeTableM treeTableDet
      split_ifs with hA hI
      · have hid : (⟨z + 1, i⟩ : LeafId) ∈ leafIds P.hsf S :=
          Finset.mem_image.2 ⟨⟨P.hsf - (z + 1), i⟩, hA.2, by
            simp [Node.toLeafId, Nat.sub_sub_self hA.1]⟩
        obtain ⟨tws₁, hr1⟩ := hleaf ⟨z + 1, i⟩ hid tws₀
        refine ⟨tws₁, ?_⟩
        simp only [simulateQ_bind, StateT.run_bind, hr1, pure_bind, simulateQ_pure, StateT.run_pure]
      · obtain ⟨tws₁, hr1⟩ := ih (2 * i) st tws₀
        obtain ⟨tws₂, hr2⟩ := ih (2 * i + 1)
          (treeTableDet pr S (leafRecDet pr pk startFn xFn) (Scheme.Fxmss.node pr pk) z (2 * i) st).2
          tws₁
        cases hl : (treeTableDet pr S (leafRecDet pr pk startFn xFn) (Scheme.Fxmss.node pr pk) z (2 * i) st).1 <;>
          cases hr : (treeTableDet pr S (leafRecDet pr pk startFn xFn) (Scheme.Fxmss.node pr pk) z (2 * i + 1)
            (treeTableDet pr S (leafRecDet pr pk startFn xFn) (Scheme.Fxmss.node pr pk) z (2 * i) st).2).1
        · exact ⟨tws₂, by
            simp only [simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, hl, hr,
              combineM, Option.map₂, simulateQ_pure, StateT.run_pure]; rfl⟩
        · exact ⟨tws₂, by
            simp only [simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, hl, hr,
              combineM, Option.map₂, simulateQ_pure, StateT.run_pure]; rfl⟩
        · exact ⟨tws₂, by
            simp only [simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, hl, hr,
              combineM, Option.map₂, simulateQ_pure, StateT.run_pure]; rfl⟩
        · rename_i a b
          refine ⟨tws₂ ++ [(SfAdrs.treeAdrs ⟨z + 1, i⟩).toAdrs], ?_⟩
          simp only [simulateQ_bind, StateT.run_bind, hr1, pure_bind, hr2, hl, hr,
            combineM, Option.map₂, simulateQ_map, StateT.run_map, hhRun _ _ _ tws₂ (hdisTr _),
            map_pure, pure_bind, simulateQ_pure, StateT.run_pure]
          rfl
      · exact ⟨tws₀, by simp⟩
  obtain ⟨tws', hr⟩ := htree P.hsf 0 default tws
  refine ⟨tws', ?_⟩
  change (simulateQ impl (treeTableM pr S (leafRecM pr fOp cOp startFn xFn)
    (fun id a b => hOp (SfAdrs.treeAdrs id).toAdrs a b) P.hsf 0 default >>= fun p =>
      pure (assembleSfTable pr gfLeaf p.2 xFn))).run (qs, tws) = _
  rw [simulateQ_bind, StateT.run_bind, hr, pure_bind, simulateQ_pure, StateT.run_pure]
  rfl

/-- Exact `SfTableAgree` for `buildSfTableHybDet` when `gf` is `WotsC.grind` and `startOf a`
matches the block source `β` (covers both `B3Pre γ` with `startOf a = min (γ + 1) (a - 1)` and
`B5Pre` with `startOf a = a`). -/
theorem buildSfTableHybDet_agree [Inhabited pr.Digest] (hP : P.Valid) (hgc : GrindComplete pr) {S : Structure}
    (hS : S.TreeValid P.hsf) (pk : pr.PkSeed)
    (ys : Anchor P S → pr.Digest) (u' : SkIdx P S → pr.Y)
    (startOf : ℕ → ℕ) (β : LeafId → ℕ → ℕ → pr.Y)
    (hstart : ∀ a < P.w, startOf a ≤ a)
    (hβ : ∀ id (_hid : id ∈ leafIds P.hsf S) (ch : Fin P.lsf),
      let a := Hyb.relDig pr pk (digOf pr ys) id ch.val
      WotsC.chain pr pk id ch.val (skOf pr S u' id ch.val) (startOf a) (a - startOf a) =
        β id ch.val a) :
    SfTableAgree pr (hon pr S pk (digOf pr ys) β)
      (buildSfTableHybDet pr pk startOf
        (fun a => WotsC.grind pr pk a.1 (digOf pr ys a.1)) u') := by
  set gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c)) :=
    fun a => WotsC.grind pr pk a.1 (digOf pr ys a.1)
  set gfLeaf : LeafId → Option (pr.Y × Fin (2 ^ P.c)) :=
    fun id => if h : id ∈ leafIds P.hsf S then gf ⟨id, h⟩ else none
  set startFn : LeafId → Fin P.lsf → ℕ := fun id ch =>
    startOf (Hyb.relDigOf pr (gfLeaf id) ch.val)
  set xFn : LeafId → Fin P.lsf → pr.Y := fun id ch => skOf pr S u' id ch.val
  set leafDet := leafRecDet pr pk startFn xFn
  set st := (treeTableDet pr S leafDet (Scheme.Fxmss.node pr pk) P.hsf 0 default).2
  set H := hon pr S pk (digOf pr ys) β
  have hspec := treeTableDet_spec pr S leafDet (Scheme.Fxmss.node pr pk) P.hsf 0 default
  have hvisitA : ∀ id ∈ leafIds P.hsf S, .inl id ∈ treeOrder P.hsf S P.hsf 0 := fun id hid => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
    have hle := hS.anchor_depth_le v hv
    exact visit_mem_treeOrder hS (e := .inl (v.toLeafId P.hsf))
      ⟨by simp [Node.toLeafId], by rwa [Node.ofLeafId_toLeafId hle]⟩
  have hgf_anchor : ∀ id ∈ leafIds P.hsf S, gfLeaf id = WotsC.grind pr pk id (digOf pr ys id) :=
    fun id hid => by simp [gfLeaf, gf, hid]
  have hstart_anchor : ∀ id ∈ leafIds P.hsf S, ∀ ch : Fin P.lsf,
      startFn id ch = startOf (Hyb.relDig pr pk (digOf pr ys) id ch.val) :=
    fun id hid ch => by simp [startFn, hgf_anchor id hid, Hyb.relDig]
  have hchain_eq : ∀ id (hid : id ∈ leafIds P.hsf S) (ch : Fin P.lsf) (p : ℕ),
      let a := Hyb.relDig pr pk (digOf pr ys) id ch.val
      a ≤ p → p < P.w →
      (leafDet id).1 ch p = WotsC.chain pr pk id ch.val (β id ch.val a) a (p - a) := by
    intro id hid ch p a hap hpw
    have ha_lt : a < P.w := Hyb.relDigOf_lt _ _
    have hst_le : startFn id ch ≤ a := by rw [hstart_anchor id hid ch]; exact hstart a ha_lt
    have hdet := (chainRecDet_spec pr pk id ch.val (startFn id ch) (xFn id ch)
      (P.w - 1 - startFn id ch)).2 p (hst_le.trans hap) (by omega)
    have hcomp := WotsC.chain_compose pr pk id ch.val (xFn id ch) (startFn id ch)
      (a - startFn id ch) (p - a)
    rw [show startFn id ch + (a - startFn id ch) = a by omega,
      show a - startFn id ch + (p - a) = p - startFn id ch by omega] at hcomp
    have hβ' : WotsC.chain pr pk id ch.val (xFn id ch) (startFn id ch) (a - startFn id ch) =
        β id ch.val a := by
      rw [hstart_anchor id hid ch]; exact hβ id hid ch
    change (chainRecDet pr pk id ch.val (startFn id ch) (xFn id ch)
      (P.w - 1 - startFn id ch)).2 p = _
    rw [hdet, ← hcomp, hβ']
  have htops_eq : ∀ id (_hid : id ∈ leafIds P.hsf S),
      (leafDet id).2.1 = match WotsC.grind pr pk id (digOf pr ys id) with
        | some (d, c) => WotsC.topsFromSig pr pk id d (blockSig pr β id d c)
        | none => Vector.ofFn fun ch : Fin P.lsf =>
            WotsC.chain pr pk id ch.val (β id ch.val 0) 0 (P.w - 1) := by
    intro id hid
    have htop1 : ∀ ch : Fin P.lsf, (leafDet id).2.1[ch.val] =
        WotsC.chain pr pk id ch.val (β id ch.val (Hyb.relDig pr pk (digOf pr ys) id ch.val))
          (Hyb.relDig pr pk (digOf pr ys) id ch.val)
          (P.w - 1 - Hyb.relDig pr pk (digOf pr ys) id ch.val) := by
      intro ch
      have ha_lt : Hyb.relDig pr pk (digOf pr ys) id ch.val < P.w := Hyb.relDigOf_lt _ _
      have hst_le : startFn id ch ≤ Hyb.relDig pr pk (digOf pr ys) id ch.val := by
        rw [hstart_anchor id hid ch]; exact hstart _ ha_lt
      have h1 := (chainRecDet_spec pr pk id ch.val (startFn id ch) (xFn id ch)
        (P.w - 1 - startFn id ch)).1
      have h2 := (chainRecDet_spec pr pk id ch.val (startFn id ch) (xFn id ch)
        (P.w - 1 - startFn id ch)).2 (P.w - 1) (by omega) (by omega)
      have h3 := hchain_eq id hid ch (P.w - 1) (by omega) (by have := P.w_pos; omega)
      simpa [leafDet, leafRecDet, ← h2, h1] using h3
    cases hg : WotsC.grind pr pk id (digOf pr ys id) with
    | none =>
      apply Vector.ext; intro i hi
      have := htop1 ⟨i, hi⟩
      simpa [Hyb.relDig, hg, Hyb.relDigOf] using this
    | some dc =>
      obtain ⟨d, c⟩ := dc
      apply Vector.ext; intro i hi
      have := htop1 ⟨i, hi⟩
      simpa [WotsC.topsFromSig, blockSig, Hyb.relDig, hg, Hyb.relDigOf] using this
  have hleaf_eq : ∀ id ∈ leafIds P.hsf S, (leafDet id).2.2 = H.leafVal id := by
    intro id hid
    have ht := htops_eq id hid
    simp only [H, hon]
    change pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs (leafDet id).2.1 = _
    rw [ht]
    cases WotsC.grind pr pk id (digOf pr ys id) <;> rfl
  have htree_congr : ∀ z i, Tree.treeNode P.hsf S (fun id => (leafDet id).2.2)
      (Scheme.Fxmss.node pr pk) z i = H.value z i :=
    Hyb.treeNode_congr (Scheme.Fxmss.node pr pk) hleaf_eq
  have hnodeEq : ∀ z i, z ≤ P.hsf → (⟨P.hsf - z, i⟩ : Node) ∈ S.nodes →
      st.nodeVal z i = H.value z i := by
    intro z i hz hmem
    change st.nodeVal z i = Tree.treeNode P.hsf S H.leafVal (Scheme.Fxmss.node pr pk) z i
    rcases Structure.mem_nodes.1 hmem with hA | hI
    · have hid : (⟨z, i⟩ : LeafId) ∈ leafIds P.hsf S :=
        Finset.mem_image.2 ⟨⟨P.hsf - z, i⟩, hA, by simp [Node.toLeafId, Nat.sub_sub_self hz]⟩
      rw [(hspec.1 ⟨z, i⟩ (hvisitA _ hid)).2.2.2, hleaf_eq _ hid, Tree.treeNode_anchor hz hA]
    · have h1 : 1 ≤ z := by have hlt := hS.internal_depth_lt hI; dsimp at hlt; omega
      have hv := hspec.2.1 ⟨z, i⟩ (visit_mem_treeOrder hS (e := .inr ⟨z, i⟩) ⟨h1, hz, hI⟩)
      rw [hv, htree_congr]
      rfl
  have hpkSf : (st.nodeVal P.hsf 0).getD default = H.pkSf := by
    simp only [Honest.pkSf,
      hnodeEq P.hsf 0 le_rfl (by simpa [Node.root] using Structure.internal_subset_nodes hS.root_mem)]
  change SfTableAgree pr H (assembleSfTable pr gfLeaf st xFn)
  refine ⟨hpkSf, ?_, ?_, ?_, ?_, ?_, ?_, hnodeEq⟩
  · -- sig
    intro id hid
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr ys id)
    have hHgrind : WotsC.grind pr H.pk id (H.dig id) =
        some (WotsC.encode pr pk id (digOf pr ys id) c, c) := hg
    simp only [assembleSfTable, hgf_anchor id hid, Honest.sig, hg, hHgrind, Option.bind_some]
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
    have hle := hS.anchor_depth_le v hv
    have hmem : (⟨P.hsf - (v.toLeafId P.hsf).height, (v.toLeafId P.hsf).index⟩ : Node) ∈ S.nodes := by
      have : (⟨P.hsf - (v.toLeafId P.hsf).height, (v.toLeafId P.hsf).index⟩ : Node) = v := by
        simp [Node.toLeafId, Nat.sub_sub_self hle]
      rw [this]; exact Structure.anchors_subset_nodes hv
    have hauth : authPathFromTable st.nodeVal (v.toLeafId P.hsf).height (v.toLeafId P.hsf).index
          (P.hsf - (v.toLeafId P.hsf).height) =
        Tree.authPath P.hsf S H.leafVal (Scheme.Fxmss.node pr pk) (v.toLeafId P.hsf).height
          (v.toLeafId P.hsf).index (P.hsf - (v.toLeafId P.hsf).height) :=
      authPathFromTable_eq hS hnodeEq (P.hsf - (v.toLeafId P.hsf).height)
        (v.toLeafId P.hsf).height (v.toLeafId P.hsf).index
        (by simp [Node.toLeafId]) hmem
    rw [hauth]
    refine congrArg (Option.map · _) (funext fun auth => congrArg (Scheme.Fxmss.Sig.mk · auth) ?_)
    change _ = (hon pr S pk (digOf pr ys) β).wots (v.toLeafId P.hsf)
    rw [Hyb.hon_wots_of_grind hg]; unfold blockSig; congr 1
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn]
    rw [(hspec.1 _ (hvisitA _ hid)).1]
    have ha_eq : Hyb.relDig pr pk (digOf pr ys) (v.toLeafId P.hsf) i =
        WotsC.digit pr (WotsC.encode pr pk (v.toLeafId P.hsf) (digOf pr ys (v.toLeafId P.hsf)) c) i := by
      simp [Hyb.relDig, hg, Hyb.relDigOf]
    have hc := hchain_eq (v.toLeafId P.hsf) hid ⟨i, hi⟩
      (WotsC.digit pr (WotsC.encode pr pk (v.toLeafId P.hsf) (digOf pr ys (v.toLeafId P.hsf)) c) i)
      (by rw [ha_eq]) (WotsC.digit_lt pr _ i)
    simpa [ha_eq, WotsC.chain] using hc
  · -- encoded
    intro id hid
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr ys id)
    dsimp only [assembleSfTable]
    rw [hgf_anchor id hid, hg]
    exact (Hyb.hon_encoded_of_grind hg).symm
  · -- block
    intro id hid ch
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr ys id)
    dsimp only [assembleSfTable]
    rw [hgf_anchor id hid, hg]
    change st.chainVal id ch (WotsC.digit pr _ ch.val) =
      (hon pr S pk (digOf pr ys) β).block id ch
    rw [(hspec.1 id (hvisitA id hid)).1, Hyb.hon_block_of_grind hg ch]
    have ha_eq : Hyb.relDig pr pk (digOf pr ys) id ch.val =
        WotsC.digit pr (WotsC.encode pr pk id (digOf pr ys id) c) ch.val := by
      simp [Hyb.relDig, hg, Hyb.relDigOf]
    have hc := hchain_eq id hid ch
      (WotsC.digit pr (WotsC.encode pr pk id (digOf pr ys id) c) ch.val)
      (by rw [ha_eq]) (WotsC.digit_lt pr _ ch.val)
    simpa [ha_eq, WotsC.chain] using hc
  · -- chainVal
    intro id hid ch p hp1 hp2
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr ys id)
    simp only [assembleSfTable]
    rw [(hspec.1 id (hvisitA id hid)).1]
    have henc := Hyb.hon_encoded_of_grind (S := S) (β := β) hg
    have hblk := Hyb.hon_block_of_grind (S := S) (β := β) hg ch
    have ha_eq : Hyb.relDig pr pk (digOf pr ys) id ch.val =
        WotsC.digit pr (WotsC.encode pr pk id (digOf pr ys id) c) ch.val := by
      simp [Hyb.relDig, hg, Hyb.relDigOf]
    change (leafDet id).1 ch p = (hon pr S pk (digOf pr ys) β).chainValue id ch p
    rw [henc] at hp1
    have hc := hchain_eq id hid ch p (by rw [ha_eq]; exact hp1) hp2
    rw [Honest.chainValue, henc, hblk]
    change (leafDet id).1 ch p = WotsC.chain pr pk id ch.val (β id ch.val _) _ _
    simpa [ha_eq] using hc
  · -- tops
    intro id hid
    obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr ys id)
    simp only [assembleSfTable]
    rw [(hspec.1 id (hvisitA id hid)).2.1, htops_eq id hid, hg]
    change WotsC.topsFromSig pr pk id _ (blockSig pr β id _ c) =
      (hon pr S pk (digOf pr ys) β).tops id
    rw [Honest.tops, Hyb.hon_encoded_of_grind hg, Hyb.hon_wots_of_grind hg]
    rfl
  · -- leafVal
    intro id hid
    simp only [assembleSfTable]
    rw [(hspec.1 id (hvisitA id hid)).2.2.1, hleaf_eq id hid]

end LogSemantics

end Stage1Builders

end ShrincsSecurity.Complexity

end
