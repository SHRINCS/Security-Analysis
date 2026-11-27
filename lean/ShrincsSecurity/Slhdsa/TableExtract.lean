module

public import ShrincsSecurity.Slhdsa.Bridge
public import ShrincsSecurity.Scheme.VerifyCount

/-!
# Table-driven `≤ V_sl` Stage-2 verification and witness extraction

This module eliminates Stage-2 honest-tree recomputation in SLH-DSA reductions (Main Paper
Theorem 4.3 and Claim 4.16) by performing a **single explicit-`Th_λ`-oracle verification pass**
(`verifyAndExtractTableM`) over a candidate forgery `(msg, sig)` and extracting every FORS,
XMSS, and WOTS+ witness purely from the recorded pass traces and the Stage-1 precomputed table
`tbl : Adrs → Option pr.Y` (at **zero** additional `Th_λ` cost):

* `ThQuery`, `thSpec`, `thRealImpl`: explicit tweakable-hash oracle specification for all
  members of `Th_λ` (`Primitives.Member`).
* `Vsl P := P.k * (P.a + 1) + 1 + P.d * (VerifyCount.wotsSmax P + P.hp + 1)` (`2741` at SHRINCS).
* `verifyAndExtractTableM`: explicit-`thSpec`-oracle pass returning `(verified, witness)` with:
  1. `verifyAndExtractTableM_queryBound`: at most `Vsl vp.params` `Th_λ` queries on every path;
  2. `verifyAndExtractTable_fst`: the Boolean output equals
     `SLHDSA.GeneralScheme.verifyInternal` identically;
  3. `verifyAndExtractTable_sound` and `verifyAndExtractTable_isSome`: under
     `TblComplete pr pk u tbl`, every returned witness satisfies `Witness.Valid` and every
     verifying forgery (under `Function.Injective pr.yToBytes`) produces a witness.
* `wotsPreFromTrace`: pure 0-query WOTS+ `F`-preimage scanner on a recorded chain trace, used by
  keyless `WotsHybrid.findHybWotsPre` so `B_ud` and `B_pre` also use `≤ Vsl vp.params` `Th_λ`
  queries in Stage 2.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Slhdsa

open Scheme Shrincs SLHDSA.Security
open SLHDSA (Adrs AddrType Byte Bytes wotsSkAdrs wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsSkAdrs forsNodeAdrs forsPkAdrs chain chainStepsCore chainStepsCore_le
  chain_zero chain_succ chain_compose wotsPkGen wotsPkGenTops wotsSign wotsSign_eq_ofFn
  wotsPkGenTops_eq_ofFn wotsPkFromSig wotsPkFromSigTops wotsPkFromSigTops_eq_ofFn
  wotsPkFromSig_eq_tl forsLeaf forsNodeHash forsPkGen forsPkFromSig xmssLeaf xmssNode
  xmssRoot xmssPkFromSig LayerPosition DigestParts splitDigest)

/-! ## 1. Explicit `Th_λ` oracle specification and `Vsl` constant -/

/-- A single evaluation query to the tweakable-hash collection `Th_λ`. -/
abbrev ThQuery {P : Params} (pr : Primitives P) : Type :=
  (i : Primitives.Member) × Adrs × pr.MemberMsg i

/-- Explicit oracle specification for evaluating any member of `Th_λ`. -/
@[reducible] def thSpec {P : Params} (pr : Primitives P) : OracleSpec (ThQuery pr) :=
  fun _ => pr.Y

/-- Deterministic interpretation of `thSpec` by `pr.memberEval` under `pk`. -/
def thRealImpl {P : Params} (pr : Primitives P) (pk : pr.PkSeed) : QueryImpl (thSpec pr) Id :=
  fun q => pr.memberEval q.1 pk q.2.1 q.2.2

/-- Lemma 5.1 stateless verification tweakable-hash budget `V_sl` (`2741` at SHRINCS). -/
def Vsl (P : Params) : ℕ :=
  P.k * (P.a + 1) + 1 + P.d * (VerifyCount.wotsSmax P + P.hp + 1)

/-- Query helper lifting a `thSpec` query into `OracleComp (thSpec pr)`. -/
def thQuery {P : Params} (pr : Primitives P) (q : ThQuery pr) : OracleComp (thSpec pr) pr.Y :=
  liftM ((thSpec pr).query q)

theorem isTotalQueryBound_thQuery {P : Params} (pr : Primitives P) (q : ThQuery pr) :
    IsTotalQueryBound (thQuery pr q) 1 := by
  unfold thQuery
  exact (isQueryBoundP_true_iff _ _).1
    ((isQueryBoundP_query_iff (fun _ => True) q 1).2 fun _ => Nat.zero_lt_one)

private theorem isTotalQueryBound_pure' {ι α : Type} {spec : OracleSpec ι} (a : α) :
    IsTotalQueryBound (pure a : OracleComp spec α) 0 := trivial

private theorem list_find?_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.find?_cons, h a (by simp)]
    cases q a
    · exact ih fun x hx => h x (by simp [hx])
    · rfl

/-- Query-bound helper for `Vector.ofFnM` under `IsTotalQueryBound`. -/
theorem isTotalQueryBound_ofFnM {ι α : Type} {spec : OracleSpec ι} :
    ∀ {k : ℕ} (g : Fin k → OracleComp spec α) (budget : Fin k → ℕ),
      (∀ i, IsTotalQueryBound (g i) (budget i)) →
      IsTotalQueryBound (Vector.ofFnM g) (∑ i, budget i)
  | 0, _, _, _ => by
    rw [Vector.ofFnM_zero, Finset.univ_eq_empty, Finset.sum_empty]
    exact isTotalQueryBound_pure' _
  | k + 1, g, budget, h => by
    rw [Vector.ofFnM_succ, Fin.sum_univ_castSucc]
    refine isTotalQueryBound_bind
      (isTotalQueryBound_ofFnM (fun i => g i.castSucc) (fun i => budget i.castSucc)
        (fun i => h i.castSucc)) fun xs => ?_
    refine (isTotalQueryBound_bind (n₂ := 0) (h (Fin.last k)) fun a =>
      isTotalQueryBound_pure' (xs.push a)).mono (by omega)

/-! ## 2. FORS witness extractor (exposed) -/

section ForsExposed

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Exposed FORS per-tree collision finder (mirroring `SLHDSA.Security.findForsTreeCollision`). -/
noncomputable def slFindForsTreeCollision [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (i : Fin vp.sl.params.k) :
    Option (ForsWitness vp.sl.params (prEager pr)) :=
  let idx := forsSigLeafIndex vp.sl.params md i.val
  let y := (prEager pr).F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
  if forsLeaf (prEager pr) u pk adrs idx = y then none
  else
    (PerfectMerkleTree.findCollision (forsLeaf (prEager pr) u pk adrs)
      (forsNodeHash (prEager pr) pk adrs) idx y (sig[i.val]).auth.toList).map
      fun w => .hCollision i w.1 w.2.2

/-- Exposed FORS witness extractor (mirroring `SLHDSA.Security.findForsWitness`): depends on `u`
only through `forsHonestRoots` and `forsLeaf`, and honors `target` on the `.fPreimage` arm. -/
noncomputable def slFindForsWitness [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (target : Fin vp.sl.params.k) :
    ForsWitness vp.sl.params (prEager pr) :=
  if forsRecoveredRoots (prEager pr) sig md pk adrs = forsHonestRoots (prEager pr) u pk adrs then
    ((List.finRange vp.sl.params.k).findSome?
      (slFindForsTreeCollision pr sig md u pk adrs)).getD
      (.fPreimage target (sig[target.val]).sk)
  else .tlCollision (forsRecoveredRoots (prEager pr) sig md pk adrs)

theorem slForsRecoveredRoot_climb
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (i : Fin vp.sl.params.k)
    (hroot : (forsRecoveredRoots (prEager pr) sig md pk adrs)[i.val] =
      (forsHonestRoots (prEager pr) u pk adrs)[i.val]) :
    PerfectMerkleTree.climb (forsNodeHash (prEager pr) pk adrs)
        (forsSigLeafIndex vp.sl.params md i.val)
        ((prEager pr).F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex vp.sl.params md i.val)) (sig[i.val]).sk)
        (sig[i.val]).auth.toList =
      PerfectMerkleTree.merkleRoot (forsLeaf (prEager pr) u pk adrs)
        (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
        (forsSigLeafIndex vp.sl.params md i.val / 2 ^ vp.sl.params.a) := by
  rw [forsSigLeafIndex_div_pow_a vp.sl.params md i.val]
  rw [forsRecoveredRoots_getElem, forsHonestRoots_getElem, SLHDSA.forsRoot_eq_merkleRoot] at hroot
  exact hroot

theorem slFindForsTreeCollision_sound [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (i : Fin vp.sl.params.k)
    (hroot : (forsRecoveredRoots (prEager pr) sig md pk adrs)[i.val] =
      (forsHonestRoots (prEager pr) u pk adrs)[i.val])
    {w : ForsWitness vp.sl.params (prEager pr)}
    (hw : slFindForsTreeCollision pr sig md u pk adrs i = some w) :
    w.Valid u pk adrs md := by
  unfold slFindForsTreeCollision at hw
  dsimp only at hw
  split at hw
  · exact absurd hw (by simp)
  · rename_i hleaf
    rw [Option.map_eq_some_iff] at hw
    obtain ⟨u', hu', rfl⟩ := hw
    have hlen : (sig[i.val]).auth.toList.length = vp.sl.params.a := by simp
    have hclimb := slForsRecoveredRoot_climb pr sig md u pk adrs i hroot
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (forsLeaf (prEager pr) u pk adrs) (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
      (forsSigLeafIndex vp.sl.params md i.val) _ _ hlen hclimb hleaf
    rw [hor, Option.some.injEq] at hu'
    subst hu'
    obtain ⟨hzpos, hzle, hne, hcoll⟩ := PerfectMerkleTree.findCollision_sound
      (forsLeaf (prEager pr) u pk adrs) (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
      (forsSigLeafIndex vp.sl.params md i.val) _ _ hlen z _ c hor
    rw [ForsWitness.valid_hCollision]
    refine ⟨hzpos, hzle, ?_, ?_⟩
    · rw [forsHonestChildren_eq]; exact hne
    · rw [forsHonestChildren_eq]
      simpa only [SLHDSA.forsNodeHash_eq_h, PerfectMerkleTree.honestChildren] using hcoll

theorem slFindForsWitness_sound [DecidableEq pr.Y]
    (sig : SLHDSA.ForsSigCore vp.sl.params (prEager pr).core) (md : List Byte)
    (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (adrs : Adrs) (target : Fin vp.sl.params.k)
    (hpk : forsPkFromSig (prEager pr) sig md pk adrs = forsPkGen (prEager pr) u pk adrs) :
    (slFindForsWitness pr sig md u pk adrs target).Valid u pk adrs md := by
  unfold slFindForsWitness
  split
  · rename_i hroots
    rcases hfind : (List.finRange vp.sl.params.k).findSome?
        (slFindForsTreeCollision pr sig md u pk adrs) with _ | w
    · rw [Option.getD_none, ForsWitness.valid_fPreimage]
      rw [List.findSome?_eq_none_iff] at hfind
      have hnone := hfind target (List.mem_finRange target)
      have hleaf : forsLeaf (prEager pr) u pk adrs (forsSigLeafIndex vp.sl.params md target.val) =
          (prEager pr).F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex vp.sl.params md target.val))
            (sig[target.val]).sk := by
        by_contra hne
        have hlen : (sig[target.val]).auth.toList.length = vp.sl.params.a := by simp
        have hclimb := slForsRecoveredRoot_climb pr sig md u pk adrs target (by rw [hroots])
        obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
          (forsLeaf (prEager pr) u pk adrs) (forsNodeHash (prEager pr) pk adrs) vp.sl.params.a
          (forsSigLeafIndex vp.sl.params md target.val) _ _ hlen hclimb hne
        unfold slFindForsTreeCollision at hnone
        simp only [hne, ite_false, hor, Option.map_some] at hnone
        cases hnone
      exact forsLeafPreimage (prEager pr) u pk adrs _ _ hleaf
    · rw [Option.getD_some]
      obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hfind
      exact slFindForsTreeCollision_sound pr sig md u pk adrs i (by rw [hroots]) hi
  · rename_i hroots
    rw [ForsWitness.valid_tlCollision]
    exact ⟨hroots, forsRootsBinding (prEager pr) sig md u pk adrs hpk⟩

end ForsExposed

/-! ## 3. Single-pass Merkle climb trace and 0-query collision extraction -/

section MerkleTrace

variable {P : Params} (pr : Primitives P)

/-- Bottom-up Merkle climb accumulating a top-down trace of `(height, childPair, parent)` triples. -/
def merkleClimbTraceAuxM (adrsFn : ℕ → ℕ → Adrs) (idx : ℕ) :
    ℕ → pr.Y → List pr.Y → List (ℕ × (pr.Y × pr.Y) × pr.Y) →
    OracleComp (thSpec pr) (pr.Y × List (ℕ × (pr.Y × pr.Y) × pr.Y))
  | _, cur, [], acc => pure (cur, acc)
  | h, cur, s :: rest, acc => do
    let pair := if (idx / 2 ^ h) % 2 = 0 then (cur, s) else (s, cur)
    let parent ← thQuery pr ⟨.H, adrsFn (h + 1) (idx / 2 ^ (h + 1)), pair⟩
    merkleClimbTraceAuxM adrsFn idx (h + 1) parent rest ((h + 1, pair, parent) :: acc)

/-- Single-pass explicit-oracle Merkle climb returning `(root, topDownTrace)`. -/
def merkleClimbTraceM (adrsFn : ℕ → ℕ → Adrs) (idx : ℕ) (leafVal : pr.Y) (auth : List pr.Y) :
    OracleComp (thSpec pr) (pr.Y × List (ℕ × (pr.Y × pr.Y) × pr.Y)) :=
  merkleClimbTraceAuxM pr adrsFn idx 0 leafVal auth []

theorem merkleClimbTraceAuxM_queryBound (adrsFn : ℕ → ℕ → Adrs) (idx : ℕ) :
    ∀ (h : ℕ) (cur : pr.Y) (auth : List pr.Y) (acc : List (ℕ × (pr.Y × pr.Y) × pr.Y)),
      IsTotalQueryBound (merkleClimbTraceAuxM pr adrsFn idx h cur auth acc) auth.length
  | _, _, [], _ => isTotalQueryBound_pure' _
  | h, cur, s :: rest, acc => by
    simp only [merkleClimbTraceAuxM, List.length_cons]
    refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := rest.length)
      (isTotalQueryBound_thQuery pr _) fun parent =>
        merkleClimbTraceAuxM_queryBound adrsFn idx (h + 1) parent rest _).mono (by omega)

theorem merkleClimbTraceM_queryBound (adrsFn : ℕ → ℕ → Adrs) (idx : ℕ)
    (leafVal : pr.Y) (auth : List pr.Y) :
    IsTotalQueryBound (merkleClimbTraceM pr adrsFn idx leafVal auth) auth.length :=
  merkleClimbTraceAuxM_queryBound pr adrsFn idx 0 leafVal auth []

/-- Pure 0-query top-down Merkle collision scan matching `PerfectMerkleTree.findCollision`. -/
def merkleFindCollisionFromTrace [DecidableEq pr.Y] (honestNode : ℕ → ℕ → pr.Y) (idx : ℕ) :
    List (ℕ × (pr.Y × pr.Y) × pr.Y) → Option (ℕ × (pr.Y × pr.Y) × (pr.Y × pr.Y))
  | [] => none
  | (h, pair, parent) :: rest =>
    let t := idx / 2 ^ h
    let hPair := (honestNode (h - 1) (2 * t), honestNode (h - 1) (2 * t + 1))
    if hPair = pair then
      merkleFindCollisionFromTrace honestNode idx rest
    else if honestNode h t = parent then
      some (h, hPair, pair)
    else
      none

private theorem simulateQ_thQuery (pk : pr.PkSeed) (q : ThQuery pr) :
    Id.run (simulateQ (thRealImpl pr pk) (thQuery pr q)) = pr.memberEval q.1 pk q.2.1 q.2.2 := by
  unfold thQuery
  rw [simulateQ_spec_query]
  rfl

private theorem simulateQ_merkleClimbTraceAuxM_append (pk : pr.PkSeed) (adrsFn : ℕ → ℕ → Adrs)
    (idx : ℕ) :
    ∀ (h : ℕ) (cur : pr.Y) (auth₁ auth₂ : List pr.Y) (acc : List (ℕ × (pr.Y × pr.Y) × pr.Y)),
      Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceAuxM pr adrsFn idx h cur (auth₁ ++ auth₂) acc)) =
        let r₁ := Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceAuxM pr adrsFn idx h cur auth₁ acc))
        Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceAuxM pr adrsFn idx (h + auth₁.length) r₁.1 auth₂ r₁.2))
  | h, cur, [], auth₂, acc => by
    simp [merkleClimbTraceAuxM]
  | h, cur, s :: rest, auth₂, acc => by
    simp only [List.cons_append, merkleClimbTraceAuxM, simulateQ_bind, Id.run_bind,
      simulateQ_thQuery, List.length_cons]
    have hadd : h + (rest.length + 1) = h + 1 + rest.length := by omega
    rw [hadd]
    exact simulateQ_merkleClimbTraceAuxM_append pk adrsFn idx (h + 1)
      (pr.memberEval .H pk (adrsFn (h + 1) (idx / 2 ^ (h + 1)))
        (if (idx / 2 ^ h) % 2 = 0 then (cur, s) else (s, cur)))
      rest auth₂
      ((h + 1, if (idx / 2 ^ h) % 2 = 0 then (cur, s) else (s, cur),
        pr.memberEval .H pk (adrsFn (h + 1) (idx / 2 ^ (h + 1)))
          (if (idx / 2 ^ h) % 2 = 0 then (cur, s) else (s, cur))) :: acc)

private theorem getPutativeRoot_of_eq {s : BinaryTree.Skeleton}
    (nh : BinaryTree.SkeletonInternalIndex s → pr.Y → pr.Y → pr.Y)
    {i₁ i₂ : BinaryTree.SkeletonLeafIndex s} (hi : i₁ = i₂) (y : pr.Y)
    (v₁ : List.Vector pr.Y i₁.depth) (v₂ : List.Vector pr.Y i₂.depth)
    (hv : v₁.toList = v₂.toList) :
    AddressedMerkleTree.getPutativeRootAddressedWithHash nh i₁ y v₁ =
    AddressedMerkleTree.getPutativeRootAddressedWithHash nh i₂ y v₂ := by
  subst hi; congr 1; exact Subtype.ext hv

private theorem findCollisionAddressed_of_eq [DecidableEq pr.Y] {s : BinaryTree.Skeleton}
    (nh : BinaryTree.SkeletonInternalIndex s → pr.Y → pr.Y → pr.Y)
    (t : BinaryTree.FullData pr.Y s)
    {i₁ i₂ : BinaryTree.SkeletonLeafIndex s} (hi : i₁ = i₂) (x y : pr.Y)
    (v₁ : List.Vector pr.Y i₁.depth) (v₂ : List.Vector pr.Y i₂.depth)
    (hv : v₁.toList = v₂.toList) :
    AddressedMerkleTree.findCollisionAddressed nh i₁ (InductiveMerkleTree.generateProof t i₁) v₁ x y =
    AddressedMerkleTree.findCollisionAddressed nh i₂ (InductiveMerkleTree.generateProof t i₂) v₂ x y := by
  subst hi; congr 1; exact Subtype.ext hv

private theorem perfect_climb_append_singleton (nodeHash : ℕ → ℕ → pr.Y → pr.Y → pr.Y)
    (idx : ℕ) (y : pr.Y) (auth : List pr.Y) (s : pr.Y) :
    PerfectMerkleTree.climb nodeHash idx y (auth ++ [s]) =
      let sub := PerfectMerkleTree.climb nodeHash idx y auth
      if (idx / 2 ^ auth.length) % 2 = 0 then
        nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) sub s
      else
        nodeHash (auth.length + 1) (idx / 2 ^ (auth.length + 1)) s sub := by
  set z := auth.length
  rw [PerfectMerkleTree.climb_eq nodeHash idx y (auth ++ [s]) (z := z + 1) (by simp [z])]
  rw [PerfectMerkleTree.climb_eq nodeHash idx y auth (z := z) rfl]
  have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
  by_cases hpar : idx / 2 ^ z % 2 = 0
  · have h2 : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
    have hnh : (fun a => PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) (.ofLeft a)) =
        PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z) := by
      funext a
      simp [PerfectMerkleTree.nodeHashAt, BinaryTree.SkeletonInternalIndex.natAddr, h2]
    have hof : BinaryTree.SkeletonLeafIndex.ofNat (z + 1) idx =
        .ofLeft (BinaryTree.SkeletonLeafIndex.ofNat z idx) := by
      simp [BinaryTree.SkeletonLeafIndex.ofNat, hpar]
    rw [ite_eq_left hpar]
    refine (getPutativeRoot_of_eq pr _ hof y _ (List.Vector.cons s ⟨auth.reverse, by simp [z]⟩) (by simp [List.reverse_append]; rfl)).trans ?_
    simp only [AddressedMerkleTree.getPutativeRootAddressedWithHash, hnh]
    rfl
  · have h2 : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by omega
    have hnh : (fun a => PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) (.ofRight a)) =
        PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z) := by
      funext a
      simp [PerfectMerkleTree.nodeHashAt, BinaryTree.SkeletonInternalIndex.natAddr, h2]
    have hof : BinaryTree.SkeletonLeafIndex.ofNat (z + 1) idx =
        .ofRight (BinaryTree.SkeletonLeafIndex.ofNat z idx) := by
      simp [BinaryTree.SkeletonLeafIndex.ofNat, hpar]
    rw [ite_eq_right hpar]
    refine (getPutativeRoot_of_eq pr _ hof y _ (List.Vector.cons s ⟨auth.reverse, by simp [z]⟩) (by simp [List.reverse_append]; rfl)).trans ?_
    simp only [AddressedMerkleTree.getPutativeRootAddressedWithHash, hnh]
    rfl

/-- `merkleClimbTraceM` computes the exact `PerfectMerkleTree.climb` root. -/
theorem simulateQ_merkleClimbTraceM_fst (pk : pr.PkSeed) (adrsFn : ℕ → ℕ → Adrs)
    (idx : ℕ) (leafVal : pr.Y) (auth : List pr.Y) :
    (Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr adrsFn idx leafVal auth))).1 =
      PerfectMerkleTree.climb (fun h t l r => pr.H pk (adrsFn h t) l r) idx leafVal auth := by
  induction auth using List.reverseRecOn with
  | nil =>
    simp [merkleClimbTraceM, merkleClimbTraceAuxM, PerfectMerkleTree.climb,
      BinaryTree.SkeletonLeafIndex.ofNat]
  | append_singleton auth s ih =>
    unfold merkleClimbTraceM at ih ⊢
    rw [simulateQ_merkleClimbTraceAuxM_append]
    simp only [Nat.zero_add, merkleClimbTraceAuxM, simulateQ_bind, Id.run_bind,
      simulateQ_thQuery, simulateQ_pure, Id.run_pure, Primitives.memberEval, ih]
    rw [perfect_climb_append_singleton]
    split_ifs <;> rfl

/-- Exact equality between `merkleFindCollisionFromTrace` on the recorded climb trace and
VCVio's `PerfectMerkleTree.findCollision`, whenever `honestNode` matches `merkleRoot` on the
ancestors and children along `idx`. -/
theorem merkleFindCollisionFromTrace_eq_findCollision [DecidableEq pr.Y]
    (pk : pr.PkSeed) (adrsFn : ℕ → ℕ → Adrs) (leaf : ℕ → pr.Y)
    (honestNode : ℕ → ℕ → pr.Y) (idx : ℕ) (leafVal : pr.Y) (auth : List pr.Y)
    (hhon : ∀ h, 0 < h → h ≤ auth.length →
      honestNode h (idx / 2 ^ h) =
        PerfectMerkleTree.merkleRoot leaf (fun z t l r => pr.H pk (adrsFn z t) l r) h (idx / 2 ^ h) ∧
      honestNode (h - 1) (2 * (idx / 2 ^ h)) =
        PerfectMerkleTree.merkleRoot leaf (fun z t l r => pr.H pk (adrsFn z t) l r) (h - 1) (2 * (idx / 2 ^ h)) ∧
      honestNode (h - 1) (2 * (idx / 2 ^ h) + 1) =
        PerfectMerkleTree.merkleRoot leaf (fun z t l r => pr.H pk (adrsFn z t) l r) (h - 1) (2 * (idx / 2 ^ h) + 1)) :
    merkleFindCollisionFromTrace pr honestNode idx
        (Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr adrsFn idx leafVal auth))).2 =
      PerfectMerkleTree.findCollision leaf (fun z t l r => pr.H pk (adrsFn z t) l r) idx leafVal auth := by
  set nodeHash : ℕ → ℕ → pr.Y → pr.Y → pr.Y := fun z t l r => pr.H pk (adrsFn z t) l r
  induction auth using List.reverseRecOn with
  | nil =>
    simp [merkleClimbTraceM, merkleClimbTraceAuxM, merkleFindCollisionFromTrace,
      PerfectMerkleTree.findCollision, PerfectMerkleTree.findCollisionBetween,
      BinaryTree.SkeletonLeafIndex.ofNat, AddressedMerkleTree.findCollisionAddressed]
  | append_singleton auth s ih =>
    set z := auth.length
    have hhon_init : ∀ h, 0 < h → h ≤ z →
        honestNode h (idx / 2 ^ h) = PerfectMerkleTree.merkleRoot leaf nodeHash h (idx / 2 ^ h) ∧
        honestNode (h - 1) (2 * (idx / 2 ^ h)) =
          PerfectMerkleTree.merkleRoot leaf nodeHash (h - 1) (2 * (idx / 2 ^ h)) ∧
        honestNode (h - 1) (2 * (idx / 2 ^ h) + 1) =
          PerfectMerkleTree.merkleRoot leaf nodeHash (h - 1) (2 * (idx / 2 ^ h) + 1) :=
      fun h hp hle => hhon h hp (by simp; omega)
    have ih' := ih hhon_init
    have htop := hhon (z + 1) (Nat.succ_pos z) (by simp [z])
    simp only [Nat.add_sub_cancel] at htop
    have htrace : (Id.run (simulateQ (thRealImpl pr pk)
          (merkleClimbTraceM pr adrsFn idx leafVal (auth ++ [s])))).2 =
        let sub := PerfectMerkleTree.climb nodeHash idx leafVal auth
        let pair := if (idx / 2 ^ z) % 2 = 0 then (sub, s) else (s, sub)
        let parent := nodeHash (z + 1) (idx / 2 ^ (z + 1)) pair.1 pair.2
        (z + 1, pair, parent) ::
          (Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr adrsFn idx leafVal auth))).2 := by
      have hfst := simulateQ_merkleClimbTraceM_fst pr pk adrsFn idx leafVal auth
      unfold merkleClimbTraceM at hfst ⊢
      rw [simulateQ_merkleClimbTraceAuxM_append]
      simp only [Nat.zero_add, merkleClimbTraceAuxM, simulateQ_bind, Id.run_bind,
        simulateQ_thQuery, simulateQ_pure, Id.run_pure, Primitives.memberEval, hfst, z]
      split_ifs <;> rfl
    rw [htrace]
    dsimp only [merkleFindCollisionFromTrace]
    simp only [Nat.add_sub_cancel, htop.1, htop.2.1, htop.2.2]
    rw [PerfectMerkleTree.findCollision_eq leaf nodeHash idx leafVal (auth ++ [s]) (z := z + 1) (by simp [z])]
    rw [PerfectMerkleTree.findCollision_eq leaf nodeHash idx leafVal auth (z := z) rfl] at ih'
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hdm := Nat.div_add_mod (idx / 2 ^ z) 2
    by_cases hpar : idx / 2 ^ z % 2 = 0
    · have h2 : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
      have hnh : (fun a => PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) (.ofLeft a)) =
          PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z) := by
        funext a
        simp [PerfectMerkleTree.nodeHashAt, BinaryTree.SkeletonInternalIndex.natAddr, h2]
      have hcomp : AddressedMerkleTree.getPutativeRootAddressedWithHash
          (PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z))
          (BinaryTree.SkeletonLeafIndex.ofNat z idx) (leaf idx)
          (InductiveMerkleTree.generateProof (PerfectMerkleTree.tree leaf nodeHash z (idx / 2 ^ z))
            (BinaryTree.SkeletonLeafIndex.ofNat z idx)) =
          PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))) := by
        rw [← PerfectMerkleTree.leafData_get_ofNat leaf z idx, h2]
        exact AddressedMerkleTree.addressed_functional_completeness _ _ _
      have hsub2 : AddressedMerkleTree.getPutativeRootAddressedWithHash
          (PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z))
          (BinaryTree.SkeletonLeafIndex.ofNat z idx) leafVal ⟨auth.reverse, by simp [z]⟩ =
          PerfectMerkleTree.climb nodeHash idx leafVal auth :=
        (PerfectMerkleTree.climb_eq nodeHash idx leafVal auth (z := z) rfl).symm
      have hof : BinaryTree.SkeletonLeafIndex.ofNat (z + 1) idx =
          .ofLeft (BinaryTree.SkeletonLeafIndex.ofNat z idx) := by
        simp [BinaryTree.SkeletonLeafIndex.ofNat, hpar]
      let vTail : List.Vector pr.Y (BinaryTree.SkeletonLeafIndex.ofNat z idx).depth :=
        ⟨auth.reverse, by simp [z]⟩
      have hsub2' : AddressedMerkleTree.getPutativeRootAddressedWithHash
          (PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z))
          (BinaryTree.SkeletonLeafIndex.ofNat z idx) leafVal vTail =
          PerfectMerkleTree.climb nodeHash idx leafVal auth := hsub2
      have hhd : (List.Vector.cons s vTail).head = s := rfl
      have htl : (List.Vector.cons s vTail).tail = vTail := rfl
      rw [ite_eq_left hpar]
      have hfc := findCollisionAddressed_of_eq pr
        (PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)))
        (PerfectMerkleTree.tree leaf nodeHash (z + 1) (idx / 2 ^ (z + 1))) hof (leaf idx) leafVal
        (⟨(auth ++ [s]).reverse, by simp [z]⟩ : List.Vector pr.Y _)
        (List.Vector.cons s vTail) (by simp [vTail, List.reverse_append]; rfl)
      refine Eq.trans ?_ (congrArg (Option.map _) hfc.symm)
      have hrv : ∀ t, (PerfectMerkleTree.tree leaf nodeHash z t).getRootValue =
          PerfectMerkleTree.merkleRoot leaf nodeHash z t := fun _ => rfl
      simp only [PerfectMerkleTree.tree_succ, InductiveMerkleTree.generateProof,
        BinaryTree.FullData.leftSubtree, BinaryTree.FullData.rightSubtree,
        AddressedMerkleTree.findCollisionAddressed, List.Vector.head_cons,
        List.Vector.tail_cons, hhd, htl, hnh, h2, hcomp, hsub2', hrv]
      rw [← h2]
      change (if (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))),
              PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) =
            (PerfectMerkleTree.climb nodeHash idx leafVal auth, s) then _ else _) =
        Option.map _ (if (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))),
              PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) =
            (PerfectMerkleTree.climb nodeHash idx leafVal auth, s) then _ else _)
      by_cases heq : (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))),
          PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) =
          (PerfectMerkleTree.climb nodeHash idx leafVal auth, s)
      · rw [ite_eq_left heq, ite_eq_left heq, ih', Option.map_map, h2]
        refine congrArg (fun f => Option.map f _) ?_
        funext w
        simp [BinaryTree.SkeletonInternalIndex.natAddr, h2]
      · rw [ite_eq_right heq, ite_eq_right heq]
        have hmr : PerfectMerkleTree.merkleRoot leaf nodeHash (z + 1) (idx / 2 ^ (z + 1)) =
            PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) .ofInternal
              (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))))
              (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) := rfl
        have hrh : nodeHash (z + 1) (idx / 2 ^ (z + 1)) (PerfectMerkleTree.climb nodeHash idx leafVal auth) s =
            PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) .ofInternal
              (PerfectMerkleTree.climb nodeHash idx leafVal auth) s := rfl
        by_cases hparEq : PerfectMerkleTree.merkleRoot leaf nodeHash (z + 1) (idx / 2 ^ (z + 1)) =
            nodeHash (z + 1) (idx / 2 ^ (z + 1)) (PerfectMerkleTree.climb nodeHash idx leafVal auth) s
        · rw [ite_eq_left hparEq, ite_eq_left (hmr.symm.trans (hparEq.trans hrh))]
          simp [BinaryTree.SkeletonInternalIndex.natAddr]
        · rw [ite_eq_right hparEq, ite_eq_right (fun h => hparEq (hmr.trans (h.trans hrh.symm)))]
          rfl
    · have h2 : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by omega
      have hnh : (fun a => PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) (.ofRight a)) =
          PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z) := by
        funext a
        simp [PerfectMerkleTree.nodeHashAt, BinaryTree.SkeletonInternalIndex.natAddr, h2]
      have hcomp : AddressedMerkleTree.getPutativeRootAddressedWithHash
          (PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z))
          (BinaryTree.SkeletonLeafIndex.ofNat z idx) (leaf idx)
          (InductiveMerkleTree.generateProof (PerfectMerkleTree.tree leaf nodeHash z (idx / 2 ^ z))
            (BinaryTree.SkeletonLeafIndex.ofNat z idx)) =
          PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1) := by
        rw [← PerfectMerkleTree.leafData_get_ofNat leaf z idx, h2]
        exact AddressedMerkleTree.addressed_functional_completeness _ _ _
      have hsub2 : AddressedMerkleTree.getPutativeRootAddressedWithHash
          (PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z))
          (BinaryTree.SkeletonLeafIndex.ofNat z idx) leafVal ⟨auth.reverse, by simp [z]⟩ =
          PerfectMerkleTree.climb nodeHash idx leafVal auth :=
        (PerfectMerkleTree.climb_eq nodeHash idx leafVal auth (z := z) rfl).symm
      have hof : BinaryTree.SkeletonLeafIndex.ofNat (z + 1) idx =
          .ofRight (BinaryTree.SkeletonLeafIndex.ofNat z idx) := by
        simp [BinaryTree.SkeletonLeafIndex.ofNat, hpar]
      let vTail : List.Vector pr.Y (BinaryTree.SkeletonLeafIndex.ofNat z idx).depth :=
        ⟨auth.reverse, by simp [z]⟩
      have hsub2' : AddressedMerkleTree.getPutativeRootAddressedWithHash
          (PerfectMerkleTree.nodeHashAt nodeHash z (idx / 2 ^ z))
          (BinaryTree.SkeletonLeafIndex.ofNat z idx) leafVal vTail =
          PerfectMerkleTree.climb nodeHash idx leafVal auth := hsub2
      have hhd : (List.Vector.cons s vTail).head = s := rfl
      have htl : (List.Vector.cons s vTail).tail = vTail := rfl
      rw [ite_eq_right hpar]
      have hfc := findCollisionAddressed_of_eq pr
        (PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)))
        (PerfectMerkleTree.tree leaf nodeHash (z + 1) (idx / 2 ^ (z + 1))) hof (leaf idx) leafVal
        (⟨(auth ++ [s]).reverse, by simp [z]⟩ : List.Vector pr.Y _)
        (List.Vector.cons s vTail) (by simp [vTail, List.reverse_append]; rfl)
      refine Eq.trans ?_ (congrArg (Option.map _) hfc.symm)
      have hrv : ∀ t, (PerfectMerkleTree.tree leaf nodeHash z t).getRootValue =
          PerfectMerkleTree.merkleRoot leaf nodeHash z t := fun _ => rfl
      simp only [PerfectMerkleTree.tree_succ, InductiveMerkleTree.generateProof,
        BinaryTree.FullData.leftSubtree, BinaryTree.FullData.rightSubtree,
        AddressedMerkleTree.findCollisionAddressed, List.Vector.head_cons,
        List.Vector.tail_cons, hhd, htl, hnh, h2, hcomp, hsub2', hrv]
      rw [← h2]
      change (if (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))),
              PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) =
            (s, PerfectMerkleTree.climb nodeHash idx leafVal auth) then _ else _) =
        Option.map _ (if (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))),
              PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) =
            (s, PerfectMerkleTree.climb nodeHash idx leafVal auth) then _ else _)
      by_cases heq : (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))),
          PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) =
          (s, PerfectMerkleTree.climb nodeHash idx leafVal auth)
      · rw [ite_eq_left heq, ite_eq_left heq, ih', Option.map_map, h2]
        refine congrArg (fun f => Option.map f _) ?_
        funext w
        simp [BinaryTree.SkeletonInternalIndex.natAddr, h2]
      · rw [ite_eq_right heq, ite_eq_right heq]
        have hmr : PerfectMerkleTree.merkleRoot leaf nodeHash (z + 1) (idx / 2 ^ (z + 1)) =
            PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) .ofInternal
              (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1))))
              (PerfectMerkleTree.merkleRoot leaf nodeHash z (2 * (idx / 2 ^ (z + 1)) + 1)) := rfl
        have hrh : nodeHash (z + 1) (idx / 2 ^ (z + 1)) s (PerfectMerkleTree.climb nodeHash idx leafVal auth) =
            PerfectMerkleTree.nodeHashAt nodeHash (z + 1) (idx / 2 ^ (z + 1)) .ofInternal
              s (PerfectMerkleTree.climb nodeHash idx leafVal auth) := rfl
        by_cases hparEq : PerfectMerkleTree.merkleRoot leaf nodeHash (z + 1) (idx / 2 ^ (z + 1)) =
            nodeHash (z + 1) (idx / 2 ^ (z + 1)) s (PerfectMerkleTree.climb nodeHash idx leafVal auth)
        · rw [ite_eq_left hparEq, ite_eq_left (hmr.symm.trans (hparEq.trans hrh))]
          simp [BinaryTree.SkeletonInternalIndex.natAddr]
        · rw [ite_eq_right hparEq, ite_eq_right (fun h => hparEq (hmr.trans (h.trans hrh.symm)))]
          rfl

end MerkleTrace

/-! ## 4. Single-pass WOTS+ chain trace and 0-query WOTS+ witness extraction -/

section WotsTrace

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Explicit-oracle WOTS+ chain advancing from step `i` for `n` steps, returning
`(endpoint, values)` where `values.getD k default = chain pk chAdrs x i k` for `0 ≤ k ≤ n`. -/
def wotsChainTraceM (chAdrs : Adrs) (x : pr.Y) (i : ℕ) :
    ℕ → OracleComp (thSpec pr) (pr.Y × List pr.Y)
  | 0 => pure (x, [x])
  | n + 1 => do
    let (cur, trace) ← wotsChainTraceM chAdrs x i n
    let nxt ← thQuery pr ⟨.F, chAdrs.setHashAddress (i + n), cur⟩
    return (nxt, trace ++ [nxt])

omit [Inhabited pr.Y] in
theorem wotsChainTraceM_queryBound (chAdrs : Adrs) (x : pr.Y) (i : ℕ) :
    ∀ n, IsTotalQueryBound (wotsChainTraceM pr chAdrs x i n) n
  | 0 => isTotalQueryBound_pure' _
  | n + 1 => by
    simp only [wotsChainTraceM]
    refine (isTotalQueryBound_bind (wotsChainTraceM_queryBound chAdrs x i n) fun ⟨cur, trace⟩ =>
      isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (isTotalQueryBound_thQuery pr _) fun nxt =>
        isTotalQueryBound_pure' (nxt, trace ++ [nxt])).mono (by omega)

theorem simulateQ_wotsChainTraceM_spec (pk : pr.PkSeed) (chAdrs : Adrs) (x : pr.Y) (i : ℕ) :
    ∀ n,
      let r := Id.run (simulateQ (thRealImpl pr pk) (wotsChainTraceM pr chAdrs x i n))
      r.1 = chain (prEager pr) pk chAdrs x i n ∧
      r.2.length = n + 1 ∧
      ∀ k ≤ n, r.2.getD k default = chain (prEager pr) pk chAdrs x i k
  | 0 => by
    refine ⟨rfl, rfl, fun k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | n + 1 => by
    have ih := simulateQ_wotsChainTraceM_spec pk chAdrs x i n
    set r := Id.run (simulateQ (thRealImpl pr pk) (wotsChainTraceM pr chAdrs x i n))
    have hstep : Id.run (simulateQ (thRealImpl pr pk) (wotsChainTraceM pr chAdrs x i (n + 1))) =
        (pr.F pk (chAdrs.setHashAddress (i + n)) r.1,
          r.2 ++ [pr.F pk (chAdrs.setHashAddress (i + n)) r.1]) := by
      simp [wotsChainTraceM, r, simulateQ_thQuery, Primitives.memberEval]
    rw [hstep]
    refine ⟨?_, by simp [ih.2.1], fun k hk => ?_⟩
    · rw [chain_succ, ih.1]; rfl
    · by_cases hkn : k ≤ n
      · have hlt : k < r.2.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          ← List.getD_eq_getElem?_getD]
        exact ih.2.2 k hkn
      · have hkeq : k = n + 1 := by omega
        subst hkeq
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ih.2.1,
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, chain_succ, ih.1]
        rfl

/-- Explicit-oracle WOTS+ recovery returning `(wotsPk, tops, chainTraces)`. -/
def wotsRecoverTraceM (sig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core) (msg : pr.Y)
    (leafAdrs : Adrs) :
    OracleComp (thSpec pr) (pr.Y × Vector pr.Y vp.sl.params.len × Vector (List pr.Y) vp.sl.params.len) := do
  let res ← Vector.ofFnM fun c : Fin vp.sl.params.len =>
    let a := chainStepsCore pr.toSLHDSA.core msg c.val
    wotsChainTraceM pr (wotsChainAdrs leafAdrs c.val) sig[c.val] a (vp.sl.params.w - 1 - a)
  let tops : Vector pr.Y vp.sl.params.len := res.map Prod.fst
  let traces : Vector (List pr.Y) vp.sl.params.len := res.map Prod.snd
  let pk ← thQuery pr ⟨.thLsl, wotsPkAdrs leafAdrs,
    tops.cast (Params.lsl_eq_len vp.valid).symm⟩
  return (pk, tops, traces)

omit [Inhabited pr.Y] in
theorem wotsRecoverTraceM_queryBound (sig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core)
    (msg : pr.Y) (leafAdrs : Adrs) :
    IsTotalQueryBound (wotsRecoverTraceM pr sig msg leafAdrs) (VerifyCount.wotsSmax vp.params + 1) := by
  unfold wotsRecoverTraceM
  have hchains : IsTotalQueryBound
      (Vector.ofFnM fun c : Fin vp.sl.params.len =>
        let a := chainStepsCore pr.toSLHDSA.core msg c.val
        wotsChainTraceM pr (wotsChainAdrs leafAdrs c.val) sig[c.val] a (vp.sl.params.w - 1 - a))
      (∑ c : Fin vp.sl.params.len, (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core msg c.val)) :=
    isTotalQueryBound_ofFnM _ _ fun c => wotsChainTraceM_queryBound pr _ _ _ _
  refine (isTotalQueryBound_bind hchains fun res =>
    isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (isTotalQueryBound_thQuery pr _) fun pk =>
      isTotalQueryBound_pure' (pk, res.map Prod.fst, res.map Prod.snd)).mono ?_
  have hsmax := VerifyCount.sum_complement_chainStepsCore_le_smax pr msg
  omega

/-- Honest WOTS+ chain value at chain `c`, step `s` read from `(tbl, u)` at zero hash cost. -/
def honestWotsVal (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (leafAdrs : Adrs) (c s : ℕ) : pr.Y :=
  if s = 0 then slSecOf pr u (wotsSkAdrs leafAdrs c)
  else (tbl ((wotsChainAdrs leafAdrs c).setHashAddress (s - 1))).getD default

theorem honestWotsVal_eq_chain (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tbl : Adrs → Option pr.Y) (htbl : TblComplete pr pk u tbl)
    (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (s : ℕ) (hs : s ≤ vp.sl.params.w - 1) :
    honestWotsVal pr tbl u (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val s =
      chain (prEager pr) pk (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val)
        (slSecOf pr u (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val)) 0 s := by
  unfold honestWotsVal
  rcases s with _ | t
  · simp [chain_zero]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have hmem : (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) c.val).setHashAddress t ∈
        constructionAddresses vp.sl := by
      rw [mem_constructionAddresses_iff]
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      rw [SLHDSA.Security.wotsLeafAdrs_eq_wotsInstanceAdrs pos]
      exact mem_wotsStepAddresses vp.sl (pos, c) ⟨t, by omega⟩
    rw [htbl _ hmem, Option.getD_some, honestVal_eq_wotsChain]

/-- Pure 0-query per-chain WOTS+ witness extraction from a recorded chain trace and `(tbl, u)`. -/
def wotsChainWitnessFromTrace [DecidableEq pr.Y] (tbl : Adrs → Option pr.Y)
    (u : SlSecAdrs vp → pr.Y) (leafAdrs : Adrs) (msg msg' : pr.Y)
    (traces : Vector (List pr.Y) vp.sl.params.len) (c : Fin vp.sl.params.len) :
    Option (WotsWitness vp.sl.params (prEager pr)) :=
  let a := chainStepsCore (prEager pr).core msg c.val
  let b := chainStepsCore (prEager pr).core msg' c.val
  if a < b then
    let tr := traces[c.val]
    let advanced := tr.getD (b - a) default
    let honestB := honestWotsVal pr tbl u leafAdrs c.val b
    if advanced = honestB then
      some (.fPreimage c (b - 1) (tr.getD (b - 1 - a) default))
    else
      ((List.range (vp.sl.params.w - 1 - b)).find? fun j =>
        decide (tr.getD (b - a + j) default ≠ honestWotsVal pr tbl u leafAdrs c.val (b + j) ∧
          tr.getD (b - a + (j + 1)) default = honestWotsVal pr tbl u leafAdrs c.val (b + (j + 1)))).map
        fun j => .fCollision c (b + j) (tr.getD (b - a + j) default)
  else none

/-- Pure 0-query WOTS+ witness extraction from recorded tops/traces and `(tbl, u)`. -/
def wotsWitnessFromTrace [DecidableEq pr.Y] (tbl : Adrs → Option pr.Y)
    (u : SlSecAdrs vp → pr.Y) (leafAdrs : Adrs) (msg msg' : pr.Y)
    (tops : Vector pr.Y vp.sl.params.len) (traces : Vector (List pr.Y) vp.sl.params.len) :
    Option (WotsWitness vp.sl.params (prEager pr)) :=
  let honestTops : Vector pr.Y vp.sl.params.len :=
    Vector.ofFn fun c => honestWotsVal pr tbl u leafAdrs c.val (vp.sl.params.w - 1)
  if tops = honestTops then
    (List.finRange vp.sl.params.len).findSome?
      (wotsChainWitnessFromTrace pr tbl u leafAdrs msg msg' traces)
  else
    some (.tlCollision tops)

/-- Pure 0-query keyless WOTS+ `F`-preimage scanner on recorded chain traces against an honest
signature `(honestSig, honestMsg)` (used by `WotsHybrid.findHybWotsPre` so `B_ud`/`B_pre` make
at most `V_sl` Stage-2 `Th_λ` queries). -/
def wotsPreFromTrace [DecidableEq pr.Y]
    (msg honestMsg : pr.Y) (honestSig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core)
    (traces : Vector (List pr.Y) vp.sl.params.len) :
    Option (Fin vp.sl.params.len × ℕ × pr.Y) :=
  (List.finRange vp.sl.params.len).findSome? fun c =>
    let a := chainStepsCore (prEager pr).core msg c.val
    let b := chainStepsCore (prEager pr).core honestMsg c.val
    if a < b then
      let tr := traces[c.val]
      if tr.getD (b - a) default = honestSig[c.val] then
        some (c, b - 1, tr.getD (b - 1 - a) default)
      else none
    else none

theorem simulateQ_wotsRecoverTraceM_spec (pk : pr.PkSeed)
    (sig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core) (msg : pr.Y) (leafAdrs : Adrs) :
    let r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
    r.1 = wotsPkFromSig (prEager pr) sig msg pk leafAdrs ∧
    r.2.1 = wotsPkFromSigTops (prEager pr) sig msg pk leafAdrs ∧
    ∀ (c : Fin vp.sl.params.len) (k : ℕ),
      k ≤ vp.sl.params.w - 1 - chainStepsCore (prEager pr).core msg c.val →
      r.2.2[c.val].getD k default =
        chain (prEager pr) pk (wotsChainAdrs leafAdrs c.val) sig[c.val]
          (chainStepsCore (prEager pr).core msg c.val) k := by
  set raw : Vector (pr.Y × List pr.Y) vp.sl.params.len := Vector.ofFn fun c : Fin vp.sl.params.len =>
    Id.run (simulateQ (thRealImpl pr pk) (wotsChainTraceM pr (wotsChainAdrs leafAdrs c.val) sig[c.val]
      (chainStepsCore pr.toSLHDSA.core msg c.val)
      (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core msg c.val)))
  have hrun : Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs)) =
      (pr.ThLsl pk (wotsPkAdrs leafAdrs) ((raw.map Prod.fst).cast (Params.lsl_eq_len vp.valid).symm),
        raw.map Prod.fst, raw.map Prod.snd) := by
    unfold wotsRecoverTraceM
    simp only [simulateQ_bind, Id.run_bind, VerifyCount.simulateQ_ofFnM, simulateQ_thQuery,
      simulateQ_pure, Id.run_pure, Primitives.memberEval]
    rfl
  dsimp only
  rw [hrun]
  have htops : raw.map Prod.fst = wotsPkFromSigTops (prEager pr) sig msg pk leafAdrs := by
    apply Vector.ext; intro c hc
    simp only [raw, Vector.getElem_map, Vector.getElem_ofFn, wotsPkFromSigTops_eq_ofFn]
    exact (simulateQ_wotsChainTraceM_spec pr pk _ _ _ _).1
  refine ⟨?_, htops, fun c k hk => ?_⟩
  · rw [wotsPkFromSig_eq_tl, ← htops]
    change pr.Th pk (wotsPkAdrs leafAdrs) ((raw.map Prod.fst).cast _).toList =
      pr.Th pk (wotsPkAdrs leafAdrs) (raw.map Prod.fst).toList
    rw [Vector.toList_cast]
  · simp only [raw, Vector.getElem_map, Vector.getElem_ofFn]
    exact (simulateQ_wotsChainTraceM_spec pr pk _ _ _ _).2.2 k hk

/-- Soundness of `wotsPreFromTrace`: any returned `(c, step, val)` is a genuine `F`-preimage of
`honestSig[c]` at `step = b - 1 < w - 1`. -/
theorem wotsPreFromTrace_sound [DecidableEq pr.Y]
    (pk : pr.PkSeed) (sig honestSig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core)
    (msg honestMsg : pr.Y) (leafAdrs : Adrs)
    {c : Fin vp.sl.params.len} {step : ℕ} {val : pr.Y}
    (h : wotsPreFromTrace pr msg honestMsg honestSig
      (Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))).2.2 =
      some (c, step, val)) :
    step < vp.sl.params.w - 1 ∧
    step + 1 = chainStepsCore (prEager pr).core honestMsg c.val ∧
    pr.F pk ((wotsChainAdrs leafAdrs c.val).setHashAddress step) val = honestSig[c.val] := by
  have hrec := simulateQ_wotsRecoverTraceM_spec pr pk sig msg leafAdrs
  unfold wotsPreFromTrace at h
  obtain ⟨c', -, hc'⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hc'
  set a := chainStepsCore (prEager pr).core msg c'.val
  set b := chainStepsCore (prEager pr).core honestMsg c'.val
  have hb_le : b ≤ vp.sl.params.w - 1 := chainStepsCore_le (prEager pr).core honestMsg c'.val
  split at hc'
  · rename_i hab
    split at hc'
    · rename_i hadv
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨rfl, rfl, rfl⟩ := hc'
      refine ⟨by omega, by omega, ?_⟩
      have htr1 : (Id.run (simulateQ (thRealImpl pr pk)
            (wotsRecoverTraceM pr sig msg leafAdrs))).2.2[c'.val].getD (b - 1 - a) default =
          chain (prEager pr) pk (wotsChainAdrs leafAdrs c'.val) sig[c'.val] a (b - 1 - a) :=
        hrec.2.2 c' (b - 1 - a) (by omega)
      have htr2 : (Id.run (simulateQ (thRealImpl pr pk)
            (wotsRecoverTraceM pr sig msg leafAdrs))).2.2[c'.val].getD (b - a) default =
          chain (prEager pr) pk (wotsChainAdrs leafAdrs c'.val) sig[c'.val] a (b - a) :=
        hrec.2.2 c' (b - a) (by omega)
      rw [htr1]
      rw [htr2] at hadv
      have hsucc : chain (prEager pr) pk (wotsChainAdrs leafAdrs c'.val) sig[c'.val] a (b - a) =
          pr.F pk ((wotsChainAdrs leafAdrs c'.val).setHashAddress (b - 1))
            (chain (prEager pr) pk (wotsChainAdrs leafAdrs c'.val) sig[c'.val] a (b - 1 - a)) := by
        rw [show b - a = (b - 1 - a) + 1 by omega, chain_succ,
          show a + (b - 1 - a) = b - 1 by omega]
        rfl
      rw [← hsucc]
      exact hadv
    · cases hc'
  · cases hc'

/-- Whenever `wotsWitnessFromTrace` returns `.fPreimage c step val`, `wotsPreFromTrace` succeeds. -/
theorem wotsPreFromTrace_isSome_of_wotsWitnessFromTrace [DecidableEq pr.Y]
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl)
    (sig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core) (msg msg' : pr.Y)
    {c : Fin vp.sl.params.len} {step : ℕ} {val : pr.Y}
    (hw : let leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
      let r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
      wotsWitnessFromTrace pr tbl u leafAdrs msg msg' r.2.1 r.2.2 = some (.fPreimage c step val)) :
    let leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
    let r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
    (wotsPreFromTrace pr msg msg' (wotsSign (prEager pr) msg' u pk leafAdrs) r.2.2).isSome = true := by
  dsimp only at hw ⊢
  set leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
  set r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
  unfold wotsWitnessFromTrace at hw
  dsimp only at hw
  split at hw
  · obtain ⟨c', -, hc'⟩ := List.exists_of_findSome?_eq_some hw
    unfold wotsChainWitnessFromTrace at hc'
    dsimp only at hc'
    split at hc'
    · rename_i hab
      split at hc'
      · rename_i hadv
        have hhonB : honestWotsVal pr tbl u leafAdrs c'.val (chainStepsCore (prEager pr).core msg' c'.val) =
            (wotsSign (prEager pr) msg' u pk leafAdrs)[c'.val] := by
          rw [wotsSign_eq_ofFn, Vector.getElem_ofFn]
          exact honestWotsVal_eq_chain pr pk u tbl htbl pos c' _
            (chainStepsCore_le (prEager pr).core msg' c'.val)
        rw [hhonB] at hadv
        unfold wotsPreFromTrace
        rw [Option.isSome_iff_ne_none]
        intro hnone
        rw [List.findSome?_eq_none_iff] at hnone
        have hnone' := hnone c' (List.mem_finRange c')
        simp only [hab, hadv, ↓reduceIte] at hnone'
        cases hnone'
      · rw [Option.map_eq_some_iff] at hc'
        obtain ⟨_, _, hcontra⟩ := hc'
        cases hcontra
    · cases hc'
  · cases hw

/-- Soundness of `wotsWitnessFromTrace`: every returned witness satisfies `WotsWitness.Valid`
against the honest WOTS+ material at `pos`. -/
theorem wotsWitnessFromTrace_sound [DecidableEq pr.Y]
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl)
    (sig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core) (msg msg' : pr.Y)
    (hpk : wotsPkFromSig (prEager pr) sig msg pk (wotsLeafAdrs pos.toAdrs pos.leaf.val) =
      wotsPkGen (prEager pr) u pk (wotsLeafAdrs pos.toAdrs pos.leaf.val))
    {w : WotsWitness vp.sl.params (prEager pr)}
    (hw : let leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
      let r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
      wotsWitnessFromTrace pr tbl u leafAdrs msg msg' r.2.1 r.2.2 = some w) :
    w.Valid pk (wotsLeafAdrs pos.toAdrs pos.leaf.val)
      (wotsPkGenTops (prEager pr) u pk (wotsLeafAdrs pos.toAdrs pos.leaf.val))
      (wotsSign (prEager pr) msg' u pk (wotsLeafAdrs pos.toAdrs pos.leaf.val)) msg' := by
  dsimp only at hw
  set leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
  have hrec := simulateQ_wotsRecoverTraceM_spec pr pk sig msg leafAdrs
  set r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
  have hhtops : (Vector.ofFn fun c : Fin vp.sl.params.len =>
        honestWotsVal pr tbl u leafAdrs c.val (vp.sl.params.w - 1)) =
      wotsPkGenTops (prEager pr) u pk leafAdrs := by
    apply Vector.ext; intro c hc
    simp only [Vector.getElem_ofFn, wotsPkGenTops_eq_ofFn]
    exact honestWotsVal_eq_chain pr pk u tbl htbl pos ⟨c, hc⟩ (vp.sl.params.w - 1) le_rfl
  unfold wotsWitnessFromTrace at hw
  dsimp only at hw
  rw [hrec.2.1, hhtops] at hw
  split at hw
  · obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hw
    unfold wotsChainWitnessFromTrace at hc
    dsimp only at hc
    set a := chainStepsCore (prEager pr).core msg c.val
    set b := chainStepsCore (prEager pr).core msg' c.val
    set chAdrs := wotsChainAdrs leafAdrs c.val
    have hb_le : b ≤ vp.sl.params.w - 1 := chainStepsCore_le (prEager pr).core msg' c.val
    split at hc
    · rename_i hab
      have htr : ∀ k ≤ vp.sl.params.w - 1 - a,
          r.2.2[c.val].getD k default = chain (prEager pr) pk chAdrs sig[c.val] a k :=
        fun k hk => hrec.2.2 c k hk
      have hhonB : honestWotsVal pr tbl u leafAdrs c.val b =
          (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] := by
        rw [wotsSign_eq_ofFn, Vector.getElem_ofFn]
        exact honestWotsVal_eq_chain pr pk u tbl htbl pos c b hb_le
      split at hc
      · rename_i hadv
        simp only [Option.some.injEq] at hc
        subst hc
        rw [WotsWitness.valid_fPreimage]
        refine ⟨by omega, by omega, ?_⟩
        rw [htr (b - 1 - a) (by omega)]
        rw [htr (b - a) (by omega), hhonB] at hadv
        have hstep : chain (prEager pr) pk chAdrs sig[c.val] a (b - a) =
            (prEager pr).F pk (chAdrs.setHashAddress (b - 1))
              (chain (prEager pr) pk chAdrs sig[c.val] a (b - 1 - a)) := by
          rw [show b - a = (b - 1 - a) + 1 by omega, chain_succ,
            show a + (b - 1 - a) = b - 1 by omega]
        rw [← hstep]
        exact hadv
      · rw [Option.map_eq_some_iff] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        have hj_mem : j < vp.sl.params.w - 1 - b := List.mem_range.1 (List.mem_of_find?_eq_some hj)
        have hj_pred := List.find?_some hj
        simp only [decide_eq_true_eq] at hj_pred
        rw [WotsWitness.valid_fCollision]
        have hforged : ∀ d ≤ vp.sl.params.w - 1 - b,
            r.2.2[c.val].getD (b - a + d) default =
              chain (prEager pr) pk chAdrs sig[c.val] a (b - a + d) :=
          fun d hd => htr (b - a + d) (by omega)
        have hhonest : ∀ d ≤ vp.sl.params.w - 1 - b,
            honestWotsVal pr tbl u leafAdrs c.val (b + d) =
              chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] b d := by
          intro d hd
          rw [honestWotsVal_eq_chain pr pk u tbl htbl pos c (b + d) (by omega),
            wotsSign_eq_ofFn, Vector.getElem_ofFn]
          have hcomp := chain_compose (prEager pr) pk chAdrs
            (slSecOf pr u (wotsSkAdrs leafAdrs c.val)) 0 b d
          simpa only [Nat.zero_add] using hcomp.symm
        rw [hforged j (by omega), hforged (j + 1) (by omega),
          hhonest j (by omega), hhonest (j + 1) (by omega)] at hj_pred
        have hsub : b + j - b = j := by omega
        refine ⟨by omega, Nat.le_add_right b j, ?_, ?_⟩
        · rw [hforged j (by omega)]
          simpa only [b, chAdrs, hsub] using hj_pred.1
        · rw [hforged j (by omega)]
          have hstepF : (prEager pr).F pk (chAdrs.setHashAddress (b + j))
                (chain (prEager pr) pk chAdrs sig[c.val] a (b - a + j)) =
              chain (prEager pr) pk chAdrs sig[c.val] a (b - a + (j + 1)) := by
            rw [show b - a + (j + 1) = (b - a + j) + 1 by omega, chain_succ,
              show a + (b - a + j) = b + j by omega]
          have hstepH : (prEager pr).F pk (chAdrs.setHashAddress (b + j))
                (chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] b j) =
              chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] b (j + 1) := by
            rw [chain_succ]
          simpa only [b, chAdrs, hsub, hstepF, hstepH] using hj_pred.2
    · cases hc
  · rename_i hneq
    simp only [Option.some.injEq] at hw
    subst hw
    rw [WotsWitness.valid_tlCollision]
    refine ⟨hneq, ?_⟩
    rw [wotsPkFromSig_eq_tl, SLHDSA.wotsPkGen_eq_tl] at hpk
    exact hpk

/-- Completeness of `wotsWitnessFromTrace`: on distinct messages `msg ≠ msg'` under `ByteLaws`,
`wotsWitnessFromTrace` always returns `some _`. -/
theorem wotsWitnessFromTrace_isSome [DecidableEq pr.Y]
    (hinj : Function.Injective pr.yToBytes)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl)
    (sig : SLHDSA.WotsSig vp.sl.params pr.toSLHDSA.core) (msg msg' : pr.Y)
    (hne : msg ≠ msg') :
    let leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
    let r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
    (wotsWitnessFromTrace pr tbl u leafAdrs msg msg' r.2.1 r.2.2).isSome = true := by
  dsimp only
  set leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
  have hrec := simulateQ_wotsRecoverTraceM_spec pr pk sig msg leafAdrs
  set r := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig msg leafAdrs))
  have hhtops : (Vector.ofFn fun c : Fin vp.sl.params.len =>
        honestWotsVal pr tbl u leafAdrs c.val (vp.sl.params.w - 1)) =
      wotsPkFromSigTops (prEager pr) (wotsSign (prEager pr) msg' u pk leafAdrs) msg' pk leafAdrs := by
    rw [SLHDSA.wotsPkFromSigTops_wotsSign]
    apply Vector.ext; intro c hc
    simp only [Vector.getElem_ofFn, wotsPkGenTops_eq_ofFn]
    exact honestWotsVal_eq_chain pr pk u tbl htbl pos ⟨c, hc⟩ (vp.sl.params.w - 1) le_rfl
  unfold wotsWitnessFromTrace
  dsimp only
  rw [hrec.2.1, hhtops]
  split_ifs with htops
  · obtain ⟨c, hab, -⟩ := wotsPkFromSigTops_cases vp.sl.valid (prEager pr) (prEager_byteLaws pr hinj)
      sig (wotsSign (prEager pr) msg' u pk leafAdrs) msg msg' pk leafAdrs hne htops
    have hend : chain (prEager pr) pk (wotsChainAdrs leafAdrs c.val) sig[c.val]
          (chainStepsCore (prEager pr).core msg c.val)
          (vp.sl.params.w - 1 - chainStepsCore (prEager pr).core msg c.val) =
        chain (prEager pr) pk (wotsChainAdrs leafAdrs c.val)
          (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val]
          (chainStepsCore (prEager pr).core msg' c.val)
          (vp.sl.params.w - 1 - chainStepsCore (prEager pr).core msg' c.val) := by
      have h := congrArg (fun v : Vector pr.Y vp.sl.params.len => v[c.val]) htops
      simpa only [wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn] using h
    have hcSome : (wotsChainWitnessFromTrace pr tbl u leafAdrs msg msg' r.2.2 c).isSome = true := by
      unfold wotsChainWitnessFromTrace
      dsimp only
      set a := chainStepsCore (prEager pr).core msg c.val
      set b := chainStepsCore (prEager pr).core msg' c.val
      set chAdrs := wotsChainAdrs leafAdrs c.val
      have hb_le : b ≤ vp.sl.params.w - 1 := chainStepsCore_le (prEager pr).core msg' c.val
      rw [ite_eq_left hab]
      have htr : ∀ k ≤ vp.sl.params.w - 1 - a,
          r.2.2[c.val].getD k default = chain (prEager pr) pk chAdrs sig[c.val] a k :=
        fun k hk => hrec.2.2 c k hk
      have hadv_eq : r.2.2[c.val].getD (b - a) default =
          chain (prEager pr) pk chAdrs sig[c.val] a (b - a) := htr (b - a) (by omega)
      have hhonB : honestWotsVal pr tbl u leafAdrs c.val b =
          (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] := by
        rw [wotsSign_eq_ofFn, Vector.getElem_ofFn]
        exact honestWotsVal_eq_chain pr pk u tbl htbl pos c b hb_le
      split_ifs with hadv
      · rfl
      · rw [Option.isSome_map]
        have hcomp : chain (prEager pr) pk chAdrs (chain (prEager pr) pk chAdrs sig[c.val] a (b - a))
              b (vp.sl.params.w - 1 - b) =
            chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val]
              b (vp.sl.params.w - 1 - b) := by
          have hc' := chain_compose (prEager pr) pk chAdrs sig[c.val] a (b - a) (vp.sl.params.w - 1 - b)
          rw [show a + (b - a) = b by omega, show b - a + (vp.sl.params.w - 1 - b) =
            vp.sl.params.w - 1 - a by omega] at hc'
          rw [hc', hend]
        have hdiv := findChainDivergence_isSome_of_ne (prEager pr) pk chAdrs
          (chain (prEager pr) pk chAdrs sig[c.val] a (b - a))
          (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val]
          b (vp.sl.params.w - 1 - b) (by rwa [← hadv_eq, ← hhonB]) hcomp
        rw [findChainDivergence_eq_find] at hdiv
        have hfind_eq : (List.range (vp.sl.params.w - 1 - b)).find? (fun j =>
              decide (r.2.2[c.val].getD (b - a + j) default ≠ honestWotsVal pr tbl u leafAdrs c.val (b + j) ∧
                r.2.2[c.val].getD (b - a + (j + 1)) default = honestWotsVal pr tbl u leafAdrs c.val (b + (j + 1)))) =
            (List.range (vp.sl.params.w - 1 - b)).find? (fun j =>
              decide (chain (prEager pr) pk chAdrs (chain (prEager pr) pk chAdrs sig[c.val] a (b - a)) b j ≠
                  chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] b j ∧
                chain (prEager pr) pk chAdrs (chain (prEager pr) pk chAdrs sig[c.val] a (b - a)) b (j + 1) =
                  chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] b (j + 1))) := by
          refine list_find?_congr fun j hj => ?_
          rw [List.mem_range] at hj
          have hf : ∀ d ≤ vp.sl.params.w - 1 - b,
              r.2.2[c.val].getD (b - a + d) default =
                chain (prEager pr) pk chAdrs (chain (prEager pr) pk chAdrs sig[c.val] a (b - a)) b d := by
            intro d hd
            rw [htr (b - a + d) (by omega)]
            have hcc := chain_compose (prEager pr) pk chAdrs sig[c.val] a (b - a) d
            rw [show a + (b - a) = b by omega] at hcc
            exact hcc.symm
          have hh : ∀ d ≤ vp.sl.params.w - 1 - b,
              honestWotsVal pr tbl u leafAdrs c.val (b + d) =
                chain (prEager pr) pk chAdrs (wotsSign (prEager pr) msg' u pk leafAdrs)[c.val] b d := by
            intro d hd
            rw [honestWotsVal_eq_chain pr pk u tbl htbl pos c (b + d) (by omega),
              wotsSign_eq_ofFn, Vector.getElem_ofFn]
            have hcc := chain_compose (prEager pr) pk chAdrs
              (slSecOf pr u (wotsSkAdrs leafAdrs c.val)) 0 b d
            simpa only [Nat.zero_add] using hcc.symm
          rw [hf j (by omega), hf (j + 1) (by omega), hh j (by omega), hh (j + 1) (by omega)]
        rw [hfind_eq]
        exact hdiv
    rw [Option.isSome_iff_ne_none]
    intro hnone
    rw [List.findSome?_eq_none_iff] at hnone
    have hnone' := hnone c (List.mem_finRange c)
    rw [hnone'] at hcSome
    cases hcSome
  · rfl

end WotsTrace

/-! ## 5. Single-pass FORS + Hypertree verification and witness extraction (`≤ Vsl`) -/

section FullExtract

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Recorded per-tree FORS verification data: `(recRoot, recLeaf, topDownClimbTrace)`. -/
abbrev ForsTreeTrace (pr : Primitives vp.params) :=
  pr.Y × pr.Y × List (ℕ × (pr.Y × pr.Y) × pr.Y)

/-- Explicit-oracle FORS recovery returning `(forsPk, perTreeTraces)`. -/
def forsRecoverTraceM (sig : SLHDSA.ForsSigCore vp.sl.params pr.toSLHDSA.core) (md : List Byte)
    (forsAdrs : Adrs) :
    OracleComp (thSpec pr) (pr.Y × Vector (ForsTreeTrace pr) vp.sl.params.k) := do
  let trees ← Vector.ofFnM fun i : Fin vp.sl.params.k => do
    let idx := forsSigLeafIndex vp.sl.params md i.val
    let leaf ← thQuery pr ⟨.F, forsNodeAdrs forsAdrs 0 idx, (sig[i.val]).sk⟩
    let (root, tr) ← merkleClimbTraceM pr (forsNodeAdrs forsAdrs) idx leaf (sig[i.val]).auth.toList
    return (root, leaf, tr)
  let roots : Vector pr.Y vp.params.k := (trees.map Prod.fst).cast rfl
  let forsPk ← thQuery pr ⟨.thK, forsPkAdrs forsAdrs, roots⟩
  return (forsPk, trees)

omit [Inhabited pr.Y] in
theorem forsRecoverTraceM_queryBound (sig : SLHDSA.ForsSigCore vp.sl.params pr.toSLHDSA.core)
    (md : List Byte) (forsAdrs : Adrs) :
    IsTotalQueryBound (forsRecoverTraceM pr sig md forsAdrs) (vp.params.k * (vp.params.a + 1) + 1) := by
  unfold forsRecoverTraceM
  have htrees : IsTotalQueryBound
      (Vector.ofFnM fun i : Fin vp.sl.params.k => do
        let idx := forsSigLeafIndex vp.sl.params md i.val
        let leaf ← thQuery pr ⟨.F, forsNodeAdrs forsAdrs 0 idx, (sig[i.val]).sk⟩
        let (root, tr) ← merkleClimbTraceM pr (forsNodeAdrs forsAdrs) idx leaf (sig[i.val]).auth.toList
        return (root, leaf, tr))
      (∑ _i : Fin vp.sl.params.k, (vp.params.a + 1)) :=
    isTotalQueryBound_ofFnM _ _ fun i => by
      refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := vp.params.a) (isTotalQueryBound_thQuery pr _)
        fun leaf =>
          (isTotalQueryBound_bind (n₂ := 0) (merkleClimbTraceM_queryBound pr _ _ _ _) fun ⟨root, tr⟩ =>
            isTotalQueryBound_pure' (root, leaf, tr)).mono
            (by simp [ValidatedParams.sl, Params.slParams])).mono
        (by omega)
  refine (isTotalQueryBound_bind htrees fun trees =>
    isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (isTotalQueryBound_thQuery pr _) fun forsPk =>
      isTotalQueryBound_pure' (forsPk, trees)).mono ?_
  simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, Nat.add_zero]
  exact le_rfl

/-- Pure 0-query FORS witness extraction from recorded traces and `tbl`. -/
def forsWitnessFromTrace [DecidableEq pr.Y] (tbl : Adrs → Option pr.Y)
    (sig : SLHDSA.ForsSigCore vp.sl.params pr.toSLHDSA.core) (md : List Byte)
    (forsAdrs : Adrs) (trees : Vector (ForsTreeTrace pr) vp.sl.params.k)
    (target : Fin vp.sl.params.k) : ForsWitness vp.sl.params (prEager pr) :=
  let recRoots : Vector pr.Y vp.sl.params.k := trees.map Prod.fst
  let honestRoots : Vector pr.Y vp.sl.params.k :=
    Vector.ofFn fun i => (tbl (forsNodeAdrs forsAdrs vp.sl.params.a i.val)).getD default
  if recRoots = honestRoots then
    ((List.finRange vp.sl.params.k).findSome? fun i =>
      let idx := forsSigLeafIndex vp.sl.params md i.val
      let recLeaf := (trees[i.val]).2.1
      let honestLeaf := (tbl (forsNodeAdrs forsAdrs 0 idx)).getD default
      if honestLeaf = recLeaf then none
      else
        (merkleFindCollisionFromTrace pr (fun z t => (tbl (forsNodeAdrs forsAdrs z t)).getD default)
          idx (trees[i.val]).2.2).map fun w => .hCollision i w.1 w.2.2).getD
      (.fPreimage target (sig[target.val]).sk)
  else
    .tlCollision recRoots

theorem simulateQ_forsRecoverTraceM_spec (pk : pr.PkSeed)
    (sig : SLHDSA.ForsSigCore vp.sl.params pr.toSLHDSA.core) (md : List Byte) (forsAdrs : Adrs) :
    let r := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig md forsAdrs))
    r.1 = forsPkFromSig (prEager pr) (sig.map fun t => ⟨t.sk, t.auth⟩) md pk forsAdrs ∧
    r.2.map Prod.fst = forsRecoveredRoots (prEager pr) (sig.map fun t => ⟨t.sk, t.auth⟩) md pk forsAdrs ∧
    ∀ i : Fin vp.sl.params.k,
      (r.2[i.val]).2.1 = pr.F pk (forsNodeAdrs forsAdrs 0 (forsSigLeafIndex vp.sl.params md i.val)) (sig[i.val]).sk ∧
      (r.2[i.val]).2.2 =
        (Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr (forsNodeAdrs forsAdrs)
          (forsSigLeafIndex vp.sl.params md i.val)
          (pr.F pk (forsNodeAdrs forsAdrs 0 (forsSigLeafIndex vp.sl.params md i.val)) (sig[i.val]).sk)
          (sig[i.val]).auth.toList))).2 := by
  set raw : Vector (ForsTreeTrace pr) vp.sl.params.k := Vector.ofFn fun i : Fin vp.sl.params.k =>
    let r := Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr (forsNodeAdrs forsAdrs)
      (forsSigLeafIndex vp.sl.params md i.val)
      (pr.F pk (forsNodeAdrs forsAdrs 0 (forsSigLeafIndex vp.sl.params md i.val)) (sig[i.val]).sk)
      (sig[i.val]).auth.toList))
    (r.1, pr.F pk (forsNodeAdrs forsAdrs 0 (forsSigLeafIndex vp.sl.params md i.val)) (sig[i.val]).sk, r.2)
  have hrun : Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig md forsAdrs)) =
      (pr.ThK pk (forsPkAdrs forsAdrs) ((raw.map Prod.fst).cast rfl), raw) := by
    unfold forsRecoverTraceM
    rw [simulateQ_bind, VerifyCount.simulateQ_ofFnM]
    have hvec : (Vector.ofFn fun i : Fin vp.sl.params.k =>
        simulateQ (thRealImpl pr pk) (do
          let idx := forsSigLeafIndex vp.sl.params md i.val
          let leaf ← thQuery pr ⟨.F, forsNodeAdrs forsAdrs 0 idx, (sig[i.val]).sk⟩
          let (root, tr) ← merkleClimbTraceM pr (forsNodeAdrs forsAdrs) idx leaf (sig[i.val]).auth.toList
          return (root, leaf, tr))) = raw := by
      apply Vector.ext; intro i hi
      simp only [raw, Vector.getElem_ofFn]
      have hstep : Id.run (simulateQ (thRealImpl pr pk) (do
          let idx := forsSigLeafIndex vp.sl.params md i
          let leaf ← thQuery pr ⟨.F, forsNodeAdrs forsAdrs 0 idx, (sig[i]).sk⟩
          let (root, tr) ← merkleClimbTraceM pr (forsNodeAdrs forsAdrs) idx leaf (sig[i]).auth.toList
          return (root, leaf, tr))) =
        (let r := Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr (forsNodeAdrs forsAdrs)
          (forsSigLeafIndex vp.sl.params md i)
          (pr.F pk (forsNodeAdrs forsAdrs 0 (forsSigLeafIndex vp.sl.params md i)) (sig[i]).sk)
          (sig[i]).auth.toList))
        (r.1, pr.F pk (forsNodeAdrs forsAdrs 0 (forsSigLeafIndex vp.sl.params md i)) (sig[i]).sk, r.2)) := by
        simp only [simulateQ_bind, Id.run_bind, simulateQ_thQuery, simulateQ_pure, Id.run_pure,
          Primitives.memberEval]
      exact hstep
    rw [hvec]
    simp only [Id.run_bind, simulateQ_bind, simulateQ_thQuery, simulateQ_pure, Id.run_pure,
      Primitives.memberEval]
    rfl
  dsimp only
  rw [hrun]
  have hroots : raw.map Prod.fst =
      forsRecoveredRoots (prEager pr) (sig.map fun t => ⟨t.sk, t.auth⟩) md pk forsAdrs := by
    apply Vector.ext; intro i hi
    rw [forsRecoveredRoots_getElem (prims := prEager pr) (i := i) (hi := hi)]
    simp only [raw, Vector.getElem_map, Vector.getElem_ofFn]
    exact simulateQ_merkleClimbTraceM_fst pr pk (forsNodeAdrs forsAdrs) _ _ _
  refine ⟨?_, hroots, fun i => by simp [raw]⟩
  rw [forsPkFromSig_eq_tl_recoveredRoots, ← hroots]
  rfl

theorem forsWitnessFromTrace_eq_slFindForsWitness [DecidableEq pr.Y]
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (parts : DigestParts vp.sl.params)
    (sig : SLHDSA.ForsSigCore vp.sl.params pr.toSLHDSA.core) (target : Fin vp.sl.params.k) :
    let r := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig parts.md.toList parts.forsAdrs))
    forsWitnessFromTrace pr tbl sig parts.md.toList parts.forsAdrs r.2 target =
      slFindForsWitness pr (sig.map fun t => ⟨t.sk, t.auth⟩) parts.md.toList u pk parts.forsAdrs target := by
  have hrec := simulateQ_forsRecoverTraceM_spec pr pk sig parts.md.toList parts.forsAdrs
  set r := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig parts.md.toList parts.forsAdrs))
  set bp := BottomPosition.ofDigestParts vp.sl parts
  have hfa : parts.forsAdrs = bp.forsAdrs := (BottomPosition.forsAdrs_ofDigestParts vp.sl parts).symm
  have hhonNode : ∀ (i : Fin vp.sl.params.k) (z : ℕ) (t : ℕ),
      z ≤ vp.sl.params.a → t < 2 ^ (vp.sl.params.a - z) →
      (tbl (forsNodeAdrs parts.forsAdrs z (i.val * 2 ^ (vp.sl.params.a - z) + t))).getD default =
        PerfectMerkleTree.merkleRoot (forsLeaf (prEager pr) u pk parts.forsAdrs)
          (forsNodeHash (prEager pr) pk parts.forsAdrs) z (i.val * 2 ^ (vp.sl.params.a - z) + t) := by
    intro i z t hza ht
    rcases z with _ | z'
    · simp only [Nat.sub_zero] at ht ⊢
      have hmem : forsNodeAdrs parts.forsAdrs 0 (i.val * 2 ^ vp.sl.params.a + t) ∈
          constructionAddresses vp.sl := by
        rw [mem_constructionAddresses_iff, hfa]
        refine Or.inl ?_
        simpa [SLHDSA.Params.t] using
          mem_forsLeafAddresses vp.sl bp i ⟨t, by simpa [SLHDSA.Params.t] using ht⟩
      rw [htbl _ hmem, Option.getD_some, honestVal_eq_forsNode]
    · have hmem : forsNodeAdrs parts.forsAdrs (z' + 1) (i.val * 2 ^ (vp.sl.params.a - (z' + 1)) + t) ∈
          constructionAddresses vp.sl := by
        rw [mem_constructionAddresses_iff, hfa]
        refine Or.inr (Or.inl ?_)
        exact mem_forsTreeAddresses vp.sl bp i (Nat.succ_pos z') hza ht
      rw [htbl _ hmem, Option.getD_some, honestVal_eq_forsNode]
  have hhonRoots : (Vector.ofFn fun i : Fin vp.sl.params.k =>
        (tbl (forsNodeAdrs parts.forsAdrs vp.sl.params.a i.val)).getD default) =
      forsHonestRoots (prEager pr) u pk parts.forsAdrs := by
    apply Vector.ext; intro i hi
    rw [forsHonestRoots_getElem (prims := prEager pr) (i := i) (hi := hi), SLHDSA.forsRoot_eq_merkleRoot]
    simp only [Vector.getElem_ofFn]
    have h := hhonNode ⟨i, hi⟩ vp.sl.params.a 0 le_rfl (by simp)
    simpa using h
  unfold forsWitnessFromTrace slFindForsWitness
  dsimp only
  rw [hrec.2.1, hhonRoots]
  split_ifs with hreq
  · congr 1
    · congr 1
      funext i
      unfold slFindForsTreeCollision
      dsimp only
      have hidx_eq : forsSigLeafIndex vp.sl.params parts.md.toList i.val =
          i.val * 2 ^ vp.sl.params.a + SLHDSA.forsIdx vp.sl.params parts.md.toList i.val := by
        simpa [SLHDSA.Params.t] using forsSigLeafIndex_eq vp.sl.params parts.md.toList i.val
      have hidx_lt : SLHDSA.forsIdx vp.sl.params parts.md.toList i.val < 2 ^ vp.sl.params.a := by
        simpa [SLHDSA.Params.t] using SLHDSA.forsIdx_lt vp.sl.params parts.md.toList i.val
      have hleaf : (tbl (forsNodeAdrs parts.forsAdrs 0
            (forsSigLeafIndex vp.sl.params parts.md.toList i.val))).getD default =
          forsLeaf (prEager pr) u pk parts.forsAdrs
            (forsSigLeafIndex vp.sl.params parts.md.toList i.val) := by
        rw [hidx_eq]
        simpa using hhonNode i 0 (SLHDSA.forsIdx vp.sl.params parts.md.toList i.val) (Nat.zero_le _) hidx_lt
      have hrecL : (r.2[i.val]).2.1 =
          (prEager pr).F pk (forsNodeAdrs parts.forsAdrs 0
            (forsSigLeafIndex vp.sl.params parts.md.toList i.val))
            ((sig.map fun t => (⟨t.sk, t.auth⟩ : SLHDSA.ForsTreeSigCore vp.sl.params (prEager pr).core))[i.val]).sk := by
        simp only [Vector.getElem_map]
        exact (hrec.2.2 i).1
      rw [hleaf, hrecL]
      split_ifs with hle
      · rfl
      · congr 1
        rw [(hrec.2.2 i).2]
        have hnh_eq : forsNodeHash (prEager pr) pk parts.forsAdrs =
            fun z t l r => pr.H pk (forsNodeAdrs parts.forsAdrs z t) l r := rfl
        have hauth_eq : (sig.map fun t => (⟨t.sk, t.auth⟩ : SLHDSA.ForsTreeSigCore vp.sl.params (prEager pr).core))[i.val].auth.toList =
            (sig[i.val]).auth.toList := by simp
        have hsk_eq : (prEager pr).F pk (forsNodeAdrs parts.forsAdrs 0
              (forsSigLeafIndex vp.sl.params parts.md.toList i.val))
              ((sig.map fun t => (⟨t.sk, t.auth⟩ : SLHDSA.ForsTreeSigCore vp.sl.params (prEager pr).core))[i.val]).sk =
            pr.F pk (forsNodeAdrs parts.forsAdrs 0
              (forsSigLeafIndex vp.sl.params parts.md.toList i.val)) (sig[i.val]).sk := by
          simp only [Vector.getElem_map]; rfl
        rw [hnh_eq, hauth_eq, hsk_eq]
        refine merkleFindCollisionFromTrace_eq_findCollision pr pk (forsNodeAdrs parts.forsAdrs)
          (forsLeaf (prEager pr) u pk parts.forsAdrs)
          (fun z t => (tbl (forsNodeAdrs parts.forsAdrs z t)).getD default) _ _ _ ?_
        intro h hp hle_len
        have hha : h ≤ vp.sl.params.a := by simpa using hle_len
        have hdiv_form : ∀ (z : ℕ), z ≤ vp.sl.params.a →
            forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ z =
              i.val * 2 ^ (vp.sl.params.a - z) +
                SLHDSA.forsIdx vp.sl.params parts.md.toList i.val / 2 ^ z := by
          intro z hz
          have hpow : 2 ^ vp.sl.params.a = 2 ^ z * 2 ^ (vp.sl.params.a - z) := by
            rw [← pow_add, Nat.add_sub_cancel' hz]
          rw [hidx_eq, hpow, Nat.mul_left_comm,
            Nat.mul_add_div (Nat.pow_pos (by decide : 0 < 2))]
        have hlt_z : ∀ (z : ℕ), z ≤ vp.sl.params.a →
            SLHDSA.forsIdx vp.sl.params parts.md.toList i.val / 2 ^ z < 2 ^ (vp.sl.params.a - z) := by
          intro z hz
          have hd := Nat.div_lt_div_of_lt_of_dvd (Nat.pow_dvd_pow 2 hz) hidx_lt
          simpa [Nat.pow_div hz (by decide : 0 < 2)] using hd
        have hsub : vp.sl.params.a - (h - 1) = vp.sl.params.a - h + 1 := by omega
        have hc0 : 2 * (forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ h) =
            i.val * 2 ^ (vp.sl.params.a - (h - 1)) +
              2 * (SLHDSA.forsIdx vp.sl.params parts.md.toList i.val / 2 ^ h) := by
          rw [hdiv_form h hha, hsub, pow_succ]; ring
        have hc1 : 2 * (forsSigLeafIndex vp.sl.params parts.md.toList i.val / 2 ^ h) + 1 =
            i.val * 2 ^ (vp.sl.params.a - (h - 1)) +
              (2 * (SLHDSA.forsIdx vp.sl.params parts.md.toList i.val / 2 ^ h) + 1) := by
          rw [hc0]; ring
        have hlt_c0 : 2 * (SLHDSA.forsIdx vp.sl.params parts.md.toList i.val / 2 ^ h) <
            2 ^ (vp.sl.params.a - (h - 1)) := by
          have := hlt_z h hha; rw [hsub, pow_succ]; omega
        have hlt_c1 : 2 * (SLHDSA.forsIdx vp.sl.params parts.md.toList i.val / 2 ^ h) + 1 <
            2 ^ (vp.sl.params.a - (h - 1)) := by
          have := hlt_z h hha; rw [hsub, pow_succ]; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [hdiv_form h hha]; exact hhonNode i h _ hha (hlt_z h hha)
        · rw [hc0]; exact hhonNode i (h - 1) _ (by omega) hlt_c0
        · rw [hc1]; exact hhonNode i (h - 1) _ (by omega) hlt_c1
    · simp
  · rfl

/-- Recorded per-layer XMSS verification data. -/
structure XmssLayerTrace (pr : Primitives vp.params) where
  msg : pr.Y
  wotsPk : pr.Y
  wotsTops : Vector pr.Y vp.sl.params.len
  wotsTraces : Vector (List pr.Y) vp.sl.params.len
  xmssRoot : pr.Y
  xmssTrace : List (ℕ × (pr.Y × pr.Y) × pr.Y)

/-- Explicit-oracle single-layer XMSS recovery recording all WOTS+ and Merkle traces. -/
def xmssRecoverTraceM (pos : LayerPosition vp.sl)
    (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) (msg : pr.Y) :
    OracleComp (thSpec pr) (XmssLayerTrace pr) := do
  let (wotsPk, wotsTops, wotsTraces) ← wotsRecoverTraceM pr sig.wots msg
    (wotsLeafAdrs pos.toAdrs pos.leaf.val)
  let (xmssRoot, xmssTrace) ← merkleClimbTraceM pr (xmssNodeAdrs pos.toAdrs)
    pos.leaf.val wotsPk sig.auth.toList
  return ⟨msg, wotsPk, wotsTops, wotsTraces, xmssRoot, xmssTrace⟩

omit [Inhabited pr.Y] in
theorem xmssRecoverTraceM_queryBound (pos : LayerPosition vp.sl)
    (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) (msg : pr.Y) :
    IsTotalQueryBound (xmssRecoverTraceM pr pos sig msg)
      (VerifyCount.wotsSmax vp.params + vp.params.hp + 1) := by
  unfold xmssRecoverTraceM
  refine (isTotalQueryBound_bind (n₁ := VerifyCount.wotsSmax vp.params + 1) (n₂ := vp.params.hp)
    (wotsRecoverTraceM_queryBound pr sig.wots msg _) fun ⟨wotsPk, wotsTops, wotsTraces⟩ =>
      (isTotalQueryBound_bind (n₂ := 0) (merkleClimbTraceM_queryBound pr _ _ _ _)
        fun ⟨xmssRoot, xmssTrace⟩ =>
          isTotalQueryBound_pure' (⟨msg, wotsPk, wotsTops, wotsTraces, xmssRoot, xmssTrace⟩ : XmssLayerTrace pr)).mono
        (by simp [ValidatedParams.sl, Params.slParams])).mono (by omega)

/-- Explicit-oracle hypertree recovery recording all `layers` XMSS layer traces. -/
def htRecoverTraceM (pos : LayerPosition vp.sl) :
    (layers : ℕ) → pos.layer.val + layers = vp.sl.params.d →
    pr.Y → Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers →
    OracleComp (thSpec pr) (pr.Y × Vector (XmssLayerTrace pr) layers)
  | 0, _, msg, _ => pure (msg, #v[])
  | 1, _, msg, sigs => do
    let tr ← xmssRecoverTraceM pr pos sigs.head msg
    return (tr.xmssRoot, #v[tr])
  | layers + 2, h, msg, sigs => do
    let tr ← xmssRecoverTraceM pr pos sigs.head msg
    let (finalRoot, rest) ← htRecoverTraceM (pos.next (by omega)) (layers + 1)
      (by simp only [LayerPosition.next_layer_val]; change pos.layer.val + 1 + (layers + 1) = vp.sl.params.d; omega)
      tr.xmssRoot sigs.tail
    return (finalRoot, rest.insertIdx 0 tr)

omit [Inhabited pr.Y] in
theorem htRecoverTraceM_queryBound :
    ∀ (layers : ℕ) (pos : LayerPosition vp.sl) (hrem : pos.layer.val + layers = vp.sl.params.d)
      (msg : pr.Y) (sigs : Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers),
      IsTotalQueryBound (htRecoverTraceM pr pos layers hrem msg sigs)
        (layers * (VerifyCount.wotsSmax vp.params + vp.params.hp + 1))
  | 0, _, _, _, _ => by simp [htRecoverTraceM]; exact isTotalQueryBound_pure' _
  | 1, pos, _, msg, sigs => by
    simp only [htRecoverTraceM, one_mul]
    refine (isTotalQueryBound_bind (n₂ := 0) (xmssRecoverTraceM_queryBound pr pos sigs.head msg)
      fun tr => isTotalQueryBound_pure' (tr.xmssRoot, #v[tr])).mono (by omega)
  | layers + 2, pos, hrem, msg, sigs => by
    simp only [htRecoverTraceM]
    refine (isTotalQueryBound_bind (xmssRecoverTraceM_queryBound pr pos sigs.head msg) fun tr =>
      isTotalQueryBound_bind (n₂ := 0)
        (htRecoverTraceM_queryBound (layers + 1) (pos.next (by omega)) _ tr.xmssRoot sigs.tail)
        fun ⟨finalRoot, rest⟩ => isTotalQueryBound_pure' (finalRoot, rest.insertIdx 0 tr)).mono ?_
    ring_nf; omega

/-- Pure 0-query XMSS witness extraction from a single recorded layer trace and `(tbl, u)`. -/
def xmssWitnessFromTrace [DecidableEq pr.Y] (tbl : Adrs → Option pr.Y)
    (u : SlSecAdrs vp → pr.Y) (pos : LayerPosition vp.sl) (honestMsg : pr.Y)
    (tr : XmssLayerTrace pr) : Option (XmssWitness vp.sl.params (prEager pr)) :=
  let leafAdrs := wotsLeafAdrs pos.toAdrs pos.leaf.val
  let honestLeaf := (tbl (wotsPkAdrs leafAdrs)).getD default
  if honestLeaf = tr.wotsPk then
    (wotsWitnessFromTrace pr tbl u leafAdrs tr.msg honestMsg tr.wotsTops tr.wotsTraces).map .wots
  else
    (merkleFindCollisionFromTrace pr (fun z t => (tbl (xmssCellAdrs pos.toAdrs z t)).getD default)
      pos.leaf.val tr.xmssTrace).map fun w => .hCollision w.1 w.2.2

/-- Pure 0-query hypertree witness extraction walking recorded layer traces against `(tbl, u)`. -/
def htWitnessFromTrace [DecidableEq pr.Y] (tbl : Adrs → Option pr.Y)
    (u : SlSecAdrs vp → pr.Y) (pos : LayerPosition vp.sl) :
    (layers : ℕ) → pos.layer.val + layers = vp.sl.params.d →
    pr.Y → Vector (XmssLayerTrace pr) layers → Option (HypertreeWitness vp.sl (prEager pr) layers)
  | 0, _, _, _ => none
  | 1, _, honestMsg, trs =>
    let tr := trs.head
    let honestRoot := (tbl (xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0)).getD default
    if tr.xmssRoot = honestRoot then
      (xmssWitnessFromTrace pr tbl u pos honestMsg tr).map (⟨⟨0, Nat.zero_lt_one⟩, ·⟩)
    else none
  | layers + 2, h, honestMsg, trs =>
    let tr := trs.head
    let honestRoot := (tbl (xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0)).getD default
    if tr.xmssRoot = honestRoot then
      (xmssWitnessFromTrace pr tbl u pos honestMsg tr).map (⟨⟨0, Nat.succ_pos _⟩, ·⟩)
    else
      (htWitnessFromTrace tbl u (pos.next (by omega)) (layers + 1)
          (by simp only [LayerPosition.next_layer_val]; change pos.layer.val + 1 + (layers + 1) = vp.sl.params.d; omega)
          honestRoot trs.tail).map
        fun w => ⟨⟨w.layer.val + 1, Nat.succ_lt_succ w.layer.isLt⟩, w.witness⟩

theorem simulateQ_xmssRecoverTraceM_spec (pk : pr.PkSeed) (pos : LayerPosition vp.sl)
    (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) (msg : pr.Y) :
    let tr := Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sig msg))
    tr.msg = msg ∧
    tr.wotsPk = wotsPkFromSig (prEager pr) sig.wots msg pk (wotsLeafAdrs pos.toAdrs pos.leaf.val) ∧
    tr.xmssRoot = xmssPkFromSig (prEager pr) pos.leaf.val ⟨sig.wots, sig.auth⟩ msg pk pos.toAdrs ∧
    tr.wotsTops = (Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig.wots msg
      (wotsLeafAdrs pos.toAdrs pos.leaf.val)))).2.1 ∧
    tr.wotsTraces = (Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig.wots msg
      (wotsLeafAdrs pos.toAdrs pos.leaf.val)))).2.2 ∧
    tr.xmssTrace = (Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr (xmssNodeAdrs pos.toAdrs)
      pos.leaf.val tr.wotsPk sig.auth.toList))).2 := by
  have hw := simulateQ_wotsRecoverTraceM_spec pr pk sig.wots msg (wotsLeafAdrs pos.toAdrs pos.leaf.val)
  have hm := simulateQ_merkleClimbTraceM_fst pr pk (xmssNodeAdrs pos.toAdrs) pos.leaf.val
    (Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig.wots msg
      (wotsLeafAdrs pos.toAdrs pos.leaf.val)))).1 sig.auth.toList
  have htr_def : Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sig msg)) =
      let wr := Id.run (simulateQ (thRealImpl pr pk) (wotsRecoverTraceM pr sig.wots msg
        (wotsLeafAdrs pos.toAdrs pos.leaf.val)))
      let mr := Id.run (simulateQ (thRealImpl pr pk) (merkleClimbTraceM pr (xmssNodeAdrs pos.toAdrs)
        pos.leaf.val wr.1 sig.auth.toList))
      ⟨msg, wr.1, wr.2.1, wr.2.2, mr.1, mr.2⟩ := by
    unfold xmssRecoverTraceM
    simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure]
  dsimp only
  rw [htr_def]
  refine ⟨rfl, hw.1, ?_, rfl, rfl, rfl⟩
  rw [SLHDSA.xmssPkFromSig_eq_climb]
  dsimp only
  rw [← hw.1]
  exact hm

private theorem tbl_xmssCell_eq_merkleRoot (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tbl : Adrs → Option pr.Y) (htbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl)
    (z t : ℕ) (hzh : z ≤ vp.sl.params.hp) (ht : t < 2 ^ (vp.sl.params.hp - z)) :
    (tbl (xmssCellAdrs pos.toAdrs z t)).getD default =
      PerfectMerkleTree.merkleRoot (xmssLeaf (prEager pr) u pk pos.toAdrs)
        (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs) z t := by
  rcases z with _ | z'
  · have ht' : t < 2 ^ vp.sl.params.hp := by simpa using ht
    let pos' : LayerPosition vp.sl := ⟨pos.layer, pos.tree, ⟨t, ht'⟩⟩
    have hmem : wotsPkAdrs (wotsLeafAdrs pos.toAdrs t) ∈ constructionAddresses vp.sl := by
      rw [mem_constructionAddresses_iff]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      change wotsPkAdrs (wotsLeafAdrs pos'.toAdrs pos'.leaf.val) ∈ wotsPkAddresses vp.sl
      rw [SLHDSA.Security.wotsLeafAdrs_eq_wotsInstanceAdrs pos']
      exact mem_wotsPkAddresses vp.sl pos'
    change (tbl (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))).getD default = _
    rw [htbl _ hmem, Option.getD_some, honestVal_eq_wotsPkGen, ← SLHDSA.xmssLeaf_eq_wotsPkGen]
    rfl
  · have hmem : xmssNodeAdrs pos.toAdrs (z' + 1) t ∈ constructionAddresses vp.sl := by
      rw [mem_constructionAddresses_iff]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [← LayerTreeCoord.ofPosition_toAdrs pos]
      exact mem_xmssNodeAddresses vp.sl (LayerTreeCoord.ofPosition pos) (Nat.succ_pos z') hzh ht
    change (tbl (xmssNodeAdrs pos.toAdrs (z' + 1) t)).getD default = _
    rw [htbl _ hmem, Option.getD_some, honestVal_eq_xmssNode _ _ _ _ (Nat.succ_pos z'),
      SLHDSA.xmssNode_eq_merkleRoot]

/-- Soundness of `xmssWitnessFromTrace`. -/
theorem xmssWitnessFromTrace_sound [DecidableEq pr.Y]
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl)
    (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) (msg honestMsg : pr.Y)
    (hroot : xmssPkFromSig (prEager pr) pos.leaf.val ⟨sig.wots, sig.auth⟩ msg pk pos.toAdrs =
      xmssRoot (prEager pr) u pk pos.toAdrs)
    {w : XmssWitness vp.sl.params (prEager pr)}
    (hw : xmssWitnessFromTrace pr tbl u pos honestMsg
        (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sig msg))) = some w) :
    w.Valid u pk pos.toAdrs pos.leaf.val honestMsg := by
  have htr := simulateQ_xmssRecoverTraceM_spec pr pk pos sig msg
  set tr := Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sig msg))
  have hleaf : (tbl (wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val))).getD default =
      xmssLeaf (prEager pr) u pk pos.toAdrs pos.leaf.val := by
    simpa [xmssCellAdrs] using tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos 0 pos.leaf.val
      (Nat.zero_le _) (by simp)
  unfold xmssWitnessFromTrace at hw
  dsimp only at hw
  rw [hleaf, htr.2.1] at hw
  split at hw
  · rename_i hle
    rw [Option.map_eq_some_iff] at hw
    obtain ⟨ww, hww, rfl⟩ := hw
    rw [XmssWitness.valid_wots]
    rw [htr.1, htr.2.2.2.1, htr.2.2.2.2.1] at hww
    rw [SLHDSA.xmssLeaf_eq_wotsPkGen] at hle
    exact wotsWitnessFromTrace_sound pr pk u tbl htbl pos sig.wots msg honestMsg hle.symm hww
  · rename_i hne
    rw [Option.map_eq_some_iff] at hw
    obtain ⟨mc, hmc, rfl⟩ := hw
    rw [htr.2.2.2.2.2, htr.2.1] at hmc
    have hnh_eq : (fun z t l r => pr.H pk (xmssNodeAdrs pos.toAdrs z t) l r) =
        SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs := rfl
    rw [merkleFindCollisionFromTrace_eq_findCollision pr pk (xmssNodeAdrs pos.toAdrs)
      (xmssLeaf (prEager pr) u pk pos.toAdrs)
      (fun z t => (tbl (xmssCellAdrs pos.toAdrs z t)).getD default) _ _ _ (fun h hp hle_len => by
        have hzh : h ≤ vp.sl.params.hp := by simpa using hle_len
        have hlt_h : pos.leaf.val / 2 ^ h < 2 ^ (vp.sl.params.hp - h) :=
          xmssNodeIndex_lt vp.sl.params pos.leaf.isLt hzh
        have hsub : vp.sl.params.hp - (h - 1) = vp.sl.params.hp - h + 1 := by omega
        have hlt_c0 : 2 * (pos.leaf.val / 2 ^ h) < 2 ^ (vp.sl.params.hp - (h - 1)) := by
          rw [hsub, pow_succ]; omega
        have hlt_c1 : 2 * (pos.leaf.val / 2 ^ h) + 1 < 2 ^ (vp.sl.params.hp - (h - 1)) := by
          rw [hsub, pow_succ]; omega
        exact ⟨tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos h _ hzh hlt_h,
          tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos (h - 1) _ (by omega) hlt_c0,
          tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos (h - 1) _ (by omega) hlt_c1⟩)] at hmc
    rw [hnh_eq] at hmc
    have hclimb : PerfectMerkleTree.climb (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs)
        pos.leaf.val (wotsPkFromSig (prEager pr) sig.wots msg pk (wotsLeafAdrs pos.toAdrs pos.leaf.val))
        sig.auth.toList =
      PerfectMerkleTree.merkleRoot (xmssLeaf (prEager pr) u pk pos.toAdrs)
        (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs) vp.sl.params.hp
        (pos.leaf.val / 2 ^ vp.sl.params.hp) := by
      rw [Nat.div_eq_of_lt pos.leaf.isLt, ← SLHDSA.xmssNode_eq_merkleRoot]
      have hroot' : xmssNode (prEager pr) u pk pos.toAdrs vp.sl.params.hp 0 =
          xmssRoot (prEager pr) u pk pos.toAdrs := by
        rw [← honestVal_eq_xmssRoot]
        exact (honestVal_eq_xmssNode pr pk u pos.toAdrs vp.valid.hp_pos 0).symm
      rw [hroot']
      rw [SLHDSA.xmssPkFromSig_eq_climb] at hroot
      exact hroot
    have hlen : sig.auth.toList.length = vp.sl.params.hp := by simp
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (xmssLeaf (prEager pr) u pk pos.toAdrs) (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs)
      vp.sl.params.hp pos.leaf.val _ _ hlen hclimb hne
    rw [hor, Option.some.injEq] at hmc
    subst hmc
    obtain ⟨hzpos, hzle, hcne, hcoll⟩ := PerfectMerkleTree.findCollision_sound
      (xmssLeaf (prEager pr) u pk pos.toAdrs) (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs)
      vp.sl.params.hp pos.leaf.val _ _ hlen z _ c hor
    rw [XmssWitness.valid_hCollision]
    refine ⟨hzpos, hzle, ?_, ?_⟩
    · rw [xmssHonestChildren_eq]
      simpa only [PerfectMerkleTree.honestChildren, SLHDSA.xmssNode_eq_merkleRoot] using hcne
    · rw [xmssHonestChildren_eq]
      change SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs z (pos.leaf.val / 2 ^ z) _ _ =
        SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs z (pos.leaf.val / 2 ^ z) c.1 c.2
      simpa only [PerfectMerkleTree.honestChildren, SLHDSA.xmssNode_eq_merkleRoot] using hcoll

/-- Completeness of `xmssWitnessFromTrace`. -/
theorem xmssWitnessFromTrace_isSome [DecidableEq pr.Y]
    (hinj : Function.Injective pr.yToBytes)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl)
    (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) (msg honestMsg : pr.Y)
    (hne : msg ≠ honestMsg)
    (hroot : xmssPkFromSig (prEager pr) pos.leaf.val ⟨sig.wots, sig.auth⟩ msg pk pos.toAdrs =
      xmssRoot (prEager pr) u pk pos.toAdrs) :
    (xmssWitnessFromTrace pr tbl u pos honestMsg
      (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sig msg)))).isSome = true := by
  have htr := simulateQ_xmssRecoverTraceM_spec pr pk pos sig msg
  set tr := Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sig msg))
  have hleaf : (tbl (wotsPkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val))).getD default =
      xmssLeaf (prEager pr) u pk pos.toAdrs pos.leaf.val := by
    simpa [xmssCellAdrs] using tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos 0 pos.leaf.val
      (Nat.zero_le _) (by simp)
  unfold xmssWitnessFromTrace
  dsimp only
  rw [hleaf, htr.2.1]
  split_ifs with hle
  · rw [Option.isSome_map, htr.1, htr.2.2.2.1, htr.2.2.2.2.1]
    exact wotsWitnessFromTrace_isSome pr hinj pk u tbl htbl pos sig.wots msg honestMsg hne
  · rw [Option.isSome_map, htr.2.2.2.2.2, htr.2.1]
    have hnh_eq : (fun z t l r => pr.H pk (xmssNodeAdrs pos.toAdrs z t) l r) =
        SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs := rfl
    rw [merkleFindCollisionFromTrace_eq_findCollision pr pk (xmssNodeAdrs pos.toAdrs)
      (xmssLeaf (prEager pr) u pk pos.toAdrs)
      (fun z t => (tbl (xmssCellAdrs pos.toAdrs z t)).getD default) _ _ _ (fun h hp hle_len => by
        have hzh : h ≤ vp.sl.params.hp := by simpa using hle_len
        have hlt_h : pos.leaf.val / 2 ^ h < 2 ^ (vp.sl.params.hp - h) :=
          xmssNodeIndex_lt vp.sl.params pos.leaf.isLt hzh
        have hsub : vp.sl.params.hp - (h - 1) = vp.sl.params.hp - h + 1 := by omega
        have hlt_c0 : 2 * (pos.leaf.val / 2 ^ h) < 2 ^ (vp.sl.params.hp - (h - 1)) := by
          rw [hsub, pow_succ]; omega
        have hlt_c1 : 2 * (pos.leaf.val / 2 ^ h) + 1 < 2 ^ (vp.sl.params.hp - (h - 1)) := by
          rw [hsub, pow_succ]; omega
        exact ⟨tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos h _ hzh hlt_h,
          tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos (h - 1) _ (by omega) hlt_c0,
          tbl_xmssCell_eq_merkleRoot pr pk u tbl htbl pos (h - 1) _ (by omega) hlt_c1⟩)]
    rw [hnh_eq]
    have hclimb : PerfectMerkleTree.climb (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs)
        pos.leaf.val (wotsPkFromSig (prEager pr) sig.wots msg pk (wotsLeafAdrs pos.toAdrs pos.leaf.val))
        sig.auth.toList =
      PerfectMerkleTree.merkleRoot (xmssLeaf (prEager pr) u pk pos.toAdrs)
        (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs) vp.sl.params.hp
        (pos.leaf.val / 2 ^ vp.sl.params.hp) := by
      rw [Nat.div_eq_of_lt pos.leaf.isLt, ← SLHDSA.xmssNode_eq_merkleRoot]
      have hroot' : xmssNode (prEager pr) u pk pos.toAdrs vp.sl.params.hp 0 =
          xmssRoot (prEager pr) u pk pos.toAdrs := by
        rw [← honestVal_eq_xmssRoot]
        exact (honestVal_eq_xmssNode pr pk u pos.toAdrs vp.valid.hp_pos 0).symm
      rw [hroot']
      rw [SLHDSA.xmssPkFromSig_eq_climb] at hroot
      exact hroot
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (xmssLeaf (prEager pr) u pk pos.toAdrs) (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs)
      vp.sl.params.hp pos.leaf.val _ _ (by simp) hclimb hle
    rw [hor]; rfl

private theorem vector_head_insertIdx_zero {α : Type} {n : ℕ} (a : α) (v : Vector α n) :
    (v.insertIdx 0 a).head = a := by
  simp [Vector.head]

private theorem vector_tail_insertIdx_zero {α : Type} {n : ℕ} (a : α) (v : Vector α n) :
    (v.insertIdx 0 a).tail = v := by
  apply Vector.ext; intro i hi
  simp [Vector.tail_eq_cast_extract]

/-- Specification, soundness, and completeness of `htRecoverTraceM` + `htWitnessFromTrace`. -/
theorem simulateQ_htRecoverTraceM_spec (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tbl : Adrs → Option pr.Y) (htbl : TblComplete pr pk u tbl) :
    ∀ (layers : ℕ) (pos : LayerPosition vp.sl) (hrem : pos.layer.val + layers = vp.sl.params.d)
      (msg honestMsg : pr.Y) (sigs : Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers),
      let r := Id.run (simulateQ (thRealImpl pr pk) (htRecoverTraceM pr pos layers hrem msg sigs))
      r.1 = SLHDSA.GeneralHypertree.recoverFromPosition vp.sl (prEager pr) pk pos layers hrem msg
        (sigs.map fun x => ⟨x.wots, x.auth⟩) ∧
      (∀ [DecidableEq pr.Y] {w : HypertreeWitness vp.sl (prEager pr) layers},
        htWitnessFromTrace pr tbl u pos layers hrem honestMsg r.2 = some w →
        w.Valid u pk pos honestMsg layers hrem) ∧
      (∀ [DecidableEq pr.Y], Function.Injective pr.yToBytes →
        msg ≠ honestMsg →
        r.1 = xmssRoot (prEager pr) u pk (SLHDSA.GeneralHypertree.layerAdrs (vp.sl.params.d - 1) 0) →
        (htWitnessFromTrace pr tbl u pos layers hrem honestMsg r.2).isSome = true) := by
  intro layers
  induction layers using Nat.twoStepInduction with
  | zero =>
    intro pos hrem msg honestMsg sigs
    refine ⟨rfl, fun h => by simp [htWitnessFromTrace] at h, fun _ _ _ => ?_⟩
    have := pos.layer.isLt; omega
  | one =>
    intro pos hrem msg honestMsg sigs
    have htr := simulateQ_xmssRecoverTraceM_spec pr pk pos sigs.head msg
    have hhead : (sigs.map fun x => (⟨x.wots, x.auth⟩ : SLHDSA.XmssSig vp.sl.params (prEager pr).core)).head =
        ⟨sigs.head.wots, sigs.head.auth⟩ := by simp [Vector.head]
    have hrootMem : xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0 ∈ constructionAddresses vp.sl := by
      rw [mem_constructionAddresses_iff]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [← LayerTreeCoord.ofPosition_toAdrs pos]
      exact mem_xmssNodeAddresses vp.sl (LayerTreeCoord.ofPosition pos) vp.valid.hp_pos le_rfl (by simp)
    have hhonRoot : (tbl (xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0)).getD default =
        xmssRoot (prEager pr) u pk pos.toAdrs := by
      rw [htbl _ hrootMem, Option.getD_some, honestVal_eq_xmssRoot]
    have hr1 : (Id.run (simulateQ (thRealImpl pr pk) (htRecoverTraceM pr pos 1 hrem msg sigs))).1 =
        SLHDSA.GeneralHypertree.recoverFromPosition vp.sl (prEager pr) pk pos 1 hrem msg
          (sigs.map fun x => ⟨x.wots, x.auth⟩) := by
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        SLHDSA.GeneralHypertree.recoverFromPosition, hhead]
      exact htr.2.2.1
    refine ⟨hr1, ?_, ?_⟩
    · intro _ w hw
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        htWitnessFromTrace, Vector.head, hhonRoot] at hw
      change (if (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sigs.head msg))).xmssRoot =
            xmssRoot (prEager pr) u pk pos.toAdrs then _ else _) = some w at hw
      rw [htr.2.2.1] at hw
      split at hw
      · rename_i hrm
        rw [Option.map_eq_some_iff] at hw
        obtain ⟨xw, hxw, rfl⟩ := hw
        rw [HypertreeWitness.valid_iff]
        simp only [LayerPosition.advance_zero, honestLayerMsg_zero]
        exact xmssWitnessFromTrace_sound pr pk u tbl htbl pos sigs.head msg honestMsg hrm hxw
      · cases hw
    · intro _ hinj hne htop
      have hlay : pos.layer.val = vp.sl.params.d - 1 := by omega
      have htr0 : pos.tree.val = 0 := by
        have hh : SLHDSA.layerTreeHeight vp.sl pos.layer.val = 0 := by
          simp only [SLHDSA.layerTreeHeight, hlay, Nat.mul_eq_zero]
          left; have := vp.valid.d_pos
          change vp.params.slParams.d - (vp.params.slParams.d - 1 + 1) = 0; omega
        have hlt' : pos.tree.val < 2 ^ 0 := hh ▸ pos.tree.isLt
        omega
      have hadrs : pos.toAdrs = SLHDSA.GeneralHypertree.layerAdrs (vp.sl.params.d - 1) 0 := by
        simp [LayerPosition.toAdrs, SLHDSA.GeneralHypertree.layerAdrs, hlay, htr0]
      have hrm : xmssPkFromSig (prEager pr) pos.leaf.val ⟨sigs.head.wots, sigs.head.auth⟩ msg pk pos.toAdrs =
          xmssRoot (prEager pr) u pk pos.toAdrs := by
        rw [hr1, SLHDSA.GeneralHypertree.recoverFromPosition, hhead] at htop
        rw [← hadrs] at htop; exact htop
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        htWitnessFromTrace, hhonRoot]
      have hhd_tr : (#v[Id.run (simulateQ (thRealImpl pr pk)
          (xmssRecoverTraceM pr pos sigs.head msg))]).head =
          Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sigs.head msg)) := rfl
      rw [hhd_tr, htr.2.2.1, ite_eq_left hrm, Option.isSome_map]
      exact xmssWitnessFromTrace_isSome pr hinj pk u tbl htbl pos sigs.head msg honestMsg hne hrm
  | more layers _ ih =>
    intro pos hrem msg honestMsg sigs
    have htr := simulateQ_xmssRecoverTraceM_spec pr pk pos sigs.head msg
    set tr := Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr pos sigs.head msg))
    have hhead : (sigs.map fun x => (⟨x.wots, x.auth⟩ : SLHDSA.XmssSig vp.sl.params (prEager pr).core)).head =
        ⟨sigs.head.wots, sigs.head.auth⟩ := by simp [Vector.head]
    have htail : (sigs.map fun x => (⟨x.wots, x.auth⟩ : SLHDSA.XmssSig vp.sl.params (prEager pr).core)).tail =
        sigs.tail.map fun x => ⟨x.wots, x.auth⟩ := by
      apply Vector.ext; intro i hi; simp [Vector.tail_eq_cast_extract]
    have hrootMem : xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0 ∈ constructionAddresses vp.sl := by
      rw [mem_constructionAddresses_iff]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [← LayerTreeCoord.ofPosition_toAdrs pos]
      exact mem_xmssNodeAddresses vp.sl (LayerTreeCoord.ofPosition pos) vp.valid.hp_pos le_rfl (by simp)
    have hhonRoot : (tbl (xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0)).getD default =
        xmssRoot (prEager pr) u pk pos.toAdrs := by
      rw [htbl _ hrootMem, Option.getD_some, honestVal_eq_xmssRoot]
    have hnext_rem : (pos.next (by omega)).layer.val + (layers + 1) = vp.sl.params.d := by
      simp only [LayerPosition.next_layer_val]
      change pos.layer.val + 1 + (layers + 1) = vp.sl.params.d; omega
    have hnext_spec := ih (pos.next (by omega)) hnext_rem tr.xmssRoot
      (xmssRoot (prEager pr) u pk pos.toAdrs) sigs.tail
    have hr1 : (Id.run (simulateQ (thRealImpl pr pk) (htRecoverTraceM pr pos (layers + 2) hrem msg sigs))).1 =
        SLHDSA.GeneralHypertree.recoverFromPosition vp.sl (prEager pr) pk pos (layers + 2) hrem msg
          (sigs.map fun x => ⟨x.wots, x.auth⟩) := by
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        SLHDSA.GeneralHypertree.recoverFromPosition, hhead, htail]
      rw [← htr.2.2.1]
      exact hnext_spec.1
    refine ⟨hr1, ?_, ?_⟩
    · intro _ w hw
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        htWitnessFromTrace, vector_head_insertIdx_zero, vector_tail_insertIdx_zero, hhonRoot] at hw
      change (if tr.xmssRoot = xmssRoot (prEager pr) u pk pos.toAdrs then _ else _) = some w at hw
      by_cases hrm : tr.xmssRoot = xmssRoot (prEager pr) u pk pos.toAdrs
      · rw [ite_eq_left hrm, Option.map_eq_some_iff] at hw
        obtain ⟨xw, hxw, rfl⟩ := hw
        rw [HypertreeWitness.valid_iff]
        simp only [LayerPosition.advance_zero, honestLayerMsg_zero]
        exact xmssWitnessFromTrace_sound pr pk u tbl htbl pos sigs.head msg honestMsg
          (htr.2.2.1.symm.trans hrm) hxw
      · rw [ite_eq_right hrm, Option.map_eq_some_iff] at hw
        obtain ⟨hw', hhw', rfl⟩ := hw
        have hval := hnext_spec.2.1 hhw'
        rw [HypertreeWitness.valid_iff] at hval ⊢
        simp only [LayerPosition.advance_next]
        rw [honestLayerMsg_next vp.sl (prEager pr) u pk pos honestMsg hw'.layer.val _]
        exact hval
    · intro _ hinj hne htop
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        htWitnessFromTrace, vector_head_insertIdx_zero, vector_tail_insertIdx_zero, hhonRoot]
      by_cases hrm : tr.xmssRoot = xmssRoot (prEager pr) u pk pos.toAdrs
      · rw [ite_eq_left hrm, Option.isSome_map]
        exact xmssWitnessFromTrace_isSome pr hinj pk u tbl htbl pos sigs.head msg honestMsg hne
          (htr.2.2.1.symm.trans hrm)
      · rw [ite_eq_right hrm, Option.isSome_map]
        have htop' : (Id.run (simulateQ (thRealImpl pr pk)
            (htRecoverTraceM pr (pos.next (by omega)) (layers + 1) hnext_rem tr.xmssRoot sigs.tail))).1 =
            xmssRoot (prEager pr) u pk (SLHDSA.GeneralHypertree.layerAdrs (vp.sl.params.d - 1) 0) := by
          simpa only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure] using htop
        exact hnext_spec.2.2 hinj hrm htop'

/-- **Single-pass explicit-`Th_λ`-oracle verification + table-driven witness extraction**:
computes `(verifyInternal vp.sl pr.toSLHDSA msg sig ⟨pk, pkSl⟩, witness)` in at most
`Vsl vp.params` (`= 2741`) tweakable-hash queries! -/
def verifyAndExtractTableM [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (sig : Stateless.Sig pr) (target : Fin vp.sl.params.k) :
    OracleComp (thSpec pr) (Bool × Option (Witness vp.sl (prEager pr))) := do
  let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  let (forsPk, forsTrees) ← forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs
  let (finalRoot, htTraces) ← htRecoverTraceM pr (LayerPosition.initial vp.sl parts)
    vp.sl.params.d (by simp) forsPk sig.hypertree
  let verified := decide (finalRoot = pkSl)
  let honestForsPk := (tbl (forsPkAdrs parts.forsAdrs)).getD default
  let wit : Option (Witness vp.sl (prEager pr)) :=
    if forsPk = honestForsPk then
      some (.fors (forsWitnessFromTrace pr tbl sig.fors parts.md.toList parts.forsAdrs forsTrees target))
    else
      (htWitnessFromTrace pr tbl u (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
        honestForsPk htTraces).map .hypertree
  return (verified, wit)

/-- **Query bound (`≤ Vsl`)**: `verifyAndExtractTableM` makes at most
`Vsl vp.params = k(a+1) + 1 + d(smax + h' + 1)` (`= 2741`) tweakable-hash queries on every path. -/
theorem verifyAndExtractTableM_queryBound [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (sig : Stateless.Sig pr) (target : Fin vp.sl.params.k) :
    IsTotalQueryBound (verifyAndExtractTableM pr pk pkSl tbl u msg sig target) (Vsl vp.params) := by
  unfold verifyAndExtractTableM Vsl
  refine (isTotalQueryBound_bind (forsRecoverTraceM_queryBound pr sig.fors _ _) fun ⟨forsPk, forsTrees⟩ =>
    isTotalQueryBound_bind (n₂ := 0)
      (htRecoverTraceM_queryBound pr vp.sl.params.d _ _ forsPk sig.hypertree) fun ⟨finalRoot, htTraces⟩ => by
        dsimp only
        exact isTotalQueryBound_pure' _).mono ?_
  dsimp only [ValidatedParams.sl, Params.slParams]
  omega

/-- Deterministic simulation of `verifyAndExtractTableM` under `thRealImpl pr pk`. -/
noncomputable def verifyAndExtractTable [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (sig : Stateless.Sig pr) (target : Fin vp.sl.params.k) :
    Bool × Option (Witness vp.sl (prEager pr)) :=
  Id.run (simulateQ (thRealImpl pr pk) (verifyAndExtractTableM pr pk pkSl tbl u msg sig target))

/-- First component of `verifyAndExtractTable` equals `SLHDSA.GeneralScheme.verifyInternal`
identically. -/
theorem verifyAndExtractTable_fst [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (htbl : TblComplete pr pk u tbl) (msg : List Byte) (sig : Stateless.Sig pr)
    (target : Fin vp.sl.params.k) :
    (verifyAndExtractTable pr pk pkSl tbl u msg sig target).1 =
      SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA msg sig ⟨pk, pkSl⟩ := by
  unfold verifyAndExtractTable verifyAndExtractTableM
  simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure]
  set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  have hfors := simulateQ_forsRecoverTraceM_spec pr pk sig.fors parts.md.toList parts.forsAdrs
  set fr := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))
  have hht := simulateQ_htRecoverTraceM_spec pr pk u tbl htbl vp.sl.params.d
    (LayerPosition.initial vp.sl parts) (by simp) fr.1 (forsPkGen (prEager pr) u pk parts.forsAdrs)
    sig.hypertree
  rw [← verifyInternal_prEager_eq, SLHDSA.GeneralScheme.verifyInternal_eq_decide]
  change decide ((Id.run (simulateQ (thRealImpl pr pk)
      (htRecoverTraceM pr (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
        fr.1 sig.hypertree))).1 = pkSl) =
    decide (SLHDSA.GeneralHypertree.pkFromSig vp.sl (prEager pr)
      (forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs)
      (toEagerSig pr sig).hypertree pk parts = pkSl)
  rw [SLHDSA.GeneralHypertree.pkFromSig_eq_recoverFromPosition, hht.1, hfors.1]
  rfl

/-- On the FORS arm (`forsPkFromSig = forsPkGen`), `verifyAndExtractTable.2` equals
`some (.fors (slFindForsWitness ...))`. -/
theorem verifyAndExtractTable_snd_of_forsPk_eq [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (htbl : TblComplete pr pk u tbl) (msg : List Byte) (sig : Stateless.Sig pr)
    (target : Fin vp.sl.params.k)
    (hfp : let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
      forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
        forsPkGen (prEager pr) u pk parts.forsAdrs) :
    (verifyAndExtractTable pr pk pkSl tbl u msg sig target).2 =
      let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
      some (.fors (slFindForsWitness pr (toEagerSig pr sig).fors parts.md.toList u pk
        parts.forsAdrs target)) := by
  unfold verifyAndExtractTable verifyAndExtractTableM
  simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure]
  set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  have hfors := simulateQ_forsRecoverTraceM_spec pr pk sig.fors parts.md.toList parts.forsAdrs
  have hforsPkMem : forsPkAdrs parts.forsAdrs ∈ constructionAddresses vp.sl := by
    rw [mem_constructionAddresses_iff]
    exact Or.inr (Or.inr (Or.inl (mem_forsRootAddresses_of_parts parts)))
  have hhonForsPk : (tbl (forsPkAdrs parts.forsAdrs)).getD default =
      forsPkGen (prEager pr) u pk parts.forsAdrs := by
    rw [htbl _ hforsPkMem, Option.getD_some, honestVal_eq_forsPkGen]
  rw [hhonForsPk]
  have hfp' : (Id.run (simulateQ (thRealImpl pr pk)
      (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))).1 =
      forsPkGen (prEager pr) u pk parts.forsAdrs := by
    rw [hfors.1]; exact hfp
  rw [ite_eq_left hfp']
  congr 2
  exact forsWitnessFromTrace_eq_slFindForsWitness pr pk u tbl htbl parts sig.fors target

/-- On the hypertree arm (`forsPkFromSig ≠ forsPkGen`), `verifyAndExtractTable.2` returns
`Option.map .hypertree (htWitnessFromTrace ...)`. -/
theorem verifyAndExtractTable_snd_of_forsPk_ne [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (htbl : TblComplete pr pk u tbl) (msg : List Byte) (sig : Stateless.Sig pr)
    (target : Fin vp.sl.params.k)
    (hfp : let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
      forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs ≠
        forsPkGen (prEager pr) u pk parts.forsAdrs) :
    let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
    let fr := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))
    let htr := Id.run (simulateQ (thRealImpl pr pk)
      (htRecoverTraceM pr (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp) fr.1 sig.hypertree))
    (verifyAndExtractTable pr pk pkSl tbl u msg sig target).2 =
      (htWitnessFromTrace pr tbl u (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
        (forsPkGen (prEager pr) u pk parts.forsAdrs) htr.2).map .hypertree := by
  unfold verifyAndExtractTable verifyAndExtractTableM
  simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure]
  set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  have hfors := simulateQ_forsRecoverTraceM_spec pr pk sig.fors parts.md.toList parts.forsAdrs
  have hforsPkMem : forsPkAdrs parts.forsAdrs ∈ constructionAddresses vp.sl := by
    rw [mem_constructionAddresses_iff]
    exact Or.inr (Or.inr (Or.inl (mem_forsRootAddresses_of_parts parts)))
  have hhonForsPk : (tbl (forsPkAdrs parts.forsAdrs)).getD default =
      forsPkGen (prEager pr) u pk parts.forsAdrs := by
    rw [htbl _ hforsPkMem, Option.getD_some, honestVal_eq_forsPkGen]
  rw [hhonForsPk]
  have hfp' : (Id.run (simulateQ (thRealImpl pr pk)
      (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))).1 ≠
      forsPkGen (prEager pr) u pk parts.forsAdrs := by
    rw [hfors.1]; exact hfp
  rw [ite_eq_right hfp']

/-- **Soundness of `verifyAndExtractTable`**: under `TblComplete pr pk u tbl`, any witness
returned by `verifyAndExtractTable` satisfies `Witness.Valid`. -/
theorem verifyAndExtractTable_sound [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl : pr.Y)
    (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (htbl : TblComplete pr pk u tbl) (msg : List Byte) (sig : Stateless.Sig pr)
    (target : Fin vp.sl.params.k) {w : Witness vp.sl (prEager pr)}
    (hw : (verifyAndExtractTable pr pk pkSl tbl u msg sig target).2 = some w) :
    w.Valid u ⟨pk, pkSl⟩ msg (toEagerSig pr sig) := by
  set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  have hparts : schemeParts vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, pkSl⟩ = parts :=
    schemeParts_eq vp.sl (prEager pr) msg (toEagerSig pr sig) ⟨pk, pkSl⟩
  by_cases hfp : forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
      forsPkGen (prEager pr) u pk parts.forsAdrs
  · rw [verifyAndExtractTable_snd_of_forsPk_eq pr pk pkSl tbl u htbl msg sig target hfp,
      Option.some.injEq] at hw
    subst hw
    rw [Witness.valid_fors, hparts]
    exact slFindForsWitness_sound pr _ _ u pk _ _ hfp
  · rw [verifyAndExtractTable_snd_of_forsPk_ne pr pk pkSl tbl u htbl msg sig target hfp,
      Option.map_eq_some_iff] at hw
    obtain ⟨hw', hhw', rfl⟩ := hw
    rw [Witness.valid_hypertree, hparts]
    set fr := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))
    have hht := simulateQ_htRecoverTraceM_spec pr pk u tbl htbl vp.sl.params.d
      (LayerPosition.initial vp.sl parts) (by simp) fr.1 (forsPkGen (prEager pr) u pk parts.forsAdrs)
      sig.hypertree
    exact hht.2.1 hhw'

/-- **Completeness of `verifyAndExtractTable`**: under `hinj`, `TblComplete pr pk u tbl`, and
`pkSl = slRootDet pr pk u`, every verifying forgery yields a witness (`isSome = true`). -/
theorem verifyAndExtractTable_isSome [DecidableEq pr.Y]
    (hinj : Function.Injective pr.yToBytes)
    (pk : pr.PkSeed) (tbl : Adrs → Option pr.Y) (u : SlSecAdrs vp → pr.Y)
    (htbl : TblComplete pr pk u tbl) (msg : List Byte) (sig : Stateless.Sig pr)
    (target : Fin vp.sl.params.k)
    (hver : SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA msg sig ⟨pk, slRootDet pr pk u⟩ = true) :
    ((verifyAndExtractTable pr pk (slRootDet pr pk u) tbl u msg sig target).2).isSome = true := by
  set pkSl := slRootDet pr pk u
  set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  by_cases hfp : forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs =
      forsPkGen (prEager pr) u pk parts.forsAdrs
  · rw [verifyAndExtractTable_snd_of_forsPk_eq pr pk pkSl tbl u htbl msg sig target hfp]
    rfl
  · rw [verifyAndExtractTable_snd_of_forsPk_ne pr pk pkSl tbl u htbl msg sig target hfp,
      Option.isSome_map]
    have hfors := simulateQ_forsRecoverTraceM_spec pr pk sig.fors parts.md.toList parts.forsAdrs
    set fr := Id.run (simulateQ (thRealImpl pr pk) (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))
    have hht := simulateQ_htRecoverTraceM_spec pr pk u tbl htbl vp.sl.params.d
      (LayerPosition.initial vp.sl parts) (by simp) fr.1 (forsPkGen (prEager pr) u pk parts.forsAdrs)
      sig.hypertree
    have htop : (Id.run (simulateQ (thRealImpl pr pk)
        (htRecoverTraceM pr (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
          fr.1 sig.hypertree))).1 =
        xmssRoot (prEager pr) u pk (SLHDSA.GeneralHypertree.layerAdrs (vp.sl.params.d - 1) 0) := by
      rw [hht.1, hfors.1]
      rw [← verifyInternal_prEager_eq, SLHDSA.GeneralScheme.verifyInternal_eq_decide,
        decide_eq_true_eq] at hver
      have hroot : SLHDSA.GeneralHypertree.pkFromSig vp.sl (prEager pr)
          (forsPkFromSig (prEager pr) (toEagerSig pr sig).fors parts.md.toList pk parts.forsAdrs)
          (toEagerSig pr sig).hypertree pk parts =
          SLHDSA.GeneralHypertree.root vp.sl (prEager pr) u pk := by
        rw [← slRootDet_eq_prEager_root]
        exact hver
      rw [SLHDSA.GeneralHypertree.pkFromSig_eq_recoverFromPosition,
        SLHDSA.GeneralHypertree.root_eq_xmssRoot] at hroot
      exact hroot
    exact hht.2.2 hinj (by rw [hfors.1]; exact hfp) htop

end FullExtract

end ShrincsSecurity.Slhdsa

end
