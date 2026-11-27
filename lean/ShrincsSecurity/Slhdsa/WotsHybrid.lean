module

public import ShrincsSecurity.Slhdsa.TableExtract
public import ShrincsSecurity.Fxmss.HybCommon

/-!
# Stateless SLH-DSA WOTS-TW hybrid (`WotsHybrid.lean`)

Bottom-up layer-by-layer WOTS-TW hybrid argument for the stateless SLH-DSA hypertree, used by
both Main Paper **Claim 4.16** (`Shrincs/Claim416.lean`) and Main Paper **Theorem 4.3**
(`Slhdsa/Theorem43.lean`).

## Architecture

1. **`SfStage1`**: generic hook for optional Stage-1 stateful `O_coll` precomputation (trivial
   `Unit` for standalone SLH-DSA Theorem 4.3; `Bridge.sfPrecompM` for SHRINCS Claim 4.16). All
   stateful queries touch only `Scheme.IsStateful` tweaks, leaving every stateless tweak fresh.
2. **`HybTree` & `buildHybTreeM`**: unified bottom-up builder that constructs FORS (types 3–4),
   then layers `ℓ = 0, …, d - 1` of the hypertree (WOTS chains, WOTS public keys, XMSS trees).
   At layer `ℓ`, the honest WOTS message `wotsMsg pos` is already present in the table (FORS pk
   at layer `0`; child XMSS root at layer `ℓ > 0`). Instantiating the chain-start callback gives:
   * `hybTreeDet pr γ pk u` (deterministic hybrid `γ`, reading `u`),
   * `hybTreeProb pr γ pk u` (probabilistic hybrid `γ`, sampling WOTS chain seeds fresh on the fly),
   * `udBuildM pr γ u` (Stage-1 `SM-UD` builder for `F ∈ Th_λ`, `q₂ = wotsInstanceCount * len`),
   * `preBuildM pr u` (Stage-1 `SM-PRE` builder for `F ∈ Th_λ`, `q₂ = wotsInstanceCount * len`).
3. **Keyless Stage-2 signing & extraction**:
   * `hybSign`: zero-`Th_λ` Stage-2 signer reading `u` only at `FORS_PRF` (`type = 6`) and reading
     WOTS signatures and auth paths from `HybTree`. At `γ = 0`, `hybSign = slSignDet`.
   * `findHybWotsPre`: single-pass keyless WOTS-preimage extractor built on `TableExtract`
     (`≤ Vsl vp.params` `Th_λ` queries, zero secret keys, zero calls to opaque `findWotsWitness`).
     At `γ = 0`, it succeeds whenever `verifyAndExtractTable` verifies and returns a
     `.hypertree ⟨ℓ, .wots (.fPreimage c step val)⟩` witness.
4. **Master bound `wotsPre_bound`**: for any Stage-2 interaction ignoring `u` at `WOTS_PRF`
   (`type = 5`),
   `Pr_{Hyb(0)}[IsHybWotsPre] ≤ ∑_{γ < w - 2} Adv^{sm-ud}(B_ud γ) + Succ^{sm-pre}(B_pre)`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Slhdsa

open Scheme Shrincs SLHDSA.Security
open SLHDSA (Adrs AddrType Byte wotsSkAdrs wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsSkAdrs forsNodeAdrs forsPkAdrs chainStepsCore chainStepsCore_le
  xmssPkFromSig wotsPkFromSig forsPkFromSig forsIdx WotsSig XmssSig ForsSigCore HtSigCore
  LayerPosition DigestParts splitDigest layerTreeHeight)
open Fxmss.Rom (probUD probPre)
open Fxmss.Rom.Hyb (FSpec)

/-! ## 1. Generic Stage-1 stateful `O_coll` precomputation hook -/

section SfStage1

/-- Generic hook for an optional Stage-1 stateful `O_coll` precomputation (trivial for standalone
SLH-DSA Theorem 4.3; `Bridge.sfPrecompM` for SHRINCS Claim 4.16). -/
structure SfStage1 {vp : ValidatedParams} (pr : Primitives vp.params) (D E : Type) where
  /-- Setup distribution sampled before `PK.seed` is revealed. -/
  g₁ : ProbComp D
  /-- Deterministic Stage-1 stateful precomputed value for `(d, pk)`. -/
  sfDet : D → pr.PkSeed → E
  /-- Stage-1 oracle computation via any `O_coll` caller. -/
  sfRun : ∀ {ι : Type} {spec : OracleSpec ι},
    ((i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y) →
    D → OracleComp spec E
  /-- Every `O_coll` call made by `sfRun` is at a `Scheme.IsStateful` address, and when those
  calls are answered faithfully by `pr.memberEval pk`, `sfRun` deterministically outputs
  `sfDet d pk`. -/
  sfRun_spec : ∀ {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (pk : pr.PkSeed) (Inv : σ → Prop) (step : σ → Adrs → σ),
    (∀ i a msg s, Scheme.IsStateful a → Inv s →
      (simulateQ impl (collCall i a msg)).run s = pure (pr.memberEval i pk a msg, step s a)) →
    (∀ s a, Inv s → Scheme.IsStateful a → Inv (step s a)) →
    ∀ d ∈ support g₁, ∀ s, Inv s →
      ∃ s', Inv s' ∧ (simulateQ impl (sfRun collCall d)).run s = pure (sfDet d pk, s')

/-- Trivial `SfStage1` with no stateful part (used by standalone SLH-DSA Theorem 4.3). -/
def SfStage1.unit {vp : ValidatedParams} (pr : Primitives vp.params) : SfStage1 pr Unit Unit where
  g₁ := pure ()
  sfDet _ _ := ()
  sfRun _ _ := pure ()
  sfRun_spec _ _ _ _ _ _ _ _ _ s hs := ⟨s, hs, by simp⟩

end SfStage1

/-! ## 3. Uniform table splitting & single-entry resampling helper -/

section ResampleHelpers

/-- Splitting a uniform table `u : α → β` along a decidable predicate `P`: sampling `u` once has
the same distribution as sampling independent `u₁, u₂` and taking `u₂` on `P`, `u₁` off `P`. -/
theorem uniform_split_pred {α β γ : Type} [Fintype α] [DecidableEq α] [SampleableType β]
    (P : α → Prop) [DecidablePred P] (f : (α → β) → ProbComp γ) :
    ($ᵗ (α → β) >>= f) =ᵈ
      ($ᵗ (α → β) >>= fun u₁ => $ᵗ (α → β) >>= fun u₂ =>
        f (fun a => if P a then u₂ a else u₁ a)) := by
  have hS : ∀ (S : Finset α) (g : (α → β) → ProbComp γ),
      ($ᵗ (α → β) >>= g) =ᵈ
        ($ᵗ (α → β) >>= fun u₁ => $ᵗ (α → β) >>= fun u₂ =>
          g (fun a => if a ∈ S then u₂ a else u₁ a)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro g
      simp only [Finset.notMem_empty, ↓reduceIte]
      refine EvalDistEq.bind_right _ fun u₁ => ?_
      exact (EvalDistEq.bind_const ($ᵗ (α → β)) (g u₁)).symm
    | insert x S hx ih =>
      intro g
      refine (ih g).trans ?_
      refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.trans (EvalDistEq.bind_right _ fun u₂ =>
        (Repro.resample x (fun u₁ => g (fun a => if a ∈ S then u₂ a else u₁ a))).symm) ?_
      have hupd : ∀ (u₂ u₁ : α → β) (y : β),
          (fun a => if a ∈ S then u₂ a else Function.update u₁ x y a) =
          (fun a => if a ∈ insert x S then Function.update u₂ x y a else u₁ a) := by
        intro u₂ u₁ y; funext a
        by_cases hax : a = x
        · subst hax; simp [hx]
        · simp [hax]
      simp only [hupd]
      refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y =>
        EvalDistEq.bind_bind_swap _ _ _) ?_
      refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.bind_right _ fun u₁ => ?_
      exact Repro.resample x (fun u₂ => g (fun a => if a ∈ insert x S then u₂ a else u₁ a))
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    hS (Finset.univ.filter P) f

end ResampleHelpers

/-! ## 4. Hybrid virtual hypertree (`HybTree`) and unified bottom-up builder -/

section HybTree

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- State of a WOTS-TW hybrid virtual hypertree: top root `PK.sl`, node table for FORS (types 3–4)
and WOTS pk / XMSS internal nodes (types 1–2), honest WOTS message at every `LayerPosition`, and
honest WOTS signature block vector at every `LayerPosition`. -/
structure HybTree where
  /-- Top-layer XMSS root (`PK.sl`). -/
  pkSl : pr.Y
  /-- Precomputed FORS nodes (types 3–4), WOTS public keys (type 1), and XMSS nodes (type 2). -/
  tbl : Adrs → Option pr.Y
  /-- Message signed by the WOTS+ instance at `pos` (FORS pk at layer 0; child XMSS root above). -/
  wotsMsg : LayerPosition vp.sl → pr.Y
  /-- WOTS+ signature blocks (at digits `b = chainStepsCore (wotsMsg pos) c`) at `pos`. -/
  wotsSig : LayerPosition vp.sl → Vector pr.Y vp.sl.params.len

/-- Monadic WOTS chain evaluation through `collCall .F`. -/
def slChainM {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (chAdrs : Adrs) (x : pr.Y) (start : ℕ) : ℕ → m pr.Y
  | 0 => pure x
  | steps + 1 => do
    let prev ← slChainM collCall chAdrs x start steps
    collCall .F (chAdrs.setHashAddress (start + steps)) prev

/-- Pure deterministic WOTS chain evaluation (`pr.F`). -/
def slChainDet (pk : pr.PkSeed) (chAdrs : Adrs) (x : pr.Y) (start steps : ℕ) : pr.Y :=
  Id.run (slChainM pr (sfDetCall pr pk) chAdrs x start steps)

theorem slChainDet_eq_chain (pk : pr.PkSeed) (chAdrs : Adrs)
    (x : pr.Y) (start steps : ℕ) :
    slChainDet pr pk chAdrs x start steps = SLHDSA.chain (prEager pr) pk chAdrs x start steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [slChainDet, slChainM, Id.run_bind, sfDetCall, Id.run_pure, SLHDSA.chain_succ] at ih ⊢
    rw [ih]; rfl

theorem slChainDet_compose (pk : pr.PkSeed) (chAdrs : Adrs) (x : pr.Y) (start s₁ s₂ : ℕ) :
    slChainDet pr pk chAdrs (slChainDet pr pk chAdrs x start s₁) (start + s₁) s₂ =
      slChainDet pr pk chAdrs x start (s₁ + s₂) := by
  rw [slChainDet_eq_chain pr, slChainDet_eq_chain pr,
    slChainDet_eq_chain pr]
  exact SLHDSA.chain_compose (prEager pr) pk chAdrs x start s₁ s₂

/-- FORS addresses (bottom layer, independent of the WOTS hybrid index `γ`). -/
def forsAddresses (vp : ValidatedParams) : List Adrs :=
  forsLeafAddresses vp.sl ++ forsTreeAddresses vp.sl ++ forsRootAddresses vp.sl

/-- Read the honest WOTS message at `pos` from a table `tbl` that already contains FORS and all
layers strictly below `pos.layer`. -/
def wotsMsgFromTbl (tbl : Adrs → Option pr.Y) (pos : LayerPosition vp.sl) : pr.Y :=
  if pos.layer.val = 0 then
    (tbl (forsPkAdrs ((pos.toAdrs.setTypeAndClear .forsTree).setKeyPairAddress pos.leaf.val))).getD
      default
  else
    (tbl (xmssNodeAdrs (SLHDSA.GeneralHypertree.layerAdrs (pos.layer.val - 1)
      (pos.tree.val * 2 ^ vp.sl.params.hp + pos.leaf.val)) vp.sl.params.hp 0)).getD default

/-- Accumulator state while building a `HybTree` bottom-up across layers. -/
structure HybAcc where
  tbl : Adrs → Option pr.Y
  wotsMsg : LayerPosition vp.sl → pr.Y
  wotsSig : LayerPosition vp.sl → Vector pr.Y vp.sl.params.len

/-- Process one WOTS+ leaf `pos`: compute `msg`, run `chainStart` + remaining chain steps for each
chain `c : Fin len`, compress tops into `wotsPk`, and update `acc`. -/
def buildLeafM {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (chainStart : LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → m pr.Y)
    (acc : HybAcc pr) (pos : LayerPosition vp.sl) : m (HybAcc pr) := do
  let msg := wotsMsgFromTbl pr acc.tbl pos
  let pairs ← Vector.ofFnM fun c : Fin vp.sl.params.len => do
    let b := chainStepsCore pr.toSLHDSA.core msg c.val
    let sigBlk ← chainStart pos c b
    let top ← slChainM pr collCall (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b
      (vp.sl.params.w - 1 - b)
    return (sigBlk, top)
  let sigVec : Vector pr.Y vp.sl.params.len := Vector.ofFn fun c => pairs[c.val].1
  let topVec : Vector pr.Y vp.params.lsl :=
    (Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
      (Params.lsl_eq_len vp.valid).symm
  let wpk ← collCall .thLsl (wotsPkAdrs (wotsInstanceAdrs pos)) topVec
  return ⟨Function.update acc.tbl (wotsPkAdrs (wotsInstanceAdrs pos)) (some wpk),
          Function.update acc.wotsMsg pos msg,
          Function.update acc.wotsSig pos sigVec⟩

/-- Process one XMSS tree `coord`: process all `2^hp` leaves, then fold internal nodes bottom-up. -/
def buildTreeM {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (chainStart : LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → m pr.Y)
    (acc : HybAcc pr) (coord : LayerTreeCoord vp.sl) : m (HybAcc pr) := do
  let acc₁ ← (List.finRange (2 ^ vp.sl.params.hp)).foldlM
    (fun a lf => buildLeafM pr collCall chainStart a ⟨coord.layer, coord.tree, lf⟩) acc
  let tbl₂ ← (perfectInternalCoords vp.sl.params.hp).foldlM (fun tbl zi => do
    let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
    let l := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
    let r := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
    let v ← collCall .H a (l, r)
    return Function.update tbl a (some v)) acc₁.tbl
  return { acc₁ with tbl := tbl₂ }

/-- Exposed list of all reachable XMSS trees in strictly increasing layer order `0, …, d - 1`
(same elements as `SLHDSA.Security.allXmssTrees`, exposed for layer-by-layer induction). -/
def allXmssTreesList (vp : ValidatedParams) : List (LayerTreeCoord vp.sl) :=
  (List.finRange vp.sl.params.d).flatMap fun layer =>
    (List.finRange (2 ^ layerTreeHeight vp.sl layer.val)).map fun tree => ⟨layer, tree⟩

theorem allXmssTreesList_nodup (vp : ValidatedParams) : (allXmssTreesList vp).Nodup := by
  rw [allXmssTreesList, List.nodup_flatMap]
  refine ⟨fun layer _ => (List.nodup_finRange _).map_on (fun _ _ _ _ h =>
      Fin.ext (congrArg (fun c : LayerTreeCoord vp.sl => c.tree.val) h)),
    (List.nodup_iff_pairwise_ne.1 (List.nodup_finRange _)).imp fun {l₁ l₂} hne a ha hb => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
      obtain ⟨_, _, heq⟩ := List.mem_map.1 hb
      exact hne (congrArg LayerTreeCoord.layer heq).symm⟩

theorem allXmssTreesList_length (vp : ValidatedParams) :
    (allXmssTreesList vp).length = xmssTreeCount vp.sl.params := by
  simp only [allXmssTreesList, List.length_flatMap, List.length_map, List.length_finRange]
  change ((List.finRange vp.sl.params.d).map fun layer => 2 ^ layerTreeHeight vp.sl layer.val).sum = _
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  unfold xmssTreeCount
  exact Finset.sum_congr rfl fun layer _ => (SLHDSA.Security.treesAtLayer_eq_layerTreeHeight vp.sl layer).symm

theorem mem_allXmssTreesList (vp : ValidatedParams) (coord : LayerTreeCoord vp.sl) :
    coord ∈ allXmssTreesList vp := by
  rcases coord with ⟨layer, tree⟩
  simp only [allXmssTreesList, List.mem_flatMap, List.mem_map]
  exact ⟨layer, List.mem_finRange _, tree, List.mem_finRange _, rfl⟩

/-- **Unified bottom-up virtual-hypertree builder**: builds FORS (types 3–4) using `u` at
`FORS_PRF`, then builds all XMSS trees in `allXmssTreesList vp` (which enumerates layers
`0, …, d - 1` in strictly increasing order) using `chainStart` for every WOTS chain. -/
def buildHybTreeM {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (chainStart : LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → m pr.Y)
    (u : SlSecAdrs vp → pr.Y) : m (HybTree pr) := do
  let tbl₀ ← (forsAddresses vp).foldlM (fun tbl a => do
    let v ← evalNodeM pr collCall u tbl a
    return Function.update tbl a (some v)) (fun _ => none)
  let accFin ← (allXmssTreesList vp).foldlM (buildTreeM pr collCall chainStart)
    ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩
  return ⟨(accFin.tbl (topRootAdrs vp)).getD default, accFin.tbl, accFin.wotsMsg, accFin.wotsSig⟩

/-- Hybrid `γ` WOTS chain-start block: `chain x m (b - m)` where `m = min γ (b - 1)`. -/
def hybBlockVal (γ : ℕ) (pk : pr.PkSeed) (chAdrs : Adrs) (b : ℕ) (x : pr.Y) : pr.Y :=
  let m := min γ (b - 1)
  slChainDet pr pk chAdrs x m (b - m)

/-- Deterministic hybrid `γ` virtual hypertree (`Hyb(γ)` from eager secrets `u`). -/
def hybTreeDet (γ : ℕ) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) : HybTree pr :=
  Id.run <| buildHybTreeM pr (sfDetCall pr pk)
    (fun pos c b => pure (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b
      (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c.val))))
    u

/-- Probabilistic hybrid `γ` virtual hypertree: reads `u` only for FORS (`type = 6`) and samples
every WOTS chain seed `x ← $ᵗ pr.Y` freshly on the fly. -/
noncomputable def hybTreeProb [SampleableType pr.Y] (γ : ℕ) (pk : pr.PkSeed)
    (u : SlSecAdrs vp → pr.Y) : ProbComp (HybTree pr) :=
  buildHybTreeM pr (fun i a msg => pure (pr.memberEval i pk a msg))
    (fun pos c b => do
      let x ← $ᵗ pr.Y
      return hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
    u

/-! ## 5. Keyless Stage-2 table signer (`hybSign`) and WOTS-preimage extractor (`findHybWotsPre`) -/

/-- **Zero-`Th_λ` Stage-2 stateless signer on a `HybTree`**: reads `u` ONLY at `FORS_PRF`
(`type = 6`, never `WOTS_PRF`), evaluates only `H_msg^sl`, and reads all FORS/XMSS auth paths and
WOTS signatures directly from `hyb`. -/
def hybSign (pk : pr.PkSeed) (hyb : HybTree pr) (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (R : pr.Y) : Stateless.Sig pr :=
  let parts := splitDigest vp.sl.params (pr.HmsgSl R pk hyb.pkSl msg)
  let forsSig : ForsSigCore vp.sl.params pr.toSLHDSA.core :=
    Vector.ofFn fun i : Fin vp.sl.params.k =>
      let idx := forsSigLeafIndex vp.sl.params parts.md.toList i.val
      let sk := slSecOf pr u (forsSkAdrs parts.forsAdrs idx)
      let auth : Vector pr.Y vp.sl.params.a := Vector.ofFn fun j : Fin vp.sl.params.a =>
        (hyb.tbl (forsNodeAdrs parts.forsAdrs j.val
          (PerfectMerkleTree.sibling (idx / 2 ^ j.val)))).getD default
      ⟨sk, auth⟩
  let htSig : HtSigCore vp.sl.params pr.toSLHDSA.core :=
    Vector.ofFn fun ℓ : Fin vp.sl.params.d =>
      let pos := LayerPosition.atLayer vp.sl parts ℓ
      let auth : Vector pr.Y vp.sl.params.hp := Vector.ofFn fun j : Fin vp.sl.params.hp =>
        (hyb.tbl (xmssCellAdrs pos.toAdrs j.val
          (PerfectMerkleTree.sibling (pos.leaf.val / 2 ^ j.val)))).getD default
      ⟨hyb.wotsSig pos, auth⟩
  ⟨R, forsSig, htSig⟩

/-- Pure 0-query keyless layer walk for `findHybWotsPre`, reading recorded `XmssLayerTrace`s
against `hyb` without any secret keys or extra `Th_λ` queries. -/
def findHybWotsPreFromTrace [DecidableEq pr.Y] (hyb : HybTree pr)
    (pos : LayerPosition vp.sl) :
    (layers : ℕ) → pos.layer.val + layers = vp.sl.params.d →
      Vector (XmssLayerTrace pr) layers →
      Option ((LayerPosition vp.sl × Fin vp.sl.params.len) × ℕ × pr.Y)
  | 0, _, _ => none
  | 1, _, trs =>
    let tr := trs.head
    let honRoot := (hyb.tbl (xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0)).getD default
    if tr.xmssRoot = honRoot then
      let wotsHon := (hyb.tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default
      if tr.wotsPk = wotsHon then
        match wotsPreFromTrace pr tr.msg (hyb.wotsMsg pos) (hyb.wotsSig pos) tr.wotsTraces with
        | some (c, step, val) => some ((pos, c), step, val)
        | none => none
      else none
    else none
  | layers + 2, hrem, trs =>
    let tr := trs.head
    let honRoot := (hyb.tbl (xmssNodeAdrs pos.toAdrs vp.sl.params.hp 0)).getD default
    if tr.xmssRoot = honRoot then
      let wotsHon := (hyb.tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default
      if tr.wotsPk = wotsHon then
        match wotsPreFromTrace pr tr.msg (hyb.wotsMsg pos) (hyb.wotsSig pos) tr.wotsTraces with
        | some (c, step, val) => some ((pos, c), step, val)
        | none => none
      else none
    else
      findHybWotsPreFromTrace hyb (pos.next (by omega))
        (layers + 1)
        (by simp only [LayerPosition.next_layer_val]; change pos.layer.val + 1 + (layers + 1) = vp.sl.params.d; omega)
        trs.tail

/-- **Single-pass explicit-`Th_λ`-oracle keyless WOTS-preimage extractor** on a `HybTree`:
verifies `finalRoot = hyb.pkSl` AND extracts `some ((pos, c), step, val)` in ONE pass of
at most `Vsl vp.params` (`= 2741`) tweakable-hash queries (zero secret keys). -/
def findHybWotsPreM [DecidableEq pr.Y] (pk : pr.PkSeed) (hyb : HybTree pr)
    (msg : List Byte) (sig : Stateless.Sig pr) :
    OracleComp (thSpec pr) (Option ((LayerPosition vp.sl × Fin vp.sl.params.len) × ℕ × pr.Y)) := do
  let parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk hyb.pkSl msg)
  let (forsRec, _) ← forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs
  let (finalRoot, htTraces) ← htRecoverTraceM pr (LayerPosition.initial vp.sl parts)
    vp.sl.params.d (by simp) forsRec sig.hypertree
  let forsHon := (hyb.tbl (forsPkAdrs parts.forsAdrs)).getD default
  return if finalRoot = hyb.pkSl ∧ forsRec ≠ forsHon then
    findHybWotsPreFromTrace pr hyb (LayerPosition.initial vp.sl parts)
      vp.sl.params.d (by simp) htTraces
  else none

/-- **Query bound (`≤ Vsl`)**: `findHybWotsPreM` makes at most `Vsl vp.params` (`= 2741`)
tweakable-hash queries on every path. -/
theorem findHybWotsPreM_queryBound [DecidableEq pr.Y] (pk : pr.PkSeed) (hyb : HybTree pr)
    (msg : List Byte) (sig : Stateless.Sig pr) :
    IsTotalQueryBound (findHybWotsPreM pr pk hyb msg sig) (Vsl vp.params) := by
  unfold findHybWotsPreM Vsl
  refine (isTotalQueryBound_bind (forsRecoverTraceM_queryBound pr sig.fors _ _) fun ⟨forsRec, _⟩ =>
    isTotalQueryBound_bind (n₂ := 0)
      (htRecoverTraceM_queryBound pr vp.sl.params.d _ _ forsRec sig.hypertree) fun ⟨finalRoot, htTraces⟩ => by
        dsimp only
        simpa only [isQueryBoundP_true_iff] using
          (isQueryBoundP_pure (spec := thSpec pr) (p := fun _ => True) _ 0)).mono ?_
  dsimp only [ValidatedParams.sl, Params.slParams]
  omega

/-- Deterministic simulation of `findHybWotsPreM` under `thRealImpl pr pk`. -/
noncomputable def findHybWotsPre [DecidableEq pr.Y] (pk : pr.PkSeed) (hyb : HybTree pr)
    (msg : List Byte) (sig : Stateless.Sig pr) :
    Option ((LayerPosition vp.sl × Fin vp.sl.params.len) × ℕ × pr.Y) :=
  Id.run (simulateQ (thRealImpl pr pk) (findHybWotsPreM pr pk hyb msg sig))

/-- Boolean predicate: `findHybWotsPre` succeeds on `o`. -/
noncomputable def isHybWotsPre [DecidableEq pr.Y] (pk : pr.PkSeed) (hyb : HybTree pr)
    (o : Option (List Byte × Stateless.Sig pr)) : Bool :=
  match o with
  | some (msg, sig) => (findHybWotsPre pr pk hyb msg sig).isSome
  | none => false

end HybTree

/-! ## 6. Correctness at `γ = 0`, keyless signing agreement, and extractor soundness -/

section ZeroAndSound

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- `wotsInstanceAdrs pos` has the same `layer`, `tree`, and `keyPair` as `pos`. -/
theorem wotsLeafAdrs_eq_wotsInstanceAdrs' (pos : LayerPosition vp.sl) :
    wotsLeafAdrs pos.toAdrs pos.leaf.val = wotsInstanceAdrs pos :=
  SLHDSA.Security.wotsLeafAdrs_eq_wotsInstanceAdrs pos

/-- Every `wotsSkAdrs (wotsInstanceAdrs pos) c.val` belongs to `slSecretList vp.sl`. -/
theorem mem_slSecretList_wotsSk {vp : ValidatedParams} (pos : LayerPosition vp.sl)
    (c : Fin vp.sl.params.len) :
    wotsSkAdrs (wotsInstanceAdrs pos) c.val ∈ slSecretList vp.sl :=
  mem_slSecretList
    (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos c (t := 0)
      (by have : 1 < vp.sl.params.w := Params.one_lt_w vp.valid; omega))
    (by rw [childAdrs_wotsChainAdrs_setHashAddress_zero]; simp)

omit [Inhabited pr.Y] in
/-- `hybBlockVal` at `γ = 0` starts from step `0` and runs `b` steps. -/
theorem hybBlockVal_zero (pk : pr.PkSeed) (chAdrs : Adrs) (b : ℕ) (x : pr.Y) :
    hybBlockVal pr 0 pk chAdrs b x = slChainDet pr pk chAdrs x 0 b := by
  simp [hybBlockVal]

/-- `hybBlockVal` step identity for `γ < b - 1`: one step of `F` at hash address `γ` followed by
`hybBlockVal (γ + 1)` equals `hybBlockVal γ`. -/
theorem hybBlockVal_succ_F (γ : ℕ) (pk : pr.PkSeed) (chAdrs : Adrs) (b : ℕ) (x : pr.Y)
    (hγ : γ < b - 1) :
    slChainDet pr pk chAdrs (pr.F pk (chAdrs.setHashAddress γ) x) (γ + 1) (b - (γ + 1)) =
      hybBlockVal pr γ pk chAdrs b x := by
  unfold hybBlockVal
  rw [min_eq_left (by omega : γ ≤ b - 1)]
  have h1 : pr.F pk (chAdrs.setHashAddress γ) x = slChainDet pr pk chAdrs x γ 1 := rfl
  rw [h1, slChainDet_compose pr pk chAdrs x γ 1 (b - (γ + 1))]
  congr 1; omega

omit [Inhabited pr.Y] in
/-- `hybBlockVal` for `γ + 1` when `γ < b - 1`. -/
theorem hybBlockVal_succ_ideal (γ : ℕ) (pk : pr.PkSeed) (chAdrs : Adrs) (b : ℕ) (y : pr.Y)
    (hγ : γ < b - 1) :
    slChainDet pr pk chAdrs y (γ + 1) (b - (γ + 1)) =
      hybBlockVal pr (γ + 1) pk chAdrs b y := by
  unfold hybBlockVal
  rw [min_eq_left (by omega : γ + 1 ≤ b - 1)]

omit [Inhabited pr.Y] in
/-- `hybBlockVal` is unchanged from `γ` to `γ + 1` when `¬ (γ < b - 1)`. -/
theorem hybBlockVal_succ_of_not_lt (γ : ℕ) (pk : pr.PkSeed) (chAdrs : Adrs) (b : ℕ) (x : pr.Y)
    (hγ : ¬ γ < b - 1) :
    hybBlockVal pr (γ + 1) pk chAdrs b x = hybBlockVal pr γ pk chAdrs b x := by
  unfold hybBlockVal
  rw [min_eq_right (by omega : b - 1 ≤ γ + 1), min_eq_right (by omega : b - 1 ≤ γ)]

omit [Inhabited pr.Y] in
/-- `hybBlockVal` at `γ = w - 2` for `0 < b ≤ w - 1` is a single `F` call at step `b - 1`. -/
theorem hybBlockVal_top (pk : pr.PkSeed) (chAdrs : Adrs) {b : ℕ} (hb0 : 0 < b)
    (hbw : b ≤ vp.sl.params.w - 1) (x : pr.Y) :
    hybBlockVal pr (vp.params.w - 2) pk chAdrs b x =
      pr.F pk (chAdrs.setHashAddress (b - 1)) x := by
  unfold hybBlockVal
  dsimp only
  have hle : b - 1 ≤ vp.params.w - 2 := by
    have : vp.sl.params.w = vp.params.w := rfl; omega
  rw [min_eq_right hle, show b - (b - 1) = 1 by omega]
  rfl

omit [Inhabited pr.Y] in
/-- `hybBlockVal` at `b = 0` is the identity `x`. -/
theorem hybBlockVal_b_zero (γ : ℕ) (pk : pr.PkSeed) (chAdrs : Adrs) (x : pr.Y) :
    hybBlockVal pr γ pk chAdrs 0 x = x := by
  simp [hybBlockVal, slChainDet, slChainM]

/-- Helper: `Id.run (Vector.ofFnM f) = Vector.ofFn (fun i => Id.run (f i))`. -/
theorem idRun_ofFnM {n : ℕ} {α : Type} (f : Fin n → Id α) :
    Id.run (Vector.ofFnM f) = Vector.ofFn (fun i => Id.run (f i)) := by
  induction n with
  | zero => rw [Vector.ofFnM_zero]; apply Vector.ext; intro i hi; omega
  | succ n ih =>
    rw [Vector.ofFnM_succ]; apply Vector.ext; intro i hi
    change ((Id.run (Vector.ofFnM (fun j : Fin n => f j.castSucc))).push
      (Id.run (f (Fin.last n))))[i] = _
    rw [ih (fun j => f j.castSucc)]
    by_cases hlt : i < n
    · simp [Vector.getElem_push_lt hlt]
    · have : i = n := by omega
      subst this; simp [Fin.last]

/-- Consistency invariant of a `HybTree` (satisfied in EVERY hybrid `γ`, and by `udBuildM` and
`preBuildM`): at every `pos`, the table's WOTS public key is `wotsPkFromSig` of `wotsSig pos` on
`wotsMsg pos`. -/
def HybWotsConsistent (pk : pr.PkSeed) (hyb : HybTree pr) : Prop :=
  ∀ pos : LayerPosition vp.sl,
    (hyb.tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default =
      SLHDSA.wotsPkFromSig (prEager pr) (hyb.wotsSig pos) (hyb.wotsMsg pos) pk
        (wotsInstanceAdrs pos)

/-- **Soundness of `findHybWotsPre` in ANY `HybTree`**: if `findHybWotsPre` returns
`some ((pos, c), step, val)`, then `step < w - 1`, `step + 1 = b`, and `val` is an `F`-preimage
of `(hyb.wotsSig pos)[c.val]` at `(wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step`. -/
theorem findHybWotsPre_sound [DecidableEq pr.Y] (pk : pr.PkSeed) (hyb : HybTree pr)
    (_hcons : HybWotsConsistent pr pk hyb) (msg : List Byte) (sig : Stateless.Sig pr)
    {pos : LayerPosition vp.sl} {c : Fin vp.sl.params.len} {step : ℕ} {val : pr.Y}
    (h : findHybWotsPre pr pk hyb msg sig = some ((pos, c), step, val)) :
    step < vp.sl.params.w - 1 ∧
      step + 1 = chainStepsCore pr.toSLHDSA.core (hyb.wotsMsg pos) c.val ∧
      pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step) val =
        (hyb.wotsSig pos)[c.val] := by
  have hwalk : ∀ (layers : ℕ) (p0 : LayerPosition vp.sl) (hrem : p0.layer.val + layers = vp.sl.params.d)
      (fMsg : pr.Y) (sigs : Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers),
      findHybWotsPreFromTrace pr hyb p0 layers hrem
        (Id.run (simulateQ (thRealImpl pr pk) (htRecoverTraceM pr p0 layers hrem fMsg sigs))).2 =
        some ((pos, c), step, val) →
      step < vp.sl.params.w - 1 ∧
        step + 1 = chainStepsCore pr.toSLHDSA.core (hyb.wotsMsg pos) c.val ∧
        pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step) val =
          (hyb.wotsSig pos)[c.val] := by
    intro layers
    induction layers using Nat.twoStepInduction with
    | zero => intro _ _ _ _ hw; simp [findHybWotsPreFromTrace] at hw
    | one =>
      intro p0 hrem fMsg sigs hw
      have htr := simulateQ_xmssRecoverTraceM_spec pr pk p0 sigs.head fMsg
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        findHybWotsPreFromTrace] at hw
      have hhd : (#v[Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg))]).head =
          Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg)) := rfl
      rw [hhd] at hw
      dsimp only at hw
      split at hw
      · split at hw
        · cases hwp : wotsPreFromTrace pr
              (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg))).msg
              (hyb.wotsMsg p0) (hyb.wotsSig p0)
              (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg))).wotsTraces with
          | none => rw [hwp] at hw; cases hw
          | some t =>
            rcases t with ⟨c', step', val'⟩
            rw [hwp] at hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hw
            rw [htr.1, htr.2.2.2.2.1] at hwp
            have hs := wotsPreFromTrace_sound pr pk sigs.head.wots (hyb.wotsSig p0) fMsg
              (hyb.wotsMsg p0) (wotsLeafAdrs p0.toAdrs p0.leaf.val) hwp
            rwa [wotsLeafAdrs_eq_wotsInstanceAdrs'] at hs
        · cases hw
      · cases hw
    | more layers _ ih =>
      intro p0 hrem fMsg sigs hw
      have htr := simulateQ_xmssRecoverTraceM_spec pr pk p0 sigs.head fMsg
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        findHybWotsPreFromTrace] at hw
      have hhd : ∀ {α : Type} {n : ℕ} (a : α) (v : Vector α n), (v.insertIdx 0 a).head = a :=
        fun _ _ => by simp [Vector.head]
      have htl : ∀ {α : Type} {n : ℕ} (a : α) (v : Vector α n), (v.insertIdx 0 a).tail = v :=
        fun _ _ => by apply Vector.ext; intro i hi; simp [Vector.tail_eq_cast_extract]
      rw [hhd, htl] at hw
      split at hw
      · split at hw
        · cases hwp : wotsPreFromTrace pr
              (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg))).msg
              (hyb.wotsMsg p0) (hyb.wotsSig p0)
              (Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg))).wotsTraces with
          | none => rw [hwp] at hw; cases hw
          | some t =>
            rcases t with ⟨c', step', val'⟩
            rw [hwp] at hw
            simp only [Option.some.injEq, Prod.mk.injEq] at hw
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hw
            rw [htr.1, htr.2.2.2.2.1] at hwp
            have hs := wotsPreFromTrace_sound pr pk sigs.head.wots (hyb.wotsSig p0) fMsg
              (hyb.wotsMsg p0) (wotsLeafAdrs p0.toAdrs p0.leaf.val) hwp
            rwa [wotsLeafAdrs_eq_wotsInstanceAdrs'] at hs
        · cases hw
      · exact ih (p0.next (by omega)) _ _ sigs.tail hw
  unfold findHybWotsPre findHybWotsPreM at h
  simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure] at h
  split at h
  · exact hwalk vp.sl.params.d _ (by simp) _ _ h
  · cases h

/-- FORS pass of `buildHybTreeM` with `sfDetCall pr pk` computes `honestVal` on every address of
`forsAddresses vp` and leaves non-FORS addresses `none`. -/
theorem forsPass_det (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    let tbl₀ := Id.run ((forsAddresses vp).foldlM (fun tbl a => do
      let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
      return Function.update tbl a (some v)) (fun _ => none))
    TblSound pr pk u tbl₀ ∧
      (∀ a ∈ forsAddresses vp, tbl₀ a = some (honestVal pr pk u a)) ∧
      (∀ a, a ∉ forsAddresses vp → tbl₀ a = none) := by
  have hfold : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
      Id.run (l.foldlM (fun tbl a => do
        let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
        return Function.update tbl a (some v)) tbl) =
      l.foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) tbl := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons a as ih => intro tbl; exact ih _
  have hpres_none : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y) (a : Adrs),
      a ∉ l → tbl a = none →
      (l.foldl (fun tbl x => Function.update tbl x (some (evalNodeDet pr pk u tbl x))) tbl) a = none := by
    intro l; induction l with
    | nil => intro tbl a _ h; exact h
    | cons x xs ih =>
      intro tbl a hnot h
      simp only [List.mem_cons, not_or] at hnot
      exact ih _ a hnot.2 (by dsimp only; rw [Function.update_of_ne hnot.1]; exact h)
  -- Use `slVirtualTreeDet_spec` on the prefix `forsAddresses vp` of `slTreeAddresses vp`!
  -- Actually even more direct: `forsAddresses vp` is a prefix of `slTreeAddresses vp`!
  -- Let's prove directly via `honestVal` on the 3 sub-lists:
  have hstep_sound : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      (∀ a ∈ l, ∀ tbl', TblSound pr pk u tbl' →
        (∀ x, tbl x = some (honestVal pr pk u x) → tbl' x = some (honestVal pr pk u x)) →
        evalNodeDet pr pk u tbl' a = honestVal pr pk u a) →
      TblSound pr pk u (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) ∧
        (∀ x, tbl x = some (honestVal pr pk u x) →
          (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) x =
            some (honestVal pr pk u x)) ∧
        (∀ a ∈ l,
          (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) a =
            some (honestVal pr pk u a)) := by
    intro l; induction l with
    | nil => intro tbl hs _; exact ⟨hs, fun _ h => h, fun _ h => by simp at h⟩
    | cons a as ih =>
      intro tbl hs hev
      have hva := hev a (by simp) tbl hs (fun _ h => h)
      set tbl₁ := Function.update tbl a (some (evalNodeDet pr pk u tbl a))
      have hs₁ : TblSound pr pk u tbl₁ := by
        intro b v hb
        by_cases hba : b = a
        · subst hba; simp only [tbl₁, Function.update_self, Option.some.injEq] at hb; exact hb.symm.trans hva
        · simp only [tbl₁, Function.update_of_ne hba] at hb; exact hs b v hb
      have hm₁ : ∀ x, tbl x = some (honestVal pr pk u x) → tbl₁ x = some (honestVal pr pk u x) := by
        intro x hx; by_cases hxa : x = a
        · subst hxa; simp [tbl₁, hva]
        · simp [tbl₁, Function.update_of_ne hxa, hx]
      have ha₁ : tbl₁ a = some (honestVal pr pk u a) := by simp [tbl₁, hva]
      obtain ⟨hs₂, hm₂, ha₂⟩ := ih tbl₁ hs₁ (fun b hb tbl' hs' hsub =>
        hev b (by simp [hb]) tbl' hs' (fun x hx => hsub x (hm₁ x hx)))
      refine ⟨hs₂, fun x hx => hm₂ x (hm₁ x hx), fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hm₂ x ha₁
      · exact ha₂ x hx'
  -- Step 1: forsLeafAddresses
  have h1 := hstep_sound (forsLeafAddresses vp.sl) (fun _ => none) (fun _ _ h => by simp at h)
    (fun a ha tbl' _ _ => by
      obtain ⟨⟨⟨bpos, i⟩, j⟩, -, rfl⟩ := List.mem_map.1 ha
      have hty3 : (forsNodeAdrs bpos.forsAdrs 0 (i.val * vp.sl.params.t + j.val)).type = 3 := rfl
      have hw2 : (forsNodeAdrs bpos.forsAdrs 0 (i.val * vp.sl.params.t + j.val)).word2 = 0 := rfl
      have hw3 : (forsNodeAdrs bpos.forsAdrs 0 (i.val * vp.sl.params.t + j.val)).word3 =
          i.val * vp.sl.params.t + j.val := rfl
      have hsk : forsSkAdrs (forsNodeAdrs bpos.forsAdrs 0 (i.val * vp.sl.params.t + j.val))
          (i.val * vp.sl.params.t + j.val) = forsSkAdrs bpos.forsAdrs (i.val * vp.sl.params.t + j.val) := rfl
      rw [honestVal_forsLeaf]
      unfold evalNodeDet evalNodeM
      simp only [hty3, hw2, hw3, ↓reduceIte, hsk]
      rfl)
  set tbl₁ := (forsLeafAddresses vp.sl).foldl
    (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) (fun _ => none)
  -- Step 2: forsTreeAddresses (layered by height via `perfectInternalCoords`)
  have h2_inner : ∀ (bpos : BottomPosition vp.sl) (i : Fin vp.sl.params.k)
      (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      (∀ t < 2 ^ vp.sl.params.a, tbl (forsNodeAdrs bpos.forsAdrs 0 (i.val * vp.sl.params.t + t)) =
        some (honestVal pr pk u (forsNodeAdrs bpos.forsAdrs 0 (i.val * vp.sl.params.t + t)))) →
      let l := (perfectInternalCoords vp.sl.params.a).map fun zi =>
        forsNodeAdrs bpos.forsAdrs zi.1 (i.val * 2 ^ (vp.sl.params.a - zi.1) + zi.2)
      TblSound pr pk u (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) ∧
        (∀ x, tbl x = some (honestVal pr pk u x) →
          (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) x =
            some (honestVal pr pk u x)) ∧
        (∀ a ∈ l,
          (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) a =
            some (honestVal pr pk u a)) := by
    intro bpos i
    have hrec : ∀ (rem z : ℕ), z + rem = vp.sl.params.a →
        ∀ (tbl : Adrs → Option pr.Y),
        TblSound pr pk u tbl →
        (∀ j < 2 ^ (vp.sl.params.a - z),
          tbl (forsNodeAdrs bpos.forsAdrs z (i.val * 2 ^ (vp.sl.params.a - z) + j)) =
            some (honestVal pr pk u (forsNodeAdrs bpos.forsAdrs z (i.val * 2 ^ (vp.sl.params.a - z) + j)))) →
        let l := (perfectInternalCoords rem).map fun zi =>
          forsNodeAdrs bpos.forsAdrs (zi.1 + z) (i.val * 2 ^ (vp.sl.params.a - (zi.1 + z)) + zi.2)
        TblSound pr pk u (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) ∧
          (∀ x, tbl x = some (honestVal pr pk u x) →
            (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) x =
              some (honestVal pr pk u x)) ∧
          (∀ a ∈ l,
            (l.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) a =
              some (honestVal pr pk u a)) := by
      intro rem; induction rem with
      | zero =>
        intro z _ tbl hs _
        exact ⟨hs, fun _ h => h, fun _ h => by simp [perfectInternalCoords] at h⟩
      | succ rem ih =>
        intro z hz tbl hs hlv
        have hsplit : ((perfectInternalCoords (rem + 1)).map fun zi =>
            forsNodeAdrs bpos.forsAdrs (zi.1 + z) (i.val * 2 ^ (vp.sl.params.a - (zi.1 + z)) + zi.2)) =
          ((List.range (2 ^ rem)).map fun j =>
            forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) ++
          ((perfectInternalCoords rem).map fun zi =>
            forsNodeAdrs bpos.forsAdrs (zi.1 + (z + 1))
              (i.val * 2 ^ (vp.sl.params.a - (zi.1 + (z + 1))) + zi.2)) := by
          simp only [perfectInternalCoords, List.map_append, List.map_map, Function.comp_def]
          congr 1
          · apply List.map_congr_left; intro j _; rw [show 1 + z = z + 1 by omega]
          · apply List.map_congr_left; intro zi _; rw [show zi.1 + 1 + z = zi.1 + (z + 1) by omega]
        dsimp only; rw [hsplit, List.foldl_append]
        have hpow : 2 ^ (vp.sl.params.a - z) = 2 * 2 ^ (vp.sl.params.a - (z + 1)) := by
          rw [show vp.sl.params.a - z = (vp.sl.params.a - (z + 1)) + 1 by omega, pow_succ, Nat.mul_comm]
        have hcur := hstep_sound ((List.range (2 ^ rem)).map fun j =>
          forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) tbl hs
          (fun a ha tbl' _ hsub => by
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
            have hjlt : j < 2 ^ (vp.sl.params.a - (z + 1)) := by
              rw [show vp.sl.params.a - (z + 1) = rem by omega]; exact List.mem_range.1 hj
            have hidx0 : 2 * (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) =
                i.val * 2 ^ (vp.sl.params.a - z) + 2 * j := by rw [hpow]; ring
            have hidx1 : 2 * (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) + 1 =
                i.val * 2 ^ (vp.sl.params.a - z) + (2 * j + 1) := by rw [hpow]; ring
            have hL := hsub _ (hlv (2 * j) (by rw [hpow]; omega))
            have hR := hsub _ (hlv (2 * j + 1) (by rw [hpow]; omega))
            rw [← hidx0] at hL; rw [← hidx1] at hR
            have hch0 : forsNodeAdrs (forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) z
                (2 * (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) =
                forsNodeAdrs bpos.forsAdrs z (2 * (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) := rfl
            have hch1 : forsNodeAdrs (forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) z
                (2 * (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) + 1) =
                forsNodeAdrs bpos.forsAdrs z (2 * (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) + 1) := rfl
            rw [honestVal_forsNode_succ]
            unfold evalNodeDet evalNodeM
            have hty3 : (forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).type = 3 := rfl
            have hw2 : (forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).word2 = z + 1 := rfl
            have hw3 : (forsNodeAdrs bpos.forsAdrs (z + 1) (i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).word3 =
                i.val * 2 ^ (vp.sl.params.a - (z + 1)) + j := rfl
            simp only [hty3, hw2, hw3, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [hch0, hch1, hL, hR, Option.getD_some, Option.getD_some]; rfl)
        have hnext := ih (z + 1) (by omega) _ hcur.1 (fun j hj =>
          hcur.2.2 _ (List.mem_map.2 ⟨j, List.mem_range.2 (by rw [show rem = vp.sl.params.a - (z + 1) by omega]; exact hj), rfl⟩))
        refine ⟨hnext.1, fun x hx => hnext.2.1 x (hcur.2.1 x hx), fun a ha => ?_⟩
        rcases List.mem_append.1 ha with ha₁ | ha₂
        · exact hnext.2.1 a (hcur.2.2 a ha₁)
        · exact hnext.2.2 a ha₂
    intro tbl hs hlv
    simpa [Nat.add_zero, SLHDSA.Params.t] using hrec vp.sl.params.a 0 (Nat.zero_add _) tbl hs
      (by simpa [SLHDSA.Params.t] using hlv)
  have h2 : TblSound pr pk u ((forsTreeAddresses vp.sl).foldl
      (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl₁) ∧
      (∀ x, tbl₁ x = some (honestVal pr pk u x) →
        ((forsTreeAddresses vp.sl).foldl
          (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl₁) x =
          some (honestVal pr pk u x)) ∧
      (∀ a ∈ forsTreeAddresses vp.sl,
        ((forsTreeAddresses vp.sl).foldl
          (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl₁) a =
          some (honestVal pr pk u a)) := by
    have hprod : ∀ (ls : List (BottomPosition vp.sl × Fin vp.sl.params.k)) (tbl : Adrs → Option pr.Y),
        TblSound pr pk u tbl →
        (∀ x, tbl₁ x = some (honestVal pr pk u x) → tbl x = some (honestVal pr pk u x)) →
        let all := (ls.product (perfectInternalCoords vp.sl.params.a)).map fun p =>
          forsNodeAdrs p.1.1.forsAdrs p.2.1 (p.1.2.val * 2 ^ (vp.sl.params.a - p.2.1) + p.2.2)
        TblSound pr pk u (all.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) ∧
          (∀ x, tbl x = some (honestVal pr pk u x) →
            (all.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) x =
              some (honestVal pr pk u x)) ∧
          (∀ a ∈ all,
            (all.foldl (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl) a =
              some (honestVal pr pk u a)) := by
      intro ls; induction ls with
      | nil => intro tbl hs _; exact ⟨hs, fun _ h => h, fun _ h => by simp [List.product] at h⟩
      | cons bi bis ih =>
        intro tbl hs hsub
        have hsp : (((bi :: bis).product (perfectInternalCoords vp.sl.params.a)).map fun p =>
            forsNodeAdrs p.1.1.forsAdrs p.2.1 (p.1.2.val * 2 ^ (vp.sl.params.a - p.2.1) + p.2.2)) =
          ((perfectInternalCoords vp.sl.params.a).map fun zi =>
            forsNodeAdrs bi.1.forsAdrs zi.1 (bi.2.val * 2 ^ (vp.sl.params.a - zi.1) + zi.2)) ++
          ((bis.product (perfectInternalCoords vp.sl.params.a)).map fun p =>
            forsNodeAdrs p.1.1.forsAdrs p.2.1 (p.1.2.val * 2 ^ (vp.sl.params.a - p.2.1) + p.2.2)) := by
          simp [List.product, List.flatMap_cons, List.map_append, List.map_map, Function.comp_def]
        dsimp only; rw [hsp, List.foldl_append]
        have hcur := h2_inner bi.1 bi.2 tbl hs (fun t ht =>
          hsub _ (h1.2.2 _ (SLHDSA.Security.mem_forsLeafAddresses vp.sl bi.1 bi.2 ⟨t, by simpa [SLHDSA.Params.t] using ht⟩)))
        have hrest := ih _ hcur.1 (fun x hx => hcur.2.1 x (hsub x hx))
        refine ⟨hrest.1, fun x hx => hrest.2.1 x (hcur.2.1 x hx), fun a ha => ?_⟩
        rcases List.mem_append.1 ha with ha₁ | ha₂
        · exact hrest.2.1 a (hcur.2.2 a ha₁)
        · exact hrest.2.2 a ha₂
    exact hprod ((allBottomPositions vp.sl).product (List.finRange vp.sl.params.k)) tbl₁ h1.1
      (fun _ h => h)
  set tbl₂ := (forsTreeAddresses vp.sl).foldl
    (fun t a => Function.update t a (some (evalNodeDet pr pk u t a))) tbl₁
  -- Step 3: forsRootAddresses
  have h3 := hstep_sound (forsRootAddresses vp.sl) tbl₂ h2.1 (fun a ha tbl' _ hsub => by
    obtain ⟨bpos, -, rfl⟩ := List.mem_map.1 ha
    simp only [evalNodeDet, evalNodeM, honestVal_forsPk]
    change pr.ThK pk (forsPkAdrs bpos.forsAdrs) (Vector.ofFn fun i : Fin vp.params.k =>
      (tbl' (forsNodeAdrs (forsPkAdrs bpos.forsAdrs) vp.params.a i.val)).getD default) = _
    congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
    have hfa : forsNodeAdrs (forsPkAdrs bpos.forsAdrs) vp.params.a i =
        forsNodeAdrs bpos.forsAdrs vp.params.a i := rfl
    rw [hfa]
    have hmem : forsNodeAdrs bpos.forsAdrs vp.params.a i ∈ forsTreeAddresses vp.sl := by
      have ha_pos : 0 < vp.sl.params.a := vp.valid.a_pos
      have ha_eq : vp.sl.params.a = vp.params.a := rfl
      rw [← ha_eq]
      simpa [Nat.sub_self] using SLHDSA.Security.mem_forsTreeAddresses vp.sl bpos ⟨i, hi⟩ ha_pos le_rfl
        (idx := 0) (by simp)
    rw [hsub _ (h2.2.2 _ hmem), Option.getD_some])
  dsimp only
  rw [hfold]
  refine ⟨?_, ?_, fun a ha => hpres_none _ _ a ha rfl⟩
  · simpa only [forsAddresses, List.foldl_append] using h3.1
  · intro a ha
    simp only [forsAddresses, List.foldl_append, List.mem_append] at ha ⊢
    rcases ha with (ha₁ | ha₂) | ha₃
    · exact h3.2.1 a (h2.2.1 a (h1.2.2 a ha₁))
    · exact h3.2.1 a (h2.2.2 a ha₂)
    · exact h3.2.2 a ha₃

/-- Every address in `forsAddresses vp` has `type ∈ {3, 4}` (in particular, `type ≠ 0, 1, 2`). -/
theorem type_of_mem_forsAddresses {a : Adrs} (ha : a ∈ forsAddresses vp) :
    a.type = 3 ∨ a.type = 4 := by
  simp only [forsAddresses, List.mem_append] at ha
  rcases ha with (h | h) | h
  · left; simpa [AddrType.toCode] using SLHDSA.Security.type_of_mem_forsLeafAddresses vp.sl h
  · left; simpa [AddrType.toCode] using SLHDSA.Security.type_of_mem_forsTreeAddresses vp.sl h
  · right; simpa [AddrType.toCode] using SLHDSA.Security.type_of_mem_forsRootAddresses vp.sl h

/-- **Complete specification of `hybTreeDet pr 0 pk u`**: at `γ = 0`, every FORS node, WOTS pk,
and XMSS node equals `honestVal`, `pkSl = slRootDet`, every `wotsMsg` equals the honest message
at that position, every `wotsSig` equals `SLHDSA.wotsSign (prEager pr)`, and `HybWotsConsistent`
holds. -/
theorem hybTreeDet_zero_spec (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    let hyb := hybTreeDet pr 0 pk u
    hyb.pkSl = slRootDet pr pk u ∧
    (∀ a ∈ forsAddresses vp, hyb.tbl a = some (honestVal pr pk u a)) ∧
    (∀ pos : LayerPosition vp.sl,
      hyb.tbl (wotsPkAdrs (wotsInstanceAdrs pos)) =
        some (honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)))) ∧
    (∀ (coord : LayerTreeCoord vp.sl) (z j : ℕ), 0 < z → z ≤ vp.sl.params.hp →
      j < 2 ^ (vp.sl.params.hp - z) →
      hyb.tbl (xmssNodeAdrs coord.toAdrs z j) =
        some (honestVal pr pk u (xmssNodeAdrs coord.toAdrs z j))) ∧
    (∀ pos : LayerPosition vp.sl,
      hyb.wotsMsg pos =
        if pos.layer.val = 0 then
          honestVal pr pk u (forsPkAdrs ((pos.toAdrs.setTypeAndClear .forsTree).setKeyPairAddress pos.leaf.val))
        else
          honestVal pr pk u (xmssNodeAdrs (SLHDSA.GeneralHypertree.layerAdrs (pos.layer.val - 1)
            (pos.tree.val * 2 ^ vp.sl.params.hp + pos.leaf.val)) vp.sl.params.hp 0)) ∧
    (∀ pos : LayerPosition vp.sl,
      hyb.wotsSig pos = SLHDSA.wotsSign (prEager pr) (hyb.wotsMsg pos) u pk (wotsInstanceAdrs pos)) ∧
    HybWotsConsistent pr pk hyb := by
  have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
  have hfors := forsPass_det pr pk u
  set tbl₀ := Id.run ((forsAddresses vp).foldlM (fun tbl a => do
    let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
    return Function.update tbl a (some v)) (fun _ => none))
  set cs0 : LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → Id pr.Y :=
    fun pos c b => pure (hybBlockVal pr 0 pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b
      (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c.val)))
  -- Helper: honest WOTS message formula
  let honMsg (pos : LayerPosition vp.sl) : pr.Y :=
    if pos.layer.val = 0 then
      honestVal pr pk u (forsPkAdrs ((pos.toAdrs.setTypeAndClear .forsTree).setKeyPairAddress pos.leaf.val))
    else
      honestVal pr pk u (xmssNodeAdrs (SLHDSA.GeneralHypertree.layerAdrs (pos.layer.val - 1)
        (pos.tree.val * 2 ^ vp.sl.params.hp + pos.leaf.val)) vp.sl.params.hp 0)
  -- Helper: one `buildLeafM` step when `wotsMsgFromTbl acc.tbl pos = honMsg pos`
  have hleaf : ∀ (acc : HybAcc pr) (pos : LayerPosition vp.sl),
      TblSound pr pk u acc.tbl →
      wotsMsgFromTbl pr acc.tbl pos = honMsg pos →
      let r := Id.run (buildLeafM pr (sfDetCall pr pk) cs0 acc pos)
      TblSound pr pk u r.tbl ∧
        (∀ x, acc.tbl x = some (honestVal pr pk u x) → r.tbl x = some (honestVal pr pk u x)) ∧
        r.tbl (wotsPkAdrs (wotsInstanceAdrs pos)) =
          some (honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos))) ∧
        (∀ p', p' ≠ pos → r.wotsMsg p' = acc.wotsMsg p' ∧ r.wotsSig p' = acc.wotsSig p') ∧
        r.wotsMsg pos = honMsg pos ∧
        r.wotsSig pos = SLHDSA.wotsSign (prEager pr) (honMsg pos) u pk (wotsInstanceAdrs pos) := by
    intro acc pos hs hmsg
    unfold buildLeafM
    simp only [Id.run_bind, idRun_ofFnM, sfDetCall, Id.run_pure, cs0]
    have hsig : (Vector.ofFn fun c : Fin vp.sl.params.len =>
        (hybBlockVal pr 0 pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val)
          (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c.val)))) =
        SLHDSA.wotsSign (prEager pr) (honMsg pos) u pk (wotsInstanceAdrs pos) := by
      apply Vector.ext; intro c hc
      rw [hmsg, SLHDSA.wotsSign_eq_ofFn]
      simp only [Vector.getElem_ofFn, hybBlockVal_zero, slChainDet_eq_chain pr]
      rfl
    have htop : (Vector.ofFn fun c : Fin vp.sl.params.len =>
        Id.run (slChainM pr (sfDetCall pr pk) (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
          (hybBlockVal pr 0 pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
            (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val)
            (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c.val)))
          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val)
          (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val))).cast
          (Params.lsl_eq_len vp.valid).symm =
        Vector.ofFn fun i : Fin vp.params.lsl =>
          honestVal pr pk u ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress (vp.params.w - 2)) := by
      apply Vector.ext; intro c hc
      simp only [Vector.getElem_cast, Vector.getElem_ofFn, hybBlockVal_zero]
      change slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c)
        (slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c)
          (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c)) 0
          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c))
        (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c)
        (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c) = _
      have hle := chainStepsCore_le pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c
      have hcomp := slChainDet_compose pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c)
        (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c)) 0
        (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c)
        (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c)
      rw [Nat.zero_add] at hcomp
      rw [hcomp]
      have hsum : chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c +
          (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c) =
          (vp.params.w - 2) + 1 := by
        have hw' : vp.sl.params.w = vp.params.w := rfl; rw [hw'] at hle ⊢; omega
      rw [hsum, slChainDet_eq_chain pr]
      have hch := honestVal_eq_wotsChain pr pk u (wotsInstanceAdrs pos) c (vp.params.w - 2)
      exact hch.symm
    have hwpk : pr.memberEval .thLsl pk (wotsPkAdrs (wotsInstanceAdrs pos))
        ((Vector.ofFn fun c : Fin vp.sl.params.len =>
          Id.run (slChainM pr (sfDetCall pr pk) (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
            (hybBlockVal pr 0 pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
              (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val)
              (slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c.val)))
            (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val)
            (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val))).cast
          (Params.lsl_eq_len vp.valid).symm) =
        honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) := by
      rw [htop, honestVal_wotsPk]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b v hb
      by_cases hba : b = wotsPkAdrs (wotsInstanceAdrs pos)
      · subst hba; simp only [Function.update_self, Option.some.injEq, Vector.getElem_ofFn] at hb
        exact hb.symm.trans hwpk
      · simp only [Function.update_of_ne hba] at hb; exact hs b v hb
    · intro x hx
      by_cases hxa : x = wotsPkAdrs (wotsInstanceAdrs pos)
      · subst hxa; simp [Vector.getElem_ofFn, hwpk]
      · simp [Function.update_of_ne hxa, hx]
    · simp [Vector.getElem_ofFn, hwpk]
    · intro p' hp'
      exact ⟨Function.update_of_ne hp' _ _, Function.update_of_ne hp' _ _⟩
    · simp [hmsg]
    · simpa [Function.update_self] using hsig
  -- Helper: one `buildTreeM` step when all inputs strictly below `coord.layer` are already in `acc.tbl`
  have htree : ∀ (acc : HybAcc pr) (coord : LayerTreeCoord vp.sl),
      TblSound pr pk u acc.tbl →
      (∀ a ∈ forsAddresses vp, acc.tbl a = some (honestVal pr pk u a)) →
      (∀ (c' : LayerTreeCoord vp.sl), c'.layer.val < coord.layer.val →
        acc.tbl (xmssNodeAdrs c'.toAdrs vp.sl.params.hp 0) =
          some (honestVal pr pk u (xmssNodeAdrs c'.toAdrs vp.sl.params.hp 0))) →
      let r := Id.run (buildTreeM pr (sfDetCall pr pk) cs0 acc coord)
      TblSound pr pk u r.tbl ∧
        (∀ x, acc.tbl x = some (honestVal pr pk u x) → r.tbl x = some (honestVal pr pk u x)) ∧
        (∀ lf : Fin (2 ^ vp.sl.params.hp),
          r.tbl (wotsPkAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf⟩)) =
            some (honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf⟩)))) ∧
        (∀ z j, 0 < z → z ≤ vp.sl.params.hp → j < 2 ^ (vp.sl.params.hp - z) →
          r.tbl (xmssNodeAdrs coord.toAdrs z j) =
            some (honestVal pr pk u (xmssNodeAdrs coord.toAdrs z j))) ∧
        (∀ p', p'.layer ≠ coord.layer ∨ p'.tree.val ≠ coord.tree.val →
          r.wotsMsg p' = acc.wotsMsg p' ∧ r.wotsSig p' = acc.wotsSig p') ∧
        (∀ lf : Fin (2 ^ vp.sl.params.hp),
          let pos : LayerPosition vp.sl := ⟨coord.layer, coord.tree, lf⟩
          r.wotsMsg pos = honMsg pos ∧
          r.wotsSig pos = SLHDSA.wotsSign (prEager pr) (honMsg pos) u pk (wotsInstanceAdrs pos)) := by
    intro acc coord hs hfa hbelow
    have hmsg_ready : ∀ (t : Adrs → Option pr.Y),
        (∀ x, acc.tbl x = some (honestVal pr pk u x) → t x = some (honestVal pr pk u x)) →
        ∀ lf : Fin (2 ^ vp.sl.params.hp),
          wotsMsgFromTbl pr t ⟨coord.layer, coord.tree, lf⟩ =
            honMsg ⟨coord.layer, coord.tree, lf⟩ := by
      intro t hsub lf
      unfold wotsMsgFromTbl
      dsimp only [honMsg]
      split_ifs with h0
      · have hb : ∃ bpos : BottomPosition vp.sl,
            bpos.forsAdrs = (((⟨coord.layer, coord.tree, lf⟩ : LayerPosition vp.sl).toAdrs.setTypeAndClear
              .forsTree).setKeyPairAddress lf.val) := by
          refine ⟨⟨coord.tree.cast (by rw [h0]), lf⟩, ?_⟩
          simp [BottomPosition.forsAdrs, BottomPosition.toLayerPosition, LayerPosition.toAdrs, h0]
        obtain ⟨bpos, hb⟩ := hb
        have hmem : forsPkAdrs bpos.forsAdrs ∈ forsAddresses vp := by
          simp only [forsAddresses, List.mem_append]
          right; exact SLHDSA.Security.mem_forsRootAddresses vp.sl bpos
        rw [← hb, hsub _ (hfa _ hmem), Option.getD_some]
      · have hlt : coord.layer.val - 1 < vp.sl.params.d := by omega
        have htr_lt : coord.tree.val * 2 ^ vp.sl.params.hp + lf.val <
            2 ^ layerTreeHeight vp.sl (coord.layer.val - 1) := by
          have hexp : layerTreeHeight vp.sl (coord.layer.val - 1) =
              layerTreeHeight vp.sl coord.layer.val + vp.sl.params.hp := by
            unfold layerTreeHeight
            have : vp.sl.params.d - (coord.layer.val - 1 + 1) =
                (vp.sl.params.d - (coord.layer.val + 1)) + 1 := by omega
            rw [this, Nat.add_mul, one_mul]
          rw [hexp, pow_add]
          have h1 := coord.tree.isLt
          have h2 := lf.isLt
          nlinarith
        let c' : LayerTreeCoord vp.sl := ⟨⟨coord.layer.val - 1, hlt⟩, ⟨_, htr_lt⟩⟩
        have hc' : c'.toAdrs = SLHDSA.GeneralHypertree.layerAdrs (coord.layer.val - 1)
            (coord.tree.val * 2 ^ vp.sl.params.hp + lf.val) := rfl
        rw [← hc', hsub _ (hbelow c' (by dsimp [c']; omega)), Option.getD_some]
    -- Fold over leaves `List.finRange (2 ^ hp)`
    have hleaves : ∀ (l : List (Fin (2 ^ vp.sl.params.hp))) (a0 : HybAcc pr),
        l.Nodup →
        TblSound pr pk u a0.tbl →
        (∀ x, acc.tbl x = some (honestVal pr pk u x) → a0.tbl x = some (honestVal pr pk u x)) →
        let r := Id.run (l.foldlM (fun a lf => buildLeafM pr (sfDetCall pr pk) cs0 a ⟨coord.layer, coord.tree, lf⟩) a0)
        TblSound pr pk u r.tbl ∧
          (∀ x, a0.tbl x = some (honestVal pr pk u x) → r.tbl x = some (honestVal pr pk u x)) ∧
          (∀ lf ∈ l,
            r.tbl (wotsPkAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf⟩)) =
              some (honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf⟩))) ∧
            r.wotsMsg ⟨coord.layer, coord.tree, lf⟩ = honMsg ⟨coord.layer, coord.tree, lf⟩ ∧
            r.wotsSig ⟨coord.layer, coord.tree, lf⟩ =
              SLHDSA.wotsSign (prEager pr) (honMsg ⟨coord.layer, coord.tree, lf⟩) u pk
                (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf⟩)) ∧
          (∀ p', (∀ lf ∈ l, p' ≠ ⟨coord.layer, coord.tree, lf⟩) →
            r.wotsMsg p' = a0.wotsMsg p' ∧ r.wotsSig p' = a0.wotsSig p') := by
      intro l; induction l with
      | nil =>
        intro a0 _ hs0 _
        exact ⟨hs0, fun _ h => h, fun _ h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
      | cons lf lfs ih =>
        intro a0 hnd hs0 hsub0
        rw [List.nodup_cons] at hnd
        have h1 := hleaf a0 ⟨coord.layer, coord.tree, lf⟩ hs0 (hmsg_ready a0.tbl hsub0 lf)
        set a1 := Id.run (buildLeafM pr (sfDetCall pr pk) cs0 a0 ⟨coord.layer, coord.tree, lf⟩)
        have h2 := ih a1 hnd.2 h1.1 (fun x hx => h1.2.1 x (hsub0 x hx))
        simp only [List.foldlM_cons, Id.run_bind]
        refine ⟨h2.1, fun x hx => h2.2.1 x (h1.2.1 x hx), fun lf' hlf' => ?_, fun p' hp' => ?_⟩
        · rcases List.mem_cons.1 hlf' with rfl | hlf''
          · have hne : ∀ lf2 ∈ lfs, (⟨coord.layer, coord.tree, lf'⟩ : LayerPosition vp.sl) ≠
                ⟨coord.layer, coord.tree, lf2⟩ := fun lf2 hlf2 heq =>
              hnd.1 (by have : lf' = lf2 := congrArg LayerPosition.leaf heq; exact this ▸ hlf2)
            have hpres := h2.2.2.2 _ hne
            exact ⟨h2.2.1 _ h1.2.2.1, hpres.1.trans h1.2.2.2.2.1, hpres.2.trans h1.2.2.2.2.2⟩
          · exact h2.2.2.1 lf' hlf''
        · have hne1 : p' ≠ ⟨coord.layer, coord.tree, lf⟩ := hp' lf (by simp)
          have hpres2 := h2.2.2.2 p' (fun lf2 hlf2 => hp' lf2 (by simp [hlf2]))
          have hpres1 := h1.2.2.2.1 p' hne1
          exact ⟨hpres2.1.trans hpres1.1, hpres2.2.trans hpres1.2⟩
    have hlAll := hleaves (List.finRange (2 ^ vp.sl.params.hp)) acc (List.nodup_finRange _) hs (fun _ h => h)
    set acc₁ := Id.run ((List.finRange (2 ^ vp.sl.params.hp)).foldlM
      (fun a lf => buildLeafM pr (sfDetCall pr pk) cs0 a ⟨coord.layer, coord.tree, lf⟩) acc)
    -- Fold over `perfectInternalCoords hp`
    have hxmss : ∀ (rem z : ℕ), z + rem = vp.sl.params.hp →
        ∀ (tbl : Adrs → Option pr.Y),
        TblSound pr pk u tbl →
        (∀ j < 2 ^ (vp.sl.params.hp - z),
          tbl (xmssCellAdrs coord.toAdrs z j) = some (honestVal pr pk u (xmssCellAdrs coord.toAdrs z j))) →
        let l := (perfectInternalCoords rem).map fun zi => (zi.1 + z, zi.2)
        let r := Id.run (l.foldlM (fun t zi => do
          let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
          let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
          let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
          let v ← sfDetCall pr pk .H a (lv, rv)
          return Function.update t a (some v)) tbl)
        TblSound pr pk u r ∧
          (∀ x, tbl x = some (honestVal pr pk u x) → r x = some (honestVal pr pk u x)) ∧
          (∀ zi ∈ l, r (xmssNodeAdrs coord.toAdrs zi.1 zi.2) =
            some (honestVal pr pk u (xmssNodeAdrs coord.toAdrs zi.1 zi.2))) := by
      intro rem; induction rem with
      | zero =>
        intro z _ tbl hst _
        exact ⟨hst, fun _ h => h, fun _ h => by simp [perfectInternalCoords] at h⟩
      | succ rem ih =>
        intro z hz tbl hst hlv
        have hsp : ((perfectInternalCoords (rem + 1)).map fun zi => (zi.1 + z, zi.2)) =
          ((List.range (2 ^ rem)).map fun j => (z + 1, j)) ++
          ((perfectInternalCoords rem).map fun zi => (zi.1 + (z + 1), zi.2)) := by
          simp only [perfectInternalCoords, List.map_append, List.map_map, Function.comp_def]
          congr 1
          · apply List.map_congr_left; intro j _; congr 1; omega
          · apply List.map_congr_left; intro zi _; congr 1; omega
        dsimp only
        rw [hsp, List.foldlM_append, Id.run_bind]
        have hpow : 2 ^ (vp.sl.params.hp - z) = 2 * 2 ^ (vp.sl.params.hp - (z + 1)) := by
          rw [show vp.sl.params.hp - z = (vp.sl.params.hp - (z + 1)) + 1 by omega, pow_succ, Nat.mul_comm]
        have hcur : ∀ (js : List ℕ) (t0 : Adrs → Option pr.Y),
            (∀ j ∈ js, j < 2 ^ rem) →
            TblSound pr pk u t0 →
            (∀ j < 2 ^ (vp.sl.params.hp - z),
              t0 (xmssCellAdrs coord.toAdrs z j) = some (honestVal pr pk u (xmssCellAdrs coord.toAdrs z j))) →
            let r := Id.run ((js.map fun j => (z + 1, j)).foldlM (fun t zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← sfDetCall pr pk .H a (lv, rv)
              return Function.update t a (some v)) t0)
            TblSound pr pk u r ∧
              (∀ x, t0 x = some (honestVal pr pk u x) → r x = some (honestVal pr pk u x)) ∧
              (∀ j ∈ js, r (xmssNodeAdrs coord.toAdrs (z + 1) j) =
                some (honestVal pr pk u (xmssNodeAdrs coord.toAdrs (z + 1) j))) := by
          intro js; induction js with
          | nil => intro t0 _ ht0 _; exact ⟨ht0, fun _ h => h, fun _ h => by simp at h⟩
          | cons j js' ihj =>
            intro t0 hjs ht0 hlv0
            have hjlt : j < 2 ^ (vp.sl.params.hp - (z + 1)) := by
              rw [show vp.sl.params.hp - (z + 1) = rem by omega]; exact hjs j (by simp)
            have hL := hlv0 (2 * j) (by rw [hpow]; omega)
            have hR := hlv0 (2 * j + 1) (by rw [hpow]; omega)
            have hval : pr.H pk (xmssNodeAdrs coord.toAdrs (z + 1) j)
                ((t0 (xmssCellAdrs coord.toAdrs z (2 * j))).getD default)
                ((t0 (xmssCellAdrs coord.toAdrs z (2 * j + 1))).getD default) =
                honestVal pr pk u (xmssNodeAdrs coord.toAdrs (z + 1) j) := by
              rw [hL, hR, Option.getD_some, Option.getD_some]
              exact (honestVal_xmssCell_succ pr pk u coord.toAdrs z j).symm
            set t1 := Function.update t0 (xmssNodeAdrs coord.toAdrs (z + 1) j)
              (some (pr.H pk (xmssNodeAdrs coord.toAdrs (z + 1) j)
                ((t0 (xmssCellAdrs coord.toAdrs z (2 * j))).getD default)
                ((t0 (xmssCellAdrs coord.toAdrs z (2 * j + 1))).getD default)))
            have ht1 : TblSound pr pk u t1 := by
              intro b v hb
              by_cases hba : b = xmssNodeAdrs coord.toAdrs (z + 1) j
              · subst hba; simp only [t1, Function.update_self, Option.some.injEq] at hb; exact hb.symm.trans hval
              · simp only [t1, Function.update_of_ne hba] at hb; exact ht0 b v hb
            have hsub1 : ∀ x, t0 x = some (honestVal pr pk u x) → t1 x = some (honestVal pr pk u x) := by
              intro x hx; by_cases hxa : x = xmssNodeAdrs coord.toAdrs (z + 1) j
              · subst hxa; simp [t1, hval]
              · simp [t1, Function.update_of_ne hxa, hx]
            have hrest := ihj t1 (fun j' hj' => hjs j' (by simp [hj'])) ht1 (fun k hk => hsub1 _ (hlv0 k hk))
            simp only [List.map_cons, List.foldlM_cons, Id.run_bind, sfDetCall, Id.run_pure, Nat.add_sub_cancel]
            refine ⟨hrest.1, fun x hx => hrest.2.1 x (hsub1 x hx), fun j' hj' => ?_⟩
            rcases List.mem_cons.1 hj' with rfl | hj''
            · exact hrest.2.1 _ (by simp [t1, hval])
            · exact hrest.2.2 j' hj''
        have h1 := hcur (List.range (2 ^ rem)) tbl (fun j hj => List.mem_range.1 hj) hst hlv
        have h2 := ih (z + 1) (by omega) _ h1.1 (fun j hj => by
          simpa [xmssCellAdrs] using h1.2.2 j (List.mem_range.2 (by rw [show rem = vp.sl.params.hp - (z + 1) by omega]; exact hj)))
        refine ⟨h2.1, fun x hx => h2.2.1 x (h1.2.1 x hx), fun zi hzi => ?_⟩
        rcases List.mem_append.1 hzi with hzi₁ | hzi₂
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hzi₁
          exact h2.2.1 _ (h1.2.2 j hj)
        · exact h2.2.2 zi hzi₂
    have hxAll := hxmss vp.sl.params.hp 0 (Nat.zero_add _) acc₁.tbl hlAll.1 (fun j hj => by
      have hmem : (⟨j, hj⟩ : Fin (2 ^ vp.sl.params.hp)) ∈ List.finRange (2 ^ vp.sl.params.hp) :=
        List.mem_finRange _
      have hpk := (hlAll.2.2.1 ⟨j, hj⟩ hmem).1
      have hEq : wotsLeafAdrs coord.toAdrs j = wotsInstanceAdrs ⟨coord.layer, coord.tree, ⟨j, hj⟩⟩ :=
        wotsLeafAdrs_eq_wotsInstanceAdrs' ⟨coord.layer, coord.tree, ⟨j, hj⟩⟩
      rw [xmssCellAdrs, hEq]
      exact hpk)
    have hmap_id : (perfectInternalCoords vp.sl.params.hp).map (fun zi => (zi.1 + 0, zi.2)) =
        perfectInternalCoords vp.sl.params.hp := by
      simp
    rw [hmap_id] at hxAll
    unfold buildTreeM
    simp only [Id.run_bind, Id.run_pure]
    refine ⟨hxAll.1, fun x hx => hxAll.2.1 x (hlAll.2.1 x hx), fun lf => ?_,
      fun z j hz hzh hj => ?_, fun p' hp' => ?_, fun lf => ?_⟩
    · exact hxAll.2.1 _ (hlAll.2.2.1 lf (List.mem_finRange _)).1
    · exact hxAll.2.2 (z, j) (SLHDSA.Security.mem_perfectInternalCoords_of_bounds hz hzh hj)
    · exact hlAll.2.2.2 p' (fun lf _ heq => by
        rcases hp' with h1 | h2
        · exact h1 (congrArg LayerPosition.layer heq)
        · exact h2 (congrArg (fun p : LayerPosition vp.sl => p.tree.val) heq))
    · exact (hlAll.2.2.1 lf (List.mem_finRange _)).2
  -- Fold `buildTreeM` over layers `0, …, d - 1`
  have hlayers : ∀ (k : ℕ) (hk : k ≤ vp.sl.params.d),
      let ts := ((List.finRange vp.sl.params.d).take k).flatMap fun layer =>
        (List.finRange (2 ^ layerTreeHeight vp.sl layer.val)).map fun tree =>
          (⟨layer, tree⟩ : LayerTreeCoord vp.sl)
      let r := Id.run (ts.foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
        ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)
      TblSound pr pk u r.tbl ∧
        (∀ a ∈ forsAddresses vp, r.tbl a = some (honestVal pr pk u a)) ∧
        (∀ pos : LayerPosition vp.sl, pos.layer.val < k →
          r.tbl (wotsPkAdrs (wotsInstanceAdrs pos)) =
            some (honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos))) ∧
          r.wotsMsg pos = honMsg pos ∧
          r.wotsSig pos = SLHDSA.wotsSign (prEager pr) (honMsg pos) u pk (wotsInstanceAdrs pos)) ∧
        (∀ (coord : LayerTreeCoord vp.sl), coord.layer.val < k →
          ∀ z j, 0 < z → z ≤ vp.sl.params.hp → j < 2 ^ (vp.sl.params.hp - z) →
            r.tbl (xmssNodeAdrs coord.toAdrs z j) =
              some (honestVal pr pk u (xmssNodeAdrs coord.toAdrs z j))) := by
    intro k; induction k with
    | zero =>
      intro _
      exact ⟨hfors.1, hfors.2.1, fun _ h => by omega, fun _ h => by omega⟩
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have htake : (List.finRange vp.sl.params.d).take (k + 1) =
          (List.finRange vp.sl.params.d).take k ++ [⟨k, by omega⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; change k < vp.sl.params.d; omega)]
        simp
      dsimp only
      rw [htake, List.flatMap_append, List.flatMap_singleton, List.foldlM_append, Id.run_bind]
      set accK := Id.run ((((List.finRange vp.sl.params.d).take k).flatMap fun layer =>
        (List.finRange (2 ^ layerTreeHeight vp.sl layer.val)).map fun tree =>
          (⟨layer, tree⟩ : LayerTreeCoord vp.sl)).foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
        ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)
      have htrees : ∀ (trs : List (Fin (2 ^ layerTreeHeight vp.sl k))) (a0 : HybAcc pr),
          trs.Nodup →
          TblSound pr pk u a0.tbl →
          (∀ x, accK.tbl x = some (honestVal pr pk u x) → a0.tbl x = some (honestVal pr pk u x)) →
          let r := Id.run ((trs.map fun tr => (⟨⟨k, by omega⟩, tr⟩ : LayerTreeCoord vp.sl)).foldlM
            (buildTreeM pr (sfDetCall pr pk) cs0) a0)
          TblSound pr pk u r.tbl ∧
            (∀ x, a0.tbl x = some (honestVal pr pk u x) → r.tbl x = some (honestVal pr pk u x)) ∧
            (∀ tr ∈ trs, ∀ lf : Fin (2 ^ vp.sl.params.hp),
              let pos : LayerPosition vp.sl := ⟨⟨k, by omega⟩, tr, lf⟩
              r.tbl (wotsPkAdrs (wotsInstanceAdrs pos)) =
                some (honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos))) ∧
              r.wotsMsg pos = honMsg pos ∧
              r.wotsSig pos = SLHDSA.wotsSign (prEager pr) (honMsg pos) u pk (wotsInstanceAdrs pos)) ∧
            (∀ tr ∈ trs, ∀ z j, 0 < z → z ≤ vp.sl.params.hp → j < 2 ^ (vp.sl.params.hp - z) →
              r.tbl (xmssNodeAdrs (⟨⟨k, by omega⟩, tr⟩ : LayerTreeCoord vp.sl).toAdrs z j) =
                some (honestVal pr pk u (xmssNodeAdrs (⟨⟨k, by omega⟩, tr⟩ : LayerTreeCoord vp.sl).toAdrs z j))) ∧
            (∀ p', p'.layer.val ≠ k ∨ (∀ tr ∈ trs, p'.tree.val ≠ tr.val) →
              r.wotsMsg p' = a0.wotsMsg p' ∧ r.wotsSig p' = a0.wotsSig p') := by
        intro trs; induction trs with
        | nil =>
          intro a0 _ hs0 _
          exact ⟨hs0, fun _ h => h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
        | cons tr trs' iht =>
          intro a0 hnd hs0 hsub0
          rw [List.nodup_cons] at hnd
          have h1 := htree a0 ⟨⟨k, by omega⟩, tr⟩ hs0
            (fun a ha => hsub0 _ (hprev.2.1 a ha))
            (fun c' hc' => hsub0 _ (hprev.2.2.2 c' hc' vp.sl.params.hp 0 vp.valid.hp_pos le_rfl (by simp)))
          set a1 := Id.run (buildTreeM pr (sfDetCall pr pk) cs0 a0 ⟨⟨k, by omega⟩, tr⟩)
          have h2 := iht a1 hnd.2 h1.1 (fun x hx => h1.2.1 x (hsub0 x hx))
          simp only [List.map_cons, List.foldlM_cons, Id.run_bind]
          refine ⟨h2.1, fun x hx => h2.2.1 x (h1.2.1 x hx), fun tr' htr' lf => ?_,
            fun tr' htr' z j hz hzh hj => ?_, fun p' hp' => ?_⟩
          · rcases List.mem_cons.1 htr' with rfl | htr''
            · have hpres := h2.2.2.2.2 ⟨⟨k, by omega⟩, tr', lf⟩ (Or.inr fun t2 ht2 heq =>
                hnd.1 (by have : tr' = t2 := Fin.ext heq; exact this ▸ ht2))
              exact ⟨h2.2.1 _ (h1.2.2.1 lf), hpres.1.trans (h1.2.2.2.2.2 lf).1,
                hpres.2.trans (h1.2.2.2.2.2 lf).2⟩
            · exact h2.2.2.1 tr' htr'' lf
          · rcases List.mem_cons.1 htr' with rfl | htr''
            · exact h2.2.1 _ (h1.2.2.2.1 z j hz hzh hj)
            · exact h2.2.2.2.1 tr' htr'' z j hz hzh hj
          · have hpres2 := h2.2.2.2.2 p' (hp'.imp_right fun h t2 ht2 => h t2 (by simp [ht2]))
            have hpres1 := h1.2.2.2.2.1 p' (hp'.imp (fun h heq => h (congrArg Fin.val heq))
              (fun h => h tr (by simp)))
            exact ⟨hpres2.1.trans hpres1.1, hpres2.2.trans hpres1.2⟩
      have htrAll := htrees (List.finRange (2 ^ layerTreeHeight vp.sl k)) accK
        (List.nodup_finRange _) hprev.1 (fun _ h => h)
      refine ⟨htrAll.1, fun a ha => htrAll.2.1 a (hprev.2.1 a ha), fun pos hpos => ?_,
        fun coord hcoord z j hz hzh hj => ?_⟩
      · by_cases heq : pos.layer.val = k
        · rcases pos with ⟨⟨l, hl⟩, tree, leaf⟩
          dsimp only at heq; subst heq
          exact htrAll.2.2.1 tree (List.mem_finRange _) leaf
        · have hlt : pos.layer.val < k := by omega
          have hp := hprev.2.2.1 pos hlt
          have hpres := htrAll.2.2.2.2 pos (Or.inl heq)
          exact ⟨htrAll.2.1 _ hp.1, hpres.1.trans hp.2.1, hpres.2.trans hp.2.2⟩
      · by_cases heq : coord.layer.val = k
        · rcases coord with ⟨⟨l, hl⟩, tree⟩
          dsimp only at heq; subst heq
          exact htrAll.2.2.2.1 tree (List.mem_finRange _) z j hz hzh hj
        · exact htrAll.2.1 _ (hprev.2.2.2 coord (by omega) z j hz hzh hj)
  have hall := hlayers vp.sl.params.d le_rfl
  have htake_all : (List.finRange vp.sl.params.d).take vp.sl.params.d = List.finRange vp.sl.params.d := by
    simp
  simp only [htake_all] at hall
  have hfold_eq : ((List.finRange vp.sl.params.d).flatMap fun layer =>
      (List.finRange (2 ^ layerTreeHeight vp.sl layer.val)).map fun tree =>
        (⟨layer, tree⟩ : LayerTreeCoord vp.sl)) = allXmssTreesList vp := rfl
  rw [hfold_eq] at hall
  have htop : (hybTreeDet pr 0 pk u).pkSl = slRootDet pr pk u := by
    rw [slRootDet_eq_honestVal]
    unfold hybTreeDet buildHybTreeM
    change ((Id.run ((allXmssTreesList vp).foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
      ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)).tbl
      (xmssNodeAdrs (LayerTreeCoord.top vp.sl).toAdrs vp.sl.params.hp 0)).getD default = _
    have hmem := hall.2.2.2 (LayerTreeCoord.top vp.sl) (LayerTreeCoord.top vp.sl).layer.isLt
      vp.sl.params.hp 0 vp.valid.hp_pos le_rfl (by simp)
    rw [hmem, Option.getD_some]; rfl
  refine ⟨htop, hall.2.1, fun pos => (hall.2.2.1 pos pos.layer.isLt).1,
    fun coord z j hz hzh hj => hall.2.2.2 coord coord.layer.isLt z j hz hzh hj,
    fun pos => (hall.2.2.1 pos pos.layer.isLt).2.1,
    fun pos => (hall.2.2.1 pos pos.layer.isLt).2.2.trans (by
      change SLHDSA.wotsSign (prEager pr) (honMsg pos) u pk (wotsInstanceAdrs pos) =
        SLHDSA.wotsSign (prEager pr) ((Id.run ((allXmssTreesList vp).foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
          ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)).wotsMsg pos) u pk (wotsInstanceAdrs pos)
      rw [(hall.2.2.1 pos pos.layer.isLt).2.1]), ?_⟩
  intro pos
  change ((Id.run ((allXmssTreesList vp).foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
      ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)).tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default = _
  rw [(hall.2.2.1 pos pos.layer.isLt).1, Option.getD_some]
  change _ = SLHDSA.wotsPkFromSig (prEager pr)
    ((Id.run ((allXmssTreesList vp).foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
      ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)).wotsSig pos)
    ((Id.run ((allXmssTreesList vp).foldlM (buildTreeM pr (sfDetCall pr pk) cs0)
      ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)).wotsMsg pos) pk (wotsInstanceAdrs pos)
  rw [(hall.2.2.1 pos pos.layer.isLt).2.1, (hall.2.2.1 pos pos.layer.isLt).2.2,
    SLHDSA.wotsPkFromSig_wotsSign, ← honestVal_eq_wotsPkGen pr pk u (wotsInstanceAdrs pos)]

omit [Inhabited pr.Y] in
/-- Helper: `Vector.ofFn` of sibling values equals `PerfectMerkleTree.intrinsicAuthPath`. -/
private theorem vector_ofFn_eq_intrinsicAuthPath {H : ℕ} (val : ℕ → ℕ → pr.Y)
    (leaf : ℕ → pr.Y) (node : ℕ → ℕ → pr.Y → pr.Y → pr.Y)
    (h : ∀ z t, z ≤ H → t < 2 ^ (H - z) → PerfectMerkleTree.merkleRoot leaf node z t = val z t)
    {idx : ℕ} (hidx : idx < 2 ^ H) :
    ∀ k, k ≤ H →
      (Vector.ofFn fun j : Fin k => val j.val (PerfectMerkleTree.sibling (idx / 2 ^ j.val))) =
        PerfectMerkleTree.intrinsicAuthPath leaf node idx k := by
  intro k; induction k with
  | zero => intro _; apply Vector.ext; intro i hi; omega
  | succ k ih =>
    intro hk
    simp only [PerfectMerkleTree.intrinsicAuthPath]
    have hsib : PerfectMerkleTree.sibling (idx / 2 ^ k) < 2 ^ (H - k) := by
      have hq : idx / 2 ^ k < 2 ^ (H - k) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
        exact hidx
      unfold PerfectMerkleTree.sibling
      split_ifs with hev
      · obtain ⟨m, hm⟩ := dvd_pow_self 2 (by omega : H - k ≠ 0)
        omega
      · exact (Nat.sub_le _ _).trans_lt hq
    rw [← ih (by omega), h k _ (by omega) hsib]
    apply Vector.ext; intro i hi
    by_cases hlt : i < k
    · simp [Vector.getElem_push_lt hlt]
    · have : i = k := by omega
      subst this; simp

/-- **Zero-`Th_λ` signing agreement at `γ = 0`**: `hybSign` on `hybTreeDet pr 0 pk u` produces the
EXACT same `Stateless.Sig pr` as `slSignDet`. -/
theorem hybSign_zero_eq_slSignDet (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (R : pr.Y) :
    hybSign pr pk (hybTreeDet pr 0 pk u) u msg R =
      slSignDet pr pk (slRootDet pr pk u) u msg R := by
  have hspec := hybTreeDet_zero_spec pr pk u
  set hyb := hybTreeDet pr 0 pk u
  -- Also compare via `prEager pr u` (`GeneralScheme.signInternalWithRandomizer`) or `slSignTable`!
  -- Actually, compare field by field against `slSignDet` directly using `Bridge`!
  have htbl_fors : ∀ (parts : DigestParts vp.sl.params) (i : Fin vp.sl.params.k) (z t : ℕ),
      z ≤ vp.sl.params.a → t < 2 ^ (vp.sl.params.a - z) →
      hyb.tbl (forsNodeAdrs parts.forsAdrs z (i.val * 2 ^ (vp.sl.params.a - z) + t)) =
        some (honestVal pr pk u (forsNodeAdrs parts.forsAdrs z (i.val * 2 ^ (vp.sl.params.a - z) + t))) := by
    intro parts i z t hza ht
    let bpos := BottomPosition.ofDigestParts vp.sl parts
    have hfa : bpos.forsAdrs = parts.forsAdrs := BottomPosition.forsAdrs_ofDigestParts vp.sl parts
    rw [← hfa]
    rcases z with _ | z
    · exact hspec.2.1 _ (by
        simp only [forsAddresses, List.mem_append]
        left; left
        have hmem := SLHDSA.Security.mem_forsLeafAddresses vp.sl bpos i ⟨t, by simpa [SLHDSA.Params.t] using ht⟩
        simpa [SLHDSA.Params.t] using hmem)
    · exact hspec.2.1 _ (by
        simp only [forsAddresses, List.mem_append]
        left; right
        exact SLHDSA.Security.mem_forsTreeAddresses vp.sl bpos i (Nat.succ_pos z) hza ht)
  have htbl_xmss : ∀ (coord : LayerTreeCoord vp.sl) (z t : ℕ),
      z ≤ vp.sl.params.hp → t < 2 ^ (vp.sl.params.hp - z) →
      hyb.tbl (xmssCellAdrs coord.toAdrs z t) =
        some (honestVal pr pk u (xmssCellAdrs coord.toAdrs z t)) := by
    intro coord z t hzh ht
    rcases z with _ | z
    · have hEq : wotsLeafAdrs coord.toAdrs t = wotsInstanceAdrs ⟨coord.layer, coord.tree, ⟨t, by simpa using ht⟩⟩ :=
        wotsLeafAdrs_eq_wotsInstanceAdrs' ⟨coord.layer, coord.tree, ⟨t, by simpa using ht⟩⟩
      rw [xmssCellAdrs, hEq]
      exact hspec.2.2.1 ⟨coord.layer, coord.tree, ⟨t, by simpa using ht⟩⟩
    · exact hspec.2.2.2.1 coord (z + 1) t (Nat.succ_pos z) hzh ht
  have hsign_det : ∀ (s₁ s₂ : Stateless.Sig pr),
      s₁.randomness = s₂.randomness →
      (∀ i (hi : i < vp.sl.params.k), s₁.fors[i].sk = s₂.fors[i].sk ∧ s₁.fors[i].auth = s₂.fors[i].auth) →
      (∀ ℓ (hℓ : ℓ < vp.sl.params.d), s₁.hypertree[ℓ].wots = s₂.hypertree[ℓ].wots ∧
        s₁.hypertree[ℓ].auth = s₂.hypertree[ℓ].auth) →
      s₁ = s₂ := by
    rintro ⟨r₁, f₁, h₁⟩ ⟨r₂, f₂, h₂⟩ hr hf hh
    subst hr
    have hf' : f₁ = f₂ := by
      apply Vector.ext; intro i hi
      obtain ⟨hsk, hau⟩ := hf i hi
      cases hf1 : f₁[i]; cases hf2 : f₂[i]
      simp only [hf1, hf2] at hsk hau; subst hsk; subst hau; rfl
    have hh' : h₁ = h₂ := by
      apply Vector.ext; intro ℓ hℓ
      obtain ⟨hw, hau⟩ := hh ℓ hℓ
      cases hh1 : h₁[ℓ]; cases hh2 : h₂[ℓ]
      simp only [hh1, hh2] at hw hau; subst hw; subst hau; rfl
    subst hf'; subst hh'; rfl
  -- Identify `slSignDet` via `GeneralScheme.signInternalWithSecretRandomizerM` under `pubQ`
  unfold hybSign slSignDet
  rw [hspec.1]
  set parts := splitDigest vp.sl.params (pr.HmsgSl R pk (slRootDet pr pk u) msg)
  apply hsign_det
  · rfl
  · intro i hi
    -- Compare FORS tree `i`
    simp only [SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM, SLHDSA.forsSignWithSecretM,
      SLHDSA.forsSignWithSecret, SLHDSA.PublicHash.hmsg, HasQuery.query, Id.run_bind,
      idRun_ofFnM, Id.run_pure, Vector.getElem_ofFn]
    refine ⟨by rw [SLHDSA.Security.forsSigLeafIndex_eq]; rfl, ?_⟩
    have hid_auth : ∀ (leaf : ℕ → Id pr.Y) (node : ℕ → ℕ → pr.Y → pr.Y → Id pr.Y) (idx k : ℕ),
        Id.run (PerfectMerkleTree.intrinsicAuthPathM leaf node idx k) =
        PerfectMerkleTree.intrinsicAuthPath (fun t => Id.run (leaf t))
          (fun z t l r => Id.run (node z t l r)) idx k := by
      intro leaf node idx k; induction k with
      | zero => rfl
      | succ k ihk =>
        have hmr : ∀ z t, Id.run (PerfectMerkleTree.merkleRootM leaf node z t) =
            PerfectMerkleTree.merkleRoot (fun t => Id.run (leaf t))
              (fun z t l r => Id.run (node z t l r)) z t := by
          intro z; induction z with
          | zero => intro t; rfl
          | succ z ihz =>
            intro t
            simp only [PerfectMerkleTree.merkleRootM, PerfectMerkleTree.merkleRoot_succ, Id.run_bind, ihz]
        simp only [PerfectMerkleTree.intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath,
          Id.run_bind, Id.run_pure, ihk, hmr]
    rw [hid_auth]
    -- Use `vector_ofFn_eq_intrinsicAuthPath` on tree `i`!
    -- Wait: `intrinsicAuthPath` at global index `idx = i * 2^a + localIdx`!
    have hidx_eq : forsSigLeafIndex vp.sl.params parts.md.toList i =
        i * 2 ^ vp.sl.params.a + forsIdx vp.sl.params parts.md.toList i :=
      SLHDSA.Security.forsSigLeafIndex_eq vp.sl.params parts.md.toList i
    have hmerkle : ∀ z t, z ≤ vp.sl.params.a → t < 2 ^ (vp.sl.params.a - z) →
        PerfectMerkleTree.merkleRoot
          (fun t => Id.run (SLHDSA.forsLeafWithSecret pr.toSLHDSA.core
            (fun a x => (pure (pr.F pk a x) : Id pr.Y)) (fun a => pure (slSecOf pr u a))
            parts.forsAdrs t))
          (fun z t l r => Id.run (SLHDSA.forsNodeHashWith
            (fun a l r => (pure (pr.H pk a l r) : Id pr.Y)) parts.forsAdrs z t l r))
          z (i * 2 ^ (vp.sl.params.a - z) + t) =
        honestVal pr pk u (forsNodeAdrs parts.forsAdrs z (i * 2 ^ (vp.sl.params.a - z) + t)) := by
      intro z; induction z with
      | zero =>
        intro t _ _
        simp only [PerfectMerkleTree.merkleRoot, SLHDSA.forsLeafWithSecret, Id.run_bind, Id.run_pure]
        exact (honestVal_forsLeaf pr pk u parts.forsAdrs _).symm
      | succ z ih =>
        intro t hza ht
        have hpow : 2 ^ (vp.sl.params.a - z) = 2 * 2 ^ (vp.sl.params.a - (z + 1)) := by
          rw [show vp.sl.params.a - z = (vp.sl.params.a - (z + 1)) + 1 by omega, pow_succ, Nat.mul_comm]
        have h0 : 2 * (i * 2 ^ (vp.sl.params.a - (z + 1)) + t) =
            i * 2 ^ (vp.sl.params.a - z) + 2 * t := by rw [hpow]; ring
        have h1 : 2 * (i * 2 ^ (vp.sl.params.a - (z + 1)) + t) + 1 =
            i * 2 ^ (vp.sl.params.a - z) + (2 * t + 1) := by rw [hpow]; ring
        rw [PerfectMerkleTree.merkleRoot_succ, h0, ih (2 * t) (by omega) (by rw [hpow]; omega),
          Nat.add_assoc, ih (2 * t + 1) (by omega) (by rw [hpow]; omega), ← h1, ← h0]
        exact (honestVal_forsNode_succ pr pk u parts.forsAdrs z _).symm
    have hvec_fors : ∀ k, k ≤ vp.sl.params.a →
        (Vector.ofFn fun j : Fin k => (hyb.tbl (forsNodeAdrs parts.forsAdrs j.val
          (PerfectMerkleTree.sibling ((i * 2 ^ vp.sl.params.a + forsIdx vp.sl.params parts.md.toList i) /
            2 ^ j.val)))).getD default) =
        PerfectMerkleTree.intrinsicAuthPath
          (fun t => Id.run (SLHDSA.forsLeafWithSecret pr.toSLHDSA.core
            (fun a x => (pure (pr.F pk a x) : Id pr.Y)) (fun a => pure (slSecOf pr u a))
            parts.forsAdrs t))
          (fun z t l r => Id.run (SLHDSA.forsNodeHashWith
            (fun a l r => (pure (pr.H pk a l r) : Id pr.Y)) parts.forsAdrs z t l r))
          (i * 2 ^ vp.sl.params.a + forsIdx vp.sl.params parts.md.toList i) k := by
      intro k; induction k with
      | zero => intro _; apply Vector.ext; intro j hj; omega
      | succ k ihk =>
        intro hk
        simp only [PerfectMerkleTree.intrinsicAuthPath]
        rw [← ihk (by omega)]
        obtain ⟨hdiv, hlt⟩ := SLHDSA.Security.forsSigLeafIndex_div_lt vp.sl.params parts.md.toList i k (by omega)
        have hdiv' : (i * 2 ^ vp.sl.params.a + forsIdx vp.sl.params parts.md.toList i) / 2 ^ k =
            i * 2 ^ (vp.sl.params.a - k) + forsIdx vp.sl.params parts.md.toList i / 2 ^ k := by
          rwa [hidx_eq] at hdiv
        have hsib_lt : PerfectMerkleTree.sibling (forsIdx vp.sl.params parts.md.toList i / 2 ^ k) <
            2 ^ (vp.sl.params.a - k) := by
          unfold PerfectMerkleTree.sibling
          split_ifs with hev
          · obtain ⟨m, hm⟩ := dvd_pow_self 2 (by omega : vp.sl.params.a - k ≠ 0); omega
          · exact (Nat.sub_le _ _).trans_lt hlt
        have hsib_eq : PerfectMerkleTree.sibling
            (i * 2 ^ (vp.sl.params.a - k) + forsIdx vp.sl.params parts.md.toList i / 2 ^ k) =
            i * 2 ^ (vp.sl.params.a - k) +
              PerfectMerkleTree.sibling (forsIdx vp.sl.params parts.md.toList i / 2 ^ k) := by
          obtain ⟨m, hm⟩ := dvd_pow_self 2 (by omega : vp.sl.params.a - k ≠ 0)
          have h2 : (i * 2 ^ (vp.sl.params.a - k)) % 2 = 0 := by
            rw [hm, ← Nat.mul_assoc, Nat.mul_comm i 2, Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
          have hpar : (i * 2 ^ (vp.sl.params.a - k) + forsIdx vp.sl.params parts.md.toList i / 2 ^ k) % 2 =
              (forsIdx vp.sl.params parts.md.toList i / 2 ^ k) % 2 := by
            rw [Nat.add_mod, h2, Nat.zero_add, Nat.mod_mod]
          unfold PerfectMerkleTree.sibling
          rw [hpar]
          split_ifs with hev
          · omega
          · have hpos : 0 < forsIdx vp.sl.params parts.md.toList i / 2 ^ k :=
              Nat.pos_of_ne_zero fun h0 => by simp [h0] at hev
            exact Nat.add_sub_assoc hpos _
        rw [hdiv', hsib_eq, hmerkle k _ (by omega) hsib_lt]
        have htb := htbl_fors parts ⟨i, hi⟩ k _ (by omega) hsib_lt
        apply Vector.ext; intro j hj
        by_cases hjk : j < k
        · simp [Vector.getElem_push_lt hjk]
        · have : j = k := by omega
          subst this
          simp only [Vector.getElem_push_eq, Vector.getElem_ofFn, hdiv', hsib_eq, htb, Option.getD_some]
    rw [hidx_eq]
    convert hvec_fors vp.sl.params.a le_rfl using 1
    rfl
  · intro ℓ hℓ
    -- Helper: `Id.run` of `PerfectMerkleTree.intrinsicAuthPathM` and `climbM`
    have hid_auth : ∀ (leaf : ℕ → Id pr.Y) (node : ℕ → ℕ → pr.Y → pr.Y → Id pr.Y) (idx k : ℕ),
        Id.run (PerfectMerkleTree.intrinsicAuthPathM leaf node idx k) =
        PerfectMerkleTree.intrinsicAuthPath (fun t => Id.run (leaf t))
          (fun z t l r => Id.run (node z t l r)) idx k := by
      intro leaf node idx k; induction k with
      | zero => rfl
      | succ k ihk =>
        have hmr : ∀ z t, Id.run (PerfectMerkleTree.merkleRootM leaf node z t) =
            PerfectMerkleTree.merkleRoot (fun t => Id.run (leaf t))
              (fun z t l r => Id.run (node z t l r)) z t := by
          intro z; induction z with
          | zero => intro t; rfl
          | succ z ihz =>
            intro t
            simp only [PerfectMerkleTree.merkleRootM, PerfectMerkleTree.merkleRoot_succ, Id.run_bind, ihz]
        simp only [PerfectMerkleTree.intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath,
          Id.run_bind, Id.run_pure, ihk, hmr]
    have hid_chain : ∀ (a : Adrs) (x : pr.Y) (start steps : ℕ),
        Id.run (letI := pubQ pr Id
          SLHDSA.chainWith (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) a x start steps) =
        SLHDSA.chain (prEager pr) pk a x start steps := by
      intro a x start steps; induction steps with
      | zero => rfl
      | succ steps ih =>
        rw [SLHDSA.chainWith_succ, Id.run_bind, ih, SLHDSA.chain_succ]
        rfl
    have hxmss_sign : ∀ (m0 : pr.Y) (a : Adrs) (idx : ℕ),
        let s1 := Id.run (letI := pubQ pr Id
          SLHDSA.xmssSignWithSecret pr.toSLHDSA.core
            (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
            (fun b => pure (slSecOf pr u b)) m0 a idx)
        let s2 := SLHDSA.xmssSign (prEager pr) m0 u pk a idx
        s1.wots = s2.wots ∧ s1.auth = s2.auth := by
      intro m0 a idx
      rw [SLHDSA.xmssSign_eq_pair]
      simp only [SLHDSA.xmssSignWithSecret, SLHDSA.wotsSignWithSecret, Id.run_bind, Id.run_pure,
        idRun_ofFnM, hid_auth]
      refine ⟨?_, ?_⟩
      · rw [SLHDSA.wotsSign_eq_ofFn]
        apply Vector.ext; intro i hi
        simp only [Vector.getElem_ofFn]
        exact hid_chain _ _ _ _
      · congr 1
        · funext t
          simp only [SLHDSA.xmssLeafWithSecret, SLHDSA.wotsPkGenWithSecret,
            SLHDSA.wotsPkGenTopsWithSecret, Id.run_bind, Id.run_pure, idRun_ofFnM,
            SLHDSA.xmssLeaf_eq_wotsPkGen, SLHDSA.wotsPkGen_eq_tl]
          change pr.Th pk _ _ = pr.Th pk _ _
          congr 1; apply List.ext_getElem
          · simp
          · intro j hj₁ hj₂
            simp only [Vector.getElem_toList, Vector.getElem_ofFn, SLHDSA.wotsPkGenTops_eq_ofFn]
            exact hid_chain _ _ _ _
    have hxmss_pk : ∀ (idx : ℕ) (s1 : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core)
        (s2 : SLHDSA.XmssSig vp.sl.params (prEager pr).core) (m0 : pr.Y) (a : Adrs),
        s1.wots = s2.wots → s1.auth = s2.auth →
        Id.run (letI := pubQ pr Id
          SLHDSA.xmssPkFromSigWith pr.toSLHDSA.core
            (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) idx s1 m0 a) =
        SLHDSA.xmssPkFromSig (prEager pr) idx s2 m0 pk a := by
      intro idx s1 s2 m0 a hw ha
      rw [SLHDSA.xmssPkFromSig_eq_climb]
      simp only [SLHDSA.xmssPkFromSigWith, Id.run_bind, PerfectMerkleTree.idRun_climbM, ha]
      have hwp : Id.run (letI := pubQ pr Id
          SLHDSA.wotsPkFromSigWith pr.toSLHDSA.core
            (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) s1.wots m0 (wotsLeafAdrs a idx)) =
          SLHDSA.wotsPkFromSig (prEager pr) s2.wots m0 pk (wotsLeafAdrs a idx) := by
        rw [SLHDSA.wotsPkFromSig_eq_tl, hw]
        simp only [SLHDSA.wotsPkFromSigWith, SLHDSA.wotsPkFromSigTopsWith, Id.run_bind, idRun_ofFnM]
        change pr.Th pk _ _ = pr.Th pk _ _
        congr 1; apply List.ext_getElem
        · simp
        · intro j hj₁ hj₂
          simp only [Vector.getElem_toList, Vector.getElem_ofFn, SLHDSA.wotsPkFromSigTops_eq_ofFn]
          exact hid_chain _ _ _ _
      rw [hwp]; rfl
    -- Compare hypertree layer `ℓ`
    -- In `slSignDet`, `signFromPositionWith` under `pubQ` equals `GeneralHypertree.signFromPosition (prEager pr)`!
    have hht_eq : ∀ (layers : ℕ) (p0 : LayerPosition vp.sl) (hrem : p0.layer.val + layers = vp.sl.params.d)
        (rf : Bool) (m0 : pr.Y) (j : ℕ) (hj : j < layers),
        let s1 := (Id.run (letI := pubQ pr Id
          SLHDSA.GeneralHypertree.signFromPositionWithSecret (vp := vp.sl) pr.toSLHDSA.core
            (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
            (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
            (fun a => pure (slSecOf pr u a)) rf p0 layers hrem m0))[j]
        let s2 := (SLHDSA.GeneralHypertree.signFromPosition vp.sl (prEager pr) u pk rf p0 layers hrem m0)[j]
        s1.wots = s2.wots ∧ s1.auth = s2.auth := by
      intro layers; induction layers using Nat.twoStepInduction with
      | zero => intro _ _ _ _ _ hj; omega
      | one =>
        intro p0 hrem rf m0 j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret,
          SLHDSA.GeneralHypertree.signFromPosition]
        cases rf <;> simp only [↓reduceIte, Bool.false_eq_true, Id.run_bind, Id.run_pure] <;>
          exact hxmss_sign m0 p0.toAdrs p0.leaf.val
      | more layers _ ih =>
        intro p0 hrem rf m0 j hj
        have hd_eq : vp.sl.params.d = vp.params.slParams.d := rfl
        simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret,
          SLHDSA.GeneralHypertree.signFromPosition, Id.run_bind, Id.run_pure]
        have hs0 := hxmss_sign m0 p0.toAdrs p0.leaf.val
        have hrec := hxmss_pk p0.leaf.val _ _ m0 p0.toAdrs hs0.1 hs0.2
        rcases j with _ | j
        · simp only [Vector.getElem_insertIdx_self]
          exact hs0
        · simp only [Vector.getElem_insertIdx, Nat.not_lt_zero, ↓reduceDIte,
            Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
          have hstep : ∀ (x₁ x₂ : pr.Y), x₁ = x₂ →
              (Id.run (letI := pubQ pr Id
                SLHDSA.GeneralHypertree.signFromPositionWithSecret (vp := vp.sl) pr.toSLHDSA.core
                  (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
                  (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
                  (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
                  (fun a => pure (slSecOf pr u a)) false (p0.next (by omega)) (layers + 1)
                  (by simp only [LayerPosition.next_layer_val]; omega) x₁))[j] =
              (Id.run (letI := pubQ pr Id
                SLHDSA.GeneralHypertree.signFromPositionWithSecret (vp := vp.sl) pr.toSLHDSA.core
                  (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
                  (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
                  (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
                  (fun a => pure (slSecOf pr u a)) false (p0.next (by omega)) (layers + 1)
                  (by simp only [LayerPosition.next_layer_val]; omega) x₂))[j] := by
            rintro x _ rfl; rfl
          simpa [hstep _ _ hrec] using ih (p0.next (by omega)) (by simp only [LayerPosition.next_layer_val]; omega)
            false _ j (by omega)
    -- Show `forsPk` computed in `slSignDet` equals `forsPkGen (prEager pr) u pk parts.forsAdrs`!
    have hfors_pk : Id.run (letI := pubQ pr Id
        SLHDSA.forsPkFromSigM pr.toSLHDSA.core
          (Id.run (letI := pubQ pr Id
            SLHDSA.forsSignWithSecretM pr.toSLHDSA.core (fun a => pure (slSecOf pr u a))
              parts.md.toList pk parts.forsAdrs))
          parts.md.toList pk parts.forsAdrs) =
        SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs := by
      have hf : Id.run (letI := pubQ pr Id
          SLHDSA.forsPkFromSigM pr.toSLHDSA.core
            (Id.run (letI := pubQ pr Id
              SLHDSA.forsSignWithSecretM pr.toSLHDSA.core (fun a => pure (slSecOf pr u a))
                parts.md.toList pk parts.forsAdrs))
            parts.md.toList pk parts.forsAdrs) =
          SLHDSA.forsPkFromSig (prEager pr)
            (SLHDSA.forsSign (prEager pr) parts.md.toList u pk parts.forsAdrs)
            parts.md.toList pk parts.forsAdrs := by
        rw [SLHDSA.forsPkFromSig_eq_tl]
        simp only [SLHDSA.forsPkFromSigM, SLHDSA.forsPkFromSigWith, SLHDSA.forsSignWithSecretM,
          SLHDSA.forsSignWithSecret, Id.run_bind, Id.run_pure, idRun_ofFnM,
          PerfectMerkleTree.idRun_climbM]
        change pr.Th pk _ _ = pr.Th pk _ _
        congr 1; apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [Vector.getElem_toList, Vector.getElem_ofFn, SLHDSA.forsSign_eq_ofFn, hid_auth]
          congr 1
      rw [hf, SLHDSA.forsPkFromSig_forsSign]
    -- Therefore layer `ℓ` of `slSignDet` matches `xmssSign (prEager pr) (honestLayerMsg ... ℓ) u pk (atLayer ℓ).toAdrs (atLayer ℓ).leaf.val`!
    have hpos_eq : (LayerPosition.initial vp.sl parts).advance ℓ (by simpa using hℓ) =
        LayerPosition.atLayer vp.sl parts ⟨ℓ, hℓ⟩ :=
      LayerPosition.advance_initial_eq_atLayer vp.sl parts ℓ (by simpa using hℓ)
    have hlayer_sig := SLHDSA.Security.signFromPosition_getElem vp.sl (prEager pr) u pk
      (vp.sl.params.d == 1) (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
      (SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs) ℓ hℓ
    -- Show `honestLayerMsg ... ℓ = hyb.wotsMsg (atLayer ℓ)`!
    have hmsg_eq : SLHDSA.Security.honestLayerMsg vp.sl (prEager pr) u pk
        (LayerPosition.initial vp.sl parts) (SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs)
        ℓ (by simpa using hℓ) = hyb.wotsMsg (LayerPosition.atLayer vp.sl parts ⟨ℓ, hℓ⟩) := by
      rw [hspec.2.2.2.2.1]
      rcases ℓ with _ | ℓ'
      · simp only [SLHDSA.Security.honestLayerMsg_zero, LayerPosition.atLayer_zero_eq_initial,
          LayerPosition.initial_layer_val, ↓reduceIte]
        rw [← honestVal_eq_forsPkGen pr pk u]
        rfl
      · simp only [SLHDSA.Security.honestLayerMsg_succ, LayerPosition.atLayer_layer_val,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        rw [← honestVal_eq_xmssRoot pr pk u]
        have hℓ' : ℓ' < vp.sl.params.d := by omega
        have hℓ'_adv : (LayerPosition.initial vp.sl parts).layer.val + ℓ' < vp.sl.params.d := by
          simp [LayerPosition.initial_layer_val, hℓ']
        have hnext_eq : LayerPosition.atLayer vp.sl parts ⟨ℓ' + 1, hℓ⟩ =
            ((LayerPosition.initial vp.sl parts).advance ℓ' hℓ'_adv).next
              (by rw [LayerPosition.advance_layer_val]; simp only [LayerPosition.initial_layer_val, Nat.zero_add]; exact hℓ) := by
          rw [LayerPosition.atLayer_succ_eq_next vp.sl parts ⟨ℓ', hℓ'⟩ hℓ]
          exact LayerPosition.next_congr
            (LayerPosition.advance_initial_eq_atLayer vp.sl parts ℓ' hℓ'_adv).symm _ _
        set pPrev := (LayerPosition.initial vp.sl parts).advance ℓ' hℓ'_adv
        have htree_eq : (LayerPosition.atLayer vp.sl parts ⟨ℓ' + 1, hℓ⟩).tree.val * 2 ^ vp.sl.params.hp +
            (LayerPosition.atLayer vp.sl parts ⟨ℓ' + 1, hℓ⟩).leaf.val = pPrev.tree.val := by
          rw [hnext_eq, LayerPosition.next_tree_val, LayerPosition.next_leaf_val, Nat.mul_comm]
          exact Nat.div_add_mod pPrev.tree.val (2 ^ vp.sl.params.hp)
        have hlay_eq : pPrev.layer.val = ℓ' := by simp [pPrev]
        have hadrs : SLHDSA.GeneralHypertree.layerAdrs ℓ'
            ((LayerPosition.atLayer vp.sl parts ⟨ℓ' + 1, hℓ⟩).tree.val * 2 ^ vp.sl.params.hp +
              (LayerPosition.atLayer vp.sl parts ⟨ℓ' + 1, hℓ⟩).leaf.val) = pPrev.toAdrs := by
          rw [htree_eq, ← hlay_eq]; rfl
        rw [hadrs]
    have hcomp :
        let s1 := (Id.run (letI := pubQ pr Id
          SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
            (fun a => pure (slSecOf pr u a)) msg pk (slRootDet pr pk u) R)).hypertree[ℓ]
        let s2 := SLHDSA.xmssSign (prEager pr) (hyb.wotsMsg (LayerPosition.atLayer vp.sl parts ⟨ℓ, hℓ⟩))
          u pk (LayerPosition.atLayer vp.sl parts ⟨ℓ, hℓ⟩).toAdrs
          (LayerPosition.atLayer vp.sl parts ⟨ℓ, hℓ⟩).leaf.val
        s1.wots = s2.wots ∧ s1.auth = s2.auth := by
      dsimp only
      simp only [SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM,
        SLHDSA.PublicHash.hmsg, HasQuery.query, Id.run_bind, Id.run_pure]
      have hpart_def : splitDigest vp.params.slParams
          (SLHDSA.PublicHash.impl pr.toSLHDSA (SLHDSA.PublicHashQuery.hmsg R pk (slRootDet pr pk u) msg)) =
          parts := rfl
      simp only [hpart_def]
      have hsign_congr : ∀ m₁ m₂ : pr.Y, m₁ = m₂ →
          (Id.run (letI := pubQ pr Id
            SLHDSA.GeneralHypertree.signWithSecretM (vp := vp.sl) pr.toSLHDSA.core
              (fun a => pure (slSecOf pr u a)) m₁ pk parts))[ℓ] =
          (Id.run (letI := pubQ pr Id
            SLHDSA.GeneralHypertree.signWithSecretM (vp := vp.sl) pr.toSLHDSA.core
              (fun a => pure (slSecOf pr u a)) m₂ pk parts))[ℓ] := by
        rintro m _ rfl; rfl
      rw [hsign_congr _ _ hfors_pk]
      have hpair := hht_eq vp.sl.params.d (LayerPosition.initial vp.sl parts) (by simp)
        (vp.sl.params.d == 1) (SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs) ℓ hℓ
      dsimp only at hpair
      rw [hlayer_sig, hpos_eq, hmsg_eq] at hpair
      exact hpair
    rw [hcomp.1, hcomp.2]
    simp only [Vector.getElem_ofFn, SLHDSA.xmssSign_eq_pair]
    set pos := LayerPosition.atLayer vp.sl parts ⟨ℓ, hℓ⟩
    refine ⟨?_, ?_⟩
    · rw [hspec.2.2.2.2.2.1 pos, wotsLeafAdrs_eq_wotsInstanceAdrs']
    · exact vector_ofFn_eq_intrinsicAuthPath pr
        (fun z t => (hyb.tbl (xmssCellAdrs pos.toAdrs z t)).getD default)
        (SLHDSA.xmssLeaf (prEager pr) u pk pos.toAdrs)
        (SLHDSA.xmssNodeHash (prEager pr) pk pos.toAdrs)
        (fun z t hzh ht => by
          rw [← SLHDSA.xmssNode_eq_merkleRoot, ← honestVal_eq_xmssCell pr pk u,
            ← LayerTreeCoord.ofPosition_toAdrs pos,
            htbl_xmss (LayerTreeCoord.ofPosition pos) z t hzh ht, Option.getD_some])
        pos.leaf.isLt vp.sl.params.hp le_rfl

/-- `hybSign` does NOT depend on `u` at `WOTS_PRF` addresses (`type = 5`). -/
theorem hybSign_indep_wotsSk (pk : pr.PkSeed) (hyb : HybTree pr)
    (u₁ u₂ : SlSecAdrs vp → pr.Y)
    (h : ∀ a : SlSecAdrs vp, a.1.type ≠ 5 → u₁ a = u₂ a) (msg : List Byte) (R : pr.Y) :
    hybSign pr pk hyb u₁ msg R = hybSign pr pk hyb u₂ msg R := by
  dsimp only [hybSign]
  congr 1
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  congr 1
  unfold slSecOf
  split_ifs with hmem
  · exact h ⟨_, hmem⟩ (by simp [forsSkAdrs, Adrs.setTreeIndex, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode])
  · rfl

/-- **Completeness at `γ = 0`**: whenever `verifyAndExtractTable` verifies and returns a WOTS
`F`-preimage witness `.hypertree ⟨ℓ, .wots (.fPreimage c step val)⟩`, the single-pass keyless
extractor `findHybWotsPre` succeeds on `hybTreeDet pr 0 pk u`. -/
theorem findHybWotsPre_zero_of_verifyAndExtractTable [DecidableEq pr.Y]
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (htbl : TblComplete pr pk u tbl) (msg : List Byte) (sig : Stateless.Sig pr)
    (target : Fin vp.sl.params.k) {ℓ : Fin vp.sl.params.d} {c : Fin vp.sl.params.len}
    {step : ℕ} {val : pr.Y}
    (hver : (verifyAndExtractTable pr pk (slRootDet pr pk u) tbl u msg sig target).1 = true)
    (hwit : (verifyAndExtractTable pr pk (slRootDet pr pk u) tbl u msg sig target).2 =
      some (.hypertree ⟨ℓ, .wots (.fPreimage c step val)⟩)) :
    (findHybWotsPre pr pk (hybTreeDet pr 0 pk u) msg sig).isSome = true := by
  have hspec := hybTreeDet_zero_spec pr pk u
  set hyb := hybTreeDet pr 0 pk u
  set pkSl := slRootDet pr pk u
  set parts := splitDigest vp.sl.params (pr.HmsgSl sig.randomness pk pkSl msg)
  have hfors_hon_hyb : (hyb.tbl (forsPkAdrs parts.forsAdrs)).getD default =
      SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs := by
    let bpos := BottomPosition.ofDigestParts vp.sl parts
    have hmem : forsPkAdrs bpos.forsAdrs ∈ forsAddresses vp := by
      simp only [forsAddresses, List.mem_append]; right
      exact SLHDSA.Security.mem_forsRootAddresses vp.sl bpos
    have hb : bpos.forsAdrs = parts.forsAdrs := BottomPosition.forsAdrs_ofDigestParts vp.sl parts
    rw [← hb, hspec.2.1 _ hmem, Option.getD_some, honestVal_eq_forsPkGen]
  have hfors_hon_tbl : (tbl (forsPkAdrs parts.forsAdrs)).getD default =
      SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs := by
    have hmem : forsPkAdrs parts.forsAdrs ∈ constructionAddresses vp.sl :=
      (mem_constructionAddresses_iff _).2 (Or.inr (Or.inr (Or.inl (mem_forsRootAddresses_of_parts parts))))
    rw [htbl _ hmem, Option.getD_some, honestVal_eq_forsPkGen]
  -- Layer-by-layer transfer from `htWitnessFromTrace` to `findHybWotsPreFromTrace`
  have hwalk : ∀ (layers : ℕ) (p0 : LayerPosition vp.sl)
      (hrem : p0.layer.val + layers = vp.sl.params.d)
      (fMsg hMsg : pr.Y)
      (hMsg_eq : hMsg = hyb.wotsMsg p0)
      (hMsg_hon : ∀ (j : ℕ) (hj : p0.layer.val + j < vp.sl.params.d),
        SLHDSA.Security.honestLayerMsg vp.sl (prEager pr) u pk p0 hMsg j hj =
          hyb.wotsMsg (p0.advance j hj))
      (sigs : Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers)
      (ℓ' : Fin layers),
      htWitnessFromTrace pr tbl u p0 layers hrem hMsg
        (Id.run (simulateQ (thRealImpl pr pk) (htRecoverTraceM pr p0 layers hrem fMsg sigs))).2 =
        some ⟨ℓ', .wots (.fPreimage c step val)⟩ →
      (findHybWotsPreFromTrace pr hyb p0 layers hrem
        (Id.run (simulateQ (thRealImpl pr pk) (htRecoverTraceM pr p0 layers hrem fMsg sigs))).2).isSome =
        true := by
    intro layers; induction layers using Nat.twoStepInduction with
    | zero => intro _ _ _ _ _ _ _ ℓ'; exact absurd ℓ'.isLt (Nat.not_lt_zero _)
    | one =>
      intro p0 hrem fMsg hMsg hMsg_eq _ sigs ℓ' hw
      have hroot_hyb : (hyb.tbl (xmssNodeAdrs p0.toAdrs vp.sl.params.hp 0)).getD default =
          SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs := by
        have h := hspec.2.2.2.1 (LayerTreeCoord.ofPosition p0) vp.sl.params.hp 0 vp.valid.hp_pos le_rfl (by simp)
        rw [LayerTreeCoord.ofPosition_toAdrs] at h
        rw [h, Option.getD_some, honestVal_eq_xmssRoot]
      have hroot_tbl : (tbl (xmssNodeAdrs p0.toAdrs vp.sl.params.hp 0)).getD default =
          SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs := by
        have hmem : xmssNodeAdrs p0.toAdrs vp.sl.params.hp 0 ∈ constructionAddresses vp.sl := by
          rw [mem_constructionAddresses_iff]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
          rw [← LayerTreeCoord.ofPosition_toAdrs p0]
          exact mem_xmssNodeAddresses vp.sl (LayerTreeCoord.ofPosition p0) vp.valid.hp_pos le_rfl (by simp)
        rw [htbl _ hmem, Option.getD_some, honestVal_eq_xmssRoot]
      have hwots_hyb : (hyb.tbl (wotsPkAdrs (wotsInstanceAdrs p0))).getD default =
          SLHDSA.wotsPkGen (prEager pr) u pk (wotsLeafAdrs p0.toAdrs p0.leaf.val) := by
        rw [hspec.2.2.1 p0, Option.getD_some, wotsLeafAdrs_eq_wotsInstanceAdrs', honestVal_eq_wotsPkGen]
      have hwots_tbl : (tbl (wotsPkAdrs (wotsLeafAdrs p0.toAdrs p0.leaf.val))).getD default =
          SLHDSA.wotsPkGen (prEager pr) u pk (wotsLeafAdrs p0.toAdrs p0.leaf.val) := by
        have hmem : wotsPkAdrs (wotsLeafAdrs p0.toAdrs p0.leaf.val) ∈ constructionAddresses vp.sl := by
          rw [mem_constructionAddresses_iff, wotsLeafAdrs_eq_wotsInstanceAdrs']
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_wotsPkAddresses vp.sl p0)))))
        rw [htbl _ hmem, Option.getD_some, honestVal_eq_wotsPkGen]
      have htr := simulateQ_xmssRecoverTraceM_spec pr pk p0 sigs.head fMsg
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        htWitnessFromTrace, findHybWotsPreFromTrace] at hw ⊢
      have hhd : (#v[Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg))]).head =
          Id.run (simulateQ (thRealImpl pr pk) (xmssRecoverTraceM pr p0 sigs.head fMsg)) := rfl
      rw [hhd] at hw ⊢
      dsimp only at hw ⊢
      rw [hroot_tbl] at hw
      rw [hroot_hyb]
      split at hw
      · rename_i hrm
        rw [Option.map_eq_some_iff] at hw
        obtain ⟨xw, hxw, hxeq⟩ := hw
        have hxweq : xw = .wots (.fPreimage c step val) := by
          have := congrArg SLHDSA.Security.HypertreeWitness.witness hxeq; exact this
        subst hxweq
        unfold xmssWitnessFromTrace at hxw
        dsimp only at hxw
        rw [hwots_tbl] at hxw
        rw [ite_eq_left hrm, hwots_hyb]
        split at hxw
        · rename_i hwpk
          rw [ite_eq_left hwpk.symm]
          rw [Option.map_eq_some_iff] at hxw
          obtain ⟨ww, hww, hwweq⟩ := hxw
          have : ww = .fPreimage c step val := by cases hwweq; rfl
          subst this
          rw [htr.1, htr.2.2.2.1, htr.2.2.2.2.1] at hww
          have hpre := wotsPreFromTrace_isSome_of_wotsWitnessFromTrace pr pk u tbl htbl p0
            sigs.head.wots fMsg hMsg hww
          rw [htr.1, htr.2.2.2.2.1, ← hMsg_eq, hspec.2.2.2.2.2.1 p0, ← hMsg_eq,
            ← wotsLeafAdrs_eq_wotsInstanceAdrs']
          cases hopt : wotsPreFromTrace pr fMsg hMsg
              (SLHDSA.wotsSign (prEager pr) hMsg u pk (wotsLeafAdrs p0.toAdrs p0.leaf.val))
              (Id.run (simulateQ (thRealImpl pr pk)
                (wotsRecoverTraceM pr sigs.head.wots fMsg (wotsLeafAdrs p0.toAdrs p0.leaf.val)))).2.2 with
          | none => dsimp only at hpre; rw [hopt] at hpre; simp at hpre
          | some t => rcases t with ⟨_, _, _⟩; rfl
        · rw [Option.map_eq_some_iff] at hxw
          obtain ⟨_, _, hcontra⟩ := hxw; cases hcontra
      · cases hw
    | more layers _ ih =>
      intro p0 hrem fMsg hMsg hMsg_eq hMsg_hon sigs ℓ' hw
      have hroot_hyb : (hyb.tbl (xmssNodeAdrs p0.toAdrs vp.sl.params.hp 0)).getD default =
          SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs := by
        have h := hspec.2.2.2.1 (LayerTreeCoord.ofPosition p0) vp.sl.params.hp 0 vp.valid.hp_pos le_rfl (by simp)
        rw [LayerTreeCoord.ofPosition_toAdrs] at h
        rw [h, Option.getD_some, honestVal_eq_xmssRoot]
      have hroot_tbl : (tbl (xmssNodeAdrs p0.toAdrs vp.sl.params.hp 0)).getD default =
          SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs := by
        have hmem : xmssNodeAdrs p0.toAdrs vp.sl.params.hp 0 ∈ constructionAddresses vp.sl := by
          rw [mem_constructionAddresses_iff]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
          rw [← LayerTreeCoord.ofPosition_toAdrs p0]
          exact mem_xmssNodeAddresses vp.sl (LayerTreeCoord.ofPosition p0) vp.valid.hp_pos le_rfl (by simp)
        rw [htbl _ hmem, Option.getD_some, honestVal_eq_xmssRoot]
      have hwots_hyb : (hyb.tbl (wotsPkAdrs (wotsInstanceAdrs p0))).getD default =
          SLHDSA.wotsPkGen (prEager pr) u pk (wotsLeafAdrs p0.toAdrs p0.leaf.val) := by
        rw [hspec.2.2.1 p0, Option.getD_some, wotsLeafAdrs_eq_wotsInstanceAdrs', honestVal_eq_wotsPkGen]
      have hwots_tbl : (tbl (wotsPkAdrs (wotsLeafAdrs p0.toAdrs p0.leaf.val))).getD default =
          SLHDSA.wotsPkGen (prEager pr) u pk (wotsLeafAdrs p0.toAdrs p0.leaf.val) := by
        have hmem : wotsPkAdrs (wotsLeafAdrs p0.toAdrs p0.leaf.val) ∈ constructionAddresses vp.sl := by
          rw [mem_constructionAddresses_iff, wotsLeafAdrs_eq_wotsInstanceAdrs']
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_wotsPkAddresses vp.sl p0)))))
        rw [htbl _ hmem, Option.getD_some, honestVal_eq_wotsPkGen]
      have htr := simulateQ_xmssRecoverTraceM_spec pr pk p0 sigs.head fMsg
      have hhd : ∀ {α : Type} {n : ℕ} (a : α) (v : Vector α n), (v.insertIdx 0 a).head = a :=
        fun _ _ => by simp [Vector.head]
      have htl : ∀ {α : Type} {n : ℕ} (a : α) (v : Vector α n), (v.insertIdx 0 a).tail = v :=
        fun _ _ => by apply Vector.ext; intro i hi; simp [Vector.tail_eq_cast_extract]
      simp only [htRecoverTraceM, simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure,
        htWitnessFromTrace, findHybWotsPreFromTrace] at hw ⊢
      rw [hhd, htl] at hw ⊢
      rw [hroot_tbl] at hw
      rw [hroot_hyb]
      by_cases hrm : (Id.run (simulateQ (thRealImpl pr pk)
          (xmssRecoverTraceM pr p0 sigs.head fMsg))).xmssRoot =
          SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs
      · rw [ite_eq_left hrm, Option.map_eq_some_iff] at hw
        obtain ⟨xw, hxw, hxeq⟩ := hw
        have hxweq : xw = .wots (.fPreimage c step val) := by
          have := congrArg SLHDSA.Security.HypertreeWitness.witness hxeq; exact this
        subst hxweq
        unfold xmssWitnessFromTrace at hxw
        dsimp only at hxw
        rw [hwots_tbl] at hxw
        rw [ite_eq_left hrm, hwots_hyb]
        split at hxw
        · rename_i hwpk
          rw [ite_eq_left hwpk.symm]
          rw [Option.map_eq_some_iff] at hxw
          obtain ⟨ww, hww, hwweq⟩ := hxw
          have : ww = .fPreimage c step val := by cases hwweq; rfl
          subst this
          rw [htr.1, htr.2.2.2.1, htr.2.2.2.2.1] at hww
          have hpre := wotsPreFromTrace_isSome_of_wotsWitnessFromTrace pr pk u tbl htbl p0
            sigs.head.wots fMsg hMsg hww
          rw [htr.1, htr.2.2.2.2.1, ← hMsg_eq, hspec.2.2.2.2.2.1 p0, ← hMsg_eq,
            ← wotsLeafAdrs_eq_wotsInstanceAdrs']
          cases hopt : wotsPreFromTrace pr fMsg hMsg
              (SLHDSA.wotsSign (prEager pr) hMsg u pk (wotsLeafAdrs p0.toAdrs p0.leaf.val))
              (Id.run (simulateQ (thRealImpl pr pk)
                (wotsRecoverTraceM pr sigs.head.wots fMsg (wotsLeafAdrs p0.toAdrs p0.leaf.val)))).2.2 with
          | none => dsimp only at hpre; rw [hopt] at hpre; simp at hpre
          | some t => rcases t with ⟨_, _, _⟩; rfl
        · rw [Option.map_eq_some_iff] at hxw
          obtain ⟨_, _, hcontra⟩ := hxw; cases hcontra
      · rw [ite_eq_right hrm, Option.map_eq_some_iff] at hw
        obtain ⟨hw', hhw', hweq⟩ := hw
        rcases hw' with ⟨l', w'⟩
        have hw'eq : w' = .wots (.fPreimage c step val) := by
          have := congrArg SLHDSA.Security.HypertreeWitness.witness hweq; exact this
        subst hw'eq
        rw [ite_eq_right hrm]
        have hd_eq : vp.sl.params.d = vp.params.slParams.d := rfl
        have hnext_msg : SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs =
            hyb.wotsMsg (p0.next (by omega)) := by
          have := hMsg_hon 1 (by omega)
          simpa [SLHDSA.Security.honestLayerMsg_succ, LayerPosition.advance_next] using this
        exact ih (p0.next (by omega)) (by simp only [LayerPosition.next_layer_val]; omega)
          _ (SLHDSA.xmssRoot (prEager pr) u pk p0.toAdrs) hnext_msg
          (fun j hj => by
            have hj' : p0.layer.val + (j + 1) < vp.sl.params.d := by
              simp only [LayerPosition.next_layer_val] at hj; omega
            have := hMsg_hon (j + 1) hj'
            rw [SLHDSA.Security.honestLayerMsg_next, LayerPosition.advance_next] at this
            exact this)
          sigs.tail l' hhw'
  -- Connect top-level `verifyAndExtractTable` to `findHybWotsPre`!
  unfold verifyAndExtractTable verifyAndExtractTableM at hver hwit
  simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure] at hver hwit
  unfold findHybWotsPre findHybWotsPreM
  simp only [simulateQ_bind, Id.run_bind, simulateQ_pure, Id.run_pure, hspec.1]
  have hrootEq : (Id.run (simulateQ (thRealImpl pr pk)
      (htRecoverTraceM pr (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
        (Id.run (simulateQ (thRealImpl pr pk)
          (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))).1 sig.hypertree))).1 = pkSl :=
    of_decide_eq_true hver
  rw [hfors_hon_tbl] at hwit
  by_cases hfp : (Id.run (simulateQ (thRealImpl pr pk)
      (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))).1 =
      SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs
  · rw [ite_eq_left hfp] at hwit; cases hwit
  · rw [ite_eq_right hfp, Option.map_eq_some_iff] at hwit
    obtain ⟨hw', hhw', hweq⟩ := hwit
    cases hweq
    have hcond : (Id.run (simulateQ (thRealImpl pr pk)
        (htRecoverTraceM pr (LayerPosition.initial vp.sl parts) vp.sl.params.d (by simp)
          (Id.run (simulateQ (thRealImpl pr pk)
            (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))).1 sig.hypertree))).1 = pkSl ∧
        (Id.run (simulateQ (thRealImpl pr pk)
          (forsRecoverTraceM pr sig.fors parts.md.toList parts.forsAdrs))).1 ≠
          (hyb.tbl (forsPkAdrs parts.forsAdrs)).getD default := by
      rw [hfors_hon_hyb]; exact ⟨hrootEq, hfp⟩
    change (if _ then _ else none).isSome = true
    rw [ite_eq_left hcond]
    have h0_eq : SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs =
        hyb.wotsMsg (LayerPosition.initial vp.sl parts) := by
      rw [hspec.2.2.2.2.1]
      simp only [LayerPosition.initial_layer_val, ↓reduceIte]
      rw [← honestVal_eq_forsPkGen pr pk u]; rfl
    have hhon_all : ∀ (j : ℕ) (hj : (LayerPosition.initial vp.sl parts).layer.val + j < vp.sl.params.d),
        SLHDSA.Security.honestLayerMsg vp.sl (prEager pr) u pk (LayerPosition.initial vp.sl parts)
          (SLHDSA.forsPkGen (prEager pr) u pk parts.forsAdrs) j hj =
        hyb.wotsMsg ((LayerPosition.initial vp.sl parts).advance j hj) := by
      intro j hj
      rw [LayerPosition.advance_initial_eq_atLayer vp.sl parts j hj, hspec.2.2.2.2.1]
      rcases j with _ | j'
      · simp only [SLHDSA.Security.honestLayerMsg_zero, LayerPosition.atLayer_zero_eq_initial,
          LayerPosition.initial_layer_val, ↓reduceIte]
        rw [← honestVal_eq_forsPkGen pr pk u]; rfl
      · simp only [SLHDSA.Security.honestLayerMsg_succ, LayerPosition.atLayer_layer_val,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        rw [← honestVal_eq_xmssRoot pr pk u]
        have hj_lt : j' + 1 < vp.sl.params.d := by simpa [LayerPosition.initial_layer_val] using hj
        have hj'_lt : j' < vp.sl.params.d := by omega
        have hj'_adv : (LayerPosition.initial vp.sl parts).layer.val + j' < vp.sl.params.d := by
          simp [LayerPosition.initial_layer_val, hj'_lt]
        have hnext_eq : LayerPosition.atLayer vp.sl parts ⟨j' + 1, hj_lt⟩ =
            ((LayerPosition.initial vp.sl parts).advance j' hj'_adv).next
              (by rw [LayerPosition.advance_layer_val]; simp only [LayerPosition.initial_layer_val, Nat.zero_add]; exact hj_lt) := by
          rw [LayerPosition.atLayer_succ_eq_next vp.sl parts ⟨j', hj'_lt⟩ hj_lt]
          exact LayerPosition.next_congr
            (LayerPosition.advance_initial_eq_atLayer vp.sl parts j' hj'_adv).symm _ _
        set pPrev := (LayerPosition.initial vp.sl parts).advance j' hj'_adv
        have htree_eq : (LayerPosition.atLayer vp.sl parts ⟨j' + 1, hj_lt⟩).tree.val *
              2 ^ vp.sl.params.hp +
            (LayerPosition.atLayer vp.sl parts ⟨j' + 1, hj_lt⟩).leaf.val = pPrev.tree.val := by
          rw [hnext_eq, LayerPosition.next_tree_val, LayerPosition.next_leaf_val, Nat.mul_comm]
          exact Nat.div_add_mod pPrev.tree.val (2 ^ vp.sl.params.hp)
        have hadrs : SLHDSA.GeneralHypertree.layerAdrs j'
            ((LayerPosition.atLayer vp.sl parts ⟨j' + 1, hj_lt⟩).tree.val *
              2 ^ vp.sl.params.hp +
              (LayerPosition.atLayer vp.sl parts ⟨j' + 1, hj_lt⟩).leaf.val) = pPrev.toAdrs := by
          rw [htree_eq, show j' = pPrev.layer.val by simp [pPrev]]; rfl
        rw [hadrs]
    exact hwalk vp.sl.params.d (LayerPosition.initial vp.sl parts) (by simp) _ _ h0_eq hhon_all
      sig.hypertree ℓ hhw'

end ZeroAndSound

/-! ## 7. Equivalence of deterministic and probabilistic hybrids (`hybTreeDet` =ᵈ `hybTreeProb`) -/

section DetProbEquiv

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Typed `SlSecAdrs` for a WOTS chain `(pos, c)`. -/
def wotsSecAdrs {vp : ValidatedParams} (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) : SlSecAdrs vp :=
  ⟨wotsSkAdrs (wotsInstanceAdrs pos) c.val, List.mem_toFinset.2 (mem_slSecretList_wotsSk pos c)⟩

theorem wotsSecAdrs_type {vp : ValidatedParams} (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) :
    (wotsSecAdrs pos c).1.type = 5 := by
  simp [wotsSecAdrs, wotsSkAdrs, Adrs.setChainAddress, Adrs.setKeyPairAddress,
    Adrs.setTypeAndClear, AddrType.toCode]

theorem wotsSecAdrs_injective {vp : ValidatedParams} :
    Function.Injective (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len =>
      wotsSecAdrs pc.1 pc.2) := by
  rintro ⟨⟨l₁, t₁, lf₁⟩, c₁⟩ ⟨⟨l₂, t₂, lf₂⟩, c₂⟩ h
  have hval := congrArg Subtype.val h
  have hl : l₁ = l₂ := Fin.ext (by
    have := congrArg Adrs.layer hval
    simpa [wotsSecAdrs, wotsSkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
      Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress,
      Adrs.setLayerAddress] using this)
  subst hl
  have ht : t₁ = t₂ := Fin.ext (by
    have := congrArg Adrs.tree hval
    simpa [wotsSecAdrs, wotsSkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
      Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress,
      Adrs.setLayerAddress] using this)
  subst ht
  have hlf : lf₁ = lf₂ := Fin.ext (by
    have := congrArg Adrs.word1 hval
    simpa [wotsSecAdrs, wotsSkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
      Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress,
      Adrs.setLayerAddress, Adrs.getKeyPairAddress] using this)
  subst hlf
  have hc : c₁ = c₂ := Fin.ext (by
    have := congrArg Adrs.word2 hval
    simpa [wotsSecAdrs, wotsSkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
      Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress,
      Adrs.setLayerAddress] using this)
  subst hc
  rfl

omit [Inhabited pr.Y] in
/-- Replacing `n` distinct entries of a uniform table `u : SlSecAdrs vp → pr.Y` by fresh on-the-fly
samples in `Vector.ofFnM` preserves `=ᵈ` when the continuation does not depend on those entries. -/
private theorem vector_ofFnM_det_eq_prob [SampleableType pr.Y] {n : ℕ} {α γ : Type}
    (addr : Fin n → SlSecAdrs vp) (hinj : Function.Injective addr)
    (step : Fin n → pr.Y → α)
    (S : Finset (SlSecAdrs vp)) (hdisj : ∀ i, addr i ∉ S)
    (K : (SlSecAdrs vp → pr.Y) → Vector α n → ProbComp γ)
    (hK : ∀ u₁ u₂, (∀ a ∈ S, u₁ a = u₂ a) → ∀ v, K u₁ v = K u₂ v) :
    ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun u => K u (Vector.ofFn fun i => step i (u (addr i)))) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun u =>
        (Vector.ofFnM fun i => do let x ← $ᵗ pr.Y; pure (step i x)) >>= K u) := by
  induction n generalizing S with
  | zero =>
    simp only [Vector.ofFnM_zero, pure_bind]
    refine EvalDistEq.bind_right _ fun u => ?_
    rw [show (Vector.ofFn fun i : Fin 0 => step i (u (addr i))) = #v[] from Vector.ext fun i hi => by omega]
  | succ n ih =>
    let aLast := addr (Fin.last n)
    have hne : ∀ j : Fin n, addr j.castSucc ≠ aLast := fun j heq =>
      Fin.castSucc_ne_last j (hinj heq)
    have hsplit : ∀ (u : SlSecAdrs vp → pr.Y),
        (Vector.ofFn fun i : Fin (n + 1) => step i (u (addr i))) =
        (Vector.ofFn fun j : Fin n => step j.castSucc (u (addr j.castSucc))).push
          (step (Fin.last n) (u aLast)) := by
      intro u; apply Vector.ext; intro i hi
      by_cases hlt : i < n
      · simp [Vector.getElem_push_lt hlt]
      · have : i = n := by omega
        subst this; simp [Fin.last, aLast]
    simp only [hsplit]
    refine (Repro.resample aLast (fun u => K u
      ((Vector.ofFn fun j : Fin n => step j.castSucc (u (addr j.castSucc))).push
        (step (Fin.last n) (u aLast))))).symm.trans ?_
    have hupd : ∀ (x : pr.Y) (u : SlSecAdrs vp → pr.Y),
        K (Function.update u aLast x)
          ((Vector.ofFn fun j : Fin n =>
              step j.castSucc (Function.update u aLast x (addr j.castSucc))).push
            (step (Fin.last n) (Function.update u aLast x aLast))) =
        K u ((Vector.ofFn fun j : Fin n => step j.castSucc (u (addr j.castSucc))).push
          (step (Fin.last n) x)) := by
      intro x u
      rw [hK (Function.update u aLast x) u (fun a ha => Function.update_of_ne (fun h => hdisj (Fin.last n) (by change aLast ∈ S; rw [← h]; exact ha)) _ _)]
      congr 1; congr 1
      · apply Vector.ext; intro j hj; simp only [Vector.getElem_ofFn]
        rw [Function.update_of_ne (hne ⟨j, hj⟩)]
      · rw [Function.update_self]
    simp only [hupd]
    refine (EvalDistEq.bind_right _ fun x =>
      ih (fun j => addr j.castSucc) (fun _ _ h => Fin.castSucc_inj.1 (hinj h))
        (fun j => step j.castSucc) S (fun j => hdisj j.castSucc)
        (fun u v => K u (v.push (step (Fin.last n) x)))
        (fun u₁ u₂ hu v => hK u₁ u₂ hu _)).trans ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun u => ?_
    simp only [Vector.ofFnM_succ, bind_assoc, pure_bind]
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    exact EvalDistEq.bind_right _ fun v => EvalDistEq.refl _

/-- **Equivalence of deterministic `hybTreeDet` and probabilistic `hybTreeProb`**: for any Stage-2
continuation `f` that does not read `u` at `WOTS_PRF` (`type = 5`), sampling `u` uniformly and
building `hybTreeDet pr γ pk u` has the exact same distribution (`=ᵈ`) as sampling `u` uniformly
(for FORS) and building `hybTreeProb pr γ pk u` (with fresh WOTS seeds). -/
theorem hybTreeDet_evalDistEq_hybTreeProb [SampleableType pr.Y] {β : Type}
    (γ : ℕ) (pk : pr.PkSeed)
    (f : (SlSecAdrs vp → pr.Y) → HybTree pr → ProbComp β)
    (hf : ∀ u₁ u₂, (∀ a : SlSecAdrs vp, a.1.type ≠ 5 → u₁ a = u₂ a) → ∀ hyb, f u₁ hyb = f u₂ hyb) :
    (do let u ← $ᵗ (SlSecAdrs vp → pr.Y); f u (hybTreeDet pr γ pk u)) =ᵈ
      (do let u ← $ᵗ (SlSecAdrs vp → pr.Y); let hyb ← hybTreeProb pr γ pk u; f u hyb) := by
  -- Split `u` into `uFors` (type ≠ 5) and `uWots` (type = 5) on LHS
  refine (uniform_split_pred (fun a : SlSecAdrs vp => a.1.type = 5)
    (fun u => f u (hybTreeDet pr γ pk u))).trans ?_
  refine EvalDistEq.bind_right _ fun uFors => ?_
  -- Fix `uFors`: FORS table `tbl₀` is independent of `uWots`!
  let mix (uWots : SlSecAdrs vp → pr.Y) : SlSecAdrs vp → pr.Y :=
    fun a => if a.1.type = 5 then uWots a else uFors a
  have hmix_non5 : ∀ uWots (a : SlSecAdrs vp), a.1.type ≠ 5 → mix uWots a = uFors a := by
    intro uWots a ha; simp [mix, ha]
  have hmix_5 : ∀ uWots (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len),
      slSecOf pr (mix uWots) (wotsSkAdrs (wotsInstanceAdrs pos) c.val) =
        uWots (wotsSecAdrs pos c) := by
    intro uWots pos c
    simp only [slSecOf, List.mem_toFinset.2 (mem_slSecretList_wotsSk pos c), ↓reduceDIte]
    change (if (wotsSecAdrs pos c).1.type = 5 then uWots (wotsSecAdrs pos c) else uFors _) = _
    rw [wotsSecAdrs_type]; simp
  have hfors_eq : ∀ uWots,
      Id.run ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (sfDetCall pr pk) (mix uWots) tbl a
        return Function.update tbl a (some v)) (fun _ => none)) =
      Id.run ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (sfDetCall pr pk) uFors tbl a
        return Function.update tbl a (some v)) (fun _ => none)) := by
    intro uWots
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
        (∀ a ∈ l, a.type = 3 ∨ a.type = 4) →
        Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (sfDetCall pr pk) (mix uWots) tbl a
          return Function.update tbl a (some v)) tbl) =
        Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (sfDetCall pr pk) uFors tbl a
          return Function.update tbl a (some v)) tbl) := by
      intro l; induction l with
      | nil => intro _ _; rfl
      | cons a as ih =>
        intro tbl hty
        have hev : evalNodeM pr (sfDetCall pr pk) (mix uWots) tbl a =
            evalNodeM pr (sfDetCall pr pk) uFors tbl a := by
          rcases hty a (by simp) with h3 | h4
          · by_cases hw2 : a.word2 = 0
            · simp only [evalNodeM, h3, hw2, ↓reduceIte]
              congr 1
            · simp only [evalNodeM, h3, hw2, ↓reduceIte]
          · simp only [evalNodeM, h4]
        simp only [List.foldlM_cons, Id.run_bind, hev]
        exact ih _ (fun b hb => hty b (by simp [hb]))
    exact haux _ _ (fun a ha => type_of_mem_forsAddresses ha)
  -- For ProbComp FORS pass, it is deterministic and equals `tbl₀`!
  have hfors_prob :
      ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) uFors tbl a
        return Function.update tbl a (some v)) (fun _ => none)) =
      pure (Id.run ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (sfDetCall pr pk) uFors tbl a
        return Function.update tbl a (some v)) (fun _ => none))) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
        (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) uFors tbl a
          return Function.update tbl a (some v)) tbl) =
        pure (Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (sfDetCall pr pk) uFors tbl a
          return Function.update tbl a (some v)) tbl)) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons a as ih =>
        intro tbl
        have hev : evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) uFors tbl a =
            pure (Id.run (evalNodeM pr (sfDetCall pr pk) uFors tbl a)) := by
          rw [evalNodeM_eq_of_input, evalNodeM_eq_of_input]
          cases evalNodeInput pr uFors tbl a <;> rfl
        simp only [List.foldlM_cons, hev, pure_bind, Id.run_bind, Id.run_pure]
        exact ih _
    exact haux _ _
  -- Helper: deterministic `slChainM` in `ProbComp` equals `pure (slChainDet ...)`
  have hchain_prob : ∀ chAdrs x s steps,
      slChainM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) chAdrs x s steps =
        pure (slChainDet pr pk chAdrs x s steps) := by
    intro chAdrs x s steps; induction steps with
    | zero => rfl
    | succ steps ih =>
      simp only [slChainM, ih, pure_bind, slChainDet, Id.run_bind, sfDetCall, Id.run_pure]
  -- Helper: single leaf step `buildLeafM`
  let detCs (uWots : SlSecAdrs vp → pr.Y) :
      LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → Id pr.Y :=
    fun pos c b => pure (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b
      (uWots (wotsSecAdrs pos c)))
  let probCs : LayerPosition vp.sl → Fin vp.sl.params.len → ℕ → ProbComp pr.Y :=
    fun pos c b => do
      let x ← $ᵗ pr.Y
      return hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x
  have hleaf_eq : ∀ (pos : LayerPosition vp.sl) (acc : HybAcc pr)
      (S : Finset (SlSecAdrs vp)) (hdisj : ∀ c : Fin vp.sl.params.len, wotsSecAdrs pos c ∉ S)
      (K : (SlSecAdrs vp → pr.Y) → HybAcc pr → ProbComp β)
      (hK : ∀ u₁ u₂, (∀ a ∈ S, u₁ a = u₂ a) → ∀ a', K u₁ a' = K u₂ a'),
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW =>
        K uW (Id.run (buildLeafM pr (sfDetCall pr pk) (detCs uW) acc pos))) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW =>
        buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs acc pos >>= K uW) := by
    intro pos acc S hdisj K hK
    set msg := wotsMsgFromTbl pr acc.tbl pos
    let stepPair (c : Fin vp.sl.params.len) (x : pr.Y) : pr.Y × pr.Y :=
      let b := chainStepsCore pr.toSLHDSA.core msg c.val
      let sigBlk := hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x
      (sigBlk, slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b (vp.sl.params.w - 1 - b))
    let finish (pairs : Vector (pr.Y × pr.Y) vp.sl.params.len) : HybAcc pr :=
      let sigVec : Vector pr.Y vp.sl.params.len := Vector.ofFn fun c => pairs[c.val].1
      let topVec : Vector pr.Y vp.params.lsl :=
        (Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
          (Params.lsl_eq_len vp.valid).symm
      let wpk := pr.memberEval .thLsl pk (wotsPkAdrs (wotsInstanceAdrs pos)) topVec
      ⟨Function.update acc.tbl (wotsPkAdrs (wotsInstanceAdrs pos)) (some wpk),
       Function.update acc.wotsMsg pos msg,
       Function.update acc.wotsSig pos sigVec⟩
    have hdet : ∀ uW, Id.run (buildLeafM pr (sfDetCall pr pk) (detCs uW) acc pos) =
        finish (Vector.ofFn fun c => stepPair c (uW (wotsSecAdrs pos c))) := by
      intro uW
      unfold buildLeafM
      simp only [Id.run_bind, idRun_ofFnM, sfDetCall, Id.run_pure, detCs, finish, stepPair, msg]
      rfl
    have hprob : buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs acc pos =
        (Vector.ofFnM fun c : Fin vp.sl.params.len => do let x ← $ᵗ pr.Y; pure (stepPair c x)) >>=
          fun pairs => pure (finish pairs) := by
      unfold buildLeafM
      simp only [probCs, bind_assoc, pure_bind, hchain_prob, finish, stepPair, msg]
    simp only [hdet, hprob, bind_assoc, pure_bind]
    exact vector_ofFnM_det_eq_prob pr (fun c => wotsSecAdrs pos c)
      (fun c₁ c₂ h => congrArg Prod.snd (wotsSecAdrs_injective (a₁ := (pos, c₁)) (a₂ := (pos, c₂)) h))
      stepPair S hdisj (fun uW pairs => K uW (finish pairs))
      (fun u₁ u₂ hu pairs => hK u₁ u₂ hu (finish pairs))
  -- Helper: XMSS internal-node fold in `ProbComp` is deterministic
  have hxmss_prob : ∀ (coord : LayerTreeCoord vp.sl) (tbl : Adrs → Option pr.Y),
      ((perfectInternalCoords vp.sl.params.hp).foldlM (fun t zi => do
        let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
        let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
        let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
        let v ← (pure (pr.memberEval .H pk a (lv, rv)) : ProbComp pr.Y)
        return Function.update t a (some v)) tbl) =
      pure (Id.run ((perfectInternalCoords vp.sl.params.hp).foldlM (fun t zi => do
        let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
        let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
        let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
        let v ← sfDetCall pr pk .H a (lv, rv)
        return Function.update t a (some v)) tbl)) := by
    intro coord
    have haux : ∀ (l : List (ℕ × ℕ)) (tbl : Adrs → Option pr.Y),
        (l.foldlM (fun t zi => do
          let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
          let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
          let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
          let v ← (pure (pr.memberEval .H pk a (lv, rv)) : ProbComp pr.Y)
          return Function.update t a (some v)) tbl) =
        pure (Id.run (l.foldlM (fun t zi => do
          let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
          let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
          let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
          let v ← sfDetCall pr pk .H a (lv, rv)
          return Function.update t a (some v)) tbl)) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons zi zis ih =>
        intro tbl; simp only [List.foldlM_cons, pure_bind, sfDetCall]
        exact ih _
    exact haux _
  -- Helper: `buildTreeM` over a list of leaves `l`
  have hleaves_eq : ∀ (coord : LayerTreeCoord vp.sl) (l : List (Fin (2 ^ vp.sl.params.hp))),
      l.Nodup →
      ∀ (acc : HybAcc pr) (S : Finset (SlSecAdrs vp)),
      (∀ lf ∈ l, ∀ c : Fin vp.sl.params.len, wotsSecAdrs ⟨coord.layer, coord.tree, lf⟩ c ∉ S) →
      ∀ (K : (SlSecAdrs vp → pr.Y) → HybAcc pr → ProbComp β),
      (∀ u₁ u₂, (∀ a ∈ S, u₁ a = u₂ a) → ∀ a', K u₁ a' = K u₂ a') →
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW =>
        K uW (Id.run (l.foldlM (fun a lf => buildLeafM pr (sfDetCall pr pk) (detCs uW) a ⟨coord.layer, coord.tree, lf⟩) acc))) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW =>
        (l.foldlM (fun a lf => buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs a ⟨coord.layer, coord.tree, lf⟩) acc) >>= K uW) := by
    intro coord l; induction l with
    | nil =>
      intro _ acc _ _ K _
      simp only [List.foldlM_nil, Id.run_pure, pure_bind]; exact EvalDistEq.refl _
    | cons lf lfs ih =>
      intro hnd acc S hdisj K hK
      rw [List.nodup_cons] at hnd
      let S' : Finset (SlSecAdrs vp) :=
        S ∪ (lfs.flatMap fun lf' => (List.finRange vp.sl.params.len).map fun c =>
          wotsSecAdrs ⟨coord.layer, coord.tree, lf'⟩ c).toFinset
      have hdisj1 : ∀ c : Fin vp.sl.params.len, wotsSecAdrs ⟨coord.layer, coord.tree, lf⟩ c ∉ S' := by
        intro c hm
        simp only [S', Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_map] at hm
        rcases hm with hmS | ⟨lf', hlf', c', -, heq⟩
        · exact hdisj lf (by simp) c hmS
        · have hp := congrArg Prod.fst
            (wotsSecAdrs_injective (a₁ := (⟨coord.layer, coord.tree, lf'⟩, c')) (a₂ := (⟨coord.layer, coord.tree, lf⟩, c)) heq)
          have : lf' = lf := congrArg LayerPosition.leaf hp
          exact hnd.1 (this ▸ hlf')
      have htail_dep : ∀ u₁ u₂, (∀ a ∈ S', u₁ a = u₂ a) → ∀ acc₁,
          Id.run (lfs.foldlM (fun a lf' => buildLeafM pr (sfDetCall pr pk) (detCs u₁) a ⟨coord.layer, coord.tree, lf'⟩) acc₁) =
          Id.run (lfs.foldlM (fun a lf' => buildLeafM pr (sfDetCall pr pk) (detCs u₂) a ⟨coord.layer, coord.tree, lf'⟩) acc₁) := by
        intro u₁ u₂ hu acc₁
        have haux : ∀ (ls : List (Fin (2 ^ vp.sl.params.hp))) (a0 : HybAcc pr),
            (∀ lf' ∈ ls, ∀ c, wotsSecAdrs ⟨coord.layer, coord.tree, lf'⟩ c ∈ S') →
            Id.run (ls.foldlM (fun a lf' => buildLeafM pr (sfDetCall pr pk) (detCs u₁) a ⟨coord.layer, coord.tree, lf'⟩) a0) =
            Id.run (ls.foldlM (fun a lf' => buildLeafM pr (sfDetCall pr pk) (detCs u₂) a ⟨coord.layer, coord.tree, lf'⟩) a0) := by
          intro ls; induction ls with
          | nil => intro _ _; rfl
          | cons lf' ls' ihls =>
            intro a0 hsub
            have h1 : Id.run (buildLeafM pr (sfDetCall pr pk) (detCs u₁) a0 ⟨coord.layer, coord.tree, lf'⟩) =
                Id.run (buildLeafM pr (sfDetCall pr pk) (detCs u₂) a0 ⟨coord.layer, coord.tree, lf'⟩) := by
              unfold buildLeafM
              simp only [Id.run_bind, idRun_ofFnM, sfDetCall, Id.run_pure, detCs]
              have hvec : (Vector.ofFn fun c : Fin vp.sl.params.len =>
                  (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (u₁ (wotsSecAdrs ⟨coord.layer, coord.tree, lf'⟩ c)),
                   Id.run (slChainM pr (sfDetCall pr pk) (wotsChainAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf'⟩) c.val)
                      (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)
                      (u₁ (wotsSecAdrs ⟨coord.layer, coord.tree, lf'⟩ c)))
                    (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)))) =
                (Vector.ofFn fun c : Fin vp.sl.params.len =>
                  (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (u₂ (wotsSecAdrs ⟨coord.layer, coord.tree, lf'⟩ c)),
                   Id.run (slChainM pr (sfDetCall pr pk) (wotsChainAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, lf'⟩) c.val)
                      (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)
                      (u₂ (wotsSecAdrs ⟨coord.layer, coord.tree, lf'⟩ c)))
                    (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)
                    (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr a0.tbl ⟨coord.layer, coord.tree, lf'⟩) c.val)))) := by
                apply Vector.ext; intro c hc; simp only [Vector.getElem_ofFn]
                rw [hu _ (hsub lf' (by simp) ⟨c, hc⟩)]
              simp only [hvec]
            simp only [List.foldlM_cons, Id.run_bind, h1]
            exact ihls _ (fun lf'' hlf'' => hsub lf'' (by simp [hlf'']))
        exact haux lfs acc₁ (fun lf' hlf' c => by
          simp only [S', Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_map]
          right; exact ⟨lf', hlf', c, List.mem_finRange c, rfl⟩)
      simp only [List.foldlM_cons, Id.run_bind, bind_assoc]
      refine (hleaf_eq ⟨coord.layer, coord.tree, lf⟩ acc S' hdisj1
        (fun uW a1 => K uW (Id.run (lfs.foldlM (fun a lf' =>
          buildLeafM pr (sfDetCall pr pk) (detCs uW) a ⟨coord.layer, coord.tree, lf'⟩) a1)))
        (fun u₁ u₂ hu a1 => by
          rw [htail_dep u₁ u₂ hu a1, hK u₁ u₂ (fun a ha => hu a (Finset.mem_union_left _ ha))])).trans ?_
      refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine (EvalDistEq.bind_right _ fun a1 =>
        ih hnd.2 a1 S (fun lf' hlf' => hdisj lf' (by simp [hlf'])) K hK).trans ?_
      exact EvalDistEq.bind_bind_swap _ _ _
  -- Helper: fold `buildTreeM` over any `Nodup` list of `LayerTreeCoord`s
  have htrees_eq : ∀ (ts : List (LayerTreeCoord vp.sl)),
      ts.Nodup →
      ∀ (acc : HybAcc pr) (S : Finset (SlSecAdrs vp)),
      (∀ coord ∈ ts, ∀ lf : Fin (2 ^ vp.sl.params.hp), ∀ c : Fin vp.sl.params.len,
        wotsSecAdrs ⟨coord.layer, coord.tree, lf⟩ c ∉ S) →
      ∀ (K : (SlSecAdrs vp → pr.Y) → HybAcc pr → ProbComp β),
      (∀ u₁ u₂, (∀ a ∈ S, u₁ a = u₂ a) → ∀ a', K u₁ a' = K u₂ a') →
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW =>
        K uW (Id.run (ts.foldlM (buildTreeM pr (sfDetCall pr pk) (detCs uW)) acc))) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW =>
        (ts.foldlM (buildTreeM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs) acc) >>= K uW) := by
    intro ts; induction ts with
    | nil =>
      intro _ acc _ _ K _
      simp only [List.foldlM_nil, Id.run_pure, pure_bind]; exact EvalDistEq.refl _
    | cons coord coords ih =>
      intro hnd acc S hdisj K hK
      rw [List.nodup_cons] at hnd
      let S' : Finset (SlSecAdrs vp) :=
        S ∪ (coords.flatMap fun c' =>
          (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun ch =>
              wotsSecAdrs ⟨c'.layer, c'.tree, lf⟩ ch).toFinset
      have hdisj1 : ∀ lf ∈ List.finRange (2 ^ vp.sl.params.hp), ∀ ch : Fin vp.sl.params.len,
          wotsSecAdrs ⟨coord.layer, coord.tree, lf⟩ ch ∉ S' := by
        intro lf _ ch hm
        simp only [S', Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_map] at hm
        rcases hm with hmS | ⟨c', hc', lf', -, ch', -, heq⟩
        · exact hdisj coord (by simp) lf ch hmS
        · have hp := congrArg Prod.fst
            (wotsSecAdrs_injective (a₁ := (⟨c'.layer, c'.tree, lf'⟩, ch')) (a₂ := (⟨coord.layer, coord.tree, lf⟩, ch)) heq)
          have hceq : c' = coord := by
            cases c'; cases coord
            have hl : _ = _ := congrArg LayerPosition.layer hp
            simp only at hl; subst hl
            have ht : _ = _ := congrArg (fun p : LayerPosition vp.sl => p.tree.val) hp
            simp only at ht
            exact congrArg _ (Fin.ext ht)
          exact hnd.1 (hceq ▸ hc')
      have htail_dep : ∀ u₁ u₂, (∀ a ∈ S', u₁ a = u₂ a) → ∀ acc₁,
          Id.run (coords.foldlM (buildTreeM pr (sfDetCall pr pk) (detCs u₁)) acc₁) =
          Id.run (coords.foldlM (buildTreeM pr (sfDetCall pr pk) (detCs u₂)) acc₁) := by
        intro u₁ u₂ hu acc₁
        have haux : ∀ (cs : List (LayerTreeCoord vp.sl)) (a0 : HybAcc pr),
            (∀ c' ∈ cs, ∀ lf ch, wotsSecAdrs ⟨c'.layer, c'.tree, lf⟩ ch ∈ S') →
            Id.run (cs.foldlM (buildTreeM pr (sfDetCall pr pk) (detCs u₁)) a0) =
            Id.run (cs.foldlM (buildTreeM pr (sfDetCall pr pk) (detCs u₂)) a0) := by
          intro cs; induction cs with
          | nil => intro _ _; rfl
          | cons c' cs' ihc =>
            intro a0 hsub
            have h1 : Id.run (buildTreeM pr (sfDetCall pr pk) (detCs u₁) a0 c') =
                Id.run (buildTreeM pr (sfDetCall pr pk) (detCs u₂) a0 c') := by
              unfold buildTreeM
              have hlfs : ∀ (ls : List (Fin (2 ^ vp.sl.params.hp))) (b0 : HybAcc pr),
                  Id.run (ls.foldlM (fun a lf => buildLeafM pr (sfDetCall pr pk) (detCs u₁) a ⟨c'.layer, c'.tree, lf⟩) b0) =
                  Id.run (ls.foldlM (fun a lf => buildLeafM pr (sfDetCall pr pk) (detCs u₂) a ⟨c'.layer, c'.tree, lf⟩) b0) := by
                intro ls; induction ls with
                | nil => intro _; rfl
                | cons lf ls' ihl =>
                  intro b0
                  have hlf : Id.run (buildLeafM pr (sfDetCall pr pk) (detCs u₁) b0 ⟨c'.layer, c'.tree, lf⟩) =
                      Id.run (buildLeafM pr (sfDetCall pr pk) (detCs u₂) b0 ⟨c'.layer, c'.tree, lf⟩) := by
                    unfold buildLeafM
                    simp only [Id.run_bind, idRun_ofFnM, sfDetCall, Id.run_pure, detCs]
                    have hvec : (Vector.ofFn fun ch : Fin vp.sl.params.len =>
                        (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (u₁ (wotsSecAdrs ⟨c'.layer, c'.tree, lf⟩ ch)),
                         Id.run (slChainM pr (sfDetCall pr pk) (wotsChainAdrs (wotsInstanceAdrs ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨c'.layer, c'.tree, lf⟩) ch.val)
                            (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)
                            (u₁ (wotsSecAdrs ⟨c'.layer, c'.tree, lf⟩ ch)))
                          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)))) =
                      (Vector.ofFn fun ch : Fin vp.sl.params.len =>
                        (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (u₂ (wotsSecAdrs ⟨c'.layer, c'.tree, lf⟩ ch)),
                         Id.run (slChainM pr (sfDetCall pr pk) (wotsChainAdrs (wotsInstanceAdrs ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs ⟨c'.layer, c'.tree, lf⟩) ch.val)
                            (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)
                            (u₂ (wotsSecAdrs ⟨c'.layer, c'.tree, lf⟩ ch)))
                          (chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)
                          (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr b0.tbl ⟨c'.layer, c'.tree, lf⟩) ch.val)))) := by
                      apply Vector.ext; intro ch hch; simp only [Vector.getElem_ofFn]
                      rw [hu _ (hsub c' (by simp) lf ⟨ch, hch⟩)]
                    simp only [hvec]
                  simp only [List.foldlM_cons, Id.run_bind, hlf]
                  exact ihl _
              simp only [Id.run_bind, hlfs]
            simp only [List.foldlM_cons, Id.run_bind, h1]
            exact ihc _ (fun c'' hc'' => hsub c'' (by simp [hc'']))
        exact haux coords acc₁ (fun c' hc' lf ch => by
          simp only [S', Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_map]
          right; exact ⟨c', hc', lf, List.mem_finRange lf, ch, List.mem_finRange ch, rfl⟩)
      -- Split `buildTreeM` into leaves + deterministic XMSS internal nodes
      let xmssFinish (a1 : HybAcc pr) : HybAcc pr :=
        { a1 with tbl := Id.run ((perfectInternalCoords vp.sl.params.hp).foldlM (fun t zi => do
          let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
          let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
          let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
          let v ← sfDetCall pr pk .H a (lv, rv)
          return Function.update t a (some v)) a1.tbl) }
      simp only [List.foldlM_cons, Id.run_bind, bind_assoc]
      have htree_det : ∀ uW, Id.run (buildTreeM pr (sfDetCall pr pk) (detCs uW) acc coord) =
          xmssFinish (Id.run ((List.finRange (2 ^ vp.sl.params.hp)).foldlM
            (fun a lf => buildLeafM pr (sfDetCall pr pk) (detCs uW) a ⟨coord.layer, coord.tree, lf⟩) acc)) := by
        intro uW; rfl
      have htree_prob : buildTreeM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs acc coord =
          ((List.finRange (2 ^ vp.sl.params.hp)).foldlM
            (fun a lf => buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs a ⟨coord.layer, coord.tree, lf⟩) acc) >>=
          fun a1 => pure (xmssFinish a1) := by
        unfold buildTreeM
        refine bind_congr fun a1 => ?_
        rw [hxmss_prob coord a1.tbl, pure_bind]
      simp only [htree_det, htree_prob, bind_assoc, pure_bind]
      refine (hleaves_eq coord (List.finRange (2 ^ vp.sl.params.hp)) (List.nodup_finRange _) acc S'
        hdisj1 (fun uW a1 => K uW (Id.run (coords.foldlM (buildTreeM pr (sfDetCall pr pk) (detCs uW)) (xmssFinish a1))))
        (fun u₁ u₂ hu a1 => by
          rw [htail_dep u₁ u₂ hu (xmssFinish a1), hK u₁ u₂ (fun a ha => hu a (Finset.mem_union_left _ ha))])).trans ?_
      refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine (EvalDistEq.bind_right _ fun a1 =>
        ih hnd.2 (xmssFinish a1) S (fun c' hc' => hdisj c' (by simp [hc'])) K hK).trans ?_
      exact EvalDistEq.bind_bind_swap _ _ _
  -- Assemble for `hybTreeDet` vs `hybTreeProb`!
  set tbl₀ := Id.run ((forsAddresses vp).foldlM (fun tbl a => do
    let v ← evalNodeM pr (sfDetCall pr pk) uFors tbl a
    return Function.update tbl a (some v)) (fun _ => none))
  have hlhs : ∀ uW, f (mix uW) (hybTreeDet pr γ pk (mix uW)) =
      (fun aFin => f uFors ⟨(aFin.tbl (topRootAdrs vp)).getD default, aFin.tbl, aFin.wotsMsg, aFin.wotsSig⟩)
        (Id.run ((allXmssTreesList vp).foldlM (buildTreeM pr (sfDetCall pr pk) (detCs uW))
          ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩)) := by
    intro uW
    rw [hf (mix uW) uFors (hmix_non5 uW)]
    congr 1
    unfold hybTreeDet buildHybTreeM
    simp only [Id.run_bind, hfors_eq uW]
    have hcs : (fun pos c b => (pure (hybBlockVal pr γ pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b
        (slSecOf pr (mix uW) (wotsSkAdrs (wotsInstanceAdrs pos) c.val))) : Id pr.Y)) = detCs uW := by
      funext pos c b; simp [detCs, hmix_5]
    rw [hcs]; rfl
  have hrhs : (hybTreeProb pr γ pk uFors >>= f uFors) =
      ((allXmssTreesList vp).foldlM (buildTreeM pr (fun i a msg => pure (pr.memberEval i pk a msg)) probCs)
        ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩) >>=
      fun aFin => f uFors ⟨(aFin.tbl (topRootAdrs vp)).getD default, aFin.tbl, aFin.wotsMsg, aFin.wotsSig⟩ := by
    unfold hybTreeProb buildHybTreeM
    simp only [hfors_prob, bind_assoc, pure_bind]
    rfl
  change ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uW => f (mix uW) (hybTreeDet pr γ pk (mix uW))) =ᵈ _
  simp only [hlhs, hrhs]
  refine (htrees_eq (allXmssTreesList vp) (allXmssTreesList_nodup vp)
    ⟨tbl₀, fun _ => default, fun _ => Vector.replicate _ default⟩ ∅
    (fun _ _ _ _ h => by simp at h)
    (fun _ aFin => f uFors ⟨(aFin.tbl (topRootAdrs vp)).getD default, aFin.tbl, aFin.wotsMsg, aFin.wotsSig⟩)
    (fun _ _ _ _ => rfl)).trans ?_
  exact EvalDistEq.bind_const ($ᵗ (SlSecAdrs vp → pr.Y)) _

end DetProbEquiv

/-! ## 8. Stage-1 SM-UD and SM-PRE reductions (`B_ud`, `B_pre`) and `wotsPre_bound` -/

section Reductions

variable {vp : ValidatedParams} (pr : Primitives vp.params)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]

/-- Number of WOTS+ chains across the entire SLH-DSA hypertree (`q₂ = wotsInstanceCount * len`). -/
def qWots (vp : ValidatedParams) : ℕ :=
  wotsInstanceCount vp.sl.params * vp.sl.params.len

/-- Position-and-chain key `(layer, tree, leaf, chain)` of a `WOTS_HASH` address. -/
def chainKey (a : Adrs) : ℕ × ℕ × ℕ × ℕ :=
  (a.layer, a.tree, a.word1, a.word2)

/-- Position-and-chain key of `(pos, c)`. -/
def pcKey (pc : LayerPosition vp.sl × Fin vp.sl.params.len) : ℕ × ℕ × ℕ × ℕ :=
  (pc.1.layer.val, pc.1.tree.val, pc.1.leaf.val, pc.2.val)

theorem chainKey_wotsChainAdrs (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (k : ℕ) :
    chainKey ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress k) = pcKey (pos, c) := by
  simp [chainKey, pcKey, wotsChainAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs,
    Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
    Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.getKeyPairAddress]

theorem type_wotsChainAdrs (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (k : ℕ) :
    ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress k).type = 0 := by
  simp [wotsChainAdrs, Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress,
    Adrs.setTypeAndClear, AddrType.toCode]

theorem word3_wotsChainAdrs (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (k : ℕ) :
    ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress k).word3 = k := by
  simp [wotsChainAdrs, Adrs.setHashAddress]

theorem pcKey_injective : Function.Injective (pcKey (vp := vp)) := by
  rintro ⟨⟨l₁, t₁, lf₁⟩, c₁⟩ ⟨⟨l₂, t₂, lf₂⟩, c₂⟩ h
  simp only [pcKey, Prod.mk.injEq] at h
  obtain ⟨hl, ht, hlf, hc⟩ := h
  have hl' : l₁ = l₂ := Fin.ext hl; subst hl'
  have ht' : t₁ = t₂ := Fin.ext ht; subst ht'
  have hlf' : lf₁ = lf₂ := Fin.ext hlf; subst hlf'
  have hc' : c₁ = c₂ := Fin.ext hc; subst hc'
  rfl

/-- Stage-1 `SM-UD` chain-start callback for hybrid `γ`: queries `O_ch` at hash address `γ`
whenever `γ < b - 1`, and samples a fresh seed via `unifSpec` otherwise. -/
noncomputable def udChainStart (γ : ℕ) (pos : LayerPosition vp.sl)
    (c : Fin vp.sl.params.len) (b : ℕ) : OracleComp (Fxmss.Rom.Hyb.FSpec pr) pr.Y :=
  let chAdrs := wotsChainAdrs (wotsInstanceAdrs pos) c.val
  if γ < b - 1 then do
    let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl (chAdrs.setHashAddress γ)))) :
      OracleComp (Fxmss.Rom.Hyb.FSpec pr) (Option pr.Y))
    slChainM pr (hybCollCall pr) chAdrs (r.getD default) (γ + 1) (b - (γ + 1))
  else do
    let x ← (liftM ($ᵗ pr.Y) : OracleComp (Fxmss.Rom.Hyb.FSpec pr) pr.Y)
    let m := min γ (b - 1)
    slChainM pr (hybCollCall pr) chAdrs x m (b - m)

/-- Stage-1 `SM-UD` virtual-hypertree builder for hybrid `γ`. -/
noncomputable def udBuildM (γ : ℕ) (u : SlSecAdrs vp → pr.Y) :
    OracleComp (Fxmss.Rom.Hyb.FSpec pr) (HybTree pr) :=
  buildHybTreeM pr (hybCollCall pr) (udChainStart pr γ) u

/-- Stage-1 `SM-PRE` chain-start callback: queries `O_ch` at hash address `b - 1` whenever
`0 < b` (recording the tweak in `StateT (List Adrs)`), and samples a fresh seed otherwise. -/
noncomputable def preChainStart (pos : LayerPosition vp.sl)
    (c : Fin vp.sl.params.len) (b : ℕ) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y :=
  let chAdrs := wotsChainAdrs (wotsInstanceAdrs pos) c.val
  if 0 < b then do
    let a := chAdrs.setHashAddress (b - 1)
    let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl a))) :
      StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (Option pr.Y))
    modify (· ++ [a])
    return r.getD default
  else
    (liftM ($ᵗ pr.Y) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y)

/-- Stage-1 `SM-PRE` virtual-hypertree builder returning `(hyb, savedT)`. -/
noncomputable def preBuildM (u : SlSecAdrs vp → pr.Y) :
    OracleComp (Fxmss.Rom.Hyb.FSpec pr) (HybTree pr × List Adrs) :=
  (buildHybTreeM pr (fun i a msg => liftM (hybCollCall pr i a msg)) (preChainStart pr) u).run []

/-- Shared freshness invariant on `(qsTweaks, tws)` for both `udBuildM` and `preBuildM`: every
challenge tweak has `type = 0` and belongs to `seen`, every `type = 0` collection tweak belongs to
`seen`, and `qsTweaks.length ≤ seen.length`. -/
def ChainOracleInv (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
    (qsTweaks tws : List Adrs) : Prop :=
  (∀ q ∈ qsTweaks, q.type = 0 ∧ ∃ pc ∈ seen, chainKey q = pcKey pc) ∧
  (∀ t ∈ tws, t.type ≠ 0 ∨ ∃ pc ∈ seen, chainKey t = pcKey pc) ∧
  qsTweaks.length ≤ seen.length

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] in
/-- Helper: `slChainM` through `hybCollCall` against ANY `SM_DT_UD_oracles` or `SM_DT_PRE_oracles`
when every tweak in the chain is unreserved. -/
private theorem simulateQ_slChainM_run {σ : Type}
    (impl : QueryImpl (Fxmss.Rom.Hyb.FSpec pr) (StateT σ ProbComp)) (pk : pr.PkSeed)
    (Inv : σ → Prop) (step : σ → Adrs → σ)
    (chAdrs : Adrs) {x : pr.Y} (start : ℕ)
    (hcall : ∀ k s, start ≤ k → Inv s →
      (simulateQ impl (hybCollCall pr .F (chAdrs.setHashAddress k)
        (slChainDet pr pk chAdrs x start (k - start)))).run s =
      pure (pr.F pk (chAdrs.setHashAddress k) (slChainDet pr pk chAdrs x start (k - start)),
        step s (chAdrs.setHashAddress k)))
    (hinv : ∀ k s, start ≤ k → Inv s → Inv (step s (chAdrs.setHashAddress k))) :
    ∀ steps s, Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (slChainM pr (hybCollCall pr) chAdrs x start steps)).run s =
          pure (slChainDet pr pk chAdrs x start steps, s') := by
  intro steps; induction steps with
  | zero => intro s hs; exact ⟨s, hs, by simp [slChainM, slChainDet]⟩
  | succ steps ih =>
    intro s hs
    obtain ⟨s₁, hs₁, h1⟩ := ih s hs
    have hstep := hcall (start + steps) s₁ (Nat.le_add_right _ _) hs₁
    simp only [Nat.add_sub_cancel_left] at hstep
    refine ⟨step s₁ _, hinv (start + steps) s₁ (Nat.le_add_right _ _) hs₁, ?_⟩
    simp only [slChainM, simulateQ_bind, StateT.run_bind, h1, pure_bind, slChainDet, Id.run_bind,
      sfDetCall, Id.run_pure]
    exact hstep

omit [Fintype pr.Y] [DecidableEq pr.Y] [DecidableEq pr.PkSeed] in
/-- **Exact simulation of `udBuildM γ` against `SM_DT_UD_oracles w (probUD pr (qWots vp)) pk`**:
in `.real` it produces the EXACT `ProbComp` distribution `hybTreeProb pr γ pk u`; in `.ideal` it
produces `hybTreeProb pr (γ + 1) pk u`. -/
theorem simulateQ_udBuildM_eval {β : Type} (w : SM_DT_UD_World) (γ : ℕ) (pk : pr.PkSeed)
    (u : SlSecAdrs vp → pr.Y) (tws₀ : List Adrs) (htws₀ : ∀ t ∈ tws₀, Scheme.IsStateful t)
    (K : HybTree pr → ProbComp β) :
    ((simulateQ (SM_DT_UD_oracles w (probUD pr (qWots vp)) pk) (udBuildM pr γ u)).run ([], tws₀) >>=
        fun z => K z.1) =
      (hybTreeProb pr (if w = .real then γ else γ + 1) pk u >>= K) := by
  set impl := SM_DT_UD_oracles w (probUD pr (qWots vp)) pk
  set γ' := if w = .real then γ else γ + 1
  -- Step 1: FORS pass is deterministic and produces `tbl₀`, leaving `qs = []` and `t.type ≠ 0`
  have hfors : ∃ tws₁, (∀ t ∈ tws₁, t.type ≠ 0) ∧
      (simulateQ impl ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (hybCollCall pr) u tbl a
        return Function.update tbl a (some v)) (fun _ => none))).run ([], tws₀) =
      pure (Id.run ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
        return Function.update tbl a (some v)) (fun _ => none)), ([], tws₁)) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y) (tws : List Adrs),
        (∀ a ∈ l, a.type = 3 ∨ a.type = 4) →
        (∀ t ∈ tws, t.type ≠ 0) →
        ∃ tws', (∀ t ∈ tws', t.type ≠ 0) ∧
          (simulateQ impl (l.foldlM (fun tbl a => do
            let v ← evalNodeM pr (hybCollCall pr) u tbl a
            return Function.update tbl a (some v)) tbl)).run ([], tws) =
          pure (Id.run (l.foldlM (fun tbl a => do
            let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
            return Function.update tbl a (some v)) tbl), ([], tws')) := by
      intro l; induction l with
      | nil => intro tbl tws _ htws; exact ⟨tws, htws, by simp⟩
      | cons a as ih =>
        intro tbl tws hty htws
        have ha_ty : a.type = 3 ∨ a.type = 4 := hty a (by simp)
        have ha_ne0 : a.type ≠ 0 := by rcases ha_ty with h | h <;> omega
        have ha_val : ValidNodeAdrs a := ⟨by rcases ha_ty with h | h <;> omega, fun h => by omega⟩
        obtain ⟨⟨i, msg⟩, hinp⟩ := Option.isSome_iff_exists.1 (evalNodeInput_isSome_of_valid pr u tbl ha_val)
        have h1 : (simulateQ impl (evalNodeM pr (hybCollCall pr) u tbl a)).run ([], tws) =
            pure (Id.run (evalNodeM pr (sfDetCall pr pk) u tbl a), ([], tws ++ [a])) := by
          rw [evalNodeM_eq_of_input, evalNodeM_eq_of_input, hinp]
          unfold hybCollCall sfDetCall impl
          simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_UD_oracles, QueryImpl.add_apply_inr,
            StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
            pure_bind, TweakReserved, List.not_mem_nil, false_and, exists_false,
            ↓reduceIte, StateT.run_set, Option.getD_some, Id.run_pure]
          rfl
        have htws1 : ∀ t ∈ tws ++ [a], t.type ≠ 0 := by
          intro t ht; rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2; exact ha_ne0
        obtain ⟨tws', htws', hrest⟩ := ih _ (tws ++ [a]) (fun b hb => hty b (by simp [hb])) htws1
        refine ⟨tws', htws', ?_⟩
        simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, h1, pure_bind,
          simulateQ_pure, StateT.run_pure, Id.run_bind, Id.run_pure]
        exact hrest
    exact haux _ _ tws₀ (fun a ha => type_of_mem_forsAddresses ha) (fun t ht h0 => by
      obtain ⟨st, hst⟩ := htws₀ t ht; have := st.sixteen_le_toCode; omega)
  -- Helper: single chain step `(pos, c)` for `udChainStart` + remaining chain
  have hchain_step : ∀ (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (b : ℕ)
      (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
      (hnot : (pos, c) ∉ seen) (hlen : seen.length < qWots vp)
      (s : List Adrs × List Adrs) (hs : ChainOracleInv seen s.1 s.2)
      (K₁ : (pr.Y × pr.Y) × (List Adrs × List Adrs) → ProbComp β)
      (K₁' : pr.Y × pr.Y → ProbComp β)
      (hK : ∀ pair s', ChainOracleInv (seen ++ [(pos, c)]) s'.1 s'.2 → K₁ (pair, s') = K₁' pair),
      ((simulateQ impl (do
        let sigBlk ← udChainStart pr γ pos c b
        let top ← slChainM pr (hybCollCall pr) (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b
          (vp.sl.params.w - 1 - b)
        return (sigBlk, top))).run s >>= K₁) =
      ((do
        let x ← $ᵗ pr.Y
        let sigBlk := hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x
        let top := slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)) >>= K₁') := by
    intro pos c b seen hnot hlen s hs K₁ K₁' hK
    set chAdrs := wotsChainAdrs (wotsInstanceAdrs pos) c.val
    have hnot_q : ∀ q ∈ s.1, chainKey q ≠ pcKey (pos, c) := by
      intro q hq heq
      obtain ⟨_, pc, hpc, hk⟩ := hs.1 q hq
      exact hnot (pcKey_injective (hk.symm.trans heq) ▸ hpc)
    have hnot_t : ∀ t ∈ s.2, t.type = 0 → chainKey t ≠ pcKey (pos, c) := by
      intro t ht ht0 heq
      rcases hs.2.1 t ht with hne0 | ⟨pc, hpc, hk⟩
      · exact hne0 ht0
      · exact hnot (pcKey_injective (hk.symm.trans heq) ▸ hpc)
    have hcoll_step : ∀ (qs₁ tws₁ : List Adrs) (k : ℕ) (v : pr.Y),
        (∀ q ∈ qs₁, q ≠ chAdrs.setHashAddress k) →
        (simulateQ impl (hybCollCall pr .F (chAdrs.setHashAddress k) v)).run (qs₁, tws₁) =
          pure (pr.F pk (chAdrs.setHashAddress k) v, (qs₁, tws₁ ++ [chAdrs.setHashAddress k])) := by
      intro qs₁ tws₁ k v hne
      have hnr : ¬ TweakReserved id qs₁ (chAdrs.setHashAddress k) := fun ⟨q, hq, heq⟩ => hne q hq heq
      unfold hybCollCall impl
      simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_UD_oracles, QueryImpl.add_apply_inr,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
        pure_bind, hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
      rfl
    unfold udChainStart
    dsimp only
    split_ifs with hγ
    · -- Branch `γ < b - 1`: query `SM-UD` challenge oracle at `chAdrs.setHashAddress γ`
      set aγ := chAdrs.setHashAddress γ
      have hfr : TweakFresh id s.1 s.2 aγ := by
        constructor
        · rintro ⟨q, hq, heq⟩
          dsimp only [id] at heq
          exact hnot_q q hq (by rw [heq, chainKey_wotsChainAdrs])
        · intro hmem
          exact hnot_t aγ hmem (type_wotsChainAdrs pos c γ) (chainKey_wotsChainAdrs pos c γ)
      have hcap : ¬ qWots vp ≤ s.1.length := by have := hs.2.2; omega
      have hchal : (simulateQ impl (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl aγ))) :
          OracleComp (Fxmss.Rom.Hyb.FSpec pr) (Option pr.Y))).run s =
          (do let x ← $ᵗ pr.Y
              let y := match w with | .real => pr.F pk aγ x | .ideal => x
              return (some y, (s.1 ++ [aγ], s.2))) := by
        unfold impl
        simp only [simulateQ_spec_query, SM_DT_UD_oracles, QueryImpl.add_apply_inr,
          QueryImpl.add_apply_inl, SM_DT_UD_challengeOracle, StateT.run_bind, StateT.run_get,
          pure_bind, hfr, hcap, not_true_eq_false, or_self, ↓reduceIte, StateT.run_monadLift,
          StateT.run_set, StateT.run_pure, bind_assoc]
        cases w <;> simp [Fxmss.Rom.thF, SM_DT_UD_response, TweakableHash.ofFun]
      simp only [simulateQ_bind, StateT.run_bind, hchal, bind_assoc, pure_bind]
      refine bind_congr fun x => ?_
      set y₀ := match w with | .real => pr.F pk aγ x | .ideal => x
      have hInv_ch : ∀ (tws₁ : List Adrs),
          (∀ t ∈ tws₁, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc) →
          ChainOracleInv (seen ++ [(pos, c)]) (s.1 ++ [aγ]) tws₁ := by
        intro tws₁ htws₁
        refine ⟨fun q hq => ?_, htws₁, by simp; have := hs.2.2; omega⟩
        rcases List.mem_append.1 hq with hq1 | hq2
        · obtain ⟨ht0, pc, hpc, hk⟩ := hs.1 q hq1
          exact ⟨ht0, pc, List.mem_append_left _ hpc, hk⟩
        · simp only [List.mem_singleton] at hq2; subst hq2
          exact ⟨type_wotsChainAdrs pos c γ, (pos, c), List.mem_append_right _ (by simp),
            chainKey_wotsChainAdrs pos c γ⟩
      have hne_gt : ∀ k, γ + 1 ≤ k → ∀ q ∈ s.1 ++ [aγ], q ≠ chAdrs.setHashAddress k := by
        intro k hk q hq heq
        rcases List.mem_append.1 hq with hq1 | hq2
        · exact hnot_q q hq1 (by rw [heq, chainKey_wotsChainAdrs])
        · simp only [List.mem_singleton] at hq2; subst hq2
          have := congrArg Adrs.word3 heq
          simp only [aγ, chAdrs, word3_wotsChainAdrs] at this; omega
      obtain ⟨s₁, hs₁, hrun₁⟩ := simulateQ_slChainM_run pr impl pk
        (fun st => st.1 = s.1 ++ [aγ] ∧ ∀ t ∈ st.2, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc)
        (fun st a => (st.1, st.2 ++ [a])) chAdrs (x := y₀) (γ + 1)
        (fun k st hk ⟨hqeq, _⟩ => by
          rcases st with ⟨qs₁, tws₁⟩; dsimp only at hqeq; subst hqeq
          exact hcoll_step _ tws₁ k _ (hne_gt k hk))
        (fun k st hk ⟨hqeq, htws₁⟩ => ⟨hqeq, fun t ht => by
          rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws₁ t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2
            exact Or.inr ⟨(pos, c), List.mem_append_right _ (by simp), chainKey_wotsChainAdrs pos c k⟩⟩)
        (b - (γ + 1)) (s.1 ++ [aγ], s.2)
        ⟨rfl, fun t ht => (hs.2.1 t ht).imp_right fun ⟨pc, hpc, hk⟩ => ⟨pc, List.mem_append_left _ hpc, hk⟩⟩
      obtain ⟨s₂, hs₂, hrun₂⟩ := simulateQ_slChainM_run pr impl pk
        (fun st => st.1 = s.1 ++ [aγ] ∧ ∀ t ∈ st.2, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc)
        (fun st a => (st.1, st.2 ++ [a])) chAdrs (x := slChainDet pr pk chAdrs y₀ (γ + 1) (b - (γ + 1))) b
        (fun k st hk ⟨hqeq, _⟩ => by
          rcases st with ⟨qs₁, tws₁⟩; dsimp only at hqeq; subst hqeq
          exact hcoll_step _ tws₁ k _ (hne_gt k (by omega)))
        (fun k st hk ⟨hqeq, htws₁⟩ => ⟨hqeq, fun t ht => by
          rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws₁ t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2
            exact Or.inr ⟨(pos, c), List.mem_append_right _ (by simp), chainKey_wotsChainAdrs pos c k⟩⟩)
        (vp.sl.params.w - 1 - b) s₁ hs₁
      simp only [Option.getD_some]
      rw [hrun₁, pure_bind, hrun₂, pure_bind]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      have hs2_inv : ChainOracleInv (seen ++ [(pos, c)]) s₂.1 s₂.2 := by
        rw [hs₂.1]; exact hInv_ch s₂.2 hs₂.2
      have hblk : slChainDet pr pk chAdrs y₀ (γ + 1) (b - (γ + 1)) = hybBlockVal pr γ' pk chAdrs b x := by
        cases w
        · simp only [y₀, γ', ↓reduceIte]; exact hybBlockVal_succ_F pr γ pk chAdrs b x hγ
        · simp only [y₀, γ', reduceCtorEq, ↓reduceIte]; exact hybBlockVal_succ_ideal pr γ pk chAdrs b x hγ
      rw [hK _ s₂ hs2_inv, hblk]
    · -- Branch `¬ (γ < b - 1)`: sample `x ← $ᵗ pr.Y` via `unifSpec`, run `slChainM` via `O_coll`
      have hunif : (simulateQ impl (liftM ($ᵗ pr.Y) : OracleComp (Fxmss.Rom.Hyb.FSpec pr) pr.Y)).run s =
          (fun x => (x, s)) <$> ($ᵗ pr.Y) := by
        unfold impl
        exact Fxmss.simulateQ_add_liftM_run _ ($ᵗ pr.Y) s
      simp only [simulateQ_bind, StateT.run_bind, hunif, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun x => ?_
      have hne_all : ∀ k, ∀ q ∈ s.1, q ≠ chAdrs.setHashAddress k := fun k q hq heq =>
        hnot_q q hq (by rw [heq, chainKey_wotsChainAdrs])
      set m := min γ (b - 1)
      obtain ⟨s₁, hs₁, hrun₁⟩ := simulateQ_slChainM_run pr impl pk
        (fun st => st.1 = s.1 ∧ ∀ t ∈ st.2, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc)
        (fun st a => (st.1, st.2 ++ [a])) chAdrs (x := x) m
        (fun k st _ ⟨hqeq, _⟩ => by
          rcases st with ⟨qs₁, tws₁⟩; dsimp only at hqeq; subst hqeq
          exact hcoll_step _ tws₁ k _ (hne_all k))
        (fun k st _ ⟨hqeq, htws₁⟩ => ⟨hqeq, fun t ht => by
          rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws₁ t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2
            exact Or.inr ⟨(pos, c), List.mem_append_right _ (by simp), chainKey_wotsChainAdrs pos c k⟩⟩)
        (b - m) s
        ⟨rfl, fun t ht => (hs.2.1 t ht).imp_right fun ⟨pc, hpc, hk⟩ => ⟨pc, List.mem_append_left _ hpc, hk⟩⟩
      obtain ⟨s₂, hs₂, hrun₂⟩ := simulateQ_slChainM_run pr impl pk
        (fun st => st.1 = s.1 ∧ ∀ t ∈ st.2, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc)
        (fun st a => (st.1, st.2 ++ [a])) chAdrs (x := slChainDet pr pk chAdrs x m (b - m)) b
        (fun k st _ ⟨hqeq, _⟩ => by
          rcases st with ⟨qs₁, tws₁⟩; dsimp only at hqeq; subst hqeq
          exact hcoll_step _ tws₁ k _ (hne_all k))
        (fun k st _ ⟨hqeq, htws₁⟩ => ⟨hqeq, fun t ht => by
          rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws₁ t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2
            exact Or.inr ⟨(pos, c), List.mem_append_right _ (by simp), chainKey_wotsChainAdrs pos c k⟩⟩)
        (vp.sl.params.w - 1 - b) s₁ hs₁
      dsimp only [Function.comp_def]
      rw [pure_bind, hrun₁, pure_bind, hrun₂, pure_bind]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      have hs2_inv : ChainOracleInv (seen ++ [(pos, c)]) s₂.1 s₂.2 := by
        refine ⟨fun q hq => ?_, hs₂.2, by rw [hs₂.1]; simp; have := hs.2.2; omega⟩
        rw [hs₂.1] at hq
        obtain ⟨ht0, pc, hpc, hk⟩ := hs.1 q hq
        exact ⟨ht0, pc, List.mem_append_left _ hpc, hk⟩
      have hblk : slChainDet pr pk chAdrs x m (b - m) = hybBlockVal pr γ' pk chAdrs b x := by
        cases w
        · rfl
        · simp only [γ', reduceCtorEq, ↓reduceIte]
          exact (hybBlockVal_succ_of_not_lt pr γ pk chAdrs b x hγ).symm
      rw [hK _ s₂ hs2_inv, hblk]
  -- Helper: `Vector.ofFnM` over chains of `pos`
  have hleaf_step : ∀ (pos : LayerPosition vp.sl) (acc : HybAcc pr)
      (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
      (hnot : ∀ c : Fin vp.sl.params.len, (pos, c) ∉ seen)
      (hlen : seen.length + vp.sl.params.len ≤ qWots vp)
      (s : List Adrs × List Adrs) (hs : ChainOracleInv seen s.1 s.2)
      (K₁ : HybAcc pr × (List Adrs × List Adrs) → ProbComp β)
      (K₁' : HybAcc pr → ProbComp β)
      (hK : ∀ a' s', ChainOracleInv (seen ++ (List.finRange vp.sl.params.len).map (pos, ·)) s'.1 s'.2 →
        K₁ (a', s') = K₁' a'),
      ((simulateQ impl (buildLeafM pr (hybCollCall pr) (udChainStart pr γ) acc pos)).run s >>= K₁) =
      ((buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg))
        (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
        acc pos) >>= K₁') := by
    intro pos acc seen hnot hlen s hs K₁ K₁' hK
    set msg := wotsMsgFromTbl pr acc.tbl pos
    -- Induction on `n ≤ len` for `Vector.ofFnM`
    have hvec : ∀ (n : ℕ) (hn : n ≤ vp.sl.params.len) (s₀ : List Adrs × List Adrs)
        (hs₀ : ChainOracleInv seen s₀.1 s₀.2)
        (Kv : Vector (pr.Y × pr.Y) n × (List Adrs × List Adrs) → ProbComp β)
        (Kv' : Vector (pr.Y × pr.Y) n → ProbComp β),
        (∀ v s', ChainOracleInv (seen ++ (List.finRange n).map fun j => (pos, ⟨j.val, by omega⟩)) s'.1 s'.2 →
          Kv (v, s') = Kv' v) →
        ((simulateQ impl (Vector.ofFnM fun j : Fin n => do
          let b := chainStepsCore pr.toSLHDSA.core msg j.val
          let sigBlk ← udChainStart pr γ pos ⟨j.val, by omega⟩ b
          let top ← slChainM pr (hybCollCall pr) (wotsChainAdrs (wotsInstanceAdrs pos) j.val) sigBlk b
            (vp.sl.params.w - 1 - b)
          return (sigBlk, top))).run s₀ >>= Kv) =
        ((Vector.ofFnM fun j : Fin n => do
          let b := chainStepsCore pr.toSLHDSA.core msg j.val
          let x ← $ᵗ pr.Y
          let sigBlk := hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) b x
          let top := slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) sigBlk b (vp.sl.params.w - 1 - b)
          return (sigBlk, top)) >>= Kv') := by
      intro n; induction n with
      | zero =>
        intro _ s₀ hs₀ Kv Kv' hKv
        simp only [Vector.ofFnM_zero, simulateQ_pure, StateT.run_pure, pure_bind]
        exact hKv #v[] s₀ (by simpa using hs₀)
      | succ n ihn =>
        intro hn s₀ hs₀ Kv Kv' hKv
        rw [Vector.ofFnM_succ, Vector.ofFnM_succ, simulateQ_bind, StateT.run_bind, bind_assoc, bind_assoc]
        refine ihn (by omega) s₀ hs₀ _ _ (fun v s₁ hs₁ => ?_)
        rw [simulateQ_bind, StateT.run_bind, bind_assoc, bind_assoc]
        simp only [Fin.val_last, simulateQ_pure, StateT.run_pure, pure_bind]
        set seen₁ := seen ++ (List.finRange n).map fun j => (pos, ⟨j.val, by omega⟩)
        have hnot1 : (pos, ⟨n, hn⟩) ∉ seen₁ := by
          intro hm; rcases List.mem_append.1 hm with hm1 | hm2
          · exact hnot ⟨n, hn⟩ hm1
          · obtain ⟨j, -, heq⟩ := List.mem_map.1 hm2
            have := congrArg (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len => pc.2.val) heq
            simp only at this; omega
        have hlen1 : seen₁.length < qWots vp := by simp [seen₁]; omega
        refine hchain_step pos ⟨n, hn⟩ (chainStepsCore pr.toSLHDSA.core msg n) seen₁ hnot1 hlen1 s₁ hs₁ _ _
          (fun pair s₂ hs₂ => ?_)
        have hseen_eq : seen₁ ++ [(pos, ⟨n, hn⟩)] =
            seen ++ (List.finRange (n + 1)).map fun j => (pos, ⟨j.val, by omega⟩) := by
          simp only [seen₁, List.append_assoc, List.finRange_succ_last, List.map_append,
            List.map_map, List.map_singleton, Function.comp_def, Fin.val_castSucc, Fin.val_last]
        rw [hseen_eq] at hs₂
        exact hKv (v.push pair) s₂ hs₂
    -- Apply `hvec` at `n = len`, then handle `hybCollCall .thLsl` (type 1 ≠ 0)
    unfold buildLeafM
    dsimp only
    change ((simulateQ impl _).run s >>= K₁) = _
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hprob_vec : (Vector.ofFnM fun c : Fin vp.sl.params.len => do
        let b := chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val
        let x ← $ᵗ pr.Y
        let sigBlk := hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x
        let top ← slChainM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y))
          (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)) =
      (Vector.ofFnM fun j : Fin vp.sl.params.len => do
        let b := chainStepsCore pr.toSLHDSA.core msg j.val
        let x ← $ᵗ pr.Y
        let sigBlk := hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) b x
        let top := slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)) := by
      congr 1; funext c
      refine bind_congr fun x => ?_
      have hc : ∀ chAdrs y st steps,
          slChainM pr (fun i a m => (pure (pr.memberEval i pk a m) : ProbComp pr.Y)) chAdrs y st steps =
            pure (slChainDet pr pk chAdrs y st steps) := by
        intro chAdrs y st steps; induction steps with
        | zero => rfl
        | succ steps ih => simp only [slChainM, ih, pure_bind, slChainDet, Id.run_bind, sfDetCall, Id.run_pure]
      simp only [hc, pure_bind, msg]
    simp only [pure_bind]
    rw [hprob_vec]
    refine hvec vp.sl.params.len le_rfl s hs _ _ (fun pairs s₁ hs₁ => ?_)
    have hnr : ¬ TweakReserved id s₁.1 (wotsPkAdrs (wotsInstanceAdrs pos)) := by
      rintro ⟨q, hq, heq⟩
      have ht0 := (hs₁.1 q hq).1
      dsimp only [id] at heq; rw [heq] at ht0
      simp [wotsPkAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode] at ht0
    have hwpk : (simulateQ impl (hybCollCall pr .thLsl (wotsPkAdrs (wotsInstanceAdrs pos))
        ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
          (Params.lsl_eq_len vp.valid).symm))).run s₁ =
        pure (pr.memberEval .thLsl pk (wotsPkAdrs (wotsInstanceAdrs pos))
          ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
            (Params.lsl_eq_len vp.valid).symm),
          (s₁.1, s₁.2 ++ [wotsPkAdrs (wotsInstanceAdrs pos)])) := by
      unfold hybCollCall impl
      simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_UD_oracles, QueryImpl.add_apply_inr,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
        pure_bind, hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
      rfl
    simp only [hwpk, pure_bind, simulateQ_pure, StateT.run_pure]
    have hs2 : ChainOracleInv (seen ++ (List.finRange vp.sl.params.len).map (pos, ·)) s₁.1
        (s₁.2 ++ [wotsPkAdrs (wotsInstanceAdrs pos)]) := by
      refine ⟨hs₁.1, fun t ht => ?_, hs₁.2.2⟩
      rcases List.mem_append.1 ht with ht1 | ht2
      · exact hs₁.2.1 t ht1
      · simp only [List.mem_singleton] at ht2; subst ht2
        left; simp [wotsPkAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode]
    exact hK _ _ hs2
  -- Helper: fold `buildTreeM` over `allXmssTrees vp.sl`
  have htrees_step : ∀ (ts : List (LayerTreeCoord vp.sl)),
      ts.Nodup →
      ∀ (acc : HybAcc pr) (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len)),
      (∀ coord ∈ ts, ∀ lf : Fin (2 ^ vp.sl.params.hp), ∀ c : Fin vp.sl.params.len,
        (⟨coord.layer, coord.tree, lf⟩, c) ∉ seen) →
      seen.length + ts.length * (2 ^ vp.sl.params.hp * vp.sl.params.len) ≤ qWots vp →
      ∀ (s : List Adrs × List Adrs), ChainOracleInv seen s.1 s.2 →
      ∀ (K₁ : HybAcc pr × (List Adrs × List Adrs) → ProbComp β) (K₁' : HybAcc pr → ProbComp β),
      (∀ a' s', ChainOracleInv (seen ++ ts.flatMap fun coord =>
        (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
          (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) s'.1 s'.2 →
        K₁ (a', s') = K₁' a') →
      ((simulateQ impl (ts.foldlM (buildTreeM pr (hybCollCall pr) (udChainStart pr γ)) acc)).run s >>= K₁) =
      ((ts.foldlM (buildTreeM pr (fun i a msg => pure (pr.memberEval i pk a msg))
        (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x))
        acc) >>= K₁') := by
    intro ts; induction ts with
    | nil =>
      intro _ acc seen _ _ s hs K₁ K₁' hK
      simp only [List.foldlM_nil, simulateQ_pure, StateT.run_pure, pure_bind]
      exact hK acc s (by simpa using hs)
    | cons coord coords iht =>
      intro hnd acc seen hnot hlen s hs K₁ K₁' hK
      rw [List.nodup_cons] at hnd
      simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, bind_assoc]
      -- First fold the `2^hp` leaves of `coord`
      have hlfs : ∀ (ls : List (Fin (2 ^ vp.sl.params.hp))),
          ls.Nodup →
          ∀ (a0 : HybAcc pr) (sn0 : List (LayerPosition vp.sl × Fin vp.sl.params.len)),
          (∀ lf ∈ ls, ∀ c, (⟨coord.layer, coord.tree, lf⟩, c) ∉ sn0) →
          sn0.length + ls.length * vp.sl.params.len ≤ qWots vp →
          ∀ (s0 : List Adrs × List Adrs), ChainOracleInv sn0 s0.1 s0.2 →
          ∀ (Kl : HybAcc pr × (List Adrs × List Adrs) → ProbComp β) (Kl' : HybAcc pr → ProbComp β),
          (∀ a' s', ChainOracleInv (sn0 ++ ls.flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) s'.1 s'.2 →
            Kl (a', s') = Kl' a') →
          ((simulateQ impl (ls.foldlM (fun a lf => buildLeafM pr (hybCollCall pr) (udChainStart pr γ) a ⟨coord.layer, coord.tree, lf⟩) a0)).run s0 >>= Kl) =
          ((ls.foldlM (fun a lf => buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg))
            (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
            a ⟨coord.layer, coord.tree, lf⟩) a0) >>= Kl') := by
        intro ls; induction ls with
        | nil =>
          intro _ a0 sn0 _ _ s0 hs0 Kl Kl' hKl
          simp only [List.foldlM_nil, simulateQ_pure, StateT.run_pure, pure_bind]
          exact hKl a0 s0 (by simpa using hs0)
        | cons lf ls' ihl =>
          intro hndl a0 sn0 hnotl hlenl s0 hs0 Kl Kl' hKl
          rw [List.nodup_cons] at hndl
          simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, bind_assoc]
          refine hleaf_step ⟨coord.layer, coord.tree, lf⟩ a0 sn0 (hnotl lf (by simp))
            (by simp only [List.length_cons] at hlenl; nlinarith) s0 hs0 _ _ (fun a1 s1 hs1 => ?_)
          set sn1 := sn0 ++ (List.finRange vp.sl.params.len).map (⟨coord.layer, coord.tree, lf⟩, ·)
          refine ihl hndl.2 a1 sn1 (fun lf' hlf' c hm => ?_)
            (by simp only [sn1, List.length_append, List.length_map, List.length_finRange]; simp only [List.length_cons] at hlenl; nlinarith)
            s1 hs1 Kl Kl' (fun a' s' hs' => ?_)
          · rcases List.mem_append.1 hm with hm1 | hm2
            · exact hnotl lf' (by simp [hlf']) c hm1
            · obtain ⟨c', -, heq⟩ := List.mem_map.1 hm2
              have : lf = lf' := congrArg (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len => pc.1.leaf) heq
              exact hndl.1 (this ▸ hlf')
          · have hsn_eq : sn1 ++ ls'.flatMap (fun lf => (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) =
                sn0 ++ (lf :: ls').flatMap (fun lf => (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) := by
              simp [sn1, List.flatMap_cons, List.append_assoc]
            rw [hsn_eq] at hs'
            exact hKl a' s' hs'
      -- Step `buildTreeM` = leaves + deterministic XMSS nodes (`type = 2 ≠ 0`)
      have hhead_l : buildTreeM pr (hybCollCall pr) (udChainStart pr γ) acc coord =
          (do
            let acc₁ ← (List.finRange (2 ^ vp.sl.params.hp)).foldlM
              (fun a lf => buildLeafM pr (hybCollCall pr) (udChainStart pr γ) a ⟨coord.layer, coord.tree, lf⟩) acc
            let tbl₂ ← (perfectInternalCoords vp.sl.params.hp).foldlM (fun tbl zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← hybCollCall pr .H a (lv, rv)
              return Function.update tbl a (some v)) acc₁.tbl
            return { acc₁ with tbl := tbl₂ }) := rfl
      have hhead_r : buildTreeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y))
          (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
          acc coord =
          (do
            let acc₁ ← (List.finRange (2 ^ vp.sl.params.hp)).foldlM
              (fun a lf => buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg))
                (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr γ' pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
                a ⟨coord.layer, coord.tree, lf⟩) acc
            let tbl₂ ← (perfectInternalCoords vp.sl.params.hp).foldlM (fun tbl zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← (pure (pr.memberEval .H pk a (lv, rv)) : ProbComp pr.Y)
              return Function.update tbl a (some v)) acc₁.tbl
            return { acc₁ with tbl := tbl₂ }) := rfl
      rw [hhead_l, hhead_r]
      simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
      have hlen_head : seen.length + (List.finRange (2 ^ vp.sl.params.hp)).length * vp.sl.params.len ≤ qWots vp := by
        rw [List.length_finRange]; change seen.length + 2 ^ vp.params.slParams.hp * vp.params.slParams.len ≤ qWots vp
        simp only [List.length_cons, Nat.add_mul, one_mul] at hlen; omega
      refine hlfs (List.finRange (2 ^ vp.sl.params.hp)) (List.nodup_finRange _) acc seen
        (fun lf _ c => hnot coord (by simp) lf c) hlen_head
        s hs _ _ (fun a1 s1 hs1 => ?_)
      -- XMSS internal nodes (`type = 2 ≠ 0`)
      have hxmss : ∀ (l : List (ℕ × ℕ)) (tbl : Adrs → Option pr.Y) (s' : List Adrs × List Adrs),
          ChainOracleInv (seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) s'.1 s'.2 →
          ∃ s'', ChainOracleInv (seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) s''.1 s''.2 ∧
            (simulateQ impl (l.foldlM (fun t zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← hybCollCall pr .H a (lv, rv)
              return Function.update t a (some v)) tbl)).run s' =
            pure (Id.run (l.foldlM (fun t zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← sfDetCall pr pk .H a (lv, rv)
              return Function.update t a (some v)) tbl), s'') := by
        intro l; induction l with
        | nil => intro tbl s' hs'; exact ⟨s', hs', by simp⟩
        | cons zi zis ihz =>
          intro tbl s' hs'
          have hnr : ¬ TweakReserved id s'.1 (xmssNodeAdrs coord.toAdrs zi.1 zi.2) := by
            rintro ⟨q, hq, heq⟩
            have ht0 := (hs'.1 q hq).1; dsimp only [id] at heq; rw [heq] at ht0
            simp [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode] at ht0
          have h1 : (simulateQ impl (hybCollCall pr .H (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
              ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
               (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default))).run s' =
              pure (pr.memberEval .H pk (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
                ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
                 (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default),
                (s'.1, s'.2 ++ [xmssNodeAdrs coord.toAdrs zi.1 zi.2])) := by
            unfold hybCollCall impl
            simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_UD_oracles, QueryImpl.add_apply_inr,
              StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
              pure_bind, hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
            rfl
          have hs'' : ChainOracleInv
              (seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
                (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c))
              s'.1 (s'.2 ++ [xmssNodeAdrs coord.toAdrs zi.1 zi.2]) := by
            refine ⟨hs'.1, fun t ht => ?_, hs'.2.2⟩
            rcases List.mem_append.1 ht with ht1 | ht2
            · exact hs'.2.1 t ht1
            · simp only [List.mem_singleton] at ht2; subst ht2
              left; simp [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode]
          obtain ⟨s''', hs''', hrest⟩ := ihz
            (Function.update tbl (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
              (some (pr.memberEval .H pk (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
                ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
                 (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default))))
            (s'.1, s'.2 ++ [xmssNodeAdrs coord.toAdrs zi.1 zi.2]) hs''
          refine ⟨s''', hs''', ?_⟩
          simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, h1, pure_bind,
            simulateQ_pure, StateT.run_pure, sfDetCall]
          exact hrest
      have hxmss_p : ∀ (l : List (ℕ × ℕ)) (tbl : Adrs → Option pr.Y),
          (l.foldlM (fun t zi => do
            let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
            let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
            let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
            let v ← (pure (pr.memberEval .H pk a (lv, rv)) : ProbComp pr.Y)
            return Function.update t a (some v)) tbl) =
          pure (Id.run (l.foldlM (fun t zi => do
            let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
            let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
            let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
            let v ← sfDetCall pr pk .H a (lv, rv)
            return Function.update t a (some v)) tbl)) := by
        intro l; induction l with
        | nil => intro _; rfl
        | cons zi zis ihz => intro tbl; simp only [List.foldlM_cons, pure_bind, sfDetCall]; exact ihz _
      obtain ⟨s2, hs2, hrun2⟩ := hxmss (perfectInternalCoords vp.sl.params.hp) a1.tbl s1 hs1
      rw [hxmss_p]
      simp only [hrun2, pure_bind, simulateQ_pure, StateT.run_pure]
      set sn1 := seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
        (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)
      refine iht hnd.2 _ sn1 (fun c' hc' lf ch hm => ?_) ?_ s2 hs2 K₁ K₁' (fun a' s' hs' => ?_)
      · rcases List.mem_append.1 hm with hm1 | hm2
        · exact hnot c' (by simp [hc']) lf ch hm1
        · simp only [List.mem_flatMap, List.mem_map] at hm2
          obtain ⟨lf', -, ch', -, heq⟩ := hm2
          have hceq : coord = c' := by
            cases coord; cases c'
            have hl := congrArg (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len => pc.1.layer) heq
            simp only at hl; subst hl
            have ht := congrArg (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len => pc.1.tree.val) heq
            simp only at ht
            exact congrArg _ (Fin.ext ht)
          exact hnd.1 (hceq ▸ hc')
      · have hlen_sn1 : sn1.length = seen.length + 2 ^ vp.sl.params.hp * vp.sl.params.len := by
          simp [sn1, List.length_flatMap]
        rw [hlen_sn1]; simp only [List.length_cons] at hlen; nlinarith
      · have hsn_eq : sn1 ++ coords.flatMap (fun c' => (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun ch => (⟨c'.layer, c'.tree, lf⟩, ch)) =
          seen ++ (coord :: coords).flatMap (fun c' => (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun ch => (⟨c'.layer, c'.tree, lf⟩, ch)) := by
          simp [sn1, List.flatMap_cons, List.append_assoc]
        rw [hsn_eq] at hs'
        exact hK a' s' hs'
  -- Assemble FORS + `allXmssTrees`
  obtain ⟨tws₁, htws₁, hfors_run⟩ := hfors
  have hfors_prob : ((forsAddresses vp).foldlM (fun tbl a => do
      let v ← evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) u tbl a
      return Function.update tbl a (some v)) (fun _ => none)) =
    pure (Id.run ((forsAddresses vp).foldlM (fun tbl a => do
      let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
      return Function.update tbl a (some v)) (fun _ => none))) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
        (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) u tbl a
          return Function.update tbl a (some v)) tbl) =
        pure (Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
          return Function.update tbl a (some v)) tbl)) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons a as ih =>
        intro tbl
        have hev : evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) u tbl a =
            pure (Id.run (evalNodeM pr (sfDetCall pr pk) u tbl a)) := by
          rw [evalNodeM_eq_of_input, evalNodeM_eq_of_input]
          cases evalNodeInput pr u tbl a <;> rfl
        simp only [List.foldlM_cons, hev, pure_bind, Id.run_bind, Id.run_pure]
        exact ih _
    exact haux _ _
  unfold udBuildM hybTreeProb buildHybTreeM
  simp only [simulateQ_bind, StateT.run_bind, hfors_run, hfors_prob, bind_assoc, pure_bind,
    simulateQ_pure, StateT.run_pure]
  have hlen_all : 0 + (allXmssTreesList vp).length * (2 ^ vp.sl.params.hp * vp.sl.params.len) ≤ qWots vp := by
    rw [Nat.zero_add, allXmssTreesList_length, ← Nat.mul_assoc]
    have hw : xmssTreeCount vp.sl.params * 2 ^ vp.sl.params.hp = wotsInstanceCount vp.sl.params := by
      unfold wotsInstanceCount xmssTreeCount; exact Finset.sum_mul _ _ _
    rw [hw]; exact le_rfl
  exact htrees_step (allXmssTreesList vp) (allXmssTreesList_nodup vp) _ []
    (fun _ _ _ _ h => by simp at h) hlen_all ([], tws₁)
    ⟨fun _ h => by simp at h, fun t ht => Or.inl (htws₁ t ht), by simp⟩
    (fun z => K ⟨(z.1.tbl (topRootAdrs vp)).getD default, z.1.tbl, z.1.wotsMsg, z.1.wotsSig⟩)
    (fun a => K ⟨(a.tbl (topRootAdrs vp)).getD default, a.tbl, a.wotsMsg, a.wotsSig⟩)
    (fun _ _ _ => rfl)

/-- **The `SM-UD` reduction `B_ud γ`** (against `F ∈ Th_λ`, `q₂ = wotsInstanceCount * len` targets):
samples setup `d` and `u` (for FORS), runs optional stateful Stage-1 precomp `sfStage.sfRun` via
`O_coll`, builds `hyb ← udBuildM pr γ u`, and in Stage 2 runs `stage2` and outputs `isHybWotsPre`. -/
noncomputable def B_ud {D E : Type} (sfStage : SfStage1 pr D E)
    (stage2 : D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr)))
    (γ : ℕ) : SM_DT_UD_Adversary (probUD pr (qWots vp)) where
  State := D × E × (SlSecAdrs vp → pr.Y) × HybTree pr
  pick := do
    let d ← (liftM sfStage.g₁ : OracleComp (FSpec pr) D)
    let u ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y)) : OracleComp (FSpec pr) _)
    let sf ← sfStage.sfRun (hybCollCall pr) d
    let hyb ← udBuildM pr γ u
    return (d, sf, u, hyb)
  distinguish st pk := do
    let o ← stage2 st.1 st.2.1 pk st.2.2.1 st.2.2.2
    return isHybWotsPre pr pk st.2.2.2 o

/-- Probabilistic hybrid `γ` experiment outputting `isHybWotsPre`. -/
noncomputable def hybProbExp {D E : Type} (sfStage : SfStage1 pr D E)
    (stage2 : D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr)))
    (γ : ℕ) : ProbComp Bool := do
  let pk ← $ᵗ pr.PkSeed
  let d ← sfStage.g₁
  let u ← $ᵗ (SlSecAdrs vp → pr.Y)
  let hyb ← hybTreeProb pr γ pk u
  let o ← stage2 d (sfStage.sfDet d pk) pk u hyb
  return isHybWotsPre pr pk hyb o

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Real world of `B_ud γ` is `hybProbExp γ`; ideal world is `hybProbExp (γ + 1)`.** -/
theorem B_ud_exp {D E : Type} (sfStage : SfStage1 pr D E)
    (stage2 : D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr)))
    (w : SM_DT_UD_World) (γ : ℕ) :
    SM_DT_UD_Experiment w (B_ud pr sfStage stage2 γ) =ᵈ
      hybProbExp pr sfStage stage2 (if w = .real then γ else γ + 1) := by
  unfold SM_DT_UD_Experiment hybProbExp
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B_ud]
  rw [show SM_DT_UD_oracles w (probUD pr (qWots vp)) pk =
      Fxmss.unifFwd _ + (SM_DT_UD_challengeOracle w (probUD pr (qWots vp)) pk +
        collectionOracle id (probUD pr (qWots vp)).thColl pk) from rfl]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_right _ fun u => ?_
  rw [← show SM_DT_UD_oracles w (probUD pr (qWots vp)) pk =
      Fxmss.unifFwd _ + (SM_DT_UD_challengeOracle w (probUD pr (qWots vp)) pk +
        collectionOracle id (probUD pr (qWots vp)).thColl pk) from rfl]
  obtain ⟨⟨qs₀, tws₀⟩, ⟨hqs₀, htws₀⟩, hsf⟩ := sfStage.sfRun_spec
    (SM_DT_UD_oracles w (probUD pr (qWots vp)) pk) (hybCollCall pr) pk
    (fun s => s.1 = [] ∧ ∀ t ∈ s.2, Scheme.IsStateful t)
    (fun s a => (s.1, s.2 ++ [a]))
    (fun i a msg s hsf ⟨hqs, _⟩ => by
      rcases s with ⟨qs, tws⟩; dsimp only at hqs; subst hqs
      unfold hybCollCall
      simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_UD_oracles, QueryImpl.add_apply_inr,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
        pure_bind, TweakReserved, List.not_mem_nil, false_and, exists_false,
        ↓reduceIte, StateT.run_set, Option.getD_some]
      rfl)
    (fun s a ⟨hqs, htws⟩ hsf => ⟨hqs, fun t ht => by
      rcases List.mem_append.1 ht with ht1 | ht2
      · exact htws t ht1
      · simp only [List.mem_singleton] at ht2; subst ht2; exact hsf⟩)
    d hd ([], []) ⟨rfl, fun _ h => by simp at h⟩
  dsimp only at hqs₀; subst hqs₀
  simp only [simulateQ_bind, StateT.run_bind, hsf, pure_bind, bind_assoc, simulateQ_pure, StateT.run_pure]
  rw [simulateQ_udBuildM_eval pr w γ pk u tws₀ htws₀
    (fun hyb => do let o ← stage2 d (sfStage.sfDet d pk) pk u hyb; return isHybWotsPre pr pk hyb o)]

/-- Extraction of `SM-PRE` answer from Stage-2 output `o` and Stage-1 `savedT`. -/
noncomputable def extractPre (pk : pr.PkSeed) (hyb : HybTree pr) (savedT : List Adrs)
    (o : Option (List Byte × Stateless.Sig pr)) : ℕ × pr.Y :=
  match o with
  | some (msg, sig) =>
    match findHybWotsPre pr pk hyb msg sig with
    | some ((pos, c), step, val) =>
      (savedT.idxOf ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step), val)
    | none => (0, default)
  | none => (0, default)

/-- **The `SM-PRE` reduction `B_pre`** (against `F ∈ Th_λ`, `q₂ = wotsInstanceCount * len` targets):
samples setup `d` and `u` (for FORS), runs optional stateful Stage-1 precomp `sfStage.sfRun`,
builds `(hyb, savedT) ← preBuildM pr u`, and in Stage 2 runs `stage2` and extracts the preimage
at the exact target index in `savedT`. -/
noncomputable def B_pre {D E : Type} (sfStage : SfStage1 pr D E)
    (stage2 : D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr))) :
    SM_DT_PRE_Adversary (probPre pr (qWots vp)) where
  State := D × E × (SlSecAdrs vp → pr.Y) × HybTree pr × List Adrs
  choose := do
    let d ← (liftM sfStage.g₁ : OracleComp (FSpec pr) D)
    let u ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y)) : OracleComp (FSpec pr) _)
    let sf ← sfStage.sfRun (hybCollCall pr) d
    let (hyb, savedT) ← preBuildM pr u
    return (d, sf, u, hyb, savedT)
  invert st pk := do
    let o ← stage2 st.1 st.2.1 pk st.2.2.1 st.2.2.2.1
    return extractPre pr pk st.2.2.2.1 st.2.2.2.2 o

/-- Invariant tracked during `preBuildM`: freshness invariant + `savedT = qs.map Prod.fst` +
`Nodup` + WOTS pk consistency + every processed chain `(pos, c)` with `b > 0` has its `(a, x)`
recorded in `qs` with `pr.F pk a x = (acc.wotsSig pos)[c.val]`. -/
def PreBuildInv (pk : pr.PkSeed) (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
    (donePos : List (LayerPosition vp.sl))
    (acc : HybAcc pr) (savedT : List Adrs) (s : List (Adrs × pr.Y) × List Adrs) : Prop :=
  ChainOracleInv seen (s.1.map Prod.fst) s.2 ∧
  savedT = s.1.map Prod.fst ∧
  savedT.Nodup ∧
  (∀ pos ∈ donePos,
    (acc.tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default =
      SLHDSA.wotsPkFromSig (prEager pr) (acc.wotsSig pos) (acc.wotsMsg pos) pk (wotsInstanceAdrs pos) ∧
    ∀ c : Fin vp.sl.params.len,
      let b := chainStepsCore pr.toSLHDSA.core (acc.wotsMsg pos) c.val
      0 < b → ∃ x, ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (b - 1), x) ∈ s.1 ∧
        pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (b - 1)) x =
          (acc.wotsSig pos)[c.val])

private theorem coord_eq_of_pos_eq {vp : ValidatedParams} {c₁ c₂ : LayerTreeCoord vp.sl}
    {lf₁ lf₂ : Fin (2 ^ vp.sl.params.hp)}
    (heq : (⟨c₁.layer, c₁.tree, lf₁⟩ : LayerPosition vp.sl) = ⟨c₂.layer, c₂.tree, lf₂⟩) :
    c₁ = c₂ := by
  cases c₁; cases c₂
  have hl := congrArg LayerPosition.layer heq; simp only at hl; subst hl
  have ht := congrArg (fun p : LayerPosition vp.sl => p.tree.val) heq
  simp only at ht
  exact congrArg _ (Fin.ext ht)

omit [Fintype pr.Y] [DecidableEq pr.Y] [DecidableEq pr.PkSeed] in
/-- **Pointwise probability domination for `preBuildM`**: for any `Bool`-valued Stage-2
continuations `K₁` (with `SM-PRE` oracle state) and `K₁'` (in `Hyb(w - 2)`) where `K₁` dominates
`K₁'` whenever `PreBuildInv` holds on all positions, `preBuildM` dominates `hybTreeProb (w - 2)`. -/
theorem simulateQ_preBuildM_le (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tws₀ : List Adrs) (htws₀ : ∀ t ∈ tws₀, Scheme.IsStateful t)
    (K₁ : (HybTree pr × List Adrs) × (List (Adrs × pr.Y) × List Adrs) → ProbComp Bool)
    (K₁' : HybTree pr → ProbComp Bool)
    (hdom : ∀ hyb savedT s',
      savedT = s'.1.map Prod.fst → savedT.Nodup → HybWotsConsistent pr pk hyb →
      (∀ pos : LayerPosition vp.sl, ∀ c : Fin vp.sl.params.len,
        let b := chainStepsCore pr.toSLHDSA.core (hyb.wotsMsg pos) c.val
        0 < b → ∃ x, ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (b - 1), x) ∈ s'.1 ∧
          pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (b - 1)) x =
            (hyb.wotsSig pos)[c.val]) →
      𝒟[K₁' hyb] {true} ≤ 𝒟[K₁ ((hyb, savedT), s')] {true}) :
    𝒟[hybTreeProb pr (vp.params.w - 2) pk u >>= K₁'] {true} ≤
      𝒟[(simulateQ (SM_DT_PRE_oracles (probPre pr (qWots vp)) pk) (preBuildM pr u)).run ([], tws₀) >>= K₁] {true} := by
  set impl := SM_DT_PRE_oracles (probPre pr (qWots vp)) pk
  -- Helper: monotonicity of `𝒟[m >>= f] {true}`
  have hbind_le : ∀ {α : Type} (m : ProbComp α) (f g : α → ProbComp Bool),
      (∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) →
      𝒟[m >>= f] {true} ≤ 𝒟[m >>= g] {true} := fun m f g hfg =>
    evalDist_bind_apply_mono_of_support m f g (measurableSet_singleton true) (fun a _ => hfg a)
  -- Step 1: FORS pass (deterministic, `qs = []`, `savedT = []`)
  have hfors : ∃ tws₁, (∀ t ∈ tws₁, t.type ≠ 0) ∧
      (simulateQ impl ((((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (fun i a msg => liftM (hybCollCall pr i a msg)) u tbl a
        return Function.update tbl a (some v)) (fun _ => none) :
        StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (Adrs → Option pr.Y)).run []))).run ([], tws₀) =
      pure ((Id.run ((forsAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
        return Function.update tbl a (some v)) (fun _ => none)), []), ([], tws₁)) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y) (tws : List Adrs),
        (∀ a ∈ l, a.type = 3 ∨ a.type = 4) →
        (∀ t ∈ tws, t.type ≠ 0) →
        ∃ tws', (∀ t ∈ tws', t.type ≠ 0) ∧
          (simulateQ impl (((l.foldlM (fun tbl a => do
            let v ← evalNodeM pr (fun i a msg => liftM (hybCollCall pr i a msg)) u tbl a
            return Function.update tbl a (some v)) tbl :
            StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (Adrs → Option pr.Y)).run []))).run ([], tws) =
          pure ((Id.run (l.foldlM (fun tbl a => do
            let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
            return Function.update tbl a (some v)) tbl), []), ([], tws')) := by
      intro l; induction l with
      | nil => intro tbl tws _ htws; exact ⟨tws, htws, by simp⟩
      | cons a as ih =>
        intro tbl tws hty htws
        have ha_ty : a.type = 3 ∨ a.type = 4 := hty a (by simp)
        have ha_ne0 : a.type ≠ 0 := by rcases ha_ty with h | h <;> omega
        have ha_val : ValidNodeAdrs a := ⟨by rcases ha_ty with h | h <;> omega, fun h => by omega⟩
        obtain ⟨⟨i, msg⟩, hinp⟩ := Option.isSome_iff_exists.1 (evalNodeInput_isSome_of_valid pr u tbl ha_val)
        have h1 : (simulateQ impl ((evalNodeM pr (fun i a msg => liftM (hybCollCall pr i a msg)) u tbl a :
              StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y).run [])).run ([], tws) =
            pure ((Id.run (evalNodeM pr (sfDetCall pr pk) u tbl a), []), ([], tws ++ [a])) := by
          rw [evalNodeM_eq_of_input, evalNodeM_eq_of_input, hinp]
          change (simulateQ impl ((StateT.lift (hybCollCall pr i a msg)).run [])).run ([], tws) =
            pure ((Id.run (sfDetCall pr pk i a msg), []), ([], tws ++ [a]))
          rw [StateT.run_lift]
          simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
          unfold hybCollCall impl sfDetCall
          simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_PRE_oracles, QueryImpl.add_apply_inr,
            StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
            pure_bind, TweakReserved, List.not_mem_nil, false_and, exists_false,
            ↓reduceIte, StateT.run_set, Option.getD_some, Id.run_pure]
          rfl
        have htws1 : ∀ t ∈ tws ++ [a], t.type ≠ 0 := by
          intro t ht; rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2; exact ha_ne0
        obtain ⟨tws', htws', hrest⟩ := ih _ (tws ++ [a]) (fun b hb => hty b (by simp [hb])) htws1
        refine ⟨tws', htws', ?_⟩
        simp only [List.foldlM_cons, StateT.run_bind, simulateQ_bind, h1, pure_bind,
          StateT.run_pure, simulateQ_pure, Id.run_bind, Id.run_pure]
        exact hrest
    exact haux _ _ tws₀ (fun a ha => type_of_mem_forsAddresses ha) (fun t ht h0 => by
      obtain ⟨st, hst⟩ := htws₀ t ht; have := st.sixteen_le_toCode; omega)
  -- Helper: `slChainM` through `liftM (hybCollCall pr ...)` leaves `savedT` unchanged
  have hchain_lift : ∀ chAdrs x start steps (savedT : List Adrs),
      (slChainM pr (fun i a msg => liftM (hybCollCall pr i a msg)) chAdrs x start steps :
          StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y).run savedT =
        (fun y => (y, savedT)) <$> slChainM pr (hybCollCall pr) chAdrs x start steps := by
    intro chAdrs x start steps savedT; induction steps with
    | zero => simp [slChainM]
    | succ steps ih =>
      simp only [slChainM, StateT.run_bind, ih, map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun y => ?_
      simp [liftM, monadLift, MonadLift.monadLift, map_eq_bind_pure_comp]
  -- Helper: single chain step `(pos, c)` for `preChainStart` + remaining chain
  have hchain_step : ∀ (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (b : ℕ)
      (hbw : b ≤ vp.sl.params.w - 1)
      (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
      (hnot : (pos, c) ∉ seen) (hlen : seen.length < qWots vp)
      (savedT : List Adrs) (s : List (Adrs × pr.Y) × List Adrs),
      ChainOracleInv seen (s.1.map Prod.fst) s.2 →
      savedT = s.1.map Prod.fst →
      savedT.Nodup →
      ∀ (Kc : ((pr.Y × pr.Y) × List Adrs) × (List (Adrs × pr.Y) × List Adrs) → ProbComp Bool)
        (Kc' : pr.Y × pr.Y → ProbComp Bool),
      (∀ pair savedT' s',
        ChainOracleInv (seen ++ [(pos, c)]) (s'.1.map Prod.fst) s'.2 →
        savedT' = s'.1.map Prod.fst →
        savedT'.Nodup →
        (∀ e ∈ s.1, e ∈ s'.1) →
        pair.2 = slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) pair.1 b
          (vp.sl.params.w - 1 - b) →
        (0 < b → ∃ x, ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (b - 1), x) ∈ s'.1 ∧
          pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (b - 1)) x = pair.1) →
        𝒟[Kc' pair] {true} ≤ 𝒟[Kc ((pair, savedT'), s')] {true}) →
      𝒟[(do
        let x ← $ᵗ pr.Y
        let sigBlk := hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x
        let top := slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)) >>= Kc'] {true} ≤
      𝒟[(simulateQ impl ((do
        let sigBlk ← preChainStart pr pos c b
        let top ← slChainM pr (fun i a msg => liftM (hybCollCall pr i a msg))
          (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)).run savedT)).run s >>= Kc] {true} := by
    intro pos c b hbw seen hnot hlen savedT s hs hst hnd Kc Kc' hKc
    set chAdrs := wotsChainAdrs (wotsInstanceAdrs pos) c.val
    have hnot_q : ∀ q ∈ s.1.map Prod.fst, chainKey q ≠ pcKey (pos, c) := by
      intro q hq heq
      obtain ⟨_, pc, hpc, hk⟩ := hs.1 q hq
      exact hnot (pcKey_injective (hk.symm.trans heq) ▸ hpc)
    have hnot_t : ∀ t ∈ s.2, t.type = 0 → chainKey t ≠ pcKey (pos, c) := by
      intro t ht ht0 heq
      rcases hs.2.1 t ht with hne0 | ⟨pc, hpc, hk⟩
      · exact hne0 ht0
      · exact hnot (pcKey_injective (hk.symm.trans heq) ▸ hpc)
    have hcoll_step : ∀ (qs₁ : List (Adrs × pr.Y)) (tws₁ : List Adrs) (k : ℕ) (v : pr.Y),
        (∀ q ∈ qs₁, q.1 ≠ chAdrs.setHashAddress k) →
        (simulateQ impl (hybCollCall pr .F (chAdrs.setHashAddress k) v)).run (qs₁, tws₁) =
          pure (pr.F pk (chAdrs.setHashAddress k) v, (qs₁, tws₁ ++ [chAdrs.setHashAddress k])) := by
      intro qs₁ tws₁ k v hne
      have hnr : ¬ TweakReserved Prod.fst qs₁ (chAdrs.setHashAddress k) := fun ⟨e, he, heq⟩ => hne e he heq
      unfold hybCollCall impl
      simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_PRE_oracles, QueryImpl.add_apply_inr,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
        pure_bind, hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
      rfl
    unfold preChainStart
    dsimp only
    split_ifs with hb0
    · -- `0 < b`: query `SM-PRE` challenge oracle at `chAdrs.setHashAddress (b - 1)`
      set ab := chAdrs.setHashAddress (b - 1)
      have hfr : TweakFresh Prod.fst s.1 s.2 ab := by
        constructor
        · rintro ⟨e, he, heq⟩
          exact hnot_q e.1 (List.mem_map.2 ⟨e, he, rfl⟩) (by rw [heq, chainKey_wotsChainAdrs])
        · intro hmem
          exact hnot_t ab hmem (type_wotsChainAdrs pos c (b - 1)) (chainKey_wotsChainAdrs pos c (b - 1))
      have hcap : ¬ qWots vp ≤ s.1.length := by have := hs.2.2; simp at this; omega
      have hchal : (simulateQ impl (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl ab))) :
          OracleComp (Fxmss.Rom.Hyb.FSpec pr) (Option pr.Y))).run s =
          (do let x ← $ᵗ pr.Y
              return (some (pr.F pk ab x), (s.1 ++ [(ab, x)], s.2))) := by
        unfold impl
        simp only [simulateQ_spec_query, SM_DT_PRE_oracles, QueryImpl.add_apply_inr,
          QueryImpl.add_apply_inl, SM_DT_PRE_challengeOracle, StateT.run_bind, StateT.run_get,
          pure_bind, hfr, hcap, not_true_eq_false, or_self, ↓reduceIte, StateT.run_monadLift,
          StateT.run_set, StateT.run_pure, bind_assoc]
        simp [Fxmss.Rom.thF, TweakableHash.ofFun]
      have hpre_l : ((do
          let a := chAdrs.setHashAddress (b - 1)
          let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl a))) :
            StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (Option pr.Y))
          modify (· ++ [a])
          let sigBlk := r.getD default
          let top ← slChainM pr (fun i a msg => liftM (hybCollCall pr i a msg))
            chAdrs sigBlk b (vp.sl.params.w - 1 - b)
          return (sigBlk, top)) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (pr.Y × pr.Y)).run savedT =
          (do
            let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl ab))) :
              OracleComp (Fxmss.Rom.Hyb.FSpec pr) (Option pr.Y))
            let top ← slChainM pr (hybCollCall pr) chAdrs (r.getD default) b (vp.sl.params.w - 1 - b)
            return ((r.getD default, top), savedT ++ [ab])) := by
        simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_modify,
          StateT.run_pure, hchain_lift, map_eq_bind_pure_comp, bind_assoc, pure_bind, ab]
        rfl
      rw [show ((do
          let sigBlk ← (do
            let a := chAdrs.setHashAddress (b - 1)
            let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl a))) :
              StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (Option pr.Y))
            modify (· ++ [a])
            return r.getD default)
          let top ← slChainM pr (fun i a msg => liftM (hybCollCall pr i a msg))
            chAdrs sigBlk b (vp.sl.params.w - 1 - b)
          return (sigBlk, top)) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (pr.Y × pr.Y)).run savedT =
        (do
          let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inl ab))) :
            OracleComp (Fxmss.Rom.Hyb.FSpec pr) (Option pr.Y))
          let top ← slChainM pr (hybCollCall pr) chAdrs (r.getD default) b (vp.sl.params.w - 1 - b)
          return ((r.getD default, top), savedT ++ [ab])) from by simpa [bind_assoc, pure_bind] using hpre_l]
      simp only [simulateQ_bind, StateT.run_bind, hchal, bind_assoc, pure_bind, Option.getD_some]
      refine hbind_le ($ᵗ pr.Y) _ _ fun x => ?_
      have hne_gt : ∀ k, b ≤ k → ∀ e ∈ s.1 ++ [(ab, x)], e.1 ≠ chAdrs.setHashAddress k := by
        intro k hk e he heq
        rcases List.mem_append.1 he with he1 | he2
        · exact hnot_q e.1 (List.mem_map.2 ⟨e, he1, rfl⟩) (by rw [heq, chainKey_wotsChainAdrs])
        · simp only [List.mem_singleton] at he2; subst he2
          have := congrArg Adrs.word3 heq
          simp only [ab, chAdrs, word3_wotsChainAdrs] at this; omega
      obtain ⟨s₂, hs₂, hrun₂⟩ := simulateQ_slChainM_run pr impl pk
        (fun st => st.1 = s.1 ++ [(ab, x)] ∧
          ∀ t ∈ st.2, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc)
        (fun st a => (st.1, st.2 ++ [a])) chAdrs (x := pr.F pk ab x) b
        (fun k st hk ⟨hqeq, _⟩ => by
          rcases st with ⟨qs₁, tws₁⟩; dsimp only at hqeq; subst hqeq
          exact hcoll_step _ tws₁ k _ (hne_gt k hk))
        (fun k st _ ⟨hqeq, htws₁⟩ => ⟨hqeq, fun t ht => by
          rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws₁ t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2
            exact Or.inr ⟨(pos, c), List.mem_append_right _ (by simp), chainKey_wotsChainAdrs pos c k⟩⟩)
        (vp.sl.params.w - 1 - b) (s.1 ++ [(ab, x)], s.2)
        ⟨rfl, fun t ht => (hs.2.1 t ht).imp_right fun ⟨pc, hpc, hk⟩ => ⟨pc, List.mem_append_left _ hpc, hk⟩⟩
      rw [hrun₂, pure_bind]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      have hinv2 : ChainOracleInv (seen ++ [(pos, c)]) (s₂.1.map Prod.fst) s₂.2 := by
        rw [hs₂.1]
        refine ⟨fun q hq => ?_, hs₂.2, by simp; have := hs.2.2; simp at this; omega⟩
        simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hq
        rcases hq with hq1 | rfl
        · obtain ⟨ht0, pc, hpc, hk⟩ := hs.1 q hq1
          exact ⟨ht0, pc, List.mem_append_left _ hpc, hk⟩
        · exact ⟨type_wotsChainAdrs pos c (b - 1), (pos, c), List.mem_append_right _ (by simp),
            chainKey_wotsChainAdrs pos c (b - 1)⟩
      have hst2 : savedT ++ [ab] = s₂.1.map Prod.fst := by rw [hs₂.1, hst]; simp
      have hnd2 : (savedT ++ [ab]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton ab, fun a ha b' hb' heq => ?_⟩
        simp only [List.mem_singleton] at hb'; subst hb'; subst heq
        rw [hst] at ha
        exact hnot_q ab ha (chainKey_wotsChainAdrs pos c (b - 1))
      rw [hybBlockVal_top pr pk chAdrs hb0 hbw x]
      exact hKc _ _ s₂ hinv2 hst2 hnd2 (fun e he => by rw [hs₂.1]; exact List.mem_append_left _ he)
        rfl (fun _ => ⟨x, by rw [hs₂.1]; exact List.mem_append_right _ (by simp), rfl⟩)
    · -- `b = 0`: sample `x ← $ᵗ pr.Y` via `unifSpec`, run `slChainM` via `O_coll`
      have hb_eq : b = 0 := by omega
      subst hb_eq
      have hunif : (simulateQ impl (liftM ($ᵗ pr.Y) : OracleComp (Fxmss.Rom.Hyb.FSpec pr) pr.Y)).run s =
          (fun x => (x, s)) <$> ($ᵗ pr.Y) := by
        unfold impl; exact Fxmss.simulateQ_add_liftM_run _ ($ᵗ pr.Y) s
      have hpre_0 : ((do
          let sigBlk ← (liftM ($ᵗ pr.Y) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y)
          let top ← slChainM pr (fun i a msg => liftM (hybCollCall pr i a msg))
            chAdrs sigBlk 0 (vp.sl.params.w - 1 - 0)
          return (sigBlk, top)) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) (pr.Y × pr.Y)).run savedT =
          (do
            let x ← (liftM ($ᵗ pr.Y) : OracleComp (Fxmss.Rom.Hyb.FSpec pr) pr.Y)
            let top ← slChainM pr (hybCollCall pr) chAdrs x 0 (vp.sl.params.w - 1 - 0)
            return ((x, top), savedT)) := by
        simp only [StateT.run_bind, liftM, monadLift, MonadLift.monadLift,
          StateT.run_mk, StateT.run_lift, StateT.run_pure, OracleComp.liftComp_bind,
          OracleComp.liftComp_pure, bind_assoc, pure_bind]
        refine bind_congr fun x => ?_
        rw [show (fun i a msg => StateT.lift (hybCollCall pr i a msg)) =
            (fun i a msg => (liftM (hybCollCall pr i a msg) :
              StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y)) from rfl,
          hchain_lift]
        simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
      rw [hpre_0]
      simp only [simulateQ_bind, StateT.run_bind, hunif, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine hbind_le ($ᵗ pr.Y) _ _ fun x => ?_
      have hne_all : ∀ k, ∀ e ∈ s.1, e.1 ≠ chAdrs.setHashAddress k := fun k e he heq =>
        hnot_q e.1 (List.mem_map.2 ⟨e, he, rfl⟩) (by rw [heq, chainKey_wotsChainAdrs])
      obtain ⟨s₂, hs₂, hrun₂⟩ := simulateQ_slChainM_run pr impl pk
        (fun st => st.1 = s.1 ∧
          ∀ t ∈ st.2, t.type ≠ 0 ∨ ∃ pc ∈ seen ++ [(pos, c)], chainKey t = pcKey pc)
        (fun st a => (st.1, st.2 ++ [a])) chAdrs (x := x) 0
        (fun k st _ ⟨hqeq, _⟩ => by
          rcases st with ⟨qs₁, tws₁⟩; dsimp only at hqeq; subst hqeq
          exact hcoll_step _ tws₁ k _ (hne_all k))
        (fun k st _ ⟨hqeq, htws₁⟩ => ⟨hqeq, fun t ht => by
          rcases List.mem_append.1 ht with ht1 | ht2
          · exact htws₁ t ht1
          · simp only [List.mem_singleton] at ht2; subst ht2
            exact Or.inr ⟨(pos, c), List.mem_append_right _ (by simp), chainKey_wotsChainAdrs pos c k⟩⟩)
        (vp.sl.params.w - 1 - 0) s
        ⟨rfl, fun t ht => (hs.2.1 t ht).imp_right fun ⟨pc, hpc, hk⟩ => ⟨pc, List.mem_append_left _ hpc, hk⟩⟩
      dsimp only [Function.comp_def]
      rw [pure_bind, hrun₂, pure_bind]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, hybBlockVal_b_zero]
      have hinv2 : ChainOracleInv (seen ++ [(pos, c)]) (s₂.1.map Prod.fst) s₂.2 := by
        rw [hs₂.1]
        refine ⟨fun q hq => ?_, hs₂.2, by simp; have := hs.2.2; simp at this; omega⟩
        obtain ⟨ht0, pc, hpc, hk⟩ := hs.1 q hq
        exact ⟨ht0, pc, List.mem_append_left _ hpc, hk⟩
      exact hKc _ _ s₂ hinv2 (by rw [hs₂.1]; exact hst) hnd (fun e he => by rw [hs₂.1]; exact he)
        rfl (fun h => by omega)
  -- Helper: single leaf step `buildLeafM` for `preBuildM`
  have hleaf_step : ∀ (pos : LayerPosition vp.sl) (acc : HybAcc pr)
      (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
      (donePos : List (LayerPosition vp.sl))
      (hnot : ∀ c : Fin vp.sl.params.len, (pos, c) ∉ seen)
      (hnotP : pos ∉ donePos)
      (hlen : seen.length + vp.sl.params.len ≤ qWots vp)
      (savedT : List Adrs) (s : List (Adrs × pr.Y) × List Adrs),
      PreBuildInv pr pk seen donePos acc savedT s →
      ∀ (Kl : (HybAcc pr × List Adrs) × (List (Adrs × pr.Y) × List Adrs) → ProbComp Bool)
        (Kl' : HybAcc pr → ProbComp Bool),
      (∀ acc' savedT' s',
        PreBuildInv pr pk (seen ++ (List.finRange vp.sl.params.len).map (pos, ·)) (donePos ++ [pos])
          acc' savedT' s' →
        𝒟[Kl' acc'] {true} ≤ 𝒟[Kl ((acc', savedT'), s')] {true}) →
      𝒟[buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg))
        (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
        acc pos >>= Kl'] {true} ≤
      𝒟[(simulateQ impl ((buildLeafM pr (fun i a msg => liftM (hybCollCall pr i a msg))
        (preChainStart pr) acc pos).run savedT)).run s >>= Kl] {true} := by
    intro pos acc seen donePos hnot hnotP hlen savedT s hinv Kl Kl' hKl
    set msg := wotsMsgFromTbl pr acc.tbl pos
    -- `Vector.ofFnM` over chains `0 .. n-1`
    have hvec : ∀ (n : ℕ) (hn : n ≤ vp.sl.params.len)
        (savedT₀ : List Adrs) (s₀ : List (Adrs × pr.Y) × List Adrs),
        ChainOracleInv seen (s₀.1.map Prod.fst) s₀.2 →
        savedT₀ = s₀.1.map Prod.fst → savedT₀.Nodup →
        ∀ (Kv : (Vector (pr.Y × pr.Y) n × List Adrs) × (List (Adrs × pr.Y) × List Adrs) → ProbComp Bool)
          (Kv' : Vector (pr.Y × pr.Y) n → ProbComp Bool),
        (∀ v savedT' s',
          ChainOracleInv (seen ++ (List.finRange n).map fun j => (pos, ⟨j.val, by omega⟩)) (s'.1.map Prod.fst) s'.2 →
          savedT' = s'.1.map Prod.fst → savedT'.Nodup →
          (∀ e ∈ s₀.1, e ∈ s'.1) →
          (∀ (j : Fin n),
            let b := chainStepsCore pr.toSLHDSA.core msg j.val
            v[j.val].2 = slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) v[j.val].1 b (vp.sl.params.w - 1 - b) ∧
            (0 < b → ∃ x, ((wotsChainAdrs (wotsInstanceAdrs pos) j.val).setHashAddress (b - 1), x) ∈ s'.1 ∧
              pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) j.val).setHashAddress (b - 1)) x = v[j.val].1)) →
          𝒟[Kv' v] {true} ≤ 𝒟[Kv ((v, savedT'), s')] {true}) →
        𝒟[(Vector.ofFnM fun j : Fin n => do
          let b := chainStepsCore pr.toSLHDSA.core msg j.val
          let x ← $ᵗ pr.Y
          let sigBlk := hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) b x
          let top := slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) sigBlk b (vp.sl.params.w - 1 - b)
          return (sigBlk, top)) >>= Kv'] {true} ≤
        𝒟[(simulateQ impl ((Vector.ofFnM fun j : Fin n => do
          let b := chainStepsCore pr.toSLHDSA.core msg j.val
          let sigBlk ← preChainStart pr pos ⟨j.val, by omega⟩ b
          let top ← slChainM pr (fun i a msg => liftM (hybCollCall pr i a msg))
            (wotsChainAdrs (wotsInstanceAdrs pos) j.val) sigBlk b (vp.sl.params.w - 1 - b)
          return (sigBlk, top)).run savedT₀)).run s₀ >>= Kv] {true} := by
      intro n; induction n with
      | zero =>
        intro _ savedT₀ s₀ hs₀ hst₀ hnd₀ Kv Kv' hKv
        simp only [Vector.ofFnM_zero, StateT.run_pure, simulateQ_pure, pure_bind]
        exact hKv #v[] savedT₀ s₀ (by simpa using hs₀) hst₀ hnd₀ (fun _ h => h) (fun j => j.elim0)
      | succ n ihn =>
        intro hn savedT₀ s₀ hs₀ hst₀ hnd₀ Kv Kv' hKv
        rw [Vector.ofFnM_succ, Vector.ofFnM_succ, bind_assoc, StateT.run_bind, simulateQ_bind,
          StateT.run_bind, bind_assoc]
        refine ihn (by omega) savedT₀ s₀ hs₀ hst₀ hnd₀ _ _ (fun v savedT₁ s₁ hs₁ hst₁ hnd₁ hsub₁ hv₁ => ?_)
        rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_assoc]
        simp only [Fin.val_last, StateT.run_pure, simulateQ_pure, pure_bind]
        set seen₁ := seen ++ (List.finRange n).map fun j => (pos, ⟨j.val, by omega⟩)
        have hnot1 : (pos, ⟨n, hn⟩) ∉ seen₁ := by
          intro hm; rcases List.mem_append.1 hm with hm1 | hm2
          · exact hnot ⟨n, hn⟩ hm1
          · obtain ⟨j, -, heq⟩ := List.mem_map.1 hm2
            have := congrArg (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len => pc.2.val) heq
            simp only at this; omega
        have hlen1 : seen₁.length < qWots vp := by simp [seen₁]; omega
        have hgoal := hchain_step pos ⟨n, hn⟩ (chainStepsCore pr.toSLHDSA.core msg n)
          (chainStepsCore_le pr.toSLHDSA.core msg n) seen₁ hnot1 hlen1 savedT₁ s₁ hs₁ hst₁ hnd₁
          (fun p => Kv ((v.push p.1.1, p.1.2), p.2))
          (fun p => Kv' (v.push p))
          (fun pair savedT₂ s₂ hs₂ hst₂ hnd₂ hsub₂ htop_pair hpair => by
            have hseen_eq : seen₁ ++ [(pos, ⟨n, hn⟩)] =
                seen ++ (List.finRange (n + 1)).map fun j => (pos, ⟨j.val, by omega⟩) := by
              simp only [seen₁, List.append_assoc, List.finRange_succ_last, List.map_append,
                List.map_map, List.map_singleton, Function.comp_def, Fin.val_castSucc, Fin.val_last]
            rw [hseen_eq] at hs₂
            refine hKv (v.push pair) savedT₂ s₂ hs₂ hst₂ hnd₂ (fun e he => hsub₂ e (hsub₁ e he)) fun j => ?_
            by_cases hj : j.val < n
            · simp only [Vector.getElem_push_lt hj]
              obtain ⟨htop_j, hpre_j⟩ := hv₁ ⟨j.val, hj⟩
              exact ⟨htop_j, fun hb => by
                obtain ⟨x, hx1, hx2⟩ := hpre_j hb
                exact ⟨x, hsub₂ _ hx1, hx2⟩⟩
            · have hjn : j.val = n := by omega
              simp only [hjn, Vector.getElem_push_eq]
              exact ⟨htop_pair, hpair⟩)
        simpa only [bind_assoc, pure_bind] using hgoal
    -- Apply `hvec` at `n = len`, then handle `thLsl` (`type = 1 ≠ 0`)
    unfold buildLeafM
    dsimp only
    simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
    have hprob_vec : (Vector.ofFnM fun c : Fin vp.sl.params.len => do
        let b := chainStepsCore pr.toSLHDSA.core (wotsMsgFromTbl pr acc.tbl pos) c.val
        let x ← $ᵗ pr.Y
        let sigBlk := hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x
        let top ← slChainM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y))
          (wotsChainAdrs (wotsInstanceAdrs pos) c.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)) =
      (Vector.ofFnM fun j : Fin vp.sl.params.len => do
        let b := chainStepsCore pr.toSLHDSA.core msg j.val
        let x ← $ᵗ pr.Y
        let sigBlk := hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) b x
        let top := slChainDet pr pk (wotsChainAdrs (wotsInstanceAdrs pos) j.val) sigBlk b (vp.sl.params.w - 1 - b)
        return (sigBlk, top)) := by
      congr 1; funext c
      refine bind_congr fun x => ?_
      have hc : ∀ chAdrs y st steps,
          slChainM pr (fun i a m => (pure (pr.memberEval i pk a m) : ProbComp pr.Y)) chAdrs y st steps =
            pure (slChainDet pr pk chAdrs y st steps) := by
        intro chAdrs y st steps; induction steps with
        | zero => rfl
        | succ steps ih => simp only [slChainM, ih, pure_bind, slChainDet, Id.run_bind, sfDetCall, Id.run_pure]
      simp only [hc, pure_bind, msg]
    simp only [pure_bind]
    rw [hprob_vec]
    refine hvec vp.sl.params.len le_rfl savedT s hinv.1 hinv.2.1 hinv.2.2.1 _ _
      (fun pairs savedT₁ s₁ hs₁ hst₁ hnd₁ hsub₁ hv₁ => ?_)
    have hnr : ¬ TweakReserved Prod.fst s₁.1 (wotsPkAdrs (wotsInstanceAdrs pos)) := by
      rintro ⟨e, he, heq⟩
      have ht0 := (hs₁.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).1
      rw [heq] at ht0
      simp [wotsPkAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode] at ht0
    have hwpk : (simulateQ impl ((liftM (hybCollCall pr .thLsl (wotsPkAdrs (wotsInstanceAdrs pos))
        ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
          (Params.lsl_eq_len vp.valid).symm)) : StateT (List Adrs) (OracleComp (FSpec pr)) pr.Y).run savedT₁)).run s₁ =
        pure ((pr.memberEval .thLsl pk (wotsPkAdrs (wotsInstanceAdrs pos))
          ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
            (Params.lsl_eq_len vp.valid).symm), savedT₁),
          (s₁.1, s₁.2 ++ [wotsPkAdrs (wotsInstanceAdrs pos)])) := by
      change (simulateQ impl ((StateT.lift (hybCollCall pr .thLsl (wotsPkAdrs (wotsInstanceAdrs pos))
        ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
          (Params.lsl_eq_len vp.valid).symm))).run savedT₁)).run s₁ = _
      rw [StateT.run_lift]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
      unfold hybCollCall impl
      simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_PRE_oracles, QueryImpl.add_apply_inr,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
        pure_bind, hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
      rfl
    simp only [hwpk, pure_bind, StateT.run_pure, simulateQ_pure]
    have hinv_next : PreBuildInv pr pk (seen ++ (List.finRange vp.sl.params.len).map (pos, ·))
        (donePos ++ [pos])
        ⟨Function.update acc.tbl (wotsPkAdrs (wotsInstanceAdrs pos))
            (some (pr.memberEval .thLsl pk (wotsPkAdrs (wotsInstanceAdrs pos))
              ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
                (Params.lsl_eq_len vp.valid).symm))),
          Function.update acc.wotsMsg pos msg,
          Function.update acc.wotsSig pos (Vector.ofFn fun c => pairs[c.val].1)⟩
        savedT₁ (s₁.1, s₁.2 ++ [wotsPkAdrs (wotsInstanceAdrs pos)]) := by
      refine ⟨⟨hs₁.1, fun t ht => ?_, hs₁.2.2⟩, hst₁, hnd₁, fun p' hp' => ?_⟩
      · rcases List.mem_append.1 ht with ht1 | ht2
        · exact hs₁.2.1 t ht1
        · simp only [List.mem_singleton] at ht2; subst ht2
          left; simp [wotsPkAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode]
      · rcases List.mem_append.1 hp' with hp1 | hp2
        · have hne_p : p' ≠ pos := fun heq => hnotP (heq ▸ hp1)
          have hne_adrs : wotsPkAdrs (wotsInstanceAdrs p') ≠ wotsPkAdrs (wotsInstanceAdrs pos) := by
            intro heq
            apply hne_p
            rcases p' with ⟨l₁, t₁, lf₁⟩; rcases pos with ⟨l₂, t₂, lf₂⟩
            have hl : l₁.val = l₂.val := by
              have := congrArg Adrs.layer heq
              simpa [wotsPkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs, Adrs.setKeyPairAddress,
                Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.setLayerAddress] using this
            have hl' : l₁ = l₂ := Fin.ext hl; subst hl'
            have ht : t₁.val = t₂.val := by
              have := congrArg Adrs.tree heq
              simpa [wotsPkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs, Adrs.setKeyPairAddress,
                Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.setLayerAddress] using this
            have ht' : t₁ = t₂ := Fin.ext ht; subst ht'
            have hlf : lf₁.val = lf₂.val := by
              have := congrArg Adrs.word1 heq
              simpa [wotsPkAdrs, wotsInstanceAdrs, wotsLeafAdrs, LayerPosition.toAdrs, Adrs.setKeyPairAddress,
                Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.setLayerAddress, Adrs.getKeyPairAddress] using this
            have hlf' : lf₁ = lf₂ := Fin.ext hlf; subst hlf'; rfl
          simp only [Function.update_of_ne hne_adrs, Function.update_of_ne hne_p]
          obtain ⟨hpk_p, hch_p⟩ := hinv.2.2.2 p' hp1
          refine ⟨hpk_p, fun c hb => ?_⟩
          obtain ⟨x, hx1, hx2⟩ := hch_p c hb
          exact ⟨x, hsub₁ _ hx1, hx2⟩
        · have hpeq : p' = pos := List.mem_singleton.1 hp2
          subst p'
          simp only [Function.update_self, Option.getD_some]
          refine ⟨?_, fun c hb => ?_⟩
          · rw [SLHDSA.wotsPkFromSig_eq_tl]
            have htops : ((Vector.ofFn fun c : Fin vp.sl.params.len => pairs[c.val].2).cast
                (Params.lsl_eq_len vp.valid).symm).toList =
              (SLHDSA.wotsPkFromSigTops (prEager pr) (Vector.ofFn fun c => pairs[c.val].1) msg pk
                (wotsInstanceAdrs pos)).toList := by
              apply List.ext_getElem
              · simp [Params.lsl_eq_len vp.valid]
              · intro i hi₁ hi₂
                simp only [Vector.getElem_toList, Vector.getElem_cast, Vector.getElem_ofFn,
                  SLHDSA.wotsPkFromSigTops_eq_ofFn]
                have hi' : i < vp.sl.params.len := by simpa [Params.lsl_eq_len vp.valid] using hi₁
                rw [(hv₁ ⟨i, hi'⟩).1, slChainDet_eq_chain pr]
                rfl
            change pr.Th pk (wotsPkAdrs (wotsInstanceAdrs pos)) _ =
              pr.Th pk (wotsPkAdrs (wotsInstanceAdrs pos)) _
            rw [htops]
          · simpa only [Vector.getElem_ofFn] using (hv₁ c).2 hb
    exact hKl _ savedT₁ _ hinv_next
  -- Fold `buildTreeM` over `allXmssTrees vp.sl`
  have htrees_step : ∀ (ts : List (LayerTreeCoord vp.sl)),
      ts.Nodup →
      ∀ (acc : HybAcc pr) (seen : List (LayerPosition vp.sl × Fin vp.sl.params.len))
        (donePos : List (LayerPosition vp.sl)),
      (∀ coord ∈ ts, ∀ lf : Fin (2 ^ vp.sl.params.hp), ∀ c : Fin vp.sl.params.len,
        (⟨coord.layer, coord.tree, lf⟩, c) ∉ seen) →
      (∀ coord ∈ ts, ∀ lf : Fin (2 ^ vp.sl.params.hp),
        (⟨coord.layer, coord.tree, lf⟩ : LayerPosition vp.sl) ∉ donePos) →
      seen.length + ts.length * (2 ^ vp.sl.params.hp * vp.sl.params.len) ≤ qWots vp →
      ∀ (savedT : List Adrs) (s : List (Adrs × pr.Y) × List Adrs),
      PreBuildInv pr pk seen donePos acc savedT s →
      ∀ (Kt : (HybAcc pr × List Adrs) × (List (Adrs × pr.Y) × List Adrs) → ProbComp Bool)
        (Kt' : HybAcc pr → ProbComp Bool),
      (∀ acc' savedT' s',
        PreBuildInv pr pk
          (seen ++ ts.flatMap fun coord => (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c))
          (donePos ++ ts.flatMap fun coord => (List.finRange (2 ^ vp.sl.params.hp)).map fun lf =>
            ⟨coord.layer, coord.tree, lf⟩)
          acc' savedT' s' →
        𝒟[Kt' acc'] {true} ≤ 𝒟[Kt ((acc', savedT'), s')] {true}) →
      𝒟[ts.foldlM (buildTreeM pr (fun i a msg => pure (pr.memberEval i pk a msg))
        (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x))
        acc >>= Kt'] {true} ≤
      𝒟[(simulateQ impl ((ts.foldlM (buildTreeM pr (fun i a msg => liftM (hybCollCall pr i a msg))
        (preChainStart pr)) acc).run savedT)).run s >>= Kt] {true} := by
    intro ts; induction ts with
    | nil =>
      intro _ acc seen donePos _ _ _ savedT s hinv Kt Kt' hKt
      simp only [List.foldlM_nil, StateT.run_pure, simulateQ_pure, pure_bind]
      exact hKt acc savedT s (by simpa using hinv)
    | cons coord coords iht =>
      intro hnd acc seen donePos hnot hnotP hlen savedT s hinv Kt Kt' hKt
      rw [List.nodup_cons] at hnd
      simp only [List.foldlM_cons, StateT.run_bind, simulateQ_bind, bind_assoc]
      -- Fold the `2^hp` leaves of `coord`
      have hlfs : ∀ (ls : List (Fin (2 ^ vp.sl.params.hp))),
          ls.Nodup →
          ∀ (a0 : HybAcc pr) (sn0 : List (LayerPosition vp.sl × Fin vp.sl.params.len))
            (dp0 : List (LayerPosition vp.sl)),
          (∀ lf ∈ ls, ∀ c, (⟨coord.layer, coord.tree, lf⟩, c) ∉ sn0) →
          (∀ lf ∈ ls, (⟨coord.layer, coord.tree, lf⟩ : LayerPosition vp.sl) ∉ dp0) →
          sn0.length + ls.length * vp.sl.params.len ≤ qWots vp →
          ∀ (st0 : List Adrs) (s0 : List (Adrs × pr.Y) × List Adrs),
          PreBuildInv pr pk sn0 dp0 a0 st0 s0 →
          ∀ (Kl : (HybAcc pr × List Adrs) × (List (Adrs × pr.Y) × List Adrs) → ProbComp Bool)
            (Kl' : HybAcc pr → ProbComp Bool),
          (∀ a' st' s',
            PreBuildInv pr pk
              (sn0 ++ ls.flatMap fun lf => (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c))
              (dp0 ++ ls.map fun lf => ⟨coord.layer, coord.tree, lf⟩)
              a' st' s' →
            𝒟[Kl' a'] {true} ≤ 𝒟[Kl ((a', st'), s')] {true}) →
          𝒟[ls.foldlM (fun a lf => buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg))
            (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
            a ⟨coord.layer, coord.tree, lf⟩) a0 >>= Kl'] {true} ≤
          𝒟[(simulateQ impl ((ls.foldlM (fun a lf => buildLeafM pr (fun i a msg => liftM (hybCollCall pr i a msg))
            (preChainStart pr) a ⟨coord.layer, coord.tree, lf⟩) a0).run st0)).run s0 >>= Kl] {true} := by
        intro ls; induction ls with
        | nil =>
          intro _ a0 sn0 dp0 _ _ _ st0 s0 hinv0 Kl Kl' hKl
          simp only [List.foldlM_nil, StateT.run_pure, simulateQ_pure, pure_bind]
          exact hKl a0 st0 s0 (by simpa using hinv0)
        | cons lf ls' ihl =>
          intro hndl a0 sn0 dp0 hnotl hnotPl hlenl st0 s0 hinv0 Kl Kl' hKl
          rw [List.nodup_cons] at hndl
          simp only [List.foldlM_cons, StateT.run_bind, simulateQ_bind, bind_assoc]
          refine hleaf_step ⟨coord.layer, coord.tree, lf⟩ a0 sn0 dp0 (hnotl lf (by simp))
            (hnotPl lf (by simp)) (by simp only [List.length_cons] at hlenl; nlinarith) st0 s0 hinv0
            _ _ (fun a1 st1 s1 hinv1 => ?_)
          set sn1 := sn0 ++ (List.finRange vp.sl.params.len).map (⟨coord.layer, coord.tree, lf⟩, ·)
          set dp1 := dp0 ++ [⟨coord.layer, coord.tree, lf⟩]
          refine ihl hndl.2 a1 sn1 dp1 (fun lf' hlf' c hm => ?_) (fun lf' hlf' hm => ?_)
            (by simp only [sn1, List.length_append, List.length_map, List.length_finRange]; simp only [List.length_cons] at hlenl; nlinarith)
            st1 s1 hinv1 Kl Kl' (fun a' st' s' hinv' => ?_)
          · rcases List.mem_append.1 hm with hm1 | hm2
            · exact hnotl lf' (by simp [hlf']) c hm1
            · obtain ⟨c', -, heq⟩ := List.mem_map.1 hm2
              have : lf = lf' := congrArg (fun pc : LayerPosition vp.sl × Fin vp.sl.params.len => pc.1.leaf) heq
              exact hndl.1 (this ▸ hlf')
          · rcases List.mem_append.1 hm with hm1 | hm2
            · exact hnotPl lf' (by simp [hlf']) hm1
            · simp only [List.mem_singleton] at hm2
              have : lf' = lf := congrArg LayerPosition.leaf hm2
              exact hndl.1 (this ▸ hlf')
          · have hsn_eq : sn1 ++ ls'.flatMap (fun lf => (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) =
                sn0 ++ (lf :: ls').flatMap (fun lf => (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)) := by
              simp [sn1, List.flatMap_cons, List.append_assoc]
            have hdp_eq : dp1 ++ ls'.map (fun lf => (⟨coord.layer, coord.tree, lf⟩ : LayerPosition vp.sl)) =
                dp0 ++ (lf :: ls').map (fun lf => ⟨coord.layer, coord.tree, lf⟩) := by
              simp [dp1, List.append_assoc]
            rw [hsn_eq, hdp_eq] at hinv'
            exact hKl a' st' s' hinv'
      have hhead_l : buildTreeM pr (fun i a msg => liftM (hybCollCall pr i a msg)) (preChainStart pr) acc coord =
          (do
            let acc₁ ← (List.finRange (2 ^ vp.sl.params.hp)).foldlM
              (fun a lf => buildLeafM pr (fun i a msg => liftM (hybCollCall pr i a msg))
                (preChainStart pr) a ⟨coord.layer, coord.tree, lf⟩) acc
            let tbl₂ ← (perfectInternalCoords vp.sl.params.hp).foldlM (fun tbl zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← (liftM (hybCollCall pr .H a (lv, rv)) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y)
              return Function.update tbl a (some v)) acc₁.tbl
            return { acc₁ with tbl := tbl₂ }) := rfl
      have hhead_r : buildTreeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y))
          (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
          acc coord =
          (do
            let acc₁ ← (List.finRange (2 ^ vp.sl.params.hp)).foldlM
              (fun a lf => buildLeafM pr (fun i a msg => pure (pr.memberEval i pk a msg))
                (fun pos c b => do let x ← $ᵗ pr.Y; return hybBlockVal pr (vp.params.w - 2) pk (wotsChainAdrs (wotsInstanceAdrs pos) c.val) b x)
                a ⟨coord.layer, coord.tree, lf⟩) acc
            let tbl₂ ← (perfectInternalCoords vp.sl.params.hp).foldlM (fun tbl zi => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← (pure (pr.memberEval .H pk a (lv, rv)) : ProbComp pr.Y)
              return Function.update tbl a (some v)) acc₁.tbl
            return { acc₁ with tbl := tbl₂ }) := rfl
      rw [hhead_l, hhead_r]
      simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
      have hlen_head : seen.length + (List.finRange (2 ^ vp.sl.params.hp)).length * vp.sl.params.len ≤ qWots vp := by
        rw [List.length_finRange]; change seen.length + 2 ^ vp.params.slParams.hp * vp.params.slParams.len ≤ qWots vp
        simp only [List.length_cons, Nat.add_mul, one_mul] at hlen; omega
      refine hlfs (List.finRange (2 ^ vp.sl.params.hp)) (List.nodup_finRange _) acc seen donePos
        (fun lf _ c => hnot coord (by simp) lf c) (fun lf _ => hnotP coord (by simp) lf) hlen_head
        savedT s hinv _ _ (fun a1 st1 s1 hinv1 => ?_)
      -- XMSS internal nodes (`type = 2 ≠ 0, 1`): deterministic, preserves `PreBuildInv`!
      have hxmss : ∀ (l : List (ℕ × ℕ)) (tbl : Adrs → Option pr.Y)
          (s' : List (Adrs × pr.Y) × List Adrs),
          PreBuildInv pr pk
            (seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
              (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c))
            (donePos ++ (List.finRange (2 ^ vp.sl.params.hp)).map fun lf => ⟨coord.layer, coord.tree, lf⟩)
            { a1 with tbl := tbl } st1 s' →
          ∃ s'',
            PreBuildInv pr pk
              (seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
                (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c))
              (donePos ++ (List.finRange (2 ^ vp.sl.params.hp)).map fun lf => ⟨coord.layer, coord.tree, lf⟩)
              { a1 with tbl := Id.run (l.foldlM (fun t zi => do
                let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
                let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
                let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
                let v ← sfDetCall pr pk .H a (lv, rv)
                return Function.update t a (some v)) tbl) }
              st1 s'' ∧
            (simulateQ impl ((l.foldlM (fun (t : Adrs → Option pr.Y) (zi : ℕ × ℕ) => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← (liftM (hybCollCall pr .H a (lv, rv)) : StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y)
              return Function.update t a (some v)) tbl).run st1)).run s' =
            pure ((Id.run (l.foldlM (fun (t : Adrs → Option pr.Y) (zi : ℕ × ℕ) => do
              let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
              let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
              let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
              let v ← sfDetCall pr pk .H a (lv, rv)
              return Function.update t a (some v)) tbl), st1), s'') := by
        intro l; induction l with
        | nil => intro tbl s' hs'; exact ⟨s', hs', by simp⟩
        | cons zi zis ihz =>
          intro tbl s' hs'
          have hnr : ¬ TweakReserved Prod.fst s'.1 (xmssNodeAdrs coord.toAdrs zi.1 zi.2) := by
            rintro ⟨e, he, heq⟩
            have ht0 := (hs'.1.1 e.1 (List.mem_map.2 ⟨e, he, rfl⟩)).1; rw [heq] at ht0
            simp [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode] at ht0
          have h1 : (simulateQ impl ((liftM (hybCollCall pr .H (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
              ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
               (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default)) :
              StateT (List Adrs) (OracleComp (Fxmss.Rom.Hyb.FSpec pr)) pr.Y).run st1)).run s' =
              pure ((pr.memberEval .H pk (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
                ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
                 (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default), st1),
                (s'.1, s'.2 ++ [xmssNodeAdrs coord.toAdrs zi.1 zi.2])) := by
            change (simulateQ impl ((StateT.lift (hybCollCall pr .H (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
              ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
               (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default))).run st1)).run s' = _
            rw [StateT.run_lift]
            simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
            unfold hybCollCall impl
            simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_PRE_oracles, QueryImpl.add_apply_inr,
              StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
              pure_bind, hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
            rfl
          have hs'' : PreBuildInv pr pk
              (seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
                (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c))
              (donePos ++ (List.finRange (2 ^ vp.sl.params.hp)).map fun lf => ⟨coord.layer, coord.tree, lf⟩)
              ⟨Function.update tbl (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
                  (some (pr.memberEval .H pk (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
                    ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
                     (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default))),
                a1.wotsMsg, a1.wotsSig⟩
              st1 (s'.1, s'.2 ++ [xmssNodeAdrs coord.toAdrs zi.1 zi.2]) := by
            refine ⟨⟨hs'.1.1, fun t ht => ?_, hs'.1.2.2⟩, hs'.2.1, hs'.2.2.1, fun p' hp' => ?_⟩
            · rcases List.mem_append.1 ht with ht1 | ht2
              · exact hs'.1.2.1 t ht1
              · simp only [List.mem_singleton] at ht2; subst ht2
                left; simp [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode]
            · have hne_adrs : wotsPkAdrs (wotsInstanceAdrs p') ≠ xmssNodeAdrs coord.toAdrs zi.1 zi.2 := by
                intro heq
                have := congrArg Adrs.type heq
                simp [wotsPkAdrs, xmssNodeAdrs, Adrs.setKeyPairAddress, Adrs.setTreeIndex,
                  Adrs.setTreeHeight, Adrs.setTypeAndClear, AddrType.toCode] at this
              simpa [Function.update_of_ne hne_adrs] using hs'.2.2.2 p' hp'
          obtain ⟨s''', hs''', hrest⟩ := ihz
            (Function.update tbl (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
              (some (pr.memberEval .H pk (xmssNodeAdrs coord.toAdrs zi.1 zi.2)
                ((tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default,
                 (tbl (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default))))
            (s'.1, s'.2 ++ [xmssNodeAdrs coord.toAdrs zi.1 zi.2]) hs''
          refine ⟨s''', hs''', ?_⟩
          simp only [List.foldlM_cons, StateT.run_bind, simulateQ_bind, h1, pure_bind,
            StateT.run_pure, simulateQ_pure, sfDetCall]
          exact hrest
      have hxmss_p : ∀ (l : List (ℕ × ℕ)) (tbl : Adrs → Option pr.Y),
          (l.foldlM (fun t zi => do
            let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
            let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
            let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
            let v ← (pure (pr.memberEval .H pk a (lv, rv)) : ProbComp pr.Y)
            return Function.update t a (some v)) tbl) =
          pure (Id.run (l.foldlM (fun t zi => do
            let a := xmssNodeAdrs coord.toAdrs zi.1 zi.2
            let lv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2))).getD default
            let rv := (t (xmssCellAdrs coord.toAdrs (zi.1 - 1) (2 * zi.2 + 1))).getD default
            let v ← sfDetCall pr pk .H a (lv, rv)
            return Function.update t a (some v)) tbl)) := by
        intro l; induction l with
        | nil => intro _; rfl
        | cons zi zis ihz => intro tbl; simp only [List.foldlM_cons, pure_bind, sfDetCall]; exact ihz _
      obtain ⟨s2, hinv2, hrun2⟩ := hxmss (perfectInternalCoords vp.sl.params.hp) a1.tbl s1 hinv1
      rw [hxmss_p, hrun2]
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      set sn1 := seen ++ (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
        (List.finRange vp.sl.params.len).map fun c => (⟨coord.layer, coord.tree, lf⟩, c)
      set dp1 := donePos ++ (List.finRange (2 ^ vp.sl.params.hp)).map fun lf => ⟨coord.layer, coord.tree, lf⟩
      refine iht hnd.2 _ sn1 dp1 (fun c' hc' lf ch hm => ?_) (fun c' hc' lf hm => ?_) ?_ st1 s2 hinv2
        Kt Kt' (fun acc' st' s' hinv' => ?_)
      · rcases List.mem_append.1 hm with hm1 | hm2
        · exact hnot c' (by simp [hc']) lf ch hm1
        · simp only [List.mem_flatMap, List.mem_map] at hm2
          obtain ⟨lf', -, ch', -, heq⟩ := hm2
          exact hnd.1 (coord_eq_of_pos_eq (congrArg Prod.fst heq) ▸ hc')
      · rcases List.mem_append.1 hm with hm1 | hm2
        · exact hnotP c' (by simp [hc']) lf hm1
        · obtain ⟨lf', -, heq⟩ := List.mem_map.1 hm2
          exact hnd.1 (coord_eq_of_pos_eq heq ▸ hc')
      · have hlen_sn1 : sn1.length = seen.length + 2 ^ vp.params.slParams.hp * vp.params.slParams.len := by
          simp [sn1, List.length_flatMap]
        rw [hlen_sn1]
        change seen.length + 2 ^ vp.params.slParams.hp * vp.params.slParams.len +
          coords.length * (2 ^ vp.params.slParams.hp * vp.params.slParams.len) ≤ qWots vp
        simp only [List.length_cons, Nat.add_mul, one_mul] at hlen; omega
      · have hsn_eq : sn1 ++ coords.flatMap (fun c' => (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun ch => (⟨c'.layer, c'.tree, lf⟩, ch)) =
          seen ++ (coord :: coords).flatMap (fun c' => (List.finRange (2 ^ vp.sl.params.hp)).flatMap fun lf =>
            (List.finRange vp.sl.params.len).map fun ch => (⟨c'.layer, c'.tree, lf⟩, ch)) := by
          simp [sn1, List.flatMap_cons, List.append_assoc]
        have hdp_eq : dp1 ++ coords.flatMap (fun c' => (List.finRange (2 ^ vp.sl.params.hp)).map fun lf =>
            (⟨c'.layer, c'.tree, lf⟩ : LayerPosition vp.sl)) =
          donePos ++ (coord :: coords).flatMap (fun c' => (List.finRange (2 ^ vp.sl.params.hp)).map fun lf =>
            ⟨c'.layer, c'.tree, lf⟩) := by
          simp [dp1, List.flatMap_cons, List.append_assoc]
        rw [hsn_eq, hdp_eq] at hinv'
        exact hKt acc' st' s' hinv'
  -- Assemble FORS + `allXmssTrees`
  obtain ⟨tws₁, htws₁, hfors_run⟩ := hfors
  have hfors_prob : ((forsAddresses vp).foldlM (fun tbl a => do
      let v ← evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) u tbl a
      return Function.update tbl a (some v)) (fun _ => none)) =
    pure (Id.run ((forsAddresses vp).foldlM (fun tbl a => do
      let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
      return Function.update tbl a (some v)) (fun _ => none))) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
        (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) u tbl a
          return Function.update tbl a (some v)) tbl) =
        pure (Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (sfDetCall pr pk) u tbl a
          return Function.update tbl a (some v)) tbl)) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons a as ih =>
        intro tbl
        have hev : evalNodeM pr (fun i a msg => (pure (pr.memberEval i pk a msg) : ProbComp pr.Y)) u tbl a =
            pure (Id.run (evalNodeM pr (sfDetCall pr pk) u tbl a)) := by
          rw [evalNodeM_eq_of_input, evalNodeM_eq_of_input]
          cases evalNodeInput pr u tbl a <;> rfl
        simp only [List.foldlM_cons, hev, pure_bind, Id.run_bind, Id.run_pure]
        exact ih _
    exact haux _ _
  unfold preBuildM hybTreeProb buildHybTreeM
  simp only [StateT.run_bind, simulateQ_bind, hfors_run, hfors_prob, bind_assoc, pure_bind,
    StateT.run_pure, simulateQ_pure]
  have hlen_all : 0 + (allXmssTreesList vp).length * (2 ^ vp.sl.params.hp * vp.sl.params.len) ≤ qWots vp := by
    rw [Nat.zero_add, allXmssTreesList_length, ← Nat.mul_assoc]
    have hw : xmssTreeCount vp.sl.params * 2 ^ vp.sl.params.hp = wotsInstanceCount vp.sl.params := by
      unfold wotsInstanceCount xmssTreeCount; exact Finset.sum_mul _ _ _
    rw [hw]; exact le_rfl
  exact htrees_step (allXmssTreesList vp) (allXmssTreesList_nodup vp) _ [] []
    (fun _ _ _ _ h => by simp at h) (fun _ _ _ h => by simp at h) hlen_all [] ([], tws₁)
    ⟨⟨fun _ h => by simp at h, fun t ht => Or.inl (htws₁ t ht), by simp⟩, rfl, List.nodup_nil,
      fun _ h => by simp at h⟩
    (fun z => K₁ ((⟨(z.1.1.tbl (topRootAdrs vp)).getD default, z.1.1.tbl, z.1.1.wotsMsg, z.1.1.wotsSig⟩, z.1.2), z.2))
    (fun a => K₁' ⟨(a.tbl (topRootAdrs vp)).getD default, a.tbl, a.wotsMsg, a.wotsSig⟩)
    (fun acc' savedT' s' hinv' => by
      have hall_pos : ∀ pos : LayerPosition vp.sl,
          pos ∈ [] ++ (allXmssTreesList vp).flatMap fun coord =>
            (List.finRange (2 ^ vp.sl.params.hp)).map fun lf => ⟨coord.layer, coord.tree, lf⟩ := fun pos => by
        simp only [List.nil_append, List.mem_flatMap, List.mem_map]
        exact ⟨⟨pos.layer, pos.tree⟩, mem_allXmssTreesList vp _, pos.leaf, List.mem_finRange _, rfl⟩
      exact hdom _ savedT' s' hinv'.2.1 hinv'.2.2.1
        (fun pos => (hinv'.2.2.2 pos (hall_pos pos)).1)
        (fun pos => (hinv'.2.2.2 pos (hall_pos pos)).2))

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **In `Hyb(w - 2)`, `isHybWotsPre` is bounded by `SM_DT_PRE_Advantage (B_pre pr sfStage stage2)`.** -/
theorem hybProbExp_top_le_B_pre {D E : Type} (sfStage : SfStage1 pr D E)
    (stage2 : D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr))) :
    𝒟[hybProbExp pr sfStage stage2 (vp.params.w - 2)] {true} ≤
      SM_DT_PRE_Advantage (B_pre pr sfStage stage2) := by
  have hbind_le : ∀ {α : Type} (m : ProbComp α) (f g : α → ProbComp Bool),
      (∀ a ∈ support m, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) →
      𝒟[m >>= f] {true} ≤ 𝒟[m >>= g] {true} := fun m f g hfg =>
    evalDist_bind_apply_mono_of_support m f g (measurableSet_singleton true) hfg
  unfold SM_DT_PRE_Advantage SM_DT_PRE_Experiment hybProbExp
  refine hbind_le ($ᵗ pr.PkSeed) _ _ fun pk _ => ?_
  simp only [B_pre]
  rw [show SM_DT_PRE_oracles (probPre pr (qWots vp)) pk =
      Fxmss.unifFwd _ + (SM_DT_PRE_challengeOracle (probPre pr (qWots vp)) pk +
        collectionOracle Prod.fst (probPre pr (qWots vp)).thColl pk) from rfl]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine hbind_le sfStage.g₁ _ _ fun d hd => ?_
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine hbind_le ($ᵗ (SlSecAdrs vp → pr.Y)) _ _ fun u _ => ?_
  rw [← show SM_DT_PRE_oracles (probPre pr (qWots vp)) pk =
      Fxmss.unifFwd _ + (SM_DT_PRE_challengeOracle (probPre pr (qWots vp)) pk +
        collectionOracle Prod.fst (probPre pr (qWots vp)).thColl pk) from rfl]
  obtain ⟨⟨qs₀, tws₀⟩, ⟨hqs₀, htws₀⟩, hsf⟩ := sfStage.sfRun_spec
    (SM_DT_PRE_oracles (probPre pr (qWots vp)) pk) (hybCollCall pr) pk
    (fun s => s.1 = [] ∧ ∀ t ∈ s.2, Scheme.IsStateful t)
    (fun s a => (s.1, s.2 ++ [a]))
    (fun i a msg s hsf ⟨hqs, _⟩ => by
      rcases s with ⟨qs, tws⟩; dsimp only at hqs; subst hqs
      unfold hybCollCall
      simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_PRE_oracles, QueryImpl.add_apply_inr,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, collectionOracle, StateT.run_get,
        pure_bind, TweakReserved, List.not_mem_nil, false_and, exists_false,
        ↓reduceIte, StateT.run_set, Option.getD_some]
      rfl)
    (fun s a ⟨hqs, htws⟩ hsf => ⟨hqs, fun t ht => by
      rcases List.mem_append.1 ht with ht1 | ht2
      · exact htws t ht1
      · simp only [List.mem_singleton] at ht2; subst ht2; exact hsf⟩)
    d hd ([], []) ⟨rfl, fun _ h => by simp at h⟩
  dsimp only at hqs₀; subst hqs₀
  simp only [simulateQ_bind, StateT.run_bind, hsf, pure_bind, bind_assoc, simulateQ_pure, StateT.run_pure]
  refine simulateQ_preBuildM_le pr pk u tws₀ htws₀ _ _
    fun hyb savedT s' hst hnd hcons hrec => ?_
  refine hbind_le (stage2 d (sfStage.sfDet d pk) pk u hyb) _ _ fun o _ => ?_
  by_cases ho : isHybWotsPre pr pk hyb o = true
  · rw [ho]
    rcases o with _ | ⟨msg, sig⟩
    · simp [isHybWotsPre] at ho
    · simp only [isHybWotsPre, Option.isSome_iff_exists] at ho
      obtain ⟨⟨⟨pos, c⟩, step, val⟩, hfind⟩ := ho
      obtain ⟨_, hstep, hF⟩ := findHybWotsPre_sound pr pk hyb hcons msg sig hfind
      have hb0 : 0 < chainStepsCore pr.toSLHDSA.core (hyb.wotsMsg pos) c.val := by omega
      obtain ⟨x, hmem, hFx⟩ := hrec pos c hb0
      set a := (wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step
      have ha_eq : (wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress
          (chainStepsCore pr.toSLHDSA.core (hyb.wotsMsg pos) c.val - 1) = a := by
        simp only [a, show chainStepsCore pr.toSLHDSA.core (hyb.wotsMsg pos) c.val - 1 = step by omega]
      rw [ha_eq] at hmem hFx
      have ha_mem : a ∈ savedT := by rw [hst]; exact List.mem_map.2 ⟨(a, x), hmem, rfl⟩
      have hlen_st : savedT.length = s'.1.length := by rw [hst, List.length_map]
      have hidx_lt : savedT.idxOf a < s'.1.length :=
        (List.idxOf_lt_length_of_mem ha_mem).trans_eq hlen_st
      have hget_fst : (s'.1[savedT.idxOf a]'hidx_lt).1 = a := by
        have h1 : savedT[savedT.idxOf a]'(List.idxOf_lt_length_of_mem ha_mem) = a :=
          List.getElem_idxOf (List.idxOf_lt_length_of_mem ha_mem)
        have h2 : savedT[savedT.idxOf a]'(List.idxOf_lt_length_of_mem ha_mem) =
            (s'.1[savedT.idxOf a]'hidx_lt).1 := by
          have : ∀ (l : List Adrs) (hl : l = s'.1.map Prod.fst) (j : ℕ) (hj1 : j < l.length)
              (hj2 : j < s'.1.length), l[j]'hj1 = (s'.1[j]'hj2).1 := by
            rintro _ rfl j hj1 hj2; simp
          exact this savedT hst (savedT.idxOf a) (List.idxOf_lt_length_of_mem ha_mem) hidx_lt
        exact h2.symm.trans h1
      have hget_snd : (s'.1[savedT.idxOf a]'hidx_lt).2 = x := by
        obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.1 hmem
        have hk_st : k < savedT.length := hk.trans_eq hlen_st.symm
        have hk_fst : savedT[k]'hk_st = a := by
          have : ∀ (l : List Adrs) (hl : l = s'.1.map Prod.fst) (j : ℕ) (hj1 : j < l.length)
              (hj2 : j < s'.1.length), l[j]'hj1 = (s'.1[j]'hj2).1 := by
            rintro _ rfl j hj1 hj2; simp
          rw [this savedT hst k hk_st hk, hkeq]
        have hkeq_idx : k = savedT.idxOf a := by
          have hinj := List.nodup_iff_injective_getElem.1 hnd
          have heq : (⟨k, hk_st⟩ : Fin savedT.length) = ⟨savedT.idxOf a, List.idxOf_lt_length_of_mem ha_mem⟩ :=
            hinj (hk_fst.trans (List.getElem_idxOf (List.idxOf_lt_length_of_mem ha_mem)).symm)
          exact congrArg Fin.val heq
        subst hkeq_idx; exact congrArg Prod.snd hkeq
      have hget : s'.1[savedT.idxOf a]? = some (a, x) := by
        rw [List.getElem?_eq_getElem hidx_lt]
        exact congrArg some (Prod.ext hget_fst hget_snd)
      simp only [extractPre, hfind, Fxmss.Rom.thF, TweakableHash.ofFun, id]
      rw [show (wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress step = a from rfl, hget]
      simp only [hF, hFx, decide_true, le_refl]
  · simp only [Bool.not_eq_true] at ho
    rw [ho, evalDist_pure]
    simp

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] in
/-- **Master WOTS-TW hybrid theorem (`wotsPre_bound`)**: for ANY Stage-1 stateful hook `sfStage`
and ANY Stage-2 interaction `stage2` that does not read `u` at `WOTS_PRF` (`type = 5`),
the probability of `isHybWotsPre` in `Hyb(0)` is bounded by the `w - 2` `SM-UD` advantages of
`B_ud γ` plus the `SM-PRE` advantage of `B_pre` (against `F ∈ Th_λ`, `q₂ = wotsInstanceCount * len`
targets). -/
theorem wotsPre_bound {D E : Type} (sfStage : SfStage1 pr D E)
    (stage2 : D → E → pr.PkSeed → (SlSecAdrs vp → pr.Y) → HybTree pr →
      ProbComp (Option (List Byte × Stateless.Sig pr)))
    (hstage2 : ∀ u₁ u₂, (∀ a : SlSecAdrs vp, a.1.type ≠ 5 → u₁ a = u₂ a) →
      ∀ d sf pk hyb, stage2 d sf pk u₁ hyb = stage2 d sf pk u₂ hyb) :
    𝒟[do
        let pk ← $ᵗ pr.PkSeed
        let d ← sfStage.g₁
        let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        let hyb := hybTreeDet pr 0 pk u
        let o ← stage2 d (sfStage.sfDet d pk) pk u hyb
        return isHybWotsPre pr pk hyb o] {true} ≤
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) +
      SM_DT_PRE_Advantage (B_pre pr sfStage stage2) := by
  -- Step 1: Identify LHS with `𝒟[hybProbExp 0] {true}` via `hybTreeDet_evalDistEq_hybTreeProb`
  have h0 : (do
      let pk ← $ᵗ pr.PkSeed
      let d ← sfStage.g₁
      let u ← $ᵗ (SlSecAdrs vp → pr.Y)
      let hyb := hybTreeDet pr 0 pk u
      let o ← stage2 d (sfStage.sfDet d pk) pk u hyb
      return isHybWotsPre pr pk hyb o) =ᵈ hybProbExp pr sfStage stage2 0 := by
    unfold hybProbExp
    refine EvalDistEq.bind_right _ fun pk => EvalDistEq.bind_right _ fun d => ?_
    exact hybTreeDet_evalDistEq_hybTreeProb pr 0 pk
      (fun u hyb => do let o ← stage2 d (sfStage.sfDet d pk) pk u hyb; return isHybWotsPre pr pk hyb o)
      (fun u₁ u₂ hu hyb => by rw [hstage2 u₁ u₂ hu])
  rw [h0.evalDist_eq]
  -- Step 2: Telescope `γ = 0 .. w - 3` via `B_ud_exp`
  have hstep : ∀ γ,
      𝒟[hybProbExp pr sfStage stage2 γ] {true} ≤
        𝒟[hybProbExp pr sfStage stage2 (γ + 1)] {true} +
          SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) := by
    intro γ
    have hR := (B_ud_exp pr sfStage stage2 .real γ).evalDist_eq
    have hI := (B_ud_exp pr sfStage stage2 .ideal γ).evalDist_eq
    simp only [↓reduceIte, reduceCtorEq] at hR hI
    rw [SM_DT_UD_Advantage, MeasureTheory.Measure.boolDist, hR, hI]
    exact (ENNReal.absDiff_le_iff.1 le_rfl).1
  have htel : ∀ n,
      𝒟[hybProbExp pr sfStage stage2 0] {true} ≤
        𝒟[hybProbExp pr sfStage stage2 n] {true} +
          ∑ γ ∈ Finset.range n, SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ]
      calc 𝒟[hybProbExp pr sfStage stage2 n] {true} +
              ∑ γ ∈ Finset.range n, SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ)
          ≤ 𝒟[hybProbExp pr sfStage stage2 (n + 1)] {true} +
              SM_DT_UD_Advantage (B_ud pr sfStage stage2 n) +
              ∑ γ ∈ Finset.range n, SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) :=
            add_le_add (hstep n) le_rfl
        _ = 𝒟[hybProbExp pr sfStage stage2 (n + 1)] {true} +
              (∑ γ ∈ Finset.range n, SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) +
                SM_DT_UD_Advantage (B_ud pr sfStage stage2 n)) := by ring
  calc 𝒟[hybProbExp pr sfStage stage2 0] {true}
      ≤ 𝒟[hybProbExp pr sfStage stage2 (vp.params.w - 2)] {true} +
          ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) :=
        htel (vp.params.w - 2)
    _ ≤ SM_DT_PRE_Advantage (B_pre pr sfStage stage2) +
          ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) :=
        add_le_add (hybProbExp_top_le_B_pre pr sfStage stage2) le_rfl
    _ = ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B_ud pr sfStage stage2 γ) +
          SM_DT_PRE_Advantage (B_pre pr sfStage stage2) := add_comm _ _

end Reductions

end ShrincsSecurity.Slhdsa
