module

public import ShrincsSecurity.Shrincs.VirtualTree
public import ShrincsSecurity.Fxmss.TreeQueries
public import HashSig.SLHDSA.Security.SchemeWitnesses

/-!
# SLH-DSA bridge: `prEager`, routed Stage-1 virtual-tree precomputation, and stateful FXMSS precomputation

Infrastructure shared by **Main Paper Claim 4.16** (stateless route of SHRINCS Theorem 4.1) and
**Main Paper Theorem 4.3** (standalone SLH-DSA EU-CMA security [HK22]):

1. **Message encoding injectivity (`MsgEnc.Injective`, `slMsg_injective`)** and identification of
   `Shrincs.slVerify` with `SLHDSA.GeneralScheme.verifyInternal` (`slVerify_eq_verifyInternal`).
2. **Eager-secret SLH-DSA primitive bundle (`prEager`)**: equips `pr.toSLHDSA` with
   `SkSeed := SlSecAdrs vp → pr.Y` and `PRF := fun _ u a => slSecOf pr u a`, allowing VCVio's
   deterministic witness extractors (`SLHDSA.Security.findWitness`, `ForsWitnesses`,
   `HypertreeWitnesses`, `XmssWitnesses`, `WotsWitnesses`) to apply directly to `slSignDet` and
   `honestVal` after the `PRF` hop.
3. **Routed Stage-1 `slVirtualTreeM` (`simulateQ_slVirtualTreeM_routed`)**: a single theorem
   showing that routing any subset `isTarget : Adrs → Bool` of `constructionAddresses vp.sl` to
   an `SM-TCR` or `SM-DSPR` challenge oracle and the remaining stateless addresses to `O_coll`
   (after arbitrary stateful `O_coll` queries) suffers zero refusals, computes the exact
   `slVirtualTreeDet pr pk u`, and records the exact deterministic target list `routedTargets`.
4. **Stage-1 stateful FXMSS precomputation via `O_coll` (`sfPrecompM`)**: Claim 4.16's reverse
   precomputation of `PK.sf` and all stateful anchor signatures (`H_grind`, `F`, `Th_lsf`, `H` at
   `Scheme.IsStateful` tweaks) before `PK.seed` is revealed, leaving Stage 2 with zero stateful
   `Th_λ` evaluations and leaving stateless challenge tweaks untouched.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Slhdsa

open Scheme Shrincs SLHDSA.Security
open SLHDSA (Adrs AddrType Byte Bytes wotsSkAdrs wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsSkAdrs forsNodeAdrs forsPkAdrs chain chainStepsCore chainStepsCore_le
  wotsPkGen wotsPkGenTops wotsSign forsLeaf forsNodeHash forsPkGen forsSign
  xmssLeaf xmssNode xmssRoot xmssSign LayerPosition DigestParts splitDigest)

/-! ## 1. Message encoding injectivity and stateless verification bridge -/

/-- Injectivity of `MsgEnc` on `(ctx, body)` pairs: distinct messages carry distinct `(ctx, M)`
encodings, as in the paper where the message space is `{(ctx, M) | |ctx| ≤ 255}`. Without this,
two distinct `m₁ ≠ m₂` with the same `(ctx, body)` yield identical stateless signatures and break
stateless EU-CMA trivially. -/
def _root_.ShrincsSecurity.Shrincs.MsgEnc.Injective {Msg : Type} (enc : MsgEnc Msg) : Prop :=
  Function.Injective fun m => (enc.ctx m, enc.body m)

section MsgBridge

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)

/-- Under `enc.Injective`, the FIPS 205 pure-mode stateless message `slMsg pkSf m` is injective
in `m : Msg` (cross-binding preserves freshness on the stateless path, Claim 4.16). -/
theorem slMsg_injective (henc : enc.Injective) (pkSf : pr.Y) :
    Function.Injective (slMsg pr Msg enc pkSf) := by
  intro m₁ m₂ h
  unfold slMsg Scheme.Shrincs.statelessMessage at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
  obtain ⟨hlen, hrest⟩ := h
  have hctx1 := enc.ctx_le m₁
  have hctx2 := enc.ctx_le m₂
  have hlen' : (enc.ctx m₁).length = (enc.ctx m₂).length := by
    have hnat := congrArg UInt8.toNat hlen
    simp only [UInt8.toNat_ofNat'] at hnat
    omega
  obtain ⟨hctx, htail⟩ := List.append_inj hrest hlen'
  have hbody : enc.body m₁ = enc.body m₂ := List.append_cancel_left htail
  exact henc (Prod.ext hctx hbody)

/-- `Shrincs.slVerify` is literally `SLHDSA.GeneralScheme.verifyInternal` on `slMsg`. -/
theorem slVerify_eq_verifyInternal [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl pkSf : pr.Y)
    (m : Msg) (σ : Stateless.Sig pr) :
    slVerify pr Msg enc pk pkSl pkSf m σ =
      SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA (slMsg pr Msg enc pkSf m) σ
        ⟨pk, pkSl⟩ := by
  unfold slVerify Stateless.verify SLHDSA.External.verifyPure Stateless.publicKey slMsg
  rw [SLHDSA.External.encodePureMessage_eq_ok _ _ (enc.ctx_le m)]

end MsgBridge

/-! ## 2. Eager-secret SLH-DSA primitive bundle `prEager` -/

section PrEager

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- The SLH-DSA primitive bundle with `SkSeed := SlSecAdrs vp → pr.Y` and `PRF` reading the eager
uniform secret table `slSecOf pr u`. Shares `PkSeed`, `Y`, `F`, `H`, `Tl`, `Hmsg`, and `yToBytes`
definitionally with `pr.toSLHDSA`. -/
@[reducible] def prEager : SLHDSA.Primitives vp.sl.params where
  PkSeed := pr.PkSeed
  SkSeed := SlSecAdrs vp → pr.Y
  SkPrf := pr.SkPrf
  Y := pr.Y
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ u a => slSecOf pr u a
  PRFmsg := pr.PRFmsgSl
  yToBytes := pr.yToBytes
  Thash := pr.Th
  Hmsg := pr.HmsgSl

/-- `ByteLaws` for `prEager` from `Function.Injective pr.yToBytes`. -/
theorem prEager_byteLaws (hinj : Function.Injective pr.yToBytes) :
    (prEager pr).core.ByteLaws := ⟨hinj⟩

/-- Convert a `Stateless.Sig pr` (`SignatureCore vp.sl pr.toSLHDSA.core`) into the structurally
identical `SignatureCore vp.sl (prEager pr).core` (same `Y` entries, different `SkSeed` phantom). -/
def toEagerSig (σ : Stateless.Sig pr) :
    SLHDSA.GeneralScheme.SignatureCore vp.sl (prEager pr).core where
  randomness := σ.randomness
  fors := σ.fors.map fun t => ⟨t.sk, t.auth⟩
  hypertree := σ.hypertree.map fun x => ⟨x.wots, x.auth⟩

/-- `chain` on `prEager` equals `chain` on `pr.toSLHDSA`. -/
theorem chain_prEager_eq (pk : pr.PkSeed) (adrs : Adrs) (x : pr.Y) (i : ℕ) :
    ∀ n, chain (prEager pr) pk adrs x i n = chain pr.toSLHDSA pk adrs x i n
  | 0 => by rw [SLHDSA.chain_zero, SLHDSA.chain_zero]
  | n + 1 => by
    rw [SLHDSA.chain_succ, SLHDSA.chain_succ, chain_prEager_eq pk adrs x i n]

/-- `forsPkFromSig` is invariant under `toEagerSig`. -/
theorem forsPkFromSig_toEager (sig : SLHDSA.ForsSigCore vp.sl.params pr.toSLHDSA.core)
    (md : List Byte) (pk : pr.PkSeed) (adrs : Adrs) :
    SLHDSA.forsPkFromSig (prEager pr) (sig.map fun t => ⟨t.sk, t.auth⟩) md pk adrs =
      SLHDSA.forsPkFromSig pr.toSLHDSA sig md pk adrs := by
  rw [forsPkFromSig_eq_tl_recoveredRoots, forsPkFromSig_eq_tl_recoveredRoots]
  change pr.Th pk (forsPkAdrs adrs) _ = pr.Th pk (forsPkAdrs adrs) _
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [Vector.getElem_toList]
    have hi : i < vp.sl.params.k := by simpa using hi₂
    rw [forsRecoveredRoots_getElem, forsRecoveredRoots_getElem]
    simp only [Vector.getElem_map]
    rfl

/-- `xmssPkFromSig` is invariant under `toEagerSig`. -/
theorem xmssPkFromSig_toEager (idx : ℕ) (sig : SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core)
    (msg : pr.Y) (pk : pr.PkSeed) (adrs : Adrs) :
    SLHDSA.xmssPkFromSig (prEager pr) idx ⟨sig.wots, sig.auth⟩ msg pk adrs =
      SLHDSA.xmssPkFromSig pr.toSLHDSA idx sig msg pk adrs := by
  rw [SLHDSA.xmssPkFromSig_eq_climb, SLHDSA.xmssPkFromSig_eq_climb]
  have hwots : SLHDSA.wotsPkFromSig (prEager pr) sig.wots msg pk (wotsLeafAdrs adrs idx) =
      SLHDSA.wotsPkFromSig pr.toSLHDSA sig.wots msg pk (wotsLeafAdrs adrs idx) := by
    rw [SLHDSA.wotsPkFromSig_eq_tl, SLHDSA.wotsPkFromSig_eq_tl]
    change pr.Th pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) _ =
      pr.Th pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) _
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [Vector.getElem_toList, SLHDSA.wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn]
      exact chain_prEager_eq pr pk _ _ _ _
  rw [hwots]
  rfl

/-- `GeneralHypertree.recoverFromPosition` is invariant under mapping XMSS signatures to `prEager`. -/
theorem recoverFromPosition_toEager (pk : pr.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp.sl) (hrem : pos.layer.val + layers = vp.sl.params.d)
      (msg : pr.Y) (sigs : Vector (SLHDSA.XmssSig vp.sl.params pr.toSLHDSA.core) layers),
      SLHDSA.GeneralHypertree.recoverFromPosition vp.sl (prEager pr) pk pos layers hrem msg
        (sigs.map fun x => ⟨x.wots, x.auth⟩) =
      SLHDSA.GeneralHypertree.recoverFromPosition vp.sl pr.toSLHDSA pk pos layers hrem msg sigs := by
  intro layers
  induction layers using Nat.twoStepInduction with
  | zero => intro _ _ _ _; rfl
  | one =>
    intro pos hrem msg sigs
    simp only [SLHDSA.GeneralHypertree.recoverFromPosition]
    have hhead : (sigs.map fun x => (⟨x.wots, x.auth⟩ : SLHDSA.XmssSig vp.sl.params (prEager pr).core)).head =
        ⟨sigs.head.wots, sigs.head.auth⟩ := by simp [Vector.head]
    rw [hhead]
    exact xmssPkFromSig_toEager pr pos.leaf.val sigs.head msg pk pos.toAdrs
  | more layers _ ih =>
    intro pos hrem msg sigs
    simp only [SLHDSA.GeneralHypertree.recoverFromPosition]
    have hhead : (sigs.map fun x => (⟨x.wots, x.auth⟩ : SLHDSA.XmssSig vp.sl.params (prEager pr).core)).head =
        ⟨sigs.head.wots, sigs.head.auth⟩ := by simp [Vector.head]
    have htail : (sigs.map fun x => (⟨x.wots, x.auth⟩ : SLHDSA.XmssSig vp.sl.params (prEager pr).core)).tail =
        sigs.tail.map fun x => ⟨x.wots, x.auth⟩ := by
      apply Vector.ext; intro i hi; simp [Vector.tail_eq_cast_extract]
    rw [hhead, htail, xmssPkFromSig_toEager]
    exact ih _ _ _ _

/-- Verification on `prEager` via `toEagerSig` equals verification on `pr.toSLHDSA`. -/
theorem verifyInternal_prEager_eq [DecidableEq pr.Y] (msg : List Byte) (σ : Stateless.Sig pr)
    (pk : pr.PkSeed) (pkSl : pr.Y) :
    SLHDSA.GeneralScheme.verifyInternal vp.sl (prEager pr) msg (toEagerSig pr σ) ⟨pk, pkSl⟩ =
      SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA msg σ ⟨pk, pkSl⟩ := by
  rw [SLHDSA.GeneralScheme.verifyInternal_eq_decide, SLHDSA.GeneralScheme.verifyInternal_eq_decide]
  have hpk : SLHDSA.GeneralHypertree.pkFromSig vp.sl (prEager pr)
        (SLHDSA.forsPkFromSig (prEager pr) (toEagerSig pr σ).fors
          (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)).md.toList pk
          (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)).forsAdrs)
        (toEagerSig pr σ).hypertree pk
        (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)) =
      SLHDSA.GeneralHypertree.pkFromSig vp.sl pr.toSLHDSA
        (SLHDSA.forsPkFromSig pr.toSLHDSA σ.fors
          (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)).md.toList pk
          (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)).forsAdrs)
        σ.hypertree pk
        (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)) := by
    dsimp only [toEagerSig]
    rw [forsPkFromSig_toEager,
      SLHDSA.GeneralHypertree.pkFromSig_eq_recoverFromPosition,
      SLHDSA.GeneralHypertree.pkFromSig_eq_recoverFromPosition]
    exact recoverFromPosition_toEager pr pk vp.sl.params.d _ _ _ σ.hypertree
  change decide (SLHDSA.GeneralHypertree.pkFromSig vp.sl (prEager pr)
      (SLHDSA.forsPkFromSig (prEager pr) (toEagerSig pr σ).fors
        (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)).md.toList pk
        (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)).forsAdrs)
      (toEagerSig pr σ).hypertree pk
      (splitDigest vp.sl.params (pr.HmsgSl σ.randomness pk pkSl msg)) = pkSl) =
    decide (_ = pkSl)
  simp only [hpk]

/-- `honestVal` at a FORS leaf address equals `forsLeaf` of `prEager`. -/
theorem honestVal_eq_forsLeaf (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (t : ℕ) :
    honestVal pr pk u (forsNodeAdrs b 0 t) = forsLeaf (prEager pr) u pk b t := by
  rw [honestVal_forsLeaf]
  rfl

/-- `honestVal` at a FORS internal node equals `PerfectMerkleTree.merkleRoot` of `prEager`. -/
theorem honestVal_eq_forsNode (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    ∀ z t,
      honestVal pr pk u (forsNodeAdrs b z t) =
        PerfectMerkleTree.merkleRoot (forsLeaf (prEager pr) u pk b)
          (forsNodeHash (prEager pr) pk b) z t
  | 0, t => honestVal_eq_forsLeaf pr pk u b t
  | z + 1, t => by
    rw [honestVal_forsNode_succ, PerfectMerkleTree.merkleRoot_succ,
      honestVal_eq_forsNode pk u b z (2 * t),
      honestVal_eq_forsNode pk u b z (2 * t + 1)]
    rfl

/-- `honestVal` at a FORS root compression address equals `forsPkGen` of `prEager`. -/
theorem honestVal_eq_forsPkGen (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestVal pr pk u (forsPkAdrs b) = forsPkGen (prEager pr) u pk b := by
  rw [honestVal_forsPk, forsPkGen_eq_tl_honestRoots]
  change pr.Th pk (forsPkAdrs b) _ = pr.Th pk (forsPkAdrs b) _
  congr 1
  apply List.ext_getElem
  · simp [ValidatedParams.sl, Params.slParams]
  · intro i hi₁ hi₂
    simp only [Vector.getElem_toList, Vector.getElem_ofFn]
    rw [forsHonestRoots_getElem, SLHDSA.forsRoot_eq_merkleRoot]
    exact honestVal_eq_forsNode pr pk u b vp.params.a i

/-- `honestVal` at a WOTS chain step address `(t : ℕ)` equals `chain` of `prEager` from step `0`
for `t + 1` steps. -/
theorem honestVal_eq_wotsChain (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (c : ℕ) :
    ∀ t,
      honestVal pr pk u ((wotsChainAdrs b c).setHashAddress t) =
        chain (prEager pr) pk (wotsChainAdrs b c) (slSecOf pr u (wotsSkAdrs b c)) 0 (t + 1)
  | 0 => by
    rw [honestVal_wotsStep_zero, SLHDSA.chain_succ, SLHDSA.chain_zero]
    rfl
  | t + 1 => by
    rw [honestVal_wotsStep_succ, honestVal_eq_wotsChain pk u b c t]
    rw [SLHDSA.chain_succ (prEager pr) pk (wotsChainAdrs b c) (slSecOf pr u (wotsSkAdrs b c)) 0 (t + 1)]
    simp only [Nat.zero_add]
    rfl

/-- `honestVal` at a WOTS public-key compression address equals `wotsPkGen` of `prEager`. -/
theorem honestVal_eq_wotsPkGen (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestVal pr pk u (wotsPkAdrs b) = wotsPkGen (prEager pr) u pk b := by
  have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
  rw [honestVal_wotsPk, SLHDSA.wotsPkGen_eq_tl]
  change pr.Th pk (wotsPkAdrs b) _ = pr.Th pk (wotsPkAdrs b) _
  congr 1
  apply List.ext_getElem
  · simp [Params.lsl_eq_len vp.valid]
  · intro i hi₁ hi₂
    simp only [Vector.getElem_toList, Vector.getElem_ofFn, SLHDSA.wotsPkGenTops_eq_ofFn]
    rw [honestVal_eq_wotsChain]
    have hsub : vp.params.w - 2 + 1 = vp.sl.params.w - 1 := by
      change vp.params.w - 2 + 1 = vp.params.w - 1; omega
    rw [hsub]

/-- `honestVal` at an XMSS cell `(z, t)` equals `xmssNode` of `prEager`. -/
theorem honestVal_eq_xmssCell (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    ∀ z t,
      honestVal pr pk u (xmssCellAdrs b z t) = xmssNode (prEager pr) u pk b z t
  | 0, t => by
    rw [SLHDSA.xmssNode_zero, SLHDSA.xmssLeaf_eq_wotsPkGen]
    exact honestVal_eq_wotsPkGen pr pk u (wotsLeafAdrs b t)
  | z + 1, t => by
    rw [honestVal_xmssCell_succ, SLHDSA.xmssNode_succ,
      honestVal_eq_xmssCell pk u b z (2 * t), honestVal_eq_xmssCell pk u b z (2 * t + 1)]
    rfl

/-- `honestVal` at an XMSS internal node (`1 ≤ z`) equals `xmssNode` of `prEager`. -/
theorem honestVal_eq_xmssNode (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs)
    {z : ℕ} (hz : 0 < z) (t : ℕ) :
    honestVal pr pk u (xmssNodeAdrs b z t) = xmssNode (prEager pr) u pk b z t := by
  obtain ⟨z', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hz)
  exact honestVal_eq_xmssCell pr pk u b (z' + 1) t

/-- `honestVal` at the root of an XMSS tree equals `xmssRoot` of `prEager`. -/
theorem honestVal_eq_xmssRoot (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestVal pr pk u (xmssNodeAdrs b vp.sl.params.hp 0) = xmssRoot (prEager pr) u pk b :=
  honestVal_eq_xmssNode pr pk u b vp.valid.hp_pos 0

/-- `honestVal` at `topRootAdrs vp` equals `GeneralHypertree.root` of `prEager`. -/
theorem honestVal_eq_topRoot (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    honestVal pr pk u (topRootAdrs vp) =
      SLHDSA.GeneralHypertree.root vp.sl (prEager pr) u pk := by
  rw [SLHDSA.GeneralHypertree.root_eq_xmssRoot, topRootAdrs, LayerTreeCoord.top_toAdrs]
  exact honestVal_eq_xmssRoot pr pk u (SLHDSA.GeneralHypertree.layerAdrs (vp.sl.params.d - 1) 0)

/-- `slRootDet` equals `GeneralHypertree.root` on `prEager`. -/
theorem slRootDet_eq_prEager_root (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    slRootDet pr pk u = SLHDSA.GeneralHypertree.root vp.sl (prEager pr) u pk :=
  (slRootDet_eq_honestVal pr pk u).trans (honestVal_eq_topRoot pr pk u)

/-- The honest FORS child pair at `(z, t)` (`0 < z`) equals the pair of `honestVal` children. -/
theorem forsHonestChildren_eq_honestVal (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs)
    (z t : ℕ) :
    forsHonestChildren (prEager pr) u pk b z t =
      (honestVal pr pk u (forsNodeAdrs b (z - 1) (2 * t)),
       honestVal pr pk u (forsNodeAdrs b (z - 1) (2 * t + 1))) := by
  rw [forsHonestChildren_eq]
  simp only [Prod.mk.injEq]
  exact ⟨(honestVal_eq_forsNode pr pk u b (z - 1) (2 * t)).symm,
    (honestVal_eq_forsNode pr pk u b (z - 1) (2 * t + 1)).symm⟩

/-- The honest XMSS child pair at `(z, t)` (`0 < z`) equals the pair of `honestVal` children. -/
theorem xmssHonestChildren_eq_honestVal (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs)
    (z t : ℕ) :
    xmssHonestChildren (prEager pr) u pk b z t =
      (honestVal pr pk u (xmssCellAdrs b (z - 1) (2 * t)),
       honestVal pr pk u (xmssCellAdrs b (z - 1) (2 * t + 1))) := by
  rw [xmssHonestChildren_eq]
  simp only [Prod.mk.injEq]
  exact ⟨(honestVal_eq_xmssCell pr pk u b (z - 1) (2 * t)).symm,
    (honestVal_eq_xmssCell pr pk u b (z - 1) (2 * t + 1)).symm⟩

end PrEager

/-! ## 3. Routed Stage-1 `slVirtualTreeM` execution for stateless collection games -/

section RoutedVirtualTree

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- `slTreeAddresses vp` has no duplicate addresses (from VCVio's `nodup_structuralLedgers_append`). -/
theorem nodup_slTreeAddresses : (slTreeAddresses vp).Nodup :=
  nodup_structuralLedgers_append vp.sl

/-- Membership in `slTreeAddresses vp` coincides with membership in `constructionAddresses vp.sl`. -/
theorem mem_slTreeAddresses_iff {a : Adrs} :
    a ∈ slTreeAddresses vp ↔ a ∈ constructionAddresses vp.sl := by
  simp [slTreeAddresses, mem_constructionAddresses_iff]

/-- Every address in `constructionAddresses vp.sl` is a stateless address. -/
theorem isStateless_of_mem_constructionAddresses {a : Adrs}
    (ha : a ∈ constructionAddresses vp.sl) : Scheme.IsStateless a := by
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨.forsTree, rfl⟩
  · simp only [forsTreeAddresses, List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨.forsTree, rfl⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨.forsRoots, rfl⟩
  · simp only [wotsStepAddresses, List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨.wotsHash, rfl⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨.wotsPk, rfl⟩
  · simp only [xmssNodeAddresses, List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨.tree, rfl⟩

/-- Extract the exact honest member message passed to `evalNodeM` at address `a` given a sound
table `tbl` (with `tbl` already populated at all children of `a`). -/
def evalNodeInput (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) (a : Adrs) :
    Option ((i : Primitives.Member) × pr.MemberMsg i) :=
  match a.type with
  | 0 =>
    let x := if a.word3 = 0 then slSecOf pr u (wotsSkAdrs a a.word2)
             else (tbl (a.setHashAddress (a.word3 - 1))).getD default
    some ⟨.F, x⟩
  | 1 =>
    let v : Vector pr.Y vp.params.lsl := Vector.ofFn fun i : Fin vp.params.lsl =>
      (tbl ((wotsChainAdrs a i.val).setHashAddress (vp.params.w - 2))).getD default
    some ⟨.thLsl, v⟩
  | 2 =>
    if a.word2 = 0 then none
    else if a.word2 = 1 then
      let l := (tbl (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3)))).getD default
      let r := (tbl (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3 + 1)))).getD default
      some ⟨.H, (l, r)⟩
    else
      let l := (tbl (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3))).getD default
      let r := (tbl (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1))).getD default
      some ⟨.H, (l, r)⟩
  | 3 =>
    if a.word2 = 0 then
      some ⟨.F, slSecOf pr u (forsSkAdrs a a.word3)⟩
    else
      let l := (tbl (forsNodeAdrs a (a.word2 - 1) (2 * a.word3))).getD default
      let r := (tbl (forsNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1))).getD default
      some ⟨.H, (l, r)⟩
  | 4 =>
    let v : Vector pr.Y vp.params.k := Vector.ofFn fun i : Fin vp.params.k =>
      (tbl (forsNodeAdrs a vp.params.a i.val)).getD default
    some ⟨.thK, v⟩
  | _ => none

/-- `evalNodeM` agrees with `evalNodeInput`: if `evalNodeInput` returns `some ⟨i, msg⟩`, then
`evalNodeM` makes the single call `collCall i a msg`; if `none`, it returns `pure default`. -/
theorem evalNodeM_eq_of_input {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) (a : Adrs) :
    evalNodeM pr collCall u tbl a =
      match evalNodeInput pr u tbl a with
      | some ⟨i, msg⟩ => collCall i a msg
      | none => pure default := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  rcases ty with _ | _ | _ | _ | _ | ty' <;> simp only [evalNodeM, evalNodeInput]
  · by_cases hw3 : w3 = 0 <;> simp [hw3]
  · by_cases hw2 : w2 = 0
    · simp [hw2]
    · by_cases hw2' : w2 = 1 <;> simp [hw2, hw2']
  · by_cases hw2 : w2 = 0 <;> simp [hw2]

/-- Deterministic honest input to `Th_λ` at any address `a ∈ constructionAddresses vp.sl`
(evaluated directly against `honestVal`). -/
def honestInput (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (a : Adrs) :
    Option ((i : Primitives.Member) × pr.MemberMsg i) :=
  evalNodeInput pr u (fun z => some (honestVal pr pk u z)) a

/-- Syntactic validity of an address for `evalNodeInput`: every address in
`constructionAddresses vp.sl` satisfies this predicate, so `evalNodeInput` always returns `some`. -/
def ValidNodeAdrs (a : Adrs) : Prop :=
  a.type ≤ 4 ∧ (a.type = 2 → a.word2 ≠ 0)

theorem validNodeAdrs_of_mem_constructionAddresses {a : Adrs}
    (ha : a ∈ constructionAddresses vp.sl) : ValidNodeAdrs a := by
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨by change 3 ≤ 4; omega, fun h => by cases h⟩
  · simp only [forsTreeAddresses, List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨by change 3 ≤ 4; omega, fun h => by cases h⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨by change 4 ≤ 4; omega, fun h => by cases h⟩
  · simp only [wotsStepAddresses, List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨by change 0 ≤ 4; omega, fun h => by cases h⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨by change 1 ≤ 4; omega, fun h => by cases h⟩
  · simp only [xmssNodeAddresses, List.mem_map] at h
    obtain ⟨⟨coord, zi⟩, hmem, rfl⟩ := h
    have hzi : zi ∈ perfectInternalCoords vp.sl.params.hp := (List.mem_product.1 hmem).2
    have hz : 0 < zi.1 := perfectInternalCoords_height_pos hzi
    refine ⟨by change 2 ≤ 4; omega, fun _ => ?_⟩
    change zi.1 ≠ 0
    omega

theorem evalNodeInput_isSome_of_valid (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    {a : Adrs} (ha : ValidNodeAdrs a) : (evalNodeInput pr u tbl a).isSome := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  rcases ha with ⟨hle, h2⟩
  rcases ty with _ | _ | _ | _ | _ | ty'
  · simp [evalNodeInput]
  · simp [evalNodeInput]
  · have hw2 : w2 ≠ 0 := h2 rfl
    simp only [evalNodeInput, hw2, ↓reduceIte]
    split_ifs <;> rfl
  · simp only [evalNodeInput]; split_ifs <;> rfl
  · simp [evalNodeInput]
  · dsimp only at hle; omega

/-- Generic fold execution of `slVirtualTreeM` over a `Nodup` list `l` of valid node addresses:
if `collCall` answers every unvisited address deterministically with `pr.memberEval i pk a msg`
and transitions state via `stepS`, then the fold returns the exact deterministic table and
maintains the invariant over visited addresses. -/
theorem simulateQ_foldlM_evalNodeM {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (Inv : List Adrs → σ → Prop)
    (stepS : (i : Primitives.Member) → Adrs → pr.MemberMsg i → σ → σ)
    (hcall : ∀ visited s i a msg, Inv visited s → a ∉ visited →
      (simulateQ impl (collCall i a msg)).run s =
        pure (pr.memberEval i pk a msg, stepS i a msg s))
    (hinv : ∀ visited s i a msg, Inv visited s → a ∉ visited →
      Inv (visited ++ [a]) (stepS i a msg s)) :
    ∀ (l : List Adrs) (visited : List Adrs) (tbl : Adrs → Option pr.Y) (s : σ),
      l.Nodup → (∀ a ∈ l, ValidNodeAdrs a) → (∀ a ∈ l, a ∉ visited) → Inv visited s →
      ∃ s', Inv (visited ++ l) s' ∧
        (simulateQ impl (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr collCall u tbl a
          return Function.update tbl a (some v)) tbl)).run s =
        pure (l.foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) tbl, s') := by
  intro l
  induction l with
  | nil =>
    intro visited tbl s _ _ _ hs
    exact ⟨s, by simpa using hs, by simp⟩
  | cons a as ih =>
    intro visited tbl s hnd hval hdisj hs
    rw [List.nodup_cons] at hnd
    have ha_not : a ∉ visited := hdisj a (by simp)
    have ha_val : ValidNodeAdrs a := hval a (by simp)
    obtain ⟨⟨i, msg⟩, hinp⟩ := Option.isSome_iff_exists.1 (evalNodeInput_isSome_of_valid pr u tbl ha_val)
    have hrun₁ : (simulateQ impl (evalNodeM pr collCall u tbl a)).run s =
        pure (evalNodeDet pr pk u tbl a, stepS i a msg s) := by
      rw [evalNodeM_eq_of_input, hinp]
      unfold evalNodeDet
      rw [evalNodeM_eq_of_input, hinp]
      exact hcall visited s i a msg hs ha_not
    have hs₁ : Inv (visited ++ [a]) (stepS i a msg s) := hinv visited s i a msg hs ha_not
    have hdisj' : ∀ b ∈ as, b ∉ visited ++ [a] := by
      intro b hb hmem
      rcases List.mem_append.1 hmem with h1 | h2
      · exact hdisj b (by simp [hb]) h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact hnd.1 hb
    obtain ⟨s₂, hs₂, hrun₂⟩ := ih (visited ++ [a])
      (Function.update tbl a (some (evalNodeDet pr pk u tbl a)))
      (stepS i a msg s) hnd.2 (fun b hb => hval b (by simp [hb])) hdisj' hs₁
    refine ⟨s₂, by simpa [List.append_assoc] using hs₂, ?_⟩
    simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, hrun₁, pure_bind,
      simulateQ_pure, StateT.run_pure, List.foldl_cons]
    exact hrun₂

/-- Deterministic target list recorded when routing addresses `a ∈ l` satisfying `isTarget a`
to a challenge oracle for member `mem`. -/
def routedTargetsAux (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) :
    List Adrs → (Adrs → Option pr.Y) → List (Adrs × pr.MemberMsg mem)
  | [], _ => []
  | a :: as, tbl =>
    let tbl' := Function.update tbl a (some (evalNodeDet pr pk u tbl a))
    let rest := routedTargetsAux pk u mem isTarget as tbl'
    if isTarget a then
      match evalNodeInput pr u tbl a with
      | some ⟨i, msg⟩ =>
        if h : i = mem then (a, h ▸ msg) :: rest else rest
      | none => rest
    else rest

/-- The deterministic list of `(a, msg)` targets committed by `slVirtualTreeM` when addresses
satisfying `isTarget` are routed to the challenge oracle of member `mem`. -/
def routedTargets (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) : List (Adrs × pr.MemberMsg mem) :=
  routedTargetsAux pr pk u mem isTarget (slTreeAddresses vp) (fun _ => none)

/-- Every `(a, msg)` in `routedTargetsAux` has `isTarget a = true`, and if `a ∈ l` has
`isTarget a = true` and member `mem` then `(a, msg)` appears in `routedTargetsAux`. -/
theorem routedTargetsAux_length_le (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) :
    ∀ l tbl, (routedTargetsAux pr pk u mem isTarget l tbl).length ≤ l.countP isTarget
  | [], _ => le_rfl
  | a :: as, tbl => by
    simp only [routedTargetsAux, List.countP_cons]
    have ih := routedTargetsAux_length_le pk u mem isTarget as
      (Function.update tbl a (some (evalNodeDet pr pk u tbl a)))
    cases ht : isTarget a
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      cases evalNodeInput pr u tbl a with
      | none => exact ih.trans (Nat.le_succ _)
      | some im =>
        rcases im with ⟨i, msg⟩
        by_cases h : i = mem
        · simp only [h, ↓reduceDIte, List.length_cons]
          exact Nat.succ_le_succ ih
        · simp only [h, ↓reduceDIte]
          exact ih.trans (Nat.le_succ _)

/-- **Routed `slVirtualTreeM` against `SM_DT_TCR_oracles`**: routing all addresses `a` with
`isTarget a = true` (which must belong to member `mem`) to the `SM-TCR` challenge oracle and all
other addresses to `O_coll`, starting from `([], tws₀)` with only stateful tweaks in `tws₀` and
`(slTreeAddresses vp).countP isTarget ≤ p`, runs deterministically with ZERO refusals,
returns `slVirtualTreeDet pr pk u`, and records exact challenge history `routedTargets`. -/
theorem simulateQ_slVirtualTreeM_routed_tcr [SampleableType pr.PkSeed]
    (mem : Primitives.Member) (isTarget : Adrs → Bool) (p : ℕ)
    (hmem : ∀ a ∈ constructionAddresses vp.sl, isTarget a = true →
      ∀ u tbl, ∃ msg, evalNodeInput pr u tbl a = some ⟨mem, msg⟩)
    (hp : (slTreeAddresses vp).countP isTarget ≤ p)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tws₀ : List Adrs) (htws₀ : ∀ t ∈ tws₀, Scheme.IsStateful t) :
    let prob := Notions.smTcrMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p
    let collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i →
        OracleComp (Fxmss.TcrOracleSpec prob) pr.Y := fun i a msg =>
      if h : isTarget a = true ∧ i = mem then do
        let y ← (liftM ((Fxmss.TcrOracleSpec prob).query (.inr (.inl (a, h.2 ▸ msg)))) :
          OracleComp (Fxmss.TcrOracleSpec prob) (Option pr.Y))
        return y.getD default
      else do
        let y ← (liftM ((Fxmss.TcrOracleSpec prob).query (.inr (.inr ⟨some i, a, msg⟩))) :
          OracleComp (Fxmss.TcrOracleSpec prob) (Option pr.Y))
        return y.getD default
    ∃ tws', (∀ t ∈ tws', t ∈ tws₀ ∨ Scheme.IsStateless t) ∧
      (simulateQ (SM_DT_TCR_oracles prob pk) (slVirtualTreeM pr collCall u)).run ([], tws₀) =
        pure (slVirtualTreeDet pr pk u, (routedTargets pr pk u mem isTarget, tws')) := by
  intro prob collCall
  -- Prove by induction over a suffix `l` of `slTreeAddresses vp`
  have hfold : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y)
      (qs : List (Adrs × pr.MemberMsg mem)) (tws : List Adrs),
      l.Nodup →
      (∀ a ∈ l, a ∈ constructionAddresses vp.sl) →
      (∀ a ∈ l, TweakFresh Prod.fst qs tws a) →
      qs.length + l.countP isTarget ≤ p →
      (∀ t ∈ tws, t ∈ tws₀ ∨ Scheme.IsStateless t) →
      ∃ tws', (∀ t ∈ tws', t ∈ tws₀ ∨ Scheme.IsStateless t) ∧
        (simulateQ (SM_DT_TCR_oracles prob pk) (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr collCall u tbl a
          return Function.update tbl a (some v)) tbl)).run (qs, tws) =
        pure (l.foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) tbl,
          (qs ++ routedTargetsAux pr pk u mem isTarget l tbl, tws')) := by
    intro l
    induction l with
    | nil =>
      intro tbl qs tws _ _ _ _ htws
      exact ⟨tws, htws, by simp [routedTargetsAux]⟩
    | cons a as ih =>
      intro tbl qs tws hnd hsub hfr hcap htws
      rw [List.nodup_cons] at hnd
      have ha_ca : a ∈ constructionAddresses vp.sl := hsub a (by simp)
      have ha_val : ValidNodeAdrs a := validNodeAdrs_of_mem_constructionAddresses ha_ca
      have ha_sl : Scheme.IsStateless a := isStateless_of_mem_constructionAddresses ha_ca
      have ha_fr : TweakFresh Prod.fst qs tws a := hfr a (by simp)
      obtain ⟨⟨i, msg⟩, hinp⟩ := Option.isSome_iff_exists.1 (evalNodeInput_isSome_of_valid pr u tbl ha_val)
      have hcnt : (a :: as).countP isTarget = (if isTarget a then 1 else 0) + as.countP isTarget := by
        simp [List.countP_cons, Nat.add_comm]
      by_cases ht : isTarget a = true
      · obtain ⟨msg', hinp'⟩ := hmem a ha_ca ht u tbl
        rw [hinp] at hinp'
        have hi_eq : i = mem := congrArg Sigma.fst (Option.some.inj hinp')
        subst hi_eq
        have hlt : qs.length < p := by
          rw [hcnt] at hcap; simp [ht] at hcap; omega
        have hstep : (simulateQ (SM_DT_TCR_oracles prob pk)
            (evalNodeM pr collCall u tbl a)).run (qs, tws) =
            pure (evalNodeDet pr pk u tbl a, (qs ++ [(a, msg)], tws)) := by
          rw [evalNodeM_eq_of_input, hinp]
          unfold evalNodeDet
          rw [evalNodeM_eq_of_input, hinp]
          have hnotle : ¬ p ≤ qs.length := Nat.not_le.mpr hlt
          simp only [collCall, ht, and_self, ↓reduceDIte, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, simulateQ_pure, StateT.run_pure, SM_DT_TCR_oracles,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, SM_DT_TCR_challengeOracle,
            StateT.run_get, pure_bind, prob, Notions.smTcrMemberProblem, hnotle, ha_fr]
          rfl
        have hfr' : ∀ b ∈ as, TweakFresh Prod.fst (qs ++ [(a, msg)]) tws b := by
          intro b hb
          have hb_fr := hfr b (by simp [hb])
          have hba : a ≠ b := fun h => hnd.1 (h ▸ hb)
          simpa [TweakFresh, TweakReserved, hba] using hb_fr
        have hcap' : (qs ++ [(a, msg)]).length + as.countP isTarget ≤ p := by
          rw [List.length_append, List.length_singleton]
          rw [hcnt] at hcap; simp [ht] at hcap; omega
        obtain ⟨tws', htws', hih⟩ := ih
          (Function.update tbl a (some (evalNodeDet pr pk u tbl a)))
          (qs ++ [(a, msg)]) tws hnd.2 (fun b hb => hsub b (by simp [hb])) hfr' hcap' htws
        refine ⟨tws', htws', ?_⟩
        simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, hstep, pure_bind,
          simulateQ_pure, StateT.run_pure, List.foldl_cons]
        rw [hih]
        simp only [routedTargetsAux, ht, ↓reduceIte, hinp, ↓reduceDIte, List.append_assoc,
          List.singleton_append]
      · have hnot : ¬ (isTarget a = true ∧ i = mem) := fun h => ht h.1
        have hstep : (simulateQ (SM_DT_TCR_oracles prob pk)
            (evalNodeM pr collCall u tbl a)).run (qs, tws) =
            pure (evalNodeDet pr pk u tbl a, (qs, tws ++ [a])) := by
          rw [evalNodeM_eq_of_input, hinp]
          unfold evalNodeDet
          rw [evalNodeM_eq_of_input, hinp]
          have hnotres : ¬ TweakReserved Prod.fst qs a := ha_fr.1
          simp only [collCall, hnot, ↓reduceDIte, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, simulateQ_pure, StateT.run_pure, SM_DT_TCR_oracles,
            QueryImpl.add_apply_inr, collectionOracle, StateT.run_get, pure_bind,
            hnotres, ↓reduceIte, StateT.run_set, Option.getD_some]
          rfl
        have hfr' : ∀ b ∈ as, TweakFresh Prod.fst qs (tws ++ [a]) b := by
          intro b hb
          have hb_fr := hfr b (by simp [hb])
          have hba : b ≠ a := fun h => hnd.1 (h ▸ hb)
          simpa [TweakFresh, TweakReserved, hba] using hb_fr
        have hcap' : qs.length + as.countP isTarget ≤ p := by
          rw [hcnt] at hcap; simp [ht] at hcap; exact hcap
        have htws1 : ∀ t ∈ tws ++ [a], t ∈ tws₀ ∨ Scheme.IsStateless t := by
          intro t ht'
          rcases List.mem_append.1 ht' with h1 | h2
          · exact htws t h1
          · simp only [List.mem_singleton] at h2; subst h2; exact Or.inr ha_sl
        obtain ⟨tws', htws', hih⟩ := ih
          (Function.update tbl a (some (evalNodeDet pr pk u tbl a)))
          qs (tws ++ [a]) hnd.2 (fun b hb => hsub b (by simp [hb])) hfr' hcap' htws1
        refine ⟨tws', htws', ?_⟩
        simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, hstep, pure_bind,
          simulateQ_pure, StateT.run_pure, List.foldl_cons]
        rw [hih]
        simp only [routedTargetsAux, Bool.eq_false_iff.2 ht, Bool.false_eq_true, ↓reduceIte]
  have hfr0 : ∀ a ∈ slTreeAddresses vp, TweakFresh Prod.fst ([] : List (Adrs × pr.MemberMsg mem)) tws₀ a := by
    intro a ha
    refine ⟨by simp [TweakReserved], fun hmem => ?_⟩
    exact Scheme.not_isStateful_of_isStateless
      (isStateless_of_mem_constructionAddresses (mem_slTreeAddresses_iff.1 ha)) (htws₀ a hmem)
  obtain ⟨tws', htws', hrun⟩ := hfold (slTreeAddresses vp) (fun _ => none) [] tws₀
    (nodup_slTreeAddresses (vp := vp)) (fun _ h => mem_slTreeAddresses_iff.1 h) hfr0
    (by simpa using hp) (fun _ h => Or.inl h)
  refine ⟨tws', htws', ?_⟩
  unfold slVirtualTreeM slVirtualTreeDet
  simp only [simulateQ_bind, StateT.run_bind, hrun, pure_bind, simulateQ_pure, StateT.run_pure,
    List.nil_append]
  have hdet_eq :
      Id.run ((slTreeAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a
        return Function.update tbl a (some v)) (fun _ => none)) =
      (slTreeAddresses vp).foldl
        (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) (fun _ => none) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
        Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a
          return Function.update tbl a (some v)) tbl) =
        l.foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) tbl := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a as ih => intro tbl; exact ih _
    exact haux _ _
  change (pure (((((slTreeAddresses vp).foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) (fun _ => none)) (topRootAdrs vp)).getD default, (slTreeAddresses vp).foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) (fun _ => none)), (routedTargets pr pk u mem isTarget, tws')) : ProbComp _) = _
  rw [← hdet_eq]
  rfl

/-- **Routed `slVirtualTreeM` against `SM_DT_DSPR_oracles`** (identical to `routed_tcr` because
`SM_DT_DSPR_challengeOracle` has the exact same state & refusal semantics as `SM_DT_TCR_challengeOracle`). -/
theorem simulateQ_slVirtualTreeM_routed_dspr [SampleableType pr.PkSeed]
    (mem : Primitives.Member) (isTarget : Adrs → Bool) (p : ℕ)
    (hmem : ∀ a ∈ constructionAddresses vp.sl, isTarget a = true →
      ∀ u tbl, ∃ msg, evalNodeInput pr u tbl a = some ⟨mem, msg⟩)
    (hp : (slTreeAddresses vp).countP isTarget ≤ p)
    (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tws₀ : List Adrs) (htws₀ : ∀ t ∈ tws₀, Scheme.IsStateful t) :
    let prob := Notions.smDsprMemberProblem (pr.member ($ᵗ pr.PkSeed) mem) pr.collection p
    let spec := unifSpec + (SM_DT_DSPR_challengeSpec Adrs (pr.MemberMsg mem) pr.Y +
      collectionSpec prob.thColl)
    let collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i →
        OracleComp spec pr.Y := fun i a msg =>
      if h : isTarget a = true ∧ i = mem then do
        let y ← (liftM (spec.query (.inr (.inl (a, h.2 ▸ msg)))) :
          OracleComp spec (Option pr.Y))
        return y.getD default
      else do
        let y ← (liftM (spec.query (.inr (.inr ⟨some i, a, msg⟩))) :
          OracleComp spec (Option pr.Y))
        return y.getD default
    ∃ tws', (∀ t ∈ tws', t ∈ tws₀ ∨ Scheme.IsStateless t) ∧
      (simulateQ (SM_DT_DSPR_oracles prob pk) (slVirtualTreeM pr collCall u)).run ([], tws₀) =
        pure (slVirtualTreeDet pr pk u, (routedTargets pr pk u mem isTarget, tws')) := by
  intro prob spec collCall
  have hfold : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y)
      (qs : List (Adrs × pr.MemberMsg mem)) (tws : List Adrs),
      l.Nodup →
      (∀ a ∈ l, a ∈ constructionAddresses vp.sl) →
      (∀ a ∈ l, TweakFresh Prod.fst qs tws a) →
      qs.length + l.countP isTarget ≤ p →
      (∀ t ∈ tws, t ∈ tws₀ ∨ Scheme.IsStateless t) →
      ∃ tws', (∀ t ∈ tws', t ∈ tws₀ ∨ Scheme.IsStateless t) ∧
        (simulateQ (SM_DT_DSPR_oracles prob pk) (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr collCall u tbl a
          return Function.update tbl a (some v)) tbl)).run (qs, tws) =
        pure (l.foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) tbl,
          (qs ++ routedTargetsAux pr pk u mem isTarget l tbl, tws')) := by
    intro l
    induction l with
    | nil =>
      intro tbl qs tws _ _ _ _ htws
      exact ⟨tws, htws, by simp [routedTargetsAux]⟩
    | cons a as ih =>
      intro tbl qs tws hnd hsub hfr hcap htws
      rw [List.nodup_cons] at hnd
      have ha_ca : a ∈ constructionAddresses vp.sl := hsub a (by simp)
      have ha_val : ValidNodeAdrs a := validNodeAdrs_of_mem_constructionAddresses ha_ca
      have ha_sl : Scheme.IsStateless a := isStateless_of_mem_constructionAddresses ha_ca
      have ha_fr : TweakFresh Prod.fst qs tws a := hfr a (by simp)
      obtain ⟨⟨i, msg⟩, hinp⟩ := Option.isSome_iff_exists.1 (evalNodeInput_isSome_of_valid pr u tbl ha_val)
      have hcnt : (a :: as).countP isTarget = (if isTarget a then 1 else 0) + as.countP isTarget := by
        simp [List.countP_cons, Nat.add_comm]
      by_cases ht : isTarget a = true
      · obtain ⟨msg', hinp'⟩ := hmem a ha_ca ht u tbl
        rw [hinp] at hinp'
        have hi_eq : i = mem := congrArg Sigma.fst (Option.some.inj hinp')
        subst hi_eq
        have hlt : qs.length < p := by rw [hcnt] at hcap; simp [ht] at hcap; omega
        have hstep : (simulateQ (SM_DT_DSPR_oracles prob pk)
            (evalNodeM pr collCall u tbl a)).run (qs, tws) =
            pure (evalNodeDet pr pk u tbl a, (qs ++ [(a, msg)], tws)) := by
          rw [evalNodeM_eq_of_input, hinp]
          unfold evalNodeDet
          rw [evalNodeM_eq_of_input, hinp]
          have hnotle : ¬ p ≤ qs.length := Nat.not_le.mpr hlt
          simp only [collCall, ht, and_self, ↓reduceDIte, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, simulateQ_pure, StateT.run_pure, SM_DT_DSPR_oracles,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, SM_DT_DSPR_challengeOracle,
            StateT.run_get, pure_bind, prob, Notions.smDsprMemberProblem, hnotle, ha_fr]
          rfl
        have hfr' : ∀ b ∈ as, TweakFresh Prod.fst (qs ++ [(a, msg)]) tws b := by
          intro b hb
          have hb_fr := hfr b (by simp [hb])
          have hba : a ≠ b := fun h => hnd.1 (h ▸ hb)
          simpa [TweakFresh, TweakReserved, hba] using hb_fr
        have hcap' : (qs ++ [(a, msg)]).length + as.countP isTarget ≤ p := by
          rw [List.length_append, List.length_singleton]
          rw [hcnt] at hcap; simp [ht] at hcap; omega
        obtain ⟨tws', htws', hih⟩ := ih
          (Function.update tbl a (some (evalNodeDet pr pk u tbl a)))
          (qs ++ [(a, msg)]) tws hnd.2 (fun b hb => hsub b (by simp [hb])) hfr' hcap' htws
        refine ⟨tws', htws', ?_⟩
        simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, hstep, pure_bind,
          simulateQ_pure, StateT.run_pure, List.foldl_cons]
        rw [hih]
        simp only [routedTargetsAux, ht, ↓reduceIte, hinp, ↓reduceDIte, List.append_assoc,
          List.singleton_append]
      · have hnot : ¬ (isTarget a = true ∧ i = mem) := fun h => ht h.1
        have hstep : (simulateQ (SM_DT_DSPR_oracles prob pk)
            (evalNodeM pr collCall u tbl a)).run (qs, tws) =
            pure (evalNodeDet pr pk u tbl a, (qs, tws ++ [a])) := by
          rw [evalNodeM_eq_of_input, hinp]
          unfold evalNodeDet
          rw [evalNodeM_eq_of_input, hinp]
          have hnotres : ¬ TweakReserved Prod.fst qs a := ha_fr.1
          simp only [collCall, hnot, ↓reduceDIte, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, simulateQ_pure, StateT.run_pure, SM_DT_DSPR_oracles,
            QueryImpl.add_apply_inr, collectionOracle, StateT.run_get, pure_bind,
            hnotres, ↓reduceIte, StateT.run_set, Option.getD_some]
          rfl
        have hfr' : ∀ b ∈ as, TweakFresh Prod.fst qs (tws ++ [a]) b := by
          intro b hb
          have hb_fr := hfr b (by simp [hb])
          have hba : b ≠ a := fun h => hnd.1 (h ▸ hb)
          simpa [TweakFresh, TweakReserved, hba] using hb_fr
        have hcap' : qs.length + as.countP isTarget ≤ p := by
          rw [hcnt] at hcap; simp [ht] at hcap; exact hcap
        have htws1 : ∀ t ∈ tws ++ [a], t ∈ tws₀ ∨ Scheme.IsStateless t := by
          intro t ht'
          rcases List.mem_append.1 ht' with h1 | h2
          · exact htws t h1
          · simp only [List.mem_singleton] at h2; subst h2; exact Or.inr ha_sl
        obtain ⟨tws', htws', hih⟩ := ih
          (Function.update tbl a (some (evalNodeDet pr pk u tbl a)))
          qs (tws ++ [a]) hnd.2 (fun b hb => hsub b (by simp [hb])) hfr' hcap' htws1
        refine ⟨tws', htws', ?_⟩
        simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, hstep, pure_bind,
          simulateQ_pure, StateT.run_pure, List.foldl_cons]
        rw [hih]
        simp only [routedTargetsAux, Bool.eq_false_iff.2 ht, Bool.false_eq_true, ↓reduceIte]
  have hfr0 : ∀ a ∈ slTreeAddresses vp, TweakFresh Prod.fst ([] : List (Adrs × pr.MemberMsg mem)) tws₀ a := by
    intro a ha
    refine ⟨by simp [TweakReserved], fun hmem => ?_⟩
    exact Scheme.not_isStateful_of_isStateless
      (isStateless_of_mem_constructionAddresses (mem_slTreeAddresses_iff.1 ha)) (htws₀ a hmem)
  obtain ⟨tws', htws', hrun⟩ := hfold (slTreeAddresses vp) (fun _ => none) [] tws₀
    (nodup_slTreeAddresses (vp := vp)) (fun _ h => mem_slTreeAddresses_iff.1 h) hfr0
    (by simpa using hp) (fun _ h => Or.inl h)
  refine ⟨tws', htws', ?_⟩
  unfold slVirtualTreeM slVirtualTreeDet
  simp only [simulateQ_bind, StateT.run_bind, hrun, pure_bind, simulateQ_pure, StateT.run_pure,
    List.nil_append]
  have hdet_eq :
      Id.run ((slTreeAddresses vp).foldlM (fun tbl a => do
        let v ← evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a
        return Function.update tbl a (some v)) (fun _ => none)) =
      (slTreeAddresses vp).foldl
        (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) (fun _ => none) := by
    have haux : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
        Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a
          return Function.update tbl a (some v)) tbl) =
        l.foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) tbl := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a as ih => intro tbl; exact ih _
    exact haux _ _
  change (pure (((((slTreeAddresses vp).foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) (fun _ => none)) (topRootAdrs vp)).getD default, (slTreeAddresses vp).foldl (fun tbl a => Function.update tbl a (some (evalNodeDet pr pk u tbl a))) (fun _ => none)), (routedTargets pr pk u mem isTarget, tws')) : ProbComp _) = _
  rw [← hdet_eq]
  rfl

private def stepTbl' (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (tbl : Adrs → Option pr.Y) (a : Adrs) : Adrs → Option pr.Y :=
  Function.update tbl a (some (evalNodeDet pr pk u tbl a))

private theorem routedTargetsAux_append (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) :
    ∀ (l₁ l₂ : List Adrs) (tbl : Adrs → Option pr.Y),
      routedTargetsAux pr pk u mem isTarget (l₁ ++ l₂) tbl =
        routedTargetsAux pr pk u mem isTarget l₁ tbl ++
          routedTargetsAux pr pk u mem isTarget l₂ (l₁.foldl (stepTbl' pr pk u) tbl)
  | [], l₂, tbl => by simp [routedTargetsAux]
  | a :: as, l₂, tbl => by
    simp only [List.cons_append, routedTargetsAux, List.foldl_cons, stepTbl']
    rw [routedTargetsAux_append pk u mem isTarget as l₂ _]
    split_ifs <;> try rfl
    cases evalNodeInput pr u tbl a with
    | none => rfl
    | some im =>
      rcases im with ⟨i, msg⟩
      by_cases h : i = mem <;> simp [h]

def honestTargetEntry (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) (a : Adrs) :
    Option (Adrs × pr.MemberMsg mem) :=
  if isTarget a then
    match honestInput pr pk u a with
    | some ⟨i, msg⟩ => if h : i = mem then some (a, h ▸ msg) else none
    | none => none
  else none

private theorem evalNodeDet_eq_honestVal_of_input {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y}
    {tbl : Adrs → Option pr.Y} {a : Adrs} (ha : ValidNodeAdrs a)
    (hinp : evalNodeInput pr u tbl a = honestInput pr pk u a) :
    evalNodeDet pr pk u tbl a = honestVal pr pk u a := by
  have hhon : evalNodeDet pr pk u (fun z => some (honestVal pr pk u z)) a =
      honestVal pr pk u a := by
    rcases a with ⟨l, tr, ty, w1, w2, w3⟩
    rcases ha with ⟨hle, h2⟩
    rcases ty with _ | _ | _ | _ | _ | ty'
    · by_cases hw3 : w3 = 0
      · subst hw3
        have hEq : (⟨l, tr, 0, w1, w2, 0⟩ : Adrs) =
            (wotsChainAdrs ⟨l, tr, 0, w1, w2, 0⟩ w2).setHashAddress 0 := by
          simp [wotsChainAdrs, Adrs.setHashAddress, Adrs.setChainAddress,
            Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.getKeyPairAddress,
            AddrType.toCode]
        rw [hEq, honestVal_wotsStep_zero]; rfl
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hw3
        have hEq : (⟨l, tr, 0, w1, w2, t + 1⟩ : Adrs) =
            (wotsChainAdrs ⟨l, tr, 0, w1, w2, t + 1⟩ w2).setHashAddress (t + 1) := by
          simp [wotsChainAdrs, Adrs.setHashAddress, Adrs.setChainAddress,
            Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.getKeyPairAddress,
            AddrType.toCode]
        rw [hEq, honestVal_wotsStep_succ]
        unfold evalNodeDet evalNodeM
        simp [wotsChainAdrs, Adrs.setHashAddress, Adrs.setChainAddress,
          Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.getKeyPairAddress,
          AddrType.toCode, Primitives.memberEval, Id.run]
    · unfold honestVal evalNodeDet evalNodeM
      have hr : nodeRank vp ⟨l, tr, 1, w1, w2, w3⟩ = vp.params.w := rfl
      rw [hr, honestValAux]
      have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
      simp only [Primitives.memberEval, Id.run]
      congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn, Option.getD_some]
      exact (honestValAux_eq_honestVal pr pk u (by
        simp [nodeRank, wotsChainAdrs, Adrs.setHashAddress, Adrs.setChainAddress,
          Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode]; omega)).symm
    · have hw2 : w2 ≠ 0 := h2 rfl
      unfold honestVal evalNodeDet evalNodeM
      have hr : nodeRank vp ⟨l, tr, 2, w1, w2, w3⟩ = vp.params.w + w2 := rfl
      rw [hr, honestValAux]
      simp only [hw2, ↓reduceIte, Primitives.memberEval, Id.run]
      split_ifs with hw2'
      · subst hw2'
        simp only [Option.getD_some]
        congr 1
      · simp only [Option.getD_some]
        congr 1 <;> exact (honestValAux_eq_honestVal pr pk u (by
          simp [nodeRank, xmssNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
            Adrs.setTypeAndClear, AddrType.toCode]; omega)).symm
    · unfold honestVal evalNodeDet evalNodeM
      have hr : nodeRank vp ⟨l, tr, 3, w1, w2, w3⟩ = w2 := rfl
      rw [hr, honestValAux]
      simp only [Primitives.memberEval, Id.run]
      split_ifs with hw2
      · rfl
      · simp only [Option.getD_some]
        congr 1 <;> exact (honestValAux_eq_honestVal pr pk u (by
          simp [nodeRank, forsNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
            Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode]; omega)).symm
    · unfold honestVal evalNodeDet evalNodeM
      have hr : nodeRank vp ⟨l, tr, 4, w1, w2, w3⟩ = vp.params.a + 1 := rfl
      rw [hr, honestValAux]
      simp only [Primitives.memberEval, Id.run]
      congr 1
    · dsimp only at hle; omega
  rw [← hhon]
  unfold evalNodeDet
  rw [evalNodeM_eq_of_input, evalNodeM_eq_of_input, hinp]
  rfl

private theorem foldl_routed_mono (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) :
    ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      (∀ a ∈ l, ValidNodeAdrs a) →
      (∀ a ∈ l, ∀ tbl', TblSound pr pk u tbl' →
        (∀ z, tbl z = some (honestVal pr pk u z) → tbl' z = some (honestVal pr pk u z)) →
        evalNodeInput pr u tbl' a = honestInput pr pk u a) →
      TblSound pr pk u (l.foldl (stepTbl' pr pk u) tbl) ∧
        (∀ z, tbl z = some (honestVal pr pk u z) →
          (l.foldl (stepTbl' pr pk u) tbl) z = some (honestVal pr pk u z)) ∧
        (∀ a ∈ l, (l.foldl (stepTbl' pr pk u) tbl) a = some (honestVal pr pk u a)) ∧
        routedTargetsAux pr pk u mem isTarget l tbl =
          l.filterMap (honestTargetEntry pr pk u mem isTarget)
  | [], tbl, hs, _, _ => ⟨hs, fun _ h => h, fun _ h => by simp at h, by simp [routedTargetsAux]⟩
  | a :: as, tbl, hs, hval, hstep => by
    have hinp : evalNodeInput pr u tbl a = honestInput pr pk u a :=
      hstep a (by simp) tbl hs (fun _ h => h)
    have hev : evalNodeDet pr pk u tbl a = honestVal pr pk u a :=
      evalNodeDet_eq_honestVal_of_input pr (hval a (by simp)) hinp
    have hs1 : TblSound pr pk u (stepTbl' pr pk u tbl a) := by
      intro z v hz
      by_cases hza : z = a
      · subst hza; simp only [stepTbl', Function.update_self, Option.some.injEq] at hz; rw [← hz, hev]
      · simp only [stepTbl', Function.update_of_ne hza] at hz; exact hs z v hz
    have hm1 : ∀ z, tbl z = some (honestVal pr pk u z) →
        (stepTbl' pr pk u tbl a) z = some (honestVal pr pk u z) := by
      intro z hz
      by_cases hza : z = a
      · subst hza; simp [stepTbl', hev]
      · simp [stepTbl', Function.update_of_ne hza, hz]
    have ih := foldl_routed_mono pk u mem isTarget as (stepTbl' pr pk u tbl a) hs1
      (fun b hb => hval b (by simp [hb]))
      (fun b hb tbl' hs' hsub => hstep b (by simp [hb]) tbl' hs' (fun z hz => hsub z (hm1 z hz)))
    refine ⟨ih.1, fun z hz => ih.2.1 z (hm1 z hz), fun b hb => ?_, ?_⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ih.2.1 b (by simp [stepTbl', hev])
      · exact ih.2.2.1 b hb
    · simp only [routedTargetsAux, List.filterMap_cons, honestTargetEntry]
      change (if isTarget a = true then match evalNodeInput pr u tbl a with
          | some ⟨i, msg⟩ => if h : i = mem then (a, h ▸ msg) :: routedTargetsAux pr pk u mem isTarget as (stepTbl' pr pk u tbl a)
              else routedTargetsAux pr pk u mem isTarget as (stepTbl' pr pk u tbl a)
          | none => routedTargetsAux pr pk u mem isTarget as (stepTbl' pr pk u tbl a)
        else routedTargetsAux pr pk u mem isTarget as (stepTbl' pr pk u tbl a)) = _
      rw [hinp, ih.2.2.2]
      cases ht : isTarget a
      · simp
      · simp only [↓reduceIte]
        cases honestInput pr pk u a with
        | none => simp
        | some im =>
          rcases im with ⟨i, msg⟩
          by_cases h : i = mem <;> simp [h]

private theorem foldl_routed_product (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool)
    {α β : Type} (f : α → β → Adrs) (ls : List α) (rs : List β) :
    ∀ (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      (∀ x ∈ ls, ∀ tbl', TblSound pr pk u tbl' →
        (∀ z, tbl z = some (honestVal pr pk u z) → tbl' z = some (honestVal pr pk u z)) →
        let seg := rs.map (f x)
        TblSound pr pk u (seg.foldl (stepTbl' pr pk u) tbl') ∧
          (∀ z, tbl' z = some (honestVal pr pk u z) →
            (seg.foldl (stepTbl' pr pk u) tbl') z = some (honestVal pr pk u z)) ∧
          (∀ a ∈ seg, (seg.foldl (stepTbl' pr pk u) tbl') a = some (honestVal pr pk u a)) ∧
          routedTargetsAux pr pk u mem isTarget seg tbl' =
            seg.filterMap (honestTargetEntry pr pk u mem isTarget)) →
      let all := (ls.product rs).map fun p => f p.1 p.2
      TblSound pr pk u (all.foldl (stepTbl' pr pk u) tbl) ∧
        (∀ z, tbl z = some (honestVal pr pk u z) →
          (all.foldl (stepTbl' pr pk u) tbl) z = some (honestVal pr pk u z)) ∧
        (∀ a ∈ all, (all.foldl (stepTbl' pr pk u) tbl) a = some (honestVal pr pk u a)) ∧
        routedTargetsAux pr pk u mem isTarget all tbl =
          all.filterMap (honestTargetEntry pr pk u mem isTarget) := by
  induction ls with
  | nil =>
    intro tbl hs _
    exact ⟨hs, fun _ h => h, fun _ h => by simp [List.product] at h, by simp [List.product, routedTargetsAux]⟩
  | cons x xs ih =>
    intro tbl hs hone
    have hprod : ((x :: xs).product rs).map (fun p => f p.1 p.2) =
        rs.map (f x) ++ (xs.product rs).map (fun p => f p.1 p.2) := by
      simp [List.product, List.flatMap_cons, List.map_append, List.map_map, Function.comp_def]
    dsimp only
    rw [hprod, List.foldl_append, routedTargetsAux_append, List.filterMap_append]
    have hx := hone x (by simp) tbl hs (fun _ h => h)
    have hxs := ih ((rs.map (f x)).foldl (stepTbl' pr pk u) tbl) hx.1
      (fun y hy tbl' hs' hsub => hone y (by simp [hy]) tbl' hs' (fun z hz => hsub z (hx.2.1 z hz)))
    refine ⟨hxs.1, fun z hz => hxs.2.1 z (hx.2.1 z hz), fun a ha => ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha₁ | ha₂
      · exact hxs.2.1 a (hx.2.2.1 a ha₁)
      · exact hxs.2.2.1 a ha₂
    · rw [hx.2.2.2, hxs.2.2.2]

private theorem foldl_routed_perfectInternalCoords (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool)
    (cell : ℕ → ℕ → Adrs) (H : ℕ)
    (hvalid : ∀ z j, z < H → j < 2 ^ (H - (z + 1)) → ValidNodeAdrs (cell (z + 1) j))
    (hstep : ∀ z j tbl, z < H → j < 2 ^ (H - (z + 1)) →
      tbl (cell z (2 * j)) = some (honestVal pr pk u (cell z (2 * j))) →
      tbl (cell z (2 * j + 1)) = some (honestVal pr pk u (cell z (2 * j + 1))) →
      evalNodeInput pr u tbl (cell (z + 1) j) = honestInput pr pk u (cell (z + 1) j)) :
    ∀ (rem z : ℕ), z + rem = H →
      ∀ (tbl : Adrs → Option pr.Y),
        TblSound pr pk u tbl →
        (∀ j < 2 ^ (H - z), tbl (cell z j) = some (honestVal pr pk u (cell z j))) →
        let l := (perfectInternalCoords rem).map fun zi => cell (zi.1 + z) zi.2
        TblSound pr pk u (l.foldl (stepTbl' pr pk u) tbl) ∧
          (∀ w, tbl w = some (honestVal pr pk u w) →
            (l.foldl (stepTbl' pr pk u) tbl) w = some (honestVal pr pk u w)) ∧
          (∀ a ∈ l, (l.foldl (stepTbl' pr pk u) tbl) a = some (honestVal pr pk u a)) ∧
          routedTargetsAux pr pk u mem isTarget l tbl =
            l.filterMap (honestTargetEntry pr pk u mem isTarget)
  | 0, _, _, tbl, hs, _ => ⟨hs, fun _ h => h, fun _ h => by simp [perfectInternalCoords] at h,
      by simp [perfectInternalCoords, routedTargetsAux]⟩
  | rem + 1, z, hz, tbl, hs, hbase => by
    dsimp only
    have hsplit : (perfectInternalCoords (rem + 1)).map (fun zi => cell (zi.1 + z) zi.2) =
        ((List.range (2 ^ rem)).map fun j => cell (z + 1) j) ++
        ((perfectInternalCoords rem).map fun zi => cell (zi.1 + (z + 1)) zi.2) := by
      simp only [perfectInternalCoords, List.map_append, List.map_map, Function.comp_def]
      congr 1
      · apply List.map_congr_left; intro j _; congr 1; omega
      · apply List.map_congr_left; intro zi _; congr 1; omega
    rw [hsplit, List.foldl_append, routedTargetsAux_append, List.filterMap_append]
    have hrem : H - (z + 1) = rem := by omega
    have hlevel := foldl_routed_mono pr pk u mem isTarget
      ((List.range (2 ^ rem)).map fun j => cell (z + 1) j) tbl hs
      (fun a ha => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
        exact hvalid z j (by omega) (by rw [hrem]; exact List.mem_range.1 hj))
      (fun a ha tbl' _ hsub => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
        have hjlt : j < 2 ^ rem := List.mem_range.1 hj
        have hsub0 : H - z = rem + 1 := by omega
        have h0 : 2 * j < 2 ^ (H - z) := by rw [hsub0, pow_succ]; omega
        have h1 : 2 * j + 1 < 2 ^ (H - z) := by rw [hsub0, pow_succ]; omega
        exact hstep z j tbl' (by omega) (by rw [hrem]; exact hjlt) (hsub _ (hbase _ h0)) (hsub _ (hbase _ h1)))
    set tbl₁ := (((List.range (2 ^ rem)).map fun j => cell (z + 1) j).foldl (stepTbl' pr pk u) tbl)
    have ih := foldl_routed_perfectInternalCoords pk u mem isTarget cell H hvalid hstep rem (z + 1)
      (by omega) tbl₁ hlevel.1 (fun j hj => hlevel.2.2.1 _ (List.mem_map.2 ⟨j, List.mem_range.2 (by rw [← hrem]; exact hj), rfl⟩))
    refine ⟨ih.1, fun w hw => ih.2.1 w (hlevel.2.1 w hw), fun a ha => ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha₁ | ha₂
      · exact ih.2.1 a (hlevel.2.2.1 a ha₁)
      · exact ih.2.2.1 a ha₂
    · rw [hlevel.2.2.2, ih.2.2.2]

private theorem foldl_routed_wotsSteps (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) (b : Adrs) (ch : ℕ) :
    ∀ (m : ℕ) (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      let l := (List.range m).map fun t => (wotsChainAdrs b ch).setHashAddress t
      TblSound pr pk u (l.foldl (stepTbl' pr pk u) tbl) ∧
        (∀ z, tbl z = some (honestVal pr pk u z) →
          (l.foldl (stepTbl' pr pk u) tbl) z = some (honestVal pr pk u z)) ∧
        (∀ a ∈ l, (l.foldl (stepTbl' pr pk u) tbl) a = some (honestVal pr pk u a)) ∧
        routedTargetsAux pr pk u mem isTarget l tbl =
          l.filterMap (honestTargetEntry pr pk u mem isTarget)
  | 0, tbl, hs => ⟨hs, fun _ h => h, fun _ h => by simp at h, by simp [routedTargetsAux]⟩
  | m + 1, tbl, hs => by
    dsimp only
    rw [List.range_succ, List.map_append, List.foldl_append, routedTargetsAux_append, List.filterMap_append]
    have ih := foldl_routed_wotsSteps pk u mem isTarget b ch m tbl hs
    set l₁ := (List.range m).map fun t => (wotsChainAdrs b ch).setHashAddress t
    set tbl₁ := l₁.foldl (stepTbl' pr pk u) tbl
    have hinp : evalNodeInput pr u tbl₁ ((wotsChainAdrs b ch).setHashAddress m) =
        honestInput pr pk u ((wotsChainAdrs b ch).setHashAddress m) := by
      rcases m with _ | m
      · rfl
      · have hprev : tbl₁ ((wotsChainAdrs b ch).setHashAddress m) =
            some (honestVal pr pk u ((wotsChainAdrs b ch).setHashAddress m)) :=
          ih.2.2.1 _ (List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_self m), rfl⟩)
        unfold honestInput evalNodeInput
        have hty : ((wotsChainAdrs b ch).setHashAddress (m + 1)).type = 0 := rfl
        have hw3 : ((wotsChainAdrs b ch).setHashAddress (m + 1)).word3 = m + 1 := rfl
        have hset : ((wotsChainAdrs b ch).setHashAddress (m + 1)).setHashAddress m =
            (wotsChainAdrs b ch).setHashAddress m := rfl
        simp only [hty, hw3, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, hset, hprev, Option.getD_some]
    have hsingle := foldl_routed_mono pr pk u mem isTarget
      [(wotsChainAdrs b ch).setHashAddress m] tbl₁ ih.1
      (fun a ha => by rw [List.mem_singleton.1 ha]; exact ⟨by change 0 ≤ 4; omega, fun h => by cases h⟩)
      (fun a ha tbl' _ hsub => by
        rw [List.mem_singleton.1 ha]
        rcases m with _ | m
        · rfl
        · have hprev := hsub _ (ih.2.2.1 _ (List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_self m), rfl⟩))
          unfold honestInput evalNodeInput
          have hty : ((wotsChainAdrs b ch).setHashAddress (m + 1)).type = 0 := rfl
          have hw3 : ((wotsChainAdrs b ch).setHashAddress (m + 1)).word3 = m + 1 := rfl
          have hset : ((wotsChainAdrs b ch).setHashAddress (m + 1)).setHashAddress m =
              (wotsChainAdrs b ch).setHashAddress m := rfl
          simp only [hty, hw3, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Nat.add_sub_cancel, hset, hprev, Option.getD_some])
    refine ⟨hsingle.1, fun z hz => hsingle.2.1 z (ih.2.1 z hz), fun a ha => ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha₁ | ha₂
      · exact hsingle.2.1 a (ih.2.2.1 a ha₁)
      · exact hsingle.2.2.1 a ha₂
    · rw [List.map_singleton, ih.2.2.2, hsingle.2.2.2]

/-- **`routedTargets` exact formula**: equals filtering `slTreeAddresses vp` by
`honestTargetEntry`. -/
theorem routedTargets_eq_filterMap (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) :
    routedTargets pr pk u mem isTarget =
      (slTreeAddresses vp).filterMap (honestTargetEntry pr pk u mem isTarget) := by
  let t0 : Adrs → Option pr.Y := fun _ => none
  have hs0 : TblSound pr pk u t0 := fun _ _ h => by simp [t0] at h
  -- Pass 1: FORS leaves
  set t1 := (forsLeafAddresses vp.sl).foldl (stepTbl' pr pk u) t0
  have hp1 := foldl_routed_mono pr pk u mem isTarget (forsLeafAddresses vp.sl) t0 hs0
    (fun a ha => validNodeAdrs_of_mem_constructionAddresses ((mem_constructionAddresses_iff a).2 (Or.inl ha)))
    (fun a ha _ _ _ => by obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; rfl)
  -- Pass 2: FORS internal nodes
  set t2 := (forsTreeAddresses vp.sl).foldl (stepTbl' pr pk u) t1
  have hp2 : TblSound pr pk u t2 ∧
      (∀ z, t1 z = some (honestVal pr pk u z) → t2 z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ forsTreeAddresses vp.sl, t2 a = some (honestVal pr pk u a)) ∧
      routedTargetsAux pr pk u mem isTarget (forsTreeAddresses vp.sl) t1 =
        (forsTreeAddresses vp.sl).filterMap (honestTargetEntry pr pk u mem isTarget) := by
    unfold forsTreeAddresses
    refine foldl_routed_product pr pk u mem isTarget
      (fun (pt : BottomPosition vp.sl × Fin vp.sl.params.k) (zi : ℕ × ℕ) =>
        forsNodeAdrs pt.1.forsAdrs zi.1 (pt.2.val * 2 ^ (vp.sl.params.a - zi.1) + zi.2))
      ((allBottomPositions vp.sl).product (List.finRange vp.sl.params.k))
      (perfectInternalCoords vp.sl.params.a) t1 hp1.1 ?_
    intro pt _ tbl' hs' hsub
    have hmap : ((perfectInternalCoords vp.sl.params.a).map fun zi =>
          forsNodeAdrs pt.1.forsAdrs zi.1 (pt.2.val * 2 ^ (vp.sl.params.a - zi.1) + zi.2)) =
        ((perfectInternalCoords vp.sl.params.a).map fun zi =>
          forsNodeAdrs pt.1.forsAdrs (zi.1 + 0)
            (pt.2.val * 2 ^ (vp.sl.params.a - (zi.1 + 0)) + zi.2)) := by simp
    rw [hmap]
    refine foldl_routed_perfectInternalCoords pr pk u mem isTarget
      (fun z j => forsNodeAdrs pt.1.forsAdrs z (pt.2.val * 2 ^ (vp.sl.params.a - z) + j))
      vp.sl.params.a (fun _ _ _ _ => ⟨by change 3 ≤ 4; omega, fun h => by cases h⟩)
      (fun z j tbl'' hza _ hl hr => by
        have hsub1 : vp.sl.params.a - z = vp.sl.params.a - (z + 1) + 1 := by omega
        have hidx0 : 2 * (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) =
            pt.2.val * 2 ^ (vp.sl.params.a - z) + 2 * j := by rw [hsub1, pow_succ]; ring
        have hidx1 : 2 * (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) + 1 =
            pt.2.val * 2 ^ (vp.sl.params.a - z) + (2 * j + 1) := by rw [hsub1, pow_succ]; ring
        unfold honestInput evalNodeInput
        have hty : (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).type = 3 := rfl
        have hw2 : (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).word2 = z + 1 := rfl
        have hw3 : (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).word3 =
            pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j := rfl
        have hf0 : forsNodeAdrs (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) z
            (2 * (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) =
            forsNodeAdrs pt.1.forsAdrs z (pt.2.val * 2 ^ (vp.sl.params.a - z) + 2 * j) := by
          rw [← hidx0]; rfl
        have hf1 : forsNodeAdrs (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)) z
            (2 * (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) + 1) =
            forsNodeAdrs pt.1.forsAdrs z (pt.2.val * 2 ^ (vp.sl.params.a - z) + (2 * j + 1)) := by
          rw [← hidx1]; rfl
        simp only [hty, hw2, hw3, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, hf0, hf1, hl, hr, Option.getD_some])
      vp.sl.params.a 0 (Nat.zero_add _) tbl' hs' (fun j hj =>
        hsub _ (hp1.2.2.1 _ (by simpa [SLHDSA.Params.t] using mem_forsLeafAddresses vp.sl pt.1 pt.2 ⟨j, hj⟩)))
  -- Pass 3: FORS roots
  set t3 := (forsRootAddresses vp.sl).foldl (stepTbl' pr pk u) t2
  have hp3 := foldl_routed_mono pr pk u mem isTarget (forsRootAddresses vp.sl) t2 hp2.1
    (fun a ha => validNodeAdrs_of_mem_constructionAddresses ((mem_constructionAddresses_iff a).2 (Or.inr (Or.inr (Or.inl ha)))))
    (fun a ha tbl' _ hsub => by
      obtain ⟨pos, -, rfl⟩ := List.mem_map.1 ha
      unfold honestInput evalNodeInput
      have hty : (forsPkAdrs pos.forsAdrs).type = 4 := rfl
      simp only [hty]
      congr 1; congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      have hmem : forsNodeAdrs pos.forsAdrs vp.params.a i ∈ forsTreeAddresses vp.sl := by
        have hm := mem_forsTreeAddresses vp.sl pos ⟨i, hi⟩ vp.valid.a_pos le_rfl (idx := 0) (by simp)
        simpa [ValidatedParams.sl, Params.slParams] using hm
      have heq : forsNodeAdrs (forsPkAdrs pos.forsAdrs) vp.params.a i =
          forsNodeAdrs pos.forsAdrs vp.params.a i := rfl
      rw [heq, hsub _ (hp2.2.2.1 _ hmem), Option.getD_some])
  -- Pass 4: WOTS+ chain steps
  set t4 := (wotsStepAddresses vp.sl).foldl (stepTbl' pr pk u) t3
  have hp4 : TblSound pr pk u t4 ∧
      (∀ z, t3 z = some (honestVal pr pk u z) → t4 z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ wotsStepAddresses vp.sl, t4 a = some (honestVal pr pk u a)) ∧
      routedTargetsAux pr pk u mem isTarget (wotsStepAddresses vp.sl) t3 =
        (wotsStepAddresses vp.sl).filterMap (honestTargetEntry pr pk u mem isTarget) := by
    unfold wotsStepAddresses
    refine foldl_routed_product pr pk u mem isTarget
      (fun (c : WotsChainCoord vp.sl) (s : Fin (vp.sl.params.w - 1)) => wotsStepAdrs c s)
      (allWotsChains vp.sl) (List.finRange (vp.sl.params.w - 1)) t3 hp3.1 ?_
    intro c _ tbl' hs' _
    have hfin : (List.finRange (vp.sl.params.w - 1)).map (wotsStepAdrs c) =
        (List.range (vp.sl.params.w - 1)).map fun t =>
          (wotsChainAdrs (wotsInstanceAdrs c.1) c.2.val).setHashAddress t := by
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂; simp [wotsStepAdrs]
    rw [hfin]
    exact foldl_routed_wotsSteps pr pk u mem isTarget (wotsInstanceAdrs c.1) c.2.val (vp.sl.params.w - 1) tbl' hs'
  -- Pass 5: WOTS+ public keys
  set t5 := (wotsPkAddresses vp.sl).foldl (stepTbl' pr pk u) t4
  have hp5 := foldl_routed_mono pr pk u mem isTarget (wotsPkAddresses vp.sl) t4 hp4.1
    (fun a ha => validNodeAdrs_of_mem_constructionAddresses ((mem_constructionAddresses_iff a).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
    (fun a ha tbl' _ hsub => by
      obtain ⟨pos, -, rfl⟩ := List.mem_map.1 ha
      unfold honestInput evalNodeInput
      have hty : (wotsPkAdrs (wotsInstanceAdrs pos)).type = 1 := rfl
      simp only [hty]
      congr 1; congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      have hi' : i < vp.sl.params.len := by rw [← Params.lsl_eq_len vp.valid]; exact hi
      have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
      have hw2 : vp.params.w - 2 < vp.sl.params.w - 1 := by
        change vp.params.w - 2 < vp.params.w - 1; omega
      have hmem : (wotsChainAdrs (wotsInstanceAdrs pos) i).setHashAddress (vp.params.w - 2) ∈
          wotsStepAddresses vp.sl :=
        mem_wotsStepAddresses vp.sl (pos, ⟨i, hi'⟩) ⟨vp.params.w - 2, hw2⟩
      have heq : (wotsChainAdrs (wotsPkAdrs (wotsInstanceAdrs pos)) i).setHashAddress (vp.params.w - 2) =
          (wotsChainAdrs (wotsInstanceAdrs pos) i).setHashAddress (vp.params.w - 2) := rfl
      rw [heq, hsub _ (hp4.2.2.1 _ hmem), Option.getD_some])
  -- Pass 6: XMSS internal nodes
  set t6 := (xmssNodeAddresses vp.sl).foldl (stepTbl' pr pk u) t5
  have hp6 : TblSound pr pk u t6 ∧
      (∀ z, t5 z = some (honestVal pr pk u z) → t6 z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ xmssNodeAddresses vp.sl, t6 a = some (honestVal pr pk u a)) ∧
      routedTargetsAux pr pk u mem isTarget (xmssNodeAddresses vp.sl) t5 =
        (xmssNodeAddresses vp.sl).filterMap (honestTargetEntry pr pk u mem isTarget) := by
    unfold xmssNodeAddresses
    refine foldl_routed_product pr pk u mem isTarget
      (fun (coord : LayerTreeCoord vp.sl) (zi : ℕ × ℕ) => xmssNodeAdrs coord.toAdrs zi.1 zi.2)
      (allXmssTrees vp.sl) (perfectInternalCoords vp.sl.params.hp) t5 hp5.1 ?_
    intro coord _ tbl' hs' hsub
    have hmap : ((perfectInternalCoords vp.sl.params.hp).map fun zi =>
          xmssNodeAdrs coord.toAdrs zi.1 zi.2) =
        ((perfectInternalCoords vp.sl.params.hp).map fun zi =>
          xmssCellAdrs coord.toAdrs (zi.1 + 0) zi.2) := by
      apply List.map_congr_left
      intro zi hzi
      have hz := perfectInternalCoords_height_pos hzi
      rcases zi with ⟨z, j⟩
      cases z with
      | zero => omega
      | succ z => rfl
    rw [hmap]
    refine foldl_routed_perfectInternalCoords pr pk u mem isTarget (xmssCellAdrs coord.toAdrs)
      vp.sl.params.hp
      (fun z j _ _ => ⟨by change 2 ≤ 4; omega, fun _ => by change z + 1 ≠ 0; omega⟩)
      (fun z j tbl'' _ _ hl hr => by
        unfold honestInput evalNodeInput
        rcases z with _ | z
        · have hty : (xmssCellAdrs coord.toAdrs 1 j).type = 2 := rfl
          have hw2 : (xmssCellAdrs coord.toAdrs 1 j).word2 = 1 := rfl
          have hw3 : (xmssCellAdrs coord.toAdrs 1 j).word3 = j := rfl
          have h1 : wotsPkAdrs (wotsLeafAdrs (xmssCellAdrs coord.toAdrs 1 j) (2 * j)) =
              xmssCellAdrs coord.toAdrs 0 (2 * j) := rfl
          have h2 : wotsPkAdrs (wotsLeafAdrs (xmssCellAdrs coord.toAdrs 1 j) (2 * j + 1)) =
              xmssCellAdrs coord.toAdrs 0 (2 * j + 1) := rfl
          simp only [hty, hw2, hw3, one_ne_zero, ↓reduceIte, h1, h2, hl, hr, Option.getD_some]
        · have hty : (xmssCellAdrs coord.toAdrs (z + 2) j).type = 2 := rfl
          have hw2 : (xmssCellAdrs coord.toAdrs (z + 2) j).word2 = z + 2 := rfl
          have hw3 : (xmssCellAdrs coord.toAdrs (z + 2) j).word3 = j := rfl
          have hne0 : z + 2 ≠ 0 := by omega
          have hne1 : z + 2 ≠ 1 := by omega
          have h1 : xmssNodeAdrs (xmssCellAdrs coord.toAdrs (z + 2) j) (z + 2 - 1) (2 * j) =
              xmssCellAdrs coord.toAdrs (z + 1) (2 * j) := rfl
          have h2 : xmssNodeAdrs (xmssCellAdrs coord.toAdrs (z + 2) j) (z + 2 - 1) (2 * j + 1) =
              xmssCellAdrs coord.toAdrs (z + 1) (2 * j + 1) := rfl
          simp only [hty, hw2, hw3, hne0, hne1, ↓reduceIte, h1, h2, hl, hr, Option.getD_some])
      vp.sl.params.hp 0 (Nat.zero_add _) tbl' hs' (fun j hj => by
        have hpos : wotsPkAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, ⟨j, hj⟩⟩) ∈
            wotsPkAddresses vp.sl := mem_wotsPkAddresses vp.sl _
        exact hsub _ (hp5.2.2.1 _ hpos))
  -- Assemble all 6 passes
  unfold routedTargets slTreeAddresses
  simp only [routedTargetsAux_append, List.foldl_append, List.filterMap_append]
  rw [hp1.2.2.2, hp2.2.2.2, hp3.2.2.2, hp4.2.2.2, hp5.2.2.2, hp6.2.2.2]

/-- **Completeness of `routedTargets`**: for every `a ∈ constructionAddresses vp.sl` with
`isTarget a = true` and `honestInput pr pk u a = some ⟨mem, msg⟩`, `(a, msg)` occurs in
`routedTargets pr pk u mem isTarget`. -/
theorem mem_routedTargets_of_honestInput (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool)
    {a : Adrs} (ha : a ∈ constructionAddresses vp.sl) (ht : isTarget a = true)
    {msg : pr.MemberMsg mem} (hmsg : honestInput pr pk u a = some ⟨mem, msg⟩) :
    (a, msg) ∈ routedTargets pr pk u mem isTarget := by
  rw [routedTargets_eq_filterMap, List.mem_filterMap]
  exact ⟨a, mem_slTreeAddresses_iff.2 ha, by simp [honestTargetEntry, ht, hmsg]⟩

/-- Uniqueness of tweaks in `routedTargets`: no two entries in `routedTargets` share a tweak. -/
theorem nodup_map_fst_routedTargets (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (mem : Primitives.Member) (isTarget : Adrs → Bool) :
    ((routedTargets pr pk u mem isTarget).map Prod.fst).Nodup := by
  rw [routedTargets_eq_filterMap]
  have hsub : List.Sublist
      (((slTreeAddresses vp).filterMap (honestTargetEntry pr pk u mem isTarget)).map Prod.fst)
      (slTreeAddresses vp) := by
    have haux : ∀ l : List Adrs,
        List.Sublist ((l.filterMap (honestTargetEntry pr pk u mem isTarget)).map Prod.fst) l := by
      intro l
      induction l with
      | nil => simp
      | cons a as ih =>
        simp only [List.filterMap_cons]
        cases h : honestTargetEntry pr pk u mem isTarget a with
        | none => exact List.Sublist.cons a ih
        | some e =>
          have hea : e.1 = a := by
            unfold honestTargetEntry at h
            split_ifs at h
            cases hhi : honestInput pr pk u a with
            | none => rw [hhi] at h; cases h
            | some im =>
              rw [hhi] at h
              rcases im with ⟨i, msg⟩
              by_cases hi : i = mem
              · simp only [hi, ↓reduceDIte, Option.some.injEq] at h
                subst h; rfl
              · simp only [hi, ↓reduceDIte] at h; cases h
          simp only [List.map_cons, hea]
          exact List.Sublist.cons_cons a ih
    exact haux _
  exact (nodup_slTreeAddresses (vp := vp)).sublist hsub

/-! ### Concrete role target predicates and exact target counts (`q₃, q₄, q₅, q₆, q₈`) -/

/-- FORS leaf addresses (`type = 3`, `word2 = 0`), member `.F`, count `q₈ = 2^h · k · 2^a`. -/
def isForsLeaf (a : Adrs) : Bool := a.type == 3 && a.word2 == 0

/-- Internal hash addresses (`FORS_TREE` with `word2 ≠ 0`, or `TREE` with `word2 ≠ 0`), member `.H`,
count `q₄ = 2^h · k · (2^a - 1) + xmssTreeCount · (2^h' - 1)`. -/
def isInternalH (a : Adrs) : Bool := (a.type == 3 && a.word2 != 0) || (a.type == 2 && a.word2 != 0)

/-- FORS root compression addresses (`type = 4`), member `.thK`, count `q₅ = 2^h`. -/
def isForsRoot (a : Adrs) : Bool := a.type == 4

/-- WOTS+ chain step addresses (`type = 0`), member `.F`, count `q₃ = wotsInstanceCount · len · (w - 1)`. -/
def isWotsStep (a : Adrs) : Bool := a.type == 0

/-- WOTS+ public key compression addresses (`type = 1`), member `.thLsl`, count `q₆ = wotsInstanceCount`. -/
def isWotsPk (a : Adrs) : Bool := a.type == 1

theorem countP_slTreeAddresses_isForsLeaf :
    (slTreeAddresses vp).countP isForsLeaf = (forsLeafAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isForsLeaf a = true := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isForsLeaf a = false := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha
    obtain ⟨⟨_, zi⟩, hmem, rfl⟩ := ha
    have hz := perfectInternalCoords_height_pos (List.mem_product.1 hmem).2
    simp only [isForsLeaf, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    right; change zi.1 ≠ 0; omega
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isForsLeaf a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isForsLeaf a = false := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isForsLeaf a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isForsLeaf a = false := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  rw [slTreeAddresses]
  simp only [List.countP_append]
  rw [List.countP_eq_length.2 h1,
    List.countP_eq_zero.2 (fun a ha => by rw [h2 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h3 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h4 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h5 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h6 a ha]; decide)]
  omega

theorem countP_slTreeAddresses_isInternalH :
    (slTreeAddresses vp).countP isInternalH =
      (forsTreeAddresses vp.sl).length + (xmssNodeAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isInternalH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isInternalH a = true := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha
    obtain ⟨⟨_, zi⟩, hmem, rfl⟩ := ha
    have hz := perfectInternalCoords_height_pos (List.mem_product.1 hmem).2
    simp only [isInternalH, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    left; exact ⟨rfl, by change zi.1 ≠ 0; omega⟩
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isInternalH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isInternalH a = false := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isInternalH a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isInternalH a = true := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha
    obtain ⟨⟨_, zi⟩, hmem, rfl⟩ := ha
    have hz := perfectInternalCoords_height_pos (List.mem_product.1 hmem).2
    simp only [isInternalH, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    right; exact ⟨rfl, by change zi.1 ≠ 0; omega⟩
  rw [slTreeAddresses]
  simp only [List.countP_append]
  rw [List.countP_eq_zero.2 (fun a ha => by rw [h1 a ha]; decide),
    List.countP_eq_length.2 h2,
    List.countP_eq_zero.2 (fun a ha => by rw [h3 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h4 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h5 a ha]; decide),
    List.countP_eq_length.2 h6]
  omega

theorem countP_slTreeAddresses_isForsRoot :
    (slTreeAddresses vp).countP isForsRoot = (forsRootAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isForsRoot a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isForsRoot a = false := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isForsRoot a = true := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isForsRoot a = false := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isForsRoot a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isForsRoot a = false := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  rw [slTreeAddresses]
  simp only [List.countP_append]
  rw [List.countP_eq_zero.2 (fun a ha => by rw [h1 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h2 a ha]; decide),
    List.countP_eq_length.2 h3,
    List.countP_eq_zero.2 (fun a ha => by rw [h4 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h5 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h6 a ha]; decide)]
  omega

theorem countP_slTreeAddresses_isWotsStep :
    (slTreeAddresses vp).countP isWotsStep = (wotsStepAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isWotsStep a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isWotsStep a = false := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isWotsStep a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isWotsStep a = true := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isWotsStep a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isWotsStep a = false := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  rw [slTreeAddresses]
  simp only [List.countP_append]
  rw [List.countP_eq_zero.2 (fun a ha => by rw [h1 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h2 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h3 a ha]; decide),
    List.countP_eq_length.2 h4,
    List.countP_eq_zero.2 (fun a ha => by rw [h5 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h6 a ha]; decide)]
  omega

theorem countP_slTreeAddresses_isWotsPk :
    (slTreeAddresses vp).countP isWotsPk = (wotsPkAddresses vp.sl).length := by
  have h1 : ∀ a ∈ forsLeafAddresses vp.sl, isWotsPk a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h2 : ∀ a ∈ forsTreeAddresses vp.sl, isWotsPk a = false := by
    intro a ha; simp only [forsTreeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h3 : ∀ a ∈ forsRootAddresses vp.sl, isWotsPk a = false := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h4 : ∀ a ∈ wotsStepAddresses vp.sl, isWotsPk a = false := by
    intro a ha; simp only [wotsStepAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  have h5 : ∀ a ∈ wotsPkAddresses vp.sl, isWotsPk a = true := by
    intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; rfl
  have h6 : ∀ a ∈ xmssNodeAddresses vp.sl, isWotsPk a = false := by
    intro a ha; simp only [xmssNodeAddresses, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  rw [slTreeAddresses]
  simp only [List.countP_append]
  rw [List.countP_eq_zero.2 (fun a ha => by rw [h1 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h2 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h3 a ha]; decide),
    List.countP_eq_zero.2 (fun a ha => by rw [h4 a ha]; decide),
    List.countP_eq_length.2 h5,
    List.countP_eq_zero.2 (fun a ha => by rw [h6 a ha]; decide)]
  omega

theorem evalNodeInput_isForsLeaf {a : Adrs} (ht : isForsLeaf a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.F, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isForsLeaf, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact ⟨_, rfl⟩

theorem evalNodeInput_isInternalH {a : Adrs} (ht : isInternalH a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.H, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isInternalH, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at ht
  rcases ht with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · simp only [evalNodeInput, h2, ↓reduceIte]; exact ⟨_, rfl⟩
  · by_cases h2' : w2 = 1
    · subst h2'; exact ⟨_, rfl⟩
    · simp only [evalNodeInput, h2, h2', ↓reduceIte]; exact ⟨_, rfl⟩

theorem evalNodeInput_isForsRoot {a : Adrs} (ht : isForsRoot a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.thK, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isForsRoot, beq_iff_eq] at ht
  subst ht
  exact ⟨_, rfl⟩

theorem evalNodeInput_isWotsStep {a : Adrs} (ht : isWotsStep a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.F, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isWotsStep, beq_iff_eq] at ht
  subst ht
  exact ⟨_, rfl⟩

theorem evalNodeInput_isWotsPk {a : Adrs} (ht : isWotsPk a = true)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) :
    ∃ msg, evalNodeInput pr u tbl a = some ⟨.thLsl, msg⟩ := by
  rcases a with ⟨l, tr, ty, w1, w2, w3⟩
  simp only [isWotsPk, beq_iff_eq] at ht
  subst ht
  exact ⟨_, rfl⟩

end RoutedVirtualTree

/-! ## 4. Stage-1 stateful FXMSS precomputation via `O_coll` (`sfPrecompM`, Claim 4.16) -/

section StatefulPrecomp

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Precomputed stateful FXMSS data produced in Stage 1 via `O_coll` (Claim 4.16): `PK.sf` and
the precomputed signature of every anchor (used in Stage 2 with zero stateful `Th_λ` calls). -/
structure SfPrecomp where
  pkSf : pr.Y
  sig : LeafId → Option (Scheme.Fxmss.Sig pr)

/-- Monadic bounded counter search (`WotsC.grind`) through `O_coll` at `SfAdrs.grindAdrs id`. -/
def sfGrindAuxM {m : Type → Type*} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (id : LeafId) (md : pr.Digest) :
    ℕ → m (Option (pr.Y × Fin (2 ^ vp.params.c)))
  | 0 => pure none
  | k + 1 => do
    let r ← sfGrindAuxM collCall id md k
    match r with
    | some v => pure (some v)
    | none =>
      if h : k < 2 ^ vp.params.c then do
        let c : Fin (2 ^ vp.params.c) := ⟨k, h⟩
        let d ← collCall .grind (SfAdrs.grindAdrs id).toAdrs (md, c)
        if WotsC.TargetSum pr d then pure (some (d, c)) else pure none
      else pure none

/-- Monadic WOTS+C chain computation through `O_coll` at `SfAdrs.chainAdrs id ch`. -/
def sfChainM {m : Type → Type*} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (id : LeafId) (ch : ℕ) (x : pr.Y) : ℕ → ℕ → m pr.Y
  | _, 0 => pure x
  | start, steps + 1 => do
    let prev ← sfChainM collCall id ch x start steps
    collCall .F (SfAdrs.chainAdrs id ch (start + steps)).toAdrs prev

/-- Monadic WOTS+C anchor precomputation: grinds counter, computes revealed chain blocks and
compressed anchor public key via `O_coll` (exclusively at `Scheme.IsStateful` addresses). -/
def sfAnchorM {m : Type → Type*} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (S : Structure) (dig : LeafId → pr.Digest) (u : Fxmss.Rom.SkIdx vp.params S → pr.Y)
    (id : LeafId) : m (Option (WotsC.Sig pr) × pr.Y) := do
  let g ← sfGrindAuxM pr collCall id (dig id) (2 ^ vp.params.c)
  match g with
  | some (d, c) =>
    let chains ← Vector.ofFnM fun ch : Fin vp.params.lsf =>
      sfChainM pr collCall id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (WotsC.digit pr d ch.val)
    let tops ← Vector.ofFnM fun ch : Fin vp.params.lsf =>
      let a := WotsC.digit pr d ch.val
      sfChainM pr collCall id ch.val chains[ch.val] a (vp.params.w - 1 - a)
    let pkLeaf ← collCall .thLsf (SfAdrs.pkAdrs id).toAdrs tops
    pure (some ⟨c, chains⟩, pkLeaf)
  | none =>
    let tops ← Vector.ofFnM fun ch : Fin vp.params.lsf =>
      sfChainM pr collCall id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (vp.params.w - 1)
    let pkLeaf ← collCall .thLsf (SfAdrs.pkAdrs id).toAdrs tops
    pure (none, pkLeaf)

/-- Monadic FXMSS tree evaluation storing every visited `(z, i)` node in a table `LeafId → Option pr.Y`
via `O_coll` at `SfAdrs.treeAdrs` (exclusively `Scheme.IsStateful`). -/
def sfTreeNodeM {m : Type → Type*} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (S : Structure) (leafTbl : LeafId → pr.Y) :
    ℕ → ℕ → (LeafId → Option pr.Y) → m (Option pr.Y × (LeafId → Option pr.Y))
  | 0, i, tbl =>
    if (⟨vp.params.hsf, i⟩ : Node) ∈ S.anchors then
      let v := leafTbl ⟨0, i⟩
      pure (some v, Function.update tbl ⟨0, i⟩ (some v))
    else pure (none, tbl)
  | z + 1, i, tbl =>
    if z + 1 ≤ vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∈ S.anchors then
      let v := leafTbl ⟨z + 1, i⟩
      pure (some v, Function.update tbl ⟨z + 1, i⟩ (some v))
    else if z + 1 ≤ vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∈ S.internal then do
      let (lOpt, tbl₁) ← sfTreeNodeM collCall S leafTbl z (2 * i) tbl
      let (rOpt, tbl₂) ← sfTreeNodeM collCall S leafTbl z (2 * i + 1) tbl₁
      match lOpt, rOpt with
      | some l, some r =>
        let v ← collCall .H (SfAdrs.treeAdrs ⟨z + 1, i⟩).toAdrs (l, r)
        pure (some v, Function.update tbl₂ ⟨z + 1, i⟩ (some v))
      | _, _ => pure (none, tbl₂)
    else pure (none, tbl)

/-- Read an authentication path from the precomputed FXMSS node table (zero `Th_λ` calls!). -/
def authPathFromTbl (nodeTbl : LeafId → Option pr.Y) : ℕ → ℕ → ℕ → Option (List pr.Y)
  | _, _, 0 => some []
  | z, i, s + 1 =>
    (nodeTbl ⟨z, Node.sibIdx i⟩).bind fun a =>
      (authPathFromTbl nodeTbl (z + 1) (i / 2) s).map (a :: ·)

/-- **Stage-1 stateful FXMSS precomputation via `O_coll` (Claim 4.16)**: computes `PK.sf` and
every anchor's FXMSS signature using `O_coll` exclusively at `Scheme.IsStateful` tweaks. -/
noncomputable def sfPrecompM {m : Type → Type*} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (S : Structure) (ys : Fxmss.Rom.Anchor vp.params S → pr.Digest)
    (u : Fxmss.Rom.SkIdx vp.params S → pr.Y) [Inhabited pr.Digest] : m (SfPrecomp pr) := do
  let anchors := Fxmss.Rom.anchorList vp.params S
  let (wotsTbl, leafTbl) ← anchors.foldlM
    (fun (acc : (LeafId → Option (WotsC.Sig pr)) × (LeafId → pr.Y)) id => do
      let (wOpt, lv) ← sfAnchorM pr collCall S (Fxmss.Rom.digOf pr ys) u id
      pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv))
    (fun _ => none, fun _ => default)
  let (rootOpt, nodeTbl) ← sfTreeNodeM pr collCall S leafTbl vp.params.hsf 0 (fun _ => none)
  pure {
    pkSf := rootOpt.getD default
    sig := fun id =>
      (wotsTbl id).bind fun w =>
        (authPathFromTbl pr nodeTbl id.height id.index (vp.params.hsf - id.height)).map fun auth =>
          ⟨w, auth⟩
  }

/-- Pure `Id`-monad member-evaluation callback for deterministic stateful precomputation. -/
def sfDetCall (pk : pr.PkSeed) (i : Primitives.Member) (a : Adrs) (msg : pr.MemberMsg i) :
    Id pr.Y :=
  pure (pr.memberEval i pk a msg)

/-- Deterministic evaluation of `sfPrecompM` at `PK.seed = pk`. -/
noncomputable def sfPrecompDet (pk : pr.PkSeed) (S : Structure)
    (ys : Fxmss.Rom.Anchor vp.params S → pr.Digest)
    (u : Fxmss.Rom.SkIdx vp.params S → pr.Y) [Inhabited pr.Digest] : SfPrecomp pr :=
  Id.run (sfPrecompM pr (sfDetCall pr pk) S ys u)

/-- Generic execution theorem for `sfPrecompM`: if `collCall` answers every `Scheme.IsStateful`
address `a` deterministically with `pr.memberEval i pk a msg` while preserving state invariant
`Inv`, then `sfPrecompM` returns `sfPrecompDet` deterministically and preserves `Inv`. -/
theorem simulateQ_sfPrecompM_run {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (pk : pr.PkSeed) (Inv : σ → Prop) (step : σ → Adrs → σ)
    (hcall : ∀ i a msg s, Scheme.IsStateful a → Inv s →
      (simulateQ impl (collCall i a msg)).run s = pure (pr.memberEval i pk a msg, step s a))
    (hinv : ∀ s a, Inv s → Scheme.IsStateful a → Inv (step s a))
    (S : Structure) (ys : Fxmss.Rom.Anchor vp.params S → pr.Digest)
    (u : Fxmss.Rom.SkIdx vp.params S → pr.Y) [Inhabited pr.Digest]
    (s : σ) (hs : Inv s) :
    ∃ s', Inv s' ∧
      (simulateQ impl (sfPrecompM pr collCall S ys u)).run s =
        pure (sfPrecompDet pr pk S ys u, s') := by
  have hgrind : ∀ id md k s, Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (sfGrindAuxM pr collCall id md k)).run s =
          pure (Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md k), s') := by
    intro id md k
    induction k with
    | zero => intro s hs; exact ⟨s, hs, by simp [sfGrindAuxM]⟩
    | succ k ih =>
      intro s hs
      obtain ⟨s₁, hs₁, h1⟩ := ih s hs
      simp only [sfGrindAuxM, simulateQ_bind, StateT.run_bind, h1, pure_bind, Id.run_bind]
      generalize hprev : Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md k) = prev
      cases prev with
      | some v =>
        refine ⟨s₁, hs₁, ?_⟩
        simp only [simulateQ_pure, StateT.run_pure, Id.run_pure]
      | none =>
        by_cases hk : k < 2 ^ vp.params.c
        · simp only [hk, ↓reduceDIte, simulateQ_bind, StateT.run_bind]
          have hsf : Scheme.IsStateful (SfAdrs.grindAdrs id).toAdrs := SfAdrs.isStateful_toAdrs _
          rw [hcall .grind (SfAdrs.grindAdrs id).toAdrs (md, ⟨k, hk⟩) s₁ hsf hs₁, pure_bind]
          refine ⟨step s₁ (SfAdrs.grindAdrs id).toAdrs, hinv s₁ _ hs₁ hsf, ?_⟩
          simp only [Id.run_bind, sfDetCall, Id.run_pure]
          split_ifs <;> simp
        · refine ⟨s₁, hs₁, ?_⟩
          simp only [hk, ↓reduceDIte, simulateQ_pure, StateT.run_pure, Id.run_pure]
  have hchain : ∀ id ch x start steps s, Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (sfChainM pr collCall id ch x start steps)).run s =
          pure (Id.run (sfChainM pr (sfDetCall pr pk) id ch x start steps), s') := by
    intro id ch x start steps
    induction steps with
    | zero => intro s hs; exact ⟨s, hs, by simp [sfChainM]⟩
    | succ steps ih =>
      intro s hs
      obtain ⟨s₁, hs₁, h1⟩ := ih s hs
      have hsf : Scheme.IsStateful (SfAdrs.chainAdrs id ch (start + steps)).toAdrs :=
        SfAdrs.isStateful_toAdrs _
      refine ⟨step s₁ _, hinv s₁ _ hs₁ hsf, ?_⟩
      simp only [sfChainM, simulateQ_bind, StateT.run_bind, h1, pure_bind, Id.run_bind,
        sfDetCall, Id.run_pure]
      exact hcall .F _ _ s₁ hsf hs₁
  have hvec : ∀ {n : ℕ} (f : Fin n → OracleComp spec pr.Y) (fDet : Fin n → pr.Y),
      (∀ (j : Fin n) s, Inv s → ∃ s', Inv s' ∧ (simulateQ impl (f j)).run s = pure (fDet j, s')) →
      ∀ s, Inv s → ∃ s', Inv s' ∧ (simulateQ impl (Vector.ofFnM f)).run s = pure (Vector.ofFn fDet, s') := by
    intro n
    induction n with
    | zero =>
      intro f fDet _ s hs
      refine ⟨s, hs, ?_⟩
      rw [Vector.ofFnM_zero, simulateQ_pure, StateT.run_pure]
      congr 1
    | succ n ih =>
      intro f fDet hf s hs
      obtain ⟨s₁, hs₁, h1⟩ := ih (fun j => f j.castSucc) (fun j => fDet j.castSucc)
        (fun j => hf j.castSucc) s hs
      obtain ⟨s₂, hs₂, h2⟩ := hf (Fin.last n) s₁ hs₁
      refine ⟨s₂, hs₂, ?_⟩
      rw [Vector.ofFnM_succ, simulateQ_bind, StateT.run_bind, h1, pure_bind,
        simulateQ_bind, StateT.run_bind, h2, pure_bind, simulateQ_pure, StateT.run_pure]
      congr 1
      refine Prod.ext (Vector.ext fun i hi => ?_) rfl
      by_cases hlt : i < n
      · simp [Vector.getElem_push_lt hlt]
      · have : i = n := by omega
        subst this; simp [Fin.last]
  have hvecId : ∀ {n : ℕ} (f : Fin n → Id pr.Y),
      Id.run (Vector.ofFnM f) = Vector.ofFn (fun j => Id.run (f j)) := by
    intro n
    induction n with
    | zero => intro f; rw [Vector.ofFnM_zero]; apply Vector.ext; intro i hi; omega
    | succ n ih =>
      intro f; rw [Vector.ofFnM_succ]; apply Vector.ext; intro i hi
      change ((Id.run (Vector.ofFnM (fun j : Fin n => f j.castSucc))).push (Id.run (f (Fin.last n))))[i] = _
      rw [ih (fun j => f j.castSucc)]
      by_cases hlt : i < n
      · simp [Vector.getElem_push_lt hlt]
      · have : i = n := by omega
        subst this; simp [Fin.last]
  have hanchor : ∀ id s, Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (sfAnchorM pr collCall S (Fxmss.Rom.digOf pr ys) u id)).run s =
          pure (Id.run (sfAnchorM pr (sfDetCall pr pk) S (Fxmss.Rom.digOf pr ys) u id), s') := by
    intro id s hs
    obtain ⟨s₁, hs₁, h1⟩ := hgrind id (Fxmss.Rom.digOf pr ys id) (2 ^ vp.params.c) s hs
    unfold sfAnchorM
    simp only [simulateQ_bind, StateT.run_bind, h1, pure_bind, Id.run_bind]
    generalize hg : Id.run (sfGrindAuxM pr (sfDetCall pr pk) id (Fxmss.Rom.digOf pr ys id) (2 ^ vp.params.c)) = g
    cases g with
    | some dc =>
      rcases dc with ⟨d, c⟩
      obtain ⟨s₂, hs₂, h2⟩ := hvec
        (fun ch : Fin vp.params.lsf => sfChainM pr collCall id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (WotsC.digit pr d ch.val))
        (fun ch : Fin vp.params.lsf => Id.run (sfChainM pr (sfDetCall pr pk) id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (WotsC.digit pr d ch.val)))
        (fun ch => hchain id ch.val _ 0 _) s₁ hs₁
      set chVec := Vector.ofFn (fun ch : Fin vp.params.lsf =>
        Id.run (sfChainM pr (sfDetCall pr pk) id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (WotsC.digit pr d ch.val)))
      obtain ⟨s₃, hs₃, h3⟩ := hvec
        (fun ch : Fin vp.params.lsf => sfChainM pr collCall id ch.val chVec[ch.val] (WotsC.digit pr d ch.val) (vp.params.w - 1 - WotsC.digit pr d ch.val))
        (fun ch : Fin vp.params.lsf => Id.run (sfChainM pr (sfDetCall pr pk) id ch.val chVec[ch.val] (WotsC.digit pr d ch.val) (vp.params.w - 1 - WotsC.digit pr d ch.val)))
        (fun ch => hchain id ch.val _ _ _) s₂ hs₂
      have hsf : Scheme.IsStateful (SfAdrs.pkAdrs id).toAdrs := SfAdrs.isStateful_toAdrs _
      refine ⟨step s₃ _, hinv s₃ _ hs₃ hsf, ?_⟩
      simp only [simulateQ_bind, StateT.run_bind, h2, pure_bind, h3, simulateQ_pure, StateT.run_pure,
        Id.run_bind, hvecId, sfDetCall, Id.run_pure]
      have hc := hcall .thLsf (SfAdrs.pkAdrs id).toAdrs
        (Vector.ofFn (fun ch : Fin vp.params.lsf =>
          Id.run (sfChainM pr (sfDetCall pr pk) id ch.val chVec[ch.val]
            (WotsC.digit pr d ch.val) (vp.params.w - 1 - WotsC.digit pr d ch.val)))) s₃ hsf hs₃
      exact (congrArg (fun m => m >>= fun p => pure ((some (WotsC.Sig.mk c chVec), p.1), p.2)) hc).trans (pure_bind _ _)
    | none =>
      obtain ⟨s₂, hs₂, h2⟩ := hvec
        (fun ch : Fin vp.params.lsf => sfChainM pr collCall id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (vp.params.w - 1))
        (fun ch : Fin vp.params.lsf => Id.run (sfChainM pr (sfDetCall pr pk) id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (vp.params.w - 1)))
        (fun ch => hchain id ch.val _ 0 _) s₁ hs₁
      have hsf : Scheme.IsStateful (SfAdrs.pkAdrs id).toAdrs := SfAdrs.isStateful_toAdrs _
      refine ⟨step s₂ _, hinv s₂ _ hs₂ hsf, ?_⟩
      simp only [simulateQ_bind, StateT.run_bind, h2, pure_bind, simulateQ_pure, StateT.run_pure,
        Id.run_bind, hvecId, sfDetCall, Id.run_pure]
      have hc := hcall .thLsf (SfAdrs.pkAdrs id).toAdrs
        (Vector.ofFn (fun ch : Fin vp.params.lsf =>
          Id.run (sfChainM pr (sfDetCall pr pk) id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (vp.params.w - 1)))) s₂ hsf hs₂
      exact (congrArg (fun m => m >>= fun p => pure ((none, p.1), p.2)) hc).trans (pure_bind _ _)
  have hfoldA : ∀ (l : List LeafId) (acc : (LeafId → Option (WotsC.Sig pr)) × (LeafId → pr.Y)) s, Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (l.foldlM (fun acc id => do
          let (wOpt, lv) ← sfAnchorM pr collCall S (Fxmss.Rom.digOf pr ys) u id
          pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv)) acc)).run s =
        pure (Id.run (l.foldlM (fun acc id => do
          let (wOpt, lv) ← sfAnchorM pr (sfDetCall pr pk) S (Fxmss.Rom.digOf pr ys) u id
          pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv)) acc), s') := by
    intro l
    induction l with
    | nil => intro acc s hs; exact ⟨s, hs, by simp⟩
    | cons id ids ih =>
      intro acc s hs
      obtain ⟨s₁, hs₁, h1⟩ := hanchor id s hs
      obtain ⟨s₂, hs₂, h2⟩ := ih _ s₁ hs₁
      refine ⟨s₂, hs₂, ?_⟩
      simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, h1, pure_bind,
        simulateQ_pure, StateT.run_pure]
      exact h2
  have htree : ∀ leafTbl z i tbl s, Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (sfTreeNodeM pr collCall S leafTbl z i tbl)).run s =
          pure (Id.run (sfTreeNodeM pr (sfDetCall pr pk) S leafTbl z i tbl), s') := by
    intro leafTbl z
    induction z with
    | zero =>
      intro i tbl s hs
      refine ⟨s, hs, ?_⟩
      unfold sfTreeNodeM
      split_ifs <;> simp
    | succ z ih =>
      intro i tbl s hs
      unfold sfTreeNodeM
      split_ifs with h1 h2
      · exact ⟨s, hs, by simp⟩
      · obtain ⟨s₁, hs₁, hl⟩ := ih (2 * i) tbl s hs
        obtain ⟨s₂, hs₂, hr⟩ := ih (2 * i + 1) _ s₁ hs₁
        simp only [simulateQ_bind, StateT.run_bind, hl, pure_bind, Id.run_bind]
        rw [hr, pure_bind]
        generalize hl' : Id.run (sfTreeNodeM pr (sfDetCall pr pk) S leafTbl z (2 * i) tbl) = rL
        generalize hr' : Id.run (sfTreeNodeM pr (sfDetCall pr pk) S leafTbl z (2 * i + 1) rL.2) = rR
        cases hL : rL.1 with
        | none =>
          refine ⟨s₂, hs₂, ?_⟩
          simp only [simulateQ_pure, StateT.run_pure, Id.run_pure]
        | some l =>
          cases hR : rR.1 with
          | none =>
            refine ⟨s₂, hs₂, ?_⟩
            simp only [simulateQ_pure, StateT.run_pure, Id.run_pure]
          | some r =>
            have hsf : Scheme.IsStateful (SfAdrs.treeAdrs ⟨z + 1, i⟩).toAdrs := SfAdrs.isStateful_toAdrs _
            refine ⟨step s₂ _, hinv s₂ _ hs₂ hsf, ?_⟩
            simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
              Id.run_bind, sfDetCall, Id.run_pure]
            rw [hcall .H (SfAdrs.treeAdrs ⟨z + 1, i⟩).toAdrs (l, r) s₂ hsf hs₂, pure_bind]
      · exact ⟨s, hs, by simp⟩
  obtain ⟨s₁, hs₁, h1⟩ := hfoldA (Fxmss.Rom.anchorList vp.params S) (fun _ => none, fun _ => default) s hs
  obtain ⟨s₂, hs₂, h2⟩ := htree _ vp.params.hsf 0 (fun _ => none) s₁ hs₁
  refine ⟨s₂, hs₂, ?_⟩
  unfold sfPrecompM sfPrecompDet
  simp only [simulateQ_bind, StateT.run_bind, h1, pure_bind]
  rw [h2, pure_bind, simulateQ_pure, StateT.run_pure]
  rfl

omit [Inhabited pr.Y] in
/-- Deterministic `sfGrindAuxM` over `2^c` counters equals `WotsC.grind`. -/
theorem sfGrindAuxM_det (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) :
    Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md (2 ^ vp.params.c)) = WotsC.grind pr pk id md := by
  have haux : ∀ k ≤ 2 ^ vp.params.c,
      let r := Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md k)
      (∀ d c, r = some (d, c) → c.val < k ∧ d = WotsC.encode pr pk id md c ∧ WotsC.TargetSum pr d ∧
        ∀ c' : Fin (2 ^ vp.params.c), c' < c → ¬ WotsC.TargetSum pr (WotsC.encode pr pk id md c')) ∧
      (r = none → ∀ c : Fin (2 ^ vp.params.c), c.val < k → ¬ WotsC.TargetSum pr (WotsC.encode pr pk id md c)) := by
    intro k hk
    induction k with
    | zero => exact ⟨fun _ _ h => by simp [sfGrindAuxM, Id.run] at h, fun _ c hc => by omega⟩
    | succ k ih =>
      obtain ⟨hS, hN⟩ := ih (by omega)
      have hstep : Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md (k + 1)) =
          match Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md k) with
          | some v => some v
          | none =>
            if h : k < 2 ^ vp.params.c then
              let d := WotsC.encode pr pk id md ⟨k, h⟩
              if WotsC.TargetSum pr d then some (d, ⟨k, h⟩) else none
            else none := rfl
      dsimp only
      rw [hstep]
      cases hprev : Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md k) with
      | some v =>
        rcases v with ⟨d₀, c₀⟩
        obtain ⟨hlt, he, hT, hmin⟩ := hS d₀ c₀ hprev
        refine ⟨(fun d c h => ?_), fun h => by cases h⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨by omega, he, hT, hmin⟩
      | none =>
        have hklt : k < 2 ^ vp.params.c := by omega
        simp only [hklt, ↓reduceDIte]
        by_cases hT : WotsC.TargetSum pr (WotsC.encode pr pk id md ⟨k, hklt⟩)
        · simp only [hT, ↓reduceIte]
          refine ⟨(fun d c h => ?_), fun h => by cases h⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨Nat.lt_succ_self k, rfl, hT, fun c' hc' => hN hprev c' hc'⟩
        · simp only [hT, ↓reduceIte]
          refine ⟨(fun _ _ h => by cases h), fun _ c hc => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | heq
          · exact hN hprev c hlt
          · have : c = ⟨k, hklt⟩ := Fin.ext heq
            subst this; exact hT
  obtain ⟨hS, hN⟩ := haux (2 ^ vp.params.c) le_rfl
  cases h : Id.run (sfGrindAuxM pr (sfDetCall pr pk) id md (2 ^ vp.params.c)) with
  | some dc =>
    obtain ⟨_, he, hT, hmin⟩ := hS dc.1 dc.2 h
    exact ((WotsC.grind_eq_some_iff pr).2 ⟨he, hT, hmin⟩).symm
  | none =>
    exact ((WotsC.grind_eq_none_iff pr).2 fun c => hN h c c.isLt).symm

omit [Inhabited pr.Y] in
/-- Deterministic `sfChainM` equals `WotsC.chain`. -/
theorem sfChainM_det (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (start : ℕ) :
    ∀ steps,
      Id.run (sfChainM pr (sfDetCall pr pk) id ch x start steps) =
        WotsC.chain pr pk id ch x start steps
  | 0 => rfl
  | steps + 1 => by
    change pr.F pk (SfAdrs.chainAdrs id ch (start + steps)).toAdrs
        (Id.run (sfChainM pr (sfDetCall pr pk) id ch x start steps)) =
      WotsC.chain pr pk id ch x start (steps + 1)
    rw [sfChainM_det pk id ch x start steps]
    exact (WotsC.chain_succ pr pk id ch x start steps).symm

/-- **Exactness of Stage-1 stateful FXMSS precomputation (`sfPrecompDet_eq_hon`)**: for every
valid structure `S`, `sfPrecompDet` equals `(H.pkSf, H.sig)` for `H := Fxmss.Rom.hon pr S pk
(digOf pr ys) (betaOf pr 0 pk u)`. -/
theorem sfPrecompDet_eq_hon {S : Structure} (hS : S.TreeValid vp.params.hsf) (pk : pr.PkSeed)
    (ys : Fxmss.Rom.Anchor vp.params S → pr.Digest)
    (u : Fxmss.Rom.SkIdx vp.params S → pr.Y) [Inhabited pr.Digest] :
    let H := Fxmss.Rom.hon pr S pk (Fxmss.Rom.digOf pr ys) (Fxmss.Rom.betaOf pr 0 pk u)
    (sfPrecompDet pr pk S ys u).pkSf = H.pkSf ∧
      ∀ id ∈ Structure.leafIds vp.params.hsf S, (sfPrecompDet pr pk S ys u).sig id = H.sig id := by
  intro H
  have hvecId : ∀ {n : ℕ} (f : Fin n → Id pr.Y),
      Id.run (Vector.ofFnM f) = Vector.ofFn (fun j => Id.run (f j)) := by
    intro n
    induction n with
    | zero => intro f; rw [Vector.ofFnM_zero]; apply Vector.ext; intro i hi; omega
    | succ n ih =>
      intro f; rw [Vector.ofFnM_succ]; apply Vector.ext; intro i hi
      change ((Id.run (Vector.ofFnM (fun j : Fin n => f j.castSucc))).push (Id.run (f (Fin.last n))))[i] = _
      rw [ih (fun j => f j.castSucc)]
      by_cases hlt : i < n
      · simp [Vector.getElem_push_lt hlt]
      · have : i = n := by omega
        subst this; simp [Fin.last]
  have hanchor : ∀ id,
      Id.run (sfAnchorM pr (sfDetCall pr pk)
        S (Fxmss.Rom.digOf pr ys) u id) =
      ((WotsC.grind pr pk id (H.dig id)).map fun _ => H.wots id, H.leafVal id) := by
    intro id
    unfold sfAnchorM
    change (match Id.run (sfGrindAuxM pr (sfDetCall pr pk)
        id (Fxmss.Rom.digOf pr ys id) (2 ^ vp.params.c)) with
      | some (d, c) => _
      | none => _) = _
    rw [sfGrindAuxM_det]
    cases hg : WotsC.grind pr pk id (Fxmss.Rom.digOf pr ys id) with
    | none =>
      change (none, pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs (Id.run (Vector.ofFnM fun ch : Fin vp.params.lsf =>
        sfChainM pr (sfDetCall pr pk) id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (vp.params.w - 1)))) = _
      rw [hvecId]
      simp only [H, Fxmss.Rom.hon, hg, Option.map_none, Prod.mk.injEq, true_and]
      congr 1; apply Vector.ext; intro ch hch
      simp only [Vector.getElem_ofFn, sfChainM_det, Fxmss.Rom.betaOf, Fxmss.Rom.blockVal]
      rfl
    | some dc =>
      rcases dc with ⟨d, c⟩
      set chVec := Id.run (Vector.ofFnM fun ch : Fin vp.params.lsf =>
        sfChainM pr (sfDetCall pr pk) id ch.val (Fxmss.Rom.skOf pr S u id ch.val) 0 (WotsC.digit pr d ch.val))
      have hchains : chVec = (Fxmss.Rom.blockSig pr (Fxmss.Rom.betaOf pr 0 pk u) id d c).chains := by
        rw [show chVec = Vector.ofFn (fun ch : Fin vp.params.lsf =>
          Id.run (sfChainM pr (sfDetCall pr pk) id ch.val
            (Fxmss.Rom.skOf pr S u id ch.val) 0 (WotsC.digit pr d ch.val))) from hvecId _]
        apply Vector.ext; intro ch hch
        simp only [Vector.getElem_ofFn, sfChainM_det, Fxmss.Rom.blockSig,
          Fxmss.Rom.Claim42.betaOf_zero]
      change (some (WotsC.Sig.mk c chVec),
        pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs (Id.run (Vector.ofFnM fun ch : Fin vp.params.lsf =>
          sfChainM pr (sfDetCall pr pk) id ch.val chVec[ch.val]
            (WotsC.digit pr d ch.val) (vp.params.w - 1 - WotsC.digit pr d ch.val)))) = _
      rw [hvecId]
      simp only [H, Fxmss.Rom.hon, hg, Option.map_some, Prod.mk.injEq]
      constructor
      · congr 1; exact congrArg (WotsC.Sig.mk c) hchains
      · congr 1; apply Vector.ext; intro ch hch
        simp only [Vector.getElem_ofFn, hchains, sfChainM_det, WotsC.topsFromSig]
  -- After folding over `anchors = anchorList`, `wotsTbl id` and `leafTbl id` agree with `H` on every anchor.
  set anchors := Fxmss.Rom.anchorList vp.params S
  have hfoldA : ∀ (l : List LeafId) (acc : (LeafId → Option (WotsC.Sig pr)) × (LeafId → pr.Y)),
      ∀ id ∈ l,
        (Id.run (l.foldlM (fun acc id => do
          let (wOpt, lv) ← sfAnchorM pr (sfDetCall pr pk)
            S (Fxmss.Rom.digOf pr ys) u id
          pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv)) acc)).1 id =
            (WotsC.grind pr pk id (H.dig id)).map (fun _ => H.wots id) ∧
        (Id.run (l.foldlM (fun acc id => do
          let (wOpt, lv) ← sfAnchorM pr (sfDetCall pr pk)
            S (Fxmss.Rom.digOf pr ys) u id
          pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv)) acc)).2 id = H.leafVal id := by
    intro l
    induction l with
    | nil => intro _ _ h; simp at h
    | cons id0 ids ih =>
      intro acc id hid
      have h1 := hanchor id0
      have hpres : ∀ (ls : List LeafId) (a0 : (LeafId → Option (WotsC.Sig pr)) × (LeafId → pr.Y))
          (x : LeafId),
          (a0.1 x = (WotsC.grind pr pk x (H.dig x)).map (fun _ => H.wots x) ∧ a0.2 x = H.leafVal x) →
          (Id.run (ls.foldlM (fun acc id => do
            let (wOpt, lv) ← sfAnchorM pr (sfDetCall pr pk)
              S (Fxmss.Rom.digOf pr ys) u id
            pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv)) a0)).1 x =
              (WotsC.grind pr pk x (H.dig x)).map (fun _ => H.wots x) ∧
          (Id.run (ls.foldlM (fun acc id => do
            let (wOpt, lv) ← sfAnchorM pr (sfDetCall pr pk)
              S (Fxmss.Rom.digOf pr ys) u id
            pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv)) a0)).2 x = H.leafVal x := by
        intro ls
        induction ls with
        | nil => intro a0 x hx; exact hx
        | cons y ys' ih' =>
          intro a0 x hx
          simp only [List.foldlM_cons, Id.run_bind, Id.run_pure]
          apply ih'
          have hy := hanchor y
          by_cases hxy : x = y
          · subst hxy; simp [hy]
          · simp [Function.update_of_ne hxy, hx]
      simp only [List.foldlM_cons, Id.run_bind, Id.run_pure]
      rcases List.mem_cons.1 hid with rfl | hid'
      · apply hpres
        simp [h1]
      · exact ih _ id hid'
  set resA := Id.run (anchors.foldlM (fun acc id => do
    let (wOpt, lv) ← sfAnchorM pr (sfDetCall pr pk)
      S (Fxmss.Rom.digOf pr ys) u id
    pure (Function.update acc.1 id wOpt, Function.update acc.2 id lv))
    (fun _ => none, fun _ => default))
  have hleafEq : ∀ id, id.height ≤ vp.params.hsf → Node.ofLeafId vp.params.hsf id ∈ S.anchors →
      resA.2 id = H.leafVal id := fun id hz hA => by
    have hmem : id ∈ anchors := by
      rw [Fxmss.Rom.mem_anchorList, Structure.leafIds, Finset.mem_image]
      exact ⟨Node.ofLeafId vp.params.hsf id, hA, by simp [Node.ofLeafId, Node.toLeafId, Nat.sub_sub_self hz]⟩
    exact (hfoldA anchors _ id hmem).2
  -- Show `sfTreeNodeM` computes `H.value z i` and stores every visited `S.nodes` member in `nodeTbl`.
  have htree : ∀ (z i : ℕ) (tbl : LeafId → Option pr.Y),
      (∀ w v, tbl w = some v → H.value w.height w.index = some v) →
      let r := Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 z i tbl)
      r.1 = H.value z i ∧
        (∀ w v, r.2 w = some v → H.value w.height w.index = some v) ∧
        (∀ w, tbl w ≠ none → r.2 w = tbl w) ∧
        (z ≤ vp.params.hsf → (⟨vp.params.hsf - z, i⟩ : Node) ∈ S.nodes →
          ∀ (z' i' : ℕ), z' ≤ z → i' / 2 ^ (z - z') = i →
            (⟨vp.params.hsf - z', i'⟩ : Node) ∈ S.nodes →
            r.2 ⟨z', i'⟩ = H.value z' i') := by
    intro z
    induction z with
    | zero =>
      intro i tbl hsound
      simp only [sfTreeNodeM, Fxmss.Rom.Honest.value, Tree.treeNode]
      by_cases hA : (⟨vp.params.hsf, i⟩ : Node) ∈ S.anchors
      · have hlv : resA.2 ⟨0, i⟩ = H.leafVal ⟨0, i⟩ := hleafEq ⟨0, i⟩ (Nat.zero_le _) hA
        have hAH : (⟨vp.params.hsf, i⟩ : Node) ∈ H.S.anchors := hA
        simp only [hA, hAH, ↓reduceIte, hlv, Id.run_pure]
        refine ⟨trivial, ?_, ?_, ?_⟩
        · intro w v hw
          by_cases hwi : w = ⟨0, i⟩
          · subst hwi; simp only [Function.update_self, Option.some.injEq] at hw
            subst hw; simp [Tree.treeNode, hAH]
          · simp only [Function.update_of_ne hwi] at hw; exact hsound w v hw
        · intro w hw
          by_cases hwi : w = ⟨0, i⟩
          · subst hwi
            obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hw
            have := hsound ⟨0, i⟩ v hv
            simp only [Fxmss.Rom.Honest.value, Tree.treeNode, hAH, ↓reduceIte, Option.some.injEq] at this
            simp [hv, this]
          · simp [Function.update_of_ne hwi]
        · intro _ _ z' i' hz' hdiv _
          have hz0 : z' = 0 := by omega
          subst hz0
          simp only [Nat.sub_self, pow_zero, Nat.div_one] at hdiv
          subst hdiv
          simp [Tree.treeNode, hAH]
      · have hAH : (⟨vp.params.hsf, i⟩ : Node) ∉ H.S.anchors := hA
        simp only [hA, hAH, ↓reduceIte, Id.run_pure]
        refine ⟨trivial, hsound, fun _ _ => trivial, ?_⟩
        intro _ hN _ _ _ _ _
        rcases Structure.mem_nodes.1 hN with hA' | hI
        · exact (hA (by simpa using hA')).elim
        · have := hS.internal_depth_lt hI; simp at this
    | succ z ih =>
      intro i tbl hsound
      by_cases hA : z + 1 ≤ vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∈ S.anchors
      · have hlv : resA.2 ⟨z + 1, i⟩ = H.leafVal ⟨z + 1, i⟩ := hleafEq ⟨z + 1, i⟩ hA.1 hA.2
        have hstep : Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 (z + 1) i tbl) =
            (some (H.leafVal ⟨z + 1, i⟩), Function.update tbl ⟨z + 1, i⟩ (some (H.leafVal ⟨z + 1, i⟩))) := by
          unfold sfTreeNodeM; simp only [hA, and_self, ↓reduceIte, hlv, Id.run_pure]
        have hval : H.value (z + 1) i = some (H.leafVal ⟨z + 1, i⟩) :=
          Tree.treeNode_anchor hA.1 hA.2
        dsimp only; rw [hstep]
        refine ⟨hval.symm, ?_, ?_, ?_⟩
        · intro w v hw
          by_cases hwi : w = ⟨z + 1, i⟩
          · subst hwi; simp only [Function.update_self, Option.some.injEq] at hw
            subst hw; exact hval
          · simp only [Function.update_of_ne hwi] at hw; exact hsound w v hw
        · intro w hw
          by_cases hwi : w = ⟨z + 1, i⟩
          · subst hwi
            obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hw
            have := hsound ⟨z + 1, i⟩ v hv
            rw [hval, Option.some.injEq] at this
            simp [hv, this]
          · simp [Function.update_of_ne hwi]
        · intro _ _ z' i' hz' hdiv hN'
          by_cases heq : z' = z + 1
          · subst heq
            simp only [Nat.sub_self, pow_zero, Nat.div_one] at hdiv
            subst hdiv
            simp [hval]
          · exfalso
            have hstep' : z + 1 - z' ≤ vp.params.hsf - z' := by omega
            have hanc_eq : (⟨vp.params.hsf - z', i'⟩ : Node).ancestor (z + 1 - z') =
                ⟨vp.params.hsf - (z + 1), i⟩ := by
              simp only [Node.ancestor, Node.mk.injEq]
              exact ⟨by omega, hdiv⟩
            exact hS.anchor_ne_ancestor hN' (by omega) hstep' (hanc_eq ▸ hA.2)
      · by_cases hI : z + 1 ≤ vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∈ S.internal
        · have hAnot : (⟨vp.params.hsf - (z + 1), i⟩ : Node) ∉ S.anchors := fun h => hA ⟨hI.1, h⟩
          have hl := ih (2 * i) tbl hsound
          set rL := Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 z (2 * i) tbl)
          have hr := ih (2 * i + 1) rL.2 hl.2.1
          set rR := Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 z (2 * i + 1) rL.2)
          have hval : H.value (z + 1) i = Option.map₂ (Scheme.Fxmss.node pr pk ⟨z + 1, i⟩) (H.value z (2 * i)) (H.value z (2 * i + 1)) :=
            Tree.treeNode_internal hI.1 hI.2 hAnot
          have hch0 : (⟨vp.params.hsf - z, 2 * i⟩ : Node) ∈ S.nodes := by
            have := hS.child_mem _ hI.2 false
            simpa [Node.child, show vp.params.hsf - (z + 1) + 1 = vp.params.hsf - z by omega] using this
          have hch1 : (⟨vp.params.hsf - z, 2 * i + 1⟩ : Node) ∈ S.nodes := by
            have := hS.child_mem _ hI.2 true
            simpa [Node.child, show vp.params.hsf - (z + 1) + 1 = vp.params.hsf - z by omega] using this
          obtain ⟨vl, hvl⟩ := Option.isSome_iff_exists.1 (Tree.treeNode_isSome hS z ⟨vp.params.hsf - z, 2 * i⟩ hch0 (by simp; omega))
          obtain ⟨vr, hvr⟩ := Option.isSome_iff_exists.1 (Tree.treeNode_isSome hS z ⟨vp.params.hsf - z, 2 * i + 1⟩ hch1 (by simp; omega))
          have hrL1 : rL.1 = some vl := hl.1.trans hvl
          have hrR1 : rR.1 = some vr := hr.1.trans hvr
          have hval_eq : H.value (z + 1) i = some (Scheme.Fxmss.node pr pk ⟨z + 1, i⟩ vl vr) := by
            rw [hval]
            change Option.map₂ (Scheme.Fxmss.node pr pk ⟨z + 1, i⟩)
              (Tree.treeNode vp.params.hsf S H.leafVal (Scheme.Fxmss.node pr H.pk) z (2 * i))
              (Tree.treeNode vp.params.hsf S H.leafVal (Scheme.Fxmss.node pr H.pk) z (2 * i + 1)) = _
            rw [hvl, hvr]; rfl
          have hstep : Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 (z + 1) i tbl) =
              (some (Scheme.Fxmss.node pr pk ⟨z + 1, i⟩ vl vr),
                Function.update rR.2 ⟨z + 1, i⟩ (some (Scheme.Fxmss.node pr pk ⟨z + 1, i⟩ vl vr))) := by
            unfold sfTreeNodeM
            simp only [hAnot, and_false, ↓reduceIte, hI, and_self, Id.run_bind]
            change (match rL.1, rR.1 with
              | some l, some r => Id.run (do
                  let v ← sfDetCall pr pk .H (SfAdrs.treeAdrs ⟨z + 1, i⟩).toAdrs (l, r)
                  pure (some v, Function.update rR.2 ⟨z + 1, i⟩ (some v)))
              | _, _ => (none, rR.2)) = _
            rw [hrL1, hrR1]
            simp only [Id.run_bind, sfDetCall, Id.run_pure]; rfl
          dsimp only; rw [hstep]
          refine ⟨hval_eq.symm, ?_, ?_, ?_⟩
          · intro w v hw
            by_cases hwi : w = ⟨z + 1, i⟩
            · subst hwi; simp only [Function.update_self, Option.some.injEq] at hw
              subst hw; exact hval_eq
            · simp only [Function.update_of_ne hwi] at hw; exact hr.2.1 w v hw
          · intro w hw
            dsimp only
            by_cases hwi : w = ⟨z + 1, i⟩
            · subst hwi
              obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hw
              have := hsound ⟨z + 1, i⟩ v hv
              rw [hval_eq, Option.some.injEq] at this
              simp [hv, this]
            · rw [Function.update_of_ne hwi, hr.2.2.1 w (by rw [hl.2.2.1 w hw]; exact hw), hl.2.2.1 w hw]
          · intro _ _ z' i' hz' hdiv hN'
            dsimp only
            by_cases heq : z' = z + 1
            · subst heq
              simp only [Nat.sub_self, pow_zero, Nat.div_one] at hdiv
              subst hdiv
              simp [hval_eq]
            · have hle : z' ≤ z := by omega
              have hne : (⟨z', i'⟩ : LeafId) ≠ ⟨z + 1, i⟩ := fun h => heq (congrArg LeafId.height h)
              rw [Function.update_of_ne hne]
              have hpow : 2 ^ (z + 1 - z') = 2 ^ (z - z') * 2 := by
                rw [show z + 1 - z' = (z - z') + 1 by omega, pow_succ]
              have hdiv2 : (i' / 2 ^ (z - z')) / 2 = i := by
                rw [Nat.div_div_eq_div_mul, ← hpow]; exact hdiv
              rcases Nat.mod_two_eq_zero_or_one (i' / 2 ^ (z - z')) with hm | hm
              · have hleft : i' / 2 ^ (z - z') = 2 * i := by omega
                have hl_val := hl.2.2.2 (by omega) hch0 z' i' hle hleft hN'
                have hne_none : rL.2 ⟨z', i'⟩ ≠ none := by
                  rw [hl_val]
                  exact Option.isSome_iff_ne_none.1 (Tree.treeNode_isSome hS z' ⟨vp.params.hsf - z', i'⟩ hN' (by simp; omega))
                rw [hr.2.2.1 ⟨z', i'⟩ hne_none, hl_val]
              · have hright : i' / 2 ^ (z - z') = 2 * i + 1 := by omega
                exact hr.2.2.2 (by omega) hch1 z' i' hle hright hN'
        · have hstep : Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 (z + 1) i tbl) = (none, tbl) := by
            unfold sfTreeNodeM; simp only [hA, hI, ↓reduceIte, Id.run_pure]
          have hval : H.value (z + 1) i = none := by
            change Tree.treeNode vp.params.hsf S H.leafVal (Scheme.Fxmss.node pr pk) (z + 1) i = none
            simp only [Tree.treeNode, hA, hI, ↓reduceIte]
          dsimp only; rw [hstep]
          refine ⟨hval.symm, hsound, fun _ _ => rfl, ?_⟩
          intro hz hN
          rcases Structure.mem_nodes.1 hN with hA' | hI'
          · exact (hA ⟨hz, hA'⟩).elim
          · exact (hI ⟨hz, hI'⟩).elim
  have hroot := htree vp.params.hsf 0 (fun _ => none) (fun _ _ h => by simp at h)
  set resT := Id.run (sfTreeNodeM pr (sfDetCall pr pk) S resA.2 vp.params.hsf 0 (fun _ => none))
  have hrootMem : (⟨0, 0⟩ : Node) ∈ S.nodes := Structure.internal_subset_nodes hS.root_mem
  have htblAll : ∀ z' i', z' ≤ vp.params.hsf → (⟨vp.params.hsf - z', i'⟩ : Node) ∈ S.nodes →
      resT.2 ⟨z', i'⟩ = H.value z' i' := by
    intro z' i' hz' hN'
    have hlt : i' < 2 ^ (vp.params.hsf - z') := hS.idx_lt_two_pow hN'
    exact hroot.2.2.2 le_rfl (by simpa using hrootMem) z' i' hz' (Nat.div_eq_of_lt hlt) hN'
  constructor
  · unfold sfPrecompDet sfPrecompM Fxmss.Rom.Honest.pkSf
    change resT.1.getD default = (H.value vp.params.hsf 0).getD default
    rw [hroot.1]
  · intro id hid
    have hid_a := (hfoldA anchors (fun _ => none, fun _ => default) id
      (Fxmss.Rom.mem_anchorList.2 hid)).1
    obtain ⟨v, hvA, hvEq⟩ := Finset.mem_image.1 hid
    have hdepth : v.depth ≤ vp.params.hsf := hS.anchor_depth_le v hvA
    have hid_v : Node.ofLeafId vp.params.hsf id = v := by
      rw [← hvEq]; exact Node.ofLeafId_toLeafId hdepth
    have hid_h : id.height ≤ vp.params.hsf := by rw [← hvEq]; exact Nat.sub_le _ _
    -- Show `authPathFromTbl resT.2 id.height id.index (hsf - id.height) = Tree.authPath ...`
    have hauth : ∀ (s z i : ℕ), z + s = vp.params.hsf →
        (⟨vp.params.hsf - z, i⟩ : Node) ∈ S.nodes →
        authPathFromTbl pr resT.2 z i s =
          Tree.authPath vp.params.hsf S H.leafVal (Scheme.Fxmss.node pr pk) z i s := by
      intro s
      induction s with
      | zero => intro _ _ _ _; rfl
      | succ s ih =>
        intro z i hzs hN
        have hnotroot : (⟨vp.params.hsf - z, i⟩ : Node) ≠ ⟨0, 0⟩ := by
          intro h; have := congrArg Node.depth h; simp at this; omega
        have hpar : (⟨vp.params.hsf - (z + 1), i / 2⟩ : Node) ∈ S.internal := by
          have := hS.parent_mem _ hN hnotroot
          exact (by simpa [Node.parent, show vp.params.hsf - z - 1 = vp.params.hsf - (z + 1) by omega] using this :
            z < vp.params.hsf ∧ (⟨vp.params.hsf - (z + 1), i / 2⟩ : Node) ∈ S.internal).2
        have hsib : (⟨vp.params.hsf - z, Node.sibIdx i⟩ : Node) ∈ S.nodes := by
          have hch := hS.child_mem _ hpar (decide (i % 2 = 0))
          rcases Nat.mod_two_eq_zero_or_one i with hm | hm
          · have h1 : 2 * (i / 2) + 1 = Node.sibIdx i := by simp [Node.sibIdx, hm]; omega
            simpa [Node.child, hm, h1, show vp.params.hsf - (z + 1) + 1 = vp.params.hsf - z by omega] using hch
          · have h1 : 2 * (i / 2) = Node.sibIdx i := by simp [Node.sibIdx, hm]; omega
            simpa [Node.child, hm, h1, show vp.params.hsf - (z + 1) + 1 = vp.params.hsf - z by omega] using hch
        simp only [authPathFromTbl, Tree.authPath]
        rw [htblAll z (Node.sibIdx i) (by omega) hsib,
          ih (z + 1) (i / 2) (by omega) (Structure.internal_subset_nodes hpar)]
        rfl
    unfold sfPrecompDet sfPrecompM Fxmss.Rom.Honest.sig
    change (resA.1 id).bind (fun w => (authPathFromTbl pr resT.2 id.height id.index
      (vp.params.hsf - id.height)).map fun auth => Scheme.Fxmss.Sig.mk w auth) = _
    rw [hid_a, hauth (vp.params.hsf - id.height) id.height id.index (by omega)
      (by rw [show (⟨vp.params.hsf - id.height, id.index⟩ : Node) = v from hid_v]; exact Structure.anchors_subset_nodes hvA)]
    have hpk : H.pk = pk := rfl
    have hS' : H.S = S := rfl
    rw [hpk, hS']
    cases WotsC.grind pr pk id (H.dig id) <;> simp

end StatefulPrecomp

end ShrincsSecurity.Slhdsa

