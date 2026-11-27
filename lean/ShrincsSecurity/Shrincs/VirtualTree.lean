module

public import ShrincsSecurity.Shrincs.AFBounds
public import ShrincsSecurity.Shrincs.PrfBound
public import ShrincsSecurity.Repro.Lazy
public import ShrincsSecurity.Fxmss.Members
public import ShrincsSecurity.Fxmss.Reduction

/-!
# Stage-1 virtual-hypertree precomputation via `O_coll` and zero-`Th_λ` Stage-2 table signing

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.15** (p. 65): the augmented reductions
`B₂⁺, …, B₈⁺` sample the uniform stateless secret elements `u_sl`, precompute `PK.sl` and the
entire virtual SLH-DSA hypertree in Stage 1 through the collection oracle `O_coll` before `PK.seed`
is revealed, and answer every stateless signing query in Stage 2 from the precomputed table without
evaluating any member of `Th_λ` on the stateless path.

This file provides the complete formal machinery for that construction:

1. **Eager stateless secrets** (`SlSecAdrs`, `slSecOf`): the finite domain `(slSecretList vp.sl)`
   of all secret-key addresses read by SLH-DSA key generation and signing (`PrfBound.lean`).
2. **Honest virtual-hypertree node function** (`honestVal`): the deterministic value of every node
   of `constructionAddresses vp.sl` given `(PK.seed, u_sl)`.
3. **Stage-1 `O_coll` precomputation** (`slVirtualTreeM`): a single bottom-up pass over VCVio's
   `constructionAddresses vp.sl` querying `O_coll` exclusively at stateless addresses
   (`Scheme.IsStateless`, types 0–4). Because all challenge tweaks of `B₂–B₈` (and their `Ω`-partners
   in `B₈`) are stateful (`Scheme.IsStateful`, types 16–22), `Scheme.not_isStateful_of_isStateless`
   guarantees that no `O_coll` query is refused and the challenge log is untouched.
4. **Stage-2 zero-`Th_λ` table signer** (`tablePubQ`, `slSignTable`): replaces `pubQ` with a pure
   table lookup for every `.thash` query (making zero calls to `Th`, `F`, `H`, `Th_k`, `Th_lsl`,
   `Th_lsf`, `H_grind`) and evaluates only `H_msg^sl`. When the table is complete (`TblComplete`),
   `slSignTable` equals `slSignDet` identically (`slSignTable_eq_slSignDet`).
5. **Eager-vs-lazy equivalence** (`gameHyb_AFEager_evalDistEq_gameHyb_AF`): sampling `u_sl` eagerly
   before `gameHyb 0` has the exact same distribution (`=ᵈ`) as `AF`'s lazy `SecCache`
   (`Repro.run'_evalDistEq_of_step` + `Repro.resample`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Shrincs

open Scheme SLHDSA.Security
open SLHDSA (Adrs AddrType Byte wotsSkAdrs wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsSkAdrs forsNodeAdrs forsPkAdrs chainWith chainStepsCore chainStepsCore_le
  wotsPkGenWithSecret wotsPkGenTopsWithSecret wotsSignWithSecret wotsPkFromSigWith
  xmssLeafWithSecret xmssNodeHashWith xmssNodeWithSecret xmssSignWithSecret xmssPkFromSigWith
  forsLeafWithSecret forsNodeHashWith forsSignWithSecret forsSignWithSecretM forsPkFromSigM
  forsIdx WotsSig XmssSigCore ForsTreeSigCore LayerPosition)
open Fxmss.Rom (Keys gameHyb stageHyb implHyb betaOf Honest St Transcript roIn completion otherMsg
  anchorList)

/-! ## 1. Eager stateless secrets -/

section EagerSecrets

/-- The finite set of all secret-key addresses read by SLH-DSA key generation and signing
(`WOTS_PRF` and `FORS_PRF` addresses of the reachable hypertree). -/
abbrev SlSecAdrs (vp : ValidatedParams) : Type :=
  {a : Adrs // a ∈ (slSecretList vp.sl).toFinset}

/-- Every address in `slSecretList` is a secret-key address (`WOTS_PRF` or `FORS_PRF`). -/
theorem isSecretKey_of_mem_slSecretList {vp : SLHDSA.ValidatedParams} {a : Adrs}
    (h : a ∈ slSecretList vp) : a.IsSecretKey := by
  simp only [slSecretList, List.mem_append, List.mem_map] at h
  rcases h with ⟨c, -, rfl⟩ | ⟨b, -, rfl⟩
  · exact Adrs.isSecretKey_wotsSkAdrs _ _
  · exact Adrs.isSecretKey_forsSkAdrs _ _

/-- Secret-key address witness for an element of `SlSecAdrs`. -/
def SlSecAdrs.toSecAdrs {vp : ValidatedParams} (a : SlSecAdrs vp) : SecAdrs :=
  ⟨a.1, isSecretKey_of_mem_slSecretList (List.mem_toFinset.1 a.2)⟩

/-- Look up an eager stateless secret table `u : SlSecAdrs vp → pr.Y` at any `Adrs`. -/
def slSecOf {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]
    (u : SlSecAdrs vp → pr.Y) (a : Adrs) : pr.Y :=
  if h : a ∈ (slSecretList vp.sl).toFinset then u ⟨a, h⟩ else default

end EagerSecrets

/-! ## 2. Honest virtual-hypertree node values -/

section HonestVal

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Structural rank of an SLH-DSA address, strictly decreasing along every edge of `childAdrs`. -/
def nodeRank (vp : ValidatedParams) (a : Adrs) : ℕ :=
  match a.type with
  | 0 => a.word3
  | 1 => vp.params.w
  | 2 => vp.params.w + a.word2
  | 3 => a.word2
  | 4 => vp.params.a + 1
  | _ => 0

/-- Fuel-indexed deterministic evaluation of the honest SLH-DSA node graph. -/
def honestValAux (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) : ℕ → Adrs → pr.Y
  | 0, _ => default
  | fuel + 1, a =>
    match a.type with
    | 0 =>
      if a.word3 = 0 then pr.F pk a (slSecOf pr u (wotsSkAdrs a a.word2))
      else pr.F pk a (honestValAux pk u fuel (a.setHashAddress (a.word3 - 1)))
    | 1 =>
      pr.ThLsl pk a (Vector.ofFn fun i : Fin vp.params.lsl =>
        honestValAux pk u fuel ((wotsChainAdrs a i.val).setHashAddress (vp.params.w - 2)))
    | 2 =>
      if a.word2 = 0 then default
      else if a.word2 = 1 then
        pr.H pk a
          (honestValAux pk u fuel (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3))))
          (honestValAux pk u fuel (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3 + 1))))
      else
        pr.H pk a
          (honestValAux pk u fuel (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3)))
          (honestValAux pk u fuel (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1)))
    | 3 =>
      if a.word2 = 0 then pr.F pk a (slSecOf pr u (forsSkAdrs a a.word3))
      else
        pr.H pk a
          (honestValAux pk u fuel (forsNodeAdrs a (a.word2 - 1) (2 * a.word3)))
          (honestValAux pk u fuel (forsNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1)))
    | 4 =>
      pr.ThK pk a (Vector.ofFn fun i : Fin vp.params.k =>
        honestValAux pk u fuel (forsNodeAdrs a vp.params.a i.val))
    | _ => default

/-- The honest value of node `a` of the virtual SLH-DSA hypertree for `(pk, u)`. -/
def honestVal (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (a : Adrs) : pr.Y :=
  honestValAux pr pk u (nodeRank vp a + 1) a

private theorem honestValAux_congr (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    ∀ f₁ f₂ a, nodeRank vp a < f₁ → nodeRank vp a < f₂ →
      honestValAux pr pk u f₁ a = honestValAux pr pk u f₂ a
  | 0, _, _, h₁, _ => (Nat.not_lt_zero _ h₁).elim
  | _, 0, _, _, h₂ => (Nat.not_lt_zero _ h₂).elim
  | f₁ + 1, f₂ + 1, a, h₁, h₂ => by
    have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
    rcases a with ⟨l, tr, ty, w1, w2, w3⟩
    rcases ty with _ | _ | _ | _ | _ | ty'
    · simp only [honestValAux]
      split_ifs with hw3
      · rfl
      · congr 1
        refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
          simp [nodeRank, Adrs.setHashAddress] at h₁ h₂ ⊢ <;> omega
    · simp only [honestValAux]
      congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
        simp [nodeRank, wotsChainAdrs, Adrs.setHashAddress, Adrs.setChainAddress,
          Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
    · simp only [honestValAux]
      split_ifs with hw2 hw2'
      · rfl
      · congr 1
        · refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
            simp [nodeRank, wotsPkAdrs, wotsLeafAdrs, Adrs.setKeyPairAddress,
              Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
        · refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
            simp [nodeRank, wotsPkAdrs, wotsLeafAdrs, Adrs.setKeyPairAddress,
              Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
      · congr 1
        · refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
            simp [nodeRank, xmssNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
              Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
        · refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
            simp [nodeRank, xmssNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
              Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
    · simp only [honestValAux]
      split_ifs with hw2
      · rfl
      · congr 1
        · refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
            simp [nodeRank, forsNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
              Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
        · refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
            simp [nodeRank, forsNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
              Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
    · simp only [honestValAux]
      congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      refine honestValAux_congr pk u f₁ f₂ _ ?_ ?_ <;>
        simp [nodeRank, forsNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
          Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode] at h₁ h₂ ⊢ <;> omega
    · simp only [honestValAux]

theorem honestValAux_eq_honestVal (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) {fuel : ℕ} {a : Adrs}
    (h : nodeRank vp a < fuel) : honestValAux pr pk u fuel a = honestVal pr pk u a :=
  honestValAux_congr pr pk u fuel (nodeRank vp a + 1) a h (Nat.lt_succ_self _)

theorem honestVal_wotsStep_zero (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (i : ℕ) :
    honestVal pr pk u ((wotsChainAdrs b i).setHashAddress 0) =
      pr.F pk ((wotsChainAdrs b i).setHashAddress 0) (slSecOf pr u (wotsSkAdrs b i)) := by
  simp only [honestVal, honestValAux, wotsChainAdrs, wotsSkAdrs, Adrs.setHashAddress,
    Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.getKeyPairAddress,
    AddrType.toCode, ↓reduceIte]

theorem honestVal_wotsStep_succ (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (i t : ℕ) :
    honestVal pr pk u ((wotsChainAdrs b i).setHashAddress (t + 1)) =
      pr.F pk ((wotsChainAdrs b i).setHashAddress (t + 1))
        (honestVal pr pk u ((wotsChainAdrs b i).setHashAddress t)) := by
  unfold honestVal
  have hr : nodeRank vp ((wotsChainAdrs b i).setHashAddress (t + 1)) = t + 1 := rfl
  rw [hr, honestValAux]
  change pr.F pk _ (honestValAux pr pk u (t + 1) ((wotsChainAdrs b i).setHashAddress t)) = _
  rw [honestValAux_eq_honestVal pr pk u (by simp [nodeRank, wotsChainAdrs, Adrs.setHashAddress,
    Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, AddrType.toCode])]
  rfl

theorem honestVal_wotsPk (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestVal pr pk u (wotsPkAdrs b) =
      pr.ThLsl pk (wotsPkAdrs b) (Vector.ofFn fun i : Fin vp.params.lsl =>
        honestVal pr pk u ((wotsChainAdrs b i.val).setHashAddress (vp.params.w - 2))) := by
  have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
  unfold honestVal
  have hr : nodeRank vp (wotsPkAdrs b) = vp.params.w := rfl
  rw [hr, honestValAux]
  change pr.ThLsl pk (wotsPkAdrs b) (Vector.ofFn fun i : Fin vp.params.lsl =>
    honestValAux pr pk u vp.params.w ((wotsChainAdrs (wotsPkAdrs b) i.val).setHashAddress
      (vp.params.w - 2))) = _
  congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
  have heq : (wotsChainAdrs (wotsPkAdrs b) i).setHashAddress (vp.params.w - 2) =
      (wotsChainAdrs b i).setHashAddress (vp.params.w - 2) := rfl
  rw [heq, honestValAux_eq_honestVal pr pk u]
  · rfl
  · change vp.params.w - 2 < vp.params.w; omega

theorem honestVal_xmssNode_one (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (j : ℕ) :
    honestVal pr pk u (xmssNodeAdrs b 1 j) =
      pr.H pk (xmssNodeAdrs b 1 j)
        (honestVal pr pk u (wotsPkAdrs (wotsLeafAdrs b (2 * j))))
        (honestVal pr pk u (wotsPkAdrs (wotsLeafAdrs b (2 * j + 1)))) := by
  unfold honestVal
  have hr : nodeRank vp (xmssNodeAdrs b 1 j) = vp.params.w + 1 := rfl
  rw [hr, honestValAux]
  change pr.H pk _
    (honestValAux pr pk u (vp.params.w + 1) (wotsPkAdrs (wotsLeafAdrs (xmssNodeAdrs b 1 j) (2 * j))))
    (honestValAux pr pk u (vp.params.w + 1) (wotsPkAdrs (wotsLeafAdrs (xmssNodeAdrs b 1 j) (2 * j + 1)))) = _
  have h1 : wotsPkAdrs (wotsLeafAdrs (xmssNodeAdrs b 1 j) (2 * j)) =
      wotsPkAdrs (wotsLeafAdrs b (2 * j)) := rfl
  have h2 : wotsPkAdrs (wotsLeafAdrs (xmssNodeAdrs b 1 j) (2 * j + 1)) =
      wotsPkAdrs (wotsLeafAdrs b (2 * j + 1)) := rfl
  rw [h1, h2, honestValAux_eq_honestVal pr pk u, honestValAux_eq_honestVal pr pk u]
  · rfl
  · simp [nodeRank, wotsPkAdrs, wotsLeafAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      AddrType.toCode]
  · simp [nodeRank, wotsPkAdrs, wotsLeafAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      AddrType.toCode]

theorem honestVal_xmssNode_succ (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) {z : ℕ}
    (hz : 1 ≤ z) (j : ℕ) :
    honestVal pr pk u (xmssNodeAdrs b (z + 1) j) =
      pr.H pk (xmssNodeAdrs b (z + 1) j)
        (honestVal pr pk u (xmssNodeAdrs b z (2 * j)))
        (honestVal pr pk u (xmssNodeAdrs b z (2 * j + 1))) := by
  unfold honestVal
  have hr : nodeRank vp (xmssNodeAdrs b (z + 1) j) = vp.params.w + (z + 1) := rfl
  rw [hr, honestValAux]
  have hne0 : (xmssNodeAdrs b (z + 1) j).word2 ≠ 0 := by
    simp only [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear]; omega
  have hne1 : (xmssNodeAdrs b (z + 1) j).word2 ≠ 1 := by
    simp only [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear]; omega
  have hty : (xmssNodeAdrs b (z + 1) j).type = 2 := rfl
  simp only [hty, hne0, hne1, ↓reduceIte]
  have h1 : xmssNodeAdrs (xmssNodeAdrs b (z + 1) j) ((xmssNodeAdrs b (z + 1) j).word2 - 1)
      (2 * (xmssNodeAdrs b (z + 1) j).word3) = xmssNodeAdrs b z (2 * j) := by
    simp [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear]
  have h2 : xmssNodeAdrs (xmssNodeAdrs b (z + 1) j) ((xmssNodeAdrs b (z + 1) j).word2 - 1)
      (2 * (xmssNodeAdrs b (z + 1) j).word3 + 1) = xmssNodeAdrs b z (2 * j + 1) := by
    simp [xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear]
  rw [h1, h2, honestValAux_eq_honestVal pr pk u, honestValAux_eq_honestVal pr pk u]
  · rfl
  · simp [nodeRank, xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear,
      AddrType.toCode]
  · simp [nodeRank, xmssNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setTypeAndClear,
      AddrType.toCode]

theorem honestVal_xmssCell_succ (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (z j : ℕ) :
    honestVal pr pk u (xmssCellAdrs b (z + 1) j) =
      pr.H pk (xmssNodeAdrs b (z + 1) j)
        (honestVal pr pk u (xmssCellAdrs b z (2 * j)))
        (honestVal pr pk u (xmssCellAdrs b z (2 * j + 1))) := by
  rcases z with _ | z
  · exact honestVal_xmssNode_one pr pk u b j
  · exact honestVal_xmssNode_succ pr pk u b (Nat.succ_pos z) j

theorem honestVal_forsLeaf (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (t : ℕ) :
    honestVal pr pk u (forsNodeAdrs b 0 t) =
      pr.F pk (forsNodeAdrs b 0 t) (slSecOf pr u (forsSkAdrs b t)) := by
  simp only [honestVal, honestValAux, forsNodeAdrs, forsSkAdrs, Adrs.setTreeIndex,
    Adrs.setTreeHeight, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.getKeyPairAddress,
    AddrType.toCode, ↓reduceIte]

theorem honestVal_forsNode_succ (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) (z j : ℕ) :
    honestVal pr pk u (forsNodeAdrs b (z + 1) j) =
      pr.H pk (forsNodeAdrs b (z + 1) j)
        (honestVal pr pk u (forsNodeAdrs b z (2 * j)))
        (honestVal pr pk u (forsNodeAdrs b z (2 * j + 1))) := by
  unfold honestVal
  have hr : nodeRank vp (forsNodeAdrs b (z + 1) j) = z + 1 := rfl
  rw [hr, honestValAux]
  change pr.H pk _
    (honestValAux pr pk u (z + 1) (forsNodeAdrs (forsNodeAdrs b (z + 1) j) z (2 * j)))
    (honestValAux pr pk u (z + 1) (forsNodeAdrs (forsNodeAdrs b (z + 1) j) z (2 * j + 1))) = _
  have h1 : forsNodeAdrs (forsNodeAdrs b (z + 1) j) z (2 * j) = forsNodeAdrs b z (2 * j) := rfl
  have h2 : forsNodeAdrs (forsNodeAdrs b (z + 1) j) z (2 * j + 1) =
      forsNodeAdrs b z (2 * j + 1) := rfl
  rw [h1, h2, honestValAux_eq_honestVal pr pk u, honestValAux_eq_honestVal pr pk u]
  · rfl
  · simp [nodeRank, forsNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setKeyPairAddress,
      Adrs.setTypeAndClear, AddrType.toCode]
  · simp [nodeRank, forsNodeAdrs, Adrs.setTreeIndex, Adrs.setTreeHeight, Adrs.setKeyPairAddress,
      Adrs.setTypeAndClear, AddrType.toCode]

theorem honestVal_forsPk (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (b : Adrs) :
    honestVal pr pk u (forsPkAdrs b) =
      pr.ThK pk (forsPkAdrs b) (Vector.ofFn fun i : Fin vp.params.k =>
        honestVal pr pk u (forsNodeAdrs b vp.params.a i.val)) := by
  unfold honestVal
  have hr : nodeRank vp (forsPkAdrs b) = vp.params.a + 1 := rfl
  rw [hr, honestValAux]
  change pr.ThK pk (forsPkAdrs b) (Vector.ofFn fun i : Fin vp.params.k =>
    honestValAux pr pk u (vp.params.a + 1) (forsNodeAdrs (forsPkAdrs b) vp.params.a i.val)) = _
  rfl

end HonestVal

/-! ## 3. Stage-1 `O_coll` precomputation of the virtual hypertree -/

section Precompute

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- Evaluate one node `a` of the virtual hypertree from the already-computed table `tbl` and
eager secrets `u`, issuing at most one query to `collCall` (always at a stateless address `a`). -/
def evalNodeM {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) (a : Adrs) : m pr.Y :=
  match a.type with
  | 0 =>
    if a.word3 = 0 then collCall .F a (slSecOf pr u (wotsSkAdrs a a.word2))
    else collCall .F a ((tbl (a.setHashAddress (a.word3 - 1))).getD default)
  | 1 =>
    collCall .thLsl a (Vector.ofFn fun i : Fin vp.params.lsl =>
      (tbl ((wotsChainAdrs a i.val).setHashAddress (vp.params.w - 2))).getD default)
  | 2 =>
    if a.word2 = 0 then pure default
    else if a.word2 = 1 then
      collCall .H a
        ((tbl (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3)))).getD default,
         (tbl (wotsPkAdrs (wotsLeafAdrs a (2 * a.word3 + 1)))).getD default)
    else
      collCall .H a
        ((tbl (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3))).getD default,
         (tbl (xmssNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1))).getD default)
  | 3 =>
    if a.word2 = 0 then collCall .F a (slSecOf pr u (forsSkAdrs a a.word3))
    else
      collCall .H a
        ((tbl (forsNodeAdrs a (a.word2 - 1) (2 * a.word3))).getD default,
         (tbl (forsNodeAdrs a (a.word2 - 1) (2 * a.word3 + 1))).getD default)
  | 4 =>
    collCall .thK a (Vector.ofFn fun i : Fin vp.params.k =>
      (tbl (forsNodeAdrs a vp.params.a i.val)).getD default)
  | _ => pure default

/-- The address of the top-layer XMSS root (`PK.sl`): layer `d - 1`, tree `0`, height `h'`,
index `0`. -/
def topRootAdrs (vp : ValidatedParams) : Adrs :=
  xmssNodeAdrs (LayerTreeCoord.top vp.sl).toAdrs vp.params.hp 0

/-- The explicit six-pass bottom-up address ledger of the virtual SLH-DSA hypertree
(same elements as VCVio's `constructionAddresses vp.sl`, exposed for bottom-up folding). -/
def slTreeAddresses (vp : ValidatedParams) : List Adrs :=
  forsLeafAddresses vp.sl ++ forsTreeAddresses vp.sl ++ forsRootAddresses vp.sl ++
    wotsStepAddresses vp.sl ++ wotsPkAddresses vp.sl ++ xmssNodeAddresses vp.sl

/-- **Stage-1 virtual-hypertree precomputation via `O_coll`**: evaluates every address in
`slTreeAddresses vp` bottom-up through `collCall` and returns `(PK.sl, tbl)`. -/
def slVirtualTreeM {m : Type → Type} [Monad m]
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → m pr.Y)
    (u : SlSecAdrs vp → pr.Y) : m (pr.Y × (Adrs → Option pr.Y)) := do
  let tbl ← (slTreeAddresses vp).foldlM (fun tbl a => do
    let v ← evalNodeM pr collCall u tbl a
    return Function.update tbl a (some v)) (fun _ => none)
  return ((tbl (topRootAdrs vp)).getD default, tbl)

/-- Pure deterministic version of `evalNodeM` (using `pr.memberEval pk`). -/
def evalNodeDet (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (a : Adrs) : pr.Y :=
  Id.run (evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a)

/-- Pure deterministic version of `slVirtualTreeM` (using `pr.memberEval pk`). -/
def slVirtualTreeDet (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) : pr.Y × (Adrs → Option pr.Y) :=
  Id.run (slVirtualTreeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u)

/-- Soundness of a partial virtual-hypertree table: every recorded entry equals `honestVal`. -/
def TblSound (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) : Prop :=
  ∀ a v, tbl a = some v → v = honestVal pr pk u a

/-- Completeness of a virtual-hypertree table on `constructionAddresses vp.sl`. -/
def TblComplete (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y) : Prop :=
  ∀ a ∈ constructionAddresses vp.sl, tbl a = some (honestVal pr pk u a)

private theorem tblSound_update {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y}
    {tbl : Adrs → Option pr.Y} (hs : TblSound pr pk u tbl) {a : Adrs} {v : pr.Y}
    (hv : v = honestVal pr pk u a) :
    TblSound pr pk u (Function.update tbl a (some v)) := by
  intro b w hb
  by_cases hba : b = a
  · subst hba; simp only [Function.update_self, Option.some.injEq] at hb; exact hb.symm.trans hv
  · rw [Function.update_of_ne hba] at hb; exact hs b w hb

private theorem tbl_update_preserves {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y}
    {tbl : Adrs → Option pr.Y} {a : Adrs} {v : pr.Y} (hv : v = honestVal pr pk u a)
    {b : Adrs} (hb : tbl b = some (honestVal pr pk u b)) :
    Function.update tbl a (some v) b = some (honestVal pr pk u b) := by
  by_cases hba : b = a
  · subst hba; simp [hv]
  · rw [Function.update_of_ne hba]; exact hb

private def stepTbl (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (tbl : Adrs → Option pr.Y)
    (a : Adrs) : Adrs → Option pr.Y :=
  Function.update tbl a (some (evalNodeDet pr pk u tbl a))

private theorem foldl_stepTbl_mono {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y} :
    ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      (∀ a ∈ l, ∀ tbl', TblSound pr pk u tbl' →
        (∀ x, tbl x = some (honestVal pr pk u x) → tbl' x = some (honestVal pr pk u x)) →
        evalNodeDet pr pk u tbl' a = honestVal pr pk u a) →
      TblSound pr pk u (l.foldl (stepTbl pr pk u) tbl) ∧
        (∀ x, tbl x = some (honestVal pr pk u x) →
          (l.foldl (stepTbl pr pk u) tbl) x = some (honestVal pr pk u x)) ∧
        (∀ a ∈ l, (l.foldl (stepTbl pr pk u) tbl) a = some (honestVal pr pk u a))
  | [], tbl, hs, _ => ⟨hs, fun _ h => h, fun _ h => by simp at h⟩
  | a :: as, tbl, hs, hev => by
    have hva : evalNodeDet pr pk u tbl a = honestVal pr pk u a :=
      hev a (by simp) tbl hs (fun _ h => h)
    let tbl₁ := stepTbl pr pk u tbl a
    have hs₁ : TblSound pr pk u tbl₁ := tblSound_update pr hs hva
    have hm₁ : ∀ x, tbl x = some (honestVal pr pk u x) →
        tbl₁ x = some (honestVal pr pk u x) := fun x hx => tbl_update_preserves pr hva hx
    have ha₁ : tbl₁ a = some (honestVal pr pk u a) := by simp [tbl₁, stepTbl, hva]
    have ih := foldl_stepTbl_mono as tbl₁ hs₁ (fun b hb tbl' hs' hsub =>
      hev b (by simp [hb]) tbl' hs' (fun x hx => hsub x (hm₁ x hx)))
    refine ⟨ih.1, fun x hx => ih.2.1 x (hm₁ x hx), fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact ih.2.1 x ha₁
    · exact ih.2.2 x hx'

/-- Generic bottom-up fold over `perfectInternalCoords h` shifted by height `off`. -/
private theorem foldl_perfectInternalCoords {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y}
    (addr : ℕ → ℕ → Adrs) (H : ℕ)
    (hstep : ∀ z j tbl, z < H → TblSound pr pk u tbl →
      tbl (addr z (2 * j)) = some (honestVal pr pk u (addr z (2 * j))) →
      tbl (addr z (2 * j + 1)) = some (honestVal pr pk u (addr z (2 * j + 1))) →
      evalNodeDet pr pk u tbl (addr (z + 1) j) = honestVal pr pk u (addr (z + 1) j)) :
    ∀ (h off : ℕ), off + h = H → ∀ (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      (∀ j < 2 ^ h, tbl (addr off j) = some (honestVal pr pk u (addr off j))) →
      let l := (perfectInternalCoords h).map fun zi => addr (zi.1 + off) zi.2
      TblSound pr pk u (l.foldl (stepTbl pr pk u) tbl) ∧
        (∀ x, tbl x = some (honestVal pr pk u x) →
          (l.foldl (stepTbl pr pk u) tbl) x = some (honestVal pr pk u x)) ∧
        (∀ a ∈ l, (l.foldl (stepTbl pr pk u) tbl) a = some (honestVal pr pk u a))
  | 0, _, _, tbl, hs, _ => ⟨hs, fun _ h => h, fun _ h => by simp [perfectInternalCoords] at h⟩
  | h + 1, off, hH, tbl, hs, hbase => by
    have hsplit : (perfectInternalCoords (h + 1)).map (fun zi => addr (zi.1 + off) zi.2) =
        ((List.range (2 ^ h)).map fun j => addr (off + 1) j) ++
          ((perfectInternalCoords h).map fun zi => addr (zi.1 + (off + 1)) zi.2) := by
      simp only [perfectInternalCoords, List.map_append, List.map_map]
      congr 1
      · apply List.map_congr_left; intro j _; dsimp only [Function.comp_apply]
        rw [Nat.add_comm 1 off]
      · apply List.map_congr_left; intro zi _; dsimp only [Function.comp_apply]
        have : zi.1 + 1 + off = zi.1 + (off + 1) := by omega
        rw [this]
    dsimp only
    rw [hsplit, List.foldl_append]
    set l₁ := (List.range (2 ^ h)).map fun j => addr (off + 1) j
    set l₂ := (perfectInternalCoords h).map fun zi => addr (zi.1 + (off + 1)) zi.2
    have hr₁ := foldl_stepTbl_mono pr l₁ tbl hs (fun a ha tbl' hs' hsub => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      rw [List.mem_range] at hj
      have h2j : 2 * j < 2 ^ (h + 1) := by rw [pow_succ]; omega
      have h2j1 : 2 * j + 1 < 2 ^ (h + 1) := by rw [pow_succ]; omega
      exact hstep off j tbl' (by omega) hs' (hsub _ (hbase _ h2j)) (hsub _ (hbase _ h2j1)))
    have hr₂ := foldl_perfectInternalCoords addr H hstep h (off + 1) (by omega)
      (l₁.foldl (stepTbl pr pk u) tbl) hr₁.1
      (fun j hj => hr₁.2.2 _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
    refine ⟨hr₂.1, fun x hx => hr₂.2.1 x (hr₁.2.1 x hx), fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha₁ | ha₂
    · exact hr₂.2.1 a (hr₁.2.2 a ha₁)
    · exact hr₂.2.2 a ha₂

private theorem foldl_product_step {α β : Type} {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y}
    (f : α → β → Adrs) (ls : List α) (rs : List β) (tbl : Adrs → Option pr.Y)
    (hs : TblSound pr pk u tbl)
    (hone : ∀ x ∈ ls, ∀ tbl', TblSound pr pk u tbl' →
      (∀ z, tbl z = some (honestVal pr pk u z) → tbl' z = some (honestVal pr pk u z)) →
      TblSound pr pk u ((rs.map (f x)).foldl (stepTbl pr pk u) tbl') ∧
        (∀ z, tbl' z = some (honestVal pr pk u z) →
          ((rs.map (f x)).foldl (stepTbl pr pk u) tbl') z = some (honestVal pr pk u z)) ∧
        (∀ a ∈ rs.map (f x),
          ((rs.map (f x)).foldl (stepTbl pr pk u) tbl') a = some (honestVal pr pk u a))) :
    let l := (ls.product rs).map fun p => f p.1 p.2
    TblSound pr pk u (l.foldl (stepTbl pr pk u) tbl) ∧
      (∀ z, tbl z = some (honestVal pr pk u z) →
        (l.foldl (stepTbl pr pk u) tbl) z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ l, (l.foldl (stepTbl pr pk u) tbl) a = some (honestVal pr pk u a)) := by
  induction ls generalizing tbl with
  | nil =>
    exact ⟨hs, fun _ h => h, fun _ h => by simp [List.product] at h⟩
  | cons x xs ih =>
    have hprod : ((x :: xs).product rs).map (fun p => f p.1 p.2) =
        rs.map (f x) ++ (xs.product rs).map (fun p => f p.1 p.2) := by
      simp [List.product, List.flatMap_cons, List.map_append, List.map_map, Function.comp_def]
    dsimp only
    rw [hprod, List.foldl_append]
    have hx := hone x (by simp) tbl hs (fun _ h => h)
    have hxs := ih ((rs.map (f x)).foldl (stepTbl pr pk u) tbl) hx.1
      (fun y hy tbl' hs' hsub => hone y (by simp [hy]) tbl' hs' (fun z hz => hsub z (hx.2.1 z hz)))
    refine ⟨hxs.1, fun z hz => hxs.2.1 z (hx.2.1 z hz), fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha₁ | ha₂
    · exact hxs.2.1 a (hx.2.2 a ha₁)
    · exact hxs.2.2 a ha₂

private theorem foldl_wotsSteps {pk : pr.PkSeed} {u : SlSecAdrs vp → pr.Y}
    (b : Adrs) (ch : ℕ) :
    ∀ (m : ℕ) (tbl : Adrs → Option pr.Y),
      TblSound pr pk u tbl →
      let l := (List.range m).map fun t => (wotsChainAdrs b ch).setHashAddress t
      TblSound pr pk u (l.foldl (stepTbl pr pk u) tbl) ∧
        (∀ z, tbl z = some (honestVal pr pk u z) →
          (l.foldl (stepTbl pr pk u) tbl) z = some (honestVal pr pk u z)) ∧
        (∀ a ∈ l, (l.foldl (stepTbl pr pk u) tbl) a = some (honestVal pr pk u a))
  | 0, tbl, hs => ⟨hs, fun _ h => h, fun _ h => by simp at h⟩
  | m + 1, tbl, hs => by
    dsimp only
    rw [List.range_succ, List.map_append, List.foldl_append]
    have ih := foldl_wotsSteps b ch m tbl hs
    set l₁ := (List.range m).map fun t => (wotsChainAdrs b ch).setHashAddress t
    set tbl₁ := l₁.foldl (stepTbl pr pk u) tbl
    have hev : evalNodeDet pr pk u tbl₁ ((wotsChainAdrs b ch).setHashAddress m) =
        honestVal pr pk u ((wotsChainAdrs b ch).setHashAddress m) := by
      rcases m with _ | m
      · rw [honestVal_wotsStep_zero]; rfl
      · rw [honestVal_wotsStep_succ]
        have hprev : tbl₁ ((wotsChainAdrs b ch).setHashAddress m) =
            some (honestVal pr pk u ((wotsChainAdrs b ch).setHashAddress m)) :=
          ih.2.2 _ (List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_self m), rfl⟩)
        unfold evalNodeDet evalNodeM
        have hty : ((wotsChainAdrs b ch).setHashAddress (m + 1)).type = 0 := rfl
        have hw3 : ((wotsChainAdrs b ch).setHashAddress (m + 1)).word3 = m + 1 := rfl
        simp only [hty, hw3, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, Primitives.memberEval, Id.run]
        have hset : ((wotsChainAdrs b ch).setHashAddress (m + 1)).setHashAddress m =
            (wotsChainAdrs b ch).setHashAddress m := rfl
        rw [hset, hprev, Option.getD_some]
    have hs₂ : TblSound pr pk u (stepTbl pr pk u tbl₁ ((wotsChainAdrs b ch).setHashAddress m)) :=
      tblSound_update pr ih.1 hev
    have hm₂ : ∀ z, tbl₁ z = some (honestVal pr pk u z) →
        (stepTbl pr pk u tbl₁ ((wotsChainAdrs b ch).setHashAddress m)) z =
          some (honestVal pr pk u z) :=
      fun z hz => tbl_update_preserves pr hev hz
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    refine ⟨hs₂, fun z hz => hm₂ z (ih.2.1 z hz), fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha₁ | ha₂
    · exact hm₂ a (ih.2.2 a ha₁)
    · simp only [List.mem_singleton] at ha₂
      subst ha₂
      simp [stepTbl, hev]

/-- The deterministic virtual-hypertree pass fills every address in `constructionAddresses vp.sl`
with its exact `honestVal`, and returns `honestVal pk u (topRootAdrs vp)` as `PK.sl`. -/
theorem slVirtualTreeDet_spec (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    (slVirtualTreeDet pr pk u).1 = honestVal pr pk u (topRootAdrs vp) ∧
      TblSound pr pk u (slVirtualTreeDet pr pk u).2 ∧
      TblComplete pr pk u (slVirtualTreeDet pr pk u).2 := by
  have hfold : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y),
      Id.run (l.foldlM (fun tbl a => do
        let v ← evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a
        return Function.update tbl a (some v)) tbl) = l.foldl (stepTbl pr pk u) tbl := by
    intro l
    induction l with
    | nil => intro tbl; rfl
    | cons a as ih => intro tbl; exact ih (stepTbl pr pk u tbl a)
  have hdet2 : (slVirtualTreeDet pr pk u).2 =
      (slTreeAddresses vp).foldl (stepTbl pr pk u) (fun _ => none) := by
    change Id.run ((slTreeAddresses vp).foldlM _ (fun _ => none)) = _
    exact hfold _ _
  have hdet1 : (slVirtualTreeDet pr pk u).1 =
      ((slVirtualTreeDet pr pk u).2 (topRootAdrs vp)).getD default := rfl
  have hca : slTreeAddresses vp =
      forsLeafAddresses vp.sl ++ forsTreeAddresses vp.sl ++ forsRootAddresses vp.sl ++
      wotsStepAddresses vp.sl ++ wotsPkAddresses vp.sl ++ xmssNodeAddresses vp.sl := rfl
  set t0 : Adrs → Option pr.Y := fun _ => none
  have hs0 : TblSound pr pk u t0 := fun _ _ h => by simp [t0] at h
  -- Pass 1: FORS leaves
  set t1 := (forsLeafAddresses vp.sl).foldl (stepTbl pr pk u) t0
  have hp1 := foldl_stepTbl_mono pr (forsLeafAddresses vp.sl) t0 hs0 (fun a ha tbl' _ _ => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
    rw [honestVal_forsLeaf]
    rfl)
  -- Pass 2: FORS internal nodes
  set t2 := (forsTreeAddresses vp.sl).foldl (stepTbl pr pk u) t1
  have hp2 : TblSound pr pk u t2 ∧
      (∀ z, t1 z = some (honestVal pr pk u z) → t2 z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ forsTreeAddresses vp.sl, t2 a = some (honestVal pr pk u a)) := by
    change TblSound pr pk u ((forsTreeAddresses vp.sl).foldl (stepTbl pr pk u) t1) ∧ _
    unfold forsTreeAddresses
    refine foldl_product_step pr
      (fun (pt : BottomPosition vp.sl × Fin vp.sl.params.k) (zi : ℕ × ℕ) =>
        forsNodeAdrs pt.1.forsAdrs zi.1 (pt.2.val * 2 ^ (vp.sl.params.a - zi.1) + zi.2))
      ((allBottomPositions vp.sl).product (List.finRange vp.sl.params.k))
      (perfectInternalCoords vp.sl.params.a) t1 hp1.1 ?_
    intro pt hpt tbl' hs' hsub
    have hmap : ((perfectInternalCoords vp.sl.params.a).map fun zi =>
          forsNodeAdrs pt.1.forsAdrs zi.1 (pt.2.val * 2 ^ (vp.sl.params.a - zi.1) + zi.2)) =
        ((perfectInternalCoords vp.sl.params.a).map fun zi =>
          forsNodeAdrs pt.1.forsAdrs (zi.1 + 0)
            (pt.2.val * 2 ^ (vp.sl.params.a - (zi.1 + 0)) + zi.2)) := by
      simp
    rw [hmap]
    refine foldl_perfectInternalCoords pr
      (fun z j => forsNodeAdrs pt.1.forsAdrs z (pt.2.val * 2 ^ (vp.sl.params.a - z) + j))
      vp.sl.params.a
      (fun z j tbl'' hza _ hl hr => by
        have hsub1 : vp.sl.params.a - z = vp.sl.params.a - (z + 1) + 1 := by omega
        have hidx0 : 2 * (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) =
            pt.2.val * 2 ^ (vp.sl.params.a - z) + 2 * j := by rw [hsub1, pow_succ]; ring
        have hidx1 : 2 * (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j) + 1 =
            pt.2.val * 2 ^ (vp.sl.params.a - z) + (2 * j + 1) := by rw [hsub1, pow_succ]; ring
        rw [honestVal_forsNode_succ]
        unfold evalNodeDet evalNodeM
        have hty : (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).type = 3 := rfl
        have hw2 : (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).word2 = z + 1 := rfl
        have hw3 : (forsNodeAdrs pt.1.forsAdrs (z + 1)
            (pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j)).word3 =
            pt.2.val * 2 ^ (vp.sl.params.a - (z + 1)) + j := rfl
        simp only [hty, hw2, hw3, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, Primitives.memberEval, Id.run]
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
        rw [hf0, hf1, hl, hr, Option.getD_some, Option.getD_some, ← hidx0, ← hidx1]
      )
      vp.sl.params.a 0 (Nat.zero_add _) tbl' hs' (fun j hj =>
        hsub _ (hp1.2.2 _ (by
          simpa [SLHDSA.Params.t] using mem_forsLeafAddresses vp.sl pt.1 pt.2 ⟨j, hj⟩)))
  -- Pass 3: FORS roots
  set t3 := (forsRootAddresses vp.sl).foldl (stepTbl pr pk u) t2
  have hp3 := foldl_stepTbl_mono pr (forsRootAddresses vp.sl) t2 hp2.1 (fun a ha tbl' _ hsub => by
    obtain ⟨pos, -, rfl⟩ := List.mem_map.1 ha
    rw [honestVal_forsPk]
    unfold evalNodeDet evalNodeM
    have hty : (forsPkAdrs pos.forsAdrs).type = 4 := rfl
    simp only [hty, Primitives.memberEval, Id.run]
    congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
    have hmem : forsNodeAdrs pos.forsAdrs vp.params.a i ∈ forsTreeAddresses vp.sl := by
      have ha_pos : 0 < vp.sl.params.a := vp.valid.a_pos
      have hm := mem_forsTreeAddresses vp.sl pos ⟨i, hi⟩ ha_pos le_rfl
        (by simp : 0 < 2 ^ (vp.sl.params.a - vp.sl.params.a))
      have hidx : i * 2 ^ (vp.sl.params.a - vp.sl.params.a) + 0 = i := by simp
      rw [hidx] at hm
      exact hm
    have heq : forsNodeAdrs (forsPkAdrs pos.forsAdrs) vp.params.a i =
        forsNodeAdrs pos.forsAdrs vp.params.a i := rfl
    rw [heq, hsub _ (hp2.2.2 _ hmem), Option.getD_some])
  -- Pass 4: WOTS+ chain steps
  set t4 := (wotsStepAddresses vp.sl).foldl (stepTbl pr pk u) t3
  have hp4 : TblSound pr pk u t4 ∧
      (∀ z, t3 z = some (honestVal pr pk u z) → t4 z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ wotsStepAddresses vp.sl, t4 a = some (honestVal pr pk u a)) := by
    change TblSound pr pk u ((wotsStepAddresses vp.sl).foldl (stepTbl pr pk u) t3) ∧ _
    unfold wotsStepAddresses
    refine foldl_product_step pr
      (fun (c : WotsChainCoord vp.sl) (s : Fin (vp.sl.params.w - 1)) => wotsStepAdrs c s)
      (allWotsChains vp.sl) (List.finRange (vp.sl.params.w - 1)) t3 hp3.1 ?_
    intro c _ tbl' hs' _
    have hfin : (List.finRange (vp.sl.params.w - 1)).map (wotsStepAdrs c) =
        (List.range (vp.sl.params.w - 1)).map fun t =>
          (wotsChainAdrs (wotsInstanceAdrs c.1) c.2.val).setHashAddress t := by
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        simp [wotsStepAdrs]
    rw [hfin]
    exact foldl_wotsSteps pr (wotsInstanceAdrs c.1) c.2.val (vp.sl.params.w - 1) tbl' hs'
  -- Pass 5: WOTS+ public keys
  set t5 := (wotsPkAddresses vp.sl).foldl (stepTbl pr pk u) t4
  have hp5 := foldl_stepTbl_mono pr (wotsPkAddresses vp.sl) t4 hp4.1 (fun a ha tbl' _ hsub => by
    obtain ⟨pos, -, rfl⟩ := List.mem_map.1 ha
    rw [honestVal_wotsPk]
    unfold evalNodeDet evalNodeM
    have hty : (wotsPkAdrs (wotsInstanceAdrs pos)).type = 1 := rfl
    simp only [hty, Primitives.memberEval, Id.run]
    congr 1; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
    have hi' : i < vp.sl.params.len := by rw [← Params.lsl_eq_len vp.valid]; exact hi
    have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
    have hw2 : vp.params.w - 2 < vp.sl.params.w - 1 := by
      change vp.params.w - 2 < vp.params.w - 1; omega
    have hmem : (wotsChainAdrs (wotsInstanceAdrs pos) i).setHashAddress (vp.params.w - 2) ∈
        wotsStepAddresses vp.sl :=
      mem_wotsStepAddresses vp.sl (pos, ⟨i, hi'⟩) ⟨vp.params.w - 2, hw2⟩
    have heq : (wotsChainAdrs (wotsPkAdrs (wotsInstanceAdrs pos)) i).setHashAddress
        (vp.params.w - 2) =
        (wotsChainAdrs (wotsInstanceAdrs pos) i).setHashAddress (vp.params.w - 2) := rfl
    rw [heq, hsub _ (hp4.2.2 _ hmem), Option.getD_some])
  -- Pass 6: XMSS internal nodes
  set t6 := (xmssNodeAddresses vp.sl).foldl (stepTbl pr pk u) t5
  have hp6 : TblSound pr pk u t6 ∧
      (∀ z, t5 z = some (honestVal pr pk u z) → t6 z = some (honestVal pr pk u z)) ∧
      (∀ a ∈ xmssNodeAddresses vp.sl, t6 a = some (honestVal pr pk u a)) := by
    change TblSound pr pk u ((xmssNodeAddresses vp.sl).foldl (stepTbl pr pk u) t5) ∧ _
    unfold xmssNodeAddresses
    refine foldl_product_step pr
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
    refine foldl_perfectInternalCoords pr (xmssCellAdrs coord.toAdrs) vp.sl.params.hp
      (fun z j tbl'' _ _ hl hr => by
        rw [honestVal_xmssCell_succ]
        unfold evalNodeDet evalNodeM
        rcases z with _ | z
        · have hty : (xmssCellAdrs coord.toAdrs 1 j).type = 2 := rfl
          have hw2 : (xmssCellAdrs coord.toAdrs 1 j).word2 = 1 := rfl
          have hw3 : (xmssCellAdrs coord.toAdrs 1 j).word3 = j := rfl
          simp only [hty, hw2, hw3, one_ne_zero, ↓reduceIte, Primitives.memberEval, Id.run]
          have h1 : wotsPkAdrs (wotsLeafAdrs (xmssCellAdrs coord.toAdrs 1 j) (2 * j)) =
              xmssCellAdrs coord.toAdrs 0 (2 * j) := rfl
          have h2 : wotsPkAdrs (wotsLeafAdrs (xmssCellAdrs coord.toAdrs 1 j) (2 * j + 1)) =
              xmssCellAdrs coord.toAdrs 0 (2 * j + 1) := rfl
          rw [h1, h2, hl, hr, Option.getD_some, Option.getD_some]; rfl
        · have hty : (xmssCellAdrs coord.toAdrs (z + 2) j).type = 2 := rfl
          have hw2 : (xmssCellAdrs coord.toAdrs (z + 2) j).word2 = z + 2 := rfl
          have hw3 : (xmssCellAdrs coord.toAdrs (z + 2) j).word3 = j := rfl
          have hne0 : z + 2 ≠ 0 := by omega
          have hne1 : z + 2 ≠ 1 := by omega
          simp only [hty, hw2, hw3, hne0, hne1, ↓reduceIte, Primitives.memberEval, Id.run]
          have h1 : xmssNodeAdrs (xmssCellAdrs coord.toAdrs (z + 2) j) (z + 2 - 1) (2 * j) =
              xmssCellAdrs coord.toAdrs (z + 1) (2 * j) := rfl
          have h2 : xmssNodeAdrs (xmssCellAdrs coord.toAdrs (z + 2) j) (z + 2 - 1) (2 * j + 1) =
              xmssCellAdrs coord.toAdrs (z + 1) (2 * j + 1) := rfl
          rw [h1, h2, hl, hr, Option.getD_some, Option.getD_some]; rfl)
      vp.sl.params.hp 0 (Nat.zero_add _) tbl' hs' (fun j hj => by
        have hpos : wotsPkAdrs (wotsInstanceAdrs ⟨coord.layer, coord.tree, ⟨j, hj⟩⟩) ∈
            wotsPkAddresses vp.sl := mem_wotsPkAddresses vp.sl _
        exact hsub _ (hp5.2.2 _ hpos))
  -- Combine all 6 passes
  have ht6_eq : (slVirtualTreeDet pr pk u).2 = t6 := by
    rw [hdet2, hca]
    simp only [List.foldl_append]
    rfl
  have hcomp : TblComplete pr pk u t6 := by
    intro a ha
    rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
    · exact hp6.2.1 _ (hp5.2.1 _ (hp4.2.1 _ (hp3.2.1 _ (hp2.2.1 _ (hp1.2.2 _ h)))))
    · exact hp6.2.1 _ (hp5.2.1 _ (hp4.2.1 _ (hp3.2.1 _ (hp2.2.2 _ h))))
    · exact hp6.2.1 _ (hp5.2.1 _ (hp4.2.1 _ (hp3.2.2 _ h)))
    · exact hp6.2.1 _ (hp5.2.1 _ (hp4.2.2 _ h))
    · exact hp6.2.1 _ (hp5.2.2 _ h)
    · exact hp6.2.2 _ h
  have htop_mem : topRootAdrs vp ∈ constructionAddresses vp.sl :=
    xmssNodeAdrs_mem_constructionAddresses (LayerTreeCoord.top vp.sl) vp.valid.hp_pos le_rfl
      (by simp)
  refine ⟨?_, ht6_eq ▸ hp6.1, ht6_eq ▸ hcomp⟩
  rw [hdet1, ht6_eq, hcomp _ htop_mem, Option.getD_some]

/-! ## 4. Exact execution of `slVirtualTreeM` against any collection oracle -/

/-- Generic execution lemma: if `collCall` answers every stateless address `a` deterministically
with `pr.memberEval i pk a msg` while preserving state invariant `Inv`, then `slVirtualTreeM`
returns `slVirtualTreeDet pr pk u` deterministically and preserves `Inv`. -/
theorem simulateQ_slVirtualTreeM_run {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (collCall : (i : Primitives.Member) → Adrs → pr.MemberMsg i → OracleComp spec pr.Y)
    (pk : pr.PkSeed) (Inv : σ → Prop) (step : σ → Adrs → σ)
    (hcall : ∀ i a msg s, Scheme.IsStateless a → Inv s →
      (simulateQ impl (collCall i a msg)).run s = pure (pr.memberEval i pk a msg, step s a))
    (hinv : ∀ s a, Inv s → Scheme.IsStateless a → Inv (step s a))
    (u : SlSecAdrs vp → pr.Y) (s : σ) (hs : Inv s) :
    ∃ s', Inv s' ∧
      (simulateQ impl (slVirtualTreeM pr collCall u)).run s =
        pure (slVirtualTreeDet pr pk u, s') := by
  have hnode : ∀ tbl a s, Inv s →
      ∃ s', Inv s' ∧ (simulateQ impl (evalNodeM pr collCall u tbl a)).run s =
        pure (evalNodeDet pr pk u tbl a, s') := by
    intro tbl a s hs
    rcases a with ⟨l, tr, ty, w1, w2, w3⟩
    rcases ty with _ | _ | _ | _ | _ | ty'
    · have hsl : Scheme.IsStateless ⟨l, tr, 0, w1, w2, w3⟩ := ⟨.wotsHash, rfl⟩
      simp only [evalNodeM, evalNodeDet, Id.run]
      split_ifs <;> exact ⟨_, hinv s _ hs hsl, hcall _ _ _ s hsl hs⟩
    · have hsl : Scheme.IsStateless ⟨l, tr, 1, w1, w2, w3⟩ := ⟨.wotsPk, rfl⟩
      simp only [evalNodeM, evalNodeDet, Id.run]
      exact ⟨_, hinv s _ hs hsl, hcall _ _ _ s hsl hs⟩
    · have hsl : Scheme.IsStateless ⟨l, tr, 2, w1, w2, w3⟩ := ⟨.tree, rfl⟩
      simp only [evalNodeM, evalNodeDet, Id.run]
      split_ifs
      · exact ⟨s, hs, by simp; rfl⟩
      · exact ⟨_, hinv s _ hs hsl, hcall _ _ _ s hsl hs⟩
      · exact ⟨_, hinv s _ hs hsl, hcall _ _ _ s hsl hs⟩
    · have hsl : Scheme.IsStateless ⟨l, tr, 3, w1, w2, w3⟩ := ⟨.forsTree, rfl⟩
      simp only [evalNodeM, evalNodeDet, Id.run]
      split_ifs <;> exact ⟨_, hinv s _ hs hsl, hcall _ _ _ s hsl hs⟩
    · have hsl : Scheme.IsStateless ⟨l, tr, 4, w1, w2, w3⟩ := ⟨.forsRoots, rfl⟩
      simp only [evalNodeM, evalNodeDet, Id.run]
      exact ⟨_, hinv s _ hs hsl, hcall _ _ _ s hsl hs⟩
    · simp only [evalNodeM, evalNodeDet, Id.run]
      exact ⟨s, hs, by simp; rfl⟩
  have hlist : ∀ (l : List Adrs) (tbl : Adrs → Option pr.Y) (s : σ), Inv s →
      ∃ s', Inv s' ∧
        (simulateQ impl (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr collCall u tbl a
          return Function.update tbl a (some v)) tbl)).run s =
        pure (Id.run (l.foldlM (fun tbl a => do
          let v ← evalNodeM pr (fun i a msg => (pr.memberEval i pk a msg : Id pr.Y)) u tbl a
          return Function.update tbl a (some v)) tbl), s') := by
    intro l
    induction l with
    | nil => intro tbl s hs; exact ⟨s, hs, by simp⟩
    | cons a as ih =>
      intro tbl s hs
      obtain ⟨s₁, hs₁, h1⟩ := hnode tbl a s hs
      obtain ⟨s₂, hs₂, h2⟩ := ih (Function.update tbl a (some (evalNodeDet pr pk u tbl a))) s₁ hs₁
      refine ⟨s₂, hs₂, ?_⟩
      simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, h1, pure_bind,
        simulateQ_pure, StateT.run_pure]
      exact h2
  obtain ⟨s', hs', hrun⟩ := hlist (slTreeAddresses vp) (fun _ => none) s hs
  refine ⟨s', hs', ?_⟩
  unfold slVirtualTreeM slVirtualTreeDet
  simp only [simulateQ_bind, StateT.run_bind, hrun, pure_bind, simulateQ_pure, StateT.run_pure]
  rfl

/-- In Claim 4.9's `shrincsX`, every `Ω`-partner of a stateful address is stateful. -/
theorem isStateful_of_mem_shrincsX_Omega {a b : Adrs} (ha : Scheme.IsStateful a)
    (hb : b ∈ Fxmss.Rom.shrincsX.Omega a) : Scheme.IsStateful b := by
  rcases hb with rfl | rfl
  · exact ha
  · unfold Fxmss.Rom.shrincsX Fxmss.Rom.shrincsPartner
    dsimp only
    split_ifs
    · exact ⟨.wotsCPk, rfl⟩
    · exact ⟨.fxmssTree, rfl⟩
    · exact ha

/-- Collection-oracle callback for `SM_DT_TCR` problems whose collection is `cons th pr.collection`. -/
def tcrCollCall {M : Type} (th : TweakableHash pr.PkSeed Adrs M pr.Y) (p : ℕ)
    (i : Primitives.Member) (a : Adrs) (msg : pr.MemberMsg i) :
    OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)) pr.Y := do
  let r ← (liftM ((Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)).query
    (.inr (.inr ⟨some i, a, msg⟩))) :
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)) (Option pr.Y))
  return r.getD default

/-- Collection-oracle callback for `S-TCR(Prop)` problems whose collection is `cons th pr.collection`. -/
def stcrCollCall {M : Type} (th : TweakableHash pr.PkSeed Adrs (M × ℕ) pr.Y) (prop : pr.Y → Bool)
    (p : ℕ) (i : Primitives.Member) (a : Adrs) (msg : pr.MemberMsg i) :
    OracleComp (Fxmss.STcrOracleSpec (Notions.sTcrMemberProblem th prop pr.collection p)) pr.Y := do
  let r ← (liftM ((Fxmss.STcrOracleSpec (Notions.sTcrMemberProblem th prop pr.collection p)).query
    (.inr (.inr ⟨some i, a, msg⟩))) :
      OracleComp (Fxmss.STcrOracleSpec (Notions.sTcrMemberProblem th prop pr.collection p))
        (Option pr.Y))
  return r.getD default

/-- Collection-oracle callback for `SM_DT_UD` and `SM_DT_PRE` (`FSpec`). -/
def hybCollCall [SampleableType pr.PkSeed] (i : Primitives.Member) (a : Adrs)
    (msg : pr.MemberMsg i) :
    OracleComp (Fxmss.Rom.Hyb.FSpec pr) pr.Y := do
  let r ← (liftM ((Fxmss.Rom.Hyb.FSpec pr).query (.inr (.inr ⟨some i, a, msg⟩))) :
    OracleComp (Fxmss.Rom.Hyb.FSpec pr) (Option pr.Y))
  return r.getD default

/-- Collection-oracle callback for `sm-tcr-excl` (`probExcl`). -/
def exclCollCall [SampleableType pr.PkSeed] (p : ℕ) (i : Primitives.Member) (a : Adrs)
    (msg : pr.MemberMsg i) :
    OracleComp (Fxmss.ExclOracleSpec (Fxmss.Rom.probExcl pr p)) pr.Y := do
  let r ← (liftM ((Fxmss.ExclOracleSpec (Fxmss.Rom.probExcl pr p)).query
    (.inr (.inr ⟨i, a, msg⟩))) :
      OracleComp (Fxmss.ExclOracleSpec (Fxmss.Rom.probExcl pr p)) (Option pr.Y))
  return r.getD default

/-- Execution of `slVirtualTreeM` against `SM_DT_TCR_oracles` from any stateful challenge log:
no query is refused (by `not_isStateful_of_isStateless`) and the challenge log `qs` is unchanged. -/
theorem simulateQ_slVirtualTreeM_tcr {M : Type} (th : TweakableHash pr.PkSeed Adrs M pr.Y)
    (p : ℕ) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (qs : List (Adrs × M)) (tws : List Adrs)
    (hqs : ∀ e ∈ qs, Scheme.IsStateful e.1) :
    ∃ tws',
      (simulateQ (SM_DT_TCR_oracles (Notions.smTcrMemberProblem th pr.collection p) pk)
        (slVirtualTreeM pr (tcrCollCall pr th p) u)).run (qs, tws) =
        pure (slVirtualTreeDet pr pk u, (qs, tws')) := by
  obtain ⟨⟨qs', tws'⟩, ⟨rfl, -⟩, hrun⟩ :=
    simulateQ_slVirtualTreeM_run pr
      (SM_DT_TCR_oracles (Notions.smTcrMemberProblem th pr.collection p) pk)
      (tcrCollCall pr th p) pk
      (fun s => s.1 = qs ∧ ∀ e ∈ s.1, Scheme.IsStateful e.1)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg ⟨qs₁, tws₁⟩ hsl ⟨heq, hsf⟩ => by
        rcases heq.symm with rfl
        have hnr : ¬ TweakReserved Prod.fst qs a := fun ⟨e, he, h⟩ =>
          not_isStateful_of_isStateless hsl (h ▸ hsf e he)
        unfold tcrCollCall
        simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_TCR_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          collectionOracle, StateT.run_get, pure_bind, hnr, ↓reduceIte, StateT.run_set,
          Option.getD_some]
        rfl)
      (fun s _ ⟨heq, hsf⟩ _ => ⟨heq, hsf⟩)
      u (qs, tws) ⟨rfl, hqs⟩
  exact ⟨tws', hrun⟩

/-- Execution of `slVirtualTreeM` against `STCR_oracles` from any stateful challenge log. -/
theorem simulateQ_slVirtualTreeM_stcr {M : Type} (th : TweakableHash pr.PkSeed Adrs (M × ℕ) pr.Y)
    (prop : pr.Y → Bool) (p : ℕ) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (qs : List ((Adrs × M) × (pr.Y × ℕ))) (tws : List Adrs)
    (hqs : ∀ e ∈ qs, Scheme.IsStateful e.1.1) :
    ∃ tws',
      (simulateQ (Notions.STCR_oracles (Notions.sTcrMemberProblem th prop pr.collection p) pk)
        (slVirtualTreeM pr (stcrCollCall pr th prop p) u)).run (qs, tws) =
        pure (slVirtualTreeDet pr pk u, (qs, tws')) := by
  obtain ⟨⟨qs', tws'⟩, ⟨rfl, -⟩, hrun⟩ :=
    simulateQ_slVirtualTreeM_run pr
      (Notions.STCR_oracles (Notions.sTcrMemberProblem th prop pr.collection p) pk)
      (stcrCollCall pr th prop p) pk
      (fun s => s.1 = qs ∧ ∀ e ∈ s.1, Scheme.IsStateful e.1.1)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg ⟨qs₁, tws₁⟩ hsl ⟨heq, hsf⟩ => by
        rcases heq.symm with rfl
        have hnr : ¬ TweakReserved (fun e : (Adrs × M) × (pr.Y × ℕ) => e.1.1) qs a :=
          fun ⟨e, he, h⟩ => not_isStateful_of_isStateless hsl (h ▸ hsf e he)
        unfold stcrCollCall
        simp only [simulateQ_bind, simulateQ_spec_query, Notions.STCR_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          collectionOracle, StateT.run_get, pure_bind, hnr, ↓reduceIte, StateT.run_set,
          Option.getD_some]
        rfl)
      (fun s _ ⟨heq, hsf⟩ _ => ⟨heq, hsf⟩)
      u (qs, tws) ⟨rfl, hqs⟩
  exact ⟨tws', hrun⟩

/-- Execution of `slVirtualTreeM` against `SM_DT_UD_oracles` from any stateful challenge log. -/
theorem simulateQ_slVirtualTreeM_ud [SampleableType pr.PkSeed] [SampleableType pr.Y]
    (w : SM_DT_UD_World) (p : ℕ) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (qs : List Adrs) (tws : List Adrs) (hqs : ∀ t ∈ qs, Scheme.IsStateful t) :
    ∃ tws',
      (simulateQ (SM_DT_UD_oracles w (Fxmss.Rom.probUD pr p) pk)
        (slVirtualTreeM pr (hybCollCall pr) u)).run (qs, tws) =
        pure (slVirtualTreeDet pr pk u, (qs, tws')) := by
  obtain ⟨⟨qs', tws'⟩, ⟨rfl, -⟩, hrun⟩ :=
    simulateQ_slVirtualTreeM_run pr
      (SM_DT_UD_oracles w (Fxmss.Rom.probUD pr p) pk)
      (hybCollCall pr) pk
      (fun s => s.1 = qs ∧ ∀ t ∈ s.1, Scheme.IsStateful t)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg ⟨qs₁, tws₁⟩ hsl ⟨heq, hsf⟩ => by
        rcases heq.symm with rfl
        have hnr : ¬ TweakReserved id qs a := fun ⟨t, ht, h⟩ =>
          not_isStateful_of_isStateless hsl (h ▸ hsf t ht)
        unfold hybCollCall
        simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_UD_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          collectionOracle, StateT.run_get, pure_bind, hnr, ↓reduceIte, StateT.run_set,
          Option.getD_some]
        rfl)
      (fun s _ ⟨heq, hsf⟩ _ => ⟨heq, hsf⟩)
      u (qs, tws) ⟨rfl, hqs⟩
  exact ⟨tws', hrun⟩

/-- Execution of `slVirtualTreeM` against `SM_DT_PRE_oracles` from any stateful challenge log. -/
theorem simulateQ_slVirtualTreeM_pre [SampleableType pr.PkSeed] [SampleableType pr.Y]
    (p : ℕ) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (qs : List (Adrs × pr.Y)) (tws : List Adrs) (hqs : ∀ e ∈ qs, Scheme.IsStateful e.1) :
    ∃ tws',
      (simulateQ (SM_DT_PRE_oracles (Fxmss.Rom.probPre pr p) pk)
        (slVirtualTreeM pr (hybCollCall pr) u)).run (qs, tws) =
        pure (slVirtualTreeDet pr pk u, (qs, tws')) := by
  obtain ⟨⟨qs', tws'⟩, ⟨rfl, -⟩, hrun⟩ :=
    simulateQ_slVirtualTreeM_run pr
      (SM_DT_PRE_oracles (Fxmss.Rom.probPre pr p) pk)
      (hybCollCall pr) pk
      (fun s => s.1 = qs ∧ ∀ e ∈ s.1, Scheme.IsStateful e.1)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg ⟨qs₁, tws₁⟩ hsl ⟨heq, hsf⟩ => by
        rcases heq.symm with rfl
        have hnr : ¬ TweakReserved Prod.fst qs a := fun ⟨e, he, h⟩ =>
          not_isStateful_of_isStateless hsl (h ▸ hsf e he)
        unfold hybCollCall
        simp only [simulateQ_bind, simulateQ_spec_query, SM_DT_PRE_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          collectionOracle, StateT.run_get, pure_bind, hnr, ↓reduceIte, StateT.run_set,
          Option.getD_some]
        rfl)
      (fun s _ ⟨heq, hsf⟩ _ => ⟨heq, hsf⟩)
      u (qs, tws) ⟨rfl, hqs⟩
  exact ⟨tws', hrun⟩

/-- Execution of `slVirtualTreeM` against `SMTCRExcl_oracles` from any stateful challenge log:
every `Ω`-partner of a stateful challenge tweak is stateful, so no stateless collection query is
refused and the challenge log `qs` is unchanged. -/
theorem simulateQ_slVirtualTreeM_excl [SampleableType pr.PkSeed]
    (p : ℕ) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (qs : List (Adrs × Fxmss.Rom.Msg9 pr)) (tws : List Adrs)
    (hqs : ∀ e ∈ qs, Scheme.IsStateful e.1) :
    ∃ tws',
      (simulateQ (Notions.SMTCRExcl_oracles (Fxmss.Rom.probExcl pr p) pk)
        (slVirtualTreeM pr (exclCollCall pr p) u)).run (qs, tws) =
        pure (slVirtualTreeDet pr pk u, (qs, tws')) := by
  obtain ⟨⟨qs', tws'⟩, ⟨rfl, -⟩, hrun⟩ :=
    simulateQ_slVirtualTreeM_run pr
      (Notions.SMTCRExcl_oracles (Fxmss.Rom.probExcl pr p) pk)
      (exclCollCall pr p) pk
      (fun s => s.1 = qs ∧ ∀ e ∈ s.1, Scheme.IsStateful e.1)
      (fun s a => (s.1, s.2 ++ [a]))
      (fun i a msg ⟨qs₁, tws₁⟩ hsl ⟨heq, hsf⟩ => by
        rcases heq.symm with rfl
        have hnr : ¬ ∃ e ∈ qs, a ∈ Fxmss.Rom.shrincsX.Omega e.1 := fun ⟨e, he, hm⟩ =>
          not_isStateful_of_isStateless hsl (isStateful_of_mem_shrincsX_Omega (hsf e he) hm)
        unfold exclCollCall
        simp only [simulateQ_bind, simulateQ_spec_query, Notions.SMTCRExcl_oracles,
          QueryImpl.add_apply_inr, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          Notions.SMTCRExcl_collectionOracle, Notions.ExclReserved, StateT.run_get, pure_bind,
          hnr, ↓reduceIte, StateT.run_set, Option.getD_some]
        rfl)
      (fun s _ ⟨heq, hsf⟩ _ => ⟨heq, hsf⟩)
      u (qs, tws) ⟨rfl, hqs⟩
  exact ⟨tws', hrun⟩

end Precompute

/-! ## 5. Stage-2 zero-`Th_λ` table signer and exact equivalence with `pubQ` -/

section TableSigner

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- **Zero-`Th_λ` Stage-2 public-hash handler**: answers every `.thash` query by looking up the
Stage-1 precomputed table `tbl` (making zero calls to `Th`, `F`, `H`, `Th_k`, `Th_lsl`, `Th_lsf`,
`H_grind`), and evaluates only `H_msg^sl`. -/
@[instance_reducible] def tablePubQ (tbl : Adrs → Option pr.Y) (m : Type → Type) [Monad m] :
    HasQuery (SLHDSA.publicHashSpec pr.toSLHDSA.core) m :=
  ⟨fun
    | .thash _ a _ => pure ((tbl a).getD default)
    | .hmsg R pk pkRoot msg => pure (pr.HmsgSl R pk pkRoot msg)⟩

/-- Deterministic stateless root computation (`pubQ`) from eager secrets `u`. -/
def slRootDet (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) : pr.Y :=
  Id.run <|
    letI := pubQ pr Id
    SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
      (fun a => pure (slSecOf pr u a)) pk

/-- Deterministic stateless signing (`pubQ`) from eager secrets `u`. -/
def slSignDet (pk : pr.PkSeed) (pkSl : pr.Y) (u : SlSecAdrs vp → pr.Y) (msg : List Byte)
    (R : pr.Y) : Stateless.Sig pr :=
  Id.run <|
    letI := pubQ pr Id
    SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
      (fun a => pure (slSecOf pr u a)) msg pk pkSl R

/-- **Zero-`Th_λ` Stage-2 stateless signing**: answers every `.thash` query from the precomputed
table `tbl` via `tablePubQ`, evaluating only `H_msg^sl`. -/
def slSignTable (tbl : Adrs → Option pr.Y) (pk : pr.PkSeed) (pkSl : pr.Y)
    (u : SlSecAdrs vp → pr.Y) (msg : List Byte) (R : pr.Y) : Stateless.Sig pr :=
  Id.run <|
    letI := tablePubQ pr tbl Id
    SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
      (fun a => pure (slSecOf pr u a)) msg pk pkSl R

private theorem idRun_vector_ofFnM {n : ℕ} {α : Type} (f : Fin n → Id α) :
    Id.run (Vector.ofFnM f) = Vector.ofFn (fun i => Id.run (f i)) := by
  induction n with
  | zero =>
    rw [Vector.ofFnM_zero]
    apply Vector.ext; intro i hi; omega
  | succ n ih =>
    rw [Vector.ofFnM_succ]
    apply Vector.ext; intro i hi
    change ((Id.run (Vector.ofFnM (fun j : Fin n => f j.castSucc))).push (Id.run (f (Fin.last n))))[i] = _
    rw [ih (fun j : Fin n => f j.castSucc)]
    by_cases hlt : i < n
    · simp [Vector.getElem_push_lt hlt]
    · have hin : i = n := by omega
      subst hin
      simp [Fin.last]

private abbrev fPub (pk : pr.PkSeed) : Adrs → pr.Y → Id pr.Y := fun a x => pure (pr.F pk a x)
private abbrev hPub (pk : pr.PkSeed) : Adrs → pr.Y → pr.Y → Id pr.Y := fun a l r => pure (pr.H pk a l r)
private abbrev tlPub (pk : pr.PkSeed) : Adrs → List pr.Y → Id pr.Y := fun a xs => pure (pr.Th pk a xs)
private abbrev fTbl (tbl : Adrs → Option pr.Y) (_pk : pr.PkSeed) : Adrs → pr.Y → Id pr.Y :=
  fun a _ => pure ((tbl a).getD default)
private abbrev hTbl' (tbl : Adrs → Option pr.Y) (_pk : pr.PkSeed) : Adrs → pr.Y → pr.Y → Id pr.Y :=
  fun a _ _ => pure ((tbl a).getD default)
private abbrev tlTbl (tbl : Adrs → Option pr.Y) (_pk : pr.PkSeed) : Adrs → List pr.Y → Id pr.Y :=
  fun a _ => pure ((tbl a).getD default)

private def chainVal (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) (pos : LayerPosition vp.sl)
    (c : Fin vp.sl.params.len) : ℕ → pr.Y
  | 0 => slSecOf pr u (wotsSkAdrs (wotsInstanceAdrs pos) c.val)
  | k + 1 => honestVal pr pk u ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress k)

private theorem chainWith_pubQ_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (start : ℕ) :
    ∀ steps,
      Id.run (chainWith (fPub pr pk)
        (wotsChainAdrs (wotsInstanceAdrs pos) c.val) (chainVal pr pk u pos c start) start steps) =
      chainVal pr pk u pos c (start + steps)
  | 0 => rfl
  | steps + 1 => by
    have ih := chainWith_pubQ_eq pk u pos c start steps
    change pr.F pk ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (start + steps))
      (Id.run (chainWith (fPub pr pk)
        (wotsChainAdrs (wotsInstanceAdrs pos) c.val) (chainVal pr pk u pos c start) start steps)) =
      chainVal pr pk u pos c (start + steps + 1)
    rw [ih]
    rcases hk : start + steps with _ | k
    · exact (honestVal_wotsStep_zero pr pk u (wotsInstanceAdrs pos) c.val).symm
    · exact (honestVal_wotsStep_succ pr pk u (wotsInstanceAdrs pos) c.val k).symm

private theorem chainWith_tablePubQ_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len) (start : ℕ) :
    ∀ steps, start + steps ≤ vp.sl.params.w - 1 →
      Id.run (chainWith (fTbl pr tbl pk)
        (wotsChainAdrs (wotsInstanceAdrs pos) c.val) (chainVal pr pk u pos c start) start steps) =
      chainVal pr pk u pos c (start + steps)
  | 0, _ => rfl
  | steps + 1, hle => by
    change (tbl ((wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress
      (start + steps))).getD default = chainVal pr pk u pos c (start + steps + 1)
    have hmem : (wotsChainAdrs (wotsInstanceAdrs pos) c.val).setHashAddress (start + steps) ∈
        constructionAddresses vp.sl :=
      wotsChainAdrs_setHashAddress_mem_constructionAddresses pos c (by omega)
    rw [hTbl _ hmem, Option.getD_some]
    rfl

private theorem wotsPkGen_pubQ_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    (pos : LayerPosition vp.sl) :
    Id.run (wotsPkGenWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
      (fun a => pure (slSecOf pr u a)) (wotsInstanceAdrs pos)) =
    honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) := by
  have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
  rw [honestVal_wotsPk]
  have htops : (Id.run (wotsPkGenTopsWithSecret pr.toSLHDSA.core (fPub pr pk)
        (fun a => pure (slSecOf pr u a)) (wotsInstanceAdrs pos))).toList =
      (Vector.ofFn fun i : Fin vp.params.lsl =>
        honestVal pr pk u ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress
          (vp.params.w - 2))).toList := by
    apply List.ext_getElem
    · simp [Params.lsl_eq_len vp.valid]
    · intro i hi₁ hi₂
      simp only [Vector.getElem_toList, Vector.getElem_ofFn]
      have hi' : i < vp.sl.params.len := by simpa using hi₁
      have hch := chainWith_pubQ_eq pr pk u pos ⟨i, hi'⟩ 0 (vp.sl.params.w - 1)
      have hidx : 0 + (vp.sl.params.w - 1) = (vp.params.w - 2) + 1 := by
        simp only [Nat.zero_add]; change vp.params.w - 1 = vp.params.w - 2 + 1; omega
      rw [hidx] at hch
      change (Id.run (Vector.ofFnM fun c : Fin vp.sl.params.len =>
        chainWith (fPub pr pk) (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
          (chainVal pr pk u pos c 0) 0 (vp.sl.params.w - 1)))[i] = _
      rw [idRun_vector_ofFnM, Vector.getElem_ofFn]
      exact hch
  change pr.Th pk (wotsPkAdrs (wotsInstanceAdrs pos))
      (Id.run (wotsPkGenTopsWithSecret pr.toSLHDSA.core (fPub pr pk)
        (fun a => pure (slSecOf pr u a)) (wotsInstanceAdrs pos))).toList =
    pr.Th pk (wotsPkAdrs (wotsInstanceAdrs pos)) _
  rw [htops]

private theorem wotsPkGen_tablePubQ_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl) (pos : LayerPosition vp.sl) :
    Id.run (wotsPkGenWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
      (fun a => pure (slSecOf pr u a)) (wotsInstanceAdrs pos)) =
    honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) := by
  change (tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default = _
  rw [hTbl _ (wotsPkAdrs_mem_constructionAddresses pos), Option.getD_some]

private theorem wotsSign_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (msg : pr.Y) (pos : LayerPosition vp.sl) :
    Id.run (wotsSignWithSecret pr.toSLHDSA.core (fPub pr pk)
        (fun a => pure (slSecOf pr u a)) msg (wotsInstanceAdrs pos)) =
      Vector.ofFn (fun c : Fin vp.sl.params.len =>
        chainVal pr pk u pos c (chainStepsCore pr.toSLHDSA.core msg c.val)) ∧
    Id.run (wotsSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
        (fun a => pure (slSecOf pr u a)) msg (wotsInstanceAdrs pos)) =
      Vector.ofFn (fun c : Fin vp.sl.params.len =>
        chainVal pr pk u pos c (chainStepsCore pr.toSLHDSA.core msg c.val)) := by
  constructor
  · apply Vector.ext; intro i hi
    change (Id.run (Vector.ofFnM fun c : Fin vp.sl.params.len =>
      chainWith (fPub pr pk) (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
        (chainVal pr pk u pos c 0) 0 (chainStepsCore pr.toSLHDSA.core msg c.val)))[i] = _
    rw [idRun_vector_ofFnM, Vector.getElem_ofFn, Vector.getElem_ofFn]
    simpa using chainWith_pubQ_eq pr pk u pos ⟨i, hi⟩ 0 (chainStepsCore pr.toSLHDSA.core msg i)
  · apply Vector.ext; intro i hi
    change (Id.run (Vector.ofFnM fun c : Fin vp.sl.params.len =>
      chainWith (fTbl pr tbl pk) (wotsChainAdrs (wotsInstanceAdrs pos) c.val)
        (chainVal pr pk u pos c 0) 0 (chainStepsCore pr.toSLHDSA.core msg c.val)))[i] = _
    rw [idRun_vector_ofFnM, Vector.getElem_ofFn, Vector.getElem_ofFn]
    simpa using chainWith_tablePubQ_eq pr pk u hTbl pos ⟨i, hi⟩ 0
      (chainStepsCore pr.toSLHDSA.core msg i)
      (by simpa using chainStepsCore_le pr.toSLHDSA.core msg i)

private theorem wotsPkFromSig_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (msg : pr.Y) (pos : LayerPosition vp.sl) :
    let sig : WotsSig vp.sl.params pr.toSLHDSA.core :=
      Vector.ofFn fun c : Fin vp.sl.params.len =>
        chainVal pr pk u pos c (chainStepsCore pr.toSLHDSA.core msg c.val)
    Id.run (wotsPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
        sig msg (wotsInstanceAdrs pos)) =
      honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) ∧
    Id.run (wotsPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        sig msg (wotsInstanceAdrs pos)) =
      honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) := by
  have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
  dsimp only
  constructor
  · rw [honestVal_wotsPk]
    have htops : (Id.run (Vector.ofFnM fun i : Fin vp.sl.params.len =>
          chainWith (fPub pr pk) (wotsChainAdrs (wotsInstanceAdrs pos) i.val)
            ((Vector.ofFn fun c : Fin vp.sl.params.len =>
              chainVal pr pk u pos c (chainStepsCore pr.toSLHDSA.core msg c.val))[i.val])
            (chainStepsCore pr.toSLHDSA.core msg i.val)
            (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core msg i.val))).toList =
        (Vector.ofFn fun i : Fin vp.params.lsl =>
          honestVal pr pk u ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress
            (vp.params.w - 2))).toList := by
      apply List.ext_getElem
      · simp [Params.lsl_eq_len vp.valid]
      · intro i hi₁ hi₂
        simp only [idRun_vector_ofFnM, Vector.getElem_toList, Vector.getElem_ofFn]
        have hi' : i < vp.sl.params.len := by simpa using hi₁
        have hle := chainStepsCore_le pr.toSLHDSA.core msg i
        have hch := chainWith_pubQ_eq pr pk u pos ⟨i, hi'⟩
          (chainStepsCore pr.toSLHDSA.core msg i)
          (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core msg i)
        have hsum : chainStepsCore pr.toSLHDSA.core msg i +
            (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core msg i) =
            (vp.params.w - 2) + 1 := by
          have hw' : vp.sl.params.w = vp.params.w := rfl; rw [hw'] at hle ⊢; omega
        rw [hsum] at hch
        exact hch
    change pr.Th pk (wotsPkAdrs (wotsInstanceAdrs pos))
      (Id.run (Vector.ofFnM fun i : Fin vp.sl.params.len =>
        chainWith (fPub pr pk) (wotsChainAdrs (wotsInstanceAdrs pos) i.val)
          ((Vector.ofFn fun c : Fin vp.sl.params.len =>
            chainVal pr pk u pos c (chainStepsCore pr.toSLHDSA.core msg c.val))[i.val])
          (chainStepsCore pr.toSLHDSA.core msg i.val)
          (vp.sl.params.w - 1 - chainStepsCore pr.toSLHDSA.core msg i.val))).toList =
      pr.Th pk (wotsPkAdrs (wotsInstanceAdrs pos)) _
    rw [htops]
  · change (tbl (wotsPkAdrs (wotsInstanceAdrs pos))).getD default = _
    rw [hTbl _ (wotsPkAdrs_mem_constructionAddresses pos), Option.getD_some]

omit [Inhabited pr.Y] in
private theorem merkleRoot_eq_val {H : ℕ} (val : ℕ → ℕ → pr.Y)
    (leaf : ℕ → pr.Y) (node : ℕ → ℕ → pr.Y → pr.Y → pr.Y)
    (hl : ∀ i < 2 ^ H, leaf i = val 0 i)
    (hn : ∀ z t, z < H → t < 2 ^ (H - (z + 1)) →
      node (z + 1) t (val z (2 * t)) (val z (2 * t + 1)) = val (z + 1) t) :
    ∀ z t, z ≤ H → t < 2 ^ (H - z) →
      PerfectMerkleTree.merkleRoot leaf node z t = val z t
  | 0, t, _, ht => hl t (by simpa using ht)
  | z + 1, t, hz, ht => by
    have hsub : H - z = H - (z + 1) + 1 := by omega
    have ht0 : 2 * t < 2 ^ (H - z) := by rw [hsub, pow_succ]; omega
    have ht1 : 2 * t + 1 < 2 ^ (H - z) := by rw [hsub, pow_succ]; omega
    rw [PerfectMerkleTree.merkleRoot_succ,
      merkleRoot_eq_val val leaf node hl hn z (2 * t) (by omega) ht0,
      merkleRoot_eq_val val leaf node hl hn z (2 * t + 1) (by omega) ht1]
    exact hn z t (by omega) ht

omit [Inhabited pr.Y] in
private theorem intrinsicAuthPath_eq_of_val {H : ℕ} (val : ℕ → ℕ → pr.Y)
    (leaf₁ leaf₂ : ℕ → pr.Y) (node₁ node₂ : ℕ → ℕ → pr.Y → pr.Y → pr.Y)
    (h₁ : ∀ z t, z ≤ H → t < 2 ^ (H - z) →
      PerfectMerkleTree.merkleRoot leaf₁ node₁ z t = val z t)
    (h₂ : ∀ z t, z ≤ H → t < 2 ^ (H - z) →
      PerfectMerkleTree.merkleRoot leaf₂ node₂ z t = val z t)
    {idx : ℕ} (hidx : idx < 2 ^ H) :
    ∀ z, z ≤ H →
      PerfectMerkleTree.intrinsicAuthPath leaf₁ node₁ idx z =
        PerfectMerkleTree.intrinsicAuthPath leaf₂ node₂ idx z
  | 0, _ => rfl
  | z + 1, hz => by
    simp only [PerfectMerkleTree.intrinsicAuthPath]
    have hsib : PerfectMerkleTree.sibling (idx / 2 ^ z) < 2 ^ (H - z) := by
      have hq : idx / 2 ^ z < 2 ^ (H - z) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
        exact hidx
      unfold PerfectMerkleTree.sibling
      split_ifs with hev
      · obtain ⟨k, hk⟩ := dvd_pow_self 2 (by omega : H - z ≠ 0)
        omega
      · exact (Nat.sub_le _ _).trans_lt hq
    rw [intrinsicAuthPath_eq_of_val val leaf₁ leaf₂ node₁ node₂ h₁ h₂ hidx z (by omega),
      h₁ z _ (by omega) hsib, h₂ z _ (by omega) hsib]

private theorem xmssNode_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (coord : LayerTreeCoord vp.sl) {z t : ℕ} (hz : z ≤ vp.sl.params.hp)
    (ht : t < 2 ^ (vp.sl.params.hp - z)) :
    Id.run (xmssNodeWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk) (hPub pr pk)
        (fun a => pure (slSecOf pr u a)) coord.toAdrs z t) =
      honestVal pr pk u (xmssCellAdrs coord.toAdrs z t) ∧
    Id.run (xmssNodeWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a)) coord.toAdrs z t) =
      honestVal pr pk u (xmssCellAdrs coord.toAdrs z t) := by
  constructor
  · rw [xmssNodeWithSecret, PerfectMerkleTree.idRun_merkleRootM]
    exact merkleRoot_eq_val pr (fun z t => honestVal pr pk u (xmssCellAdrs coord.toAdrs z t))
      _ _
      (fun i hi => wotsPkGen_pubQ_eq pr pk u ⟨coord.layer, coord.tree, ⟨i, hi⟩⟩)
      (fun z t _ _ => (honestVal_xmssCell_succ pr pk u coord.toAdrs z t).symm)
      z t hz ht
  · rw [xmssNodeWithSecret, PerfectMerkleTree.idRun_merkleRootM]
    exact merkleRoot_eq_val pr (fun z t => honestVal pr pk u (xmssCellAdrs coord.toAdrs z t))
      _ _
      (fun i hi => wotsPkGen_tablePubQ_eq pr pk u hTbl ⟨coord.layer, coord.tree, ⟨i, hi⟩⟩)
      (fun z t hz' ht' => by
        change (tbl (xmssNodeAdrs coord.toAdrs (z + 1) t)).getD default = _
        have hmem := xmssNodeAdrs_mem_constructionAddresses coord (Nat.succ_pos z) (by omega) ht'
        rw [hTbl _ hmem, Option.getD_some]; rfl)
      z t hz ht

/-- `PK.sl` computed deterministically from eager secrets `u` equals `honestVal` at `topRootAdrs`
(hence equals `(slVirtualTreeDet pr pk u).1`, computed in Stage 1 via `O_coll`). -/
theorem slRootDet_eq_honestVal (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    slRootDet pr pk u = honestVal pr pk u (topRootAdrs vp) := by
  have h := (xmssNode_eq pr pk u (slVirtualTreeDet_spec pr pk u).2.2 (LayerTreeCoord.top vp.sl)
    (z := vp.sl.params.hp) (t := 0) le_rfl (by positivity)).1
  have hcell : xmssCellAdrs (LayerTreeCoord.top vp.sl).toAdrs vp.sl.params.hp 0 = topRootAdrs vp := by
    have hpos : 0 < vp.params.hp := vp.valid.hp_pos
    change xmssCellAdrs (LayerTreeCoord.top vp.sl).toAdrs vp.params.hp 0 = topRootAdrs vp
    rcases hp : vp.params.hp with _ | hp'
    · omega
    · simp [xmssCellAdrs, topRootAdrs, hp]
  rw [hcell, LayerTreeCoord.top_toAdrs_layerAdrs] at h
  exact h

private theorem idRun_intrinsicAuthPathM {Y : Type} (leaf : ℕ → Id Y)
    (nodeHash : ℕ → ℕ → Y → Y → Id Y) (idx : ℕ) :
    ∀ z, Id.run (PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z) =
      PerfectMerkleTree.intrinsicAuthPath (fun i => Id.run (leaf i))
        (fun h i l r => Id.run (nodeHash h i l r)) idx z
  | 0 => rfl
  | z + 1 => by
    simp only [PerfectMerkleTree.intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath]
    change (Id.run (PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z)).push
      (Id.run (PerfectMerkleTree.merkleRootM leaf nodeHash z _)) = _
    rw [idRun_intrinsicAuthPathM leaf nodeHash idx z, PerfectMerkleTree.idRun_merkleRootM]

private theorem xmssSign_and_pkFromSig_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (msg : pr.Y) (pos : LayerPosition vp.sl) :
    let sigPub := Id.run (xmssSignWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
      (hPub pr pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val)
    let sigTbl := Id.run (xmssSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
      (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val)
    sigTbl = sigPub ∧
      Id.run (xmssPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        (hTbl' pr tbl pk) pos.leaf.val sigTbl msg pos.toAdrs) =
      Id.run (xmssPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
        (hPub pr pk) pos.leaf.val sigPub msg pos.toAdrs) := by
  let coord := LayerTreeCoord.ofPosition pos
  have hpath : Id.run (PerfectMerkleTree.intrinsicAuthPathM
        (xmssLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
          (fun a => pure (slSecOf pr u a)) pos.toAdrs)
        (xmssNodeHashWith (hTbl' pr tbl pk) pos.toAdrs)
        pos.leaf.val vp.sl.params.hp) =
      Id.run (PerfectMerkleTree.intrinsicAuthPathM
        (xmssLeafWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
          (fun a => pure (slSecOf pr u a)) pos.toAdrs)
        (xmssNodeHashWith (hPub pr pk) pos.toAdrs)
        pos.leaf.val vp.sl.params.hp) := by
    rw [idRun_intrinsicAuthPathM, idRun_intrinsicAuthPathM]
    exact intrinsicAuthPath_eq_of_val pr
      (fun z t => honestVal pr pk u (xmssCellAdrs coord.toAdrs z t)) _ _ _ _
      (fun z t hz ht => by
        rw [← PerfectMerkleTree.idRun_merkleRootM, ← LayerTreeCoord.ofPosition_toAdrs pos]
        exact (xmssNode_eq pr pk u hTbl coord hz ht).2)
      (fun z t hz ht => by
        rw [← PerfectMerkleTree.idRun_merkleRootM, ← LayerTreeCoord.ofPosition_toAdrs pos]
        exact (xmssNode_eq pr pk u hTbl coord hz ht).1)
      pos.leaf.isLt vp.sl.params.hp le_rfl
  have hwots := wotsSign_eq pr pk u hTbl msg pos
  have hsig : Id.run (xmssSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
      (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val) =
    Id.run (xmssSignWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
      (hPub pr pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val) := by
    show XmssSigCore.mk _ _ = XmssSigCore.mk _ _
    congr 1
    · exact hwots.2.trans hwots.1.symm
  refine ⟨hsig, ?_⟩
  have hleaf := wotsPkFromSig_eq pr pk u hTbl msg pos
  have hclimbTbl : Id.run (xmssPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
      (hTbl' pr tbl pk) pos.leaf.val
      (Id.run (xmssSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val))
      msg pos.toAdrs) =
      honestVal pr pk u (xmssCellAdrs coord.toAdrs vp.sl.params.hp 0) := by
    change Id.run (PerfectMerkleTree.climbM (xmssNodeHashWith (hTbl' pr tbl pk) pos.toAdrs)
      pos.leaf.val
      (Id.run (wotsPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        (Id.run (wotsSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
          (fun a => pure (slSecOf pr u a)) msg (wotsInstanceAdrs pos)))
        msg (wotsInstanceAdrs pos)))
      (Id.run (PerfectMerkleTree.intrinsicAuthPathM
        (xmssLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
          (fun a => pure (slSecOf pr u a)) pos.toAdrs)
        (xmssNodeHashWith (hTbl' pr tbl pk) pos.toAdrs)
        pos.leaf.val vp.sl.params.hp)).toList) = _
    rw [hwots.2, hleaf.2, idRun_intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath_toList,
      PerfectMerkleTree.idRun_climbM]
    have hleaf_eq : honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) =
        (fun i => Id.run (xmssLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
          (fun a => pure (slSecOf pr u a)) pos.toAdrs i)) pos.leaf.val :=
      (wotsPkGen_tablePubQ_eq pr pk u hTbl pos).symm
    rw [hleaf_eq, PerfectMerkleTree.climb_authPath
        (leaf := fun i => Id.run (xmssLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
          (tlTbl pr tbl pk) (fun a => pure (slSecOf pr u a)) pos.toAdrs i)),
      Nat.div_eq_of_lt pos.leaf.isLt, ← PerfectMerkleTree.idRun_merkleRootM,
      ← LayerTreeCoord.ofPosition_toAdrs pos]
    exact (xmssNode_eq pr pk u hTbl coord le_rfl (by positivity)).2
  have hclimbPub : Id.run (xmssPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
      (hPub pr pk) pos.leaf.val
      (Id.run (xmssSignWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
        (hPub pr pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val))
      msg pos.toAdrs) =
      honestVal pr pk u (xmssCellAdrs coord.toAdrs vp.sl.params.hp 0) := by
    change Id.run (PerfectMerkleTree.climbM (xmssNodeHashWith (hPub pr pk) pos.toAdrs)
      pos.leaf.val
      (Id.run (wotsPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
        (Id.run (wotsSignWithSecret pr.toSLHDSA.core (fPub pr pk)
          (fun a => pure (slSecOf pr u a)) msg (wotsInstanceAdrs pos)))
        msg (wotsInstanceAdrs pos)))
      (Id.run (PerfectMerkleTree.intrinsicAuthPathM
        (xmssLeafWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
          (fun a => pure (slSecOf pr u a)) pos.toAdrs)
        (xmssNodeHashWith (hPub pr pk) pos.toAdrs)
        pos.leaf.val vp.sl.params.hp)).toList) = _
    rw [hwots.1, hleaf.1, idRun_intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath_toList,
      PerfectMerkleTree.idRun_climbM]
    have hleaf_eq : honestVal pr pk u (wotsPkAdrs (wotsInstanceAdrs pos)) =
        (fun i => Id.run (xmssLeafWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
          (fun a => pure (slSecOf pr u a)) pos.toAdrs i)) pos.leaf.val :=
      (wotsPkGen_pubQ_eq pr pk u pos).symm
    rw [hleaf_eq, PerfectMerkleTree.climb_authPath
        (leaf := fun i => Id.run (xmssLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
          (tlPub pr pk) (fun a => pure (slSecOf pr u a)) pos.toAdrs i)),
      Nat.div_eq_of_lt pos.leaf.isLt, ← PerfectMerkleTree.idRun_merkleRootM,
      ← LayerTreeCoord.ofPosition_toAdrs pos]
    exact (xmssNode_eq pr pk u hTbl coord le_rfl (by positivity)).1
  exact hclimbTbl.trans hclimbPub.symm

private theorem forsNode_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (pos : BottomPosition vp.sl) (tree : Fin vp.sl.params.k) :
    ∀ z t, z ≤ vp.sl.params.a → t / 2 ^ (vp.sl.params.a - z) = tree.val →
      Id.run (PerfectMerkleTree.merkleRootM
          (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hPub pr pk) pos.forsAdrs) z t) =
        honestVal pr pk u (forsNodeAdrs pos.forsAdrs z t) ∧
      Id.run (PerfectMerkleTree.merkleRootM
          (forsLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hTbl' pr tbl pk) pos.forsAdrs) z t) =
        honestVal pr pk u (forsNodeAdrs pos.forsAdrs z t)
  | 0, t, _, ht => by
    have hmem := forsLeafAdrs_mem_constructionAddresses pos tree (by simpa using ht)
    constructor
    · exact (honestVal_forsLeaf pr pk u pos.forsAdrs t).symm
    · change (tbl (forsNodeAdrs pos.forsAdrs 0 t)).getD default = _
      rw [hTbl _ hmem, Option.getD_some]
  | z + 1, t, hz, ht => by
    have hsub : vp.sl.params.a - z = vp.sl.params.a - (z + 1) + 1 := by omega
    have hdiv0 : (2 * t) / 2 ^ (vp.sl.params.a - z) = tree.val := by
      rw [hsub, pow_succ, Nat.mul_comm _ 2, Nat.mul_div_mul_left _ _ (by omega)]; exact ht
    have hdiv1 : (2 * t + 1) / 2 ^ (vp.sl.params.a - z) = tree.val := by
      rw [hsub, pow_succ, Nat.mul_comm _ 2, ← Nat.div_div_eq_div_mul,
        show (2 * t + 1) / 2 = t by omega]; exact ht
    have ih0 := forsNode_eq pk u hTbl pos tree z (2 * t) (by omega) hdiv0
    have ih1 := forsNode_eq pk u hTbl pos tree z (2 * t + 1) (by omega) hdiv1
    constructor
    · change pr.H pk (forsNodeAdrs pos.forsAdrs (z + 1) t)
        (Id.run (PerfectMerkleTree.merkleRootM
          (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hPub pr pk) pos.forsAdrs) z (2 * t)))
        (Id.run (PerfectMerkleTree.merkleRootM
          (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hPub pr pk) pos.forsAdrs) z (2 * t + 1))) = _
      rw [ih0.1, ih1.1, ← honestVal_forsNode_succ]
    · change (tbl (forsNodeAdrs pos.forsAdrs (z + 1) t)).getD default = _
      have hmem := forsTreeAdrs_mem_constructionAddresses pos tree (Nat.succ_pos z) hz ht
      rw [hTbl _ hmem, Option.getD_some]

private theorem forsSign_and_pkFromSig_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl)
    (md : List Byte) (pos : BottomPosition vp.sl) :
    let sigPub := Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
      (fun a => pure (slSecOf pr u a)) md pos.forsAdrs)
    let sigTbl := Id.run (forsSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (hTbl' pr tbl pk)
      (fun a => pure (slSecOf pr u a)) md pos.forsAdrs)
    sigTbl = sigPub ∧
      Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (hTbl' pr tbl pk)
        (tlTbl pr tbl pk) sigTbl md pos.forsAdrs) =
      Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
        (tlPub pr pk) sigPub md pos.forsAdrs) := by
  have hpath : ∀ tree : Fin vp.sl.params.k,
      let idx := forsLeafIndex vp.sl.params md tree.val
      Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hTbl' pr tbl pk) pos.forsAdrs) idx vp.sl.params.a) =
      Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hPub pr pk) pos.forsAdrs) idx vp.sl.params.a) := by
    intro tree idx
    have hdiv := forsLeafIndex_div vp.sl.params md tree.val
    have rec_eq : ∀ z, z ≤ vp.sl.params.a →
        Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hTbl' pr tbl pk) pos.forsAdrs) idx z) =
        Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hPub pr pk) pos.forsAdrs) idx z) := by
      intro z hz
      induction z with
      | zero => rfl
      | succ z ih =>
        have hsib_div : PerfectMerkleTree.sibling (idx / 2 ^ z) / 2 ^ (vp.sl.params.a - z) =
            tree.val := by
          have h1 : idx / 2 ^ z / 2 ^ (vp.sl.params.a - z) = tree.val := by
            rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]; exact hdiv
          have hpos : 0 < vp.sl.params.a - z := by omega
          have h2 : 2 ^ (vp.sl.params.a - z) = 2 * 2 ^ (vp.sl.params.a - z - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hpos]
          rw [h2, ← Nat.div_div_eq_div_mul] at h1 ⊢
          rw [PerfectMerkleTree.sibling_div_two]; exact h1
        have hnode := forsNode_eq pr pk u hTbl pos tree z
          (PerfectMerkleTree.sibling (idx / 2 ^ z)) (by omega) hsib_div
        change (Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
          (forsNodeHashWith (hTbl' pr tbl pk) pos.forsAdrs) idx z)).push
          (Id.run (PerfectMerkleTree.merkleRootM
            (forsLeafWithSecret pr.toSLHDSA.core (fTbl pr tbl pk)
              (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
            (forsNodeHashWith (hTbl' pr tbl pk) pos.forsAdrs) z _)) =
          (Id.run (PerfectMerkleTree.intrinsicAuthPathM
            (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
              (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
            (forsNodeHashWith (hPub pr pk) pos.forsAdrs) idx z)).push
          (Id.run (PerfectMerkleTree.merkleRootM
            (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
              (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
            (forsNodeHashWith (hPub pr pk) pos.forsAdrs) z _))
        rw [ih (by omega), hnode.2, hnode.1]
    exact rec_eq vp.sl.params.a le_rfl
  have hsig : Id.run (forsSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (hTbl' pr tbl pk)
      (fun a => pure (slSecOf pr u a)) md pos.forsAdrs) =
    Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
      (fun a => pure (slSecOf pr u a)) md pos.forsAdrs) := by
    apply Vector.ext; intro i hi
    change (Id.run (Vector.ofFnM (n := vp.sl.params.k) _))[i] =
      (Id.run (Vector.ofFnM (n := vp.sl.params.k) _))[i]
    simp only [idRun_vector_ofFnM, Vector.getElem_ofFn]
    exact congrArg (ForsTreeSigCore.mk _) (hpath ⟨i, hi⟩)
  refine ⟨hsig, ?_⟩
  have hpkTbl : Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk)
      (hTbl' pr tbl pk) (tlTbl pr tbl pk)
      (Id.run (forsSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (hTbl' pr tbl pk)
        (fun a => pure (slSecOf pr u a)) md pos.forsAdrs)) md pos.forsAdrs) =
      honestVal pr pk u (forsPkAdrs pos.forsAdrs) := by
    change (tbl (forsPkAdrs pos.forsAdrs)).getD default = _
    rw [hTbl _ (forsRootAdrs_mem_constructionAddresses pos), Option.getD_some]
  have hpkPub : Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fPub pr pk)
      (hPub pr pk) (tlPub pr pk)
      (Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
        (fun a => pure (slSecOf pr u a)) md pos.forsAdrs)) md pos.forsAdrs) =
      honestVal pr pk u (forsPkAdrs pos.forsAdrs) := by
    rw [honestVal_forsPk]
    have hroots : (Id.run (Vector.ofFnM fun i : Fin vp.sl.params.k => do
        let idx := i.val * 2 ^ vp.sl.params.a + forsIdx vp.sl.params md i.val
        let leaf ← fPub pr pk (forsNodeAdrs pos.forsAdrs 0 idx)
          ((Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
            (fun a => pure (slSecOf pr u a)) md pos.forsAdrs))[i.val]).sk
        PerfectMerkleTree.climbM (forsNodeHashWith (hPub pr pk) pos.forsAdrs) idx leaf
          ((Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
            (fun a => pure (slSecOf pr u a)) md pos.forsAdrs))[i.val]).auth.toList)).toList =
        (Vector.ofFn fun i : Fin vp.params.k =>
          honestVal pr pk u (forsNodeAdrs pos.forsAdrs vp.params.a i.val)).toList := by
      apply List.ext_getElem
      · simp [ValidatedParams.sl, Params.slParams]
      · intro i hi₁ hi₂
        simp only [idRun_vector_ofFnM, Vector.getElem_toList, Vector.getElem_ofFn]
        have hi' : i < vp.sl.params.k := by simpa using hi₁
        have hsk : ((Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
            (fun a => pure (slSecOf pr u a)) md pos.forsAdrs))[i]).sk =
            slSecOf pr u (forsSkAdrs pos.forsAdrs (forsLeafIndex vp.sl.params md i)) := by
          unfold forsSignWithSecret
          rw [idRun_vector_ofFnM, Vector.getElem_ofFn]; rfl
        have hauth : ((Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
            (fun a => pure (slSecOf pr u a)) md pos.forsAdrs))[i]).auth =
            Id.run (PerfectMerkleTree.intrinsicAuthPathM
              (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
                (fun a => pure (slSecOf pr u a)) pos.forsAdrs)
              (forsNodeHashWith (hPub pr pk) pos.forsAdrs)
              (forsLeafIndex vp.sl.params md i) vp.sl.params.a) := by
          unfold forsSignWithSecret
          rw [idRun_vector_ofFnM, Vector.getElem_ofFn]; rfl
        change Id.run (PerfectMerkleTree.climbM (forsNodeHashWith (hPub pr pk) pos.forsAdrs)
          (forsLeafIndex vp.sl.params md i)
          (pr.F pk (forsNodeAdrs pos.forsAdrs 0 (forsLeafIndex vp.sl.params md i))
            ((Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
              (fun a => pure (slSecOf pr u a)) md pos.forsAdrs))[i]).sk)
          ((Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
            (fun a => pure (slSecOf pr u a)) md pos.forsAdrs))[i]).auth.toList) = _
        rw [hsk, hauth, idRun_intrinsicAuthPathM, PerfectMerkleTree.intrinsicAuthPath_toList,
          PerfectMerkleTree.idRun_climbM]
        change PerfectMerkleTree.climb _ (forsLeafIndex vp.sl.params md i)
          (Id.run (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
            (fun a => pure (slSecOf pr u a)) pos.forsAdrs (forsLeafIndex vp.sl.params md i))) _ = _
        rw [PerfectMerkleTree.climb_authPath
            (leaf := fun j => Id.run (forsLeafWithSecret pr.toSLHDSA.core (fPub pr pk)
              (fun a => pure (slSecOf pr u a)) pos.forsAdrs j)),
          forsLeafIndex_div, ← PerfectMerkleTree.idRun_merkleRootM]
        exact (forsNode_eq pr pk u hTbl pos ⟨i, hi'⟩ vp.sl.params.a i le_rfl (by simp)).1
    change pr.Th pk (forsPkAdrs pos.forsAdrs) _ = pr.Th pk (forsPkAdrs pos.forsAdrs) _
    exact congrArg (pr.Th pk _) hroots
  exact hpkTbl.trans hpkPub.symm

private theorem signFromPosition_eq (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl) :
    ∀ (layers : ℕ) (recoverFinal : Bool) (pos : LayerPosition vp.sl)
      (h : pos.layer.val + layers = vp.sl.params.d) (msg : pr.Y),
      Id.run (SLHDSA.GeneralHypertree.signFromPositionWithSecret
        pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk) (hTbl' pr tbl pk)
        (fun a => pure (slSecOf pr u a)) recoverFinal pos layers h msg) =
      Id.run (SLHDSA.GeneralHypertree.signFromPositionWithSecret
        pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk) (hPub pr pk)
        (fun a => pure (slSecOf pr u a)) recoverFinal pos layers h msg)
  | 0, _, _, _, _ => rfl
  | 1, recoverFinal, pos, _, msg => by
    have hx := (xmssSign_and_pkFromSig_eq pr pk u hTbl msg pos).1
    cases recoverFinal <;> simpa [SLHDSA.GeneralHypertree.signFromPositionWithSecret] using hx
  | layers + 2, _, pos, h, msg => by
    have hx := xmssSign_and_pkFromSig_eq pr pk u hTbl msg pos
    change (Id.run (SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
      (fTbl pr tbl pk) (tlTbl pr tbl pk) (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a))
      false (pos.next (by omega)) (layers + 1) _
      (Id.run (xmssPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        (hTbl' pr tbl pk) pos.leaf.val
        (Id.run (xmssSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
          (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val))
        msg pos.toAdrs)))).insertIdx 0
      (Id.run (xmssSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (tlTbl pr tbl pk)
        (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val)) =
      (Id.run (SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
      (fPub pr pk) (tlPub pr pk) (hPub pr pk) (fun a => pure (slSecOf pr u a))
      false (pos.next (by omega)) (layers + 1) _
      (Id.run (xmssPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
        (hPub pr pk) pos.leaf.val
        (Id.run (xmssSignWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
          (hPub pr pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val))
        msg pos.toAdrs)))).insertIdx 0
      (Id.run (xmssSignWithSecret pr.toSLHDSA.core (fPub pr pk) (tlPub pr pk)
        (hPub pr pk) (fun a => pure (slSecOf pr u a)) msg pos.toAdrs pos.leaf.val))
    rw [hx.2, hx.1, signFromPosition_eq pk u hTbl (layers + 1) false (pos.next (by omega)) _ _]

/-- **Stage-2 zero-`Th_λ` table-signing exactness**: whenever `tbl` is complete for `(pk, u)`
(in particular, `tbl = (slVirtualTreeDet pr pk u).2` precomputed in Stage 1 via `O_coll`),
`slSignTable` (which makes zero calls to `Th_λ`) produces the exact same signature as `slSignDet`. -/
theorem slSignTable_eq_slSignDet (pk : pr.PkSeed) (pkSl : pr.Y) (u : SlSecAdrs vp → pr.Y)
    {tbl : Adrs → Option pr.Y} (hTbl : TblComplete pr pk u tbl) (msg : List Byte) (R : pr.Y) :
    slSignTable pr tbl pk pkSl u msg R = slSignDet pr pk pkSl u msg R := by
  set parts := SLHDSA.splitDigest vp.sl.params (pr.HmsgSl R pk pkSl msg)
  have hfors := forsSign_and_pkFromSig_eq pr pk u hTbl parts.md.toList
    (BottomPosition.ofDigestParts vp.sl parts)
  rw [BottomPosition.forsAdrs_ofDigestParts] at hfors
  have hht := signFromPosition_eq pr pk u hTbl vp.sl.params.d (vp.sl.params.d == 1)
    (LayerPosition.initial vp.sl parts) (by simp)
    (Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (hPub pr pk) (tlPub pr pk)
      (Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
        (fun a => pure (slSecOf pr u a)) parts.md.toList parts.forsAdrs))
      parts.md.toList parts.forsAdrs))
  show ({ randomness := R, fors := _, hypertree := _ } : Stateless.Sig pr) =
       { randomness := R, fors := _, hypertree := _ }
  congr 1
  · exact hfors.1
  · change Id.run (SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
      (fTbl pr tbl pk) (tlTbl pr tbl pk) (hTbl' pr tbl pk) (fun a => pure (slSecOf pr u a))
      (vp.sl.params.d == 1) (LayerPosition.initial vp.sl parts) vp.sl.params.d _
      (Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fTbl pr tbl pk) (hTbl' pr tbl pk)
        (tlTbl pr tbl pk)
        (Id.run (forsSignWithSecret pr.toSLHDSA.core (fTbl pr tbl pk) (hTbl' pr tbl pk)
          (fun a => pure (slSecOf pr u a)) parts.md.toList parts.forsAdrs))
        parts.md.toList parts.forsAdrs))) =
      Id.run (SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
      (fPub pr pk) (tlPub pr pk) (hPub pr pk) (fun a => pure (slSecOf pr u a))
      (vp.sl.params.d == 1) (LayerPosition.initial vp.sl parts) vp.sl.params.d _
      (Id.run (SLHDSA.forsPkFromSigWith pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
        (tlPub pr pk)
        (Id.run (forsSignWithSecret pr.toSLHDSA.core (fPub pr pk) (hPub pr pk)
          (fun a => pure (slSecOf pr u a)) parts.md.toList parts.forsAdrs))
        parts.md.toList parts.forsAdrs)))
    rw [hfors.2]
    exact hht

end TableSigner

/-! ## 6. `AFTable`, `AFEager`, and eager-vs-lazy equivalence with `AF` -/

section EagerLazy

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

/-- State of `A_F` when stateless secrets are eager (or precomputed in Stage 1): no `SecCache`. -/
structure AFStEager where
  ctr : ℕ
  log : List Msg
  rnd : RndCache pr

/-- Stateless signing step parameterized by a deterministic signing function `signFn`. -/
noncomputable def slStepDet (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (rc : RndCache pr) :
    ProbComp (Stateless.Sig pr × RndCache pr) := do
  let optRand ← $ᵗ pr.Y
  let r ← (lazyRO (.sl optRand (slMsg pr Msg enc pkSf msg)) :
    StateT (RndCache pr) ProbComp pr.Y).run rc
  return (signFn pk pkSl (slMsg pr Msg enc pkSf msg) r.1, r.2)

/-- `A_F`'s signing oracle using `signFn` for stateless queries (no `SecCache`). -/
noncomputable def signAFDet (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    (K : Keys pr) (q : Msg × Bool) :
    StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)) (Option (Sig pr)) := do
  let s ← get
  if q.2 then
    let r ← (liftM (slStepDet pr Msg enc signFn K.pk K.pkSl K.pkSf q.1 s.rnd) :
      StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)) _)
    set { s with rnd := r.2, log := s.log ++ [q.1] }
    return some (.stateless r.1)
  else
    match K.S.leafSelect s.ctr with
    | none =>
      set { s with log := s.log ++ [q.1] }
      return none
    | some v =>
      let id := v.toLeafId vp.params.hsf
      let a ← (liftM ((FSpec pr Msg).query (.inr ((K.pkSl, q.1), id))) :
        StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)) (Option (Fxmss.Rom.Sig pr)))
      set { s with ctr := s.ctr + 1, log := s.log ++ [q.1] }
      return a.bind fun a => a.2.map (Scheme.Shrincs.Signature.stateful id.height id.index a.1)

/-- `A_F`'s handler using `signFn` for stateless queries. -/
noncomputable def implAFDet (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    (K : Keys pr) :
    QueryImpl (advSpec pr Msg) (StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg))) :=
  ((fun n => liftM ((FSpec pr Msg).query (.inl (.inl n))) :
      QueryImpl unifSpec (StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)))) +
    (fun x => liftM ((FSpec pr Msg).query (.inl (.inr x))) :
      QueryImpl (Fxmss.Rom.roSpec pr (BMsg pr Msg))
        (StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg))))) +
  (fun q => signAFDet pr Msg enc signFn K q :
    QueryImpl (Notions.ShrincsScheme.signSpec Msg (Sig pr))
      (StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg))))

/-- `A_F` given a stateless root `rootFn` and stateless signer `signFn`. -/
noncomputable def forgeExtDet (rootFn : pr.PkSeed → pr.Y)
    (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (S : Structure) (pk' : Fxmss.Rom.PK pr) :
    OracleComp (FSpec pr Msg) ((BMsg pr Msg × LeafId × Fxmss.Rom.Sig pr) × Ext) := do
  let K : Keys pr := ⟨S, pk'.1, rootFn pk'.1, pk'.2.2⟩
  let o ← (simulateQ (implAFDet pr Msg enc signFn K) (A.forge st S K.toPK)).run ⟨0, [], ∅⟩
  let fresh := !decide (o.1.1 ∈ o.2.log)
  return (outOf pr Msg K o.1.1 o.1.2, extOf pr Msg enc K o.1.1 fresh o.1.2)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg]
  [Nontrivial Msg] in
private theorem signAFDet_bound (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    (K : Keys pr) (q : Msg × Bool) (s : AFStEager pr Msg)
    (p : AFBounds.FIdx pr Msg → Prop) [DecidablePred p] (hp : ∀ n, ¬ p (.inl (.inl n))) (n : ℕ)
    (hn : ∀ x, p (.inr x) → 0 < n) :
    ((signAFDet pr Msg enc signFn K q).run s).IsQueryBoundP p n := by
  unfold signAFDet
  rcases q with ⟨m, _ | _⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_eq_true, ↓reduceIte]
    cases K.S.leafSelect s.ctr with
    | none => simp
    | some v => simpa using hn _
  · simp
    exact (AFBounds.liftM_stateT_bound pr Msg _ p hp s).mono (Nat.zero_le _)

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg]
  [Nontrivial Msg] in
private theorem implAFDet_step (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    (K : Keys pr)
    (P : (ℕ ⊕ Fxmss.Rom.RoIn pr (BMsg pr Msg)) ⊕ (Msg × Bool) → Prop) [DecidablePred P]
    (p : AFBounds.FIdx pr Msg → Prop) [DecidablePred p] (hp : ∀ n, ¬ p (.inl (.inl n)))
    (hro : ∀ x, p (.inl (.inr x)) → P (.inl (.inr x)))
    (hsign : ∀ q x, p (.inr x) → P (.inr q)) (t) (s : AFStEager pr Msg) :
    ((implAFDet pr Msg enc signFn K t).run s).IsQueryBoundP p (if P t then 1 else 0) := by
  rcases t with (n | x) | q
  · exact AFBounds.fwd_bound pr Msg _ s p _ (fun h => absurd h (hp n))
  · exact AFBounds.fwd_bound pr Msg _ s p _ (fun h => by simp [hro x h])
  · exact signAFDet_bound pr Msg enc signFn K q s p hp _ (fun x h => by simp [hsign q x h])

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
theorem forgeExtDet_signBound (rootFn : pr.PkSeed → pr.Y)
    (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (S : Structure) (pk : Fxmss.Rom.PK pr) :
    (forgeExtDet pr Msg enc rootFn signFn A st S pk).IsQueryBoundP Notions.IsSignQuery qs := by
  unfold forgeExtDet
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (A.signBound st S _)
    (implAFDet_step pr Msg enc signFn _ Notions.IsSignQuery Notions.IsSignQuery
      (fun _ h => h) (fun _ h => h) (fun _ _ _ => trivial)) _

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
theorem forgeExtDet_roBound (rootFn : pr.PkSeed → pr.Y)
    (signFn : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (st : A.State) (S : Structure) (pk : Fxmss.Rom.PK pr) :
    (forgeExtDet pr Msg enc rootFn signFn A.toShrincsAdversary st S pk).IsQueryBoundP
      (Fxmss.Rom.IsRoQuery' pr (BMsg pr Msg)) qh₂ := by
  unfold forgeExtDet
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (A.roBound₂ st S _)
    (implAFDet_step pr Msg enc signFn _ (IsRoQueryS pr Msg)
      (Fxmss.Rom.IsRoQuery' pr (BMsg pr Msg)) (fun _ h => h) (fun _ _ => trivial)
      (fun _ _ h => h)) _

/-- **`A_F` using eager stateless secrets `u`** (evaluates `slRootDet` and `slSignDet`). -/
noncomputable def AFEager {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (u : SlSecAdrs vp → pr.Y) :
    Fxmss.Rom.Forger pr (BMsg pr Msg) (slKeygenS pr) qs qh₁ qh₂ L where
  State := A.State
  chooseShape := A.chooseShape
  forge st S pk := Prod.fst <$>
    forgeExtDet pr Msg enc (fun p => slRootDet pr p u) (fun p pkSl m R => slSignDet pr p pkSl u m R)
      A.toShrincsAdversary st S pk
  signBound st S pk := by
    rw [isQueryBoundP_map_iff]
    exact forgeExtDet_signBound pr Msg enc _ _ A.toShrincsAdversary st S pk
  roBound₁ := A.roBound₁
  roBound₂ st S pk := by
    rw [isQueryBoundP_map_iff]
    exact forgeExtDet_roBound pr Msg enc _ _ A st S pk
  anchors_le := A.anchors_le

/-- **`A_F` using the Stage-1 precomputed `(pkSl, tbl)`**: performs ZERO stateless `Th_λ`
evaluations in Stage 2 (only table lookups via `tablePubQ` + `H_msg^sl`). -/
noncomputable def AFTable {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (u : SlSecAdrs vp → pr.Y) (pkSl : pr.Y) (tbl : Adrs → Option pr.Y) :
    Fxmss.Rom.Forger pr (BMsg pr Msg) (slKeygenS pr) qs qh₁ qh₂ L where
  State := A.State
  chooseShape := A.chooseShape
  forge st S pk := Prod.fst <$>
    forgeExtDet pr Msg enc (fun _ => pkSl) (fun p pkSl' m R => slSignTable pr tbl p pkSl' u m R)
      A.toShrincsAdversary st S pk
  signBound st S pk := by
    rw [isQueryBoundP_map_iff]
    exact forgeExtDet_signBound pr Msg enc _ _ A.toShrincsAdversary st S pk
  roBound₁ := A.roBound₁
  roBound₂ st S pk := by
    rw [isQueryBoundP_map_iff]
    exact forgeExtDet_roBound pr Msg enc _ _ A st S pk
  anchors_le := A.anchors_le

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
theorem forgeExtDet_congr
    (root₁ root₂ : pr.PkSeed → pr.Y)
    (sign₁ sign₂ : pr.PkSeed → pr.Y → List Byte → pr.Y → Stateless.Sig pr)
    {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (S : Structure) (pk : Fxmss.Rom.PK pr)
    (hroot : root₁ pk.1 = root₂ pk.1)
    (hsign : ∀ pkSl' m R, sign₁ pk.1 pkSl' m R = sign₂ pk.1 pkSl' m R) :
    forgeExtDet pr Msg enc root₁ sign₁ A st S pk =
      forgeExtDet pr Msg enc root₂ sign₂ A st S pk := by
  unfold forgeExtDet
  dsimp only
  rw [hroot]
  have himpl : implAFDet pr Msg enc sign₁ ⟨S, pk.1, root₂ pk.1, pk.2.2⟩ =
      implAFDet pr Msg enc sign₂ ⟨S, pk.1, root₂ pk.1, pk.2.2⟩ := by
    funext q
    rcases q with (n | x) | ⟨m, b⟩
    · rfl
    · rfl
    · change signAFDet pr Msg enc sign₁ _ (m, b) = signAFDet pr Msg enc sign₂ _ (m, b)
      unfold signAFDet
      cases b
      · rfl
      · dsimp only
        apply congrArg StateT.mk; funext s; simp only [slStepDet, hsign]
  rw [himpl]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- When `(pkSl, tbl) = slVirtualTreeDet pr pk u`, `stageHyb` with `AFTable` (zero stateless
`Th_λ` evaluations!) is **identical** to `stageHyb` with `AFEager`. -/
theorem stageHyb_AFTable_eq_AFEager {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (u : SlSecAdrs vp → pr.Y) (β : LeafId → ℕ → ℕ → pr.Y)
    (d : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) (pk : pr.PkSeed) :
    let vt := slVirtualTreeDet pr pk u
    stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFTable pr Msg enc A u vt.1 vt.2).toFxmssAdversary
        β d pk =
      stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A u).toFxmssAdversary
        β d pk := by
  have hvt := slVirtualTreeDet_spec pr pk u
  have hroot : (slVirtualTreeDet pr pk u).1 = slRootDet pr pk u :=
    hvt.1.trans (slRootDet_eq_honestVal pr pk u).symm
  have hsign : ∀ pkSl' m R, slSignTable pr (slVirtualTreeDet pr pk u).2 pk pkSl' u m R =
      slSignDet pr pk pkSl' u m R :=
    fun pkSl' m R => slSignTable_eq_slSignDet pr pk pkSl' u hvt.2.2 m R
  unfold stageHyb
  by_cases hS : d.S.TreeValid vp.params.hsf
  · simp only [hS, not_true_eq_false, ↓reduceIte]
    refine bind_congr fun pkSl => ?_
    set K : Keys pr := ⟨d.S, pk, pkSl, (Fxmss.Rom.hon pr d.S pk (Fxmss.Rom.digOf pr d.ys) β).pkSf⟩
    have hforge : (AFTable pr Msg enc A u (slVirtualTreeDet pr pk u).1
          (slVirtualTreeDet pr pk u).2).toFxmssAdversary.forge d.st K.S K.toPK =
        (AFEager pr Msg enc A u).toFxmssAdversary.forge d.st K.S K.toPK :=
      congrArg (Functor.map Prod.fst)
        (forgeExtDet_congr pr Msg enc (fun _ => (slVirtualTreeDet pr pk u).1)
          (fun p => slRootDet pr p u)
          (fun p pkSl' m R => slSignTable pr (slVirtualTreeDet pr pk u).2 p pkSl' u m R)
          (fun p pkSl' m R => slSignDet pr p pkSl' u m R)
          A.toShrincsAdversary d.st K.S K.toPK hroot hsign)
    unfold Fxmss.Rom.stage2Prog
    rw [hforge]
  · simp only [hS, not_false_eq_true, ↓reduceIte]

/-! ### Eager vs lazy stateless secrets (`AFEager` vs `AF`) -/

section EagerVsLazy

/-- Ambient spec for relating lazy `SecCache` (`AF`) to eager `u : SlSecAdrs vp → pr.Y`
(`AFEager`): `FSpec` plus queries to the finite stateless-secret table `SlSecAdrs vp →ₒ pr.Y`. -/
abbrev SecFSpec := FSpec pr Msg + (SlSecAdrs vp →ₒ pr.Y)

/-- Secret query in `SecFSpec`: queries `SlSecAdrs vp →ₒ pr.Y` when `a ∈ slSecretList`, else
returns `default`. -/
def secQueryF (a : Adrs) : OracleComp (SecFSpec pr Msg) pr.Y :=
  if h : a ∈ (slSecretList vp.sl).toFinset then
    (liftM ((SecFSpec pr Msg).query (.inr ⟨a, h⟩)) : OracleComp (SecFSpec pr Msg) pr.Y)
  else pure default

/-- Stateless root computation in `SecFSpec`. -/
def slRootSecF (pk : pr.PkSeed) : OracleComp (SecFSpec pr Msg) pr.Y :=
  letI := pubQ pr (OracleComp (SecFSpec pr Msg))
  SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
    (secQueryF pr Msg) pk

/-- Stateless signing internal call in `SecFSpec`. -/
def slSignSecF (msg : List Byte) (pk : pr.PkSeed) (pkSl R : pr.Y) :
    OracleComp (SecFSpec pr Msg) (Stateless.Sig pr) :=
  letI := pubQ pr (OracleComp (SecFSpec pr Msg))
  SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
    (secQueryF pr Msg) msg pk pkSl R

/-- Stateless signing step in `SecFSpec` (threads `RndCache` in `StateT`). -/
noncomputable def slStepSecF (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (rc : RndCache pr) :
    OracleComp (SecFSpec pr Msg) (Stateless.Sig pr × RndCache pr) := do
  let optRand ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : OracleComp (SecFSpec pr Msg) pr.Y)
  let r ← (liftM ((lazyRO (.sl optRand (slMsg pr Msg enc pkSf msg)) :
    StateT (RndCache pr) ProbComp pr.Y).run rc) : OracleComp (SecFSpec pr Msg) _)
  let sig ← slSignSecF pr Msg (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  return (sig, r.2)

/-- `A_F` signing oracle in `SecFSpec`. -/
noncomputable def signAFSecF (K : Keys pr) (q : Msg × Bool) :
    StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg)) (Option (Sig pr)) := do
  let s ← get
  if q.2 then
    let r ← (liftM (slStepSecF pr Msg enc K.pk K.pkSl K.pkSf q.1 s.rnd) :
      StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg)) _)
    set { s with rnd := r.2, log := s.log ++ [q.1] }
    return some (.stateless r.1)
  else
    match K.S.leafSelect s.ctr with
    | none =>
      set { s with log := s.log ++ [q.1] }
      return none
    | some v =>
      let id := v.toLeafId vp.params.hsf
      let a ← (liftM ((SecFSpec pr Msg).query (.inl (.inr ((K.pkSl, q.1), id)))) :
        StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg)) (Option (Fxmss.Rom.Sig pr)))
      set { s with ctr := s.ctr + 1, log := s.log ++ [q.1] }
      return a.bind fun a => a.2.map (Scheme.Shrincs.Signature.stateful id.height id.index a.1)

/-- `A_F` handler in `SecFSpec`. -/
noncomputable def implAFSecF (K : Keys pr) :
    QueryImpl (advSpec pr Msg) (StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg))) :=
  ((fun n => liftM ((SecFSpec pr Msg).query (.inl (.inl (.inl n)))) :
      QueryImpl unifSpec (StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg)))) +
    (fun x => liftM ((SecFSpec pr Msg).query (.inl (.inl (.inr x)))) :
      QueryImpl (Fxmss.Rom.roSpec pr (BMsg pr Msg))
        (StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg))))) +
  (fun q => signAFSecF pr Msg enc K q :
    QueryImpl (Notions.ShrincsScheme.signSpec Msg (Sig pr))
      (StateT (AFStEager pr Msg) (OracleComp (SecFSpec pr Msg))))

/-- `A_F`'s `stage2Prog` lifted to `SecFSpec` (returns `(out, finalSt)` after `implHyb`). -/
noncomputable def stage2SecF {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (K : Keys pr) :
    OracleComp (SecFSpec pr Msg) (BMsg pr Msg × LeafId × Fxmss.Rom.Sig pr × pr.Digest) := do
  let pkSl ← slRootSecF pr Msg K.pk
  let K' : Keys pr := ⟨K.S, K.pk, pkSl, K.pkSf⟩
  let o ← (simulateQ (implAFSecF pr Msg enc K') (A.forge st K.S K'.toPK)).run ⟨0, [], ∅⟩
  let out := outOf pr Msg K' o.1.1 o.1.2
  let yf ← ((SecFSpec pr Msg).query
    (.inl (.inl (.inr (roIn pr (BMsg pr Msg) out.2.2.1 K.pk K.pkSf out.2.1 out.1)))) :
      OracleComp (SecFSpec pr Msg) pr.Digest)
  let _ ← liftComp (completion pr (BMsg pr Msg) (otherMsg (BMsg pr Msg) out.1)
    (anchorList vp.params K.S)) (SecFSpec pr Msg)
  return (out.1, out.2.1, out.2.2, yf)

/-- Eager handler on `SecFSpec` (for fixed `K, H`): `FSpec` via `implHyb`, `SlSecAdrs` via table `u`. -/
noncomputable def implSecEager (K : Keys pr) (H : Honest pr) :
    QueryImpl (SecFSpec pr Msg) (StateT (St pr (BMsg pr Msg) × (SlSecAdrs vp → pr.Y)) ProbComp)
  | .inl t => StateT.mk fun s =>
      (fun r => (r.1, (r.2, s.2))) <$> (implHyb pr (BMsg pr Msg) K H t).run s.1
  | .inr a => StateT.mk fun s => pure (s.2 a, s)

/-- Lazy handler on `SecFSpec` (for fixed `K, H`): `FSpec` via `implHyb`, `SlSecAdrs` via `lazyRO`. -/
noncomputable def implSecLazy (K : Keys pr) (H : Honest pr) :
    QueryImpl (SecFSpec pr Msg) (StateT (St pr (BMsg pr Msg) × SecCache pr) ProbComp)
  | .inl t => StateT.mk fun s =>
      (fun r => (r.1, (r.2, s.2))) <$> (implHyb pr (BMsg pr Msg) K H t).run s.1
  | .inr a => StateT.mk fun s =>
      (fun r => (r.1, (s.1, r.2))) <$>
        (lazyRO (K.pk, a.toSecAdrs) : StateT (SecCache pr) ProbComp pr.Y).run s.2

/-- Eager-only interpreter `SecFSpec → FSpec` plugging in `u`. -/
def interpEager (u : SlSecAdrs vp → pr.Y) : QueryImpl (SecFSpec pr Msg) (OracleComp (FSpec pr Msg))
  | .inl t => (FSpec pr Msg).query t
  | .inr a => pure (u a)

/-- Lazy-only interpreter `SecFSpec → StateT SecCache (OracleComp FSpec)`. -/
noncomputable def interpLazy (pk : pr.PkSeed) :
    QueryImpl (SecFSpec pr Msg) (StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
  | .inl t => StateT.mk fun sc => (fun r => (r, sc)) <$> (FSpec pr Msg).query t
  | .inr a => StateT.mk fun sc =>
      (liftM ((lazyRO (pk, a.toSecAdrs) : StateT (SecCache pr) ProbComp pr.Y).run sc) :
        OracleComp (FSpec pr Msg) _)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem slRootSecF_interpEager (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) :
    simulateQ (interpEager pr Msg u) (slRootSecF pr Msg pk) = pure (slRootDet pr pk u) := by
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (OracleComp (FSpec pr Msg))
  let _ := pubQ pr Id
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (OracleComp (FSpec pr Msg)) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpEager pr Msg u) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpEager pr Msg u) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core F
    (secQueryF pr Msg) (fun a => pure (slSecOf pr u a))
    (fun a _ => by
      change simulateQ (interpEager pr Msg u) (secQueryF pr Msg a) = pure (slSecOf pr u a)
      unfold secQueryF slSecOf
      split_ifs <;> simp [interpEager])
    pk
  have h2 : SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
      (m := OracleComp (FSpec pr Msg)) (fun a => pure (slSecOf pr u a)) pk =
      pure (slRootDet pr pk u) := by
    let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
        Id (OracleComp (FSpec pr Msg)) :=
      { toMonadHom :=
          { toFun := fun {_} x => pure (Id.run x)
            toFun_pure' := fun _ => rfl
            toFun_bind' := fun _ _ => by rw [pure_bind]; rfl }
        map_query' := fun _ => rfl }
    exact (SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core G
      (fun a => pure (slSecOf pr u a)) (fun a => pure (slSecOf pr u a))
      (fun _ _ => rfl) pk).symm
  exact h1.trans h2

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem slSignSecF_interpEager (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) (pkSl : pr.Y)
    (msg : List Byte) (R : pr.Y) :
    simulateQ (interpEager pr Msg u) (slSignSecF pr Msg msg pk pkSl R) =
      pure (slSignDet pr pk pkSl u msg R) := by
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (OracleComp (FSpec pr Msg))
  let _ := pubQ pr Id
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (OracleComp (FSpec pr Msg)) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpEager pr Msg u) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpEager pr Msg u) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core F
    (secQueryF pr Msg) (fun a => pure (slSecOf pr u a))
    (fun a _ => by
      change simulateQ (interpEager pr Msg u) (secQueryF pr Msg a) = pure (slSecOf pr u a)
      unfold secQueryF slSecOf
      split_ifs <;> simp [interpEager])
    msg pk pkSl R
  have h2 : SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
      (m := OracleComp (FSpec pr Msg)) (fun a => pure (slSecOf pr u a)) msg pk pkSl R =
      pure (slSignDet pr pk pkSl u msg R) := by
    let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
        Id (OracleComp (FSpec pr Msg)) :=
      { toMonadHom :=
          { toFun := fun {_} x => pure (Id.run x)
            toFun_pure' := fun _ => rfl
            toFun_bind' := fun _ _ => by rw [pure_bind]; rfl }
        map_query' := fun _ => rfl }
    exact (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
      pr.toSLHDSA.core G
      (fun a => pure (slSecOf pr u a)) (fun a => pure (slSecOf pr u a))
      (fun _ _ => rfl) msg pk pkSl R).symm
  exact h1.trans h2

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
/-- Ledger-guarded congruence: two `StateT`-monadic SLH-DSA programs that agree on secret children
of `constructionAddresses` produce identical results (replaces `secQueryF` with `guardSec lazyRO`). -/
private theorem sec_congr_of_ledger {m : Type → Type} [Monad m] [LawfulMonad m]
    (sec₁ sec₂ : Adrs → m pr.Y)
    (hsec : ∀ a b, b ∈ constructionAddresses vp.sl → .inl a ∈ childAdrs vp.sl b →
      sec₁ a = sec₂ a) :
    (∀ pk, (letI := pubQ pr m; SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl)
        pr.toSLHDSA.core sec₁ pk) =
      (letI := pubQ pr m; SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl)
        pr.toSLHDSA.core sec₂ pk)) ∧
    (∀ msg pk pkRoot R, (letI := pubQ pr m; SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM
        (vp := vp.sl) pr.toSLHDSA.core sec₁ msg pk pkRoot R) =
      (letI := pubQ pr m; SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM
        (vp := vp.sl) pr.toSLHDSA.core sec₂ msg pk pkRoot R)) := by
  have hchain : ∀ (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len),
      sec₁ (wotsSkAdrs (wotsInstanceAdrs pos) c.val) =
      sec₂ (wotsSkAdrs (wotsInstanceAdrs pos) c.val) := fun pos c => by
    have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
    exact hsec _ _
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos c (t := 0) (by
        change 0 < vp.params.w - 1; omega))
      (by rw [childAdrs_wotsChainAdrs_setHashAddress_zero]; exact List.mem_singleton_self _)
  have hwotsPk : ∀ pos : LayerPosition vp.sl, ∀ pk,
      (letI := pubQ pr m; wotsPkGenWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₁ (wotsInstanceAdrs pos)) =
      (letI := pubQ pr m; wotsPkGenWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₂ (wotsInstanceAdrs pos)) := fun pos pk => by
    unfold wotsPkGenWithSecret wotsPkGenTopsWithSecret
    congr 1; apply congrArg Vector.ofFnM; funext i; rw [hchain pos i]
  have hwotsSign : ∀ msg (pos : LayerPosition vp.sl) pk,
      (letI := pubQ pr m; wotsSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        sec₁ msg (wotsInstanceAdrs pos)) =
      (letI := pubQ pr m; wotsSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        sec₂ msg (wotsInstanceAdrs pos)) := fun msg pos pk => by
    unfold wotsSignWithSecret
    apply congrArg Vector.ofFnM; funext i; rw [hchain pos i]
  have hmerkle : ∀ {Y : Type} (l₁ l₂ : ℕ → m Y) (nh : ℕ → ℕ → Y → Y → m Y) (z t : ℕ),
      (∀ i, i / 2 ^ z = t → l₁ i = l₂ i) →
      PerfectMerkleTree.merkleRootM l₁ nh z t = PerfectMerkleTree.merkleRootM l₂ nh z t := by
    intro Y l₁ l₂ nh z
    induction z with
    | zero => intro t h; exact h t (by simp)
    | succ z ih =>
      intro t h
      simp only [PerfectMerkleTree.merkleRootM]
      rw [ih (2 * t) (fun i hi => h i (by rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega)),
        ih (2 * t + 1) (fun i hi => h i (by rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega))]
  have hauth : ∀ {Y : Type} (l₁ l₂ : ℕ → m Y) (nh : ℕ → ℕ → Y → Y → m Y) (idx z : ℕ),
      (∀ i, i / 2 ^ z = idx / 2 ^ z → l₁ i = l₂ i) →
      PerfectMerkleTree.intrinsicAuthPathM l₁ nh idx z =
        PerfectMerkleTree.intrinsicAuthPathM l₂ nh idx z := by
    intro Y l₁ l₂ nh idx z
    induction z with
    | zero => intro _; rfl
    | succ z ih =>
      intro h
      simp only [PerfectMerkleTree.intrinsicAuthPathM]
      rw [ih (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hi])),
        hmerkle l₁ l₂ nh z _ (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hi,
            PerfectMerkleTree.sibling_div_two]))]
  have hxmssNode : ∀ (coord : LayerTreeCoord vp.sl) (pk : pr.PkSeed) (z t : ℕ),
      z ≤ vp.sl.params.hp → t < 2 ^ (vp.sl.params.hp - z) →
      (letI := pubQ pr m; xmssNodeWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₁ coord.toAdrs z t) =
      (letI := pubQ pr m; xmssNodeWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₂ coord.toAdrs z t) :=
    fun coord pk z t hz ht =>
      hmerkle _ _ _ z t fun i hi =>
        hwotsPk ⟨coord.layer, coord.tree, ⟨i, lt_pow_of_div_pow_lt hz hi ht⟩⟩ pk
  have hxmssSign : ∀ msg (pos : LayerPosition vp.sl) pk,
      (letI := pubQ pr m; xmssSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
        sec₁ msg pos.toAdrs pos.leaf.val) =
      (letI := pubQ pr m; xmssSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
        sec₂ msg pos.toAdrs pos.leaf.val) := fun msg pos pk => by
    unfold xmssSignWithSecret
    have h1 := hauth
      (letI := pubQ pr m; xmssLeafWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₁ pos.toAdrs)
      (letI := pubQ pr m; xmssLeafWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₂ pos.toAdrs)
      (letI := pubQ pr m; xmssNodeHashWith (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) pos.toAdrs)
      pos.leaf.val vp.sl.params.hp (fun i hi =>
        hwotsPk ⟨pos.layer, pos.tree, ⟨i, lt_pow_of_div_pow_lt le_rfl
          (hi.trans (Nat.div_eq_of_lt pos.leaf.isLt)) (by positivity)⟩⟩ pk)
    rw [h1]
    refine bind_congr fun path => ?_
    change (letI := pubQ pr m; wotsSignWithSecret pr.toSLHDSA.core
      (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) sec₁ msg (wotsInstanceAdrs pos)) >>= _ = _
    rw [hwotsSign msg pos pk]
    rfl
  have hht : ∀ (layers : ℕ) (rf : Bool) (pos : LayerPosition vp.sl)
      (h : pos.layer.val + layers = vp.sl.params.d) (msg : pr.Y) (pk : pr.PkSeed),
      (letI := pubQ pr m; SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
        (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₁ rf pos layers h msg) =
      (letI := pubQ pr m; SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
        (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₂ rf pos layers h msg) := by
    intro layers
    induction layers with
    | zero => intro _ _ _ _ _; rfl
    | succ layers ih =>
      cases layers with
      | zero =>
        intro rf pos h msg pk
        simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret, hxmssSign msg pos pk]
      | succ layers =>
        intro rf pos h msg pk
        simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret, hxmssSign msg pos pk]
        refine bind_congr fun sig => bind_congr fun root => ?_
        rw [ih false _ _ root pk]
  have hforsSk : ∀ (pos : BottomPosition vp.sl) (tree : Fin vp.sl.params.k) {i : ℕ},
      i / 2 ^ vp.sl.params.a = tree.val →
      sec₁ (forsSkAdrs pos.forsAdrs i) = sec₂ (forsSkAdrs pos.forsAdrs i) := fun pos tree {i} hi =>
    hsec _ _ (forsLeafAdrs_mem_constructionAddresses pos tree hi)
      (by rw [childAdrs_forsNodeAdrs_zero]; exact List.mem_singleton_self _)
  have hforsSign : ∀ md (pos : BottomPosition vp.sl) pk,
      (letI := pubQ pr m; forsSignWithSecretM pr.toSLHDSA.core sec₁ md pk pos.forsAdrs) =
      (letI := pubQ pr m; forsSignWithSecretM pr.toSLHDSA.core sec₂ md pk pos.forsAdrs) :=
    fun md pos pk => by
      unfold forsSignWithSecretM forsSignWithSecret
      apply congrArg Vector.ofFnM; funext tree
      dsimp only
      have hdiv := forsLeafIndex_div vp.sl.params md tree.val
      change sec₁ (forsSkAdrs pos.forsAdrs (forsLeafIndex vp.sl.params md tree.val)) >>= _ = _
      rw [hforsSk pos tree hdiv]
      refine bind_congr fun _ => ?_
      rw [hauth _ _ _ _ _ fun i hi => by
        unfold forsLeafWithSecret; rw [hforsSk pos tree (hi.trans hdiv)]]
      rfl
  constructor
  · intro pk
    have h := hxmssNode (LayerTreeCoord.top vp.sl) pk vp.sl.params.hp 0 le_rfl (by simp)
    rw [LayerTreeCoord.top_toAdrs_layerAdrs] at h
    exact h
  · intro msg pk pkRoot R
    unfold SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM
    refine bind_congr fun digest => ?_
    dsimp only
    have hpos := BottomPosition.forsAdrs_ofDigestParts vp.sl (SLHDSA.splitDigest vp.sl.params digest)
    rw [← hpos, hforsSign _ _ pk, hpos]
    refine bind_congr fun _ => bind_congr fun forsPk => ?_
    unfold SLHDSA.GeneralHypertree.signWithSecretM SLHDSA.GeneralHypertree.signWithSecret
    rw [hht vp.sl.params.d _ _ _ forsPk pk]

omit [Fintype pr.Y] [DecidableEq pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg]
  [Nontrivial Msg] in
private theorem slRootSecF_interpLazy (pk : pr.PkSeed) (sc : SecCache pr) :
    (simulateQ (interpLazy pr Msg pk) (slRootSecF pr Msg pk)).run sc =
      (liftM (slRootP pr pk sc) : OracleComp (FSpec pr Msg) _) := by
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
  let _ := pubQ pr (StateT (SecCache pr) ProbComp)
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpLazy pr Msg pk) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpLazy pr Msg pk) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core F
    (secQueryF pr Msg)
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (fun a _ => by
      change simulateQ (interpLazy pr Msg pk) (secQueryF pr Msg a) = _
      unfold secQueryF
      split_ifs <;> simp [interpLazy, SlSecAdrs.toSecAdrs])
    pk
  have h2 := (sec_congr_of_ledger pr
    (m := StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (guardSec pr (fun x => StateT.mk fun sc => liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a b hb hab => by
      have hm : a ∈ (slSecretList vp.sl).toFinset := List.mem_toFinset.2 (mem_slSecretList hb hab)
      have hsk : a.IsSecretKey := isSecretKey_of_mem_slSecretList (List.mem_toFinset.1 hm)
      simp [hm, guardSec, hsk])).1 pk
  let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (StateT (SecCache pr) ProbComp) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} m => StateT.mk fun sc => liftM (m.run sc)
          toFun_pure' := fun x => by ext sc; simp
          toFun_bind' := fun ma mb => by ext sc; simp [StateT.run_bind] }
      map_query' := fun q => by ext sc; simp }
  have h3 := SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core G
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
    (guardSec pr (fun x => StateT.mk fun sc => liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a h => by ext sc; simp [G, guardSec, h]) pk
  have hcomb := congrArg (fun f => f.run sc) ((h1.trans h2).trans h3.symm)
  exact hcomb

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem slStepSecF_interpLazy (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg)
    (sc : SecCache pr) (rc : RndCache pr) :
    (simulateQ (interpLazy pr Msg pk) (slStepSecF pr Msg enc pk pkSl pkSf msg rc)).run sc =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        (liftM (slStepP pr Msg enc pk pkSl pkSf msg sc rc) : OracleComp (FSpec pr Msg) _) := by
  have hlift : ∀ {α : Type} (p : ProbComp α) (s : SecCache pr),
      (simulateQ (interpLazy pr Msg pk) (liftM p : OracleComp (SecFSpec pr Msg) α)).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p
    induction p using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      have hq : (simulateQ (interpLazy pr Msg pk)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (SecFSpec pr Msg) _)).run s =
          (fun u => (u, s)) <$>
            (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := by
        change (interpLazy pr Msg pk (.inl (.inl (.inl t)))).run s = _
        rfl
      rw [liftM_bind, liftM_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left, map_bind]
      exact bind_congr fun u => ih u s
  have hliftM2 : ∀ {α : Type} (p : ProbComp α) (s : SecCache pr) (r : RndCache pr),
      ((liftM p : M2 pr α).run s).run r = (fun a => ((a, s), r)) <$> p := fun p s r => by
    simp [MonadLiftT.monadLift, MonadLift.monadLift, map_eq_bind_pure_comp]
  have hliftRc : ∀ {α : Type} (m : StateT (RndCache pr) ProbComp α) (s : SecCache pr)
      (r : RndCache pr),
      ((liftM m : M2 pr α).run s).run r = (fun z => ((z.1, s), z.2)) <$> m.run r := fun m s r => by
    simp [MonadLiftT.monadLift, map_eq_bind_pure_comp]
  unfold slStepSecF slStepP slSignM
  simp only [simulateQ_bind, StateT.run_bind, hlift, hliftM2, hliftRc, bind_map_left,
    liftM_bind, map_bind]
  refine bind_congr fun optRand => bind_congr fun r => ?_
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
  let _ := pubQ pr (StateT (SecCache pr) ProbComp)
  let _ := pubQ pr (M2 pr)
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpLazy pr Msg pk) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpLazy pr Msg pk) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core F
    (secQueryF pr Msg)
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (fun a _ => by
      change simulateQ (interpLazy pr Msg pk) (secQueryF pr Msg a) = _
      unfold secQueryF
      split_ifs <;> simp [interpLazy, SlSecAdrs.toSecAdrs])
    (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  have h2 := (sec_congr_of_ledger pr
    (m := StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (guardSec pr (fun x => StateT.mk fun sc => liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a b hb hab => by
      have hm : a ∈ (slSecretList vp.sl).toFinset := List.mem_toFinset.2 (mem_slSecretList hb hab)
      have hsk : a.IsSecretKey := isSecretKey_of_mem_slSecretList (List.mem_toFinset.1 hm)
      simp [hm, guardSec, hsk])).2 (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  let G_lift : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (StateT (SecCache pr) ProbComp) (M2 pr) :=
    { toMonadHom :=
        { toFun := fun {_} m => StateT.mk fun sc => StateT.mk fun rc =>
            (fun z => (z, rc)) <$> m.run sc
          toFun_pure' := fun x => by ext sc rc; simp
          toFun_bind' := fun ma mb => by ext sc rc; simp [StateT.run_bind, map_bind, bind_map_left] }
      map_query' := fun q => by ext sc rc; simp }
  let G_spec : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (StateT (SecCache pr) ProbComp) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} m => StateT.mk fun sc => liftM (m.run sc)
          toFun_pure' := fun x => by ext sc; simp
          toFun_bind' := fun ma mb => by ext sc; simp [StateT.run_bind] }
      map_query' := fun q => by ext sc; simp }
  have h3 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core G_spec
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
    (guardSec pr (fun x => StateT.mk fun sc =>
      liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a h => by ext sc; simp [G_spec, guardSec, h]) (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  have h4 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core G_lift
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → M2 pr pr.Y) pk)
    (fun a h => by
      ext sc rc
      simp only [G_lift, guardSec, h, ↓reduceDIte, lazyRO, StateT.run_mk]
      cases sc (pk, ⟨a, h⟩) with
      | none => simp [map_eq_bind_pure_comp, bind_assoc]
      | some v => simp)
    (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  have hcomb : (simulateQ (interpLazy pr Msg pk)
      (slSignSecF pr Msg (slMsg pr Msg enc pkSf msg) pk pkSl r.1)).run sc =
      (liftM ((letI := pubQ pr (StateT (SecCache pr) ProbComp);
        SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
          (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
          (slMsg pr Msg enc pkSf msg) pk pkSl r.1).run sc) : OracleComp (FSpec pr Msg) _) :=
    congrArg (fun f => f.run sc) ((h1.trans h2).trans h3.symm)
  have hrun4 : ((letI := pubQ pr (M2 pr);
      SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
        (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → M2 pr pr.Y) pk)
        (slMsg pr Msg enc pkSf msg) pk pkSl r.1).run sc).run r.2 =
      (fun z => (z, r.2)) <$> ((letI := pubQ pr (StateT (SecCache pr) ProbComp);
        SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
          (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
          (slMsg pr Msg enc pkSf msg) pk pkSl r.1).run sc) :=
    (congrArg (fun f => (f.run sc).run r.2) h4).symm
  rw [hcomb, hrun4]
  simp [bind_pure_comp, map_eq_bind_pure_comp]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] in
private theorem interpEager_stage2SecF {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (u : SlSecAdrs vp → pr.Y) (st : A.State) (K : Keys pr) :
    simulateQ (interpEager pr Msg u) (stage2SecF pr Msg enc A.toShrincsAdversary st K) =
      Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr)
        (AFEager pr Msg enc A u).toFxmssAdversary st K := by
  have hliftE : ∀ {α : Type} (p : ProbComp α),
      simulateQ (interpEager pr Msg u) (liftM p : OracleComp (SecFSpec pr Msg) α) =
        (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      have hq : simulateQ (interpEager pr Msg u)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (SecFSpec pr Msg) _) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := rfl
      rw [liftM_bind, liftM_bind, simulateQ_bind, hq]
      exact bind_congr fun x => ih x
  have hliftF : ∀ {α : Type} (oa : OracleComp (FSpec pr Msg) α),
      simulateQ (interpEager pr Msg u) (liftComp oa (SecFSpec pr Msg)) = oa := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [OracleComp.liftComp_bind, simulateQ_bind]
      have hq : simulateQ (interpEager pr Msg u) (OracleComp.liftComp
          (liftM ((FSpec pr Msg).query t) : OracleComp (FSpec pr Msg) _) (SecFSpec pr Msg)) =
          (liftM ((FSpec pr Msg).query t) : OracleComp (FSpec pr Msg) _) := by
        rcases t with (n | x) | q <;>
          (simp only [OracleComp.liftComp_liftM_query];
            change interpEager pr Msg u (.inl _) >>= pure = _; simp [interpEager])
      rw [hq]
      exact bind_congr fun x => ih x
  have hliftDet : ∀ {α : Type} (p : ProbComp α) (s : AFStEager pr Msg),
      (liftM p : StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)) α).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p s
    change liftComp (liftComp (p >>= fun a => pure (a, s))
        (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
          Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
        (FSpec pr Msg) = _
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [bind_assoc, OracleComp.liftComp_bind, OracleComp.liftComp_bind, liftM_bind, map_bind]
      have hq : liftComp (liftComp (liftM (unifSpec.query t) : ProbComp _)
          (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
            Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
          (FSpec pr Msg) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := by
        simp; rfl
      rw [hq]
      exact bind_congr fun u => ih u
  have hstep : ∀ (K' : Keys pr) (t) (s : AFStEager pr Msg),
      simulateQ (interpEager pr Msg u) ((implAFSecF pr Msg enc K' t).run s) =
        (implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K' t).run s := by
    intro K' t s
    rcases t with (n | x) | ⟨m, b⟩
    · simp [implAFSecF, implAFDet, interpEager, StateT.run_monadLift]
    · simp [implAFSecF, implAFDet, interpEager, StateT.run_monadLift]
    · unfold implAFSecF implAFDet
      simp only [QueryImpl.add_apply_inr, signAFSecF, signAFDet, StateT.run_bind, StateT.run_get,
        pure_bind]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases K'.S.leafSelect s.ctr with
        | none => simp
        | some v => simp [interpEager, StateT.run_monadLift]
      · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self, hliftDet,
          StateT.run_set, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_map_left]
        unfold slStepSecF slStepDet
        simp only [simulateQ_bind, hliftE, liftM_bind, bind_assoc, simulateQ_pure, pure_bind]
        refine bind_congr fun optRand => bind_congr fun r => ?_
        rw [slSignSecF_interpEager]
        simp
  have hsim : ∀ {α : Type} (K' : Keys pr) (oa : OracleComp (advSpec pr Msg) α)
      (s : AFStEager pr Msg),
      simulateQ (interpEager pr Msg u) ((simulateQ (implAFSecF pr Msg enc K') oa).run s) =
        (simulateQ (implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K') oa).run
          s := by
    intro α K' oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep]
      exact bind_congr fun z => ih z.1 z.2
  unfold stage2SecF Fxmss.Rom.stage2Prog AFEager forgeExtDet
  simp only [simulateQ_bind, slRootSecF_interpEager, pure_bind, hsim, bind_map_left, bind_assoc]
  refine bind_congr fun o => ?_
  have hq : simulateQ (interpEager pr Msg u)
      ((SecFSpec pr Msg).query (.inl (.inl (.inr (roIn pr (BMsg pr Msg)
        (outOf pr Msg ⟨K.S, K.pk, slRootDet pr K.pk u, K.pkSf⟩ o.1.1 o.1.2).2.2.1 K.pk K.pkSf
        (outOf pr Msg ⟨K.S, K.pk, slRootDet pr K.pk u, K.pkSf⟩ o.1.1 o.1.2).2.1
        (outOf pr Msg ⟨K.S, K.pk, slRootDet pr K.pk u, K.pkSf⟩ o.1.1 o.1.2).1)))) :
        OracleComp (SecFSpec pr Msg) pr.Digest) =
      ((FSpec pr Msg).query (.inl (.inr (roIn pr (BMsg pr Msg)
        (outOf pr Msg ⟨K.S, K.pk, slRootDet pr K.pk u, K.pkSf⟩ o.1.1 o.1.2).2.2.1 K.pk K.pkSf
        (outOf pr Msg ⟨K.S, K.pk, slRootDet pr K.pk u, K.pkSf⟩ o.1.1 o.1.2).2.1
        (outOf pr Msg ⟨K.S, K.pk, slRootDet pr K.pk u, K.pkSf⟩ o.1.1 o.1.2).1))) :
        OracleComp (FSpec pr Msg) pr.Digest) := rfl
  simp only [hq, hliftF, simulateQ_pure]
  rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] in
private theorem interpLazy_stage2SecF {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg enc qs qh₁ qh₂ L) (st : A.State) (K : Keys pr) :
    Prod.fst <$> (simulateQ (interpLazy pr Msg K.pk)
        (stage2SecF pr Msg enc A.toShrincsAdversary st K)).run ∅ =
      Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A).toFxmssAdversary
        st K := by
  have hliftF : ∀ {α : Type} (oa : OracleComp (FSpec pr Msg) α) (sc : SecCache pr),
      (simulateQ (interpLazy pr Msg K.pk) (liftComp oa (SecFSpec pr Msg))).run sc =
        (fun a => (a, sc)) <$> oa := by
    intro α oa sc
    induction oa using OracleComp.inductionOn generalizing sc with
    | pure a => simp
    | query_bind t k ih =>
      rw [OracleComp.liftComp_bind, simulateQ_bind, StateT.run_bind]
      have hq : (simulateQ (interpLazy pr Msg K.pk) (OracleComp.liftComp
          (liftM ((FSpec pr Msg).query t) : OracleComp (FSpec pr Msg) _) (SecFSpec pr Msg))).run sc =
          (fun x => (x, sc)) <$> (liftM ((FSpec pr Msg).query t) : OracleComp (FSpec pr Msg) _) := by
        rcases t with (n | x) | q <;>
          (simp only [OracleComp.liftComp_liftM_query];
            change ((interpLazy pr Msg K.pk (.inl _)) >>= pure).run sc = _;
            rw [bind_pure]; rfl)
      rw [hq, bind_map_left, map_bind]
      exact bind_congr fun x => ih x sc
  have hliftAF : ∀ {α : Type} (p : ProbComp α) (s : AFSt pr Msg),
      (liftM p : StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)) α).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p s
    change liftComp (liftComp (p >>= fun a => pure (a, s))
        (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
          Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
        (FSpec pr Msg) = _
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [bind_assoc, OracleComp.liftComp_bind, OracleComp.liftComp_bind, liftM_bind, map_bind]
      have hq : liftComp (liftComp (liftM (unifSpec.query t) : ProbComp _)
          (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
            Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
          (FSpec pr Msg) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := by
        simp; rfl
      rw [hq]
      exact bind_congr fun u => ih u
  have hstep : ∀ (K' : Keys pr) (hpk : K'.pk = K.pk) (t) (s : AFStEager pr Msg) (sc : SecCache pr),
      (simulateQ (interpLazy pr Msg K.pk) ((implAFSecF pr Msg enc K' t).run s)).run sc =
        (fun z => ((z.1, ⟨z.2.ctr, z.2.log, z.2.rnd⟩), z.2.sec)) <$>
          (implAF pr Msg enc K' t).run ⟨s.ctr, s.log, sc, s.rnd⟩ := by
    intro K' hpk t s sc
    rcases t with (n | x) | ⟨m, b⟩
    · simp [implAFSecF, implAF, interpLazy, StateT.run_monadLift, map_eq_bind_pure_comp]
    · simp [implAFSecF, implAF, interpLazy, StateT.run_monadLift, map_eq_bind_pure_comp]
    · unfold implAFSecF implAF
      simp only [QueryImpl.add_apply_inr, signAFSecF, signAF, StateT.run_bind, StateT.run_get,
        pure_bind]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases K'.S.leafSelect s.ctr with
        | none => simp
        | some v =>
          simp [interpLazy, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc]
      · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self, hliftAF,
          StateT.run_set, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_map_left,
          map_bind]
        rw [← hpk, slStepSecF_interpLazy]
        simp
  have hsim : ∀ {α : Type} (K' : Keys pr) (hpk : K'.pk = K.pk)
      (oa : OracleComp (advSpec pr Msg) α) (s : AFStEager pr Msg) (sc : SecCache pr),
      (simulateQ (interpLazy pr Msg K.pk) ((simulateQ (implAFSecF pr Msg enc K') oa).run s)).run
          sc =
        (fun z => ((z.1, ⟨z.2.ctr, z.2.log, z.2.rnd⟩), z.2.sec)) <$>
          (simulateQ (implAF pr Msg enc K') oa).run ⟨s.ctr, s.log, sc, s.rnd⟩ := by
    intro α K' hpk oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s sc; simp
    | query_bind t k ih =>
      intro s sc
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep K' hpk,
        bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 ⟨z.2.ctr, z.2.log, z.2.rnd⟩ z.2.sec
  unfold stage2SecF Fxmss.Rom.stage2Prog AF AFAdv forgeExt
  simp only [simulateQ_bind, StateT.run_bind, slRootSecF_interpLazy, map_bind, bind_assoc,
    bind_map_left]
  refine bind_congr fun r => ?_
  rw [hsim ⟨K.S, K.pk, r.1, K.pkSf⟩ rfl]
  simp only [bind_map_left]
  refine bind_congr fun o => ?_
  have hq : (simulateQ (interpLazy pr Msg K.pk)
      ((SecFSpec pr Msg).query (.inl (.inl (.inr (roIn pr (BMsg pr Msg)
        (outOf pr Msg ⟨K.S, K.pk, r.1, K.pkSf⟩ o.1.1 o.1.2).2.2.1 K.pk K.pkSf
        (outOf pr Msg ⟨K.S, K.pk, r.1, K.pkSf⟩ o.1.1 o.1.2).2.1
        (outOf pr Msg ⟨K.S, K.pk, r.1, K.pkSf⟩ o.1.1 o.1.2).1)))) :
        OracleComp (SecFSpec pr Msg) pr.Digest)).run o.2.sec =
      (fun yf => (yf, o.2.sec)) <$> ((FSpec pr Msg).query (.inl (.inr (roIn pr (BMsg pr Msg)
        (outOf pr Msg ⟨K.S, K.pk, r.1, K.pkSf⟩ o.1.1 o.1.2).2.2.1 K.pk K.pkSf
        (outOf pr Msg ⟨K.S, K.pk, r.1, K.pkSf⟩ o.1.1 o.1.2).2.1
        (outOf pr Msg ⟨K.S, K.pk, r.1, K.pkSf⟩ o.1.1 o.1.2).1))) :
        OracleComp (FSpec pr Msg) pr.Digest) := rfl
  simp only [hq, bind_map_left, hliftF, simulateQ_pure, StateT.run_pure, map_pure, pure_bind]
  rfl

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem simulateQ_implSecEager {α : Type} (K : Keys pr) (H : Honest pr)
    (u : SlSecAdrs vp → pr.Y) (oa : OracleComp (SecFSpec pr Msg) α) (s : St pr (BMsg pr Msg)) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (implSecEager pr Msg K H) oa).run (s, u) =
      (simulateQ (implHyb pr (BMsg pr Msg) K H) (simulateQ (interpEager pr Msg u) oa)).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with f | a
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecEager, interpEager,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 z.2
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecEager, interpEager,
        StateT.run_bind, StateT.run_mk, pure_bind]
      exact ih (u a) s

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem simulateQ_implSecLazy {α : Type} (K : Keys pr) (H : Honest pr)
    (oa : OracleComp (SecFSpec pr Msg) α) (s : St pr (BMsg pr Msg)) (sc : SecCache pr) :
    (fun z => ((z.1, z.2.2), z.2.1)) <$> (simulateQ (implSecLazy pr Msg K H) oa).run (s, sc) =
      (simulateQ (implHyb pr (BMsg pr Msg) K H)
        ((simulateQ (interpLazy pr Msg K.pk) oa).run sc)).run s := by
  have hlift : ∀ {β : Type} (p : ProbComp β) (s : St pr (BMsg pr Msg)),
      (simulateQ (implHyb pr (BMsg pr Msg) K H) (liftM p : OracleComp (FSpec pr Msg) β)).run s =
        (fun x => (x, s)) <$> p := by
    intro β p
    induction p using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      have hq : (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _)).run s =
          (fun x => (x, s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
        change (implHyb pr (BMsg pr Msg) K H (.inl (.inl t))).run s = _
        simp [Fxmss.Rom.implHyb, Fxmss.Rom.impl, map_eq_bind_pure_comp]
      rw [liftM_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left, map_bind]
      exact bind_congr fun x => ih x s
  induction oa using OracleComp.inductionOn generalizing s sc with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with f | a
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecLazy, interpLazy,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 z.2 sc
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecLazy, interpLazy,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind, hlift]
      exact bind_congr fun z => ih z.1 s z.2

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem implSecEager_evalDistEq_implSecLazy {α : Type} (K : Keys pr) (H : Honest pr)
    (oa : OracleComp (SecFSpec pr Msg) α) (s : St pr (BMsg pr Msg)) :
    (do let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        (fun z : α × (St pr (BMsg pr Msg) × (SlSecAdrs vp → pr.Y)) => (z.1, z.2.1)) <$>
          (simulateQ (implSecEager pr Msg K H) oa).run (s, u)) =ᵈ
      (fun z : α × (St pr (BMsg pr Msg) × SecCache pr) => (z.1, z.2.1)) <$>
        (simulateQ (implSecLazy pr Msg K H) oa).run (s, ∅) := by
  let κ : St pr (BMsg pr Msg) × SecCache pr → ProbComp (St pr (BMsg pr Msg) × (SlSecAdrs vp → pr.Y)) :=
    fun st => (fun u => (st.1, fun a => (st.2 (K.pk, a.toSecAdrs)).getD (u a))) <$>
      ($ᵗ (SlSecAdrs vp → pr.Y))
  have hstep : ∀ (t : (SecFSpec pr Msg).Domain) (stL : St pr (BMsg pr Msg) × SecCache pr),
      (κ stL >>= fun stE => (implSecEager pr Msg K H t).run stE) =ᵈ
        ((implSecLazy pr Msg K H t).run stL >>= fun z => (z.1, ·) <$> κ z.2) := by
    intro t ⟨sL, sc⟩
    rcases t with f | a
    · simp only [κ, implSecEager, implSecLazy, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      exact EvalDistEq.bind_bind_swap _ _ _
    · simp only [κ, implSecEager, implSecLazy, StateT.run_mk, lazyRO, map_eq_bind_pure_comp,
        bind_assoc, Function.comp_apply, pure_bind]
      cases hsc : sc (K.pk, a.toSecAdrs) with
      | some v =>
        simp only [Option.getD_some, pure_bind]
        exact EvalDistEq.refl _
      | none =>
        simp only [Option.getD_none, bind_assoc, Function.comp_apply, pure_bind]
        change (($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
            pure (u a, (sL, fun b => (sc (K.pk, b.toSecAdrs)).getD (u b)))) =ᵈ
          (($ᵗ pr.Y) >>= fun v => ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
            pure (v, (sL, fun b =>
              ((sc.cacheQuery (K.pk, a.toSecAdrs) v) (K.pk, b.toSecAdrs)).getD (u b))))
        refine EvalDistEq.trans (EvalDistEq.symm (Repro.resample a _)) ?_
        refine EvalDistEq.bind_right _ fun v => EvalDistEq.bind_right _ fun u => ?_
        have hupd : (fun b : SlSecAdrs vp =>
              (sc (K.pk, b.toSecAdrs)).getD (Function.update u a v b)) =
            (fun b : SlSecAdrs vp =>
              ((sc.cacheQuery (K.pk, a.toSecAdrs) v) (K.pk, b.toSecAdrs)).getD (u b)) := by
          funext b
          by_cases hba : b = a
          · subst hba; simp [hsc]
          · have hne : (K.pk, b.toSecAdrs) ≠ (K.pk, a.toSecAdrs) := by
              intro h
              apply hba
              have h1 : b.1 = a.1 := congrArg (fun p : pr.PkSeed × SecAdrs => p.2.1) h
              exact Subtype.ext h1
            simp [Function.update_of_ne hba, hne]
        simp only [Function.update_self, hupd]
        exact EvalDistEq.refl _
  have hgen : ∀ (oa : OracleComp (SecFSpec pr Msg) α) (stL : St pr (BMsg pr Msg) × SecCache pr),
      (κ stL >>= fun stE => (fun z => (z.1, z.2.1)) <$>
        (simulateQ (implSecEager pr Msg K H) oa).run stE) =ᵈ
      (fun z => (z.1, z.2.1)) <$> (simulateQ (implSecLazy pr Msg K H) oa).run stL := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro stL
      simp only [simulateQ_pure, StateT.run_pure, κ, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      exact EvalDistEq.bind_const ($ᵗ (SlSecAdrs vp → pr.Y)) (pure (a, stL.1))
    | query_bind t k ih =>
      intro stL
      have h1 : (κ stL >>= fun stE => (fun z => (z.1, z.2.1)) <$>
            (simulateQ (implSecEager pr Msg K H) (liftM ((SecFSpec pr Msg).query t) >>= k)).run stE) =
          (κ stL >>= fun stE => (implSecEager pr Msg K H t).run stE) >>= fun z =>
            (fun w => (w.1, w.2.1)) <$> (simulateQ (implSecEager pr Msg K H) (k z.1)).run z.2 := by
        simp [bind_assoc, map_bind]
      have h2 : (fun z => (z.1, z.2.1)) <$>
            (simulateQ (implSecLazy pr Msg K H) (liftM ((SecFSpec pr Msg).query t) >>= k)).run stL =
          (implSecLazy pr Msg K H t).run stL >>= fun z =>
            (fun w => (w.1, w.2.1)) <$> (simulateQ (implSecLazy pr Msg K H) (k z.1)).run z.2 := by
        simp [map_bind]
      rw [h1, h2]
      refine EvalDistEq.trans (EvalDistEq.bind_left (hstep t stL) _) ?_
      simp only [bind_assoc, bind_map_left]
      exact EvalDistEq.bind_right _ fun z => ih z.1 z.2
  have h0 := hgen oa (s, ∅)
  simpa [κ] using h0

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Eager-vs-lazy equivalence on `stageHyb`**: for every hybrid index `γ`, setup `d`, and
`PK.seed = pk`, running `stageHyb` with `AFEager u` for a uniformly sampled eager stateless secret
table `u ←$ (SlSecAdrs vp → pr.Y)` has the exact same distribution as `stageHyb` with `AF` (lazy
`SecCache`). -/
theorem stageHyb_AFEager_evalDistEq_stageHyb_AF {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg enc qs qh₁ qh₂ L) (β : LeafId → ℕ → ℕ → pr.Y)
    (d : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) (pk : pr.PkSeed) :
    (do let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A u).toFxmssAdversary
          β d pk) =ᵈ
      stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A).toFxmssAdversary β d pk := by
  by_cases hS : d.S.TreeValid vp.params.hsf
  · simp only [stageHyb, hS, not_true_eq_false, ↓reduceIte, slKeygenS, pure_bind]
    set H := Fxmss.Rom.hon pr d.S pk (Fxmss.Rom.digOf pr d.ys) β
    set K : Keys pr := ⟨d.S, pk, default, H.pkSf⟩
    have hE : ∀ u, (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr)
            (AFEager pr Msg enc A u).toFxmssAdversary d.st K)).run
          (St.init pr (BMsg pr Msg) d.cache) =
        (fun z => (z.1, z.2.1)) <$>
          (simulateQ (implSecEager pr Msg K H)
            (stage2SecF pr Msg enc A.toShrincsAdversary d.st K)).run
          (St.init pr (BMsg pr Msg) d.cache, u) := fun u => by
      rw [simulateQ_implSecEager, interpEager_stage2SecF]
    have hL : (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr)
            (AF pr Msg enc A).toFxmssAdversary d.st K)).run
          (St.init pr (BMsg pr Msg) d.cache) =
        (fun z => (z.1, z.2.1)) <$>
          (simulateQ (implSecLazy pr Msg K H)
            (stage2SecF pr Msg enc A.toShrincsAdversary d.st K)).run
          (St.init pr (BMsg pr Msg) d.cache, ∅) := by
      rw [← interpLazy_stage2SecF, simulateQ_map, StateT.run_map, ← simulateQ_implSecLazy,
        Functor.map_map]
    have heq : (($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
          ((simulateQ (implHyb pr (BMsg pr Msg) K H)
            (Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A u).toFxmssAdversary d.st K)).run
            (St.init pr (BMsg pr Msg) d.cache)) >>=
            fun r => pure (some (Transcript.ofRun pr (BMsg pr Msg) K r, H))) =
        ((($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
            (fun z => (z.1, z.2.1)) <$>
              (simulateQ (implSecEager pr Msg K H)
                (stage2SecF pr Msg enc A.toShrincsAdversary d.st K)).run
              (St.init pr (BMsg pr Msg) d.cache, u)) >>=
          fun r => pure (some (Transcript.ofRun pr (BMsg pr Msg) K r, H))) := by
      simp only [hE, bind_assoc]
    rw [heq, hL]
    exact EvalDistEq.bind_left (implSecEager_evalDistEq_implSecLazy pr Msg K H _ _) _
  · simp only [stageHyb, hS, not_false_eq_true, ↓reduceIte]
    exact EvalDistEq.bind_const ($ᵗ (SlSecAdrs vp → pr.Y)) (pure none)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Eager-vs-lazy equivalence on `gameHyb`**: for every hybrid index `γ`, sampling the eager
stateless secrets `u` before `gameHyb γ (AFEager u)` has the exact same distribution as
`gameHyb γ (AF A)`. -/
theorem gameHyb_AFEager_evalDistEq_gameHyb_AF {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg enc qs qh₁ qh₂ L) (γ : ℕ) :
    (do let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A u).toFxmssAdversary) =ᵈ
      gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary := by
  unfold gameHyb
  refine EvalDistEq.trans (EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun pk => ?_
  change (($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
    Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A).toFxmssAdversary >>=
      fun d => stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A u).toFxmssAdversary
        (betaOf pr γ pk d.u) d pk) =ᵈ _
  refine EvalDistEq.trans (EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun d => ?_
  exact stageHyb_AFEager_evalDistEq_stageHyb_AF pr Msg enc A (betaOf pr γ pk d.u) d pk

end EagerVsLazy

end EagerLazy

end ShrincsSecurity.Shrincs

end

