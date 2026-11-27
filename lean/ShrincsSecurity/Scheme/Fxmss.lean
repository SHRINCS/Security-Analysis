module

public import ShrincsSecurity.Scheme.Tree
public import ShrincsSecurity.Scheme.WotsC

/-!
# FXMSS, the stateful component

`SHRINCS-Security-Analysis.pdf`, Section 2.5 ("FXMSS: the stateful component": node computation,
`FXMSS.sign`, `FXMSS.pkFromSig`), Section 3.1 (Lemma 3.1, Steps 1, 4 and 5), Definition 4.16.

FXMSS instantiates the generic tree of `Tree` with WOTS+C public keys at the anchors
(`SF_WOTS_C_PK` compression at the anchor's position) and `H` at the `SF_FXMSS_TREE` address of
every internal node. Key generation, signing and the tree are parametric in the secret chain
starts `sk : LeafId → ℕ → Y` of the WOTS+C instances: the scheme derives them by
`PRF(PK.seed, SK.seed, ·)` at `SF_WOTS_C_PRF` addresses carrying the structure bytes
(`prfSecret`), while the idealized key generation of Definition 4.16 samples them uniformly.

Verification (`pkFromSig`, `verifyMessage`) consumes only the anchor identifier `(z*, i*)`, the
WOTS+C signature and the authentication path; it is independent of the structure.

`pkFromSig_sign` / `verifyMessage_signMessage`: for every valid structure, every non-`⊥` honest
signature at an anchor recovers the root.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.Fxmss

open SLHDSA (Byte)

variable {P : Params} (pr : Primitives P)

/-- The value at an anchor: the WOTS+C public key `WOTS+C.kg(PK.seed, SK.seed, ADRS^w_(z,i)).pk`. -/
def leaf (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y) (id : LeafId) : pr.Y :=
  WotsC.pkGen pr pk id (sk id)

/-- The node hash `H(PK.seed, ADRS^tr_(z,i), N_0 ‖ N_1)` of an internal node. -/
def node (pk : pr.PkSeed) (id : LeafId) (l r : pr.Y) : pr.Y :=
  pr.H pk (SfAdrs.treeAdrs id).toAdrs l r

/-- **`treeNode_structure(z, i, SK.seed, PK.seed)`** (Section 2.5). -/
def treeNode (S : Structure) (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y) : ℕ → ℕ → Option pr.Y :=
  Tree.treeNode P.hsf S (leaf pr pk sk) (node pr pk)

/-- The FXMSS public key `PK.sf = treeNode_structure(hsf, 0)` (Section 2.5, Algorithm 1). -/
def root (S : Structure) (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y) : Option pr.Y :=
  treeNode pr S pk sk P.hsf 0

/-- The secret chain starts of the scheme: `sk_{(z,i), ch} = PRF(PK.seed, SK.seed, ADRS)` at the
`SF_WOTS_C_PRF` address of chain `ch` of the instance at `(z, i)`, carrying the structure bytes
`S.tag` (Section 2.4, Table 3). -/
def prfSecret (pk : pr.PkSeed) (skSeed : pr.SkSeed) (S : Structure) : LeafId → ℕ → pr.Y :=
  WotsC.prfSecret pr pk skSeed S.tag

/-- An FXMSS signature `σ_tree = (σ_WOTS+C, A_1, …, A_δ*)`. -/
structure Sig (pr : Primitives P) where
  /-- The WOTS+C signature. -/
  wots : WotsC.Sig pr
  /-- The authentication path, leaf level first. -/
  auth : List pr.Y

/-- **Signing** `σ_tree ← FXMSS.sign(md, SK.seed, PK.seed, (z*, i*), structure)` (Section 2.5):
`⊥` unless `(hsf − z*, i*) ∈ A`; otherwise the WOTS+C signature of `md` at the anchor (or `⊥` if
grinding fails) and the `δ* = hsf − z*` siblings along the path to the root. -/
def sign (S : Structure) (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y) (md : pr.Digest)
    (id : LeafId) : Option (Sig pr) :=
  if id.height ≤ P.hsf ∧ Node.ofLeafId P.hsf id ∈ S.anchors then
    (WotsC.sign pr pk id (sk id) md).bind fun w =>
      (Tree.authPath P.hsf S (leaf pr pk sk) (node pr pk) id.height id.index
        (P.hsf - id.height)).map fun auth => ⟨w, auth⟩
  else none

/-- **Public-key recovery** `FXMSS.pkFromSig(md, (z*, i*), σ_tree, PK.seed)` (Section 2.5):
validation (`1 ≤ δ* ≤ hsf`, exactly `δ*` path nodes, `i* < 2^{min(64, δ*)}`), anchor recovery by
`WOTS+C.pkFromSig` (`⊥` on an invalid counter), and root recovery by climbing the path. -/
def pkFromSig (pk : pr.PkSeed) (md : pr.Digest) (id : LeafId) (σ : Sig pr) : Option pr.Y :=
  if id.height < P.hsf ∧ σ.auth.length = P.hsf - id.height ∧
      id.index < 2 ^ min 64 (P.hsf - id.height) then
    (WotsC.pkFromSig pr pk id md σ.wots).map fun N =>
      Tree.climb (node pr pk) id.height id.index N σ.auth
  else none

/-! ## Messages: the FXMSS signature scheme of Definition 4.16 -/

/-- Signing of a message `M` at the leaf `id` with randomizer `R`: the digest is
`md = H_msg^sf(R, PK.seed, PK.sf, idx, M)` (Section 2.2; Algorithm 2, lines 10–12). -/
def signMessage (S : Structure) (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y) (pkSf : pr.Y)
    (R : pr.Y) (M : List Byte) (id : LeafId) : Option (Sig pr) :=
  sign pr S pk sk (pr.HmsgSf R pk pkSf id M) id

/-- Verification `FXMSS.Verify(pk, M, (z*, i*), (R, σ_tree))`: recompute the digest and compare
the recovered root with `PK.sf` (Algorithm 3, lines 14–16). -/
def verifyMessage [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSf : pr.Y) (M : List Byte) (id : LeafId)
    (R : pr.Y) (σ : Sig pr) : Bool :=
  match pkFromSig pr pk (pr.HmsgSf R pk pkSf id M) id σ with
  | some r => decide (r = pkSf)
  | none => false

/-! ## Correctness -/

variable {pr}

theorem treeNode_anchor {S : Structure} {pk : pr.PkSeed} {sk : LeafId → ℕ → pr.Y} {id : LeafId}
    (hz : id.height ≤ P.hsf) (h : Node.ofLeafId P.hsf id ∈ S.anchors) :
    treeNode pr S pk sk id.height id.index = some (leaf pr pk sk id) :=
  Tree.treeNode_anchor hz h

theorem root_isSome {S : Structure} (hS : S.TreeValid P.hsf) (pk : pr.PkSeed)
    (sk : LeafId → ℕ → pr.Y) : (root pr S pk sk).isSome :=
  Tree.root_isSome hS

/-- Signing at an anchor of a valid structure fails exactly when grinding fails
(Lemma 3.1 (i): the only failing step is the counter search). -/
theorem sign_eq_none_iff {S : Structure} (hS : S.TreeValid P.hsf) {pk : pr.PkSeed}
    {sk : LeafId → ℕ → pr.Y} {md : pr.Digest} {id : LeafId} (hz : id.height ≤ P.hsf)
    (hA : Node.ofLeafId P.hsf id ∈ S.anchors) :
    sign pr S pk sk md id = none ↔ WotsC.grind pr pk id md = none := by
  have hpath := Tree.authPath_isSome (leaf := leaf pr pk sk) (node := node pr pk) hS
    (P.hsf - id.height) _ (Structure.anchors_subset_nodes hA)
    (by simp [Node.ofLeafId])
  simp only [Node.ofLeafId, Nat.sub_sub_self hz] at hpath
  obtain ⟨auth, hauth⟩ := Option.isSome_iff_exists.1 hpath
  rw [← WotsC.sign_eq_none_iff (sk := sk id)]
  simp only [sign, hz, hA, and_self, ↓reduceIte, hauth, Option.map_some]
  cases WotsC.sign pr pk id (sk id) md <;> simp

/-- **FXMSS correctness** (Lemma 3.1, Steps 1, 3, 4, 5): for every valid structure, every
non-`⊥` signature at a leaf recovers the root `PK.sf`. -/
theorem pkFromSig_sign {S : Structure} (hS : S.TreeValid P.hsf) {pk : pr.PkSeed}
    {sk : LeafId → ℕ → pr.Y} {md : pr.Digest} {id : LeafId} {σ : Sig pr}
    (h : sign pr S pk sk md id = some σ) : pkFromSig pr pk md id σ = root pr S pk sk := by
  unfold sign at h
  split_ifs at h with hid
  obtain ⟨hz, hA⟩ := hid
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, auth, hauth, rfl⟩ := h
  set v := Node.ofLeafId P.hsf id with hv
  have hvmem : v ∈ S.nodes := Structure.anchors_subset_nodes hA
  have hdepth : v.depth = P.hsf - id.height := rfl
  have hpos := hS.anchor_depth_pos hA
  have hlt := hS.idx_lt_two_pow hvmem
  have hlt64 := hS.anchor_idx_lt v hA
  have hzv : P.hsf - v.depth = id.height := by omega
  -- validation passes
  have hval : id.height < P.hsf ∧ auth.length = P.hsf - id.height ∧
      id.index < 2 ^ min 64 (P.hsf - id.height) := by
    refine ⟨by omega, Tree.authPath_length hauth, ?_⟩
    rw [← hdepth]
    rcases le_total 64 v.depth with h64 | h64
    · rw [min_eq_left h64]; exact hlt64
    · rw [min_eq_right h64]; exact hlt
  -- the anchor value and the round trip
  have hN := treeNode_anchor (pk := pk) (sk := sk) hz hA
  have hroot := Tree.root_eq_climb (leaf := leaf pr pk sk) (node := node pr pk) hS hvmem
    (N := leaf pr pk sk id) (as := auth) (by rw [hzv]; exact hN)
    (by rw [hzv]; exact hauth)
  rw [hzv] at hroot
  simp only [pkFromSig, hval, and_self, ↓reduceIte, WotsC.pkFromSig_sign pr hw, Option.map_some]
  exact hroot.symm

/-- **FXMSS correctness for messages**: an honest non-`⊥` signature of `M` at a leaf of a valid
structure verifies against the honest root. -/
theorem verifyMessage_signMessage [DecidableEq pr.Y] {S : Structure} (hS : S.TreeValid P.hsf)
    {pk : pr.PkSeed} {sk : LeafId → ℕ → pr.Y} {pkSf R : pr.Y} {M : List Byte} {id : LeafId}
    {σ : Sig pr} (hroot : root pr S pk sk = some pkSf)
    (h : signMessage pr S pk sk pkSf R M id = some σ) :
    verifyMessage pr pk pkSf M id R σ = true := by
  unfold verifyMessage
  rw [pkFromSig_sign hS h, hroot]
  simp

/-- **Inversion of recovery** (the verifier's path, Claim 4.10): a recovered root comes from a
well-formed signature (`1 ≤ δ* ≤ hsf`, `δ*` path nodes, `i* < 2^{min(64, δ*)}`), a WOTS+C
public key `N` recovered at the anchor identifier, and the climb along the path. -/
theorem pkFromSig_eq_some_iff {pk : pr.PkSeed} {md : pr.Digest} {id : LeafId} {σ : Sig pr}
    {r : pr.Y} :
    pkFromSig pr pk md id σ = some r ↔
      (id.height < P.hsf ∧ σ.auth.length = P.hsf - id.height ∧
        id.index < 2 ^ min 64 (P.hsf - id.height)) ∧
      ∃ N, WotsC.pkFromSig pr pk id md σ.wots = some N ∧
        r = Tree.climb (node pr pk) id.height id.index N σ.auth := by
  unfold pkFromSig
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem verifyMessage_eq_true_iff [DecidableEq pr.Y] {pk : pr.PkSeed} {pkSf R : pr.Y}
    {M : List Byte} {id : LeafId} {σ : Sig pr} :
    verifyMessage pr pk pkSf M id R σ = true ↔
      pkFromSig pr pk (pr.HmsgSf R pk pkSf id M) id σ = some pkSf := by
  unfold verifyMessage
  split <;> simp_all

end ShrincsSecurity.Scheme.Fxmss
