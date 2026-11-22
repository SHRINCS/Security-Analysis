module

public import ShrincsSecurity.Scheme.Structure

/-!
# Hash trees over a structure in the imaginary tree

`SHRINCS-Security-Analysis.pdf`, Section 2.5 ("Node computation", FXMSS signing step 2 and
`FXMSS.pkFromSig` step 3), Section 3.1 (proof of Lemma 3.1, Step 4: the Merkle round trip).

This file is the combinatorial core of FXMSS, generic in the leaf values `leaf : LeafId → Y`
(the WOTS+C public keys of the anchors) and in the node hash `node : LeafId → Y → Y → Y` (the
tweakable hash `H` at the `SF_FXMSS_TREE` address of the parent). All positions are in height
coordinates `(z, i)`; a position belongs to the structure when its depth-coordinate node
`(hsf − z, i)` does.

* `treeNode z i` is `treeNode_structure(z, i)`: the leaf value at an anchor, the hash of the two
  children at an internal node, `⊥` elsewhere.
* `authPath z i s` collects the `s` siblings `A_k = treeNode(z + k − 1, ⌊i/2^{k−1}⌋ ⊕ 1)`.
* `climb z i N auth` is the verifier's root recovery from position `(z, i)`.

`treeNode_climb` is Lemma 3.1, Step 4; `root_eq_climb` specialises it to a full path from a node
of a valid structure to the root.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.Tree

variable {Y : Type} (hsf : ℕ) (S : Structure) (leaf : LeafId → Y) (node : LeafId → Y → Y → Y)

/-- **`treeNode_structure(z, i)`** (Section 2.5): the WOTS+C public key at an anchor, the node
hash of the two children at an internal node, and `⊥` at positions outside the structure. -/
def treeNode : ℕ → ℕ → Option Y
  | 0, i => if (⟨hsf, i⟩ : Node) ∈ S.anchors then some (leaf ⟨0, i⟩) else none
  | z + 1, i =>
    if z + 1 ≤ hsf ∧ (⟨hsf - (z + 1), i⟩ : Node) ∈ S.anchors then some (leaf ⟨z + 1, i⟩)
    else if z + 1 ≤ hsf ∧ (⟨hsf - (z + 1), i⟩ : Node) ∈ S.internal then
      Option.map₂ (node ⟨z + 1, i⟩) (treeNode z (2 * i)) (treeNode z (2 * i + 1))
    else none

/-- The authentication path of `s` siblings, starting at position `(z, i)` (FXMSS signing,
step 2): `A_1 = treeNode(z, i ⊕ 1)`, then continue from the parent `(z + 1, ⌊i/2⌋)`. -/
def authPath : ℕ → ℕ → ℕ → Option (List Y)
  | _, _, 0 => some []
  | z, i, s + 1 =>
    (treeNode hsf S leaf node z (Node.sibIdx i)).bind fun a =>
      (authPath (z + 1) (i / 2) s).map (a :: ·)

/-- **Root recovery** (`FXMSS.pkFromSig`, step 3): combine the current value at `(z, i)` with
the next sibling under the node hash of the parent `(z + 1, ⌊i/2⌋)`, as left child if `i` is even
and as right child otherwise. -/
def climb : ℕ → ℕ → Y → List Y → Y
  | _, _, N, [] => N
  | z, i, N, a :: as =>
    climb (z + 1) (i / 2)
      (if i % 2 = 0 then node ⟨z + 1, i / 2⟩ N a else node ⟨z + 1, i / 2⟩ a N) as

@[simp] theorem climb_nil (z i : ℕ) (N : Y) : climb node z i N [] = N := rfl

theorem climb_cons (z i : ℕ) (N a : Y) (as : List Y) :
    climb node z i N (a :: as) =
      climb node (z + 1) (i / 2)
        (if i % 2 = 0 then node ⟨z + 1, i / 2⟩ N a else node ⟨z + 1, i / 2⟩ a N) as := rfl

variable {hsf S leaf node}

theorem treeNode_anchor {z i : ℕ} (hz : z ≤ hsf) (h : (⟨hsf - z, i⟩ : Node) ∈ S.anchors) :
    treeNode hsf S leaf node z i = some (leaf ⟨z, i⟩) := by
  cases z with
  | zero =>
    simp only [Nat.sub_zero] at h
    simp [treeNode, h]
  | succ z => simp [treeNode, hz, h]

theorem treeNode_internal {z i : ℕ} (hz : z + 1 ≤ hsf)
    (hI : (⟨hsf - (z + 1), i⟩ : Node) ∈ S.internal) (hA : (⟨hsf - (z + 1), i⟩ : Node) ∉ S.anchors) :
    treeNode hsf S leaf node (z + 1) i =
      Option.map₂ (node ⟨z + 1, i⟩) (treeNode hsf S leaf node z (2 * i))
        (treeNode hsf S leaf node z (2 * i + 1)) := by
  simp [treeNode, hz, hI, hA]

theorem authPath_length : ∀ {z i s : ℕ} {as : List Y},
    authPath hsf S leaf node z i s = some as → as.length = s
  | _, _, 0, _, h => by simp only [authPath, Option.some.injEq] at h; subst h; rfl
  | z, i, s + 1, as, h => by
    simp only [authPath, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, as', has', rfl⟩ := h
    simp [authPath_length has']

private theorem div_two_div_pow (i k : ℕ) : i / 2 / 2 ^ k = i / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- **Merkle round trip** (Lemma 3.1, Step 4): if the value at `(z, i)` is `N`, the honest
authentication path of `s` siblings is `as`, and the `s` ancestors of `(z, i)` are internal nodes
of a valid structure, then climbing from `N` along `as` yields the value at the `s`-th ancestor
`(z + s, ⌊i / 2^s⌋)`. -/
theorem treeNode_climb (hS : S.TreeValid hsf) :
    ∀ (s z i : ℕ) (N : Y) (as : List Y),
      treeNode hsf S leaf node z i = some N → authPath hsf S leaf node z i s = some as →
      (∀ k, 1 ≤ k → k ≤ s → z + k ≤ hsf ∧ (⟨hsf - (z + k), i / 2 ^ k⟩ : Node) ∈ S.internal) →
      treeNode hsf S leaf node (z + s) (i / 2 ^ s) = some (climb node z i N as)
  | 0, z, i, N, as, hN, has, _ => by
    simp only [authPath, Option.some.injEq] at has
    subst has
    simpa using hN
  | s + 1, z, i, N, as, hN, has, hanc => by
    simp only [authPath, Option.bind_eq_some_iff, Option.map_eq_some_iff] at has
    obtain ⟨a, ha, as', has', rfl⟩ := has
    obtain ⟨hz, hI⟩ := hanc 1 le_rfl (by omega)
    simp only [pow_one] at hI
    have hA := hS.not_mem_anchors_of_mem_internal hI
    have hpar : treeNode hsf S leaf node (z + 1) (i / 2) =
        some (if i % 2 = 0 then node ⟨z + 1, i / 2⟩ N a else node ⟨z + 1, i / 2⟩ a N) := by
      rw [treeNode_internal hz hI hA]
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi
      · have h1 : 2 * (i / 2) = i := by omega
        have h2 : 2 * (i / 2) + 1 = Node.sibIdx i := by simp [Node.sibIdx, hi]; omega
        rw [h2, h1, hN, ha]
        simp [hi]
      · have h1 : 2 * (i / 2) = Node.sibIdx i := by simp [Node.sibIdx, hi]; omega
        have h2 : 2 * (i / 2) + 1 = i := by omega
        rw [h2, h1, hN, ha]
        simp [hi]
    have ih := treeNode_climb hS s (z + 1) (i / 2) _ as' hpar has' fun k hk1 hk => by
      obtain ⟨h1, h2⟩ := hanc (k + 1) (by omega) (by omega)
      refine ⟨by omega, ?_⟩
      rw [div_two_div_pow]
      convert h2 using 3
      omega
    rw [div_two_div_pow, show z + 1 + s = z + (s + 1) by omega] at ih
    rw [ih, climb_cons]

/-- Every node of a valid structure has a value (`treeNode` is not `⊥` on `A ∪ I`). -/
theorem treeNode_isSome (hS : S.TreeValid hsf) :
    ∀ (h : ℕ) (v : Node), v ∈ S.nodes → v.depth + h = hsf →
      (treeNode hsf S leaf node h v.idx).isSome
  | 0, v, hv, hd => by
    rcases Structure.mem_nodes.1 hv with hA | hI
    · have : (⟨hsf - 0, v.idx⟩ : Node) = v := Node.ext (by simp; omega) rfl
      rw [treeNode_anchor (Nat.zero_le _) (this ▸ hA)]
      rfl
    · have := hS.internal_depth_lt hI; omega
  | h + 1, v, hv, hd => by
    have hv' : (⟨hsf - (h + 1), v.idx⟩ : Node) = v := Node.ext (by simp; omega) rfl
    by_cases hA : v ∈ S.anchors
    · rw [treeNode_anchor (by omega) (hv' ▸ hA)]
      rfl
    · have hI : v ∈ S.internal := (Structure.mem_nodes.1 hv).resolve_left hA
      rw [treeNode_internal (by omega) (hv' ▸ hI) (hv' ▸ hA)]
      have h0 := treeNode_isSome hS h (v.child false) (hS.child_mem v hI false)
        (by simp [Node.child]; omega)
      have h1 := treeNode_isSome hS h (v.child true) (hS.child_mem v hI true)
        (by simp [Node.child]; omega)
      simp only [Node.child, Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h0 h1
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h0
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h1
      rw [hl, hr]
      rfl

/-- The value of a node of a valid structure, in depth coordinates, is not `⊥`. -/
theorem treeNode_isSome_of_mem (hS : S.TreeValid hsf) {v : Node} (hv : v ∈ S.nodes) :
    (treeNode hsf S leaf node (hsf - v.depth) v.idx).isSome :=
  treeNode_isSome hS _ v hv (by have := hS.depth_le hv; omega)

/-- The honest authentication path of a node of a valid structure towards an ancestor is never
`⊥`: every sibling along the path lies in `A ∪ I` (Lemma 3.1, Step 1). -/
theorem authPath_isSome (hS : S.TreeValid hsf) :
    ∀ (s : ℕ) (v : Node), v ∈ S.nodes → s ≤ v.depth →
      (authPath hsf S leaf node (hsf - v.depth) v.idx s).isSome
  | 0, _, _, _ => rfl
  | s + 1, v, hv, hs => by
    have hr : v ≠ Node.root := by rintro rfl; simp [Node.root] at hs
    obtain ⟨hd, hp⟩ := hS.parent_mem v hv hr
    have hdle := hS.depth_le hv
    have hsib := treeNode_isSome_of_mem (leaf := leaf) (node := node) hS (hS.sibling_mem hv hr)
    simp only [Node.sibling] at hsib
    have ih := authPath_isSome hS s v.parent (Structure.internal_subset_nodes hp)
      (by simp [Node.parent]; omega)
    simp only [Node.parent] at ih
    rw [show hsf - (v.depth - 1) = hsf - v.depth + 1 by omega] at ih
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsib
    obtain ⟨as, has⟩ := Option.isSome_iff_exists.1 ih
    simp [authPath, ha, has]

/-- The root recovered from a node `v` of a valid structure by climbing its honest
authentication path of length `δ = depth v` is the root value `treeNode(hsf, 0)` (Lemma 3.1,
Step 5): signer and verifier traverse the same positions, and `⌊i / 2^δ⌋ = 0`. -/
theorem root_eq_climb (hS : S.TreeValid hsf) {v : Node} (hv : v ∈ S.nodes) {N : Y}
    {as : List Y} (hN : treeNode hsf S leaf node (hsf - v.depth) v.idx = some N)
    (has : authPath hsf S leaf node (hsf - v.depth) v.idx v.depth = some as) :
    treeNode hsf S leaf node hsf 0 = some (climb node (hsf - v.depth) v.idx N as) := by
  have hdle := hS.depth_le hv
  have h := treeNode_climb hS v.depth (hsf - v.depth) v.idx N as hN has fun k hk1 hk => by
    refine ⟨by omega, ?_⟩
    have := hS.ancestor_mem_internal hv hk1 hk
    simp only [Node.ancestor] at this
    convert this using 2
    omega
  rwa [Nat.sub_add_cancel hdle, Nat.div_eq_of_lt (hS.idx_lt_two_pow hv)] at h

/-- The root of a valid structure has a value. -/
theorem root_isSome (hS : S.TreeValid hsf) : (treeNode hsf S leaf node hsf 0).isSome := by
  simpa [Node.root] using treeNode_isSome_of_mem (leaf := leaf) (node := node) hS
    (Structure.internal_subset_nodes hS.root_mem)

end ShrincsSecurity.Scheme.Tree
