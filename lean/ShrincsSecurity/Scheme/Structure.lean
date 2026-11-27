module

public import ShrincsSecurity.Scheme.Address
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# FXMSS tree structures

`SHRINCS-Security-Analysis.pdf`, Section 2.5 ("Imaginary complete-tree embedding", "Tree
structure", "Valid structures", "Leaf selection", footnote 6), Section 3.1 (proof of Lemma 3.1,
Step 1 and the closing remark), Section 4.7 (Definition 4.16, Remark 4.6, Claim 4.10).

Positions of the imaginary complete binary tree of height `hsf` are `Node`s in **depth
coordinates** `(δ, i)`, `δ = hsf − z` (the paper's coordinates for structures). A `Structure` is
an anchor set `A`, an internal-node set `I`, a leaf-selection map and the structure bytes carried
by `SF_WOTS_C_PRF` addresses.

* `Structure.TreeValid`: the paper's *valid structure*: anchors addressable, and `A ∪ I`, with the
  parent/child relation of the imaginary tree, a full binary tree with root `(0, 0)`, internal
  nodes `I` and leaves `A`.
* `Structure.Valid`: additionally, `leafSelect` maps `{0, …, |A| − 1}` bijectively onto `A` and
  returns `⊥` beyond (footnote 6: the only properties of `leafSelect` the proof uses).

Structural facts for the reductions: `card_anchors` (`|I| = |A| − 1`), `ancestor_mem_internal`
(every proper ancestor of a node is internal), `sibling_mem` (every sibling along a path lies in
`A ∪ I`), `internal_depth_lt` / `depth_le` (all nodes lie in the imaginary tree), `idx_lt_two_pow`,
`anchor_ne_ancestor` (no anchor lies below another anchor), `exists_leafSelect_eq` (every anchor is
selected), and injectivity of leaf identifiers on nodes (`Node.toLeafId_injOn`).

The prescribed shapes UXMSS and BXMSS (`Descriptor.toStructure`) are valid structures
(`Descriptor.valid`) with `L = depth + 1` and `L = 2^depth` anchors.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme

/-! ## Positions of the imaginary tree -/

/-- A position `(δ, i)` of the imaginary complete binary tree, in depth coordinates: `δ` is the
distance from the root, `i` the horizontal index counted from the left. -/
@[ext] structure Node where
  /-- Depth `δ = hsf − z`. -/
  depth : ℕ
  /-- Horizontal index `i`. -/
  idx : ℕ
deriving Repr, DecidableEq

namespace Node

/-- The root `(0, 0)`. -/
def root : Node := ⟨0, 0⟩

/-- The parent `(δ − 1, ⌊i/2⌋)`. -/
def parent (v : Node) : Node := ⟨v.depth - 1, v.idx / 2⟩

/-- The child `(δ + 1, 2i + b)`: left for `b = false`, right for `b = true`. -/
def child (v : Node) (b : Bool) : Node := ⟨v.depth + 1, 2 * v.idx + b.toNat⟩

/-- `i ⊕ 1`, the index of the sibling. -/
def sibIdx (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- The sibling `(δ, i ⊕ 1)`. -/
def sibling (v : Node) : Node := ⟨v.depth, sibIdx v.idx⟩

/-- The ancestor `k` levels up, `(δ − k, ⌊i / 2^k⌋)`. -/
def ancestor (v : Node) (k : ℕ) : Node := ⟨v.depth - k, v.idx / 2 ^ k⟩

/-- The leaf identifier `(z, i) = (hsf − δ, i)` in height coordinates. -/
def toLeafId (hsf : ℕ) (v : Node) : LeafId := ⟨hsf - v.depth, v.idx⟩

/-- The node `(hsf − z, i)` of a height-coordinate position. -/
def ofLeafId (hsf : ℕ) (id : LeafId) : Node := ⟨hsf - id.height, id.index⟩

theorem sibIdx_div_two (i : ℕ) : sibIdx i / 2 = i / 2 := by
  unfold sibIdx; split_ifs <;> omega

@[simp] theorem ancestor_zero (v : Node) : v.ancestor 0 = v := by
  simp [ancestor]

theorem ancestor_succ (v : Node) (k : ℕ) : v.ancestor (k + 1) = (v.ancestor k).parent := by
  simp only [ancestor, parent, Node.mk.injEq]
  refine ⟨by omega, ?_⟩
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

@[simp] theorem ancestor_one (v : Node) : v.ancestor 1 = v.parent := by
  rw [ancestor_succ, ancestor_zero]

@[simp] theorem parent_child (v : Node) (b : Bool) : (v.child b).parent = v := by
  ext
  · simp [child, parent]
  · cases b <;> simp [child, parent]
    omega

/-- Every non-root node is the child of its parent on the side given by its parity. -/
theorem child_parent {v : Node} (hv : 0 < v.depth) : v.parent.child (v.idx % 2 == 1) = v := by
  ext
  · simp only [child, parent]; omega
  · rcases Nat.mod_two_eq_zero_or_one v.idx with h | h <;>
      simp [child, parent, h] <;> omega

/-- The sibling of a non-root node is the other child of its parent. -/
theorem sibling_eq_child_parent {v : Node} (hv : 0 < v.depth) :
    v.sibling = v.parent.child (!(v.idx % 2 == 1)) := by
  ext
  · simp only [sibling, child, parent]; omega
  · rcases Nat.mod_two_eq_zero_or_one v.idx with h | h <;>
      simp [sibling, sibIdx, child, parent, h] <;> omega

theorem child_injective {v w : Node} {b c : Bool} (h : v.child b = w.child c) : v = w ∧ b = c := by
  simp only [child, Node.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  cases b <;> cases c <;> simp only [Bool.toNat_false, Bool.toNat_true] at h2 <;>
    first
    | exact ⟨Node.ext (by omega) (by omega), rfl⟩
    | omega

theorem child_ne_root (v : Node) (b : Bool) : v.child b ≠ root := by
  simp [child, root]

/-- **Distinct positions give distinct leaf identifiers** (within the imaginary tree). -/
theorem toLeafId_injOn {hsf : ℕ} {v w : Node} (hv : v.depth ≤ hsf) (hw : w.depth ≤ hsf)
    (h : v.toLeafId hsf = w.toLeafId hsf) : v = w := by
  simp only [toLeafId, LeafId.mk.injEq] at h
  exact Node.ext (by omega) h.2

theorem ofLeafId_toLeafId {hsf : ℕ} {v : Node} (hv : v.depth ≤ hsf) :
    ofLeafId hsf (v.toLeafId hsf) = v := by
  ext
  · simp only [ofLeafId, toLeafId]; omega
  · rfl

theorem toLeafId_ofLeafId {hsf : ℕ} {id : LeafId} (h : id.height ≤ hsf) :
    (ofLeafId hsf id).toLeafId hsf = id := by
  ext
  · simp only [ofLeafId, toLeafId]; omega
  · rfl

end Node

/-! ## Structures -/

/-- An FXMSS structure (Section 2.5): anchors `A` (positions carrying WOTS+C keys), internal
nodes `I`, the leaf-selection map `leafSelect`, and the structure bytes `tag` written into the
payload of `SF_WOTS_C_PRF` addresses (Table 3). -/
structure Structure where
  /-- The anchor set `A`. -/
  anchors : Finset Node
  /-- The internal-node set `I`. -/
  internal : Finset Node
  /-- `leafSelect_structure(q)`: the anchor of the `q`-th stateful signature, or `⊥`. -/
  leafSelect : ℕ → Option Node
  /-- The payload word `shape ‖ depth ‖ 0²` of `SF_WOTS_C_PRF` addresses. -/
  tag : ℕ

namespace Structure

/-- `A ∪ I`. -/
def nodes (S : Structure) : Finset Node := S.anchors ∪ S.internal

theorem mem_nodes {S : Structure} {v : Node} : v ∈ S.nodes ↔ v ∈ S.anchors ∨ v ∈ S.internal :=
  Finset.mem_union

/-- **Valid structure** (Section 2.5): anchors are addressable (in the imaginary tree of height
`hsf`, with index below `2^64`), and `A ∪ I` is a full binary tree with root `(0, 0)`, internal
nodes `I` and leaves `A`: `A` and `I` are disjoint, the root lies in `I`, every other node of
`A ∪ I` has its parent in `I`, and every node of `I` has both children in `A ∪ I`. -/
structure TreeValid (hsf : ℕ) (S : Structure) : Prop where
  disjoint : Disjoint S.anchors S.internal
  root_mem : Node.root ∈ S.internal
  parent_mem : ∀ v ∈ S.nodes, v ≠ Node.root → 0 < v.depth ∧ v.parent ∈ S.internal
  child_mem : ∀ v ∈ S.internal, ∀ b, v.child b ∈ S.nodes
  anchor_depth_le : ∀ v ∈ S.anchors, v.depth ≤ hsf
  anchor_idx_lt : ∀ v ∈ S.anchors, v.idx < 2 ^ 64

/-- A valid structure with an admissible leaf selection (footnote 6): `leafSelect` maps
`{0, …, |A| − 1}` injectively (hence bijectively) into `A` and returns `⊥` for `q ≥ |A|`. -/
structure Valid (hsf : ℕ) (S : Structure) : Prop extends TreeValid hsf S where
  leafSelect_isSome : ∀ q, (S.leafSelect q).isSome ↔ q < S.anchors.card
  leafSelect_mem : ∀ q v, S.leafSelect q = some v → v ∈ S.anchors
  leafSelect_injective : ∀ q q' v, S.leafSelect q = some v → S.leafSelect q' = some v → q = q'

theorem internal_subset_nodes {S : Structure} {v : Node} (h : v ∈ S.internal) : v ∈ S.nodes :=
  mem_nodes.2 (Or.inr h)

theorem anchors_subset_nodes {S : Structure} {v : Node} (h : v ∈ S.anchors) : v ∈ S.nodes :=
  mem_nodes.2 (Or.inl h)

namespace TreeValid

variable {hsf : ℕ} {S : Structure} (hS : S.TreeValid hsf)
include hS

theorem not_mem_anchors_of_mem_internal {v : Node} (h : v ∈ S.internal) : v ∉ S.anchors :=
  fun ha => Finset.disjoint_left.1 hS.disjoint ha h

theorem root_not_mem_anchors : Node.root ∉ S.anchors :=
  hS.not_mem_anchors_of_mem_internal hS.root_mem

/-- Anchors are never at the root: `δ ≥ 1` (depth-zero structures are disallowed). -/
theorem anchor_depth_pos {v : Node} (h : v ∈ S.anchors) : 0 < v.depth :=
  (hS.parent_mem v (anchors_subset_nodes h)
    (fun hr => hS.root_not_mem_anchors (hr ▸ h))).1

/-- Every node of `A ∪ I` lies in the imaginary tree: `i < 2^δ`. -/
theorem idx_lt_two_pow {v : Node} (h : v ∈ S.nodes) : v.idx < 2 ^ v.depth := by
  induction hd : v.depth generalizing v with
  | zero =>
    by_cases hr : v = Node.root
    · subst hr; simp [Node.root]
    · have := (hS.parent_mem v h hr).1; omega
  | succ d ih =>
    have hr : v ≠ Node.root := by rintro rfl; simp [Node.root] at hd
    obtain ⟨-, hp⟩ := hS.parent_mem v h hr
    have := ih (internal_subset_nodes hp) (by simp [Node.parent, hd])
    simp only [Node.parent] at this
    rw [Nat.pow_succ]
    omega

/-- Ancestors of a node of `A ∪ I` stay in `A ∪ I`, and **every proper ancestor is internal**
(Lemma 3.1, Step 1; Claim 4.10). -/
theorem ancestor_mem {v : Node} (h : v ∈ S.nodes) :
    ∀ k, k ≤ v.depth → v.ancestor k ∈ S.nodes ∧ (1 ≤ k → v.ancestor k ∈ S.internal)
  | 0, _ => by simpa using h
  | k + 1, hk => by
    obtain ⟨hmem, -⟩ := ancestor_mem h k (by omega)
    have hr : v.ancestor k ≠ Node.root := by
      intro hr
      have : (v.ancestor k).depth = 0 := by rw [hr]; rfl
      simp only [Node.ancestor] at this
      omega
    have hp := (hS.parent_mem _ hmem hr).2
    rw [Node.ancestor_succ]
    exact ⟨internal_subset_nodes hp, fun _ => hp⟩

theorem ancestor_mem_internal {v : Node} (h : v ∈ S.nodes) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ v.depth) : v.ancestor k ∈ S.internal :=
  (hS.ancestor_mem h k hk).2 hk1

/-- **No anchor lies below another anchor**: proper ancestors of a node are not anchors. -/
theorem anchor_ne_ancestor {v : Node} (h : v ∈ S.nodes) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ v.depth) : v.ancestor k ∉ S.anchors :=
  hS.not_mem_anchors_of_mem_internal (hS.ancestor_mem_internal h hk1 hk)

/-- **Siblings along a path lie in `A ∪ I`** (Lemma 3.1, Step 1): the sibling of a non-root node
of `A ∪ I` is the other child of its internal parent. -/
theorem sibling_mem {v : Node} (h : v ∈ S.nodes) (hr : v ≠ Node.root) : v.sibling ∈ S.nodes := by
  obtain ⟨hd, hp⟩ := hS.parent_mem v h hr
  rw [Node.sibling_eq_child_parent hd]
  exact hS.child_mem _ hp _

/-- Every internal node lies strictly above the leaf level of the imaginary tree. -/
theorem internal_depth_lt {v : Node} (hv : v ∈ S.internal) : v.depth < hsf := by
  set D := S.nodes.sup Node.depth
  suffices H : ∀ n, ∀ v ∈ S.internal, D - v.depth = n → v.depth < hsf from H _ v hv rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hn
    have hc := hS.child_mem v hv false
    rcases mem_nodes.1 hc with hA | hI
    · have := hS.anchor_depth_le _ hA
      simp only [Node.child] at this
      omega
    · have hcD : (v.child false).depth ≤ D := Finset.le_sup hc
      simp only [Node.child] at hcD
      have := ih (D - (v.depth + 1)) (by omega) _ hI (by simp [Node.child])
      simp only [Node.child] at this
      omega

/-- Every node of `A ∪ I` lies in the imaginary tree of height `hsf`. -/
theorem depth_le {v : Node} (h : v ∈ S.nodes) : v.depth ≤ hsf := by
  rcases mem_nodes.1 h with hA | hI
  · exact hS.anchor_depth_le _ hA
  · exact (hS.internal_depth_lt hI).le

/-- The children map `I × {0,1} → (A ∪ I) \ {root}` is a bijection. -/
theorem image_child_eq :
    (S.internal ×ˢ (Finset.univ : Finset Bool)).image (fun p => p.1.child p.2) =
      S.nodes.erase Node.root := by
  ext w
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true, Prod.exists,
    Finset.mem_erase]
  constructor
  · rintro ⟨v, b, hv, rfl⟩
    exact ⟨Node.child_ne_root v b, hS.child_mem v hv b⟩
  · rintro ⟨hr, hw⟩
    obtain ⟨hd, hp⟩ := hS.parent_mem w hw hr
    exact ⟨w.parent, _, hp, Node.child_parent hd⟩

/-- **`|I| = |A| − 1`** for valid structures (a full binary tree has one more leaf than internal
nodes). -/
theorem card_anchors : S.anchors.card = S.internal.card + 1 := by
  have hinj : Set.InjOn (fun p : Node × Bool => p.1.child p.2)
      ↑(S.internal ×ˢ (Finset.univ : Finset Bool)) := by
    rintro ⟨v, b⟩ - ⟨w, c⟩ - h
    obtain ⟨rfl, rfl⟩ := Node.child_injective h
    rfl
  have h1 := Finset.card_image_of_injOn hinj
  rw [hS.image_child_eq, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Finset.card_erase_of_mem (internal_subset_nodes hS.root_mem), nodes,
    Finset.card_union_of_disjoint hS.disjoint] at h1
  have := Finset.card_pos.2 ⟨_, hS.root_mem⟩
  omega

theorem card_internal : S.internal.card = S.anchors.card - 1 := by
  rw [hS.card_anchors]; rfl

end TreeValid

namespace Valid

variable {hsf : ℕ} {S : Structure} (hS : S.Valid hsf)
include hS

/-- Every anchor is selected by some counter `q < |A|` (`leafSelect` is onto `A`). -/
theorem exists_leafSelect_eq {v : Node} (hv : v ∈ S.anchors) :
    ∃ q < S.anchors.card, S.leafSelect q = some v := by
  have key := Finset.surj_on_of_inj_on_of_card_le
    (s := Finset.range S.anchors.card) (t := S.anchors)
    (fun q hq => (S.leafSelect q).get ((hS.leafSelect_isSome q).2 (Finset.mem_range.1 hq)))
    (fun q hq => hS.leafSelect_mem q _ (Option.some_get _).symm)
    (fun q q' hq hq' h => hS.leafSelect_injective q q' _ (Option.some_get _).symm
      (by rw [h]; exact (Option.some_get _).symm))
    (by simp)
  obtain ⟨q, hq, hqv⟩ := key v hv
  exact ⟨q, Finset.mem_range.1 hq, by rw [hqv, Option.some_get]⟩

theorem leafSelect_eq_none_iff {q : ℕ} : S.leafSelect q = none ↔ S.anchors.card ≤ q := by
  rw [← Option.not_isSome_iff_eq_none, hS.leafSelect_isSome]
  omega

end Valid

end Structure

/-! ## The prescribed shapes UXMSS and BXMSS -/

/-- The shape byte: `SHAPE_UNBALANCED = 0` (UXMSS) or `SHAPE_BALANCED = 1` (BXMSS). -/
inductive Shape where
  | unbalanced
  | balanced
deriving Repr, DecidableEq

/-- The shape byte value. -/
def Shape.toCode : Shape → ℕ
  | .unbalanced => 0
  | .balanced => 1

/-- The two-byte structure `(shape, depth)` of a prescribed shape (Section 2.5). -/
structure Descriptor where
  shape : Shape
  depth : ℕ
deriving Repr, DecidableEq

/-- The payload word `shape ‖ depth ‖ 0²` (big-endian) of `SF_WOTS_C_PRF` addresses (Table 3). -/
def structureTag (shape : Shape) (depth : ℕ) : ℕ := shape.toCode * 2 ^ 24 + depth * 2 ^ 16

/-- UXMSS anchors `A = {(δ, 1) : 1 ≤ δ ≤ depth} ∪ {(depth, 0)}`. -/
def uxmssAnchors (D : ℕ) : Finset Node :=
  insert ⟨D, 0⟩ ((Finset.Icc 1 D).image fun δ => ⟨δ, 1⟩)

/-- UXMSS internal nodes `I = {(δ, 0) : 0 ≤ δ < depth}`. -/
def uxmssInternal (D : ℕ) : Finset Node := (Finset.range D).image fun δ => ⟨δ, 0⟩

/-- UXMSS leaf selection: `q < depth ↦ (hsf − 1 − q, 1)`, `q = depth ≥ 1 ↦ (hsf − depth, 0)`,
in depth coordinates `(q + 1, 1)` and `(depth, 0)`. -/
def uxmssLeafSelect (D q : ℕ) : Option Node :=
  if q < D then some ⟨q + 1, 1⟩ else if q = D ∧ 1 ≤ D then some ⟨D, 0⟩ else none

/-- BXMSS anchors `A = {(depth, i) : 0 ≤ i < 2^depth}`. -/
def bxmssAnchors (D : ℕ) : Finset Node := (Finset.range (2 ^ D)).image fun i => ⟨D, i⟩

/-- BXMSS internal nodes `I = {(δ, i) : 0 ≤ δ < depth, 0 ≤ i < 2^δ}`. -/
def bxmssInternal (D : ℕ) : Finset Node :=
  (Finset.range D).biUnion fun δ => (Finset.range (2 ^ δ)).image fun i => ⟨δ, i⟩

/-- BXMSS leaf selection: `q < 2^depth ↦ (hsf − depth, q)`, for `depth ≥ 1`. -/
def bxmssLeafSelect (D q : ℕ) : Option Node :=
  if 1 ≤ D ∧ q < 2 ^ D then some ⟨D, q⟩ else none

theorem mem_uxmssAnchors {D : ℕ} {v : Node} :
    v ∈ uxmssAnchors D ↔ (v.depth = D ∧ v.idx = 0) ∨ (1 ≤ v.depth ∧ v.depth ≤ D ∧ v.idx = 1) := by
  simp only [uxmssAnchors, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc, Node.ext_iff]
  constructor
  · rintro (h | ⟨δ, hδ, h1, h2⟩)
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨by omega, by omega, h2.symm⟩
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v.depth, ⟨h1, h2⟩, rfl, h3.symm⟩

theorem mem_uxmssInternal {D : ℕ} {v : Node} : v ∈ uxmssInternal D ↔ v.depth < D ∧ v.idx = 0 := by
  simp only [uxmssInternal, Finset.mem_image, Finset.mem_range, Node.ext_iff]
  constructor
  · rintro ⟨δ, hδ, h1, h2⟩; exact ⟨h1 ▸ hδ, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨v.depth, h1, rfl, h2.symm⟩

theorem mem_bxmssAnchors {D : ℕ} {v : Node} : v ∈ bxmssAnchors D ↔ v.depth = D ∧ v.idx < 2 ^ D := by
  simp only [bxmssAnchors, Finset.mem_image, Finset.mem_range, Node.ext_iff]
  constructor
  · rintro ⟨i, hi, h1, h2⟩; exact ⟨h1.symm, h2 ▸ hi⟩
  · rintro ⟨h1, h2⟩; exact ⟨v.idx, h2, h1.symm, rfl⟩

theorem mem_bxmssInternal {D : ℕ} {v : Node} :
    v ∈ bxmssInternal D ↔ v.depth < D ∧ v.idx < 2 ^ v.depth := by
  simp only [bxmssInternal, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Node.ext_iff]
  constructor
  · rintro ⟨δ, hδ, i, hi, h1, h2⟩; subst h1 h2; exact ⟨hδ, hi⟩
  · rintro ⟨h1, h2⟩; exact ⟨v.depth, h1, v.idx, h2, rfl, rfl⟩

theorem card_uxmssAnchors (D : ℕ) : (uxmssAnchors D).card = D + 1 := by
  unfold uxmssAnchors
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective, Nat.card_Icc]
  · omega
  · intro a b h; simpa using h
  · simp

theorem card_bxmssAnchors (D : ℕ) : (bxmssAnchors D).card = 2 ^ D := by
  unfold bxmssAnchors
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro a b h; simpa using h

/-- The structure denoted by a two-byte descriptor `(shape, depth)`. -/
def Descriptor.toStructure : Descriptor → Structure
  | ⟨.unbalanced, D⟩ => ⟨uxmssAnchors D, uxmssInternal D, uxmssLeafSelect D,
      structureTag .unbalanced D⟩
  | ⟨.balanced, D⟩ => ⟨bxmssAnchors D, bxmssInternal D, bxmssLeafSelect D,
      structureTag .balanced D⟩

/-- Admissible descriptors (Section 2.5): `1 ≤ depth ≤ hsf` for UXMSS; `1 ≤ depth ≤ 64` (the
node-index bound) and `depth ≤ hsf` for BXMSS. -/
def Descriptor.Admissible (hsf : ℕ) : Descriptor → Prop
  | ⟨.unbalanced, D⟩ => 1 ≤ D ∧ D ≤ hsf
  | ⟨.balanced, D⟩ => 1 ≤ D ∧ D ≤ 64 ∧ D ≤ hsf

/-- The number of anchors `L`: `depth + 1` for UXMSS, `2^depth` for BXMSS (Lemma 3.1). -/
theorem Descriptor.card_anchors (desc : Descriptor) :
    desc.toStructure.anchors.card =
      match desc.shape with
      | .unbalanced => desc.depth + 1
      | .balanced => 2 ^ desc.depth := by
  rcases desc with ⟨_ | _, D⟩
  · exact card_uxmssAnchors D
  · exact card_bxmssAnchors D

/-- **UXMSS is a valid structure.** -/
theorem uxmss_valid {hsf D : ℕ} (hD : 1 ≤ D) (hDh : D ≤ hsf) :
    (Descriptor.toStructure ⟨.unbalanced, D⟩).Valid hsf where
  disjoint := by
    refine Finset.disjoint_left.2 fun v ha hi => ?_
    replace ha := mem_uxmssAnchors.1 ha
    replace hi := mem_uxmssInternal.1 hi
    omega
  root_mem := mem_uxmssInternal.2 ⟨by simp [Node.root]; omega, rfl⟩
  parent_mem := by
    intro v hv hr
    have hr' : ¬ (v.depth = 0 ∧ v.idx = 0) := fun h => hr (Node.ext h.1 h.2)
    rcases Structure.mem_nodes.1 hv with ha | hi
    · replace ha := mem_uxmssAnchors.1 ha
      refine ⟨by omega, mem_uxmssInternal.2 ?_⟩
      simp only [Node.parent]; omega
    · replace hi := mem_uxmssInternal.1 hi
      refine ⟨by omega, mem_uxmssInternal.2 ?_⟩
      simp only [Node.parent]; omega
  child_mem := by
    intro v hv b
    replace hv := mem_uxmssInternal.1 hv
    refine Structure.mem_nodes.2 ?_
    cases b
    · by_cases h : v.depth + 1 < D
      · exact Or.inr (mem_uxmssInternal.2 (by simp [Node.child]; omega))
      · exact Or.inl (mem_uxmssAnchors.2 (Or.inl (by simp [Node.child]; omega)))
    · exact Or.inl (mem_uxmssAnchors.2 (Or.inr (by simp [Node.child]; omega)))
  anchor_depth_le := by
    intro v hv
    replace hv := mem_uxmssAnchors.1 hv
    omega
  anchor_idx_lt := by
    intro v hv
    replace hv := mem_uxmssAnchors.1 hv
    have : (1 : ℕ) < 2 ^ 64 := by norm_num
    omega
  leafSelect_isSome := by
    intro q
    simp only [Descriptor.toStructure, card_uxmssAnchors, uxmssLeafSelect]
    split_ifs <;> simp <;> omega
  leafSelect_mem := by
    intro q v h
    simp only [Descriptor.toStructure, uxmssLeafSelect] at h ⊢
    refine mem_uxmssAnchors.2 ?_
    split_ifs at h with h1 h2 <;> simp only [Option.some.injEq] at h <;> subst h
    · exact Or.inr ⟨by simp, by simp; omega, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  leafSelect_injective := by
    intro q q' v h h'
    simp only [Descriptor.toStructure, uxmssLeafSelect] at h h'
    split_ifs at h h' <;> simp only [Option.some.injEq] at h h' <;>
      subst h <;> simp only [Node.mk.injEq] at h' <;> omega

/-- **BXMSS is a valid structure.** -/
theorem bxmss_valid {hsf D : ℕ} (hD : 1 ≤ D) (hD64 : D ≤ 64) (hDh : D ≤ hsf) :
    (Descriptor.toStructure ⟨.balanced, D⟩).Valid hsf where
  disjoint := by
    refine Finset.disjoint_left.2 fun v ha hi => ?_
    replace ha := mem_bxmssAnchors.1 ha
    replace hi := mem_bxmssInternal.1 hi
    omega
  root_mem := mem_bxmssInternal.2 ⟨by simp [Node.root]; omega, by simp [Node.root]⟩
  parent_mem := by
    intro v hv hr
    have hr' : ¬ (v.depth = 0 ∧ v.idx = 0) := fun h => hr (Node.ext h.1 h.2)
    have key : ∀ δ i : ℕ, i < 2 ^ δ → ¬ (δ = 0 ∧ i = 0) → 0 < δ ∧ i / 2 < 2 ^ (δ - 1) := by
      intro δ i hi hne
      obtain _ | δ := δ
      · simp at hi; omega
      · rw [Nat.pow_succ] at hi
        simp only [Nat.add_sub_cancel]
        omega
    rcases Structure.mem_nodes.1 hv with ha | hi
    · replace ha := mem_bxmssAnchors.1 ha
      obtain ⟨h1, h2⟩ := key v.depth v.idx (ha.1 ▸ ha.2) hr'
      exact ⟨h1, mem_bxmssInternal.2 ⟨by simp only [Node.parent]; omega, h2⟩⟩
    · replace hi := mem_bxmssInternal.1 hi
      obtain ⟨h1, h2⟩ := key v.depth v.idx hi.2 hr'
      exact ⟨h1, mem_bxmssInternal.2 ⟨by simp only [Node.parent]; omega, h2⟩⟩
  child_mem := by
    intro v hv b
    replace hv := mem_bxmssInternal.1 hv
    have hlt : 2 * v.idx + b.toNat < 2 ^ (v.depth + 1) := by
      rw [Nat.pow_succ]
      have := Bool.toNat_le b
      omega
    refine Structure.mem_nodes.2 ?_
    by_cases h : v.depth + 1 < D
    · exact Or.inr (mem_bxmssInternal.2 ⟨by simpa [Node.child] using h, hlt⟩)
    · have hD' : v.depth + 1 = D := by omega
      exact Or.inl (mem_bxmssAnchors.2 ⟨hD', hD' ▸ hlt⟩)
  anchor_depth_le := by
    intro v hv
    replace hv := mem_bxmssAnchors.1 hv
    omega
  anchor_idx_lt := by
    intro v hv
    replace hv := mem_bxmssAnchors.1 hv
    exact lt_of_lt_of_le hv.2 (Nat.pow_le_pow_right (by norm_num) hD64)
  leafSelect_isSome := by
    intro q
    simp only [Descriptor.toStructure, card_bxmssAnchors, bxmssLeafSelect]
    split_ifs <;> simp <;> omega
  leafSelect_mem := by
    intro q v h
    simp only [Descriptor.toStructure, bxmssLeafSelect] at h ⊢
    split_ifs at h with h1
    simp only [Option.some.injEq] at h
    subst h
    exact mem_bxmssAnchors.2 ⟨rfl, h1.2⟩
  leafSelect_injective := by
    intro q q' v h h'
    simp only [Descriptor.toStructure, bxmssLeafSelect] at h h'
    split_ifs at h h'
    simp only [Option.some.injEq] at h h'
    subst h
    simp only [Node.mk.injEq] at h'
    omega

/-- **The prescribed shapes are valid structures**: every admissible descriptor denotes a
valid structure. -/
theorem Descriptor.valid {hsf : ℕ} {desc : Descriptor} (h : desc.Admissible hsf) :
    desc.toStructure.Valid hsf := by
  rcases desc with ⟨_ | _, D⟩
  · exact uxmss_valid h.1 h.2
  · exact bxmss_valid h.1 h.2.1 h.2.2

end ShrincsSecurity.Scheme
