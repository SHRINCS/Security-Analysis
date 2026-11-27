module

public import ShrincsSecurity.Scheme.Tree

/-!
# The verifier's walk up the tree

`SHRINCS-Security-Analysis.pdf`, Section 4.7, proof of **Claim 4.10** (the walk from the forged
anchor `v₀ = (z*, i*)` to the root, the least index `t*` entering `A ∪ I`, and the least index
`s ≥ t*` at which the recomputed value agrees with the honest one).

Generic in the leaf values `leaf : LeafId → Y` and the node hash `node : LeafId → Y → Y → Y` of
`Scheme.Tree`. The paper's two minimisations are replaced by one induction from the root
downwards (`climb_walk`): if the climb from `(z, i)` along `as` ends at a position whose honest
value it reproduces, then walking down the path, at the first position where the recomputed
value stops agreeing with the honest one we find

* an internal node whose honest children pair differs from the recomputed pair under the same
  node hash (the event of F.8, case `s > t*`), or
* an anchor reached by a node hash from below whose output is the honest anchor value (the event
  of F.9 with a tree-node hash in place of a public-key compression, case `s = t* > 0`),

and otherwise the recomputed value at `(z, i)` itself is honest (case `s = t* = 0`). No validity
of the structure is needed: `treeNode` is `⊥` outside `A ∪ I`, so agreement with an honest value
certifies membership (`treeNode_eq_some_cases`).
-/

@[expose] public section

namespace ShrincsSecurity.Fxmss

open Scheme

variable {Y : Type} {hsf : ℕ} {S : Structure} {leaf : LeafId → Y} {node : LeafId → Y → Y → Y}

/-- Inversion of `treeNode`: an honest value is either the leaf value at an anchor or the node
hash of the two (honest) children at an internal node. -/
theorem treeNode_eq_some_cases {z i : ℕ} {x : Y}
    (h : Tree.treeNode hsf S leaf node z i = some x) :
    (z ≤ hsf ∧ Node.ofLeafId hsf ⟨z, i⟩ ∈ S.anchors ∧ x = leaf ⟨z, i⟩) ∨
    (∃ z', z = z' + 1 ∧ z ≤ hsf ∧ Node.ofLeafId hsf ⟨z, i⟩ ∈ S.internal ∧
      ∃ l r, Tree.treeNode hsf S leaf node z' (2 * i) = some l ∧
        Tree.treeNode hsf S leaf node z' (2 * i + 1) = some r ∧ x = node ⟨z, i⟩ l r) := by
  cases z with
  | zero =>
    simp only [Tree.treeNode] at h
    split_ifs at h with hA
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨Nat.zero_le _, by simpa [Node.ofLeafId] using hA, h.symm⟩
  | succ z =>
    simp only [Tree.treeNode] at h
    split_ifs at h with hA hI
    · simp only [Option.some.injEq] at h
      exact Or.inl ⟨hA.1, hA.2, h.symm⟩
    · obtain ⟨l, r, hl, hr, hx⟩ := Option.map₂_eq_some_iff.1 h
      exact Or.inr ⟨z, rfl, hI.1, hI.2, l, r, hl, hr, hx.symm⟩

/-- **The walk of Claim 4.10.** If climbing from `(z, i)` with value `N` along `as` reproduces
the honest value at the top position `(z + |as|, ⌊i / 2^|as|⌋)`, then one of:

1. an anchor `id` of the structure whose honest value is a node hash `node id l r` (the verifier
   evaluates the tree-node hash where the signer compresses a WOTS+C key, case `s = t* > 0`);
2. an internal node `id` whose honest children `(l, r)` and some different pair `(l', r')` have
   the same node hash (case `s > t*`);
3. the value `N` at `(z, i)` is the honest one (case `s = t* = 0`). -/
theorem climb_walk : ∀ (as : List Y) (z i : ℕ) (N : Y),
    Tree.treeNode hsf S leaf node (z + as.length) (i / 2 ^ as.length) =
      some (Tree.climb node z i N as) →
    (∃ id : LeafId, id.height ≤ hsf ∧ Node.ofLeafId hsf id ∈ S.anchors ∧
      ∃ l r, node id l r = leaf id) ∨
    (∃ id : LeafId, id.height ≤ hsf ∧ Node.ofLeafId hsf id ∈ S.internal ∧
      ∃ l r, Tree.treeNode hsf S leaf node (id.height - 1) (2 * id.index) = some l ∧
        Tree.treeNode hsf S leaf node (id.height - 1) (2 * id.index + 1) = some r ∧
        ∃ l' r', (l', r') ≠ (l, r) ∧ node id l' r' = node id l r) ∨
    Tree.treeNode hsf S leaf node z i = some N
  | [], z, i, N, h => Or.inr (Or.inr (by simpa using h))
  | a :: as, z, i, N, h => by
    rw [Tree.climb_cons] at h
    have h' : Tree.treeNode hsf S leaf node (z + 1 + as.length) (i / 2 / 2 ^ as.length) =
        some (Tree.climb node (z + 1) (i / 2)
          (if i % 2 = 0 then node ⟨z + 1, i / 2⟩ N a else node ⟨z + 1, i / 2⟩ a N) as) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show z + 1 + as.length = z + (as.length + 1)
        by omega]
      simpa using h
    rcases climb_walk as (z + 1) (i / 2) _ h' with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    rcases treeNode_eq_some_cases h1 with ⟨hz, hA, hx⟩ | ⟨z', hz', hz, hI, l, r, hl, hr, hx⟩
    · refine Or.inl ⟨⟨z + 1, i / 2⟩, hz, hA, ?_⟩
      split_ifs at hx
      · exact ⟨N, a, hx⟩
      · exact ⟨a, N, hx⟩
    · obtain rfl : z = z' := by omega
      by_cases hi : i % 2 = 0
      · simp only [hi, ↓reduceIte] at hx
        by_cases hp : (N, a) = (l, r)
        · obtain ⟨rfl, -⟩ := Prod.mk.inj hp
          right; right
          rwa [show 2 * (i / 2) = i by omega] at hl
        · exact Or.inr (Or.inl ⟨⟨z + 1, i / 2⟩, hz, hI, l, r, hl, hr, N, a, hp, hx⟩)
      · simp only [hi, ↓reduceIte] at hx
        by_cases hp : (a, N) = (l, r)
        · obtain ⟨-, rfl⟩ := Prod.mk.inj hp
          right; right
          rwa [show 2 * (i / 2) + 1 = i by omega] at hr
        · exact Or.inr (Or.inl ⟨⟨z + 1, i / 2⟩, hz, hI, l, r, hl, hr, a, N, hp, hx⟩)

/-- Two sequences that differ at `b` and agree at `m ≥ b` have a last disagreement before `m`:
some `p ∈ [b, m)` with `x p ≠ h p` and `x (p + 1) = h (p + 1)`. -/
theorem exists_last_ne {x h : ℕ → Y} {b m : ℕ} (hbm : b ≤ m) (hb : x b ≠ h b) (hm : x m = h m) :
    ∃ p, b ≤ p ∧ p < m ∧ x p ≠ h p ∧ x (p + 1) = h (p + 1) := by
  induction m, hbm using Nat.le_induction with
  | base => exact absurd hm hb
  | succ m hbm ih =>
    by_cases hxm : x m = h m
    · obtain ⟨p, h1, h2, h3, h4⟩ := ih hxm
      exact ⟨p, h1, by omega, h3, h4⟩
    · exact ⟨m, hbm, by omega, hxm, hm⟩

end ShrincsSecurity.Fxmss
