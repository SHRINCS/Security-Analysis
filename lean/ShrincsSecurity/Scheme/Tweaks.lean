module

public import ShrincsSecurity.Scheme.Structure

/-!
# The tweaks of a structure

`SHRINCS-Security-Analysis.pdf`, Section 2.2 ("Addressing scheme"), Section 4.7 (the challenge
and collection tweak sets of the reductions `B_3`–`B_8`, Claims 4.3–4.9).

For a valid structure, the stateful tweaks fall into disjoint role sets, one tweak per role per
position, with the target counts used by the reductions:

| role | set | count |
|---|---|---|
| WOTS+C chain steps (`F`, Claims 4.4–4.6) | `chainTweaks` | `L · lsf · (w − 1)` |
| WOTS+C public-key compression (`Th_lsf`, Claim 4.7) | `pkTweaks` | `L` |
| internal tree nodes (`H`, Claim 4.8) | `treeTweaks` | `I = L − 1` |
| grinding (`H_grind`, Claim 4.3) | `grindTweaks` | `L` |
| leaf identifiers `idx` (`H_msg^sf`, Claims 4.1, 4.2) | `leafIds` | `L` |

Distinct anchors give distinct leaf identifiers and tweaks (injectivity of the image maps); the
role sets are pairwise disjoint; and the honest structure uses exactly one of the two partner
roles `T₂` / `T₃` at every node identifier (`exclusive_roles`, Claim 4.9). All stateful tweaks are
disjoint from the stateless path (`SfAdrs.toAdrs_ne_of_isStateless`, `Stateless.lean`).
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.Structure

open SLHDSA (Adrs)
open SfAdrs

variable (hsf : ℕ) (S : Structure)

/-- The leaf identifiers `idx = (z*, i*)` of the anchors (the `H_msg^sf` tweaks). -/
def leafIds : Finset LeafId := S.anchors.image (Node.toLeafId hsf)

/-- The `SF_WOTS_C_HASH` tweaks: anchor, chain `ch < lsf`, hash address `j < w − 1`. -/
def chainTweaks (lsf w : ℕ) : Finset Adrs :=
  (S.anchors ×ˢ (Finset.range lsf ×ˢ Finset.range (w - 1))).image fun p =>
    (chainAdrs (p.1.toLeafId hsf) p.2.1 p.2.2).toAdrs

/-- The `SF_WOTS_C_PK` tweaks, one per anchor (`T₃` of Claim 4.9). -/
def pkTweaks : Finset Adrs := S.anchors.image fun a => (pkAdrs (a.toLeafId hsf)).toAdrs

/-- The `SF_FXMSS_TREE` tweaks, one per internal node (`T₂` of Claim 4.9). -/
def treeTweaks : Finset Adrs := S.internal.image fun v => (treeAdrs (v.toLeafId hsf)).toAdrs

/-- The `SF_WOTS_C_GRIND` tweaks, one per anchor. -/
def grindTweaks : Finset Adrs := S.anchors.image fun a => (grindAdrs (a.toLeafId hsf)).toAdrs

variable {hsf S}

namespace TreeValid

variable (hS : S.TreeValid hsf)
include hS

/-- **Distinct nodes of a valid structure have distinct leaf identifiers.** -/
theorem toLeafId_injOn {v w : Node} (hv : v ∈ S.nodes) (hw : w ∈ S.nodes)
    (h : v.toLeafId hsf = w.toLeafId hsf) : v = w :=
  Node.toLeafId_injOn (hS.depth_le hv) (hS.depth_le hw) h

theorem card_leafIds : (leafIds hsf S).card = S.anchors.card :=
  Finset.card_image_of_injOn fun _ hv _ hw h =>
    hS.toLeafId_injOn (anchors_subset_nodes hv) (anchors_subset_nodes hw) h

theorem card_pkTweaks : (pkTweaks hsf S).card = S.anchors.card :=
  Finset.card_image_of_injOn fun _ hv _ hw h =>
    hS.toLeafId_injOn (anchors_subset_nodes hv) (anchors_subset_nodes hw) (pkAdrs_inj.1 h)

theorem card_grindTweaks : (grindTweaks hsf S).card = S.anchors.card :=
  Finset.card_image_of_injOn fun _ hv _ hw h =>
    hS.toLeafId_injOn (anchors_subset_nodes hv) (anchors_subset_nodes hw) (grindAdrs_inj.1 h)

/-- `|T₂| = I = L − 1`. -/
theorem card_treeTweaks : (treeTweaks hsf S).card = S.anchors.card - 1 := by
  rw [← hS.card_internal]
  exact Finset.card_image_of_injOn fun _ hv _ hw h =>
    hS.toLeafId_injOn (internal_subset_nodes hv) (internal_subset_nodes hw) (treeAdrs_inj.1 h)

theorem card_chainTweaks (lsf w : ℕ) :
    (chainTweaks hsf S lsf w).card = S.anchors.card * (lsf * (w - 1)) := by
  rw [chainTweaks, Finset.card_image_of_injOn, Finset.card_product, Finset.card_product,
    Finset.card_range, Finset.card_range]
  rintro ⟨a, ch, j⟩ ha ⟨a', ch', j'⟩ ha' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at ha ha'
  obtain ⟨hid, rfl, rfl⟩ := chainAdrs_inj.1 h
  rw [hS.toLeafId_injOn (anchors_subset_nodes ha.1) (anchors_subset_nodes ha'.1) hid]

/-- **Exclusive roles** (Claim 4.9): at no node identifier does the honest structure use both the
tree-node tweak and its `ω`-partner public-key-compression tweak. -/
theorem exclusive_roles (id : LeafId) :
    ¬ ((treeAdrs id).toAdrs ∈ treeTweaks hsf S ∧ (pkAdrs id).toAdrs ∈ pkTweaks hsf S) := by
  rintro ⟨ht, hp⟩
  obtain ⟨v, hv, hvid⟩ := Finset.mem_image.1 ht
  obtain ⟨a, ha, haid⟩ := Finset.mem_image.1 hp
  have := hS.toLeafId_injOn (internal_subset_nodes hv) (anchors_subset_nodes ha)
    ((treeAdrs_inj.1 hvid).trans (pkAdrs_inj.1 haid).symm)
  subst this
  exact hS.not_mem_anchors_of_mem_internal hv ha

/-- The `ω`-partner of an honest tree-node tweak is not an honest compression tweak. -/
theorem omega_not_mem_pkTweaks {t : Adrs} (ht : t ∈ treeTweaks hsf S) :
    omega t ∉ pkTweaks hsf S := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ht
  rw [omega_treeAdrs]
  exact fun hp => hS.exclusive_roles _ ⟨Finset.mem_image_of_mem _ hv, hp⟩

/-- The `ω⁻¹`-partner of an honest compression tweak is not an honest tree-node tweak. -/
theorem omegaInv_not_mem_treeTweaks {t : Adrs} (ht : t ∈ pkTweaks hsf S) :
    omegaInv t ∉ treeTweaks hsf S := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
  rw [omegaInv_pkAdrs]
  exact fun hp => hS.exclusive_roles _ ⟨hp, Finset.mem_image_of_mem _ ha⟩

end TreeValid

/-! ## Disjointness of the role sets -/

theorem disjoint_chainTweaks_pkTweaks (lsf w : ℕ) :
    Disjoint (chainTweaks hsf S lsf w) (pkTweaks hsf S) := by
  refine Finset.disjoint_left.2 fun t h1 h2 => ?_
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.1 h2
  exact chainAdrs_ne_pkAdrs _ _ _ _ h.symm

theorem disjoint_chainTweaks_treeTweaks (lsf w : ℕ) :
    Disjoint (chainTweaks hsf S lsf w) (treeTweaks hsf S) := by
  refine Finset.disjoint_left.2 fun t h1 h2 => ?_
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.1 h2
  exact chainAdrs_ne_treeAdrs _ _ _ _ h.symm

theorem disjoint_chainTweaks_grindTweaks (lsf w : ℕ) :
    Disjoint (chainTweaks hsf S lsf w) (grindTweaks hsf S) := by
  refine Finset.disjoint_left.2 fun t h1 h2 => ?_
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.1 h2
  exact chainAdrs_ne_grindAdrs _ _ _ _ h.symm

theorem disjoint_pkTweaks_treeTweaks : Disjoint (pkTweaks hsf S) (treeTweaks hsf S) := by
  refine Finset.disjoint_left.2 fun t h1 h2 => ?_
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.1 h2
  exact pkAdrs_ne_treeAdrs _ _ h.symm

theorem disjoint_pkTweaks_grindTweaks : Disjoint (pkTweaks hsf S) (grindTweaks hsf S) := by
  refine Finset.disjoint_left.2 fun t h1 h2 => ?_
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.1 h2
  exact pkAdrs_ne_grindAdrs _ _ h.symm

theorem disjoint_treeTweaks_grindTweaks : Disjoint (treeTweaks hsf S) (grindTweaks hsf S) := by
  refine Finset.disjoint_left.2 fun t h1 h2 => ?_
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.1 h2
  exact treeAdrs_ne_grindAdrs _ _ h.symm

/-- Every stateful tweak of a structure is a stateful address, hence distinct from every address
of the stateless path. -/
theorem isStateful_of_mem_tweaks {lsf w : ℕ} {t : Adrs}
    (h : t ∈ chainTweaks hsf S lsf w ∨ t ∈ pkTweaks hsf S ∨ t ∈ treeTweaks hsf S ∨
      t ∈ grindTweaks hsf S) : IsStateful t := by
  rcases h with h | h | h | h <;> obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 h <;>
    exact isStateful_toAdrs _

end ShrincsSecurity.Scheme.Structure
