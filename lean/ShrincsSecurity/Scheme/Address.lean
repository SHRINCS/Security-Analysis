module

public import HashSig.SLHDSA.Address

/-!
# SHRINCS addresses (tweaks)

`SHRINCS-Security-Analysis.pdf`, Section 2.2 ("Addressing scheme", Figures 1 and 2, Tables 2
and 3).

SHRINCS uses one 22-byte address format for every `Th_ℓ` and `PRF` call on both paths: a 9-byte
position prefix, a type byte and a 12-byte payload of three words. We do not model bytes. The
common format is VCVio's typed record `SLHDSA.Adrs` (fields `layer`, `tree`, `type`, `word1`,
`word2`, `word3`), which is exactly the field structure of the 22-byte compressed address `ADRSc`
(footnote 3 of the paper). This record is the tweak space `T` of the tweakable-hash collection.

* On the stateless path the prefix is `(layer, tree)` and the types are VCVio's seven FIPS 205
  types `SLHDSA.AddrType` (codes 0–6); stateless addresses are produced by VCVio's SLH-DSA code.
* On the stateful path the prefix is `(node height z, node index i)` and the types are the five
  `SfType`s (codes 16, 17, 18, 21, 22). Stateful addresses are the typed records `SfAdrs`, embedded
  into the common format by the injective map `SfAdrs.toAdrs`.

The role constructors `SfAdrs.chainAdrs`, `pkAdrs`, `treeAdrs`, `prfAdrs`, `grindAdrs` follow
Table 3. The tweak-disjointness facts used by the reductions of Section 4.7 are proved here:
injectivity within a role, disjointness between roles (type byte), disjointness between the
stateful and stateless paths (type ranges 16–22 versus 0–6), and the exclusive-partner bijection
`ω` of Claim 4.9 between tree-node and public-key-compression tweaks.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme

open SLHDSA (Adrs AddrType)

/-! ## Address types (Table 2) -/

/-- The five stateful address types of **Table 2**. -/
inductive SfType where
  /-- `SF_WOTS_C_HASH` (16): WOTS+C hash chains. -/
  | wotsCHash
  /-- `SF_WOTS_C_PK` (17): WOTS+C public-key compression. -/
  | wotsCPk
  /-- `SF_FXMSS_TREE` (18): internal FXMSS tree nodes. -/
  | fxmssTree
  /-- `SF_WOTS_C_PRF` (21): WOTS+C secret-value derivation. -/
  | wotsCPrf
  /-- `SF_WOTS_C_GRIND` (22): grinding of WOTS+C message digests. -/
  | wotsCGrind
deriving Repr, DecidableEq, Inhabited

/-- The type byte of a stateful address type (Table 2). -/
def SfType.toCode : SfType → ℕ
  | .wotsCHash => 16
  | .wotsCPk => 17
  | .fxmssTree => 18
  | .wotsCPrf => 21
  | .wotsCGrind => 22

theorem SfType.toCode_injective : Function.Injective SfType.toCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [SfType.toCode]

theorem SfType.sixteen_le_toCode (t : SfType) : 16 ≤ t.toCode := by
  cases t <;> decide

/-- Each stateful type is its stateless counterpart plus 16 (Table 2 discussion). -/
theorem SfType.toCode_eq_add_sixteen :
    SfType.wotsCHash.toCode = AddrType.wotsHash.toCode + 16 ∧
      SfType.wotsCPk.toCode = AddrType.wotsPk.toCode + 16 ∧
      SfType.fxmssTree.toCode = AddrType.tree.toCode + 16 ∧
      SfType.wotsCPrf.toCode = AddrType.wotsPrf.toCode + 16 := by
  decide

theorem addrType_toCode_lt_seven (t : AddrType) : t.toCode < 7 := by
  cases t <;> decide

theorem addrType_toCode_injective : Function.Injective AddrType.toCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [AddrType.toCode]

/-- Stateless and stateful type bytes are disjoint (Table 2: types 0–6 versus 16–22). -/
theorem addrType_toCode_ne_sfType_toCode (t : AddrType) (s : SfType) :
    t.toCode ≠ s.toCode := by
  have := addrType_toCode_lt_seven t
  have := s.sixteen_le_toCode
  omega

/-- All twelve SHRINCS address types (**Table 2**). -/
inductive AdrsType where
  | sl (t : AddrType)
  | sf (t : SfType)
deriving DecidableEq

/-- The type byte of a SHRINCS address type. -/
def AdrsType.toCode : AdrsType → ℕ
  | .sl t => t.toCode
  | .sf t => t.toCode

theorem AdrsType.toCode_injective : Function.Injective AdrsType.toCode := by
  rintro (a | a) (b | b) h <;> simp only [AdrsType.toCode] at h
  · rw [addrType_toCode_injective h]
  · exact absurd h (addrType_toCode_ne_sfType_toCode a b)
  · exact absurd h.symm (addrType_toCode_ne_sfType_toCode b a)
  · rw [SfType.toCode_injective h]

/-! ## Path predicates on the common format -/

/-- An address of the stateless path: its type byte is one of the FIPS 205 types 0–6. -/
def IsStateless (a : Adrs) : Prop := ∃ t : AddrType, a.type = t.toCode

/-- An address of the stateful path: its type byte is one of the types 16–22. -/
def IsStateful (a : Adrs) : Prop := ∃ t : SfType, a.type = t.toCode

/-- **Path separation** (Section 2.2, "Address types"): no address is on both paths. -/
theorem not_isStateful_of_isStateless {a : Adrs} (h : IsStateless a) : ¬ IsStateful a := by
  rintro ⟨s, hs⟩
  obtain ⟨t, ht⟩ := h
  exact addrType_toCode_ne_sfType_toCode t s (ht.symm.trans hs)

theorem ne_of_isStateless_of_isStateful {a b : Adrs} (ha : IsStateless a) (hb : IsStateful b) :
    a ≠ b := by
  rintro rfl
  exact not_isStateful_of_isStateless ha hb

/-- Every FIPS 205 type change produces a stateless address. -/
theorem isStateless_setTypeAndClear (a : Adrs) (t : AddrType) :
    IsStateless (a.setTypeAndClear t) := ⟨t, rfl⟩

/-- The FIPS 205 field setters other than the type change preserve the type byte. -/
theorem IsStateless.setKeyPairAddress {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setKeyPairAddress i) := h

theorem IsStateless.setChainAddress {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setChainAddress i) := h

theorem IsStateless.setHashAddress {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setHashAddress i) := h

theorem IsStateless.setTreeHeight {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setTreeHeight i) := h

theorem IsStateless.setTreeIndex {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setTreeIndex i) := h

theorem IsStateless.setLayerAddress {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setLayerAddress i) := h

theorem IsStateless.setTreeAddress {a : Adrs} (h : IsStateless a) (i : ℕ) :
    IsStateless (a.setTreeAddress i) := h

/-! ## Leaf identifiers and stateful addresses (Figure 2, Table 3) -/

/-- A position `(z, i)` of the imaginary tree in **height coordinates**: node height `z` (distance
from the leaf level) and node index `i`. For an anchor this is the leaf identifier
`idx = toByte(z*, 1) ‖ toByte(i*, 8)` absorbed by `H_msg^sf` and `PRF_msg^sf` (Section 2.2). -/
@[ext] structure LeafId where
  /-- Node height `z`. -/
  height : ℕ
  /-- Node index `i`. -/
  index : ℕ
deriving Repr, DecidableEq

/-- A stateful address (**Figure 2**, **Table 3**): node height and node index (the prefix), the
type byte, and the three payload words. -/
@[ext] structure SfAdrs where
  /-- Node height `z` (prefix byte 0). -/
  height : ℕ
  /-- Node index `i` (prefix bytes 1–8). -/
  index : ℕ
  /-- The type byte. -/
  type : SfType
  /-- Payload bytes 10–13: `shape ‖ depth ‖ 0²` for `SF_WOTS_C_PRF`, zero otherwise. -/
  word1 : ℕ
  /-- Payload bytes 14–17: chain address for `SF_WOTS_C_HASH` / `SF_WOTS_C_PRF`. -/
  chain : ℕ
  /-- Payload bytes 18–21: hash address for `SF_WOTS_C_HASH`. -/
  hash : ℕ
deriving Repr, DecidableEq

namespace SfAdrs

/-- Embed a stateful address into the common 22-byte address format: the node height occupies
the layer byte and the node index the 8-byte tree field (Figures 1 and 2). -/
def toAdrs (a : SfAdrs) : Adrs where
  layer := a.height
  tree := a.index
  type := a.type.toCode
  word1 := a.word1
  word2 := a.chain
  word3 := a.hash

theorem toAdrs_injective : Function.Injective toAdrs := by
  intro a b h
  simp only [toAdrs, Adrs.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact SfAdrs.ext h1 h2 (SfType.toCode_injective h3) h4 h5 h6

theorem toAdrs_inj {a b : SfAdrs} : a.toAdrs = b.toAdrs ↔ a = b :=
  toAdrs_injective.eq_iff

theorem isStateful_toAdrs (a : SfAdrs) : IsStateful a.toAdrs := ⟨a.type, rfl⟩

/-- **Path separation**: a stateful address never equals a stateless one. -/
theorem toAdrs_ne_of_isStateless (a : SfAdrs) {b : Adrs} (hb : IsStateless b) : a.toAdrs ≠ b :=
  fun h => ne_of_isStateless_of_isStateful hb (h ▸ a.isStateful_toAdrs) rfl

/-- Addresses of different types are different (the main domain separator). -/
theorem toAdrs_ne_of_type_ne {a b : SfAdrs} (h : a.type ≠ b.type) : a.toAdrs ≠ b.toAdrs :=
  fun h' => h (congrArg SfAdrs.type (toAdrs_injective h'))

/-- `SF_WOTS_C_HASH` address of hash step `j` of chain `ch` of the WOTS+C instance at `id`. -/
def chainAdrs (id : LeafId) (ch j : ℕ) : SfAdrs := ⟨id.height, id.index, .wotsCHash, 0, ch, j⟩

/-- `SF_WOTS_C_PK` address compressing the WOTS+C public key at `id`. -/
def pkAdrs (id : LeafId) : SfAdrs := ⟨id.height, id.index, .wotsCPk, 0, 0, 0⟩

/-- `SF_FXMSS_TREE` address of the internal FXMSS node at `id`. -/
def treeAdrs (id : LeafId) : SfAdrs := ⟨id.height, id.index, .fxmssTree, 0, 0, 0⟩

/-- `SF_WOTS_C_PRF` address deriving the secret of chain `ch` at `id`; `tag` is the payload word
`shape ‖ depth ‖ 0²` carrying the structure bytes (Table 3). -/
def prfAdrs (tag : ℕ) (id : LeafId) (ch : ℕ) : SfAdrs := ⟨id.height, id.index, .wotsCPrf, tag, ch, 0⟩

/-- `SF_WOTS_C_GRIND` address of the grinding hash at `id` (zero payload, Section 2.2). -/
def grindAdrs (id : LeafId) : SfAdrs := ⟨id.height, id.index, .wotsCGrind, 0, 0, 0⟩

/-- Chain-step addresses are VCVio's `setHashAddress` updates of the chain's base address, so the
FIPS 205 chaining function applies verbatim (Section 2.4, "Chaining function"). -/
@[simp] theorem chainAdrs_setHashAddress (id : LeafId) (ch j k : ℕ) :
    (chainAdrs id ch j).toAdrs.setHashAddress k = (chainAdrs id ch k).toAdrs := rfl

/-! ### Injectivity within a role -/

theorem chainAdrs_inj {id id' : LeafId} {ch ch' j j' : ℕ} :
    (chainAdrs id ch j).toAdrs = (chainAdrs id' ch' j').toAdrs ↔
      id = id' ∧ ch = ch' ∧ j = j' := by
  rw [toAdrs_inj]
  simp [chainAdrs, SfAdrs.mk.injEq, LeafId.ext_iff, and_assoc]

theorem pkAdrs_inj {id id' : LeafId} : (pkAdrs id).toAdrs = (pkAdrs id').toAdrs ↔ id = id' := by
  rw [toAdrs_inj]
  simp [pkAdrs, SfAdrs.mk.injEq, LeafId.ext_iff]

theorem treeAdrs_inj {id id' : LeafId} :
    (treeAdrs id).toAdrs = (treeAdrs id').toAdrs ↔ id = id' := by
  rw [toAdrs_inj]
  simp [treeAdrs, SfAdrs.mk.injEq, LeafId.ext_iff]

theorem grindAdrs_inj {id id' : LeafId} :
    (grindAdrs id).toAdrs = (grindAdrs id').toAdrs ↔ id = id' := by
  rw [toAdrs_inj]
  simp [grindAdrs, SfAdrs.mk.injEq, LeafId.ext_iff]

theorem prfAdrs_inj {tag tag' ch ch' : ℕ} {id id' : LeafId} :
    (prfAdrs tag id ch).toAdrs = (prfAdrs tag' id' ch').toAdrs ↔
      tag = tag' ∧ id = id' ∧ ch = ch' := by
  rw [toAdrs_inj]
  simp only [prfAdrs, SfAdrs.mk.injEq, LeafId.ext_iff]
  tauto

/-! ### Disjointness between roles (type byte) -/

section Roles

variable (id id' : LeafId) (ch ch' j : ℕ) (tag : ℕ)

theorem chainAdrs_ne_pkAdrs : (chainAdrs id ch j).toAdrs ≠ (pkAdrs id').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem chainAdrs_ne_treeAdrs : (chainAdrs id ch j).toAdrs ≠ (treeAdrs id').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem chainAdrs_ne_grindAdrs : (chainAdrs id ch j).toAdrs ≠ (grindAdrs id').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem chainAdrs_ne_prfAdrs : (chainAdrs id ch j).toAdrs ≠ (prfAdrs tag id' ch').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem pkAdrs_ne_treeAdrs : (pkAdrs id).toAdrs ≠ (treeAdrs id').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem pkAdrs_ne_grindAdrs : (pkAdrs id).toAdrs ≠ (grindAdrs id').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem pkAdrs_ne_prfAdrs : (pkAdrs id).toAdrs ≠ (prfAdrs tag id' ch).toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem treeAdrs_ne_grindAdrs : (treeAdrs id).toAdrs ≠ (grindAdrs id').toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem treeAdrs_ne_prfAdrs : (treeAdrs id).toAdrs ≠ (prfAdrs tag id' ch).toAdrs :=
  toAdrs_ne_of_type_ne nofun

theorem grindAdrs_ne_prfAdrs : (grindAdrs id).toAdrs ≠ (prfAdrs tag id' ch).toAdrs :=
  toAdrs_ne_of_type_ne nofun

end Roles

end SfAdrs

/-! ## The exclusive-partner bijection of Claim 4.9 -/

/-- Tweaks of internal FXMSS nodes, `T₂` of Claim 4.9 (type `SF_FXMSS_TREE`). -/
def IsTreeTweak (a : Adrs) : Prop := ∃ id, a = (SfAdrs.treeAdrs id).toAdrs

/-- Tweaks of WOTS+C public-key compressions, `T₃` of Claim 4.9 (type `SF_WOTS_C_PK`). -/
def IsPkTweak (a : Adrs) : Prop := ∃ id, a = (SfAdrs.pkAdrs id).toAdrs

/-- The bijection `ω : T₂ → T₃` of **Claim 4.9**: replace the type byte `SF_FXMSS_TREE` by
`SF_WOTS_C_PK`, keeping the node identifier `(z, i)`. -/
def omega (a : Adrs) : Adrs := { a with type := SfType.wotsCPk.toCode }

/-- The inverse partner map `ω⁻¹ : T₃ → T₂`. -/
def omegaInv (a : Adrs) : Adrs := { a with type := SfType.fxmssTree.toCode }

@[simp] theorem omega_treeAdrs (id : LeafId) :
    omega (SfAdrs.treeAdrs id).toAdrs = (SfAdrs.pkAdrs id).toAdrs := rfl

@[simp] theorem omegaInv_pkAdrs (id : LeafId) :
    omegaInv (SfAdrs.pkAdrs id).toAdrs = (SfAdrs.treeAdrs id).toAdrs := rfl

theorem omegaInv_omega {a : Adrs} (h : IsTreeTweak a) : omegaInv (omega a) = a := by
  obtain ⟨id, rfl⟩ := h; rfl

theorem omega_omegaInv {a : Adrs} (h : IsPkTweak a) : omega (omegaInv a) = a := by
  obtain ⟨id, rfl⟩ := h; rfl

theorem IsTreeTweak.omega {a : Adrs} (h : IsTreeTweak a) : IsPkTweak (omega a) := by
  obtain ⟨id, rfl⟩ := h; exact ⟨id, rfl⟩

/-- `ω` is injective on `T₂`. -/
theorem omega_injOn {a b : Adrs} (ha : IsTreeTweak a) (hb : IsTreeTweak b)
    (h : omega a = omega b) : a = b := by
  rw [← omegaInv_omega ha, ← omegaInv_omega hb, h]

/-- `T₂` and `T₃` are disjoint. -/
theorem not_isPkTweak_of_isTreeTweak {a : Adrs} (h : IsTreeTweak a) : ¬ IsPkTweak a := by
  obtain ⟨id, rfl⟩ := h
  rintro ⟨id', h'⟩
  exact SfAdrs.pkAdrs_ne_treeAdrs id' id h'.symm

end ShrincsSecurity.Scheme
