module

public import ShrincsSecurity.Scheme.Fxmss
public import ShrincsSecurity.Scheme.Tweaks
public import ShrincsSecurity.Fxmss.Walk

/-!
# Extraction from an FXMSS forgery (Claim 4.10)

`SHRINCS-Security-Analysis.pdf`, Section 4.7: the abort events of the game hops F.0 → F.1,
F.2 → F.3 and F.4 → F.9, Remark 4.6 (every anchor is signed once), and the proof of
**Claim 4.10** (`Succ^{F.9}(A) = 0`).

This file proves the deterministic core of Claim 4.10: for a fixed honest key and honest
signatures at **every** anchor (Remark 4.6), every verifying forgery on a fresh message exhibits one
of the explicit collision/preimage events below. Each event names the tweak (an element of the
tweak set of the structure from `Scheme.Tweaks`), the honest input committed at that tweak, and the
colliding input, so that a reduction can output it as a win in the corresponding game:

| event | hop | game | tweak set |
|---|---|---|---|
| `E1` | F.0 → F.1 | SM-rTCR of `H_msg^sf` | `leafIds` |
| `E3` | F.2 → F.3 | S-TCR(Prop) of `H_grind` | `grindTweaks` |
| `E5` | F.4 → F.5 | sm-tcr of `F` | `chainTweaks` |
| `E6` | F.5 → F.6 | sm-pre of `F` | `chainTweaks` |
| `E7` | F.6 → F.7 | sm-tcr of `Th_lsf` | `pkTweaks` |
| `E8` | F.7 → F.8 | sm-tcr of `H` | `treeTweaks` |
| `E9` | F.8 → F.9 | sm-tcr-excl of `Th_{2∪lsf}` | `pkTweaks` / `treeTweaks`, partner `ω^{±1}` |

## The honest view

The core theorem `HonestView.extraction` is stated over a `HonestView`: the structure, `PK.seed`,
`PK.sf`, arbitrary anchor values `leaf`, and per leaf identifier the signed message, the randomizer
and the WOTS+C signature. Its only hypotheses (`HonestView.Consistent`) are the ones the verifier
can see: the tree built from `leaf` has root `PK.sf`, and every honest WOTS+C signature recovers its
anchor value. The honest chain values are those *revealed* by the signatures (blocks `σ_{j,i}` and
their completions), so the theorem applies verbatim to the games F.4–F.9, where blocks are hashes
of fresh values rather than chain values from a secret key. `claim_4_10` instantiates it with the
scheme's key generation and signing from a secret table `sk` (`HonestView.ofSigs`).

## Deviations from the printed proof

* "`d` is determined by its `lsf` base-`w` digits" requires the byte encoding `yToBytes` to be
  injective; this is an explicit hypothesis (`hinj`), together with `P.Valid` (`lgw ∣ n`). Without
  it the case `d* ≠ d_j` with equal digit vectors has no abort event: the forger may reuse the
  honest blocks verbatim.
* The paper's two minimisations (least `t*` entering `A ∪ I`, least `s ≥ t*` with honest agreement)
  are one downward induction (`climb_walk`); validity of the structure is not needed for the
  deterministic statement (`treeNode` is `⊥` off `A ∪ I`).
* The `F.5` event is stated against the honest chain value at position `p ≥ a_{j,i}`, computed from
  the revealed block (`HonestView.chainValue`); in the secret-key model it is `c_{0,p}(sk_{j,i})`
  (`HonestView.ofSigs_chainValue`).
-/

@[expose] public section

namespace ShrincsSecurity.Fxmss

open Scheme Scheme.SfAdrs
open SLHDSA (Byte)
open Scheme.Structure (leafIds chainTweaks pkTweaks treeTweaks grindTweaks)

variable {P : Params}

/-- The honest data of an FXMSS EU-CMA run fixed for Claim 4.10: the structure, `PK.seed`,
`PK.sf`, the anchor values, and for every leaf identifier the signed (bound) message, the
randomizer and the WOTS+C signature of the signing query at that leaf (Remark 4.6). -/
structure HonestView (pr : Primitives P) where
  /-- The committed structure. -/
  S : Structure
  /-- `PK.seed`. -/
  pk : pr.PkSeed
  /-- `PK.sf`. -/
  pkSf : pr.Y
  /-- The anchor values (compressed WOTS+C public keys). -/
  leaf : LeafId → pr.Y
  /-- The signed message `M̃_j` at each leaf. -/
  msg : LeafId → List Byte
  /-- The randomizer `R_j` at each leaf. -/
  rand : LeafId → pr.Y
  /-- The honest WOTS+C signature `(c_j, σ_{j,0}, …, σ_{j,lsf−1})` at each leaf. -/
  wots : LeafId → WotsC.Sig pr

namespace HonestView

variable {pr : Primitives P} (V : HonestView pr)

/-- The honest node value `treeNode_structure(z, i)`. -/
def value (z i : ℕ) : Option pr.Y :=
  Tree.treeNode P.hsf V.S V.leaf (Scheme.Fxmss.node pr V.pk) z i

/-- The honest message digest `y_j = H_msg^sf(R_j, PK.seed, PK.sf, idx_j, M̃_j)`. -/
def digest (id : LeafId) : pr.Digest := pr.HmsgSf (V.rand id) V.pk V.pkSf id (V.msg id)

/-- The honest encoded digest `d_j = H_grind(PK.seed, ADRS^g_j, y_j, c_j)`. -/
def encoded (id : LeafId) : pr.Y := WotsC.encode pr V.pk id (V.digest id) (V.wots id).ctr

/-- The honest uncompressed WOTS+C public key, completed from the revealed blocks. -/
def tops (id : LeafId) : Vector pr.Y P.lsf :=
  WotsC.topsFromSig pr V.pk id (V.encoded id) (V.wots id)

/-- The revealed block `σ_{j,ch}`, at position `a_{j,ch}` of chain `ch`. -/
def block (id : LeafId) (ch : Fin P.lsf) : pr.Y := (V.wots id).chains[ch.val]

/-- The honest value of chain `ch` at position `p ≥ a_{j,ch}`, completed from the revealed block:
`c_{a, p − a}(σ_{j,ch})`. -/
def chainValue (id : LeafId) (ch : Fin P.lsf) (p : ℕ) : pr.Y :=
  WotsC.chain pr V.pk id ch.val (V.block id ch) (WotsC.digit pr (V.encoded id) ch.val)
    (p - WotsC.digit pr (V.encoded id) ch.val)

/-- The honest view is consistent: the tree over the anchor values has root `PK.sf`, and the
honest signature at every anchor recovers the anchor value. -/
structure Consistent : Prop where
  root : V.value P.hsf 0 = some V.pkSf
  sig : ∀ id ∈ leafIds P.hsf V.S,
    WotsC.pkFromSig pr V.pk id (V.digest id) (V.wots id) = some (V.leaf id)

/-! ## The abort events -/

/-- **Event of F.1**: an `H_msg^sf` collision at the leaf identifier `idx_j` of a signed anchor
with the honest query `(R_j, M̃_j)`. -/
def E1 : Prop :=
  ∃ id ∈ leafIds P.hsf V.S, ∃ (R : pr.Y) (M : List Byte), (R, M) ≠ (V.rand id, V.msg id) ∧
    pr.HmsgSf R V.pk V.pkSf id M = V.digest id

/-- **Event of F.3**: an `H_grind` collision at the grinding tweak of a signed anchor with the
honest target-sum pair `(y_j, c_j)`, by a pair with a different digest. -/
def E3 : Prop :=
  ∃ id, (grindAdrs id).toAdrs ∈ grindTweaks P.hsf V.S ∧ WotsC.TargetSum pr (V.encoded id) ∧
    ∃ (y : pr.Digest) (c : Fin (2 ^ P.c)), y ≠ V.digest id ∧
      pr.Hgrind V.pk (grindAdrs id).toAdrs y c =
        pr.Hgrind V.pk (grindAdrs id).toAdrs (V.digest id) (V.wots id).ctr

/-- **Event of F.5**: a chain collision: at the chain tweak of position `p` (at or above the
revealed digit) of a signed anchor, an input different from the honest chain value with the same
`F`-output. -/
def E5 : Prop :=
  ∃ (id : LeafId) (ch : Fin P.lsf) (p : ℕ),
    (chainAdrs id ch p).toAdrs ∈ chainTweaks P.hsf V.S P.lsf P.w ∧
    WotsC.digit pr (V.encoded id) ch ≤ p ∧
    ∃ x, x ≠ V.chainValue id ch p ∧
      pr.F V.pk (chainAdrs id ch p).toAdrs x =
        pr.F V.pk (chainAdrs id ch p).toAdrs (V.chainValue id ch p)

/-- **Event of F.6**: an `F`-preimage of a revealed block `σ_{j,ch}` with positive digit, at the
chain tweak of position `a_{j,ch} − 1`. -/
def E6 : Prop :=
  ∃ (id : LeafId) (ch : Fin P.lsf),
    (chainAdrs id ch (WotsC.digit pr (V.encoded id) ch - 1)).toAdrs ∈
      chainTweaks P.hsf V.S P.lsf P.w ∧
    0 < WotsC.digit pr (V.encoded id) ch ∧
    ∃ x, pr.F V.pk (chainAdrs id ch (WotsC.digit pr (V.encoded id) ch - 1)).toAdrs x =
      V.block id ch

/-- **Event of F.7**: a `Th_lsf` collision at the public-key-compression tweak of a signed anchor
between the honest uncompressed public key and a different tuple. -/
def E7 : Prop :=
  ∃ id, (pkAdrs id).toAdrs ∈ pkTweaks P.hsf V.S ∧
    ∃ tops : Vector pr.Y P.lsf, tops ≠ V.tops id ∧
      pr.ThLsf V.pk (pkAdrs id).toAdrs tops = pr.ThLsf V.pk (pkAdrs id).toAdrs (V.tops id)

/-- **Event of F.8**: an `H` collision at the tree tweak of an internal node between the honest
children pair `(l, r)` and a different pair. -/
def E8 : Prop :=
  ∃ id, (treeAdrs id).toAdrs ∈ treeTweaks P.hsf V.S ∧
    ∃ l r, V.value (id.height - 1) (2 * id.index) = some l ∧
      V.value (id.height - 1) (2 * id.index + 1) = some r ∧
      ∃ l' r', (l', r') ≠ (l, r) ∧
        pr.H V.pk (treeAdrs id).toAdrs l' r' = pr.H V.pk (treeAdrs id).toAdrs l r

/-- **Event of F.9** (sm-tcr-excl with the partner map `ω` of Claim 4.9): at a node identifier
of the structure, a hash at the partner tweak collides with the honest hash. Either the honest
node is an anchor (honest `Th_lsf` at `T₃`) and the forged call is `H` at `ω⁻¹`, or the honest
node is internal (honest `H` on its children at `T₂`) and the forged call is `Th_lsf` at `ω`. -/
def E9 : Prop :=
  (∃ id, (pkAdrs id).toAdrs ∈ pkTweaks P.hsf V.S ∧
    ∃ l r, pr.H V.pk (omegaInv (pkAdrs id).toAdrs) l r =
      pr.ThLsf V.pk (pkAdrs id).toAdrs (V.tops id)) ∨
  (∃ id, (treeAdrs id).toAdrs ∈ treeTweaks P.hsf V.S ∧
    ∃ l r, V.value (id.height - 1) (2 * id.index) = some l ∧
      V.value (id.height - 1) (2 * id.index + 1) = some r ∧
      ∃ tops : Vector pr.Y P.lsf, pr.ThLsf V.pk (omega (treeAdrs id).toAdrs) tops =
        pr.H V.pk (treeAdrs id).toAdrs l r)

end HonestView

/-! ## Tweak-set membership -/

section Membership

variable {hsf : ℕ} {S : Structure} {id : LeafId}

theorem mem_leafIds_of (hz : id.height ≤ hsf) (h : Node.ofLeafId hsf id ∈ S.anchors) :
    id ∈ leafIds hsf S :=
  Finset.mem_image.2 ⟨_, h, Node.toLeafId_ofLeafId hz⟩

theorem pkAdrs_mem_pkTweaks (hz : id.height ≤ hsf) (h : Node.ofLeafId hsf id ∈ S.anchors) :
    (pkAdrs id).toAdrs ∈ pkTweaks hsf S :=
  Finset.mem_image.2 ⟨_, h, by rw [Node.toLeafId_ofLeafId hz]⟩

theorem grindAdrs_mem_grindTweaks (hz : id.height ≤ hsf)
    (h : Node.ofLeafId hsf id ∈ S.anchors) : (grindAdrs id).toAdrs ∈ grindTweaks hsf S :=
  Finset.mem_image.2 ⟨_, h, by rw [Node.toLeafId_ofLeafId hz]⟩

theorem treeAdrs_mem_treeTweaks (hz : id.height ≤ hsf)
    (h : Node.ofLeafId hsf id ∈ S.internal) : (treeAdrs id).toAdrs ∈ treeTweaks hsf S :=
  Finset.mem_image.2 ⟨_, h, by rw [Node.toLeafId_ofLeafId hz]⟩

theorem chainAdrs_mem_chainTweaks {lsf w ch p : ℕ} (hz : id.height ≤ hsf)
    (h : Node.ofLeafId hsf id ∈ S.anchors) (hch : ch < lsf) (hp : p < w - 1) :
    (chainAdrs id ch p).toAdrs ∈ chainTweaks hsf S lsf w :=
  Finset.mem_image.2 ⟨(Node.ofLeafId hsf id, ch, p), by simp [h, hch, hp], by
    simp only
    rw [Node.toLeafId_ofLeafId hz]⟩

end Membership

/-! ## The chain argument (F.5 / F.6) -/

/-- **Chain extraction** (Claim 4.10, last two cases): if a chain started at position `a` from `x`
and a chain started at a higher position `b > a` from the revealed block `y` end in the same value
at position `w − 1`, then either the forged chain value at `b − 1` is an `F`-preimage of `y`, or the
two chains collide under `F` at some position `p ∈ [b, w − 1)` from different inputs. -/
theorem chain_extract (pr : Primitives P) (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) {x y : pr.Y}
    {a b : ℕ} (hab : a < b) (hbw : b < P.w)
    (h : WotsC.chain pr pk id ch x a (P.w - 1 - a) = WotsC.chain pr pk id ch y b (P.w - 1 - b)) :
    (∃ u, pr.F pk (chainAdrs id ch (b - 1)).toAdrs u = y) ∨
    (∃ p, b ≤ p ∧ p < P.w - 1 ∧ ∃ u, u ≠ WotsC.chain pr pk id ch y b (p - b) ∧
      pr.F pk (chainAdrs id ch p).toAdrs u =
        pr.F pk (chainAdrs id ch p).toAdrs (WotsC.chain pr pk id ch y b (p - b))) := by
  set X : ℕ → pr.Y := fun p => WotsC.chain pr pk id ch x a (p - a) with hX
  set Hh : ℕ → pr.Y := fun p => WotsC.chain pr pk id ch y b (p - b) with hH
  have stepX : ∀ p, a ≤ p → X (p + 1) = pr.F pk (chainAdrs id ch p).toAdrs (X p) := by
    intro p hp
    simp only [hX]
    rw [show p + 1 - a = (p - a) + 1 by omega, WotsC.chain_succ, show a + (p - a) = p by omega]
  have stepH : ∀ p, b ≤ p → Hh (p + 1) = pr.F pk (chainAdrs id ch p).toAdrs (Hh p) := by
    intro p hp
    simp only [hH]
    rw [show p + 1 - b = (p - b) + 1 by omega, WotsC.chain_succ, show b + (p - b) = p by omega]
  have hHb : Hh b = y := by simp [hH]
  by_cases hXb : X b = y
  · refine Or.inl ⟨X (b - 1), ?_⟩
    rw [← stepX (b - 1) (by omega), show b - 1 + 1 = b by omega, hXb]
  · have hend : X (P.w - 1) = Hh (P.w - 1) := by simpa [hX, hH] using h
    have hbw' : b ≤ P.w - 1 := by omega
    obtain ⟨p, hbp, hpw, hne, heq⟩ := exists_last_ne hbw' (by rwa [hHb]) hend
    refine Or.inr ⟨p, hbp, hpw, X p, hne, ?_⟩
    rw [← stepX p (by omega), ← stepH p hbp, heq]

/-! ## Claim 4.10 -/

namespace HonestView

variable {pr : Primitives P} {V : HonestView pr}

/-- The honest signature at a signed anchor: target-sum encoded digest and anchor value
`Th_lsf(PK.seed, ADRS^pk_j, honest tops)`. -/
theorem Consistent.sig' (hV : V.Consistent) {id : LeafId} (h : id ∈ leafIds P.hsf V.S) :
    WotsC.TargetSum pr (V.encoded id) ∧
      V.leaf id = pr.ThLsf V.pk (pkAdrs id).toAdrs (V.tops id) :=
  (WotsC.pkFromSig_eq_some_iff pr).1 (hV.sig id h)

/-- **Claim 4.10 (deterministic core), honest-view form.** Let the honest view be consistent
(root `PK.sf`, every anchor signed with a signature recovering its anchor value, Remark 4.6). If a
forgery `(M̃*, (z*, i*), (R*, σ*))` verifies under `PK.sf` and `M̃*` differs from every signed
message, then one of the abort events of F.1, F.3, F.5, F.6, F.7, F.8, F.9 occurs. -/
theorem extraction [DecidableEq pr.Y] (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hV : V.Consistent) {Mf : List Byte} {idf : LeafId} {Rf : pr.Y} {σf : Scheme.Fxmss.Sig pr}
    (hver : Scheme.Fxmss.verifyMessage pr V.pk V.pkSf Mf idf Rf σf = true)
    (hfresh : ∀ id ∈ leafIds P.hsf V.S, Mf ≠ V.msg id) :
    V.E1 ∨ V.E3 ∨ V.E5 ∨ V.E6 ∨ V.E7 ∨ V.E8 ∨ V.E9 := by
  rw [Scheme.Fxmss.verifyMessage_eq_true_iff, Scheme.Fxmss.pkFromSig_eq_some_iff] at hver
  obtain ⟨⟨hz, hlen, hidx⟩, N0, hN0, hroot⟩ := hver
  obtain ⟨hTf, hN0⟩ := (WotsC.pkFromSig_eq_some_iff pr).1 hN0
  -- the climb reproduces the honest root
  have htop : V.value (idf.height + σf.auth.length) (idf.index / 2 ^ σf.auth.length) =
      some (Tree.climb (Scheme.Fxmss.node pr V.pk) idf.height idf.index N0 σf.auth) := by
    have hi : idf.index < 2 ^ σf.auth.length := by
      rw [hlen]
      exact lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))
    rw [← hroot, Nat.div_eq_of_lt hi, hlen, Nat.add_sub_cancel' hz.le]
    exact hV.root
  rcases climb_walk σf.auth _ _ N0 htop with
    ⟨id, hzid, hA, l, r, hlr⟩ | ⟨id, hzid, hI, l, r, hl, hr, l', r', hne, heq⟩ | hbot
  · -- `s = t* > 0`: tree-node hash at an anchor (F.9)
    have hleaf := (hV.sig' (mem_leafIds_of hzid hA)).2
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    exact ⟨id, pkAdrs_mem_pkTweaks hzid hA, l, r, hlr.trans hleaf⟩
  · -- `s > t*`: tree-node collision (F.8)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨id, treeAdrs_mem_treeTweaks hzid hI, l, r, hl, hr, l', r', hne, heq⟩)))))
  rcases treeNode_eq_some_cases hbot with ⟨-, hA, hx⟩ | ⟨z', hz', -, hI, l, r, hl, hr, hx⟩
  swap
  · -- `s = t* = 0` at an internal node: public-key compression in place of `H` (F.9)
    have hh : idf.height - 1 = z' := by omega
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
    exact ⟨idf, treeAdrs_mem_treeTweaks hz.le hI, l, r, by rw [hh]; exact hl,
      by rw [hh]; exact hr, _, hN0.symm.trans hx⟩
  -- `s = t* = 0` at an anchor: the WOTS+C cases
  have hmem := mem_leafIds_of hz.le hA
  obtain ⟨hTj, hleaf⟩ := hV.sig' hmem
  have hN : N0 = pr.ThLsf V.pk (pkAdrs idf).toAdrs (V.tops idf) := hx.trans hleaf
  by_cases hy : pr.HmsgSf Rf V.pk V.pkSf idf Mf = V.digest idf
  · -- equal digests (F.1)
    exact Or.inl ⟨idf, hmem, Rf, Mf, fun h => hfresh idf hmem (Prod.mk.inj h).2, hy⟩
  by_cases hd : WotsC.encode pr V.pk idf (pr.HmsgSf Rf V.pk V.pkSf idf Mf) σf.wots.ctr =
      V.encoded idf
  · -- equal encoded digests (F.3)
    exact Or.inr (Or.inl ⟨idf, grindAdrs_mem_grindTweaks hz.le hA, hTj, _, _, hy, hd⟩)
  obtain ⟨ch, hch, hlt⟩ := WotsC.exists_digit_lt_of_ne pr hP hinj hTf hTj hd
  by_cases ht : WotsC.topsFromSig pr V.pk idf
      (WotsC.encode pr V.pk idf (pr.HmsgSf Rf V.pk V.pkSf idf Mf) σf.wots.ctr) σf.wots =
      V.tops idf
  swap
  · -- different uncompressed public key (F.7)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨idf, pkAdrs_mem_pkTweaks hz.le hA, _, ht, hN0.symm.trans hN⟩))))
  -- equal uncompressed public key: chain `ch` starts below the honest block
  have hcomp := congrArg (fun t : Vector pr.Y P.lsf => t[ch]) ht
  simp only [HonestView.tops, WotsC.topsFromSig, Vector.getElem_ofFn] at hcomp
  have hbw := WotsC.digit_lt pr (V.encoded idf) ch
  rcases chain_extract pr V.pk idf ch hlt hbw hcomp with ⟨u, hu⟩ | ⟨p, hbp, hpw, u, hne, heq⟩
  · -- preimage of a revealed block (F.6)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨idf, ⟨ch, hch⟩,
      chainAdrs_mem_chainTweaks hz.le hA hch (by dsimp only; omega), by dsimp only; omega,
      u, hu⟩)))
  · -- chain collision (F.5)
    exact Or.inr (Or.inr (Or.inl ⟨idf, ⟨ch, hch⟩, p,
      chainAdrs_mem_chainTweaks hz.le hA hch hpw, hbp, u, hne, heq⟩))

/-! ## The secret-key model -/

/-- The honest view of key generation from the secret chain starts `sk` and signing queries
`(M_j, R_j) ↦ σ_j` at every leaf identifier. -/
def ofSigs (pr : Primitives P) (S : Structure) (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y)
    (pkSf : pr.Y) (M : LeafId → List Byte) (R : LeafId → pr.Y)
    (σ : LeafId → Scheme.Fxmss.Sig pr) : HonestView pr :=
  ⟨S, pk, pkSf, Scheme.Fxmss.leaf pr pk sk, M, R, fun id => (σ id).wots⟩

section OfSigs

variable (pr : Primitives P) {S : Structure} {pk : pr.PkSeed} {sk : LeafId → ℕ → pr.Y}
  {pkSf : pr.Y} {M : LeafId → List Byte} {R : LeafId → pr.Y} {σ : LeafId → Scheme.Fxmss.Sig pr}

/-- An honest FXMSS signature carries the honest WOTS+C signature of the anchor. -/
theorem wots_sign_of_signMessage {id : LeafId}
    (h : Scheme.Fxmss.signMessage pr S pk sk pkSf (R id) (M id) id = some (σ id)) :
    WotsC.sign pr pk id (sk id) (pr.HmsgSf (R id) pk pkSf id (M id)) = some (σ id).wots := by
  unfold Scheme.Fxmss.signMessage Scheme.Fxmss.sign at h
  split_ifs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, auth, -, hσ⟩ := h
  rw [hw, ← hσ]

/-- Honest key generation and signing give a consistent honest view. -/
theorem consistent_ofSigs (hroot : Scheme.Fxmss.root pr S pk sk = some pkSf)
    (hsig : ∀ id ∈ leafIds P.hsf S,
      Scheme.Fxmss.signMessage pr S pk sk pkSf (R id) (M id) id = some (σ id)) :
    (ofSigs pr S pk sk pkSf M R σ).Consistent where
  root := hroot
  sig id h := WotsC.pkFromSig_sign pr (wots_sign_of_signMessage pr (hsig id h))

/-- In the secret-key model, the honest uncompressed public key is `pk_i = c_{0,w−1}(sk_i)`. -/
theorem ofSigs_tops {id : LeafId}
    (h : Scheme.Fxmss.signMessage pr S pk sk pkSf (R id) (M id) id = some (σ id)) :
    (ofSigs pr S pk sk pkSf M R σ).tops id = WotsC.pkTops pr pk id (sk id) := by
  have hw := ((WotsC.sign_eq_some_iff pr).1 (wots_sign_of_signMessage pr h)).2
  simp only [HonestView.tops, HonestView.encoded, HonestView.digest, ofSigs]
  rw [hw]
  exact WotsC.topsFromSig_signWith pr _ _ _ _ _

/-- In the secret-key model, the revealed block is `σ_{j,ch} = c_{0,a_{j,ch}}(sk_{j,ch})`. -/
theorem ofSigs_block {id : LeafId}
    (h : Scheme.Fxmss.signMessage pr S pk sk pkSf (R id) (M id) id = some (σ id))
    (ch : Fin P.lsf) :
    (ofSigs pr S pk sk pkSf M R σ).block id ch =
      WotsC.chain pr pk id ch (sk id ch) 0
        (WotsC.digit pr ((ofSigs pr S pk sk pkSf M R σ).encoded id) ch) := by
  have hw := congrArg (fun s : WotsC.Sig pr => s.chains[ch.val])
    ((WotsC.sign_eq_some_iff pr).1 (wots_sign_of_signMessage pr h)).2
  simp only [HonestView.block, HonestView.encoded, HonestView.digest, ofSigs]
  refine hw.trans ?_
  simp [WotsC.signWith, WotsC.signChains]

/-- In the secret-key model, the honest chain value at position `p ≥ a_{j,ch}` is
`c_{0,p}(sk_{j,ch})`. -/
theorem ofSigs_chainValue {id : LeafId}
    (h : Scheme.Fxmss.signMessage pr S pk sk pkSf (R id) (M id) id = some (σ id))
    (ch : Fin P.lsf) {p : ℕ}
    (hp : WotsC.digit pr ((ofSigs pr S pk sk pkSf M R σ).encoded id) ch ≤ p) :
    (ofSigs pr S pk sk pkSf M R σ).chainValue id ch p = WotsC.chain pr pk id ch (sk id ch) 0 p := by
  have hc := WotsC.chain_compose pr pk id ch (sk id ch) 0
    (WotsC.digit pr ((ofSigs pr S pk sk pkSf M R σ).encoded id) ch)
    (p - WotsC.digit pr ((ofSigs pr S pk sk pkSf M R σ).encoded id) ch)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at hc
  rw [HonestView.chainValue, ofSigs_block pr h ch]
  exact hc

end OfSigs

/-- **Claim 4.10 (deterministic core).** Fix a structure `S`, `PK.seed`, the secret chain starts
`sk` with root `PK.sf`, and honest signatures `σ_j` of messages `M̃_j` with randomizers `R_j` at
every anchor (Remark 4.6). If the forgery `(M̃*, (z*, i*), (R*, σ*))` verifies under `PK.sf` and
`M̃*` differs from every signed message, then one of the abort events of F.1, F.3, F.5, F.6, F.7,
F.8 or F.9 occurs. Requires the injective digit encoding (`hinj`, "`d` is determined by its
digits"). -/
theorem claim_4_10 [DecidableEq pr.Y] (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    {S : Structure} {pk : pr.PkSeed} {sk : LeafId → ℕ → pr.Y} {pkSf : pr.Y}
    (hroot : Scheme.Fxmss.root pr S pk sk = some pkSf)
    {M : LeafId → List Byte} {R : LeafId → pr.Y} {σ : LeafId → Scheme.Fxmss.Sig pr}
    (hsig : ∀ id ∈ leafIds P.hsf S,
      Scheme.Fxmss.signMessage pr S pk sk pkSf (R id) (M id) id = some (σ id))
    {Mf : List Byte} {idf : LeafId} {Rf : pr.Y} {σf : Scheme.Fxmss.Sig pr}
    (hver : Scheme.Fxmss.verifyMessage pr pk pkSf Mf idf Rf σf = true)
    (hfresh : ∀ id ∈ leafIds P.hsf S, Mf ≠ M id) :
    (ofSigs pr S pk sk pkSf M R σ).E1 ∨ (ofSigs pr S pk sk pkSf M R σ).E3 ∨
      (ofSigs pr S pk sk pkSf M R σ).E5 ∨ (ofSigs pr S pk sk pkSf M R σ).E6 ∨
      (ofSigs pr S pk sk pkSf M R σ).E7 ∨ (ofSigs pr S pk sk pkSf M R σ).E8 ∨
      (ofSigs pr S pk sk pkSf M R σ).E9 :=
  extraction hP hinj (consistent_ofSigs pr hroot hsig) hver hfresh

end HonestView

end ShrincsSecurity.Fxmss
