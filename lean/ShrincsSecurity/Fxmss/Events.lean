module

public import ShrincsSecurity.Fxmss.Games

/-!
# The abort events of Theorem 4.2, read off the forgery

`SHRINCS-Security-Analysis.pdf`, Section 4.7: the abort events of the hops `F.2 → F.3` and
`F.4 → F.9`, in the **constructive** form the reductions need.

`Extraction.lean` states the events of Claim 4.10 existentially (`∃ x ≠ x', F(x) = F(x')`). As
events of a game that is too weak: a compressing function has collisions everywhere, so such an
event can hold without any forgery, and a reduction could not find its witness. Here every event
names its witness as a value **computed from the forgery** (and the honest data): the forged
encoded digest `d*`, the forged chain values, the forged uncompressed public key, and the values
`N_k` of the verifier's climb with the sibling pairs it hashes. Each existential ranges over a
bounded index (chain `ch < lsf`, position `p < w − 1`, step `k` of the authentication path), so a
reduction finds the witness by a finite search, and the winning condition of its game follows.

| event | hop | game | the forgery supplies |
|---|---|---|---|
| `E3` | F.2 → F.3 | S-TCR(Prop) of `H_grind` | `(y*, c*)` |
| `E5` | F.4 → F.5 | SM-TCR of `F` | the forged chain value at position `p` |
| `E6` | F.5 → F.6 | SM-PRE of `F` | the forged chain value at position `a_{j,i} − 1` |
| `E7` | F.6 → F.7 | SM-TCR of `Th_lsf` | the forged uncompressed public key |
| `E8` | F.7 → F.8 | SM-TCR of `H` | the sibling pair hashed at step `k` of the climb |
| `E9` | F.8 → F.9 | sm-tcr-excl of `Th_{2∪lsf}` | that pair (at an anchor), or the forged key (at an internal node) |

The event of `F.1` is `Transcript.C1` (equal digests at a signed leaf).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Scheme.SfAdrs
open ShrincsSecurity.Scheme.Structure (leafIds pkTweaks treeTweaks)

variable {P : Params} {pr : Primitives P} [Inhabited pr.Y]

namespace Honest

variable (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr)

/-! ## The verifier's recomputation of a forgery `(idf, y*, σ*)` -/

/-- The forged encoded digest `d* = H_grind(PK.seed, ADRS^g, y*, c*)`. -/
def fEnc : pr.Y := WotsC.encode pr H.pk idf yf w.wots.ctr

/-- The forged uncompressed public key, completed from the forged blocks. -/
def fTops : Vector pr.Y P.lsf := WotsC.topsFromSig pr H.pk idf (H.fEnc idf yf w) w.wots

/-- The recomputed anchor value `N₀ = Th_lsf(PK.seed, ADRS^pk, forged key)`. -/
def fN0 : pr.Y := pr.ThLsf H.pk (pkAdrs idf).toAdrs (H.fTops idf yf w)

/-- The forged value of chain `ch` at position `p ≥ a*_ch`. -/
def fChain (ch : Fin P.lsf) (p : ℕ) : pr.Y :=
  WotsC.chain pr H.pk idf ch.val w.wots.chains[ch.val]
    (WotsC.digit pr (H.fEnc idf yf w) ch.val) (p - WotsC.digit pr (H.fEnc idf yf w) ch.val)

/-- The position `v_k = (z* + k, ⌊i* / 2^k⌋)` reached after `k` steps of the climb. -/
def fPos (k : ℕ) : LeafId := ⟨idf.height + k, idf.index / 2 ^ k⟩

/-- The recomputed value `N_k` at `v_k`. -/
def fVal (k : ℕ) : pr.Y :=
  Tree.climb (Scheme.Fxmss.node pr H.pk) idf.height idf.index (H.fN0 idf yf w) (w.auth.take k)

/-- The pair `(left, right)` hashed at step `k` of the climb, into the value at `v_{k+1}`. -/
def fPair (k : ℕ) : pr.Y × pr.Y :=
  if (idf.index / 2 ^ k) % 2 = 0 then (H.fVal idf yf w k, w.auth.getD k default)
  else (w.auth.getD k default, H.fVal idf yf w k)

/-! ## The events -/

/-- **Event of F.3** (S-TCR(Prop) of `H_grind`): at a signed anchor, a forged digest `y* ≠ y_j`
with the honest encoded digest `H_grind(y*, c*) = H_grind(y_j, c_j)`. -/
def E3 : Prop :=
  idf ∈ leafIds P.hsf H.S ∧ yf ≠ H.dig idf ∧
    WotsC.encode pr H.pk idf yf w.wots.ctr = H.encoded idf

/-- **Event of F.5** (SM-TCR of `F`): at a signed anchor, chain `ch` and position `p` at or above
both digits, the forged chain value differs from the honest one and has the same `F`-image. -/
def E5 : Prop :=
  idf ∈ leafIds P.hsf H.S ∧ ∃ ch : Fin P.lsf, ∃ p < P.w - 1,
    WotsC.digit pr (H.encoded idf) ch.val ≤ p ∧ WotsC.digit pr (H.fEnc idf yf w) ch.val ≤ p ∧
    H.fChain idf yf w ch p ≠ H.chainValue idf ch p ∧
    pr.F H.pk (chainAdrs idf ch.val p).toAdrs (H.fChain idf yf w ch p) =
      pr.F H.pk (chainAdrs idf ch.val p).toAdrs (H.chainValue idf ch p)

/-- **Event of F.6** (SM-PRE of `F`): at a signed anchor, a chain started below the honest digit
`a_{j,ch} > 0` whose forged value at position `a_{j,ch} − 1` is an `F`-preimage of the revealed
block. -/
def E6 : Prop :=
  idf ∈ leafIds P.hsf H.S ∧ ∃ ch : Fin P.lsf,
    WotsC.digit pr (H.fEnc idf yf w) ch.val < WotsC.digit pr (H.encoded idf) ch.val ∧
    pr.F H.pk (chainAdrs idf ch.val (WotsC.digit pr (H.encoded idf) ch.val - 1)).toAdrs
      (H.fChain idf yf w ch (WotsC.digit pr (H.encoded idf) ch.val - 1)) = H.block idf ch

/-- **Event of F.7** (SM-TCR of `Th_lsf`): at a signed anchor, a forged uncompressed public key
different from the honest one with the same compression. -/
def E7 : Prop :=
  idf ∈ leafIds P.hsf H.S ∧ H.fTops idf yf w ≠ H.tops idf ∧
    pr.ThLsf H.pk (pkAdrs idf).toAdrs (H.fTops idf yf w) =
      pr.ThLsf H.pk (pkAdrs idf).toAdrs (H.tops idf)

/-- **Event of F.8** (SM-TCR of `H`): at step `k` the climb hashes, at an internal node of the
structure, a pair different from the honest children with the same node hash. -/
def E8 : Prop :=
  ∃ k < w.auth.length,
    (treeAdrs (fPos idf (k + 1))).toAdrs ∈ treeTweaks P.hsf H.S ∧
    ∃ l r, H.value (idf.height + k) (2 * (idf.index / 2 ^ (k + 1))) = some l ∧
      H.value (idf.height + k) (2 * (idf.index / 2 ^ (k + 1)) + 1) = some r ∧
      H.fPair idf yf w k ≠ (l, r) ∧
      pr.H H.pk (treeAdrs (fPos idf (k + 1))).toAdrs (H.fPair idf yf w k).1
          (H.fPair idf yf w k).2 =
        pr.H H.pk (treeAdrs (fPos idf (k + 1))).toAdrs l r

/-- **Event of F.9** (sm-tcr-excl of `Th_{2∪lsf}` with the partner map `ω`): either the climb
hashes, with `H` at `ω⁻¹(ADRS^pk_v)`, a pair onto the honest compressed public key of an anchor
`v` of the structure, or the forged anchor `(z*, i*)` is an internal node of the structure and the
forged compression at `ω(ADRS^tr)` equals the honest node hash of its children. -/
def E9 : Prop :=
  (∃ k < w.auth.length,
    (pkAdrs (fPos idf (k + 1))).toAdrs ∈ pkTweaks P.hsf H.S ∧
    pr.H H.pk (treeAdrs (fPos idf (k + 1))).toAdrs (H.fPair idf yf w k).1
        (H.fPair idf yf w k).2 =
      pr.ThLsf H.pk (pkAdrs (fPos idf (k + 1))).toAdrs (H.tops (fPos idf (k + 1)))) ∨
  ((treeAdrs idf).toAdrs ∈ treeTweaks P.hsf H.S ∧
    ∃ l r, H.value (idf.height - 1) (2 * idf.index) = some l ∧
      H.value (idf.height - 1) (2 * idf.index + 1) = some r ∧
      H.fN0 idf yf w = pr.H H.pk (treeAdrs idf).toAdrs l r)

end Honest

variable {Msg : Type} [DecidableEq pr.Y]

/-! ## Events of the game outputs -/

/-- The forger wins in a game with output `o`. -/
def WinO : Option (Transcript pr Msg) → Prop
  | some tr => tr.Win
  | none => False

/-- The forger wins and the abort event of F.1 occurs. -/
def WinC1 : Option (Transcript pr Msg) → Prop
  | some tr => tr.Win ∧ tr.C1
  | none => False

/-- The forger wins and the abort event of F.1 does not occur (success in `F.1`). -/
def WinNotC1 : Option (Transcript pr Msg) → Prop
  | some tr => tr.Win ∧ ¬ tr.C1
  | none => False

/-- An event of the honest data and the forgery `(idf, y*, σ*_tree)`, on a block game's output;
a `⊥` forgery signature satisfies no event. -/
def HybEvent (E : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → Prop) :
    Option (Transcript pr Msg × Honest pr) → Prop
  | some (tr, H) => ∃ w, tr.σf.2 = some w ∧ E H tr.idf tr.yf w
  | none => False

end ShrincsSecurity.Fxmss.Rom

end
