module

public import ShrincsSecurity.Fxmss.Events

/-!
# Claim 4.10, constructive form

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.10** (`Succ^{F.9}(A) = 0`, txt lines
~3833–3880), for the honest data `Honest` of the block games and the abort events of
`Events.lean`, whose witnesses are computed from the forgery.

Let the honest data be consistent (the tree has a root, and every anchor's honest WOTS+C signature
recovers its anchor value under its digest `y_j`) and let a forgery `(idf, y*, σ*)` recover the
root `PK.sf`. If the forgery is not the abort event of F.1 at a signed anchor (`y* = y_j`), one of
the events `E3, E5, E6, E7, E8, E9` occurs (`Honest.claim_4_10`).

## The proof

The verifier's climb visits the positions `v_k = fPos k` with values `N_k = fVal k`; at the root
(`k = |auth|`) the value is honest. Let `s` be the **least** `k ≤ |auth|` at which the honest value
at `v_k` is `N_k`.

* `s > 0`: the honest node `v_s` is an anchor (the verifier hashes with `H` a pair onto the
  honest compressed key: `E9`, left), or internal with children different from the hashed pair
  by minimality of `s` (`E8`).
* `s = 0`, `idf` internal: the forged compression equals the honest node hash (`E9`, right).
* `s = 0`, `idf` an anchor: equal compressions with different uncompressed keys (`E7`); otherwise
  `y* ≠ y_j` (no F.1 event), equal encoded digests (`E3`), or a chain `ch` starting below the
  honest digit (`WotsC.exists_digit_lt_of_ne`) ending in the honest endpoint: either its value at
  `a_{j,ch} − 1` is a preimage of the block (`E6`), or the last disagreement before the endpoint
  is an `F`-collision (`E5`).

## Deviations from the printed proof

* The paper's two minimisations (least `t*` entering `A ∪ I`, least `s ≥ t*` with honest
  agreement) are one minimisation (`s`): agreement with an honest value already certifies
  membership in `A ∪ I` (`treeNode_eq_some_cases`).
* The F.1 event (`y* = y_j` at a signed anchor) is a hypothesis (`hc1`), excluded in the games by
  the transcript event `Transcript.C1`.
* "`d` is determined by its digits" needs `hinj` (injective `yToBytes`) and `hP` (`lgw ∣ n`).
-/

@[expose] public section

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Scheme.SfAdrs
open ShrincsSecurity.Scheme.Structure (leafIds pkTweaks treeTweaks)

variable {P : Params} {pr : Primitives P}

/-- Climbing along a concatenated path climbs the first part, then the second from the reached
position. -/
theorem climb_append {Y : Type} (node : LeafId → Y → Y → Y) :
    ∀ (xs ys : List Y) (z i : ℕ) (N : Y),
      Tree.climb node z i N (xs ++ ys) =
        Tree.climb node (z + xs.length) (i / 2 ^ xs.length) (Tree.climb node z i N xs) ys
  | [], ys, z, i, N => by simp
  | a :: xs, ys, z, i, N => by
    rw [List.cons_append, Tree.climb_cons, Tree.climb_cons, climb_append node xs ys,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ', List.length_cons,
      show z + 1 + xs.length = z + (xs.length + 1) by omega]

namespace Honest

variable (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr)

theorem fVal_zero : H.fVal idf yf w 0 = H.fN0 idf yf w := by simp [fVal]

theorem fVal_length : H.fVal idf yf w w.auth.length =
    Tree.climb (Scheme.Fxmss.node pr H.pk) idf.height idf.index (H.fN0 idf yf w) w.auth := by
  simp [fVal]

variable [Inhabited pr.Y]

/-- One step of the verifier's climb: `N_{k+1} = H(ADRS^tr_{v_{k+1}}, pair_k)`. -/
theorem fVal_succ {k : ℕ} (hk : k < w.auth.length) :
    H.fVal idf yf w (k + 1) = pr.H H.pk (treeAdrs (fPos idf (k + 1))).toAdrs
      (H.fPair idf yf w k).1 (H.fPair idf yf w k).2 := by
  have htake : w.auth.take (k + 1) = w.auth.take k ++ [w.auth[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hlen : (w.auth.take k).length = k := by simp; omega
  have hget : w.auth.getD k default = w.auth[k] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hpos : fPos idf (k + 1) = ⟨idf.height + k + 1, idf.index / 2 ^ k / 2⟩ := by
    simp only [fPos, Nat.div_div_eq_div_mul, ← Nat.pow_succ, Nat.add_assoc]
  unfold fPair
  rw [fVal, htake, climb_append, hlen, Tree.climb_cons, Tree.climb_nil, hget, hpos]
  split_ifs <;> rfl

/-- **Claim 4.10, constructive.** Let the honest data be consistent and let the forgery
`(idf, y*, σ*_tree)` recover the honest root `PK.sf`. Unless `idf` is an anchor signed with the
digest `y_j = y*` (the abort event of F.1), one of the abort events of F.3, F.5, F.6, F.7, F.8, F.9
occurs, with witnesses computed from the forgery (`SHRINCS-Security-Analysis.pdf`, Claim 4.10). -/
theorem claim_4_10 (hP : P.Valid) (hinj : Function.Injective pr.yToBytes) {H : Honest pr}
    (hH : H.Consistent) {idf : LeafId} {yf : pr.Digest} {w : Scheme.Fxmss.Sig pr}
    (hver : Scheme.Fxmss.pkFromSig pr H.pk yf idf w = some H.pkSf)
    (hc1 : ¬ (idf ∈ leafIds P.hsf H.S ∧ yf = H.dig idf)) :
    H.E3 idf yf w ∨ H.E5 idf yf w ∨ H.E6 idf yf w ∨ H.E7 idf yf w ∨ H.E8 idf yf w ∨
      H.E9 idf yf w := by
  classical
  obtain ⟨⟨hz, hlen, hidx⟩, N0, hN0, hroot⟩ := Scheme.Fxmss.pkFromSig_eq_some_iff.1 hver
  obtain ⟨hTf, hN0⟩ := (WotsC.pkFromSig_eq_some_iff pr).1 hN0
  have hN0' : N0 = H.fN0 idf yf w := hN0
  subst hN0'
  -- the climb reproduces the honest root
  have htop : H.value (idf.height + w.auth.length) (idf.index / 2 ^ w.auth.length) =
      some (H.fVal idf yf w w.auth.length) := by
    have hi : idf.index < 2 ^ w.auth.length := by
      rw [hlen]
      exact lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hH.root
    have hpk : H.pkSf = r := by simp [Honest.pkSf, hr]
    rw [Nat.div_eq_of_lt hi, fVal_length, ← hroot, hlen, Nat.add_sub_cancel' hz.le, hr, hpk]
  -- the least agreement index `s`
  have hex : ∃ k, k ≤ w.auth.length ∧
      H.value (idf.height + k) (idf.index / 2 ^ k) = some (H.fVal idf yf w k) :=
    ⟨_, le_rfl, htop⟩
  obtain ⟨hsle, hsv⟩ := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, ¬ (k ≤ w.auth.length ∧
      H.value (idf.height + k) (idf.index / 2 ^ k) = some (H.fVal idf yf w k)) :=
    fun k hk => Nat.find_min hex hk
  generalize Nat.find hex = s at hsle hsv hmin
  cases s with
  | succ k =>
    have hk : k < w.auth.length := by omega
    rw [fVal_succ H idf yf w hk] at hsv
    rcases treeNode_eq_some_cases hsv with ⟨hzle, hA, hx⟩ | ⟨z', hz', hzle, hI, l, r, hl, hr, hx⟩
    · -- `s > 0` at an anchor: `H` onto an honest compressed key (F.9)
      have hmem : fPos idf (k + 1) ∈ leafIds P.hsf H.S := mem_leafIds_of hzle hA
      have hleaf := ((WotsC.pkFromSig_eq_some_iff pr).1 (hH.sig _ hmem)).2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, hk, pkAdrs_mem_pkTweaks hzle hA, hx.trans hleaf⟩)))))
    · -- `s > 0` at an internal node: a tree-node collision (F.8)
      obtain rfl : z' = idf.height + k := by omega
      have hdiv : idf.index / 2 ^ (k + 1) = idf.index / 2 ^ k / 2 := by
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, hk, treeAdrs_mem_treeTweaks hzle hI, l, r, hl, hr, ?_, hx⟩))))
      intro heq
      refine hmin k (by omega) ⟨hk.le, ?_⟩
      unfold fPair at heq
      split_ifs at heq with hev
      · obtain ⟨h1, -⟩ := Prod.mk.inj heq
        rw [h1, show idf.index / 2 ^ k = 2 * (idf.index / 2 ^ (k + 1)) by omega]
        exact hl
      · obtain ⟨-, h2⟩ := Prod.mk.inj heq
        rw [h2, show idf.index / 2 ^ k = 2 * (idf.index / 2 ^ (k + 1)) + 1 by omega]
        exact hr
  | zero =>
    simp only [Nat.add_zero, pow_zero, Nat.div_one, fVal_zero] at hsv
    rcases treeNode_eq_some_cases hsv with ⟨hzle, hA, hx⟩ | ⟨z', hz', hzle, hI, l, r, hl, hr, hx⟩
    swap
    · -- `s = 0` at an internal node: a compression onto an honest node hash (F.9)
      obtain rfl : z' = idf.height - 1 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨treeAdrs_mem_treeTweaks hzle hI, l, r, hl, hr, hx⟩)))))
    -- `s = 0` at an anchor: the WOTS+C cases
    have hmem : idf ∈ leafIds P.hsf H.S := mem_leafIds_of hzle hA
    obtain ⟨hTj, hleaf⟩ := (WotsC.pkFromSig_eq_some_iff pr).1 (hH.sig _ hmem)
    by_cases ht : H.fTops idf yf w = H.tops idf
    swap
    · -- different uncompressed public key (F.7)
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hmem, ht, hx.trans hleaf⟩)))
    have hy : yf ≠ H.dig idf := fun h => hc1 ⟨hmem, h⟩
    by_cases hd : WotsC.encode pr H.pk idf yf w.wots.ctr = H.encoded idf
    · -- equal encoded digests (F.3)
      exact Or.inl ⟨hmem, hy, hd⟩
    obtain ⟨c, hlt⟩ : ∃ c : Fin P.lsf,
        WotsC.digit pr (H.fEnc idf yf w) c.val < WotsC.digit pr (H.encoded idf) c.val := by
      obtain ⟨ch, hch, hlt⟩ := WotsC.exists_digit_lt_of_ne pr hP hinj hTf hTj hd
      exact ⟨⟨ch, hch⟩, hlt⟩
    have hbw : WotsC.digit pr (H.encoded idf) c.val < P.w := WotsC.digit_lt pr _ _
    have hcomp : H.fChain idf yf w c (P.w - 1) = H.chainValue idf c (P.w - 1) := by
      have := congrArg (fun t : Vector pr.Y P.lsf => t[c.val]) ht
      simp only [fTops, Honest.tops, WotsC.topsFromSig, Vector.getElem_ofFn] at this
      exact this
    have stepF : ∀ p, WotsC.digit pr (H.fEnc idf yf w) c.val ≤ p →
        H.fChain idf yf w c (p + 1) =
          pr.F H.pk (chainAdrs idf c.val p).toAdrs (H.fChain idf yf w c p) := by
      intro p hp
      simp only [fChain]
      rw [Nat.sub_add_comm hp, WotsC.chain_succ, Nat.add_sub_cancel' hp]
    have stepH : ∀ p, WotsC.digit pr (H.encoded idf) c.val ≤ p →
        H.chainValue idf c (p + 1) =
          pr.F H.pk (chainAdrs idf c.val p).toAdrs (H.chainValue idf c p) := by
      intro p hp
      simp only [Honest.chainValue]
      rw [Nat.sub_add_comm hp, WotsC.chain_succ, Nat.add_sub_cancel' hp]
    have hHb : H.chainValue idf c (WotsC.digit pr (H.encoded idf) c.val) = H.block idf c := by
      simp [Honest.chainValue]
    by_cases hXb : H.fChain idf yf w c (WotsC.digit pr (H.encoded idf) c.val) = H.block idf c
    · -- the forged chain hits the revealed block: a preimage (F.6)
      refine Or.inr (Or.inr (Or.inl ⟨hmem, c, hlt, ?_⟩))
      rw [← stepF _ (by omega), Nat.sub_add_cancel (by omega)]
      exact hXb
    · -- the last disagreement before the endpoint: a chain collision (F.5)
      obtain ⟨p, hbp, hpw, hne, heq⟩ := exists_last_ne (x := fun p => H.fChain idf yf w c p)
        (h := fun p => H.chainValue idf c p) (b := WotsC.digit pr (H.encoded idf) c.val)
        (m := P.w - 1) (by omega) (by rwa [hHb]) hcomp
      refine Or.inr (Or.inl ⟨hmem, c, p, hpw, hbp, by omega, hne, ?_⟩)
      rw [← stepF p (by omega), ← stepH p hbp]
      exact heq

end Honest

end ShrincsSecurity.Fxmss.Rom

end
