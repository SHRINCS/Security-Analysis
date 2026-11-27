module

public import ShrincsSecurity.Fxmss.HybCommon

/-!
# Claim 4.6: the preimage event in `F.4` (SM-PRE of `F`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.6** (reduction `B₅`, Algorithm 9).

In `F.4 = H_{w−2}` (`gameHyb (w − 2)`) the revealed block of chain `i` at anchor `j` with digit
`a = a_{j,i} > 0` is `F(chainAdrs(j, i, a − 1), u_{j,i})` for a uniform `u_{j,i}`, and `u_{j,i}`
itself when `a = 0`. The reduction `B₅` (SM-PRE of `F ∈ Th_λ`, `L · lsf` targets) samples the
setup, grinds every anchor through the collection oracle, and queries the challenge oracle at
`chainAdrs(j, i, a − 1)` for every anchor and chain with `a > 0`: the answer `F(·, x)` for the
challenger's hidden uniform `x` is the block. Its second stage simulates the signing phase with
these blocks and, on the event `E6` (a forged chain value at position `a − 1` that is an
`F`-preimage of the block), outputs the target index of that chain and the forged value.

`B5_le` (equivalently `claim_4_6`): the blocks of `B₅`'s simulation are distributed as in `F.4`
(`blockVal_top`: `c_{a−1,1}(u) = F(chainAdrs(a − 1), u)`, coupling and resampling of the table),
and `E6` implies that `B₅` wins. Under Conjecture 3.1 every anchor's digest grinds, so the honest
encoded digest is the one `B₅` found and the event's chain is a target.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions
open ShrincsSecurity.Scheme.Structure (leafIds)
open ShrincsSecurity.Scheme.Grinding (GrindComplete grindComplete_iff)
open Hyb

namespace Hyb

/-! ## Block identities and honest data -/

section Lemmas

variable {P : Params} {pr : Primitives P}

/-- The block of `F.4 = H_{w−2}` at digit `0 < a < w` is `F(chainAdrs(a − 1), v)`. -/
theorem blockVal_top (pk : pr.PkSeed) (id : LeafId) (ch a : ℕ) (v : pr.Y) (h0 : 0 < a)
    (hw : a < P.w) :
    blockVal pr pk id ch (P.w - 2) a v = pr.F pk (SfAdrs.chainAdrs id ch (a - 1)).toAdrs v := by
  unfold blockVal
  rw [min_eq_right (by omega : a - 1 ≤ P.w - 2), show a - (a - 1) = 0 + 1 by omega,
    WotsC.chain_succ, WotsC.chain_zero]
  rfl

/-- The block of any hybrid at digit `0` is the table value. -/
theorem blockVal_zero (pk : pr.PkSeed) (id : LeafId) (ch γ : ℕ) (v : pr.Y) :
    blockVal pr pk id ch γ 0 v = v := by
  simp [blockVal]

theorem relDigOf_lt (g : Option (pr.Y × Fin (2 ^ P.c))) (ch : ℕ) : relDigOf pr g ch < P.w := by
  cases g with
  | none => exact P.w_pos
  | some dc => exact WotsC.digit_lt pr _ _

/-- Under Conjecture 3.1 every anchor of a valid structure grinds. -/
theorem grind_ne_none (hP : P.Valid) (hgc : GrindComplete pr) {S : Structure}
    (hS : S.TreeValid P.hsf) (pk : pr.PkSeed) {id : LeafId} (hid : id ∈ leafIds P.hsf S)
    (md : pr.Digest) : WotsC.grind pr pk id md ≠ none := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
  have h1 : P.hsf - v.depth < 256 := by have := hP.hsf_le; omega
  have h2 : v.idx < 2 ^ 64 := hS.anchor_idx_lt v hv
  exact (grindComplete_iff pr).1 hgc pk (⟨_, h1⟩, ⟨_, h2⟩) md

theorem hon_wots_of_grind {S : Structure} {pk : pr.PkSeed} {dig : LeafId → pr.Digest}
    {β : LeafId → ℕ → ℕ → pr.Y} {id : LeafId} {d : pr.Y} {c : Fin (2 ^ P.c)}
    (h : WotsC.grind pr pk id (dig id) = some (d, c)) :
    (hon pr S pk dig β).wots id = blockSig pr β id d c := by
  simp [hon, h]

theorem hon_encoded_of_grind {S : Structure} {pk : pr.PkSeed} {dig : LeafId → pr.Digest}
    {β : LeafId → ℕ → ℕ → pr.Y} {id : LeafId} {d : pr.Y} {c : Fin (2 ^ P.c)}
    (h : WotsC.grind pr pk id (dig id) = some (d, c)) :
    (hon pr S pk dig β).encoded id = d := by
  rw [Honest.encoded, hon_wots_of_grind h]
  exact ((WotsC.grind_eq_some_iff pr).1 h).1.symm

theorem hon_block_of_grind {S : Structure} {pk : pr.PkSeed} {dig : LeafId → pr.Digest}
    {β : LeafId → ℕ → ℕ → pr.Y} {id : LeafId} {d : pr.Y} {c : Fin (2 ^ P.c)}
    (h : WotsC.grind pr pk id (dig id) = some (d, c)) (ch : Fin P.lsf) :
    (hon pr S pk dig β).block id ch = β id ch (WotsC.digit pr d ch) := by
  simp [Honest.block, hon_wots_of_grind h, blockSig]

end Lemmas

end Hyb

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

namespace Hyb

/-! ## The reduction `B₅` -/

/-- The targets of `B₅`: chains with `a > 0`, queried at hash address `a − 1`. -/
def selPre (a : ℕ) : Option ℕ := if 0 < a then some (a - 1) else none

variable {pr Msg} in
/-- The inner condition of `E6` at chain `ch`. -/
def e6At (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr)
    (ch : Fin P.lsf) : Prop :=
  WotsC.digit pr (H.fEnc idf yf w) ch.val < WotsC.digit pr (H.encoded idf) ch.val ∧
    pr.F H.pk (SfAdrs.chainAdrs idf ch.val (WotsC.digit pr (H.encoded idf) ch.val - 1)).toAdrs
      (H.fChain idf yf w ch (WotsC.digit pr (H.encoded idf) ch.val - 1)) = H.block idf ch

/-- The output of `B₅` from a run of the block game: for the forgery's leaf and the first chain
`ch` satisfying `E6`, the index of the target `(idf, ch)` at `chainAdrs(idf, ch, a − 1)` and the
forged chain value at position `a − 1`. -/
noncomputable def extract5 (pk : pr.PkSeed) {S : Structure} (ys : Anchor P S → pr.Digest)
    (o : Option (Transcript pr Msg × Honest pr)) : ℕ × pr.Y :=
  match o with
  | some (tr, H) =>
    match tr.σf.2 with
    | some w =>
      if hid : tr.idf ∈ leafIds P.hsf S then
        match (List.finRange P.lsf).find? (fun ch => decide (e6At H tr.idf tr.yf w ch)) with
        | some ch =>
          ((targets pr pk selPre S ys).idxOf ((⟨tr.idf, hid⟩, ch),
              (SfAdrs.chainAdrs tr.idf ch.val
                (WotsC.digit pr (H.encoded tr.idf) ch.val - 1)).toAdrs),
            H.fChain tr.idf tr.yf w ch (WotsC.digit pr (H.encoded tr.idf) ch.val - 1))
        | none => (0, default)
      else (0, default)
    | none => (0, default)
  | none => (0, default)

/-- The second stage of `B₅`: the signing phase with the challenge answers as blocks, then the
extraction. -/
noncomputable def inv5 {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (pk : pr.PkSeed) : ProbComp (ℕ × pr.Y) :=
  extract5 pr Msg pk d.ys <$>
    stageHyb pr Msg slKeygen A (fun id ch _ => skOf pr d.S d.u id ch) d pk

end Hyb

/-- **The reduction `B₅` of Claim 4.6** (Algorithm 9; SM-PRE of `F ∈ Th_λ`, `q₁ ≤ L · lsf`
targets): the shared first stage with a challenge query at `chainAdrs(j, i, a_{j,i} − 1)` for
every anchor `j` and chain `i` with `a_{j,i} > 0` (answers written into the table, which then
holds the blocks), then the signing phase with these blocks and the extraction of a preimage
from the event `E6`. -/
noncomputable def B5 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_PRE_Adversary (probPre pr (L * P.lsf)) :=
  preAdv pr Msg slKeygen selPre A (inv5 pr Msg slKeygen A.toFxmssAdversary)

namespace Hyb

/-! ## The event `E6` makes `B₅` win -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
theorem mem_support_stageHyb {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed)
    {tr : Transcript pr Msg} {H : Honest pr}
    (ho : some (tr, H) ∈ support (stageHyb pr Msg slKeygen A β d pk)) :
    d.S.TreeValid P.hsf ∧ H = hon pr d.S pk (digOf pr d.ys) β := by
  unfold stageHyb at ho
  by_cases hS : d.S.TreeValid P.hsf
  · simp only [hS, not_true_eq_false, ite_false, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨-, -, -, -, -, rfl⟩ := ho
    exact ⟨hS, rfl⟩
  · simp [hS] at ho

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- **`E6` implies that `B₅` wins** (Conjecture 3.1 makes the forgery's anchor grind, so its
honest digit is the one `B₅` used, and the event's chain is a target whose block is the
challenge image `F(chainAdrs(a − 1), x)`). -/
theorem preWin_of_E6 (hP : P.Valid) (hgc : GrindComplete pr) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) (pk : pr.PkSeed)
    (d : Setup pr Msg A.State)
    (z : (SkIdx P d.S → pr.Y) × List (SLHDSA.Adrs × pr.Y))
    (hz : z ∈ support (runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
      (targets pr pk selPre d.S d.ys) d.u []))
    (o : Option (Transcript pr Msg × Honest pr))
    (ho : o ∈ support (stageHyb pr Msg slKeygen A (fun id ch _ => skOf pr d.S z.1 id ch) d pk))
    (hE : HybEvent Honest.E6 o) :
    preWin pr pk z.2 (extract5 pr Msg pk d.ys o) = true := by
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := mem_support_stageHyb pr Msg slKeygen A _ d pk ho
  obtain ⟨w, hw, hid, ch, hch⟩ := hE
  have hex : ∃ ch, e6At (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch)
      tr.idf tr.yf w ch := ⟨ch, hch⟩
  obtain ⟨ch', hch'⟩ : ∃ ch', (List.finRange P.lsf).find? (fun ch => decide (e6At
      (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch)
        tr.idf tr.yf w ch)) = some ch' := by
    refine Option.isSome_iff_exists.1 ?_
    rw [List.find?_isSome]
    exact ⟨ch, List.mem_finRange _, decide_eq_true hch⟩
  have he' : e6At (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch)
      tr.idf tr.yf w ch' := by
    simpa using List.find?_some hch'
  have hid' : tr.idf ∈ leafIds P.hsf d.S := hid
  obtain ⟨⟨dE, c⟩, hg⟩ := Option.ne_none_iff_exists'.1
    (grind_ne_none hP hgc hS pk hid' (digOf pr d.ys tr.idf))
  simp only [extract5, hw, hid', ↓reduceDIte, hch']
  unfold e6At at he'
  rw [hon_encoded_of_grind hg] at he'
  rw [hon_encoded_of_grind hg]
  obtain ⟨hlt, hF⟩ := he'
  rw [hon_block_of_grind hg, skOf_anchor pr z.1 hid'] at hF
  set a := WotsC.digit pr dE ch'.val with ha
  have ha0 : 0 < a := by omega
  have hmem : ((⟨tr.idf, hid'⟩, ch'), (SfAdrs.chainAdrs tr.idf ch'.val (a - 1)).toAdrs) ∈
      targets pr pk selPre d.S d.ys := by
    simp only [targets, hS, ite_true]
    refine (mem_targetsOf pr).2 ⟨a - 1, ?_, rfl⟩
    have hr : relDigOf pr (WotsC.grind pr pk tr.idf (digOf pr d.ys tr.idf)) ch'.val = a := by
      rw [hg]
      rfl
    simp only [hr, selPre, ha0, ite_true]
  have hnd : ((targets pr pk selPre d.S d.ys).map Prod.fst).Nodup := by
    simp only [targets, hS, ite_true]
    exact nodup_map_fst_targetsOf pr _ _
  obtain ⟨-, -, h3⟩ := runRef_spec _ _ _ _ _ z hz hnd
  have hjlt := List.idxOf_lt_length_of_mem hmem
  obtain ⟨x, hx1, hx2⟩ := h3 _ hjlt
  rw [List.getElem_idxOf hjlt] at hx1 hx2
  simp only [List.length_nil, Nat.zero_add] at hx2
  simp only [preWin, hx2, decide_eq_true_eq]
  simp only at hx1
  rw [← hx1]
  exact hF

/-! ## Claim 4.6 -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- `F.4` with the table resampled at `B₅`'s targets, and the blocks written as the challenge
images `F(chainAdrs(a − 1), x)` of fresh uniform `x`. -/
theorem gameTop_evalDistEq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    (fun o => decide (HybEvent Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let w ← fillWith (fun t x => pr.F pk t x) (targets pr pk selPre d.S d.ys) d.u
          evE6 pr Msg slKeygen A.toFxmssAdversary d pk w) := by
  rw [gameHyb_E6]
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.trans (setupHyb_resample pr slKeygen A.toFxmssAdversary
    (fun S ys => targets pr pk selPre S ys)
    (fun d w => evE6 pr Msg slKeygen A.toFxmssAdversary d pk (viewOf pr (P.w - 2) pk d.ys w))
    fun _ _ _ _ _ _ _ => rfl).symm (evalDistEq_of_eq ?_)
  refine bind_congr fun d => ?_
  by_cases hS : d.S.TreeValid P.hsf
  · have hl : ∀ pt ∈ targets pr pk selPre d.S d.ys, ∀ x,
        blockVal pr pk pt.1.1.1 pt.1.2.val (P.w - 2)
          (relDig pr pk (digOf pr d.ys) pt.1.1.1 pt.1.2.val) x =
        (fun t x => pr.F pk t x) pt.2 x := by
      rintro ⟨p, t⟩ hpt x
      simp only [targets, hS, ite_true] at hpt
      obtain ⟨j, hj, rfl⟩ := (mem_targetsOf pr).1 hpt
      simp only [selPre] at hj
      split_ifs at hj with h0
      cases hj
      exact blockVal_top pk _ _ _ x h0 (relDigOf_lt _ _)
    have hoff : ∀ q, q ∉ (targets pr pk selPre d.S d.ys).map Prod.fst →
        blockVal pr pk q.1.1 q.2.val (P.w - 2) (relDig pr pk (digOf pr d.ys) q.1.1 q.2.val)
          (d.u q) = d.u q := by
      intro q hq
      simp only [targets, hS, ite_true, mem_map_fst_targetsOf, selPre] at hq
      have h0 : relDig pr pk (digOf pr d.ys) q.1.1 q.2.val = 0 := by
        rw [relDig]
        by_contra hne
        exact hq (by simp [Nat.pos_of_ne_zero hne])
      rw [h0, blockVal_zero]
    have hc := fillWith_couple (fun _ x => x) (fun t x => pr.F pk t x)
      (fun q y => blockVal pr pk q.1.1 q.2.val (P.w - 2)
        (relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) y)
      (fun _ y => y) (evE6 pr Msg slKeygen A.toFxmssAdversary d pk) _ hl d.u d.u hoff
    exact hc
  · simp only [targets, hS, ite_false, pure_bind, fillWith, evE6_invalid pr slKeygen _ d hS]

end Hyb

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- **Claim 4.6** (`F.4`, SM-PRE of `F ∈ Th_λ`, `q₁ ≤ L · lsf`): the event `E6` in `F.4` is
bounded by the success of `B₅`. -/
theorem claim_4_6 (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary}[HybEvent Honest.E6 o] ≤
      SM_DT_PRE_Advantage (B5 pr Msg slKeygen A) := by
  rw [prE6_gameHyb pr slKeygen, (gameTop_evalDistEq pr Msg slKeygen A).evalDist_eq,
    SM_DT_PRE_Advantage, B5, (preExp_evalDistEq pr slKeygen selPre A _).evalDist_eq]
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
    fun pk _ => ?_
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
    fun d _ => ?_
  rw [← map_fst_runRef (fun t x => pr.F pk t x) (fun t x => (t, x)), bind_map_left]
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
    fun z hz => ?_
  have e₁ : evE6 pr Msg slKeygen A.toFxmssAdversary d pk z.1 =
      stageHyb pr Msg slKeygen A.toFxmssAdversary (fun id ch _ => skOf pr d.S z.1 id ch) d pk >>=
        fun o => pure (decide (HybEvent Honest.E6 o)) := by
    rw [evE6, map_eq_bind_pure_comp]
    rfl
  have e₂ : (inv5 pr Msg slKeygen A.toFxmssAdversary {d with u := z.1} pk >>= fun jm =>
      (pure (preWin pr pk z.2 jm) : ProbComp Bool)) =
      stageHyb pr Msg slKeygen A.toFxmssAdversary (fun id ch _ => skOf pr d.S z.1 id ch) d pk >>=
        fun o => pure (preWin pr pk z.2 (extract5 pr Msg pk d.ys o)) := by
    rw [inv5, bind_map_left]
    rfl
  rw [e₁, e₂]
  refine evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
    fun o ho => ?_
  by_cases hE : HybEvent Honest.E6 o
  · rw [decide_eq_true hE, preWin_of_E6 pr Msg slKeygen hP hgc _ pk d z hz o ho hE]
  · rw [decide_eq_false hE]
    simp

end ShrincsSecurity.Fxmss.Rom

end
