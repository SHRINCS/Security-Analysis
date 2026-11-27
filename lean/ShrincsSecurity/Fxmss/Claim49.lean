module

public import ShrincsSecurity.Fxmss.TreeQueries
public import ShrincsSecurity.Fxmss.Extraction

/-!
# Claim 4.9: the hop `F.8 → F.9` (sm-tcr-excl of `Th_{2∪lsf}`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.9** and **Algorithm 12** (the reduction
`B₈` against sm-tcr-excl of `Th_{2∪lsf}` with the partner map `ω` of `shrincsX`, against the
collection `Th_λ`, with `q₅ ≤ L + I` targets).

`B₈ = mkExclAdv (probExcl (L + (L − 1))) setupHyb (queries) forge`:

* **First stage** (`prog9`). The setup of `F.3` (`setupHyb`), then, for a valid structure, the
  honest FXMSS tree of the secret key `u` through the oracles (`treeProgM`): every chain step `F`
  through the collection oracle (tweaks of class `T₁`, never a challenged tweak or its partner),
  every anchor compression as a challenge `(ADRS^pk_v, Th_lsf-input pk_v)` and every internal node
  as a challenge `(ADRS^tr_v, H-input (l_v, r_v))`, bottom-up. At no node identifier are both the
  tree and the compression tweak challenged (`exclusive_roles`: a node is an anchor or internal,
  not both), so no challenge is refused (`Q9`: one target per node, `L + I` in all).
* **Second stage** (`forge9`). With `PK.seed`, it simulates the rest of `gameHyb 0` itself and
  searches the forgery (`exclFind`): at each climb step `k` the pair hashed by `H` at
  `ADRS^tr_{v_{k+1}} = ω⁻¹(ADRS^pk_{v_{k+1}})` against the compression target of `v_{k+1}`, and
  the forged compression at `ADRS^pk_{(z*,i*)} = ω(ADRS^tr_{(z*,i*)})` against the node target of
  `(z*, i*)`.

`claim_4_9`: `Pr_{F.2}[E9] ≤ Succ^{sm-tcr-excl}(B₈)`.

## Deviations

* As for Claim 4.8, the event is bounded in `gameHyb 0` (`F.2 = F.3`, `sk = u`), and the chains
  are evaluated through the collection oracle (the honest leaf values depend on `PK.seed`).
* Conjecture 3.1 (`hgc`, with `hP` for the one-byte node height of the grinding tweak) is used to
  identify the honest uncompressed public key `H.tops v` of the event with the challenged
  `c_{0,w−1}(u_v)`: when the counter search fails, `F.3`'s dummy signature reveals other blocks.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions Scheme.SfAdrs Scheme.Grinding
open ShrincsSecurity.Scheme.Structure (leafIds pkTweaks treeTweaks)
open SLHDSA (Adrs)

/-- The partners `Ω(t) = {t, ω^{±1}(t)}` of `shrincsX` share the node identifier of `t`. -/
theorem nodeKey_of_mem_Omega {a b : Adrs} (h : a ∈ shrincsX.Omega b) : nodeKey a = nodeKey b := by
  rcases h with rfl | rfl
  · rfl
  · simp only [shrincsX, shrincsPartner]
    split_ifs <;> rfl

section Defs

variable {P : Params} (pr : Primitives P) (Msg : Type) [Inhabited pr.Y]
  [SampleableType pr.PkSeed]

/-- The messages of `Th_{2∪lsf}`: node pairs (`H`) or uncompressed public keys (`Th_lsf`). -/
abbrev Msg9 : Type := (pr.Y × pr.Y) ⊕ Vector pr.Y P.lsf

/-- The oracles of `B₈`'s first stage (without private coins). -/
abbrev Spec9 :=
  SMTCRExcl_challengeSpec Adrs (Msg9 pr) pr.Y + collectionSpec pr.collection

/-- A chain step `F(PK.seed, t, y)` through the collection oracle. -/
def fOp9 (t : Adrs) (y : pr.Y) : OracleComp (Spec9 pr) pr.Y := do
  let r ← ((Spec9 pr).query (.inr ⟨.F, t, y⟩) : OracleComp (Spec9 pr) (Option pr.Y))
  return r.getD default

/-- An anchor compression `Th_lsf(PK.seed, t, v)` through the challenge oracle. -/
def cOp9 (t : Adrs) (v : Vector pr.Y P.lsf) : OracleComp (Spec9 pr) pr.Y := do
  let r ← ((Spec9 pr).query (.inl (t, .inr v)) : OracleComp (Spec9 pr) (Option pr.Y))
  return r.getD default

/-- An internal node `H(PK.seed, t, a ‖ b)` through the challenge oracle. -/
def hOp9 (t : Adrs) (a b : pr.Y) : OracleComp (Spec9 pr) pr.Y := do
  let r ← ((Spec9 pr).query (.inl (t, .inl (a, b))) : OracleComp (Spec9 pr) (Option pr.Y))
  return r.getD default

/-- **The queries of `B₈`** (Algorithm 12): the honest tree of the secret key `u` of a valid
structure, the compressions and the internal nodes as targets; nothing for an invalid structure. -/
noncomputable def prog9 {St : Type} (d : Setup pr Msg St) : OracleComp (Spec9 pr) Unit :=
  if d.S.TreeValid P.hsf then treeProgM pr d.S (fOp9 pr) (cOp9 pr) (hOp9 pr) (skOf pr d.S d.u)
  else pure ()

/-- The recorded targets: `(ADRS^pk_v, pk_v)` at the anchors and `(ADRS^tr_v, (l_v, r_v))` at the
internal nodes, bottom-up. -/
noncomputable def Q9 {St : Type} (d : Setup pr Msg St) (pk : pr.PkSeed) :
    List (Adrs × Msg9 pr) :=
  if d.S.TreeValid P.hsf then
    (treeOrder P.hsf d.S P.hsf 0).flatMap (entryQ P.hsf d.S (Fxmss.leaf pr pk (skOf pr d.S d.u))
      (Fxmss.node pr pk)
      (fun id => [((pkAdrs id).toAdrs, .inr (WotsC.pkTops pr pk id (skOf pr d.S d.u id)))])
      (fun id a b => [((treeAdrs id).toAdrs, .inl (a, b))]))
  else []

/-- The collection tweaks: the chain tweaks of every anchor. -/
noncomputable def C9 {St : Type} (d : Setup pr Msg St) : List Adrs :=
  if d.S.TreeValid P.hsf then (treeOrder P.hsf d.S P.hsf 0).flatMap (entryC (chainLog P))
  else []

/-- The candidates read off the forgery `(target tweak, T*, m*)`: at each climb step `k`, the pair
hashed at `ADRS^tr_{v_{k+1}}` against the compression target at `ADRS^pk_{v_{k+1}}`; and the forged
compression at `ADRS^pk_{(z*,i*)}` against the node target at `ADRS^tr_{(z*,i*)}`. -/
def cands9 (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Fxmss.Sig pr) :
    List (Adrs × Adrs × Msg9 pr) :=
  (List.range w.auth.length).map (fun k =>
    ((pkAdrs (Honest.fPos idf (k + 1))).toAdrs, (treeAdrs (Honest.fPos idf (k + 1))).toAdrs,
      .inl (H.fPair idf yf w k))) ++
  [((treeAdrs idf).toAdrs, (pkAdrs idf).toAdrs, .inr (H.fTops idf yf w))]

/-- The dummy output. -/
def dflt9 : ℕ × Adrs × Msg9 pr := (0, (pkAdrs ⟨0, 0⟩).toAdrs, .inl (default, default))

variable [DecidableEq pr.Y]

/-- The output of `B₈` from a run of the rest of `gameHyb 0`, searching the Stage-1 recorded
targets `savedQ` directly (computable). -/
def extract9 (savedQ : List (Adrs × Msg9 pr)) (pk : pr.PkSeed) :
    Option (Transcript pr Msg × Honest pr) → ℕ × Adrs × Msg9 pr
  | some (tr, H) => match tr.σf.2 with
    | some w => exclFind (fun a x => match x with | .inl lr => pr.H pk a lr.1 lr.2 | .inr v => pr.ThLsf pk a v)
        shrincsX savedQ (cands9 pr H tr.idf tr.yf w) (dflt9 pr)
    | none => dflt9 pr
  | none => dflt9 pr

end Defs

/-! ## The permissive run of the first stage -/

section Targets

variable {P : Params} (pr : Primitives P) {Msg : Type} [Inhabited pr.Y]
  [SampleableType pr.PkSeed]

theorem fOp9_isLog (p : ℕ) (pk : pr.PkSeed) (t : Adrs) (y : pr.Y) :
    IsLog (simulateQ (exclPerm (probExcl pr p) pk) (fOp9 pr t y)) (pr.F pk t y) [] [t] := by
  intro s
  simp only [fOp9, exclPerm, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    simulateQ_pure, StateT.run_bind, StateT.run_mk, StateT.run_pure, pure_bind, List.append_nil]
  rfl

theorem cOp9_isLog (p : ℕ) (pk : pr.PkSeed) (t : Adrs) (v : Vector pr.Y P.lsf) :
    IsLog (simulateQ (exclPerm (probExcl pr p) pk) (cOp9 pr t v)) (pr.ThLsf pk t v)
      [(t, .inr v)] [] := by
  intro s
  simp only [cOp9, exclPerm, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
    simulateQ_pure, StateT.run_bind, StateT.run_mk, StateT.run_pure, pure_bind, List.append_nil]
  rfl

theorem hOp9_isLog (p : ℕ) (pk : pr.PkSeed) (t : Adrs) (a b : pr.Y) :
    IsLog (simulateQ (exclPerm (probExcl pr p) pk) (hOp9 pr t a b)) (pr.H pk t a b)
      [(t, .inl (a, b))] [] := by
  intro s
  simp only [hOp9, exclPerm, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
    simulateQ_pure, StateT.run_bind, StateT.run_mk, StateT.run_pure, pure_bind, List.append_nil]
  rfl

theorem prog9_run (p : ℕ) {St : Type} (d : Setup pr Msg St) (pk : pr.PkSeed) :
    (simulateQ (exclPerm (probExcl pr p) pk) (prog9 pr Msg d)).run ([], []) =
      ((), (Q9 pr Msg d pk, C9 pr Msg d)) := by
  unfold prog9 Q9 C9
  split_ifs with hS
  · rw [simulateQ_treeProgM, treeProgM_isLog pr pk d.S (fOp9_isLog pr p pk) (cOp9_isLog pr p pk)
      (hOp9_isLog pr p pk) (skOf pr d.S d.u) ([], [])]
    simp
  · rfl

omit [SampleableType pr.PkSeed] in
/-- Every target is at the compression address of a visited anchor or at the tree address of a
visited internal node. -/
theorem mem_Q9 {St : Type} {d : Setup pr Msg St} {pk : pr.PkSeed} {e : Adrs × Msg9 pr}
    (he : e ∈ Q9 pr Msg d pk) :
    (∃ id, Visit P.hsf d.S (.inl id) ∧ e.1 = (pkAdrs id).toAdrs) ∨
      ∃ id, Visit P.hsf d.S (.inr id) ∧ e.1 = (treeAdrs id).toAdrs := by
  unfold Q9 at he
  split_ifs at he with hS
  · obtain ⟨o, ho, he⟩ := List.mem_flatMap.1 he
    obtain ⟨hv, -⟩ := mem_treeOrder _ _ o ho
    rcases o with id | id
    · simp only [entryQ, List.mem_singleton] at he
      exact Or.inl ⟨id, hv, by rw [he]⟩
    · refine Or.inr ⟨id, hv, ?_⟩
      simp only [entryQ, combineLog] at he
      split at he
      · simp only [List.mem_singleton] at he
        rw [he]
      · simp at he
  · simp at he

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] in
/-- Every collection tweak is a chain tweak. -/
theorem mem_C9 {St : Type} {d : Setup pr Msg St} {t : Adrs} (ht : t ∈ C9 pr Msg d) :
    ∃ id ch j, t = (chainAdrs id ch j).toAdrs := by
  unfold C9 at ht
  split_ifs at ht with hS
  · obtain ⟨o, -, ht⟩ := List.mem_flatMap.1 ht
    rcases o with id | id
    · simp only [entryC, chainLog, List.mem_flatMap, List.mem_map] at ht
      obtain ⟨ch, -, j, -, rfl⟩ := ht
      exact ⟨id, ch, j, rfl⟩
    · simp [entryC] at ht
  · simp at ht

omit [SampleableType pr.PkSeed] in
/-- The targets have pairwise distinct node identifiers. -/
theorem nodup_key_Q9 {St : Type} (d : Setup pr Msg St) (pk : pr.PkSeed) :
    ((Q9 pr Msg d pk).map fun e => nodeKey e.1).Nodup := by
  unfold Q9
  split_ifs with hS
  · refine nodup_map_flatMap _ _ _ posOf (fun o _ => ?_) (nodup_treeOrder _ _)
    rcases o with id | id
    · simp [entryQ, posOf, pkAdrs]
    · simp only [entryQ, combineLog]
      split <;> simp [posOf, treeAdrs]
  · simp

omit [SampleableType pr.PkSeed] in
/-- The compression target of an anchor: its compression address and `c_{0,w−1}(u)`. -/
theorem mem_Q9_of_pkTweaks {St : Type} {d : Setup pr Msg St} (hS : d.S.TreeValid P.hsf)
    (pk : pr.PkSeed) {id : LeafId} (hid : (pkAdrs id).toAdrs ∈ pkTweaks P.hsf d.S) :
    ((pkAdrs id).toAdrs, (.inr (WotsC.pkTops pr pk id (skOf pr d.S d.u id)) : Msg9 pr)) ∈
      Q9 pr Msg d pk := by
  unfold Q9
  rw [ite_eq_left hS]
  exact List.mem_flatMap.2 ⟨.inl id, visit_mem_treeOrder hS (visit_inl_of_mem_pkTweaks hS hid),
    by simp [entryQ]⟩

omit [SampleableType pr.PkSeed] in
/-- The node target of an internal node: its tree address and its honest children values. -/
theorem mem_Q9_of_treeTweaks {St : Type} {d : Setup pr Msg St} (hS : d.S.TreeValid P.hsf)
    (pk : pr.PkSeed) {id : LeafId} (hid : (treeAdrs id).toAdrs ∈ treeTweaks P.hsf d.S)
    {l r : pr.Y}
    (hl : Fxmss.treeNode pr d.S pk (skOf pr d.S d.u) (id.height - 1) (2 * id.index) = some l)
    (hr : Fxmss.treeNode pr d.S pk (skOf pr d.S d.u) (id.height - 1) (2 * id.index + 1) =
      some r) :
    ((treeAdrs id).toAdrs, (.inl (l, r) : Msg9 pr)) ∈ Q9 pr Msg d pk := by
  unfold Q9
  rw [ite_eq_left hS]
  refine List.mem_flatMap.2 ⟨.inr id, visit_mem_treeOrder hS (visit_inr_of_mem_treeTweaks hS hid),
    ?_⟩
  simp only [Fxmss.treeNode] at hl hr
  simp [entryQ, combineLog, hl, hr]

end Targets

section Main

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- **`B₈`** (Algorithm 12). -/
noncomputable def B8 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SMTCRExclAdversary (probExcl pr (L + (L - 1))) :=
  mkExclAdv (probExcl pr (L + (L - 1))) (setupHyb pr Msg slKeygen A.toFxmssAdversary)
    (fun d => OracleComp.liftComp (prog9 pr Msg d) _)
    (fun st pk => extract9 pr Msg st.2 pk <$>
      stageHyb pr Msg slKeygen A.toFxmssAdversary (betaOf pr 0 pk st.1.u) st.1 pk)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
/-- **The targets of `B₈` are admissible**: no target tweak lies in `Ω` of an earlier one (distinct
node identifiers), at most `L + I ≤ L + (L − 1)` of them, and no collection (chain) tweak lies in
`Ω` of a target. -/
theorem exclGood9 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    {d : Setup pr Msg A.State} (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary))
    (pk : pr.PkSeed) :
    ExclGood shrincsX (L + (L - 1)) (Q9 pr Msg d pk, C9 pr Msg d) := by
  have hkey := nodup_key_Q9 pr d pk
  have hnd : ((Q9 pr Msg d pk).map Prod.fst).Nodup := by
    refine List.Nodup.of_map nodeKey ?_
    rw [List.map_map]
    exact hkey
  refine ⟨?_, ?_, ?_⟩
  · exact (List.pairwise_map.1 hkey).imp fun hne hmem => hne (nodeKey_of_mem_Omega hmem).symm
  · by_cases hS : d.S.TreeValid P.hsf
    · have hsub : ((Q9 pr Msg d pk).map Prod.fst).toFinset ⊆
          treeTweaks P.hsf d.S ∪ pkTweaks P.hsf d.S := by
        intro t ht
        rw [List.mem_toFinset] at ht
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
        rcases mem_Q9 pr he with ⟨id, hv, he1⟩ | ⟨id, hv, he1⟩
        · rw [he1]
          exact Finset.mem_union_right _ (pkAdrs_mem_pkTweaks hv.1 hv.2)
        · rw [he1]
          exact Finset.mem_union_left _ (treeAdrs_mem_treeTweaks hv.2.1 hv.2.2)
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [List.toFinset_card_of_nodup hnd, List.length_map, hS.card_treeTweaks,
        hS.card_pkTweaks] at h1
      have h2 := anchors_le_of_mem_support_setupHyb pr Msg slKeygen A hd hS
      simp only
      omega
    · simp [Q9, hS]
  · intro t ht e he hmem
    obtain ⟨id, ch, j, rfl⟩ := mem_C9 pr ht
    rcases mem_Q9 pr he with ⟨id', -, he1⟩ | ⟨id', -, he1⟩
    · rw [he1] at hmem
      rcases hmem with h | h
      · exact chainAdrs_ne_pkAdrs _ _ _ _ h
      · rw [shrincsX_partner_pkAdrs] at h
        exact chainAdrs_ne_treeAdrs _ _ _ _ h
    · rw [he1] at hmem
      rcases hmem with h | h
      · exact chainAdrs_ne_treeAdrs _ _ _ _ h
      · rw [shrincsX_partner_treeAdrs] at h
        exact chainAdrs_ne_pkAdrs _ _ _ _ h

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Claim 4.9**: `Pr_{F.2}[E9] ≤ Succ^{sm-tcr-excl}_{Th_{2∪lsf}, L + I}(B₈)`. -/
theorem claim_4_9 (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEvent Honest.E9 o] ≤
      SMTCRExcl_Succ (B8 pr Msg slKeygen A) := by
  rw [B8, mkExclAdv_succ _ _ _ _ (fun d pk => Q9 pr Msg d pk) (fun d _ => C9 pr Msg d)
    (fun pk d hd => by
      rw [excl_run_eq _ _ _ (by rw [prog9_run]; exact exclGood9 pr Msg slKeygen A hd pk),
        prog9_run])]
  simp only [gameHyb, map_bind]
  refine prEvent_bind_mono' _ _ _ fun pk _ => ?_
  refine prEvent_bind_mono' _ _ _ fun d hd => ?_
  simp only [Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := stageHyb_support pr Msg slKeygen ho rfl
  obtain ⟨w, hw, hE⟩ := hE
  simp only [extract9, hw]
  apply exclIsCollision_exclFind
  rcases hE with ⟨k, hk, hpk, heq⟩ | ⟨htr, l, r, hl, hr, hN⟩
  · have hv := visit_inl_of_mem_pkTweaks hS hpk
    rw [hon_zero_tops pr hP hgc hS pk _ d.u (mem_leafIds_of hv.1 hv.2)] at heq
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩), _,
      mem_Q9_of_pkTweaks pr hS pk hpk, rfl, Or.inr (shrincsX_partner_pkAdrs _).symm,
      by simp, heq.symm⟩
  · rw [hon_zero_value] at hl hr
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), _,
      mem_Q9_of_treeTweaks pr hS pk htr hl hr, rfl, Or.inr (shrincsX_partner_treeAdrs _).symm,
      by simp, hN.symm⟩

end Main

end ShrincsSecurity.Fxmss.Rom

end
