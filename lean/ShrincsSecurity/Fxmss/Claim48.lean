module

public import ShrincsSecurity.Fxmss.TreeQueries
public import ShrincsSecurity.Fxmss.TcrCommon
public import ShrincsSecurity.Fxmss.Extraction

/-!
# Claim 4.8: the hop `F.7 → F.8` (SM-TCR of `H`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.8** and **Algorithm 11** (the reduction
`B₇` against SM-TCR of `H ∈ Th_λ` with `q₃ ≤ I = L − 1` targets).

`B₇ = mkTcrAdv (probTcrH (L − 1)) setupHyb (queries) forge`:

* **First stage** (`prog7`). The setup of `F.3` (`setupHyb`: the forger's structure phase, the
  presampled digests `y_j`, the secret key `u`), then, for a valid structure, the honest FXMSS tree
  of `u` through the oracles (`treeProgM`): every chain step `F` and every compression `Th_lsf`
  through the collection oracle, and every internal node `v` through the challenge oracle at
  `ADRS^tr_v` on the honest children values `(l, r)`, bottom-up. The targets are exactly
  `(ADRS^tr_v, (l_v, r_v))`, one per internal node (`Q7`).
* **Second stage** (`forge7`). With `PK.seed`, it simulates the rest of `gameHyb 0` itself
  (`stageHyb`) and searches the climb of the forgery (`tcrFind`): the pairs `(ADRS^tr_{v_{k+1}},
  (left, right))` hashed at the steps `k < |auth|` against the recorded targets.

`claim_4_8`: `Pr_{F.2}[E8] ≤ Succ^{sm-tcr}(B₇)`.

## Deviations

* The event is bounded in `gameHyb 0` (`F.2 = F.3` with `sk = u`), where the reduction knows `u`
  and builds the honest tree through its oracles; the paper's `F.7` differs from `F.3` only by the
  abort events of the earlier hops, which do not affect `E8`'s probability bound (the telescoping is
  in `Theorem42.lean`).
* The paper's `B₇` queries the targets of the tree only; ours also evaluates the chains and the
  compressions through the collection oracle (the honest leaf values depend on `PK.seed`, which the
  first stage does not know). The challenge oracle is queried exactly once per internal node, so
  `q₃ = I ≤ L − 1`.
* `hP` and `hgc` are not needed for this claim (at `γ = 0` every anchor value is the honest
  `WOTS+C.pkGen(u)` whether or not grinding succeeds); they are kept in the statement for
  uniformity with the other claims.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions Scheme.SfAdrs Scheme.Grinding
open ShrincsSecurity.Scheme.Structure (leafIds treeTweaks)
open SLHDSA (Adrs)

section Defs

variable {P : Params} (pr : Primitives P) (Msg : Type) [Inhabited pr.Y]
  [SampleableType pr.PkSeed]

/-! ## The first stage -/

/-- The oracles of `B₇`'s first stage (without private coins). -/
abbrev Spec7 :=
  SM_DT_TCR_challengeSpec Adrs (pr.Y × pr.Y) pr.Y +
    collectionSpec (TweakableHashCollection.cons (thH pr) pr.collection)

/-- A chain step `F(PK.seed, t, y)` through the collection oracle. -/
def fOp7 (t : Adrs) (y : pr.Y) : OracleComp (Spec7 pr) pr.Y := do
  let r ← ((Spec7 pr).query (.inr ⟨some .F, t, y⟩) : OracleComp (Spec7 pr) (Option pr.Y))
  return r.getD default

/-- A compression `Th_lsf(PK.seed, t, v)` through the collection oracle. -/
def cOp7 (t : Adrs) (v : Vector pr.Y P.lsf) : OracleComp (Spec7 pr) pr.Y := do
  let r ← ((Spec7 pr).query (.inr ⟨some .thLsf, t, v⟩) : OracleComp (Spec7 pr) (Option pr.Y))
  return r.getD default

/-- An internal node `H(PK.seed, t, a ‖ b)` through the challenge oracle. -/
def hOp7 (t : Adrs) (a b : pr.Y) : OracleComp (Spec7 pr) pr.Y := do
  let r ← ((Spec7 pr).query (.inl (t, (a, b))) : OracleComp (Spec7 pr) (Option pr.Y))
  return r.getD default

/-- **The queries of `B₇`** (Algorithm 11): the honest tree of the secret key `u` of a valid
structure, the internal nodes as targets; nothing for an invalid structure. -/
noncomputable def prog7 {St : Type} (d : Setup pr Msg St) : OracleComp (Spec7 pr) Unit :=
  if d.S.TreeValid P.hsf then treeProgM pr d.S (fOp7 pr) (cOp7 pr) (hOp7 pr) (skOf pr d.S d.u)
  else pure ()

/-- The recorded targets: `(ADRS^tr_v, (l_v, r_v))` for the internal nodes, bottom-up. -/
noncomputable def Q7 {St : Type} (d : Setup pr Msg St) (pk : pr.PkSeed) :
    List (Adrs × (pr.Y × pr.Y)) :=
  if d.S.TreeValid P.hsf then
    (treeOrder P.hsf d.S P.hsf 0).flatMap (entryQ P.hsf d.S (Fxmss.leaf pr pk (skOf pr d.S d.u))
      (Fxmss.node pr pk) (fun _ => []) (fun id a b => [((treeAdrs id).toAdrs, (a, b))]))
  else []

/-- The collection tweaks: the chain and compression tweaks of every anchor. -/
noncomputable def C7 {St : Type} (d : Setup pr Msg St) : List Adrs :=
  if d.S.TreeValid P.hsf then
    (treeOrder P.hsf d.S P.hsf 0).flatMap (entryC fun id => chainLog P id ++ [(pkAdrs id).toAdrs])
  else []

/-! ## The second stage -/

/-- The candidates read off the forgery: the pair hashed at each step `k < |auth|` of the climb,
at the tree address of the node it produces. -/
def cands7 (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Fxmss.Sig pr) :
    List (Adrs × (pr.Y × pr.Y)) :=
  (List.range w.auth.length).map fun k =>
    ((treeAdrs (Honest.fPos idf (k + 1))).toAdrs, H.fPair idf yf w k)

variable [DecidableEq pr.Y]

/-- The output of `B₇` from a run of the rest of `gameHyb 0`. -/
noncomputable def extract7 {St : Type} (d : Setup pr Msg St) (pk : pr.PkSeed) :
    Option (Transcript pr Msg × Honest pr) → ℕ × (pr.Y × pr.Y)
  | some (tr, H) => match tr.σf.2 with
    | some w => tcrFind (fun t (m : pr.Y × pr.Y) => pr.H pk t m.1 m.2) (Q7 pr Msg d pk)
        (cands7 pr H tr.idf tr.yf w)
    | none => (0, default)
  | none => (0, default)

end Defs

/-! ## The permissive run of the first stage -/

section Targets

variable {P : Params} (pr : Primitives P) {Msg : Type} [Inhabited pr.Y]
  [SampleableType pr.PkSeed]

theorem fOp7_isLog (p : ℕ) (pk : pr.PkSeed) (t : Adrs) (y : pr.Y) :
    IsLog (simulateQ (tcrPerm (probTcrH pr p) pk) (fOp7 pr t y)) (pr.F pk t y) [] [t] := by
  intro s
  simp only [fOp7, tcrPerm, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    simulateQ_pure, StateT.run_bind, StateT.run_mk, StateT.run_pure, pure_bind, List.append_nil]
  rfl

theorem cOp7_isLog (p : ℕ) (pk : pr.PkSeed) (t : Adrs) (v : Vector pr.Y P.lsf) :
    IsLog (simulateQ (tcrPerm (probTcrH pr p) pk) (cOp7 pr t v)) (pr.ThLsf pk t v) [] [t] := by
  intro s
  simp only [cOp7, tcrPerm, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    simulateQ_pure, StateT.run_bind, StateT.run_mk, StateT.run_pure, pure_bind, List.append_nil]
  rfl

theorem hOp7_isLog (p : ℕ) (pk : pr.PkSeed) (t : Adrs) (a b : pr.Y) :
    IsLog (simulateQ (tcrPerm (probTcrH pr p) pk) (hOp7 pr t a b)) (pr.H pk t a b)
      [(t, (a, b))] [] := by
  intro s
  simp only [hOp7, tcrPerm, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
    simulateQ_pure, StateT.run_bind, StateT.run_mk, StateT.run_pure, pure_bind, List.append_nil]
  rfl

theorem prog7_run (p : ℕ) {St : Type} (d : Setup pr Msg St) (pk : pr.PkSeed) :
    (simulateQ (tcrPerm (probTcrH pr p) pk) (prog7 pr Msg d)).run ([], []) =
      ((), (Q7 pr Msg d pk, C7 pr Msg d)) := by
  unfold prog7 Q7 C7
  split_ifs with hS
  · rw [simulateQ_treeProgM, treeProgM_isLog pr pk d.S (fOp7_isLog pr p pk) (cOp7_isLog pr p pk)
      (hOp7_isLog pr p pk) (skOf pr d.S d.u) ([], [])]
    simp
  · rfl

omit [SampleableType pr.PkSeed] in
/-- Every target is at the tree address of a visited internal node. -/
theorem mem_Q7 {St : Type} {d : Setup pr Msg St} {pk : pr.PkSeed} {e : Adrs × (pr.Y × pr.Y)}
    (he : e ∈ Q7 pr Msg d pk) : ∃ id, Visit P.hsf d.S (.inr id) ∧ e.1 = (treeAdrs id).toAdrs := by
  unfold Q7 at he
  split_ifs at he with hS
  · obtain ⟨o, ho, he⟩ := List.mem_flatMap.1 he
    obtain ⟨hv, -⟩ := mem_treeOrder _ _ o ho
    rcases o with id | id
    · simp [entryQ] at he
    · refine ⟨id, hv, ?_⟩
      simp only [entryQ, combineLog] at he
      split at he
      · simp only [List.mem_singleton] at he
        rw [he]
      · simp at he
  · simp at he

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] in
/-- Every collection tweak is a chain or compression tweak. -/
theorem mem_C7 {St : Type} {d : Setup pr Msg St} {t : Adrs} (ht : t ∈ C7 pr Msg d) :
    ∃ id, t = (pkAdrs id).toAdrs ∨ ∃ ch j, t = (chainAdrs id ch j).toAdrs := by
  unfold C7 at ht
  split_ifs at ht with hS
  · obtain ⟨o, -, ht⟩ := List.mem_flatMap.1 ht
    rcases o with id | id
    · simp only [entryC, chainLog, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_singleton] at ht
      rcases ht with ⟨ch, -, j, -, rfl⟩ | rfl
      · exact ⟨id, Or.inr ⟨ch, j, rfl⟩⟩
      · exact ⟨id, Or.inl rfl⟩
    · simp [entryC] at ht
  · simp at ht

omit [SampleableType pr.PkSeed] in
/-- The target of an internal node: its tree address and its honest children values. -/
theorem mem_Q7_of_treeTweaks {St : Type} {d : Setup pr Msg St} (hS : d.S.TreeValid P.hsf)
    (pk : pr.PkSeed) {id : LeafId} (hid : (treeAdrs id).toAdrs ∈ treeTweaks P.hsf d.S)
    {l r : pr.Y}
    (hl : Fxmss.treeNode pr d.S pk (skOf pr d.S d.u) (id.height - 1) (2 * id.index) = some l)
    (hr : Fxmss.treeNode pr d.S pk (skOf pr d.S d.u) (id.height - 1) (2 * id.index + 1) =
      some r) :
    ((treeAdrs id).toAdrs, (l, r)) ∈ Q7 pr Msg d pk := by
  unfold Q7
  rw [ite_eq_left hS]
  refine List.mem_flatMap.2 ⟨.inr id, visit_mem_treeOrder hS (visit_inr_of_mem_treeTweaks hS hid),
    ?_⟩
  simp only [Fxmss.treeNode] at hl hr
  simp [entryQ, combineLog, hl, hr]

end Targets

/-! ## `B₇` and Claim 4.8 -/

section Main

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- **`B₇`** (Algorithm 11). -/
noncomputable def B7 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrH pr (L - 1)) :=
  mkTcrAdv (probTcrH pr (L - 1)) (setupHyb pr Msg slKeygen A.toFxmssAdversary)
    (fun d => OracleComp.liftComp (prog7 pr Msg d) _)
    (fun d pk => extract7 pr Msg d pk <$>
      stageHyb pr Msg slKeygen A.toFxmssAdversary (betaOf pr 0 pk d.u) d pk)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
/-- **The targets of `B₇` are admissible**: distinct tree tweaks, at most `I ≤ L − 1` of them,
disjoint from the collection tweaks. -/
theorem tcrGood7 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    {d : Setup pr Msg A.State} (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary))
    (pk : pr.PkSeed) : TcrGood (L - 1) (Q7 pr Msg d pk, C7 pr Msg d) := by
  have hnd : ((Q7 pr Msg d pk).map Prod.fst).Nodup := by
    unfold Q7
    split_ifs with hS
    · refine List.Nodup.of_map nodeKey ?_
      rw [List.map_map]
      refine nodup_map_flatMap _ _ _ posOf (fun o _ => ?_) (nodup_treeOrder _ _)
      rcases o with id | id
      · simp [entryQ]
      · simp only [entryQ, combineLog]
        split <;> simp [posOf, treeAdrs]
    · simp
  refine ⟨hnd, ?_, ?_⟩
  · by_cases hS : d.S.TreeValid P.hsf
    · have hsub : ((Q7 pr Msg d pk).map Prod.fst).toFinset ⊆ treeTweaks P.hsf d.S := by
        intro t ht
        rw [List.mem_toFinset] at ht
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
        obtain ⟨id, hv, he1⟩ := mem_Q7 pr he
        rw [he1]
        exact treeAdrs_mem_treeTweaks hv.2.1 hv.2.2
      have h1 := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hnd, List.length_map, hS.card_treeTweaks] at h1
      have h2 := anchors_le_of_mem_support_setupHyb pr Msg slKeygen A hd hS
      simp only
      omega
    · simp [Q7, hS]
  · intro t ht hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
    obtain ⟨id, -, he1⟩ := mem_Q7 pr he
    obtain ⟨id', h | ⟨ch, j, h⟩⟩ := mem_C7 pr ht
    · rw [he1] at h
      exact pkAdrs_ne_treeAdrs _ _ h.symm
    · rw [he1] at h
      exact chainAdrs_ne_treeAdrs _ _ _ _ h.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Claim 4.8**: `Pr_{F.2}[E8] ≤ Succ^{sm-tcr}_{H ∈ Th_λ, L − 1}(B₇)`. -/
theorem claim_4_8 (_hP : P.Valid) (_hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEvent Honest.E8 o] ≤
      SM_DT_TCR_Advantage (B7 pr Msg slKeygen A) := by
  rw [B7, mkTcrAdv_advantage _ _ _ _ (fun d pk => Q7 pr Msg d pk) (fun d _ => C7 pr Msg d)
    (fun pk d hd => by
      rw [tcr_run_eq _ _ _ (by rw [prog7_run]; exact tcrGood7 pr Msg slKeygen A hd pk),
        prog7_run])]
  simp only [gameHyb, map_bind]
  refine prEvent_bind_mono' _ _ _ fun pk _ => ?_
  refine prEvent_bind_mono' _ _ _ fun d hd => ?_
  simp only [Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := stageHyb_support pr Msg slKeygen ho rfl
  obtain ⟨w, hw, k, hk, hmem, l, r, hl, hr, hne, heq⟩ := hE
  have hh : (Honest.fPos tr.idf (k + 1)).height - 1 = tr.idf.height + k := by
    simp only [Honest.fPos]
    omega
  rw [hon_zero_value] at hl hr
  simp only [extract7, hw]
  apply tcrWin_tcrFind
  refine ⟨_, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, _,
    mem_Q7_of_treeTweaks pr hS pk hmem (l := l) (r := r) ?_ ?_, rfl, hne, heq⟩
  · rw [hh]
    exact hl
  · rw [hh]
    exact hr

end Main

end ShrincsSecurity.Fxmss.Rom

end
