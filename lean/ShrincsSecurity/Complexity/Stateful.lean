module

public import ShrincsSecurity.Complexity.SfTable
public import ShrincsSecurity.Shrincs.Theorem41

/-!
# Formal Stage-2 `Th_λ`-Evaluation Complexity Bounds for Stateful Reductions (Theorems 4.1 and 4.2)

This file constructs **Stage-1-full-precomputing** versions of all seven stateful collection
reductions for both:
* **Theorem 4.2** (`B2Pre, B3Pre γ, B4Pre, B5Pre, B6Pre, B7Pre, B8Pre`), and
* **Theorem 4.1** (`B2SPre, B3SPre γ, B4SPre, B5SPre, B6SPre, B7SPre, B8SPre`),

where every reduction:
1. **Stage 1:** precomputes the entire stateful FXMSS table `SfFullTable` (`PK.sf`, anchor
   signatures, encoded digests, blocks, chain values, uncompressed public keys, leaf values, and
   internal tree nodes) through the game's challenge oracle and collection oracle `O_coll` before
   `PK.seed` is revealed (and for Theorem 4.1, also precomputes `PK.sl` and the virtual SLH-DSA
   hypertree table via `slVirtualTreeM`), with zero refused oracle queries by tweak disjointness.
2. **Stage 2:** runs `stageHybPre` (zero signing/key-generation `Th_λ` evaluations), runs the
   single-pass explicit-`thSpec`-oracle FXMSS verifier + trace extractor `fxmssExtractTableM`
   (`≤ Vsf P = 497` `Th_λ` evaluations), and extracts its collision/preimage/distinguisher bit
   purely from `(FxmssTrace, SfFullTable, savedQ)` with zero additional `Th_λ` evaluations.

## Headline Theorems

* `theorem_4_2_precomp`: full 9-term Theorem 4.2 EU-CMA bound using `B2Pre … B8Pre`.
* `theorem_4_2_stage2Bounds`: simultaneous `Stage2ThBound ... (ξ + Vsf P)` (`ξ̃_sf ≤ ξ + 497`)
  for all seven stateful collection reductions `B2Pre, B3Pre γ, B4Pre, B5Pre, B6Pre, B7Pre, B8Pre`
  built from any `BudgetedFxmssForger` with Stage-2 `Th_λ` budget `ξ`.
* `claim_4_15_precomp` and `theorem_4_1_full_precomp`: full 21-term Theorem 4.1 SHRINCS EU-CMA
  bound using `B2SPre … B8SPre` (and Claim 4.16's Stage-1-precomputing stateless reductions).
* `theorem_4_1_stateful_stage2Bounds`: simultaneous `Stage2ThBound ... (ξ + Vsf vp.params)`
  (`ξ̃_sf ≤ ξ + 497`) for all seven augmented stateful reductions
  `B2SPre, B3SPre γ, B4SPre, B5SPre, B6SPre, B7SPre, B8SPre` built from any
  `BudgetedShrincsForger` with Stage-2 `Th_λ` budget `ξ`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Complexity

open Scheme Slhdsa Fxmss Fxmss.Rom Shrincs Notions
open ShrincsSecurity.Scheme.Structure (leafIds pkTweaks treeTweaks)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)
open SLHDSA (Adrs)

private theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) :
    ∀ l : List α, l.flatMap (fun x => [f x]) = l.map f
  | [] => rfl
  | a :: l => congrArg (f a :: ·) (flatMap_singleton_eq_map f l)

/-! ## 1. Collection-only grinding helper and Stage-1 full-table query programs -/

section Stage1Programs

variable {P : Params} (pr : Primitives P) [Inhabited pr.Y]

/-- Counter search for `WotsC.grind` using a generic `H_grind` oracle callback. -/
def grindSearchOp {m : Type → Type} [Monad m]
    (gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → m pr.Y)
    (id : LeafId) (md : pr.Digest) :
    List (Fin (2 ^ P.c)) → m (Option (pr.Y × Fin (2 ^ P.c)))
  | [] => pure none
  | c :: cs => do
    let d ← gOp (SfAdrs.grindAdrs id).toAdrs md c
    if WotsC.TargetSum pr d then pure (some (d, c))
    else grindSearchOp gOp id md cs

omit [Inhabited pr.Y] in
theorem simulateQ_grindSearchOp {ι : Type} {spec : OracleSpec ι} {n : Type → Type}
    [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)
    (gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp spec pr.Y)
    (id : LeafId) (md : pr.Digest) :
    ∀ cs, simulateQ impl (grindSearchOp pr gOp id md cs) =
      grindSearchOp pr (fun t m c => simulateQ impl (gOp t m c)) id md cs
  | [] => by simp [grindSearchOp]
  | c :: cs => by
    simp only [grindSearchOp, simulateQ_bind]
    refine bind_congr fun d => ?_
    split_ifs <;> simp [simulateQ_grindSearchOp impl gOp id md cs]

/-- Collection-only log of `grindSearchOp`: returns `Hyb.grindPure`, logs `[]` challenges and a
list of `(SfAdrs.grindAdrs id).toAdrs` collection tweaks. -/
def grindSearchLog (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) :
    List (Fin (2 ^ P.c)) → List Adrs
  | [] => []
  | c :: cs =>
    if WotsC.TargetSum pr (WotsC.encode pr pk id md c) then [(SfAdrs.grindAdrs id).toAdrs]
    else (SfAdrs.grindAdrs id).toAdrs :: grindSearchLog pk id md cs

omit [Inhabited pr.Y] in
theorem mem_grindSearchLog (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) :
    ∀ cs t, t ∈ grindSearchLog pr pk id md cs → t = (SfAdrs.grindAdrs id).toAdrs
  | [], _, h => by simp [grindSearchLog] at h
  | c :: cs, t, h => by
    unfold grindSearchLog at h
    split_ifs at h
    · exact List.mem_singleton.1 h
    · rcases List.mem_cons.1 h with rfl | h
      · rfl
      · exact mem_grindSearchLog pk id md cs t h

omit [Inhabited pr.Y] in
theorem grindSearchOp_isLog {α : Type} (pk : pr.PkSeed)
    {gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → StateM (List α × List Adrs) pr.Y}
    (hG : ∀ t m c, IsLog (gOp t m c) (pr.Hgrind pk t m c) [] [t])
    (id : LeafId) (md : pr.Digest) :
    ∀ cs, IsLog (grindSearchOp pr gOp id md cs) (Hyb.grindPure pr pk id md cs) []
      (grindSearchLog pr pk id md cs)
  | [] => (IsLog.pure _).of_eq rfl rfl rfl
  | c :: cs => by
    unfold grindSearchOp Hyb.grindPure grindSearchLog
    have ih := grindSearchOp_isLog pk hG id md cs
    have hstep := hG (SfAdrs.grindAdrs id).toAdrs md c
    have hEq : pr.Hgrind pk (SfAdrs.grindAdrs id).toAdrs md c = WotsC.encode pr pk id md c := rfl
    by_cases hts : WotsC.TargetSum pr (WotsC.encode pr pk id md c)
    · have hcont : IsLog
          (if WotsC.TargetSum pr (pr.Hgrind pk (SfAdrs.grindAdrs id).toAdrs md c)
            then pure (some (pr.Hgrind pk (SfAdrs.grindAdrs id).toAdrs md c, c))
            else grindSearchOp pr gOp id md cs)
          (some (WotsC.encode pr pk id md c, c)) [] [] := by
        rw [hEq]; simp only [hts, ↓reduceIte]; exact IsLog.pure _
      exact (hstep.bind hcont).of_eq (by simp [hts]) (by simp) (by simp [hts])
    · have hcont : IsLog
          (if WotsC.TargetSum pr (pr.Hgrind pk (SfAdrs.grindAdrs id).toAdrs md c)
            then pure (some (pr.Hgrind pk (SfAdrs.grindAdrs id).toAdrs md c, c))
            else grindSearchOp pr gOp id md cs)
          (Hyb.grindPure pr pk id md cs) [] (grindSearchLog pr pk id md cs) := by
        rw [hEq]; simp only [hts, ↓reduceIte]; exact ih
      exact (hstep.bind hcont).of_eq (by simp [hts]) (by simp) (by simp [hts])

/-! ### Deterministic `prog2Pre`, `prog4Pre`, `prog6Pre`, `prog7Pre`, `prog8Pre` -/

variable [SampleableType pr.PkSeed] [Inhabited pr.Digest]

/-- Challenge-plus-collection oracle spec for `B2Pre` (without private coins). -/
abbrev Spec2Pre (L : ℕ) :=
  STCR_challengeSpec Adrs pr.Digest pr.Y + collectionSpec (probGrind pr L).thColl

/-- **Stage-1 full-table program for `B2Pre`**: queries `O_Prop` on `anchorList` and builds the
rest of `SfFullTable` via `O_coll(.F, .thLsf, .H)`. -/
noncomputable def prog2Pre (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : OracleComp (Spec2Pre pr L) (SfFullTable pr) :=
  let grindOp : LeafId → pr.Digest → OracleComp (Spec2Pre pr L) (Option (pr.Y × Fin (2 ^ P.c))) :=
    fun id md => do
      let r ← ((Spec2Pre pr L).query (.inl ((SfAdrs.grindAdrs id).toAdrs, md)) :
        OracleComp (Spec2Pre pr L) (Option (pr.Y × ℕ)))
      return match r with
        | some (d, c) => if h : c < 2 ^ P.c then some (d, ⟨c, h⟩) else none
        | none => none
  let fOp : Adrs → pr.Y → OracleComp (Spec2Pre pr L) pr.Y := fun t y => do
    let r ← ((Spec2Pre pr L).query (.inr ⟨some .F, t, y⟩) :
      OracleComp (Spec2Pre pr L) (Option pr.Y))
    return r.getD default
  let cOp : Adrs → Vector pr.Y P.lsf → OracleComp (Spec2Pre pr L) pr.Y := fun t v => do
    let r ← ((Spec2Pre pr L).query (.inr ⟨some .thLsf, t, v⟩) :
      OracleComp (Spec2Pre pr L) (Option pr.Y))
    return r.getD default
  let hOp : Adrs → pr.Y → pr.Y → OracleComp (Spec2Pre pr L) pr.Y := fun t a b => do
    let r ← ((Spec2Pre pr L).query (.inr ⟨some .H, t, (a, b)⟩) :
      OracleComp (Spec2Pre pr L) (Option pr.Y))
    return r.getD default
  buildSfTable0M pr grindOp fOp cOp hOp S (digOf pr ys) (skOf pr S u)

/-- Recorded Stage-1 targets for `B2Pre` (identical to `B2targets`). -/
noncomputable def Q2Pre (_L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest) (pk : pr.PkSeed) :
    List ((Adrs × pr.Digest) × (pr.Y × ℕ)) :=
  if S.TreeValid P.hsf then
    (anchorList P S).flatMap fun id =>
      match leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs
          (digOf pr ys id) with
      | none => []
      | some i =>
        [(((SfAdrs.grindAdrs id).toAdrs, digOf pr ys id),
          ((thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (digOf pr ys id, i), i))]
  else []

/-- Stage-1 collection tweaks for `B2Pre` (`chainAdrs`, `pkAdrs`, `treeAdrs` — never `grindAdrs`). -/
noncomputable def C2Pre (S : Structure) (pk : pr.PkSeed) (u : SkIdx P S → pr.Y) : List Adrs :=
  if S.TreeValid P.hsf then
    (treeOrder P.hsf S P.hsf 0).flatMap fun
      | .inl id =>
        ((List.finRange P.lsf).flatMap fun ch =>
          (List.range (P.w - 1)).map fun j => (SfAdrs.chainAdrs id ch.val j).toAdrs) ++
        [(SfAdrs.pkAdrs id).toAdrs]
      | .inr id =>
        combineLog (fun _ _ => [(SfAdrs.treeAdrs id).toAdrs])
          (Tree.treeNode P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk) (id.height - 1) (2 * id.index))
          (Tree.treeNode P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk) (id.height - 1) (2 * id.index + 1))
  else []

theorem prog2Pre_perm_run (hP : P.Valid) (hgc : GrindComplete pr) (L : ℕ) (S : Structure)
    (ys : Anchor P S → pr.Digest) (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) :
    (simulateQ (stcrPerm (probGrind pr L) pk) (prog2Pre pr L S ys u)).run ([], []) =
      (buildSfTable0Det pr pk S (digOf pr ys) (skOf pr S u), (Q2Pre pr L S ys pk, C2Pre pr S pk u)) := by
  unfold prog2Pre buildSfTable0Det Q2Pre C2Pre
  by_cases hS : S.TreeValid P.hsf
  · rw [simulateQ_buildSfTable0M]
    unfold buildSfTable0M
    simp only [hS, ↓reduceIte]
    let gOp : LeafId → pr.Digest →
        StateT (List ((Adrs × pr.Digest) × (pr.Y × ℕ)) × List Adrs) Id
          (Option (pr.Y × Fin (2 ^ P.c))) := fun id md =>
      simulateQ (stcrPerm (probGrind pr L) pk) (do
        let r ← ((Spec2Pre pr L).query (.inl ((SfAdrs.grindAdrs id).toAdrs, md)) :
          OracleComp (Spec2Pre pr L) (Option (pr.Y × ℕ)))
        return match r with
          | some (d, c) => if h : c < 2 ^ P.c then some (d, ⟨c, h⟩) else none
          | none => none)
    have hG : ∀ id ∈ anchorList P S,
        IsLog (gOp id (digOf pr ys id))
          (WotsC.grind pr pk id (digOf pr ys id))
          (match leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs
              (digOf pr ys id) with
            | none => []
            | some i =>
              [(((SfAdrs.grindAdrs id).toAdrs, digOf pr ys id),
                ((thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (digOf pr ys id, i), i))])
          [] := by
      intro id hid
      obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS (mem_anchorList.1 hid) pk (digOf pr ys id)
      have hlc := leastCounter_thGrind pr hg
      intro s
      simp only [gOp, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, stcrPerm,
        QueryImpl.add_apply_inl, StateT.run_bind, StateT.run_mk, StateT.run_pure, id_pure_eq,
        id_bind_eq, hlc, hg, c.isLt, ↓reduceDIte, List.append_nil]
      have hev : (thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (digOf pr ys id, c.val) =
          WotsC.encode pr pk id (digOf pr ys id) c := by
        simp [thGrind, TweakableHash.ofFun, WotsC.encode, Nat.mod_eq_of_lt c.isLt]
      rw [hev]
    have hGrindAll : ∀ ids : List LeafId, (∀ id ∈ ids, id ∈ anchorList P S) →
        IsLog (grindListM pr gOp (digOf pr ys) ids)
          (fun id' => if id' ∈ ids then WotsC.grind pr pk id' (digOf pr ys id') else none)
          (ids.flatMap fun id =>
            match leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs
                (digOf pr ys id) with
            | none => []
            | some i =>
              [(((SfAdrs.grindAdrs id).toAdrs, digOf pr ys id),
                ((thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (digOf pr ys id, i), i))])
          [] := by
      intro ids
      induction ids with
      | nil => intro _; exact (IsLog.pure _).of_eq rfl rfl rfl
      | cons id ids ih =>
        intro hall
        have h1 := hG id (hall id (by simp))
        have h2 := ih fun id' h' => hall id' (by simp [h'])
        intro s
        dsimp only [IsLog] at h1 h2
        unfold grindListM
        rw [StateT.run_bind]; dsimp only [id_bind_eq]; rw [h1 s]; dsimp only
        rw [StateT.run_bind]; dsimp only [id_bind_eq]; rw [h2]; dsimp only
        simp only [StateT.run_pure, id_pure_eq, List.flatMap_cons, List.append_assoc, List.append_nil]
        refine Prod.ext ?_ rfl
        funext id'
        by_cases h : id' = id
        · subst h; simp
        · simp [h]
    have hF : ∀ t y, IsLog (simulateQ (stcrPerm (probGrind pr L) pk) (do
        let r ← ((Spec2Pre pr L).query (.inr ⟨some .F, t, y⟩) :
          OracleComp (Spec2Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.F pk t y) [] [t] := fun t y s => by
      simp [stcrPerm, id_pure_eq]; rfl
    have hC : ∀ t v, IsLog (simulateQ (stcrPerm (probGrind pr L) pk) (do
        let r ← ((Spec2Pre pr L).query (.inr ⟨some .thLsf, t, v⟩) :
          OracleComp (Spec2Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.ThLsf pk t v) [] [t] := fun t v s => by
      simp [stcrPerm, id_pure_eq]; rfl
    have hH : ∀ t a b, IsLog (simulateQ (stcrPerm (probGrind pr L) pk) (do
        let r ← ((Spec2Pre pr L).query (.inr ⟨some .H, t, (a, b)⟩) :
          OracleComp (Spec2Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.H pk t a b) [] [t] := fun t a b s => by
      simp [stcrPerm, id_pure_eq]; rfl
    have hL := leafRecM_isLog pr pk hF hC (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val)
    have hT := treeTableM_isLog pr S hL (fun id a b => hH (SfAdrs.treeAdrs id).toAdrs a b) P.hsf 0 default
    have hAll := (hGrindAll (anchorList P S) fun _ h => h).bind
      (f := fun gf =>
        (treeTableM pr S
          (leafRecM pr
            (fun t y => simulateQ (stcrPerm (probGrind pr L) pk) (do
              let r ← ((Spec2Pre pr L).query (.inr ⟨some .F, t, y⟩) :
                OracleComp (Spec2Pre pr L) (Option pr.Y))
              return r.getD default))
            (fun t v => simulateQ (stcrPerm (probGrind pr L) pk) (do
              let r ← ((Spec2Pre pr L).query (.inr ⟨some .thLsf, t, v⟩) :
                OracleComp (Spec2Pre pr L) (Option pr.Y))
              return r.getD default))
            (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val))
          (fun id a b => simulateQ (stcrPerm (probGrind pr L) pk) (do
            let r ← ((Spec2Pre pr L).query (.inr ⟨some .H, (SfAdrs.treeAdrs id).toAdrs, (a, b)⟩) :
              OracleComp (Spec2Pre pr L) (Option pr.Y))
            return r.getD default))
          P.hsf 0 default) >>= fun p =>
          pure (assembleSfTable pr gf p.2 (fun id ch => skOf pr S u id ch.val)))
      (hT.bind (IsLog.pure _))
    have hrun := hAll ([], [])
    have hleafEq : (fun id => (leafRecDet pr pk (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val) id).2.2) =
        Scheme.Fxmss.leaf pr pk (skOf pr S u) := by
      funext id; exact (leafRecDet_zero pr pk (skOf pr S u) id).2
    have hQempty : (treeOrder P.hsf S P.hsf 0).flatMap
        (entryQ P.hsf S (fun id => (leafRecDet pr pk (fun _ _ => 0)
          (fun id ch => skOf pr S u id ch.val) id).2.2) (fun id => pr.H pk (SfAdrs.treeAdrs id).toAdrs)
          (fun _ => (List.finRange P.lsf).flatMap fun _ =>
            (List.range (P.w - 1 - 0)).flatMap fun _ => [])
          (fun _ _ _ => [])) = ([] : List ((Adrs × pr.Digest) × (pr.Y × ℕ))) := by
      rw [List.flatMap_eq_nil_iff]
      rintro (id | id) _
      · simp [entryQ]
      · simp only [entryQ, combineLog]; split <;> rfl
    rw [hrun]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [List.nil_append, List.append_nil, hQempty]
    · simp only [List.nil_append, List.append_nil, hleafEq]
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp only [Nat.sub_zero, Nat.zero_add, flatMap_singleton_eq_map]
      · rfl
  · simp [hS, buildSfTable0M, id_pure_eq]

theorem stcrGood_Q2Pre (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed)
    (hL : S.TreeValid P.hsf → (anchorList P S).length ≤ L) :
    STcrGood L (Q2Pre pr L S ys pk, C2Pre pr S pk u) := by
  unfold Q2Pre C2Pre
  by_cases hS : S.TreeValid P.hsf
  · simp only [hS, ↓reduceIte]
    have hsub : List.Sublist
        (((anchorList P S).flatMap fun id =>
          match leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs
              (digOf pr ys id) with
          | none => []
          | some i =>
            [(((SfAdrs.grindAdrs id).toAdrs, digOf pr ys id),
              ((thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (digOf pr ys id, i), i))]).map
            (fun e : (Adrs × pr.Digest) × (pr.Y × ℕ) => e.1.1))
        ((anchorList P S).map (fun id => (SfAdrs.grindAdrs id).toAdrs)) := by
      refine map_flatMap_sublist (anchorList P S) _
        (fun e : (Adrs × pr.Digest) × (pr.Y × ℕ) => e.1.1)
        (fun id => (SfAdrs.grindAdrs id).toAdrs) fun id _ => ?_
      cases leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs
        (digOf pr ys id) <;> simp
    refine ⟨((nodup_anchorList S).map fun a b h => SfAdrs.grindAdrs_inj.1 h).sublist hsub, ?_, ?_⟩
    · have hlen := hsub.length_le
      simp only [List.length_map] at hlen
      exact hlen.trans (hL hS)
    · intro t ht hq
      have hqt := hsub.subset hq
      obtain ⟨id', -, rfl⟩ := List.mem_map.1 hqt
      obtain ⟨e, -, he⟩ := List.mem_flatMap.1 ht
      rcases e with id | id
      · simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton] at he
        rcases he with ⟨ch, -, j, -, h⟩ | h
        · exact SfAdrs.chainAdrs_ne_grindAdrs id id' ch.val j h
        · exact SfAdrs.pkAdrs_ne_grindAdrs id id' h.symm
      · simp only [combineLog] at he
        split at he
        · exact SfAdrs.treeAdrs_ne_grindAdrs id id' (List.mem_singleton.1 he).symm
        · simp at he
  · simp [hS, STcrGood]

/-- Challenge-plus-collection oracle spec for `B4Pre` (SM-TCR of `F`). -/
abbrev Spec4Pre (L : ℕ) :=
  SM_DT_TCR_challengeSpec Adrs pr.Y pr.Y + collectionSpec (probTcrF pr (L * P.lsf * P.w)).thColl

/-- **Stage-1 full-table program for `B4Pre`**: grinds via `O_coll(.grind)`, evaluates every chain
step `F` via SM-TCR challenge oracle `O_chal`, and builds compressions and internal nodes via
`O_coll(.thLsf, .H)`. -/
noncomputable def prog4Pre (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : OracleComp (Spec4Pre pr L) (SfFullTable pr) :=
  let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec4Pre pr L) pr.Y := fun t md c => do
    let r ← ((Spec4Pre pr L).query (.inr ⟨some .grind, t, (md, c)⟩) :
      OracleComp (Spec4Pre pr L) (Option pr.Y))
    return r.getD default
  let fOp : Adrs → pr.Y → OracleComp (Spec4Pre pr L) pr.Y := fun t y => do
    let r ← ((Spec4Pre pr L).query (.inl (t, y)) : OracleComp (Spec4Pre pr L) (Option pr.Y))
    return r.getD default
  let cOp : Adrs → Vector pr.Y P.lsf → OracleComp (Spec4Pre pr L) pr.Y := fun t v => do
    let r ← ((Spec4Pre pr L).query (.inr ⟨some .thLsf, t, v⟩) :
      OracleComp (Spec4Pre pr L) (Option pr.Y))
    return r.getD default
  let hOp : Adrs → pr.Y → pr.Y → OracleComp (Spec4Pre pr L) pr.Y := fun t a b => do
    let r ← ((Spec4Pre pr L).query (.inr ⟨some .H, t, (a, b)⟩) :
      OracleComp (Spec4Pre pr L) (Option pr.Y))
    return r.getD default
  buildSfTable0M pr (fun id md => grindSearchOp pr gOp id md (List.finRange (2 ^ P.c)))
    fOp cOp hOp S (digOf pr ys) (skOf pr S u)

/-- Recorded Stage-1 targets for `B4Pre`: all chain steps `(chainAdrs id ch j, chain 0 j)` in
`treeOrder`. -/
noncomputable def Q4Pre (S : Structure) (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) :
    List (Adrs × pr.Y) :=
  if S.TreeValid P.hsf then
    (treeOrder P.hsf S P.hsf 0).flatMap (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
      (Scheme.Fxmss.node pr pk)
      (fun id => (List.finRange P.lsf).flatMap fun ch =>
        (List.range (P.w - 1)).map fun j =>
          ((SfAdrs.chainAdrs id ch.val j).toAdrs,
            WotsC.chain pr pk id ch.val (skOf pr S u id ch.val) 0 j))
      (fun _ _ _ => []))
  else []

/-- Collection tweaks spent by `prog4Pre` (`grindAdrs`, `pkAdrs`, `treeAdrs` — never `chainAdrs`). -/
noncomputable def C4Pre (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) : List Adrs :=
  if S.TreeValid P.hsf then
    ((anchorList P S).flatMap fun id =>
      grindSearchLog pr pk id (digOf pr ys id) (List.finRange (2 ^ P.c))) ++
    ((treeOrder P.hsf S P.hsf 0).flatMap fun
      | .inl id => [(SfAdrs.pkAdrs id).toAdrs]
      | .inr id =>
        combineLog (fun _ _ => [(SfAdrs.treeAdrs id).toAdrs])
          (Tree.treeNode P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk) (id.height - 1) (2 * id.index))
          (Tree.treeNode P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk) (id.height - 1) (2 * id.index + 1)))
  else []

theorem prog4Pre_perm_run (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) :
    (simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (prog4Pre pr L S ys u)).run ([], []) =
      (buildSfTable0Det pr pk S (digOf pr ys) (skOf pr S u),
        (Q4Pre pr S u pk, C4Pre pr S ys u pk)) := by
  unfold prog4Pre buildSfTable0Det Q4Pre C4Pre
  by_cases hS : S.TreeValid P.hsf
  · rw [simulateQ_buildSfTable0M]
    unfold buildSfTable0M
    simp only [hS, ↓reduceIte]
    let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec4Pre pr L) pr.Y := fun t md c => do
      let r ← ((Spec4Pre pr L).query (.inr ⟨some .grind, t, (md, c)⟩) :
        OracleComp (Spec4Pre pr L) (Option pr.Y))
      return r.getD default
    have hGop : ∀ t md c, IsLog (simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (gOp t md c))
        (pr.Hgrind pk t md c) [] [t] := fun t md c s => by
      simp [gOp, tcrPerm, id_pure_eq]; rfl
    have hG : ∀ id md, IsLog (simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk)
        (grindSearchOp pr gOp id md (List.finRange (2 ^ P.c))))
        (WotsC.grind pr pk id md) [] (grindSearchLog pr pk id md (List.finRange (2 ^ P.c))) := by
      intro id md
      rw [simulateQ_grindSearchOp]
      exact (grindSearchOp_isLog pr pk hGop id md (List.finRange (2 ^ P.c))).of_eq
        (Hyb.grindPure_finRange pr pk id md) rfl rfl
    have hF : ∀ t y, IsLog (simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (do
        let r ← ((Spec4Pre pr L).query (.inl (t, y)) : OracleComp (Spec4Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.F pk t y) [(t, y)] [] := fun t y s => by
      simp [tcrPerm, id_pure_eq]; rfl
    have hC : ∀ t v, IsLog (simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (do
        let r ← ((Spec4Pre pr L).query (.inr ⟨some .thLsf, t, v⟩) :
          OracleComp (Spec4Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.ThLsf pk t v) [] [t] := fun t v s => by
      simp [tcrPerm, id_pure_eq]; rfl
    have hH : ∀ t a b, IsLog (simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (do
        let r ← ((Spec4Pre pr L).query (.inr ⟨some .H, t, (a, b)⟩) :
          OracleComp (Spec4Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.H pk t a b) [] [t] := fun t a b s => by
      simp [tcrPerm, id_pure_eq]; rfl
    have hL := leafRecM_isLog pr pk hF hC (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val)
    have hT := treeTableM_isLog pr S hL (fun id a b => hH (SfAdrs.treeAdrs id).toAdrs a b) P.hsf 0 default
    have hAll := (grindListM_isLog pr hG (digOf pr ys) (anchorList P S)).bind
      (f := fun gf =>
        (treeTableM pr S
          (leafRecM pr
            (fun t y => simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (do
              let r ← ((Spec4Pre pr L).query (.inl (t, y)) : OracleComp (Spec4Pre pr L) (Option pr.Y))
              return r.getD default))
            (fun t v => simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (do
              let r ← ((Spec4Pre pr L).query (.inr ⟨some .thLsf, t, v⟩) :
                OracleComp (Spec4Pre pr L) (Option pr.Y))
              return r.getD default))
            (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val))
          (fun id a b => simulateQ (tcrPerm (probTcrF pr (L * P.lsf * P.w)) pk) (do
            let r ← ((Spec4Pre pr L).query (.inr ⟨some .H, (SfAdrs.treeAdrs id).toAdrs, (a, b)⟩) :
              OracleComp (Spec4Pre pr L) (Option pr.Y))
            return r.getD default))
          P.hsf 0 default) >>= fun p =>
          pure (assembleSfTable pr gf p.2 (fun id ch => skOf pr S u id ch.val)))
      (hT.bind (IsLog.pure _))
    have hleafEq : (fun id => (leafRecDet pr pk (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val) id).2.2) =
        Scheme.Fxmss.leaf pr pk (skOf pr S u) := by
      funext id; exact (leafRecDet_zero pr pk (skOf pr S u) id).2
    rw [hAll ([], [])]
    have hnil : (anchorList P S).flatMap (fun _ => ([] : List (Adrs × pr.Y))) = [] := by simp
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [List.nil_append, List.append_nil, hnil, hleafEq]
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [entryQ, flatMap_singleton_eq_map]
      · simp only [entryQ, combineLog]; split <;> (split <;> rfl)
    · simp only [List.nil_append, List.append_nil, hleafEq]
      congr 1
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp
      · rfl
  · simp [hS, buildSfTable0M, id_pure_eq]

private theorem anchors_in_treeOrder_length_le (S : Structure) (_hS : S.TreeValid P.hsf) :
    ((treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none).length ≤
      S.anchors.card := by
  have hnd : ((treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none).Nodup := by
    refine List.Nodup.filterMap (fun a b x ha hb => ?_)
      (List.Nodup.of_map posOf (nodup_treeOrder (hsf := P.hsf) (S := S) P.hsf 0))
    rcases a with id₁ | id₁ <;> rcases b with id₂ | id₂ <;> simp at ha hb
    rw [ha, hb]
  have hsub : ((treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none).toFinset ⊆
      leafIds P.hsf S := by
    intro id₀ hid
    rw [List.mem_toFinset, List.mem_filterMap] at hid
    obtain ⟨e, he, h⟩ := hid
    rcases e with id' | id'
    · simp only [Option.some.injEq] at h; subst h
      obtain ⟨hv, -, -⟩ := mem_treeOrder (hsf := P.hsf) (S := S) P.hsf 0 (.inl id') he
      exact Finset.mem_image.2 ⟨Node.ofLeafId P.hsf id', hv.2, Node.toLeafId_ofLeafId hv.1⟩
    · simp at h
  calc _ = ((treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (leafIds P.hsf S).card := Finset.card_le_card hsub
    _ ≤ S.anchors.card := Finset.card_image_le

omit [SampleableType pr.PkSeed] in
theorem tcrGood_Q4Pre (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed)
    (hL : S.TreeValid P.hsf → S.anchors.card ≤ L) :
    TcrGood (L * P.lsf * P.w) (Q4Pre pr S u pk, C4Pre pr S ys u pk) := by
  unfold Q4Pre C4Pre
  by_cases hS : S.TreeValid P.hsf
  · simp only [hS, ↓reduceIte]
    set anchorsO := (treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none
    have hndA : anchorsO.Nodup := by
      refine List.Nodup.filterMap (fun a b x ha hb => ?_)
        (List.Nodup.of_map posOf (nodup_treeOrder (hsf := P.hsf) (S := S) P.hsf 0))
      rcases a with id₁ | id₁ <;> rcases b with id₂ | id₂ <;> simp at ha hb
      rw [ha, hb]
    have hmap_eq : ((treeOrder P.hsf S P.hsf 0).flatMap
        (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u)) (Scheme.Fxmss.node pr pk)
          (fun id => (List.finRange P.lsf).flatMap fun ch =>
            (List.range (P.w - 1)).map fun j =>
              ((SfAdrs.chainAdrs id ch.val j).toAdrs,
                WotsC.chain pr pk id ch.val (skOf pr S u id ch.val) 0 j))
          (fun _ _ _ => []))).map Prod.fst =
        anchorsO.flatMap fun id => (List.finRange P.lsf).flatMap fun ch =>
          (List.range (P.w - 1)).map fun j => (SfAdrs.chainAdrs id ch.val j).toAdrs := by
      rw [List.map_flatMap]
      have hgen : ∀ l : List (LeafId ⊕ LeafId),
          l.flatMap (fun x => (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk)
            (fun id => (List.finRange P.lsf).flatMap fun ch =>
              (List.range (P.w - 1)).map fun j =>
                ((SfAdrs.chainAdrs id ch.val j).toAdrs,
                  WotsC.chain pr pk id ch.val (skOf pr S u id ch.val) 0 j))
            (fun _ _ _ => []) x).map Prod.fst) =
          (l.filterMap fun | .inl id => some id | .inr _ => none).flatMap fun id =>
            (List.finRange P.lsf).flatMap fun ch =>
              (List.range (P.w - 1)).map fun j => (SfAdrs.chainAdrs id ch.val j).toAdrs := by
        intro l; induction l with
        | nil => rfl
        | cons e l ih =>
          rcases e with id | id
          · rw [List.flatMap_cons, List.filterMap_cons, List.flatMap_cons, ih]
            simp [entryQ, List.map_flatMap, List.map_map, Function.comp_def]
          · have hempty : (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
                (Scheme.Fxmss.node pr pk)
                (fun id => (List.finRange P.lsf).flatMap fun ch =>
                  (List.range (P.w - 1)).map fun j =>
                    ((SfAdrs.chainAdrs id ch.val j).toAdrs,
                      WotsC.chain pr pk id ch.val (skOf pr S u id ch.val) 0 j))
                (fun _ _ _ => []) (.inr id)).map Prod.fst = [] := by
              simp only [entryQ, combineLog]; split <;> rfl
            simp only [List.flatMap_cons, hempty, List.nil_append, List.filterMap_cons, ih]
      exact hgen _
    refine ⟨?_, ?_, ?_⟩
    · rw [hmap_eq]
      rw [List.nodup_flatMap]
      refine ⟨fun id _ => ?_, ?_⟩
      · rw [List.nodup_flatMap]
        refine ⟨fun ch _ => List.nodup_range.map (fun a b h => (SfAdrs.chainAdrs_inj.1 h).2.2), ?_⟩
        refine (List.nodup_finRange P.lsf).imp_of_mem fun {ch₁ ch₂} _ _ hne t ht₁ ht₂ => ?_
        obtain ⟨j₁, -, rfl⟩ := List.mem_map.1 ht₁
        obtain ⟨j₂, -, h⟩ := List.mem_map.1 ht₂
        exact hne (Fin.ext (SfAdrs.chainAdrs_inj.1 h).2.1.symm)
      · refine hndA.imp_of_mem fun {id₁ id₂} _ _ hne t ht₁ ht₂ => ?_
        obtain ⟨ch₁, -, ht₁⟩ := List.mem_flatMap.1 ht₁
        obtain ⟨j₁, -, rfl⟩ := List.mem_map.1 ht₁
        obtain ⟨ch₂, -, ht₂⟩ := List.mem_flatMap.1 ht₂
        obtain ⟨j₂, -, h⟩ := List.mem_map.1 ht₂
        exact hne (SfAdrs.chainAdrs_inj.1 h).1.symm
    · have hlen_eq : ((treeOrder P.hsf S P.hsf 0).flatMap
          (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u)) (Scheme.Fxmss.node pr pk)
            (fun id => (List.finRange P.lsf).flatMap fun ch =>
              (List.range (P.w - 1)).map fun j =>
                ((SfAdrs.chainAdrs id ch.val j).toAdrs,
                  WotsC.chain pr pk id ch.val (skOf pr S u id ch.val) 0 j))
            (fun _ _ _ => []))).length =
          anchorsO.length * (P.lsf * (P.w - 1)) := by
        rw [← List.length_map (f := Prod.fst), hmap_eq]
        simp [List.length_flatMap, List.map_const', List.sum_replicate]
      rw [hlen_eq, ← Nat.mul_assoc]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _
        ((anchors_in_treeOrder_length_le S hS).trans (hL hS))) (Nat.sub_le _ _)
    · intro t ht hq
      rw [hmap_eq] at hq
      obtain ⟨id', -, hq⟩ := List.mem_flatMap.1 hq
      obtain ⟨ch', -, hq⟩ := List.mem_flatMap.1 hq
      obtain ⟨j', -, rfl⟩ := List.mem_map.1 hq
      rcases List.mem_append.1 ht with h1 | h2
      · obtain ⟨id, -, h⟩ := List.mem_flatMap.1 h1
        exact SfAdrs.chainAdrs_ne_grindAdrs id' id ch'.val j' (mem_grindSearchLog pr pk id _ _ _ h)
      · obtain ⟨e, -, h⟩ := List.mem_flatMap.1 h2
        rcases e with id | id
        · exact SfAdrs.chainAdrs_ne_pkAdrs id' id ch'.val j' (List.mem_singleton.1 h)
        · simp only [combineLog] at h
          split at h
          · exact SfAdrs.chainAdrs_ne_treeAdrs id' id ch'.val j' (List.mem_singleton.1 h)
          · simp at h
  · simp [hS, TcrGood]

/-- Challenge-plus-collection oracle spec for `B6Pre` (SM-TCR of `Th_lsf`). -/
abbrev Spec6Pre (L : ℕ) :=
  SM_DT_TCR_challengeSpec Adrs (Vector pr.Y P.lsf) pr.Y + collectionSpec (probTcrLsf pr L).thColl

/-- **Stage-1 full-table program for `B6Pre`**: grinds and chains via `O_coll(.grind, .F)`,
compresses leaves via SM-TCR challenge oracle `O_chal(pkAdrs)`, and builds internal nodes via
`O_coll(.H)`. -/
noncomputable def prog6Pre (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : OracleComp (Spec6Pre pr L) (SfFullTable pr) :=
  let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec6Pre pr L) pr.Y := fun t md c => do
    let r ← ((Spec6Pre pr L).query (.inr ⟨some .grind, t, (md, c)⟩) :
      OracleComp (Spec6Pre pr L) (Option pr.Y))
    return r.getD default
  let fOp : Adrs → pr.Y → OracleComp (Spec6Pre pr L) pr.Y := fun t y => do
    let r ← ((Spec6Pre pr L).query (.inr ⟨some .F, t, y⟩) :
      OracleComp (Spec6Pre pr L) (Option pr.Y))
    return r.getD default
  let cOp : Adrs → Vector pr.Y P.lsf → OracleComp (Spec6Pre pr L) pr.Y := fun t v => do
    let r ← ((Spec6Pre pr L).query (.inl (t, v)) : OracleComp (Spec6Pre pr L) (Option pr.Y))
    return r.getD default
  let hOp : Adrs → pr.Y → pr.Y → OracleComp (Spec6Pre pr L) pr.Y := fun t a b => do
    let r ← ((Spec6Pre pr L).query (.inr ⟨some .H, t, (a, b)⟩) :
      OracleComp (Spec6Pre pr L) (Option pr.Y))
    return r.getD default
  buildSfTable0M pr (fun id md => grindSearchOp pr gOp id md (List.finRange (2 ^ P.c)))
    fOp cOp hOp S (digOf pr ys) (skOf pr S u)

/-- Recorded Stage-1 targets for `B6Pre`: `(pkAdrs id, WotsC.pkTops ...)` for every anchor in
`treeOrder`. -/
noncomputable def Q6Pre (S : Structure) (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) :
    List (Adrs × Vector pr.Y P.lsf) :=
  if S.TreeValid P.hsf then
    (treeOrder P.hsf S P.hsf 0).flatMap (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
      (Scheme.Fxmss.node pr pk)
      (fun id => [((SfAdrs.pkAdrs id).toAdrs, WotsC.pkTops pr pk id (skOf pr S u id))])
      (fun _ _ _ => []))
  else []

/-- Collection tweaks spent by `prog6Pre` (`grindAdrs`, `chainAdrs`, `treeAdrs` — never `pkAdrs`). -/
noncomputable def C6Pre (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) : List Adrs :=
  if S.TreeValid P.hsf then
    ((anchorList P S).flatMap fun id =>
      grindSearchLog pr pk id (digOf pr ys id) (List.finRange (2 ^ P.c))) ++
    ((treeOrder P.hsf S P.hsf 0).flatMap fun
      | .inl id =>
        (List.finRange P.lsf).flatMap fun ch =>
          (List.range (P.w - 1)).map fun j => (SfAdrs.chainAdrs id ch.val j).toAdrs
      | .inr id =>
        combineLog (fun _ _ => [(SfAdrs.treeAdrs id).toAdrs])
          (Tree.treeNode P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk) (id.height - 1) (2 * id.index))
          (Tree.treeNode P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk) (id.height - 1) (2 * id.index + 1)))
  else []

theorem prog6Pre_perm_run (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed) :
    (simulateQ (tcrPerm (probTcrLsf pr L) pk) (prog6Pre pr L S ys u)).run ([], []) =
      (buildSfTable0Det pr pk S (digOf pr ys) (skOf pr S u),
        (Q6Pre pr S u pk, C6Pre pr S ys u pk)) := by
  unfold prog6Pre buildSfTable0Det Q6Pre C6Pre
  by_cases hS : S.TreeValid P.hsf
  · rw [simulateQ_buildSfTable0M]
    unfold buildSfTable0M
    simp only [hS, ↓reduceIte]
    let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec6Pre pr L) pr.Y := fun t md c => do
      let r ← ((Spec6Pre pr L).query (.inr ⟨some .grind, t, (md, c)⟩) :
        OracleComp (Spec6Pre pr L) (Option pr.Y))
      return r.getD default
    have hGop : ∀ t md c, IsLog (simulateQ (tcrPerm (probTcrLsf pr L) pk) (gOp t md c))
        (pr.Hgrind pk t md c) [] [t] := fun t md c s => by
      simp [gOp, tcrPerm, id_pure_eq]; rfl
    have hG : ∀ id md, IsLog (simulateQ (tcrPerm (probTcrLsf pr L) pk)
        (grindSearchOp pr gOp id md (List.finRange (2 ^ P.c))))
        (WotsC.grind pr pk id md) [] (grindSearchLog pr pk id md (List.finRange (2 ^ P.c))) := by
      intro id md
      rw [simulateQ_grindSearchOp]
      exact (grindSearchOp_isLog pr pk hGop id md (List.finRange (2 ^ P.c))).of_eq
        (Hyb.grindPure_finRange pr pk id md) rfl rfl
    have hF : ∀ t y, IsLog (simulateQ (tcrPerm (probTcrLsf pr L) pk) (do
        let r ← ((Spec6Pre pr L).query (.inr ⟨some .F, t, y⟩) :
          OracleComp (Spec6Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.F pk t y) [] [t] := fun t y s => by
      simp [tcrPerm, id_pure_eq]; rfl
    have hC : ∀ t v, IsLog (simulateQ (tcrPerm (probTcrLsf pr L) pk) (do
        let r ← ((Spec6Pre pr L).query (.inl (t, v)) : OracleComp (Spec6Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.ThLsf pk t v) [(t, v)] [] := fun t v s => by
      simp [tcrPerm, id_pure_eq]; rfl
    have hH : ∀ t a b, IsLog (simulateQ (tcrPerm (probTcrLsf pr L) pk) (do
        let r ← ((Spec6Pre pr L).query (.inr ⟨some .H, t, (a, b)⟩) :
          OracleComp (Spec6Pre pr L) (Option pr.Y))
        return r.getD default)) (pr.H pk t a b) [] [t] := fun t a b s => by
      simp [tcrPerm, id_pure_eq]; rfl
    have hL := leafRecM_isLog pr pk hF hC (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val)
    have hT := treeTableM_isLog pr S hL (fun id a b => hH (SfAdrs.treeAdrs id).toAdrs a b) P.hsf 0 default
    have hAll := (grindListM_isLog pr hG (digOf pr ys) (anchorList P S)).bind
      (f := fun gf =>
        (treeTableM pr S
          (leafRecM pr
            (fun t y => simulateQ (tcrPerm (probTcrLsf pr L) pk) (do
              let r ← ((Spec6Pre pr L).query (.inr ⟨some .F, t, y⟩) :
                OracleComp (Spec6Pre pr L) (Option pr.Y))
              return r.getD default))
            (fun t v => simulateQ (tcrPerm (probTcrLsf pr L) pk) (do
              let r ← ((Spec6Pre pr L).query (.inl (t, v)) : OracleComp (Spec6Pre pr L) (Option pr.Y))
              return r.getD default))
            (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val))
          (fun id a b => simulateQ (tcrPerm (probTcrLsf pr L) pk) (do
            let r ← ((Spec6Pre pr L).query (.inr ⟨some .H, (SfAdrs.treeAdrs id).toAdrs, (a, b)⟩) :
              OracleComp (Spec6Pre pr L) (Option pr.Y))
            return r.getD default))
          P.hsf 0 default) >>= fun p =>
          pure (assembleSfTable pr gf p.2 (fun id ch => skOf pr S u id ch.val)))
      (hT.bind (IsLog.pure _))
    have hleafEq : (fun id => (leafRecDet pr pk (fun _ _ => 0) (fun id ch => skOf pr S u id ch.val) id).2.2) =
        Scheme.Fxmss.leaf pr pk (skOf pr S u) := by
      funext id; exact (leafRecDet_zero pr pk (skOf pr S u) id).2
    rw [hAll ([], [])]
    have hnil : (anchorList P S).flatMap (fun _ => ([] : List (Adrs × Vector pr.Y P.lsf))) = [] := by simp
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [List.nil_append, List.append_nil, hnil, hleafEq]
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [entryQ, (leafRecDet_zero pr pk (skOf pr S u) id).1]
      · simp only [entryQ, combineLog]; split <;> (split <;> rfl)
    · simp only [List.nil_append, List.append_nil, hleafEq]
      congr 1
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [flatMap_singleton_eq_map]
      · rfl
  · simp [hS, buildSfTable0M, id_pure_eq]

omit [SampleableType pr.PkSeed] in
theorem tcrGood_Q6Pre (L : ℕ) (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) (pk : pr.PkSeed)
    (hL : S.TreeValid P.hsf → S.anchors.card ≤ L) :
    TcrGood L (Q6Pre pr S u pk, C6Pre pr S ys u pk) := by
  unfold Q6Pre C6Pre
  by_cases hS : S.TreeValid P.hsf
  · simp only [hS, ↓reduceIte]
    have hmap_eq : ((treeOrder P.hsf S P.hsf 0).flatMap
        (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u)) (Scheme.Fxmss.node pr pk)
          (fun id => [((SfAdrs.pkAdrs id).toAdrs, WotsC.pkTops pr pk id (skOf pr S u id))])
          (fun _ _ _ => []))).map Prod.fst =
        ((treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none).map
          (fun id => (SfAdrs.pkAdrs id).toAdrs) := by
      rw [List.map_flatMap]
      have hgen : ∀ l : List (LeafId ⊕ LeafId),
          l.flatMap (fun x => (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
            (Scheme.Fxmss.node pr pk)
            (fun id => [((SfAdrs.pkAdrs id).toAdrs, WotsC.pkTops pr pk id (skOf pr S u id))])
            (fun _ _ _ => []) x).map Prod.fst) =
          (l.filterMap fun | .inl id => some id | .inr _ => none).map
            (fun id => (SfAdrs.pkAdrs id).toAdrs) := by
        intro l; induction l with
        | nil => rfl
        | cons e l ih =>
          rcases e with id | id
          · rw [List.flatMap_cons, List.filterMap_cons, List.map_cons, ih]
            rfl
          · have hempty : (entryQ P.hsf S (Scheme.Fxmss.leaf pr pk (skOf pr S u))
                (Scheme.Fxmss.node pr pk)
                (fun id => [((SfAdrs.pkAdrs id).toAdrs, WotsC.pkTops pr pk id (skOf pr S u id))])
                (fun _ _ _ => []) (.inr id)).map Prod.fst = [] := by
              simp only [entryQ, combineLog]; split <;> rfl
            simp only [List.flatMap_cons, hempty, List.nil_append, List.filterMap_cons, ih]
      exact hgen _
    have hndA : ((treeOrder P.hsf S P.hsf 0).filterMap fun | .inl id => some id | .inr _ => none).Nodup := by
      refine List.Nodup.filterMap (fun a b x ha hb => ?_)
        (List.Nodup.of_map posOf (nodup_treeOrder (hsf := P.hsf) (S := S) P.hsf 0))
      rcases a with id₁ | id₁ <;> rcases b with id₂ | id₂ <;> simp at ha hb
      rw [ha, hb]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmap_eq]
      exact hndA.map fun a b h => SfAdrs.pkAdrs_inj.1 h
    · rw [← List.length_map (f := Prod.fst), hmap_eq, List.length_map]
      exact (anchors_in_treeOrder_length_le S hS).trans (hL hS)
    · intro t ht hq
      rw [hmap_eq] at hq
      obtain ⟨id', -, rfl⟩ := List.mem_map.1 hq
      rcases List.mem_append.1 ht with h1 | h2
      · obtain ⟨id, -, h⟩ := List.mem_flatMap.1 h1
        exact SfAdrs.pkAdrs_ne_grindAdrs id' id (mem_grindSearchLog pr pk id _ _ _ h)
      · obtain ⟨e, -, h⟩ := List.mem_flatMap.1 h2
        rcases e with id | id
        · obtain ⟨ch, -, h⟩ := List.mem_flatMap.1 h
          obtain ⟨j, -, h⟩ := List.mem_map.1 h
          exact SfAdrs.chainAdrs_ne_pkAdrs id id' ch.val j h
        · simp only [combineLog] at h
          split at h
          · exact SfAdrs.pkAdrs_ne_treeAdrs id' id (List.mem_singleton.1 h)
          · simp at h
  · simp [hS, TcrGood]

/-- **Stage-1 full-table program for `B7Pre`**: grinds, chains, and compresses leaves via
`O_coll(.grind, .F, .thLsf)`, and computes internal nodes via SM-TCR challenge oracle `O_chal(treeAdrs)`. -/
noncomputable def prog7Pre (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : OracleComp (Spec7 pr) (SfFullTable pr) :=
  let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec7 pr) pr.Y := fun t md c => do
    let r ← ((Spec7 pr).query (.inr ⟨some .grind, t, (md, c)⟩) :
      OracleComp (Spec7 pr) (Option pr.Y))
    return r.getD default
  buildSfTable0M pr (fun id md => grindSearchOp pr gOp id md (List.finRange (2 ^ P.c)))
    (fOp7 pr) (cOp7 pr) (hOp7 pr) S (digOf pr ys) (skOf pr S u)

/-- Collection tweaks spent by `prog7Pre` (`grindAdrs`, `chainAdrs`, `pkAdrs` — never `treeAdrs`). -/
noncomputable def C7Pre (S : Structure) (ys : Anchor P S → pr.Digest) (pk : pr.PkSeed) : List Adrs :=
  if S.TreeValid P.hsf then
    ((anchorList P S).flatMap fun id =>
      grindSearchLog pr pk id (digOf pr ys id) (List.finRange (2 ^ P.c))) ++
    ((treeOrder P.hsf S P.hsf 0).flatMap
      (entryC fun id => chainLog P id ++ [(SfAdrs.pkAdrs id).toAdrs]))
  else []

theorem prog7Pre_perm_run (p : ℕ) {Msg St : Type}
    (d : Setup pr Msg St) (pk : pr.PkSeed) :
    (simulateQ (tcrPerm (probTcrH pr p) pk) (prog7Pre pr d.S d.ys d.u)).run ([], []) =
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u),
        (Q7 pr Msg d pk, C7Pre pr d.S d.ys pk)) := by
  unfold prog7Pre buildSfTable0Det Q7 C7Pre
  by_cases hS : d.S.TreeValid P.hsf
  · rw [simulateQ_buildSfTable0M]
    unfold buildSfTable0M
    simp only [hS, ↓reduceIte]
    let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec7 pr) pr.Y := fun t md c => do
      let r ← ((Spec7 pr).query (.inr ⟨some .grind, t, (md, c)⟩) :
        OracleComp (Spec7 pr) (Option pr.Y))
      return r.getD default
    have hGop : ∀ t md c, IsLog (simulateQ (tcrPerm (probTcrH pr p) pk) (gOp t md c))
        (pr.Hgrind pk t md c) [] [t] := fun t md c s => by
      simp [gOp, tcrPerm, id_pure_eq]; rfl
    have hG : ∀ id md, IsLog (simulateQ (tcrPerm (probTcrH pr p) pk)
        (grindSearchOp pr gOp id md (List.finRange (2 ^ P.c))))
        (WotsC.grind pr pk id md) [] (grindSearchLog pr pk id md (List.finRange (2 ^ P.c))) := by
      intro id md
      rw [simulateQ_grindSearchOp]
      exact (grindSearchOp_isLog pr pk hGop id md (List.finRange (2 ^ P.c))).of_eq
        (Hyb.grindPure_finRange pr pk id md) rfl rfl
    have hL := leafRecM_isLog pr pk (fOp7_isLog pr p pk) (cOp7_isLog pr p pk)
      (fun _ _ => 0) (fun id ch => skOf pr d.S d.u id ch.val)
    have hT := treeTableM_isLog pr d.S hL (fun id a b => hOp7_isLog pr p pk (SfAdrs.treeAdrs id).toAdrs a b)
      P.hsf 0 default
    have hAll := (grindListM_isLog pr hG (digOf pr d.ys) (anchorList P d.S)).bind
      (f := fun gf =>
        (treeTableM pr d.S
          (leafRecM pr (fun t y => simulateQ (tcrPerm (probTcrH pr p) pk) (fOp7 pr t y))
            (fun t v => simulateQ (tcrPerm (probTcrH pr p) pk) (cOp7 pr t v))
            (fun _ _ => 0) (fun id ch => skOf pr d.S d.u id ch.val))
          (fun id a b => simulateQ (tcrPerm (probTcrH pr p) pk) (hOp7 pr (SfAdrs.treeAdrs id).toAdrs a b))
          P.hsf 0 default) >>= fun q =>
          pure (assembleSfTable pr gf q.2 (fun id ch => skOf pr d.S d.u id ch.val)))
      (hT.bind (IsLog.pure _))
    have hleafEq : (fun id => (leafRecDet pr pk (fun _ _ => 0) (fun id ch => skOf pr d.S d.u id ch.val) id).2.2) =
        Scheme.Fxmss.leaf pr pk (skOf pr d.S d.u) := by
      funext id; exact (leafRecDet_zero pr pk (skOf pr d.S d.u) id).2
    rw [hAll ([], [])]
    have hnil : (anchorList P d.S).flatMap (fun _ => ([] : List (Adrs × (pr.Y × pr.Y)))) = [] := by simp
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [List.nil_append, List.append_nil, hnil, hleafEq]
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [entryQ]
      · rfl
    · simp only [List.nil_append, List.append_nil, hleafEq]
      congr 1
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [entryC, chainLog, flatMap_singleton_eq_map]
      · simp only [entryC, combineLog]; split <;> rfl
  · simp [hS, buildSfTable0M, id_pure_eq]

/-- **Stage-1 full-table program for `B8Pre`**: grinds and chains via `O_coll(.grind, .F)`, and
computes both anchor compressions (`pkAdrs`) and internal nodes (`treeAdrs`) via the sm-tcr-excl
challenge oracle. -/
noncomputable def prog8Pre (S : Structure) (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : OracleComp (Spec9 pr) (SfFullTable pr) :=
  let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec9 pr) pr.Y := fun t md c => do
    let r ← ((Spec9 pr).query (.inr ⟨.grind, t, (md, c)⟩) :
      OracleComp (Spec9 pr) (Option pr.Y))
    return r.getD default
  buildSfTable0M pr (fun id md => grindSearchOp pr gOp id md (List.finRange (2 ^ P.c)))
    (fOp9 pr) (cOp9 pr) (hOp9 pr) S (digOf pr ys) (skOf pr S u)

/-- Collection tweaks spent by `prog8Pre` (`grindAdrs`, `chainAdrs` — never in `Ω(pkAdrs/treeAdrs)`). -/
noncomputable def C8Pre (S : Structure) (ys : Anchor P S → pr.Digest) (pk : pr.PkSeed) : List Adrs :=
  if S.TreeValid P.hsf then
    ((anchorList P S).flatMap fun id =>
      grindSearchLog pr pk id (digOf pr ys id) (List.finRange (2 ^ P.c))) ++
    ((treeOrder P.hsf S P.hsf 0).flatMap (entryC (chainLog P)))
  else []

theorem prog8Pre_perm_run (p : ℕ) {Msg St : Type}
    (d : Setup pr Msg St) (pk : pr.PkSeed) :
    (simulateQ (exclPerm (probExcl pr p) pk) (prog8Pre pr d.S d.ys d.u)).run ([], []) =
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u),
        (Q9 pr Msg d pk, C8Pre pr d.S d.ys pk)) := by
  unfold prog8Pre buildSfTable0Det Q9 C8Pre
  by_cases hS : d.S.TreeValid P.hsf
  · rw [simulateQ_buildSfTable0M]
    unfold buildSfTable0M
    simp only [hS, ↓reduceIte]
    let gOp : Adrs → pr.Digest → Fin (2 ^ P.c) → OracleComp (Spec9 pr) pr.Y := fun t md c => do
      let r ← ((Spec9 pr).query (.inr ⟨.grind, t, (md, c)⟩) :
        OracleComp (Spec9 pr) (Option pr.Y))
      return r.getD default
    have hGop : ∀ t md c, IsLog (simulateQ (exclPerm (probExcl pr p) pk) (gOp t md c))
        (pr.Hgrind pk t md c) [] [t] := fun t md c s => by
      simp [gOp, exclPerm, id_pure_eq]; rfl
    have hG : ∀ id md, IsLog (simulateQ (exclPerm (probExcl pr p) pk)
        (grindSearchOp pr gOp id md (List.finRange (2 ^ P.c))))
        (WotsC.grind pr pk id md) [] (grindSearchLog pr pk id md (List.finRange (2 ^ P.c))) := by
      intro id md
      rw [simulateQ_grindSearchOp]
      exact (grindSearchOp_isLog pr pk hGop id md (List.finRange (2 ^ P.c))).of_eq
        (Hyb.grindPure_finRange pr pk id md) rfl rfl
    have hL := leafRecM_isLog pr pk (fOp9_isLog pr p pk) (cOp9_isLog pr p pk)
      (fun _ _ => 0) (fun id ch => skOf pr d.S d.u id ch.val)
    have hT := treeTableM_isLog pr d.S hL (fun id a b => hOp9_isLog pr p pk (SfAdrs.treeAdrs id).toAdrs a b)
      P.hsf 0 default
    have hAll := (grindListM_isLog pr hG (digOf pr d.ys) (anchorList P d.S)).bind
      (f := fun gf =>
        (treeTableM pr d.S
          (leafRecM pr (fun t y => simulateQ (exclPerm (probExcl pr p) pk) (fOp9 pr t y))
            (fun t v => simulateQ (exclPerm (probExcl pr p) pk) (cOp9 pr t v))
            (fun _ _ => 0) (fun id ch => skOf pr d.S d.u id ch.val))
          (fun id a b => simulateQ (exclPerm (probExcl pr p) pk) (hOp9 pr (SfAdrs.treeAdrs id).toAdrs a b))
          P.hsf 0 default) >>= fun q =>
          pure (assembleSfTable pr gf q.2 (fun id ch => skOf pr d.S d.u id ch.val)))
      (hT.bind (IsLog.pure _))
    have hleafEq : (fun id => (leafRecDet pr pk (fun _ _ => 0) (fun id ch => skOf pr d.S d.u id ch.val) id).2.2) =
        Scheme.Fxmss.leaf pr pk (skOf pr d.S d.u) := by
      funext id; exact (leafRecDet_zero pr pk (skOf pr d.S d.u) id).2
    rw [hAll ([], [])]
    have hnil : (anchorList P d.S).flatMap (fun _ => ([] : List (Adrs × Msg9 pr))) = [] := by simp
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [List.nil_append, List.append_nil, hnil, hleafEq]
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [entryQ, (leafRecDet_zero pr pk (skOf pr d.S d.u) id).1]
      · rfl
    · simp only [List.nil_append, List.append_nil, hleafEq]
      congr 1
      refine List.flatMap_congr fun e _ => ?_
      rcases e with id | id
      · simp [entryC, chainLog, flatMap_singleton_eq_map]
      · simp only [entryC, combineLog]; split <;> rfl
  · simp [hS, buildSfTable0M, id_pure_eq]

/-! ### Shared Stage-1 program for `B3Pre γ` and `B5Pre` (`pickProgPre`) -/

/-- **Shared Stage-1 full-table program for `B3Pre γ` and `B5Pre`**: grinds all anchors via
`O_coll(.grind)`, queries `O_chal` on `targetsOf sel gf` updating `u`, and builds the full
stateful table `SfFullTable` via `O_coll(.F, .thLsf, .H)` at strictly higher chain positions. -/
noncomputable def pickProgPre [SampleableType pr.Y] (sel : ℕ → Option ℕ) (startOf : ℕ → ℕ)
    {S : Structure} (ys : Anchor P S → pr.Digest) (u : SkIdx P S → pr.Y) :
    OracleComp (Hyb.FSpec pr) (SfFullTable pr × List (SkIdx P S × Adrs)) :=
  if S.TreeValid P.hsf then do
    let gf ← Hyb.grindAll pr ys (Hyb.anchorsL S)
    let tgs := Hyb.targetsOf pr sel gf
    let u' ← Hyb.queryAll pr tgs u
    let tbl ← buildSfTableHybM pr startOf gf u'
    return (tbl, tgs)
  else
    pure (default, [])

/-- Generic run theorem for `pickProgPre` against any `(CollAnswers, ChalAnswers)` handler
(covers both `SM_DT_UD_oracles` and `SM_DT_PRE_oracles`). -/
theorem run_pickProgPre [SampleableType pr.Y] {Q : Type} {tweakOf : Q → Adrs} {N : ℕ}
    {pk : pr.PkSeed} {ans : Adrs → pr.Y → pr.Y} {rec : Adrs → pr.Y → Q}
    {impl : QueryImpl (Hyb.FSpec pr) (StateT (List Q × List Adrs) ProbComp)}
    (hcoll : Hyb.CollAnswers pr tweakOf pk impl)
    (hchal : Hyb.ChalAnswers pr tweakOf N ans rec impl)
    (hrec : ∀ t x, tweakOf (rec t x) = t)
    (sel : ℕ → Option ℕ) (startOf : ℕ → ℕ)
    (hdisStart : ∀ a < P.w, ∀ j, sel a = some j → j < startOf a)
    {S : Structure} (ys : Anchor P S → pr.Digest) (u : SkIdx P S → pr.Y)
    (hN : (Hyb.targets pr pk sel S ys).length ≤ N) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ impl (pickProgPre pr sel startOf ys u)).run ([], []) =ᵈ
      (fun z => ((if S.TreeValid P.hsf then
          buildSfTableHybDet pr pk startOf (fun a => WotsC.grind pr pk a.1 (digOf pr ys a.1)) z.1
        else default, Hyb.targets pr pk sel S ys), z.2)) <$>
        Hyb.runRef ans rec (Hyb.targets pr pk sel S ys) u [] := by
  unfold pickProgPre
  by_cases hS : S.TreeValid P.hsf
  · obtain ⟨tws, htws, hr⟩ := Hyb.run_grindAll hcoll ys (Hyb.anchorsL S) [] (by simp [Hyb.GrindOnly])
    set gfDet : Anchor P S → Option (pr.Y × Fin (2 ^ P.c)) :=
      fun a => WotsC.grind pr pk a.1 (digOf pr ys a.1)
    have hgf : (fun a : Anchor P S => if a ∈ Hyb.anchorsL S then
        WotsC.grind pr pk a.1 (digOf pr ys a.1) else none) = gfDet := by
      funext a; simp [Hyb.anchorsL, gfDet]
    simp only [hS, ↓reduceIte, Hyb.targets] at hN ⊢
    rw [simulateQ_bind, StateT.run_bind, hr, pure_bind, hgf, simulateQ_bind, StateT.run_bind,
      Hyb.run_queryAll hchal hrec _ _ _ _ (Hyb.nodup_map_snd_targetsOf pr sel _) ?_ (by simpa using hN),
      bind_map_left, map_bind, map_eq_bind_pure_comp]
    · refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
      have hqs_sub : ∀ e ∈ z.2, ∃ pt ∈ Hyb.targetsOf pr sel gfDet, tweakOf e = pt.2 := by
        have hsub : ∀ (l : List (SkIdx P S × Adrs)) (u₀ : SkIdx P S → pr.Y) (qs₀ : List Q)
            (w : (SkIdx P S → pr.Y) × List Q),
            w ∈ support (Hyb.runRef ans rec l u₀ qs₀) →
            ∀ e ∈ w.2, e ∈ qs₀ ∨ ∃ pt ∈ l, tweakOf e = pt.2 := by
          intro l; induction l with
          | nil =>
            intro u₀ qs₀ w hw e he
            simp only [Hyb.runRef, support_pure, Set.mem_singleton_iff] at hw
            subst hw; exact Or.inl he
          | cons pt ts ih =>
            intro u₀ qs₀ w hw e he
            simp only [Hyb.runRef, mem_support_bind_iff] at hw
            obtain ⟨x, -, hw⟩ := hw
            rcases ih _ _ w hw e he with hq | ⟨pt', hpt', heq⟩
            · rcases List.mem_append.1 hq with hq | hq
              · exact Or.inl hq
              · rw [List.mem_singleton.1 hq]; exact Or.inr ⟨pt, by simp, hrec _ _⟩
            · exact Or.inr ⟨pt', by simp [hpt'], heq⟩
        intro e he
        exact (hsub _ _ _ z hz e he).resolve_left (by simp)
      obtain ⟨tws', htbl⟩ := run_buildSfTableHybM pr hcoll startOf gfDet z.1 z.2 tws
        (fun id hid ch j hj ⟨e, he, hte⟩ => by
          obtain ⟨pt, hpt, hte'⟩ := hqs_sub e he
          obtain ⟨j₀, hj₀, hpt2⟩ := (Hyb.mem_targetsOf pr).1 hpt
          rw [hte', hpt2] at hte
          obtain ⟨hid', hch', hjeq⟩ := SfAdrs.chainAdrs_inj.1 hte
          have hpt1 : pt.1 = (⟨id, hid⟩, ch) := Prod.ext (Subtype.ext hid') (Fin.ext hch')
          rw [hpt1] at hj₀
          have hlt := hdisStart (Hyb.relDigOf pr (gfDet ⟨id, hid⟩) ch.val)
            (Hyb.relDigOf_lt _ _) j₀ hj₀
          omega)
        (fun id ⟨e, he, hte⟩ => by
          obtain ⟨pt, hpt, hte'⟩ := hqs_sub e he
          obtain ⟨j₀, -, hpt2⟩ := (Hyb.mem_targetsOf pr).1 hpt
          rw [hte', hpt2] at hte
          exact SfAdrs.chainAdrs_ne_pkAdrs _ _ _ _ hte)
        (fun id ⟨e, he, hte⟩ => by
          obtain ⟨pt, hpt, hte'⟩ := hqs_sub e he
          obtain ⟨j₀, -, hpt2⟩ := (Hyb.mem_targetsOf pr).1 hpt
          rw [hte', hpt2] at hte
          exact SfAdrs.chainAdrs_ne_treeAdrs _ _ _ _ hte)
      rw [simulateQ_bind, StateT.run_bind, htbl, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · intro t ht
      refine ⟨by simp [TweakReserved], fun htw => ?_⟩
      obtain ⟨id, rfl⟩ := htws _ htw
      obtain ⟨⟨p, t'⟩, hpt, rfl⟩ := List.mem_map.1 ht
      obtain ⟨j, -, he⟩ := (Hyb.mem_targetsOf pr).1 hpt
      exact SfAdrs.chainAdrs_ne_grindAdrs _ _ _ _ he.symm
  · simp [hS, Hyb.targets, Hyb.runRef]

end Stage1Programs

/-! ## 2. Theorem 4.2: Stage-1-full-precomputing reductions `B2Pre … B8Pre` and Stage-2 bounds -/

section Theorem42Precomp

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-! ### The seven Stage-1-full-precomputing FXMSS reductions `B2Pre … B8Pre` -/

/-- **Stage-1-full-precomputing `B₂`** (`S-TCR(Prop)` of `H_grind ∈ Th_λ`, `L` targets). -/
noncomputable def B2Pre {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Notions.STCRAdversary (probGrind pr L) where
  State := Setup pr Msg A.State × SfFullTable pr × List ((Adrs × pr.Digest) × (pr.Y × ℕ))
  choose := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (STcrOracleSpec (probGrind pr L)) _)
    let (tbl, savedQ) ← (simulateQ (recordSTcrImpl (probGrind pr L))
      (OracleComp.liftComp (prog2Pre pr L d.S d.ys d.u) _)).run []
    return (d, tbl, savedQ)
  forge := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2.1) (fun st => st.1) (fun st o => extract2Trace pr Msg st.2.2 o)

/-- **Stage-1-full-precomputing `B₃,γ`** (`SM-UD` of `F ∈ Th_λ`, `L · lsf` targets). -/
noncomputable def B3Pre (γ : ℕ) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Adversary (probUD pr (L * P.lsf)) where
  State := Setup pr Msg A.State × SfFullTable pr
  pick := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (Hyb.FSpec pr) _)
    let (tbl, _) ← pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u
    return (d, tbl)
  distinguish := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2) (fun st => st.1) (fun st o => dist3Trace pr Msg st.1.S st.2 o)

/-- **Stage-1-full-precomputing `B₄`** (`SM-TCR` of `F ∈ Th_λ`, `L · lsf · w` targets). -/
noncomputable def B4Pre {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrF pr (L * P.lsf * P.w)) where
  State := Setup pr Msg A.State × SfFullTable pr × List (Adrs × pr.Y)
  choose := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (TcrOracleSpec (probTcrF pr (L * P.lsf * P.w))) _)
    let (tbl, savedQ) ← (simulateQ (recordTcrImpl (probTcrF pr (L * P.lsf * P.w)))
      (OracleComp.liftComp (prog4Pre pr L d.S d.ys d.u) _)).run []
    return (d, tbl, savedQ)
  forge := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2.1) (fun st => st.1) (fun st o => extract4Trace pr Msg st.1.S st.2.1 st.2.2 o)

/-- **Stage-1-full-precomputing `B₅`** (`SM-PRE` of `F ∈ Th_λ`, `L · lsf` targets). -/
noncomputable def B5Pre {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_PRE_Adversary (probPre pr (L * P.lsf)) where
  State := (d : Setup pr Msg A.State) × SfFullTable pr × List (SkIdx P d.S × Adrs)
  choose := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (Hyb.FSpec pr) _)
    let (tbl, tgs) ← pickProgPre pr Hyb.selPre id d.ys d.u
    return ⟨d, tbl, tgs⟩
  invert := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2.1) (fun st => st.1) (fun st o => extract5Trace pr Msg st.2.1 st.2.2 o)

/-- **Stage-1-full-precomputing `B₆`** (`SM-TCR` of `Th_lsf ∈ Th_λ`, `L` targets). -/
noncomputable def B6Pre {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrLsf pr L) where
  State := Setup pr Msg A.State × SfFullTable pr × List (Adrs × Vector pr.Y P.lsf)
  choose := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (TcrOracleSpec (probTcrLsf pr L)) _)
    let (tbl, savedQ) ← (simulateQ (recordTcrImpl (probTcrLsf pr L))
      (OracleComp.liftComp (prog6Pre pr L d.S d.ys d.u) _)).run []
    return (d, tbl, savedQ)
  forge := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2.1) (fun st => st.1) (fun st o => extract6Trace pr Msg st.1.S st.2.1 st.2.2 o)

/-- **Stage-1-full-precomputing `B₇`** (`SM-TCR` of `H ∈ Th_λ`, `L − 1` targets). -/
noncomputable def B7Pre {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrH pr (L - 1)) where
  State := Setup pr Msg A.State × SfFullTable pr × List (Adrs × (pr.Y × pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (TcrOracleSpec (probTcrH pr (L - 1))) _)
    let (tbl, savedQ) ← (simulateQ (recordTcrImpl (probTcrH pr (L - 1)))
      (OracleComp.liftComp (prog7Pre pr d.S d.ys d.u) _)).run []
    return (d, tbl, savedQ)
  forge := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2.1) (fun st => st.1) (fun st o => extract7Trace pr Msg st.2.1 st.2.2 o)

/-- **Stage-1-full-precomputing `B₈`** (`sm-tcr-excl` of `Th_{2∪lsf} ∈ Th_λ`, `L + (L − 1)` targets). -/
noncomputable def B8Pre {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Notions.SMTCRExclAdversary (probExcl pr (L + (L - 1))) where
  State := Setup pr Msg A.State × SfFullTable pr × List (Adrs × Msg9 pr)
  choose := do
    let d ← (liftM (setupHyb pr Msg slKeygen A.toFxmssAdversary) :
      OracleComp (ExclOracleSpec (probExcl pr (L + (L - 1)))) _)
    let (tbl, savedQ) ← (simulateQ (recordExclImpl (probExcl pr (L + (L - 1))))
      (OracleComp.liftComp (prog8Pre pr d.S d.ys d.u) _)).run []
    return (d, tbl, savedQ)
  forge := stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
    (fun st => st.2.1) (fun st => st.1) (fun st o => extract8Trace pr Msg st.2.1 st.2.2 o)

/-! ### Stage-2 `≤ ξ + V_sf` (`V_sf = 497`) complexity bounds for `B2Pre … B8Pre` -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Theorem 4.2 Stage-2 `Th_λ` complexity bounds**: every stateful collection reduction
`B2Pre, B3Pre γ, B4Pre, B5Pre, B6Pre, B7Pre, B8Pre` built from a `BudgetedFxmssForger` with
Stage-2 `Th_λ` budget `ξ` makes at most `ξ + Vsf P` (`ξ + 497` at SHRINCS parameters) Stage-2
`Th_λ` evaluations. -/
noncomputable def theorem_4_2_stage2Bounds {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedFxmssForger pr Msg slKeygen qs qh₁ qh₂ L ξ) :
    STcrStage2Bound pr (B2Pre pr Msg slKeygen A.toForger) (ξ + Vsf P) ×
    (∀ γ, UdStage2Bound pr (B3Pre pr Msg slKeygen γ A.toForger) (ξ + Vsf P)) ×
    TcrStage2Bound pr (B4Pre pr Msg slKeygen A.toForger) (ξ + Vsf P) ×
    PreStage2Bound pr (B5Pre pr Msg slKeygen A.toForger) (ξ + Vsf P) ×
    TcrStage2Bound pr (B6Pre pr Msg slKeygen A.toForger) (ξ + Vsf P) ×
    TcrStage2Bound pr (B7Pre pr Msg slKeygen A.toForger) (ξ + Vsf P) ×
    ExclStage2Bound pr (B8Pre pr Msg slKeygen A.toForger) (ξ + Vsf P) :=
  ⟨stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _,
   fun _ => stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _,
   stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _,
   stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _,
   stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _,
   stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _,
   stage2RunWithTrace_stage2Bound pr Msg slKeygen (fun _ => A) _ _ _⟩

/-! ### Helper: relate `stage2RunWithTrace` on `SfTableAgree` to `stageHyb` -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem stage2RunWithTrace_eq_map_stageHyb {S α : Type} {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (tblOf : S → SfFullTable pr)
    (dOf : S → Setup pr Msg A.State) (pk : pr.PkSeed) (st : S)
    (htbl : (dOf st).S.TreeValid P.hsf →
      SfTableAgree pr (hon pr (dOf st).S pk (digOf pr (dOf st).ys) β) (tblOf st))
    (post : S → Option (Transcript pr Msg × Option (FxmssTrace pr)) → α) :
    stage2RunWithTrace pr Msg slKeygen (fun _ : S => A) tblOf dOf post st pk =
      (fun o : Option (Transcript pr Msg × Honest pr) =>
        match o with
        | none => post st none
        | some (tr, _) =>
          match tr.σf.2 with
          | none => post st (some (tr, none))
          | some w => post st (some (tr, fxmssExtractTable pr pk tr.idf tr.yf w))) <$>
        stageHyb pr Msg slKeygen A β (dOf st) pk := by
  unfold stage2RunWithTrace
  rw [stageHybPre_eq_map_stageHyb pr Msg slKeygen A β (dOf st) pk (tblOf st) htbl, bind_map_left,
    map_eq_bind_pure_comp]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨tr, H⟩
  · rfl
  · dsimp only [Option.map_some, Function.comp_apply]
    cases tr.σf.2 <;> rfl

/-! ### Security proofs `claim_4_3_pre … claim_4_9_pre` and `theorem_4_2_precomp` -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] in
private theorem B2Pre_exp_eq (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    STCR_Experiment (B2Pre pr Msg slKeygen A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q2Pre pr L d.S d.ys pk
          let out ← (B2Pre pr Msg slKeygen A).forge (d, tbl, Q) pk
          return STCR_IsCollision (probGrind pr L) pk Q out) := by
  unfold STCR_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B2Pre, STCR_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hrec := simulateQ_recordSTcr_run (probGrind pr L) pk
    (OracleComp.liftComp (prog2Pre pr L d.S d.ys d.u) _) [] []
  have hgood := stcrGood_Q2Pre pr L d.S d.ys d.u pk
    (fun hS => setupHyb_length_anchorList_le pr Msg slKeygen A hd hS)
  rw [stcr_run_eq _ _ _ (by rw [prog2Pre_perm_run pr hP hgc]; exact hgood),
    prog2Pre_perm_run pr hP hgc, map_pure] at hrec
  simp only [STCR_oracles, unifFwd, STcrOracleSpec] at hrec ⊢
  rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] in
/-- **Claim 4.3 (Stage-1-precomputing `B2Pre`)**. -/
theorem claim_4_3_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEventValid pr Msg Honest.E3 o] ≤
      Notions.STCR_Succ (B2Pre pr Msg slKeygen A) := by
  unfold STCR_Succ
  rw [(B2Pre_exp_eq pr Msg slKeygen hP hgc A).evalDist_eq, ← prEvent_eq_evalDist_singleton]
  unfold gameHyb
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono' _ _ _ fun pk _ => prEvent_bind_mono' _ _ _ fun d hd => ?_
  set tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
  set Q := Q2Pre pr L d.S d.ys pk
  have hst := stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (betaOf pr 0 pk d.u) (fun st : (B2Pre pr Msg slKeygen A).State => st.2.1)
    (fun st => st.1) pk (d, tbl, Q)
    (fun hS => buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u)
    (fun st o => extract2Trace pr Msg st.2.2 o)
  rw [show ((B2Pre pr Msg slKeygen A).forge (d, tbl, Q) pk >>= fun a =>
        pure (STCR_IsCollision (probGrind pr L) pk Q a = true)) =
      (fun a => STCR_IsCollision (probGrind pr L) pk Q a = true) <$>
        (B2Pre pr Msg slKeygen A).forge (d, tbl, Q) pk by rw [map_eq_bind_pure_comp]; rfl]
  dsimp only [B2Pre] at hst ⊢
  rw [hst, Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
  obtain ⟨w, hw, hval, hid, hne, henc⟩ := hE
  obtain ⟨ft, hft, hdStar, -, -, -, -, -, -⟩ := fxmssExtractTable_eq_some pr pk tr.idf tr.yf w hval
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  have hlc := leastCounter_thGrind pr hg
  have hev : (thGrind pr).eval pk (SfAdrs.grindAdrs tr.idf).toAdrs (digOf pr d.ys tr.idf, c.val) =
      WotsC.encode pr pk tr.idf (digOf pr d.ys tr.idf) c := by
    simp [thGrind, TweakableHash.ofFun, WotsC.encode, Nat.mod_eq_of_lt c.isLt]
  have hmem : (((SfAdrs.grindAdrs tr.idf).toAdrs, digOf pr d.ys tr.idf),
      (WotsC.encode pr pk tr.idf (digOf pr d.ys tr.idf) c, c.val)) ∈ Q := by
    simp only [Q, Q2Pre, hS, ↓reduceIte, List.mem_flatMap]
    refine ⟨tr.idf, mem_anchorList.2 hid, ?_⟩
    simp [hlc, hev]
  have hd_eq : WotsC.encode pr pk tr.idf (digOf pr d.ys tr.idf) c = ft.dStar := by
    have h1 := hon_encoded pr (S := d.S) (β := betaOf pr 0 pk d.u) hg
    exact h1.symm.trans (henc.symm.trans hdStar.symm)
  have hsome : (Q.findIdx? fun e =>
      decide (e.1.1 = (SfAdrs.grindAdrs tr.idf).toAdrs ∧ e.2.1 = ft.dStar ∧ tr.yf ≠ e.1.2)).isSome := by
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hmem, by simp only [decide_eq_true_eq]; exact ⟨trivial, hd_eq, hne⟩⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hjlt, hjp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [decide_eq_true_eq] at hjp
  obtain ⟨hp1, hp2, hp3⟩ := hjp
  have hQeq : ∀ e ∈ Q, e.2.1 = (thGrind pr).eval pk e.1.1 (e.1.2, e.2.2) := by
    intro e he
    simp only [Q, Q2Pre, hS, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨id', -, he⟩ := he
    cases hlc' : leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id').toAdrs
        (digOf pr d.ys id') with
    | none => simp [hlc'] at he
    | some i' =>
      simp only [hlc', List.mem_singleton] at he
      rw [he]
  have hej := hQeq Q[j] (List.getElem_mem hjlt)
  have h3 : (thGrind pr).eval pk (SfAdrs.grindAdrs tr.idf).toAdrs (tr.yf, w.wots.ctr.val) = ft.dStar := by
    rw [hdStar]; simp [thGrind, TweakableHash.ofFun, WotsC.encode, Nat.mod_eq_of_lt w.wots.ctr.isLt]
  simp only [hw, hft, extract2Trace, hj, STCR_IsCollision, List.getElem?_eq_getElem hjlt]
  simp only [decide_eq_true_eq]
  exact ⟨by rw [← hej, hp2, hp1, h3], hp3⟩

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B3Pre_exp_eq (hP : P.Valid) (hgc : GrindComplete pr) (w : SM_DT_UD_World) (γ : ℕ)
    {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment w (B3Pre pr Msg slKeygen γ A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let u' ← Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u
          (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
            stageHyb pr Msg slKeygen A.toFxmssAdversary (betaOf pr (γ + 1) pk u') d pk) := by
  unfold SM_DT_UD_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B3Pre, SM_DT_UD_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hcoll : Hyb.CollAnswers pr (id : Adrs → Adrs) pk
      (unifFwd (SM_DT_UD_State Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
        collectionOracle id (probUD pr (L * P.lsf)).thColl pk)) := by
    intro q qs tws hq
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
    exact collectionOracle_run_of_fresh id q hq
  have hchal : Hyb.ChalAnswers pr (id : Adrs → Adrs) (L * P.lsf) (Hyb.udAns pr w pk)
      (fun t _ => t)
      (unifFwd (SM_DT_UD_State Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
        collectionOracle id (probUD pr (L * P.lsf)).thColl pk)) := by
    intro t qs tws hlen hfr
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    cases w
    · exact SM_DT_UD_challengeOracle_run_of_fresh_real hlen hfr
    · exact SM_DT_UD_challengeOracle_run_of_fresh_ideal hlen hfr
  have hrun := run_pickProgPre pr hcoll hchal (fun _ _ => rfl) (Hyb.selUD γ)
    (fun a => min (γ + 1) (a - 1))
    (fun a _ j hj => by
      simp only [Hyb.selUD] at hj; split_ifs at hj with hγ; cases hj; omega)
    d.ys d.u (Hyb.targets_length_le pr slKeygen A pk (Hyb.selUD γ) hd)
  have hmap : Prod.fst <$>
      (simulateQ (unifFwd (SM_DT_UD_State Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
        collectionOracle id (probUD pr (L * P.lsf)).thColl pk))
        (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], []) =ᵈ
      (fun u' => (if d.S.TreeValid P.hsf then
          buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
            (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) u'
        else default, Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys)) <$>
        Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u := by
    have h1 := hrun.map Prod.fst
    rw [Functor.map_map, Functor.map_map] at h1
    have h2 : (fun z : (SkIdx P d.S → pr.Y) × List Adrs =>
          (if d.S.TreeValid P.hsf then
            buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
              (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
          else default, Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys)) <$>
          Hyb.runRef (Hyb.udAns pr w pk) (fun t _ => t) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u [] =
        (fun u' => (if d.S.TreeValid P.hsf then
            buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
              (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) u'
          else default, Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys)) <$>
          Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u := by
      rw [← Hyb.map_fst_runRef (Hyb.udAns pr w pk) (fun t _ => t)
        (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u [], Functor.map_map]
    exact h1.trans (Hyb.evalDistEq_of_eq h2)
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  have hsimp : (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
      (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
        collectionOracle id (probUD pr (L * P.lsf)).thColl pk))
      (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], []) >>=
      (fun z => (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
        (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
          collectionOracle id (probUD pr (L * P.lsf)).thColl pk))
        (pure (d, z.1.1))).run z.2 >>= fun p =>
        stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
          (fun st : Setup pr Msg A.State × SfFullTable pr => st.2) (fun st => st.1)
          (fun st o => dist3Trace pr Msg st.1.S st.2 o) p.1 pk) =
      (Prod.fst <$> (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
        (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
          collectionOracle id (probUD pr (L * P.lsf)).thColl pk))
        (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], [])) >>=
      fun tblTgs => stage2RunWithTrace pr Msg slKeygen (fun _ => A.toFxmssAdversary)
        (fun st : Setup pr Msg A.State × SfFullTable pr => st.2) (fun st => st.1)
        (fun st o => dist3Trace pr Msg st.1.S st.2 o) (d, tblTgs.1) pk := by
    simp [bind_map_left]
  refine (Hyb.evalDistEq_of_eq hsimp).trans ?_
  refine (hmap.bind_left _).trans ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun u' => ?_
  set tbl := if d.S.TreeValid P.hsf then
    buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
      (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) u' else default
  have hagree : d.S.TreeValid P.hsf →
      SfTableAgree pr (hon pr d.S pk (digOf pr d.ys) (betaOf pr (γ + 1) pk u')) tbl := fun hS => by
    simp only [tbl, hS, ↓reduceIte]
    exact buildSfTableHybDet_agree pr hP hgc hS pk d.ys u' (fun a => min (γ + 1) (a - 1))
      (betaOf pr (γ + 1) pk u') (fun a _ => by omega) (fun _ _ _ => rfl)
  rw [stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (betaOf pr (γ + 1) pk u') (fun st : Setup pr Msg A.State × SfFullTable pr => st.2)
    (fun st => st.1) pk (d, tbl) hagree
    (fun st o => dist3Trace pr Msg st.1.S st.2 o)]
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine EvalDistEq.bind_congr_of_support _ fun o ho => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact Hyb.evalDistEq_of_eq (by
      simp only [Function.comp_apply, dist3Trace]
      exact congrArg pure (decide_eq_false (show ¬ HybEventValid pr Msg Honest.E6 none from id)).symm)
  · obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
    have h3 := dist3Trace_eq_decide pr Msg _ tbl (hagree hS) tr
    cases hσ : tr.σf.2 <;> (
      simp only [hσ] at h3
      exact Hyb.evalDistEq_of_eq (by simp only [Function.comp_apply, hσ]; exact congrArg pure h3))

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem stageHyb_E6Valid_congr {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β₁ β₂ : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed)
    (h : ∀ id ∈ leafIds P.hsf d.S, ∀ ch : Fin P.lsf,
      β₁ id ch (Hyb.relDig pr pk (digOf pr d.ys) id ch) =
        β₂ id ch (Hyb.relDig pr pk (digOf pr d.ys) id ch)) :
    (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$> stageHyb pr Msg slKeygen A β₁ d pk =
      (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$> stageHyb pr Msg slKeygen A β₂ d pk := by
  have hA := Hyb.hon_agree (pr := pr) d.S pk (digOf pr d.ys) β₁ β₂ h
  by_cases hS : d.S.TreeValid P.hsf
  · simp only [stageHyb, hS, not_true_eq_false, ite_false, map_bind]
    refine bind_congr fun pkSl => ?_
    rw [hA.pkSf, Hyb.implHyb_congr Msg _ hA rfl]
    refine bind_congr fun r => ?_
    simp only [map_pure]
    congr 1
    rw [decide_eq_decide]
    simp only [HybEventValid, hA.E6, hA.pk]
  · simp only [stageHyb, hS, not_false_eq_true, ite_true]

/-- Event `HybEventValid Honest.E6` as a function of the revealed-blocks table `w`. -/
private noncomputable def evE6Valid {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (pk : pr.PkSeed) (w : SkIdx P d.S → pr.Y) : ProbComp Bool :=
  (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
    stageHyb pr Msg slKeygen A (fun id ch _ => skOf pr d.S w id ch) d pk

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem stageHyb_betaOf_E6Valid_eq {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (γ : ℕ) (d : Setup pr Msg A.State) (pk : pr.PkSeed) (u : SkIdx P d.S → pr.Y) :
    (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        stageHyb pr Msg slKeygen A (betaOf pr γ pk u) d pk =
      evE6Valid pr Msg slKeygen A d pk (Hyb.viewOf pr γ pk d.ys u) :=
  stageHyb_E6Valid_congr pr Msg slKeygen A _ _ d pk fun id hid ch => by
    simp only [betaOf, Hyb.skOf_anchor pr u hid ch, Hyb.skOf_anchor pr _ hid ch, Hyb.viewOf]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem evE6Valid_invalid {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (hS : ¬ d.S.TreeValid P.hsf) (pk : pr.PkSeed)
    (w : SkIdx P d.S → pr.Y) :
    evE6Valid pr Msg slKeygen A d pk w = pure false := by
  simp only [evE6Valid, stageHyb, hS, not_false_eq_true, ↓reduceIte, map_pure]
  exact congrArg pure (decide_eq_false (show ¬ HybEventValid pr Msg Honest.E6 none from id))

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B3Pre_real_eq (hP : P.Valid) (hgc : GrindComplete pr) (γ : ℕ)
    {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment .real (B3Pre pr Msg slKeygen γ A) =ᵈ
      (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen γ A.toFxmssAdversary := by
  refine (B3Pre_exp_eq pr Msg slKeygen hP hgc .real γ A).trans ?_
  have hgame : (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen γ A.toFxmssAdversary =
      (do let pk ← $ᵗ pr.PkSeed; let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk (Hyb.viewOf pr γ pk d.ys d.u)) := by
    simp only [gameHyb, map_bind, stageHyb_betaOf_E6Valid_eq]
  rw [hgame]
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.trans (Hyb.evalDistEq_of_eq ?_) (Hyb.setupHyb_resample pr slKeygen
    A.toFxmssAdversary (fun S ys => Hyb.targets pr pk (Hyb.selUD γ) S ys)
    (fun d w => evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk (Hyb.viewOf pr γ pk d.ys w))
    fun _ _ _ _ _ _ _ => rfl)
  refine bind_congr fun d => ?_
  simp only [stageHyb_betaOf_E6Valid_eq]
  by_cases hS : d.S.TreeValid P.hsf
  · have hl : ∀ pt ∈ Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys, ∀ x,
        blockVal pr pk pt.1.1.1 pt.1.2.val (γ + 1)
          (Hyb.relDig pr pk (digOf pr d.ys) pt.1.1.1 pt.1.2.val) (Hyb.udAns pr .real pk pt.2 x) =
        blockVal pr pk pt.1.1.1 pt.1.2.val γ
          (Hyb.relDig pr pk (digOf pr d.ys) pt.1.1.1 pt.1.2.val) x := by
      rintro ⟨p, t⟩ hpt x
      simp only [Hyb.targets, hS, ite_true] at hpt
      obtain ⟨j, hj, rfl⟩ := (Hyb.mem_targetsOf pr).1 hpt
      simp only [Hyb.selUD] at hj; split_ifs at hj with hγ; cases hj
      exact Hyb.blockVal_succ_F pr pk _ _ _ _ x hγ
    have hoff : ∀ q, q ∉ (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys).map Prod.fst →
        blockVal pr pk q.1.1 q.2.val (γ + 1)
          (Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) (d.u q) =
        blockVal pr pk q.1.1 q.2.val γ
          (Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) (d.u q) := by
      intro q hq
      simp only [Hyb.targets, hS, ite_true, Hyb.mem_map_fst_targetsOf, Hyb.selUD] at hq
      refine Hyb.blockVal_succ_of_le pr pk _ _ _ _ _ fun hγ => hq ?_
      rw [Hyb.relDig] at hγ; simp [hγ]
    have hc := Hyb.fillWith_couple (Hyb.udAns pr .real pk) (fun _ x => x)
      (fun q y => blockVal pr pk q.1.1 q.2.val (γ + 1)
        (Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) y)
      (fun q y => blockVal pr pk q.1.1 q.2.val γ
        (Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) y)
      (evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk)
      (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) hl d.u d.u hoff
    convert hc using 1 <;> exact bind_congr fun _ => congrArg _ (funext fun _ => rfl)
  · simp only [Hyb.targets, hS, ite_false, Hyb.fillWith, pure_bind,
      evE6Valid_invalid pr Msg slKeygen _ d hS]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B3Pre_ideal_eq (hP : P.Valid) (hgc : GrindComplete pr) (γ : ℕ)
    {qs qh₁ qh₂ L : ℕ} (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment .ideal (B3Pre pr Msg slKeygen γ A) =ᵈ
      (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen (γ + 1) A.toFxmssAdversary := by
  refine (B3Pre_exp_eq pr Msg slKeygen hP hgc .ideal γ A).trans ?_
  have hgame : (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen (γ + 1) A.toFxmssAdversary =
      (do let pk ← $ᵗ pr.PkSeed; let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk (Hyb.viewOf pr (γ + 1) pk d.ys d.u)) := by
    simp only [gameHyb, map_bind, stageHyb_betaOf_E6Valid_eq]
  rw [hgame]
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.trans (Hyb.evalDistEq_of_eq ?_) (Hyb.setupHyb_resample pr slKeygen
    A.toFxmssAdversary (fun S ys => Hyb.targets pr pk (Hyb.selUD γ) S ys)
    (fun d w => evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk (Hyb.viewOf pr (γ + 1) pk d.ys w))
    fun _ _ _ _ _ _ _ => rfl)
  refine bind_congr fun d => ?_
  simp only [stageHyb_betaOf_E6Valid_eq]
  rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Claim 4.4 (Stage-1-precomputing `B3Pre γ`)**: telescopes `HybEventValid Honest.E6` from
`gameHyb 0` to `gameHyb (P.w - 2)`. -/
theorem claim_4_4_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEventValid pr Msg Honest.E6 o] ≤
      Pr{let o ← gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary}[
        HybEventValid pr Msg Honest.E6 o] +
        ∑ γ ∈ Finset.range (P.w - 2), SM_DT_UD_Advantage (B3Pre pr Msg slKeygen γ A) := by
  have hstep : ∀ γ,
      Pr{let o ← gameHyb pr Msg slKeygen γ A.toFxmssAdversary}[HybEventValid pr Msg Honest.E6 o] ≤
        Pr{let o ← gameHyb pr Msg slKeygen (γ + 1) A.toFxmssAdversary}[
          HybEventValid pr Msg Honest.E6 o] +
        SM_DT_UD_Advantage (B3Pre pr Msg slKeygen γ A) := by
    intro γ
    have hpr : ∀ k, Pr{let o ← gameHyb pr Msg slKeygen k A.toFxmssAdversary}[
        HybEventValid pr Msg Honest.E6 o] =
        𝒟[(fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
          gameHyb pr Msg slKeygen k A.toFxmssAdversary] {true} := fun k => by
      rw [prEvent_eq_evalDist_decide, map_eq_bind_pure_comp]; rfl
    rw [hpr γ, hpr (γ + 1), SM_DT_UD_Advantage, MeasureTheory.Measure.boolDist,
      (B3Pre_real_eq pr Msg slKeygen hP hgc γ A).evalDist_eq,
      (B3Pre_ideal_eq pr Msg slKeygen hP hgc γ A).evalDist_eq]
    exact (ENNReal.absDiff_le_iff.1 le_rfl).1
  exact Hyb.telescope
    (fun γ => Pr{let o ← gameHyb pr Msg slKeygen γ A.toFxmssAdversary}[
      HybEventValid pr Msg Honest.E6 o])
    (fun γ => SM_DT_UD_Advantage (B3Pre pr Msg slKeygen γ A)) hstep (P.w - 2)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B4Pre_exp_eq {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B4Pre pr Msg slKeygen A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q4Pre pr d.S d.u pk
          let out ← (B4Pre pr Msg slKeygen A).forge (d, tbl, Q) pk
          return tcrWin (probTcrF pr (L * P.lsf * P.w)) pk Q out) := by
  unfold SM_DT_TCR_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B4Pre, SM_DT_TCR_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hrec := simulateQ_recordTcr_run (probTcrF pr (L * P.lsf * P.w)) pk
    (OracleComp.liftComp (prog4Pre pr L d.S d.ys d.u) _) [] []
  have hgood := tcrGood_Q4Pre pr L d.S d.ys d.u pk
    (fun hS => anchors_le_of_mem_support_setupHyb pr Msg slKeygen A hd hS)
  rw [tcr_run_eq _ _ _ (by rw [prog4Pre_perm_run]; exact hgood),
    prog4Pre_perm_run, map_pure] at hrec
  simp only [SM_DT_TCR_oracles, unifFwd, TcrOracleSpec] at hrec ⊢
  rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
  refine EvalDistEq.bind_right _ fun out => ?_
  rcases out with ⟨j, m⟩
  simp only [tcrWin]
  split <;> rename_i h <;> simp [h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Claim 4.5 (Stage-1-precomputing `B4Pre`)**. -/
theorem claim_4_5_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEventValid pr Msg Honest.E5 o] ≤
      SM_DT_TCR_Advantage (B4Pre pr Msg slKeygen A) := by
  unfold SM_DT_TCR_Advantage
  rw [(B4Pre_exp_eq pr Msg slKeygen A).evalDist_eq, ← prEvent_eq_evalDist_singleton]
  unfold gameHyb
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono' _ _ _ fun pk _ => prEvent_bind_mono' _ _ _ fun d hd => ?_
  set tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
  set Q := Q4Pre pr d.S d.u pk
  have hst := stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (betaOf pr 0 pk d.u) (fun st : (B4Pre pr Msg slKeygen A).State => st.2.1)
    (fun st => st.1) pk (d, tbl, Q)
    (fun hS => buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u)
    (fun st o => extract4Trace pr Msg st.1.S st.2.1 st.2.2 o)
  rw [show ((B4Pre pr Msg slKeygen A).forge (d, tbl, Q) pk >>= fun a =>
        pure (tcrWin (probTcrF pr (L * P.lsf * P.w)) pk Q a = true)) =
      (fun a => tcrWin (probTcrF pr (L * P.lsf * P.w)) pk Q a = true) <$>
        (B4Pre pr Msg slKeygen A).forge (d, tbl, Q) pk by rw [map_eq_bind_pure_comp]; rfl]
  dsimp only [B4Pre] at hst ⊢
  rw [hst, Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
  have hagree := buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u
  obtain ⟨w, hw, hval, hid, ch, p, hp, hd1, hd2, hne, heq⟩ := hE
  obtain ⟨ft, hft, hdStar, hch, -, -, -, -, -⟩ := fxmssExtractTable_eq_some pr pk tr.idf tr.yf w hval
  have hvisitA : .inl tr.idf ∈ treeOrder P.hsf d.S P.hsf 0 := by
    obtain ⟨v, hv, hvid⟩ := Finset.mem_image.1 hid
    have hle := hS.anchor_depth_le v hv
    rw [← hvid]
    exact visit_mem_treeOrder hS (e := .inl (v.toLeafId P.hsf))
      ⟨by simp [Node.toLeafId], by rwa [Node.ofLeafId_toLeafId hle]⟩
  have hQmem : ∀ (ch' : Fin P.lsf) (p' : ℕ), p' < P.w - 1 →
      ((SfAdrs.chainAdrs tr.idf ch'.val p').toAdrs,
        WotsC.chain pr pk tr.idf ch'.val (skOf pr d.S d.u tr.idf ch'.val) 0 p') ∈ Q := by
    intro ch' p' hp'
    simp only [Q, Q4Pre, hS, ↓reduceIte, List.mem_flatMap]
    refine ⟨.inl tr.idf, hvisitA, ?_⟩
    simp only [entryQ, List.mem_flatMap, List.mem_map]
    exact ⟨ch', List.mem_finRange _, p', List.mem_range.2 hp', rfl⟩
  have hQhon : ∀ e ∈ Q, ∀ id' ch' p', e.1 = (SfAdrs.chainAdrs id' ch' p').toAdrs →
      e.2 = WotsC.chain pr pk id' ch' (skOf pr d.S d.u id' ch') 0 p' := by
    intro e he id' ch' p' he1
    simp only [Q, Q4Pre, hS, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨node, -, he⟩ := he
    rcases node with id₀ | id₀
    · simp only [entryQ, List.mem_flatMap, List.mem_map] at he
      obtain ⟨ch₀, -, p₀, -, rfl⟩ := he
      obtain ⟨rfl, hch_eq, rfl⟩ := SfAdrs.chainAdrs_inj.1 he1
      rw [hch_eq]
    · simp only [entryQ, combineLog] at he; split at he <;> simp at he
  have hcand_check : ∀ (ch' : Fin P.lsf) (p' : ℕ), p' < P.w - 1 →
      WotsC.digit pr (tbl.encoded tr.idf) ch'.val ≤ p' →
      WotsC.digit pr ft.dStar ch'.val ≤ p' →
      ft.chainVal ch' p' ≠ tbl.chainVal tr.idf ch' p' →
      ft.chainVal ch' (p' + 1) = tbl.chainVal tr.idf ch' (p' + 1) →
      pr.F pk (SfAdrs.chainAdrs tr.idf ch'.val p').toAdrs (ft.chainVal ch' p') =
        pr.F pk (SfAdrs.chainAdrs tr.idf ch'.val p').toAdrs
          (WotsC.chain pr pk tr.idf ch'.val (skOf pr d.S d.u tr.idf ch'.val) 0 p') := by
    intro ch' p' hp' h1 h2 _ hcol
    rw [hagree.encoded tr.idf hid] at h1
    have hf1 := hch ch' p' h2 (by omega)
    have hf2 := hch ch' (p' + 1) (by omega) (by omega)
    have hstepF : pr.F pk (SfAdrs.chainAdrs tr.idf ch'.val p').toAdrs (ft.chainVal ch' p') =
        ft.chainVal ch' (p' + 1) := by
      rw [hf1, hf2, show p' + 1 - WotsC.digit pr ft.dStar ch'.val =
        (p' - WotsC.digit pr ft.dStar ch'.val) + 1 by omega, WotsC.chain_succ,
        Nat.add_sub_cancel' h2]
    obtain ⟨c', hg'⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
    have henc' := hon_encoded pr (S := d.S) (β := betaOf pr 0 pk d.u) hg'
    have ht2 := hagree.chainVal tr.idf hid ch' (p' + 1) (by omega) (by omega)
    rw [hon0_chainValue pr hg' ch' (by rw [← henc']; omega)] at ht2
    rw [hstepF, hcol, ht2, WotsC.chain_succ, Nat.zero_add]
  -- Witness `(ch, p)` produces a candidate in `cands` and matches its target in `Q`
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  have henc := hon_encoded pr (S := d.S) (β := betaOf pr 0 pk d.u) hg
  have hcv := hon0_chainValue pr (u := d.u) hg ch (p := p) (by rwa [← henc])
  have hcv1 := hon0_chainValue pr (u := d.u) hg ch (p := p + 1) (by rw [← henc]; omega)
  have hd2' : WotsC.digit pr ft.dStar ch.val ≤ p := by rw [hdStar]; exact hd2
  have hft_p : ft.chainVal ch p = (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).fChain tr.idf tr.yf w ch p := by
    have := hch ch p hd2' (by omega); rwa [hdStar] at this
  have hft_p1 : ft.chainVal ch (p + 1) =
      pr.F pk (SfAdrs.chainAdrs tr.idf ch.val p).toAdrs (ft.chainVal ch p) := by
    have hf1 := hch ch p hd2' (by omega)
    have hf2 := hch ch (p + 1) (by omega) (by omega)
    rw [hf1, hf2, show p + 1 - WotsC.digit pr ft.dStar ch.val =
      (p - WotsC.digit pr ft.dStar ch.val) + 1 by omega, WotsC.chain_succ,
      Nat.add_sub_cancel' hd2']
  have htbl_p : tbl.chainVal tr.idf ch p = (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).chainValue tr.idf ch p :=
    hagree.chainVal tr.idf hid ch p hd1 (by omega)
  have htbl_p1 : tbl.chainVal tr.idf ch (p + 1) =
      pr.F pk (SfAdrs.chainAdrs tr.idf ch.val p).toAdrs (tbl.chainVal tr.idf ch p) := by
    rw [hagree.chainVal tr.idf hid ch (p + 1) (by omega) (by omega), hcv1, htbl_p, hcv,
      WotsC.chain_succ, Nat.zero_add]
  have hid' : tr.idf ∈ leafIds P.hsf d.S := hid
  simp only [hw, hft, extract4Trace, hid', ↓reduceIte]
  set cands := (List.finRange P.lsf).flatMap fun ch' =>
    (List.range (P.w - 1)).filterMap fun p' =>
      if WotsC.digit pr (tbl.encoded tr.idf) ch'.val ≤ p' ∧
         WotsC.digit pr ft.dStar ch'.val ≤ p' ∧
         ft.chainVal ch' p' ≠ tbl.chainVal tr.idf ch' p' ∧
         ft.chainVal ch' (p' + 1) = tbl.chainVal tr.idf ch' (p' + 1) then
        some ((SfAdrs.chainAdrs tr.idf ch'.val p').toAdrs, ft.chainVal ch' p')
      else none
  have hcmem : ((SfAdrs.chainAdrs tr.idf ch.val p).toAdrs, ft.chainVal ch p) ∈ cands := by
    refine List.mem_flatMap.2 ⟨ch, List.mem_finRange _, List.mem_filterMap.2 ⟨p, List.mem_range.2 hp, ?_⟩⟩
    have hcond : WotsC.digit pr (tbl.encoded tr.idf) ch.val ≤ p ∧
        WotsC.digit pr ft.dStar ch.val ≤ p ∧
        ft.chainVal ch p ≠ tbl.chainVal tr.idf ch p ∧
        ft.chainVal ch (p + 1) = tbl.chainVal tr.idf ch (p + 1) :=
      ⟨by rwa [hagree.encoded tr.idf hid], by rwa [hdStar], by rw [hft_p, htbl_p]; exact hne,
        by rw [hft_p1, htbl_p1, hft_p, htbl_p]; exact heq⟩
    simp [hcond]
  have hsome : (cands.findSome? fun c' =>
      (Q.findIdx? fun e => decide (e.1 = c'.1 ∧ c'.2 ≠ e.2)).map fun j => (j, c'.2)).isSome := by
    rw [List.findSome?_isSome_iff]
    refine ⟨((SfAdrs.chainAdrs tr.idf ch.val p).toAdrs, ft.chainVal ch p), hcmem, ?_⟩
    rw [Option.isSome_map, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hQmem ch p hp, by
      simp only [decide_eq_true_eq]
      exact ⟨trivial, by rw [hft_p, ← hcv]; exact hne⟩⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨c', hc', hfind⟩ := List.exists_of_findSome?_eq_some hr
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hfind
  obtain ⟨hjlt, hjp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [decide_eq_true_eq] at hjp
  obtain ⟨ch', -, hc'⟩ := List.mem_flatMap.1 hc'
  obtain ⟨p', hp', hcond'⟩ := List.mem_filterMap.1 hc'
  have hp'_lt : p' < P.w - 1 := List.mem_range.1 hp'
  split_ifs at hcond' with hcc
  cases hcond'
  simp only [hr, Option.getD_some, tcrWin, List.getElem?_eq_getElem hjlt]
  simp only [decide_eq_true_eq]
  refine ⟨hjp.2, ?_⟩
  rw [hQhon Q[j] (List.getElem_mem hjlt) tr.idf ch'.val p' hjp.1, hjp.1]
  exact hcand_check ch' p' hp'_lt hcc.1 hcc.2.1 hcc.2.2.1 hcc.2.2.2

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B5Pre_exp_eq {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_PRE_Experiment (B5Pre pr Msg slKeygen A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let z ← Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u []
          let tbl := if d.S.TreeValid P.hsf then
            buildSfTableHybDet pr pk id (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
          else default
          let jm ← (B5Pre pr Msg slKeygen A).invert ⟨d, tbl, Hyb.targets pr pk Hyb.selPre d.S d.ys⟩ pk
          return Hyb.preWin pr pk z.2 jm) := by
  unfold SM_DT_PRE_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B5Pre, SM_DT_PRE_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hcoll : Hyb.CollAnswers pr (Prod.fst : Adrs × pr.Y → Adrs) pk
      (unifFwd (SM_DT_PRE_State Adrs pr.Y) + (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
        collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk)) := by
    intro q qs tws hq
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
    exact collectionOracle_run_of_fresh Prod.fst q hq
  have hchal : Hyb.ChalAnswers pr (Prod.fst : Adrs × pr.Y → Adrs) (L * P.lsf)
      (fun t x => pr.F pk t x) (fun t x => (t, x))
      (unifFwd (SM_DT_PRE_State Adrs pr.Y) + (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
        collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk)) := by
    intro t qs tws hlen hfr
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    exact SM_DT_PRE_challengeOracle_run_of_fresh hlen hfr
  have hrun := run_pickProgPre pr hcoll hchal (fun _ _ => rfl) Hyb.selPre id
    (fun a _ j hj => by simp only [Hyb.selPre, id_eq] at hj ⊢; split_ifs at hj with h0; cases hj; omega)
    d.ys d.u (Hyb.targets_length_le pr slKeygen A pk Hyb.selPre hd)
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine EvalDistEq.trans
    (my := (simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
        (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
          collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk))
        (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], []) >>= fun z =>
      (B5Pre pr Msg slKeygen A).invert ⟨d, z.1.1, z.1.2⟩ pk >>= fun jm =>
        pure (Hyb.preWin pr pk z.2.1 jm))
    (EvalDistEq.bind_right _ fun z => Hyb.evalDistEq_of_eq (by
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, B5Pre, Hyb.preWin]
      refine bind_congr fun jm => ?_
      cases z.2.1[jm.1]? with
      | none => rfl
      | some tx => obtain ⟨t, x⟩ := tx; rfl)) ?_
  have hre : ((simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
        (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
          collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk))
        (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], []) >>= fun z =>
      (B5Pre pr Msg slKeygen A).invert ⟨d, z.1.1, z.1.2⟩ pk >>= fun jm =>
        pure (Hyb.preWin pr pk z.2.1 jm)) =
      ((fun z => (z.1, z.2.1)) <$> (simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
        (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
          collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk))
        (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], [])) >>= fun z =>
      (B5Pre pr Msg slKeygen A).invert ⟨d, z.1.1, z.1.2⟩ pk >>= fun jm =>
        pure (Hyb.preWin pr pk z.2 jm) := by
    simp [bind_map_left]
  refine (Hyb.evalDistEq_of_eq hre).trans ?_
  refine (hrun.bind_left _).trans ?_
  rw [bind_map_left]; rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Claim 4.6 (Stage-1-precomputing `B5Pre`)**. -/
theorem claim_4_6_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary}[
        HybEventValid pr Msg Honest.E6 o] ≤
      SM_DT_PRE_Advantage (B5Pre pr Msg slKeygen A) := by
  have htop : (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let z ← Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u []
          evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk z.1) := by
    have h1 : (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
          gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary =
        (do let pk ← $ᵗ pr.PkSeed; let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
            evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk
              (Hyb.viewOf pr (P.w - 2) pk d.ys d.u)) := by
      simp only [gameHyb, map_bind, stageHyb_betaOf_E6Valid_eq]
    rw [h1]
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine EvalDistEq.trans (Hyb.setupHyb_resample pr slKeygen A.toFxmssAdversary
      (fun S ys => Hyb.targets pr pk Hyb.selPre S ys)
      (fun d w => evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk
        (Hyb.viewOf pr (P.w - 2) pk d.ys w))
      fun _ _ _ _ _ _ _ => rfl).symm ?_
    refine Hyb.evalDistEq_of_eq (bind_congr fun d => ?_)
    have hrw : (Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
          (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u [] >>=
        fun z => evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk z.1) =
        (Hyb.fillWith (fun t x => pr.F pk t x) (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u >>=
          fun u' => evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk u') := by
      rw [← Hyb.map_fst_runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
        (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u [], bind_map_left]
    rw [hrw]
    by_cases hS : d.S.TreeValid P.hsf
    · have hl : ∀ pt ∈ Hyb.targets pr pk Hyb.selPre d.S d.ys, ∀ x,
          blockVal pr pk pt.1.1.1 pt.1.2.val (P.w - 2)
            (Hyb.relDig pr pk (digOf pr d.ys) pt.1.1.1 pt.1.2.val) x =
          pr.F pk pt.2 x := by
        rintro ⟨p, t⟩ hpt x
        simp only [Hyb.targets, hS, ite_true] at hpt
        obtain ⟨j, hj, rfl⟩ := (Hyb.mem_targetsOf pr).1 hpt
        simp only [Hyb.selPre] at hj; split_ifs at hj with h0; cases hj
        exact Hyb.blockVal_top pk _ _ _ x h0 (Hyb.relDigOf_lt _ _)
      have hoff : ∀ q, q ∉ (Hyb.targets pr pk Hyb.selPre d.S d.ys).map Prod.fst →
          blockVal pr pk q.1.1 q.2.val (P.w - 2)
            (Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) (d.u q) = d.u q := by
        intro q hq
        simp only [Hyb.targets, hS, ite_true, Hyb.mem_map_fst_targetsOf, Hyb.selPre] at hq
        have h0 : Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val = 0 := by
          by_contra h; exact hq (by simp [Hyb.relDig] at h ⊢; omega)
        rw [h0]; exact Hyb.blockVal_zero pk _ _ _ _
      have hc := Hyb.fillWith_couple (fun _ x => x) (fun t x => pr.F pk t x)
        (fun q y => blockVal pr pk q.1.1 q.2.val (P.w - 2)
          (Hyb.relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) y)
        (fun _ y => y) (evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk)
        (Hyb.targets pr pk Hyb.selPre d.S d.ys) hl d.u d.u hoff
      convert hc using 1
      exact bind_congr fun _ => congrArg _ (funext fun _ => rfl)
    · simp only [Hyb.targets, hS, ite_false, Hyb.fillWith, pure_bind,
        evE6Valid_invalid pr Msg slKeygen _ d hS]
  rw [prEvent_eq_evalDist_decide,
    show (gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary >>=
        fun o => pure (decide (HybEventValid pr Msg Honest.E6 o))) =
      (fun o => decide (HybEventValid pr Msg Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary by rw [map_eq_bind_pure_comp]; rfl,
    htop.evalDist_eq, ← prEvent_eq_evalDist_singleton]
  unfold SM_DT_PRE_Advantage
  rw [(B5Pre_exp_eq pr Msg slKeygen A).evalDist_eq, ← prEvent_eq_evalDist_singleton]
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono' _ _ _ fun pk _ => prEvent_bind_mono' _ _ _ fun d hd =>
    prEvent_bind_mono' _ _ _ fun z hz => ?_
  rw [show Pr{let b ← evE6Valid pr Msg slKeygen A.toFxmssAdversary d pk z.1}[b = true] =
      Pr{let o ← stageHyb pr Msg slKeygen A.toFxmssAdversary (fun id ch _ => skOf pr d.S z.1 id ch) d pk}[
        HybEventValid pr Msg Honest.E6 o] by
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_decide]
    simp only [evE6Valid, map_eq_bind_pure_comp]; rfl]
  set tbl := if d.S.TreeValid P.hsf then
    buildSfTableHybDet pr pk id (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
  else default
  set tgs := Hyb.targets pr pk Hyb.selPre d.S d.ys
  have hagree : d.S.TreeValid P.hsf →
      SfTableAgree pr (hon pr d.S pk (digOf pr d.ys) (fun id ch _ => skOf pr d.S z.1 id ch)) tbl :=
    fun hS => by
      simp only [tbl, hS, ↓reduceIte]
      exact buildSfTableHybDet_agree pr hP hgc hS pk d.ys z.1 id
        (fun id ch _ => skOf pr d.S z.1 id ch) (fun _ _ => le_rfl)
        (fun _ _ _ => by simp [WotsC.chain])
  let st5 : (B5Pre pr Msg slKeygen A).State := ⟨d, tbl, tgs⟩
  have hst := stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (fun id ch _ => skOf pr d.S z.1 id ch) (fun st : (B5Pre pr Msg slKeygen A).State => st.2.1)
    (fun st => st.1) pk st5 hagree
    (fun st o => extract5Trace pr Msg st.2.1 st.2.2 o)
  rw [show ((B5Pre pr Msg slKeygen A).invert st5 pk >>= fun jm =>
        pure (Hyb.preWin pr pk z.2 jm = true)) =
      (fun jm => Hyb.preWin pr pk z.2 jm = true) <$>
        (B5Pre pr Msg slKeygen A).invert st5 pk by rw [map_eq_bind_pure_comp]; rfl]
  dsimp only [B5Pre] at hst ⊢
  rw [hst, Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
  have hag := hagree hS
  obtain ⟨w, hw, hval, hid, ch, hlt, hF⟩ := hE
  obtain ⟨ft, hft, hdStar, hch, -, -, -, -, -⟩ := fxmssExtractTable_eq_some pr pk tr.idf tr.yf w hval
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  have hcheck : ∀ ch' : Fin P.lsf,
      (WotsC.digit pr ft.dStar ch'.val < WotsC.digit pr (tbl.encoded tr.idf) ch'.val ∧
        ft.chainVal ch' (WotsC.digit pr (tbl.encoded tr.idf) ch'.val) = tbl.block tr.idf ch') ↔
      Hyb.e6At (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch)
        tr.idf tr.yf w ch' := by
    intro ch'
    rw [hag.encoded tr.idf hid, hag.block tr.idf hid ch']
    have hd' : ft.dStar = (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch).fEnc
        tr.idf tr.yf w := hdStar
    unfold Hyb.e6At
    rw [hd']
    refine and_congr_right fun hlt' => ?_
    have ha_lt : WotsC.digit pr ((hon pr d.S pk (digOf pr d.ys) fun id ch _ =>
        skOf pr d.S z.1 id ch).encoded tr.idf) ch'.val < P.w := WotsC.digit_lt pr _ _
    set a' := WotsC.digit pr ((hon pr d.S pk (digOf pr d.ys) fun id ch _ =>
      skOf pr d.S z.1 id ch).encoded tr.idf) ch'.val
    set b' := WotsC.digit pr ((hon pr d.S pk (digOf pr d.ys) fun id ch _ =>
      skOf pr d.S z.1 id ch).fEnc tr.idf tr.yf w) ch'.val
    have hval' := hch ch' a' (by rw [hd']; exact Nat.le_of_lt hlt') ha_lt
    rw [hd'] at hval'
    have hstep := WotsC.chain_succ pr pk tr.idf ch'.val w.wots.chains[ch'.val] b' (a' - 1 - b')
    rw [show b' + (a' - 1 - b') = a' - 1 by omega,
      show a' - 1 - b' + 1 = a' - b' by omega] at hstep
    rw [hval', hstep]
    rfl
  have hfind : ∃ ch', (List.finRange P.lsf).find? (fun ch' =>
      decide (WotsC.digit pr ft.dStar ch'.val < WotsC.digit pr (tbl.encoded tr.idf) ch'.val ∧
        ft.chainVal ch' (WotsC.digit pr (tbl.encoded tr.idf) ch'.val) = tbl.block tr.idf ch')) =
      some ch' := by
    refine Option.isSome_iff_exists.1 ?_
    rw [List.find?_isSome]
    exact ⟨ch, List.mem_finRange _, decide_eq_true ((hcheck ch).2 ⟨hlt, hF⟩)⟩
  obtain ⟨ch', hch'⟩ := hfind
  have hch'_true := List.find?_some hch'
  have he' : Hyb.e6At (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch)
      tr.idf tr.yf w ch' := (hcheck ch').1 (of_decide_eq_true hch'_true)
  have henc := Hyb.hon_encoded_of_grind (S := d.S) (β := fun id ch _ => skOf pr d.S z.1 id ch) hg
  have hblk := Hyb.hon_block_of_grind (S := d.S) (β := fun id ch _ => skOf pr d.S z.1 id ch) hg ch'
  set a := WotsC.digit pr (WotsC.encode pr pk tr.idf (digOf pr d.ys tr.idf) c) ch'.val
  have henc_tbl : tbl.encoded tr.idf = WotsC.encode pr pk tr.idf (digOf pr d.ys tr.idf) c := by
    rw [hag.encoded tr.idf hid, henc]
  obtain ⟨hlt', hF'⟩ := he'
  rw [henc] at hlt' hF'
  rw [hblk, Hyb.skOf_anchor pr z.1 hid] at hF'
  have ha0 : 0 < a := by omega
  have hmem : ((⟨tr.idf, hid⟩, ch'), (SfAdrs.chainAdrs tr.idf ch'.val (a - 1)).toAdrs) ∈ tgs := by
    simp only [tgs, Hyb.targets, hS, ite_true]
    refine (Hyb.mem_targetsOf pr).2 ⟨a - 1, ?_, rfl⟩
    have hr : Hyb.relDigOf pr (WotsC.grind pr pk tr.idf (digOf pr d.ys tr.idf)) ch'.val = a := by
      rw [hg]; rfl
    simp [hr, Hyb.selPre, ha0]
  have hnd : (tgs.map Prod.fst).Nodup := by
    simp only [tgs, Hyb.targets, hS, ite_true]
    exact Hyb.nodup_map_fst_targetsOf pr _ _
  obtain ⟨-, -, h3⟩ := Hyb.runRef_spec _ _ _ _ _ z hz hnd
  have hjlt := List.idxOf_lt_length_of_mem hmem
  obtain ⟨x, hx1, hx2⟩ := h3 _ hjlt
  rw [List.getElem_idxOf hjlt] at hx1 hx2
  simp only [List.length_nil, Nat.zero_add] at hx2
  have hft_pre : ft.chainVal ch' (a - 1) =
      (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch).fChain tr.idf tr.yf w ch' (a - 1) := by
    have ha_lt : a < P.w := WotsC.digit_lt pr _ _
    have := hch ch' (a - 1) (by rw [hdStar]; exact Nat.le_sub_one_of_lt hlt') (by omega)
    rwa [hdStar] at this
  have hid' : tr.idf ∈ leafIds P.hsf d.S := hid
  dsimp only [st5]
  simp only [hw, hft, extract5Trace, hid', ↓reduceDIte, hch']
  simp only [henc_tbl, Hyb.preWin]
  dsimp only [a] at hx1 hx2
  rw [hx2]
  simp only [decide_eq_true_eq]
  have hHpk : (hon pr d.S pk (digOf pr d.ys) fun id ch _ => skOf pr d.S z.1 id ch).pk = pk := rfl
  rw [hHpk] at hF'
  rw [hft_pre, ← hx1]
  exact hF'

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B6Pre_exp_eq {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B6Pre pr Msg slKeygen A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q6Pre pr d.S d.u pk
          let out ← (B6Pre pr Msg slKeygen A).forge (d, tbl, Q) pk
          return tcrWin (probTcrLsf pr L) pk Q out) := by
  unfold SM_DT_TCR_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B6Pre, SM_DT_TCR_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hrec := simulateQ_recordTcr_run (probTcrLsf pr L) pk
    (OracleComp.liftComp (prog6Pre pr L d.S d.ys d.u) _) [] []
  have hgood := tcrGood_Q6Pre pr L d.S d.ys d.u pk
    (fun hS => anchors_le_of_mem_support_setupHyb pr Msg slKeygen A hd hS)
  rw [tcr_run_eq _ _ _ (by rw [prog6Pre_perm_run]; exact hgood),
    prog6Pre_perm_run, map_pure] at hrec
  simp only [SM_DT_TCR_oracles, unifFwd, TcrOracleSpec] at hrec ⊢
  rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
  refine EvalDistEq.bind_right _ fun out => ?_
  rcases out with ⟨j, m⟩
  simp only [tcrWin]
  split <;> rename_i h <;> simp [h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Claim 4.7 (Stage-1-precomputing `B6Pre`)**. -/
theorem claim_4_7_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEventValid pr Msg Honest.E7 o] ≤
      SM_DT_TCR_Advantage (B6Pre pr Msg slKeygen A) := by
  unfold SM_DT_TCR_Advantage
  rw [(B6Pre_exp_eq pr Msg slKeygen A).evalDist_eq, ← prEvent_eq_evalDist_singleton]
  unfold gameHyb
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono' _ _ _ fun pk _ => prEvent_bind_mono' _ _ _ fun d hd => ?_
  set tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
  set Q := Q6Pre pr d.S d.u pk
  have hst := stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (betaOf pr 0 pk d.u) (fun st : (B6Pre pr Msg slKeygen A).State => st.2.1)
    (fun st => st.1) pk (d, tbl, Q)
    (fun hS => buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u)
    (fun st o => extract6Trace pr Msg st.1.S st.2.1 st.2.2 o)
  rw [show ((B6Pre pr Msg slKeygen A).forge (d, tbl, Q) pk >>= fun a =>
        pure (tcrWin (probTcrLsf pr L) pk Q a = true)) =
      (fun a => tcrWin (probTcrLsf pr L) pk Q a = true) <$>
        (B6Pre pr Msg slKeygen A).forge (d, tbl, Q) pk by rw [map_eq_bind_pure_comp]; rfl]
  dsimp only [B6Pre] at hst ⊢
  rw [hst, Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
  have hag := buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u
  obtain ⟨w, hw, hval, hid, hne, heq⟩ := hE
  obtain ⟨ft, hft, hdStar, -, htops, hN0, -, -, -⟩ :=
    fxmssExtractTable_eq_some pr pk tr.idf tr.yf w hval
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  have ht0 := hon0_tops pr (u := d.u) hg
  have hvisitA : .inl tr.idf ∈ treeOrder P.hsf d.S P.hsf 0 := by
    obtain ⟨v, hv, hvid⟩ := Finset.mem_image.1 hid
    have hle := hS.anchor_depth_le v hv
    rw [← hvid]
    exact visit_mem_treeOrder hS (e := .inl (v.toLeafId P.hsf))
      ⟨by simp [Node.toLeafId], by rwa [Node.ofLeafId_toLeafId hle]⟩
  have hQmem : ((SfAdrs.pkAdrs tr.idf).toAdrs, WotsC.pkTops pr pk tr.idf (skOf pr d.S d.u tr.idf)) ∈ Q := by
    simp only [Q, Q6Pre, hS, ↓reduceIte, List.mem_flatMap]
    exact ⟨.inl tr.idf, hvisitA, by simp [entryQ]⟩
  have hQhon : ∀ e ∈ Q, e.1 = (SfAdrs.pkAdrs tr.idf).toAdrs →
      e.2 = WotsC.pkTops pr pk tr.idf (skOf pr d.S d.u tr.idf) := by
    intro e he he1
    simp only [Q, Q6Pre, hS, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨node, -, he⟩ := he
    rcases node with id₀ | id₀
    · simp only [entryQ, List.mem_singleton] at he
      rw [he] at he1 ⊢
      rw [SfAdrs.pkAdrs_inj.1 he1]
    · simp only [entryQ, combineLog] at he; split at he <;> simp at he
  have hft_tops : ft.fTops = (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).fTops tr.idf tr.yf w := by
    rw [htops, hdStar]; rfl
  have hHpk : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).pk = pk := rfl
  have hft_N0 : ft.fN0 = tbl.leafVal tr.idf := by
    rw [hHpk] at heq
    rw [hN0, hft_tops, heq, hag.leafVal tr.idf hid, Claim42.hon_leafVal, Scheme.Fxmss.leaf,
      WotsC.pkGen, ← ht0]
  have hid' : tr.idf ∈ leafIds P.hsf d.S := hid
  have hcond : tr.idf ∈ leafIds P.hsf d.S ∧ ft.fTops ≠ tbl.tops tr.idf ∧ ft.fN0 = tbl.leafVal tr.idf :=
    ⟨hid', by rw [hft_tops, hag.tops tr.idf hid]; exact hne, hft_N0⟩
  have hsome : (Q.findIdx? fun e => decide (e.1 = (SfAdrs.pkAdrs tr.idf).toAdrs ∧ ft.fTops ≠ e.2)).isSome := by
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hQmem, by simp only [decide_eq_true_eq]; exact ⟨trivial, by rw [hft_tops, ← ht0]; exact hne⟩⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hjlt, hjp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [decide_eq_true_eq] at hjp
  simp only [hw, hft, extract6Trace, eq_true hcond, ite_true, hj, tcrWin,
    List.getElem?_eq_getElem hjlt]
  simp only [decide_eq_true_eq]
  refine ⟨hjp.2, ?_⟩
  rw [hQhon Q[j] (List.getElem_mem hjlt) hjp.1, hjp.1]
  show pr.ThLsf pk (SfAdrs.pkAdrs tr.idf).toAdrs ft.fTops =
    pr.ThLsf pk (SfAdrs.pkAdrs tr.idf).toAdrs (WotsC.pkTops pr pk tr.idf (skOf pr d.S d.u tr.idf))
  rw [hft_tops, ← ht0]
  exact heq

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B7Pre_exp_eq {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B7Pre pr Msg slKeygen A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q7 pr Msg d pk
          let out ← (B7Pre pr Msg slKeygen A).forge (d, tbl, Q) pk
          return tcrWin (probTcrH pr (L - 1)) pk Q out) := by
  unfold SM_DT_TCR_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B7Pre, SM_DT_TCR_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hrec := simulateQ_recordTcr_run (probTcrH pr (L - 1)) pk
    (OracleComp.liftComp (prog7Pre pr d.S d.ys d.u) _) [] []
  have hgood7 := tcrGood7 pr Msg slKeygen A hd pk
  have hgood : TcrGood (L - 1) (Q7 pr Msg d pk, C7Pre pr d.S d.ys pk) := by
    refine ⟨hgood7.1, hgood7.2.1, fun t ht hq => ?_⟩
    unfold C7Pre at ht
    split_ifs at ht with hS
    · rcases List.mem_append.1 ht with h1 | h2
      · obtain ⟨id, -, h⟩ := List.mem_flatMap.1 h1
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
        obtain ⟨id', -, he1⟩ := mem_Q7 pr he
        rw [he1] at h
        exact SfAdrs.treeAdrs_ne_grindAdrs id' id (mem_grindSearchLog pr pk id _ _ _ h)
      · exact hgood7.2.2 t (by simp [C7, hS, h2]) hq
    · simp at ht
  rw [tcr_run_eq _ _ _ (by rw [prog7Pre_perm_run]; exact hgood),
    prog7Pre_perm_run, map_pure] at hrec
  simp only [SM_DT_TCR_oracles, unifFwd, TcrOracleSpec] at hrec ⊢
  rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
  refine EvalDistEq.bind_right _ fun out => ?_
  rcases out with ⟨j, m⟩
  simp only [tcrWin]
  split <;> rename_i h <;> simp [h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Claim 4.8 (Stage-1-precomputing `B7Pre`)**. -/
theorem claim_4_8_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEventValid pr Msg Honest.E8 o] ≤
      SM_DT_TCR_Advantage (B7Pre pr Msg slKeygen A) := by
  unfold SM_DT_TCR_Advantage
  rw [(B7Pre_exp_eq pr Msg slKeygen A).evalDist_eq, ← prEvent_eq_evalDist_singleton]
  unfold gameHyb
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono' _ _ _ fun pk _ => prEvent_bind_mono' _ _ _ fun d hd => ?_
  set tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
  set Q := Q7 pr Msg d pk
  have hst := stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (betaOf pr 0 pk d.u) (fun st : (B7Pre pr Msg slKeygen A).State => st.2.1)
    (fun st => st.1) pk (d, tbl, Q)
    (fun hS => buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u)
    (fun st o => extract7Trace pr Msg st.2.1 st.2.2 o)
  rw [show ((B7Pre pr Msg slKeygen A).forge (d, tbl, Q) pk >>= fun a =>
        pure (tcrWin (probTcrH pr (L - 1)) pk Q a = true)) =
      (fun a => tcrWin (probTcrH pr (L - 1)) pk Q a = true) <$>
        (B7Pre pr Msg slKeygen A).forge (d, tbl, Q) pk by rw [map_eq_bind_pure_comp]; rfl]
  dsimp only [B7Pre] at hst ⊢
  rw [hst, Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
  have hag := buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u
  obtain ⟨w, hw, hval, k, hk, htw, l, r, hl, hr, hne, heq⟩ := hE
  obtain ⟨ft, hft, hdStar, -, htops, hN0, hfVal, hfPair, -⟩ :=
    fxmssExtractTable_eq_some pr pk tr.idf tr.yf w hval
  have hHleaf := Claim42.hon_leafVal d.S pk (digOf pr d.ys) d.u
  have hQhon : ∀ e ∈ Q, ∀ pos : LeafId, e.1 = (SfAdrs.treeAdrs pos).toAdrs →
      tbl.nodeVal pos.height pos.index = some (pr.H pk (SfAdrs.treeAdrs pos).toAdrs e.2.1 e.2.2) := by
    intro e he pos he1
    simp only [Q, Q7, hS, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨node, hnode, he⟩ := he
    rcases node with id₀ | id₀
    · simp [entryQ] at he
    · obtain ⟨hvis, -, -⟩ := mem_treeOrder P.hsf 0 (.inr id₀) hnode
      simp only [entryQ, combineLog] at he
      split at he
      · rename_i a b ha hb
        simp only [List.mem_singleton] at he
        rw [he] at he1 ⊢
        obtain rfl := SfAdrs.treeAdrs_inj.1 he1
        have hmem : (⟨P.hsf - id₀.height, id₀.index⟩ : Node) ∈ d.S.nodes :=
          Structure.internal_subset_nodes hvis.2.2
        rw [hag.nodeVal id₀.height id₀.index hvis.2.1 hmem, Honest.value, hHleaf]
        have hA : (⟨P.hsf - id₀.height, id₀.index⟩ : Node) ∉ d.S.anchors :=
          hS.not_mem_anchors_of_mem_internal hvis.2.2
        rcases Nat.exists_eq_succ_of_ne_zero (n := id₀.height) (by
          have := hS.internal_depth_lt hvis.2.2; dsimp [Node.ofLeafId] at this; omega) with ⟨z, hz⟩
        rw [Nat.succ_eq_add_one] at hz
        have h1 : Tree.treeNode P.hsf d.S (Scheme.Fxmss.leaf pr pk (skOf pr d.S d.u))
            (Scheme.Fxmss.node pr pk) (z + 1) id₀.index =
            Option.map₂ (Scheme.Fxmss.node pr pk ⟨z + 1, id₀.index⟩)
              (Tree.treeNode P.hsf d.S (Scheme.Fxmss.leaf pr pk (skOf pr d.S d.u))
                (Scheme.Fxmss.node pr pk) z (2 * id₀.index))
              (Tree.treeNode P.hsf d.S (Scheme.Fxmss.leaf pr pk (skOf pr d.S d.u))
                (Scheme.Fxmss.node pr pk) z (2 * id₀.index + 1)) :=
          Tree.treeNode_internal (hz ▸ hvis.2.1) (hz ▸ hvis.2.2) (hz ▸ hA)
        rw [hz] at ha hb ⊢
        simp only [Nat.add_sub_cancel] at ha hb
        have hHS0 : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).S = d.S := rfl
        have hHpk0 : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).pk = pk := rfl
        rw [hHS0, hHpk0, h1, ha, hb, ← hz]; rfl
      · simp at he
  have hfVal_step : ∀ k' < w.auth.length,
      ft.fVal (k' + 1) = pr.H pk (SfAdrs.treeAdrs (Honest.fPos tr.idf (k' + 1))).toAdrs
        (ft.fPair k').1 (ft.fPair k').2 := by
    intro k' hk'
    rw [hfVal (k' + 1) (by omega), hfPair k' hk', hfVal k' (by omega),
      show w.auth.take (k' + 1) = w.auth.take k' ++ [w.auth.getD k' default] by
        have hlen : k' < w.auth.length := hk'
        clear * - hlen
        generalize w.auth = l at hlen ⊢
        induction l generalizing k' with
        | nil => simp at hlen
        | cons a l ih =>
          cases k' with
          | zero => simp
          | succ k' =>
            simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
            exact congrArg (a :: ·) (ih k' (Nat.lt_of_succ_lt_succ hlen))]
    have hclimb : ∀ (z i : ℕ) (acc : pr.Y) (l : List pr.Y) (s : pr.Y),
        Tree.climb (Scheme.Fxmss.node pr pk) z i acc (l ++ [s]) =
          let v := Tree.climb (Scheme.Fxmss.node pr pk) z i acc l
          let z' := z + l.length
          let i' := i / 2 ^ l.length
          if i' % 2 = 0 then Scheme.Fxmss.node pr pk ⟨z' + 1, i' / 2⟩ v s
          else Scheme.Fxmss.node pr pk ⟨z' + 1, i' / 2⟩ s v := by
      intro z i acc l s
      induction l generalizing z i acc with
      | nil => simp [Tree.climb]
      | cons a l ih =>
        simp only [List.cons_append, Tree.climb_cons, List.length_cons]
        rw [ih (z + 1) (i / 2)]
        have h1 : z + 1 + l.length = z + (l.length + 1) := by omega
        have h2 : i / 2 / 2 ^ l.length = i / 2 ^ (l.length + 1) := by
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
        simp only [h1, h2]
    rw [hclimb]
    have hlen : (w.auth.take k').length = k' := List.length_take_of_le (by omega)
    have hdiv : tr.idf.index / 2 ^ k' / 2 = tr.idf.index / 2 ^ (k' + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    simp only [hlen, hdiv, Honest.fPos]
    split_ifs <;> rfl
  have hHpk : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).pk = pk := rfl
  have hHS : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).S = d.S := rfl
  have hQmem : ((SfAdrs.treeAdrs (Honest.fPos tr.idf (k + 1))).toAdrs, (l, r)) ∈ Q :=
    mem_Q7_of_treeTweaks pr hS pk htw
      (by simpa [Honest.fPos, Honest.value, hHleaf, hHS, hHpk, Scheme.Fxmss.treeNode] using hl)
      (by simpa [Honest.fPos, Honest.value, hHleaf, hHS, hHpk, Scheme.Fxmss.treeNode] using hr)
  have hft_pair_k : ft.fPair k = (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).fPair tr.idf tr.yf w k := by
    rw [hfPair k hk, hfVal k (by omega), hN0, htops, hdStar]; rfl
  have hcol_k : some (ft.fVal (k + 1)) =
      tbl.nodeVal (Honest.fPos tr.idf (k + 1)).height (Honest.fPos tr.idf (k + 1)).index := by
    rw [hHpk] at heq
    rw [hfVal_step k hk, hft_pair_k, hQhon _ hQmem _ rfl, heq]
  have hsome : ((List.range w.auth.length).findSome? fun k' =>
      let pos := Honest.fPos tr.idf (k' + 1)
      if some (ft.fVal (k' + 1)) = tbl.nodeVal pos.height pos.index then
        (Q.findIdx? fun e =>
          decide (e.1 = (SfAdrs.treeAdrs pos).toAdrs ∧ ft.fPair k' ≠ e.2)).map
          fun j => (j, ft.fPair k')
      else none).isSome := by
    rw [List.findSome?_isSome_iff]
    refine ⟨k, List.mem_range.2 hk, ?_⟩
    simp only [hcol_k, ↓reduceIte, Option.isSome_map, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, hQmem, by simp only [decide_eq_true_eq]; exact ⟨trivial, by rw [hft_pair_k]; exact hne⟩⟩
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨k', hk', hfk'⟩ := List.exists_of_findSome?_eq_some hres
  have hk'_lt : k' < w.auth.length := List.mem_range.1 hk'
  simp only at hfk'
  split_ifs at hfk' with hcol'
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hfk'
  obtain ⟨hjlt, hjp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [decide_eq_true_eq] at hjp
  simp only [hw, hft, extract7Trace, hres, Option.getD_some, tcrWin, List.getElem?_eq_getElem hjlt]
  simp only [decide_eq_true_eq]
  refine ⟨hjp.2, ?_⟩
  have hqval := hQhon Q[j] (List.getElem_mem hjlt) (Honest.fPos tr.idf (k' + 1)) hjp.1
  rw [hqval] at hcol'
  rw [hjp.1]
  show pr.H pk (SfAdrs.treeAdrs (Honest.fPos tr.idf (k' + 1))).toAdrs (ft.fPair k').1 (ft.fPair k').2 =
    pr.H pk (SfAdrs.treeAdrs (Honest.fPos tr.idf (k' + 1))).toAdrs Q[j].2.1 Q[j].2.2
  rw [← hfVal_step k' hk'_lt]
  exact Option.some.inj hcol'

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B8Pre_exp_eq {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Notions.SMTCRExcl_Experiment (B8Pre pr Msg slKeygen A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q9 pr Msg d pk
          let out ← (B8Pre pr Msg slKeygen A).forge (d, tbl, Q) pk
          return Notions.SMTCRExcl_IsCollision (probExcl pr (L + (L - 1))) pk Q out) := by
  unfold Notions.SMTCRExcl_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [B8Pre, Notions.SMTCRExcl_oracles]
  rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  have hrec := simulateQ_recordExcl_run (probExcl pr (L + (L - 1))) pk
    (OracleComp.liftComp (prog8Pre pr d.S d.ys d.u) _) [] []
  have hgood9 := exclGood9 pr Msg slKeygen A hd pk
  have hgood : ExclGood shrincsX (L + (L - 1)) (Q9 pr Msg d pk, C8Pre pr d.S d.ys pk) := by
    refine ⟨hgood9.1, hgood9.2.1, fun t ht e he hmem => ?_⟩
    unfold C8Pre at ht
    split_ifs at ht with hS
    · rcases List.mem_append.1 ht with h1 | h2
      · obtain ⟨id, -, h⟩ := List.mem_flatMap.1 h1
        have htg := mem_grindSearchLog pr pk id _ _ _ h
        subst htg
        rcases mem_Q9 pr he with ⟨id', -, he1⟩ | ⟨id', -, he1⟩
        · rcases hmem with hmem | hmem
          · rw [he1] at hmem; exact SfAdrs.pkAdrs_ne_grindAdrs id' id hmem.symm
          · rw [he1, shrincsX_partner_pkAdrs] at hmem
            exact SfAdrs.treeAdrs_ne_grindAdrs id' id hmem.symm
        · rcases hmem with hmem | hmem
          · rw [he1] at hmem; exact SfAdrs.treeAdrs_ne_grindAdrs id' id hmem.symm
          · rw [he1, shrincsX_partner_treeAdrs] at hmem
            exact SfAdrs.pkAdrs_ne_grindAdrs id' id hmem.symm
      · exact hgood9.2.2 t (by simp [C9, hS, h2]) e he hmem
    · simp at ht
  rw [excl_run_eq _ _ _ (by rw [prog8Pre_perm_run]; exact hgood),
    prog8Pre_perm_run, map_pure] at hrec
  simp only [Notions.SMTCRExcl_oracles, unifFwd, ExclOracleSpec, probExcl] at hrec ⊢
  rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Claim 4.9 (Stage-1-precomputing `B8Pre`)**. -/
theorem claim_4_9_pre (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEventValid pr Msg Honest.E9 o] ≤
      Notions.SMTCRExcl_Succ (B8Pre pr Msg slKeygen A) := by
  unfold Notions.SMTCRExcl_Succ
  rw [(B8Pre_exp_eq pr Msg slKeygen A).evalDist_eq, ← prEvent_eq_evalDist_singleton]
  unfold gameHyb
  simp only [map_bind, map_pure]
  refine prEvent_bind_mono' _ _ _ fun pk _ => prEvent_bind_mono' _ _ _ fun d hd => ?_
  set tbl := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
  set Q := Q9 pr Msg d pk
  have hst := stage2RunWithTrace_eq_map_stageHyb pr Msg slKeygen A.toFxmssAdversary
    (betaOf pr 0 pk d.u) (fun st : (B8Pre pr Msg slKeygen A).State => st.2.1)
    (fun st => st.1) pk (d, tbl, Q)
    (fun hS => buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u)
    (fun st o => extract8Trace pr Msg st.2.1 st.2.2 o)
  rw [show ((B8Pre pr Msg slKeygen A).forge (d, tbl, Q) pk >>= fun a =>
        pure (Notions.SMTCRExcl_IsCollision (probExcl pr (L + (L - 1))) pk Q a = true)) =
      (fun a => Notions.SMTCRExcl_IsCollision (probExcl pr (L + (L - 1))) pk Q a = true) <$>
        (B8Pre pr Msg slKeygen A).forge (d, tbl, Q) pk by rw [map_eq_bind_pure_comp]; rfl]
  dsimp only [B8Pre] at hst ⊢
  rw [hst, Functor.map_map]
  refine prEvent_mono_of_support _ _ _ fun o ho hE => ?_
  rcases o with _ | ⟨tr, H⟩
  · exact hE.elim
  obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr Msg slKeygen A.toFxmssAdversary _ d pk ho
  have hag := buildSfTable0Det_agree pr hP hgc hS pk (digOf pr d.ys) d.u
  obtain ⟨w, hw, hval, hE9⟩ := hE
  obtain ⟨ft, hft, hdStar, -, htops, hN0, hfVal, hfPair, -⟩ :=
    fxmssExtractTable_eq_some pr pk tr.idf tr.yf w hval
  have hHleaf := Claim42.hon_leafVal d.S pk (digOf pr d.ys) d.u
  have hQpk : ∀ e ∈ Q, ∀ pos : LeafId, e.1 = (SfAdrs.pkAdrs pos).toAdrs →
      e.2 = .inr (WotsC.pkTops pr pk pos (skOf pr d.S d.u pos)) ∧
      tbl.leafVal pos = pr.ThLsf pk (SfAdrs.pkAdrs pos).toAdrs (WotsC.pkTops pr pk pos (skOf pr d.S d.u pos)) := by
    intro e he pos he1
    simp only [Q, Q9, hS, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨node, hnode, he⟩ := he
    rcases node with id₀ | id₀
    · simp only [entryQ, List.mem_singleton] at he
      rw [he] at he1 ⊢
      obtain rfl := SfAdrs.pkAdrs_inj.1 he1
      obtain ⟨hvis, -, -⟩ := mem_treeOrder P.hsf 0 (.inl id₀) hnode
      have hid₀ : id₀ ∈ leafIds P.hsf d.S :=
        Finset.mem_image.2 ⟨Node.ofLeafId P.hsf id₀, hvis.2, Node.toLeafId_ofLeafId hvis.1⟩
      exact ⟨rfl, by rw [hag.leafVal id₀ hid₀, hHleaf]; rfl⟩
    · simp only [entryQ, combineLog] at he
      split at he
      · simp only [List.mem_singleton] at he
        rw [he] at he1
        exact absurd he1.symm (SfAdrs.pkAdrs_ne_treeAdrs pos id₀)
      · simp at he
  have hQtr : ∀ e ∈ Q, ∀ pos : LeafId, e.1 = (SfAdrs.treeAdrs pos).toAdrs →
      ∃ l r, e.2 = .inl (l, r) ∧
        tbl.nodeVal pos.height pos.index = some (pr.H pk (SfAdrs.treeAdrs pos).toAdrs l r) := by
    intro e he pos he1
    simp only [Q, Q9, hS, ↓reduceIte, List.mem_flatMap] at he
    obtain ⟨node, hnode, he⟩ := he
    rcases node with id₀ | id₀
    · simp only [entryQ, List.mem_singleton] at he
      rw [he] at he1
      exact absurd he1 (SfAdrs.pkAdrs_ne_treeAdrs id₀ pos)
    · obtain ⟨hvis, -, -⟩ := mem_treeOrder P.hsf 0 (.inr id₀) hnode
      simp only [entryQ, combineLog] at he
      split at he
      · rename_i a b ha hb
        simp only [List.mem_singleton] at he
        rw [he] at he1 ⊢
        obtain rfl := SfAdrs.treeAdrs_inj.1 he1
        refine ⟨a, b, rfl, ?_⟩
        have hmem : (⟨P.hsf - id₀.height, id₀.index⟩ : Node) ∈ d.S.nodes :=
          Structure.internal_subset_nodes hvis.2.2
        rw [hag.nodeVal id₀.height id₀.index hvis.2.1 hmem, Honest.value, hHleaf]
        have hA : (⟨P.hsf - id₀.height, id₀.index⟩ : Node) ∉ d.S.anchors :=
          hS.not_mem_anchors_of_mem_internal hvis.2.2
        rcases Nat.exists_eq_succ_of_ne_zero (n := id₀.height) (by
          have := hS.internal_depth_lt hvis.2.2; dsimp [Node.ofLeafId] at this; omega) with ⟨z, hz⟩
        rw [Nat.succ_eq_add_one] at hz
        have h1 := Tree.treeNode_internal (hsf := P.hsf) (S := d.S)
          (leaf := Scheme.Fxmss.leaf pr pk (skOf pr d.S d.u)) (node := Scheme.Fxmss.node pr pk)
          (hz ▸ hvis.2.1) (hz ▸ hvis.2.2) (hz ▸ hA)
        rw [hz] at ha hb ⊢
        simp only [Nat.add_sub_cancel] at ha hb
        have hHS0 : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).S = d.S := rfl
        have hHpk0 : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).pk = pk := rfl
        rw [hHS0, hHpk0, h1, ha, hb, ← hz]; rfl
      · simp at he
  have hfVal_step : ∀ k' < w.auth.length,
      ft.fVal (k' + 1) = pr.H pk (SfAdrs.treeAdrs (Honest.fPos tr.idf (k' + 1))).toAdrs
        (ft.fPair k').1 (ft.fPair k').2 := by
    intro k' hk'
    rw [hfVal (k' + 1) (by omega), hfPair k' hk', hfVal k' (by omega),
      show w.auth.take (k' + 1) = w.auth.take k' ++ [w.auth.getD k' default] by
        have hlen : k' < w.auth.length := hk'
        clear * - hlen
        generalize w.auth = l at hlen ⊢
        induction l generalizing k' with
        | nil => simp at hlen
        | cons a l ih =>
          cases k' with
          | zero => simp
          | succ k' =>
            simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
            exact congrArg (a :: ·) (ih k' (Nat.lt_of_succ_lt_succ hlen))]
    have hclimb : ∀ (z i : ℕ) (acc : pr.Y) (l : List pr.Y) (s : pr.Y),
        Tree.climb (Scheme.Fxmss.node pr pk) z i acc (l ++ [s]) =
          let v := Tree.climb (Scheme.Fxmss.node pr pk) z i acc l
          let z' := z + l.length
          let i' := i / 2 ^ l.length
          if i' % 2 = 0 then Scheme.Fxmss.node pr pk ⟨z' + 1, i' / 2⟩ v s
          else Scheme.Fxmss.node pr pk ⟨z' + 1, i' / 2⟩ s v := by
      intro z i acc l s
      induction l generalizing z i acc with
      | nil => simp [Tree.climb]
      | cons a l ih =>
        simp only [List.cons_append, Tree.climb_cons, List.length_cons]
        rw [ih (z + 1) (i / 2)]
        have h1 : z + 1 + l.length = z + (l.length + 1) := by omega
        have h2 : i / 2 / 2 ^ l.length = i / 2 ^ (l.length + 1) := by
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
        simp only [h1, h2]
    rw [hclimb]
    have hlen : (w.auth.take k').length = k' := List.length_take_of_le (by omega)
    have hdiv : tr.idf.index / 2 ^ k' / 2 = tr.idf.index / 2 ^ (k' + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    simp only [hlen, hdiv, Honest.fPos]
    split_ifs <;> rfl
  simp only [hw, hft, extract8Trace]
  set climbHit := (List.range w.auth.length).findSome? fun k' =>
    let pos := Honest.fPos tr.idf (k' + 1)
    if ft.fVal (k' + 1) = tbl.leafVal pos then
      (Q.findIdx? fun e => decide (e.1 = (SfAdrs.pkAdrs pos).toAdrs)).map fun j =>
        (j, (SfAdrs.treeAdrs pos).toAdrs, (.inl (ft.fPair k') : Msg9 pr))
    else none
  cases hch : climbHit with
  | some hit =>
    obtain ⟨k', hk', hfk'⟩ := List.exists_of_findSome?_eq_some hch
    have hk'_lt : k' < w.auth.length := List.mem_range.1 hk'
    simp only at hfk'
    split_ifs at hfk' with hcol'
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hfk'
    obtain ⟨hjlt, hjp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
    simp only [decide_eq_true_eq] at hjp
    obtain ⟨he2, hlv⟩ := hQpk Q[j] (List.getElem_mem hjlt) (Honest.fPos tr.idf (k' + 1)) hjp
    simp only [Notions.SMTCRExcl_IsCollision, List.getElem?_eq_getElem hjlt, decide_eq_true_eq]
    refine ⟨?_, by rw [he2]; simp, ?_⟩
    · rw [hjp]; exact Or.inr (shrincsX_partner_pkAdrs _).symm
    · rw [hjp, he2]
      show pr.ThLsf pk (SfAdrs.pkAdrs (Honest.fPos tr.idf (k' + 1))).toAdrs
          (WotsC.pkTops pr pk (Honest.fPos tr.idf (k' + 1)) (skOf pr d.S d.u (Honest.fPos tr.idf (k' + 1)))) =
        pr.H pk (SfAdrs.treeAdrs (Honest.fPos tr.idf (k' + 1))).toAdrs (ft.fPair k').1 (ft.fPair k').2
      rw [← hlv, ← hcol', hfVal_step k' hk'_lt]
  | none =>
    rcases hE9 with ⟨k, hk, htw, heq⟩ | ⟨htw, l, r, hl, hr, heq⟩
    · -- Contradiction: climbHit would have found `k`
      have hQmem := mem_Q9_of_pkTweaks pr hS pk htw (d := d)
      have hv_inl := visit_inl_of_mem_pkTweaks hS htw
      have hid_pos : Honest.fPos tr.idf (k + 1) ∈ leafIds P.hsf d.S :=
        Finset.mem_image.2 ⟨Node.ofLeafId P.hsf _, hv_inl.2, Node.toLeafId_ofLeafId hv_inl.1⟩
      obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid_pos pk (digOf pr d.ys _)
      have ht0 := hon0_tops pr (u := d.u) hg
      have hft_pair_k : ft.fPair k =
          (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).fPair tr.idf tr.yf w k := by
        rw [hfPair k hk, hfVal k (by omega), hN0, htops, hdStar]; rfl
      have hHpk : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).pk = pk := rfl
      have hcol_k : ft.fVal (k + 1) = tbl.leafVal (Honest.fPos tr.idf (k + 1)) := by
        rw [hHpk] at heq
        rw [hfVal_step k hk, hft_pair_k, heq, (hQpk _ hQmem _ rfl).2, ht0]
      have hsome : climbHit.isSome := by
        rw [List.findSome?_isSome_iff]
        refine ⟨k, List.mem_range.2 hk, ?_⟩
        simp only [hcol_k, ↓reduceIte, Option.isSome_map, List.findIdx?_isSome, List.any_eq_true]
        exact ⟨_, hQmem, by simp⟩
      rw [hch] at hsome; simp at hsome
    · have hHpk : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).pk = pk := rfl
      have hHS : (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).S = d.S := rfl
      have hQmem := mem_Q9_of_treeTweaks pr hS pk htw
        (by simpa [Honest.value, hHleaf, hHS, hHpk, Scheme.Fxmss.treeNode] using hl)
        (by simpa [Honest.value, hHleaf, hHS, hHpk, Scheme.Fxmss.treeNode] using hr)
      obtain ⟨l', r', he2', hnv'⟩ := hQtr _ hQmem tr.idf rfl
      have hlr : (l', r') = (l, r) := by
        have h : (Sum.inl (l', r') : Msg9 pr) = .inl (l, r) := he2'.symm
        exact Sum.inl.inj h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlr
      have hft_N0 : ft.fN0 = (hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)).fN0 tr.idf tr.yf w := by
        rw [hN0, htops, hdStar]; rfl
      have hcol : some ft.fN0 = tbl.nodeVal tr.idf.height tr.idf.index := by
        rw [hHpk] at heq
        rw [hnv', hft_N0, heq]
      have hsome : (Q.findIdx? fun e => decide (e.1 = (SfAdrs.treeAdrs tr.idf).toAdrs)).isSome := by
        rw [List.findIdx?_isSome, List.any_eq_true]
        exact ⟨_, hQmem, by simp⟩
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hsome
      obtain ⟨hjlt, hjp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
      simp only [decide_eq_true_eq] at hjp
      obtain ⟨l₀, r₀, he2₀, hnv₀⟩ := hQtr Q[j] (List.getElem_mem hjlt) tr.idf hjp
      simp only [hcol, ↓reduceIte, hj, Notions.SMTCRExcl_IsCollision, List.getElem?_eq_getElem hjlt,
        decide_eq_true_eq]
      refine ⟨?_, by rw [he2₀]; simp, ?_⟩
      · rw [hjp]; exact Or.inr (shrincsX_partner_treeAdrs _).symm
      · rw [he2₀, hjp]
        show pr.H pk (SfAdrs.treeAdrs tr.idf).toAdrs l₀ r₀ = pr.ThLsf pk (SfAdrs.pkAdrs tr.idf).toAdrs ft.fTops
        rw [← hN0]
        rw [hnv₀] at hcol
        exact (Option.some.inj hcol).symm

private theorem telescope_pre {s g1 g2 h e3 e5 e6 e6' e7 e8 e9 a0 a1 a2 ud a4 a5 a6 a7 a8 : ℝ≥0∞}
    (hs : s ≤ g1 + g2) (h1 : g1 ≤ a0) (h12 : g2 ≤ h + a1)
    (hx : h ≤ e3 + e5 + e6 + e7 + e8 + e9)
    (h3 : e3 ≤ a2) (h4 : e6 ≤ e6' + ud) (h5 : e5 ≤ a4) (h6 : e6' ≤ a5) (h7 : e7 ≤ a6)
    (h8 : e8 ≤ a7) (h9 : e9 ≤ a8) :
    s ≤ a0 + a1 + a2 + ud + a4 + a5 + a6 + a7 + a8 := by
  calc s ≤ g1 + g2 := hs
    _ ≤ a0 + ((a2 + a4 + (a5 + ud) + a6 + a7 + a8) + a1) := by
        gcongr
        refine h12.trans ?_
        gcongr
        refine hx.trans ?_
        gcongr
        exact h4.trans (by gcongr)
    _ = a0 + a1 + a2 + ud + a4 + a5 + a6 + a7 + a8 := by ring

omit [Fintype pr.Digest] in
/-- **Theorem 4.2 (Stage-1-full-precomputing reductions `B2Pre … B8Pre`)**: identical 9-term
FXMSS EU-CMA security bound using `B2Pre … B8Pre`, each of which satisfies
`Stage2ThBound ... (ξ + Vsf P)` (`theorem_4_2_stage2Bounds`). -/
theorem theorem_4_2_precomp (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Fxmss.Rom.succ pr Msg slKeygen A.toFxmssAdversary ≤
      Generic.RandomSamplingTCR.advantage (fun _ => true) 1 (B0 pr Msg slKeygen A) +
      ENNReal.ofReal (Repro.diAdvantage (B1 pr Msg slKeygen A)) +
      STCR_Succ (B2Pre pr Msg slKeygen A) +
      ∑ γ ∈ Finset.range (P.w - 2), SM_DT_UD_Advantage (B3Pre pr Msg slKeygen γ A) +
      SM_DT_TCR_Advantage (B4Pre pr Msg slKeygen A) +
      SM_DT_PRE_Advantage (B5Pre pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B6Pre pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B7Pre pr Msg slKeygen A) +
      SMTCRExcl_Succ (B8Pre pr Msg slKeygen A) := by
  set A' := A.toFxmssAdversary
  rw [Fxmss.Rom.succ_eq_gameG]
  have h01 : Pr{let o ← gameG pr Msg slKeygen A'}[WinO o] ≤
      Pr{let o ← gameG pr Msg slKeygen A'}[WinC1 o] +
        Pr{let o ← gameG pr Msg slKeygen A'}[WinNotC1 o] := by
    refine (prEvent_mono _ _ (fun o => WinC1 o ∨ WinNotC1 o) ?_).trans (prEvent_or_le _ _ _)
    rintro (_ | tr) h
    · exact h.elim
    · by_cases hc : tr.C1
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
  have h12 := claim_4_2 pr Msg slKeygen hP A
  rw [gameG2_eq_gameHyb pr Msg slKeygen hP A'] at h12
  exact telescope_pre h01 (claim_4_1 pr Msg slKeygen hP A) h12
    (gameHyb_winNotC1_le_valid pr Msg slKeygen hP hinj hgc 0 A')
    (claim_4_3_pre pr Msg slKeygen hP hgc A) (claim_4_4_pre pr Msg slKeygen hP hgc A)
    (claim_4_5_pre pr Msg slKeygen hP hgc A) (claim_4_6_pre pr Msg slKeygen hP hgc A)
    (claim_4_7_pre pr Msg slKeygen hP hgc A) (claim_4_8_pre pr Msg slKeygen hP hgc A)
    (claim_4_9_pre pr Msg slKeygen hP hgc A)

end Theorem42Precomp

/-! ## 3. Theorem 4.1: Stage-1-full-precomputing augmented reductions `B2SPre … B8SPre` -/

section Theorem41Precomp

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

/-! ### The seven Stage-1-full-precomputing augmented reductions `B2SPre … B8SPre` -/

/-- **Stage-1-full-precomputing augmented `B₂⁺` (`B2SPre`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B2SPre {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.STCRAdversary (probGrind pr L) where
  State :=
    (Setup pr (BMsg pr Msg) A.State × SfFullTable pr × List ((Adrs × pr.Digest) × (pr.Y × ℕ))) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (STcrOracleSpec (probGrind pr L)) _)
    let (tblSf, savedQ) ← (simulateQ (recordSTcrImpl (probGrind pr L))
      (OracleComp.liftComp (prog2Pre pr L d.S d.ys d.u) _)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (STcrOracleSpec (probGrind pr L)) _)
    let vt ← slVirtualTreeM pr (stcrCollCall pr (thGrind pr) (targetSumProp pr) L) uSl
    return ((d, tblSf, savedQ), uSl, vt)
  forge := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2.1) (fun st => st.1.1) (fun st o => extract2Trace pr (BMsg pr Msg) st.1.2.2 o)

/-- **Stage-1-full-precomputing augmented `B₃,γ⁺` (`B3SPre γ`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B3SPre (γ : ℕ) {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_UD_Adversary (probUD pr (L * vp.params.lsf)) where
  State := (Setup pr (BMsg pr Msg) A.State × SfFullTable pr) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  pick := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (Hyb.FSpec pr) _)
    let (tblSf, _) ← pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Hyb.FSpec pr) _)
    let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
    return ((d, tblSf), uSl, vt)
  distinguish := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2) (fun st => st.1.1) (fun st o => dist3Trace pr (BMsg pr Msg) st.1.1.S st.1.2 o)

/-- **Stage-1-full-precomputing augmented `B₄⁺` (`B4SPre`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B4SPre {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrF pr (L * vp.params.lsf * vp.params.w)) where
  State :=
    (Setup pr (BMsg pr Msg) A.State × SfFullTable pr × List (Adrs × pr.Y)) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (TcrOracleSpec (probTcrF pr (L * vp.params.lsf * vp.params.w))) _)
    let (tblSf, savedQ) ← (simulateQ (recordTcrImpl (probTcrF pr (L * vp.params.lsf * vp.params.w)))
      (OracleComp.liftComp (prog4Pre pr L d.S d.ys d.u) _)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (TcrOracleSpec (probTcrF pr (L * vp.params.lsf * vp.params.w))) _)
    let vt ← slVirtualTreeM pr (tcrCollCall pr (thF pr) (L * vp.params.lsf * vp.params.w)) uSl
    return ((d, tblSf, savedQ), uSl, vt)
  forge := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2.1) (fun st => st.1.1)
    (fun st o => extract4Trace pr (BMsg pr Msg) st.1.1.S st.1.2.1 st.1.2.2 o)

/-- **Stage-1-full-precomputing augmented `B₅⁺` (`B5SPre`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B5SPre {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_PRE_Adversary (probPre pr (L * vp.params.lsf)) where
  State :=
    ((d : Setup pr (BMsg pr Msg) A.State) × SfFullTable pr × List (SkIdx vp.params d.S × Adrs)) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (Hyb.FSpec pr) _)
    let (tblSf, tgs) ← pickProgPre pr Hyb.selPre id d.ys d.u
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Hyb.FSpec pr) _)
    let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
    return (⟨d, tblSf, tgs⟩, uSl, vt)
  invert := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2.1) (fun st => st.1.1)
    (fun st o => extract5Trace pr (BMsg pr Msg) st.1.2.1 st.1.2.2 o)

/-- **Stage-1-full-precomputing augmented `B₆⁺` (`B6SPre`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B6SPre {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrLsf pr L) where
  State :=
    (Setup pr (BMsg pr Msg) A.State × SfFullTable pr × List (Adrs × Vector pr.Y vp.params.lsf)) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (TcrOracleSpec (probTcrLsf pr L)) _)
    let (tblSf, savedQ) ← (simulateQ (recordTcrImpl (probTcrLsf pr L))
      (OracleComp.liftComp (prog6Pre pr L d.S d.ys d.u) _)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (TcrOracleSpec (probTcrLsf pr L)) _)
    let vt ← slVirtualTreeM pr (tcrCollCall pr (thLsf pr) L) uSl
    return ((d, tblSf, savedQ), uSl, vt)
  forge := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2.1) (fun st => st.1.1)
    (fun st o => extract6Trace pr (BMsg pr Msg) st.1.1.S st.1.2.1 st.1.2.2 o)

/-- **Stage-1-full-precomputing augmented `B₇⁺` (`B7SPre`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B7SPre {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrH pr (L - 1)) where
  State :=
    (Setup pr (BMsg pr Msg) A.State × SfFullTable pr × List (Adrs × (pr.Y × pr.Y))) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (TcrOracleSpec (probTcrH pr (L - 1))) _)
    let (tblSf, savedQ) ← (simulateQ (recordTcrImpl (probTcrH pr (L - 1)))
      (OracleComp.liftComp (prog7Pre pr d.S d.ys d.u) _)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (TcrOracleSpec (probTcrH pr (L - 1))) _)
    let vt ← slVirtualTreeM pr (tcrCollCall pr (thH pr) (L - 1)) uSl
    return ((d, tblSf, savedQ), uSl, vt)
  forge := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2.1) (fun st => st.1.1)
    (fun st o => extract7Trace pr (BMsg pr Msg) st.1.2.1 st.1.2.2 o)

/-- **Stage-1-full-precomputing augmented `B₈⁺` (`B8SPre`)** for Claim 4.15 / Theorem 4.1. -/
noncomputable def B8SPre {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.SMTCRExclAdversary (probExcl pr (L + (L - 1))) where
  State :=
    (Setup pr (BMsg pr Msg) A.State × SfFullTable pr × List (Adrs × Msg9 pr)) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (ExclOracleSpec (probExcl pr (L + (L - 1)))) _)
    let (tblSf, savedQ) ← (simulateQ (recordExclImpl (probExcl pr (L + (L - 1))))
      (OracleComp.liftComp (prog8Pre pr d.S d.ys d.u) _)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (ExclOracleSpec (probExcl pr (L + (L - 1)))) _)
    let vt ← slVirtualTreeM pr (exclCollCall pr (L + (L - 1))) uSl
    return ((d, tblSf, savedQ), uSl, vt)
  forge := stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
    (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
    (fun st => st.1.2.1) (fun st => st.1.1)
    (fun st o => extract8Trace pr (BMsg pr Msg) st.1.2.1 st.1.2.2 o)

/-! ### Stage-2 `≤ ξ + V_sf` (`V_sf = 497`) complexity bounds for `B2SPre … B8SPre` -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Theorem 4.1 stateful Stage-2 `Th_λ` complexity bounds**: every augmented stateful collection
reduction `B2SPre, B3SPre γ, B4SPre, B5SPre, B6SPre, B7SPre, B8SPre` built from a
`BudgetedShrincsForger` with Stage-2 `Th_λ` budget `ξ` makes at most `ξ + Vsf vp.params`
(`ξ + 497` at SHRINCS parameters) Stage-2 `Th_λ` evaluations. -/
noncomputable def theorem_4_1_stateful_stage2Bounds {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedShrincsForger pr Msg enc qs qh₁ qh₂ L ξ) :
    STcrStage2Bound pr (B2SPre pr Msg enc A.toForger) (ξ + Vsf vp.params) ×
    (∀ γ, UdStage2Bound pr (B3SPre pr Msg enc γ A.toForger) (ξ + Vsf vp.params)) ×
    TcrStage2Bound pr (B4SPre pr Msg enc A.toForger) (ξ + Vsf vp.params) ×
    PreStage2Bound pr (B5SPre pr Msg enc A.toForger) (ξ + Vsf vp.params) ×
    TcrStage2Bound pr (B6SPre pr Msg enc A.toForger) (ξ + Vsf vp.params) ×
    TcrStage2Bound pr (B7SPre pr Msg enc A.toForger) (ξ + Vsf vp.params) ×
    ExclStage2Bound pr (B8SPre pr Msg enc A.toForger) (ξ + Vsf vp.params) :=
  ⟨stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B2SPre pr Msg enc A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _,
   fun γ => stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B3SPre pr Msg enc γ A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _,
   stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B4SPre pr Msg enc A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _,
   stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B5SPre pr Msg enc A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _,
   stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B6SPre pr Msg enc A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _,
   stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B7SPre pr Msg enc A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _,
   stage2RunWithTrace_stage2Bound pr (BMsg pr Msg) (slKeygenS pr)
      (fun st : (B8SPre pr Msg enc A.toForger).State =>
        BudgetedShrincsForger.toAFTable pr A st.2.1 st.2.2.1 st.2.2.2) _ _ _⟩

/-! ### Bridging `B2SPre … B8SPre` to `B2Pre … B8Pre` on `AFEager` -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem stageHybPre_AFTable_eq_AFEager {qs qh₁ qh₂ L : ℕ}
    (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L)
    (uSl : SlSecAdrs vp → pr.Y) (tblSf : SfFullTable pr)
    (d : Setup pr (BMsg pr Msg) A.State) (pk : pr.PkSeed) :
    stageHybPre pr (BMsg pr Msg) (slKeygenS pr)
        (AFTable pr Msg enc A uSl (slVirtualTreeDet pr pk uSl).1
          (slVirtualTreeDet pr pk uSl).2).toFxmssAdversary tblSf d pk =
      stageHybPre pr (BMsg pr Msg) (slKeygenS pr)
        (AFEager pr Msg enc A uSl).toFxmssAdversary tblSf d pk := by
  have hvt := slVirtualTreeDet_spec pr pk uSl
  have hroot : (slVirtualTreeDet pr pk uSl).1 = slRootDet pr pk uSl :=
    hvt.1.trans (slRootDet_eq_honestVal pr pk uSl).symm
  have hsign : ∀ pkSl' m R, slSignTable pr (slVirtualTreeDet pr pk uSl).2 pk pkSl' uSl m R =
      slSignDet pr pk pkSl' uSl m R :=
    fun pkSl' m R => slSignTable_eq_slSignDet pr pk pkSl' uSl hvt.2.2 m R
  unfold stageHybPre
  by_cases hS : d.S.TreeValid vp.params.hsf
  · simp only [hS, not_true_eq_false, ↓reduceIte]
    refine bind_congr fun pkSl => ?_
    set K : Keys pr := ⟨d.S, pk, pkSl, tblSf.pkSf⟩
    have hforge : (AFTable pr Msg enc A uSl (slVirtualTreeDet pr pk uSl).1
          (slVirtualTreeDet pr pk uSl).2).toFxmssAdversary.forge d.st K.S K.toPK =
        (AFEager pr Msg enc A uSl).toFxmssAdversary.forge d.st K.S K.toPK :=
      congrArg (Functor.map Prod.fst)
        (forgeExtDet_congr pr Msg enc (fun _ => (slVirtualTreeDet pr pk uSl).1)
          (fun p => slRootDet pr p uSl)
          (fun p pkSl' m R => slSignTable pr (slVirtualTreeDet pr pk uSl).2 p pkSl' uSl m R)
          (fun p pkSl' m R => slSignDet pr p pkSl' uSl m R)
          A.toShrincsAdversary d.st K.S K.toPK hroot hsign)
    unfold stage2Prog
    rw [hforge]
  · simp only [hS, not_false_eq_true, ↓reduceIte]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] in
private theorem B2SPre_exp_eq (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    STCR_Experiment (B2SPre pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        STCR_Experiment (B2Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : STCR_Experiment (B2SPre pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q2Pre pr L d.S d.ys pk
          let out ← (B2Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return STCR_IsCollision (probGrind pr L) pk Q out) := by
    unfold STCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B2SPre, STCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordSTcr_run (probGrind pr L) pk
      (OracleComp.liftComp (prog2Pre pr L d.S d.ys d.u) _) [] []
    have hgood := stcrGood_Q2Pre pr L d.S d.ys d.u pk
      (fun hS => setupHyb_length_anchorList_le pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd hS)
    rw [stcr_run_eq _ _ _ (by rw [prog2Pre_perm_run pr vp.valid hgc]; exact hgood),
      prog2Pre_perm_run pr vp.valid hgc, map_pure] at hrec
    simp only [STCR_oracles, unifFwd, STcrOracleSpec] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    have hsf : ∀ e ∈ Q2Pre pr L d.S d.ys pk, Scheme.IsStateful e.1.1 := by
      intro e he
      unfold Q2Pre at he; split_ifs at he with hS
      · obtain ⟨id, -, he⟩ := List.mem_flatMap.1 he
        cases hlc : leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs
            (digOf pr d.ys id) with
        | none => simp [hlc] at he
        | some i => simp only [hlc, List.mem_singleton] at he; rw [he]; exact SfAdrs.isStateful_toAdrs _
      · simp at he
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_stcr pr (thGrind pr) (targetSumProp pr) L pk uSl
      (Q2Pre pr L d.S d.ys pk) (C2Pre pr d.S pk d.u) hsf
    simp only [STCR_oracles] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
    have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)) d pk
    exact Hyb.evalDistEq_of_eq (by dsimp only [B2Pre, stage2RunWithTrace]; rw [hst])
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        STCR_Experiment (B2Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q2Pre pr L d.S d.ys pk
          let out ← (B2Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return STCR_IsCollision (probGrind pr L) pk Q out) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B2Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
               let Q := Q2Pre pr L d.S d.ys pk
               let out ← (B2Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
                 (d, tblSf, Q) pk
               return STCR_IsCollision (probGrind pr L) pk Q out) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B3SPre_exp_eq (hgc : GrindComplete pr) (w : SM_DT_UD_World) (γ : ℕ)
    {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment w (B3SPre pr Msg enc γ A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_UD_Experiment w (B3Pre pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl))) := by
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_UD_Experiment w (B3SPre pr Msg enc γ A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let u' ← Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          (fun o => decide (HybEventValid pr (BMsg pr Msg) Honest.E6 o)) <$>
            stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl).toFxmssAdversary
              (betaOf pr (γ + 1) pk u') d pk) := by
    unfold SM_DT_UD_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B3SPre, SM_DT_UD_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hcoll : Hyb.CollAnswers pr (id : Adrs → Adrs) pk
        (unifFwd (SM_DT_UD_State Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
          collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk)) := by
      intro q qs tws hq; rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
      exact collectionOracle_run_of_fresh id q hq
    have hchal : Hyb.ChalAnswers pr (id : Adrs → Adrs) (L * vp.params.lsf) (Hyb.udAns pr w pk)
        (fun t _ => t)
        (unifFwd (SM_DT_UD_State Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
          collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk)) := by
      intro t qs tws hlen hfr; rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      cases w
      · exact SM_DT_UD_challengeOracle_run_of_fresh_real hlen hfr
      · exact SM_DT_UD_challengeOracle_run_of_fresh_ideal hlen hfr
    have hrun := run_pickProgPre pr hcoll hchal (fun _ _ => rfl) (Hyb.selUD γ)
      (fun a => min (γ + 1) (a - 1))
      (fun a _ j hj => by simp only [Hyb.selUD] at hj; split_ifs at hj with hγ; cases hj; omega)
      d.ys d.u (Hyb.targets_length_le pr (slKeygenS pr) (AF pr Msg enc A) pk (Hyb.selUD γ) hd)
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hstep1 : ∀ z : (SfFullTable pr × List (SkIdx vp.params d.S × Adrs)) × (List Adrs × List Adrs),
        (∀ t ∈ z.2.1, Scheme.IsStateful t) →
        (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
            (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
              collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk))
            (do let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) : OracleComp (Hyb.FSpec pr) _)
                let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
                return ((d, z.1.1), uSl, vt))).run z.2 >>=
          (fun p => stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
            (fun st => (AFTable pr Msg enc A st.2.1 st.2.2.1 st.2.2.2).toFxmssAdversary)
            (fun st => st.1.2) (fun st => st.1.1)
            (fun st o => dist3Trace pr (BMsg pr Msg) st.1.1.S st.1.2 o) p.1 pk) =
        ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun uSl =>
          stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
            (fun _ : Unit => (AFEager pr Msg enc A uSl).toFxmssAdversary)
            (fun _ => z.1.1) (fun _ => d)
            (fun _ o => dist3Trace pr (BMsg pr Msg) d.S z.1.1 o) () pk := by
      intro z hsf
      rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
      refine bind_congr fun uSl => ?_
      obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_ud pr w (L * vp.params.lsf) pk uSl z.2.1 z.2.2 hsf
      simp only [SM_DT_UD_oracles] at hvt
      rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
      have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl z.1.1 d pk
      dsimp only [stage2RunWithTrace]
      rw [hst]
    have hsf_supp : ∀ z ∈ support ((simulateQ (unifFwd (SM_DT_UD_State Adrs) +
        (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
          collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk))
        (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], [])),
        ∀ t ∈ z.2.1, Scheme.IsStateful t := by
      intro z hz t ht
      have hm : (z.1, z.2.1) ∈ support ((fun z => (z.1, z.2.1)) <$>
          (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
            (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
              collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk))
            (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], [])) := by
        rw [support_map]; exact Set.mem_image_of_mem _ hz
      rw [support_eq_of_evalDistEq hrun, support_map, Set.mem_image] at hm
      obtain ⟨w', hw', heq⟩ := hm
      have hqs_eq : z.2.1 = w'.2 := (Prod.mk.inj heq).2.symm
      rw [hqs_eq] at ht
      have hmem : ∀ (l : List (SkIdx vp.params d.S × Adrs)) (u₀ : SkIdx vp.params d.S → pr.Y)
          (qs₀ : List Adrs) (x : (SkIdx vp.params d.S → pr.Y) × List Adrs),
          x ∈ support (Hyb.runRef (Hyb.udAns pr w pk) (fun t _ => t) l u₀ qs₀) →
          (∀ s ∈ qs₀, Scheme.IsStateful s) → (∀ pt ∈ l, Scheme.IsStateful pt.2) →
          ∀ s ∈ x.2, Scheme.IsStateful s := by
        intro l; induction l with
        | nil =>
          intro u₀ qs₀ x hx hq _
          simp only [Hyb.runRef, support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hq
        | cons pt ts ih =>
          intro u₀ qs₀ x hx hq hl
          simp only [Hyb.runRef, mem_support_bind_iff] at hx
          obtain ⟨y, -, hx⟩ := hx
          refine ih _ _ x hx (fun s hs => ?_) (fun pt' h' => hl pt' (by simp [h']))
          rcases List.mem_append.1 hs with hs | hs
          · exact hq s hs
          · rw [List.mem_singleton.1 hs]; exact hl pt (by simp)
      refine hmem _ d.u [] w' hw' (by simp) (fun pt hpt => ?_) t ht
      unfold Hyb.targets at hpt; split_ifs at hpt with hS
      · obtain ⟨j, -, hpt2⟩ := (Hyb.mem_targetsOf pr).1 hpt
        rw [hpt2]; exact SfAdrs.isStateful_toAdrs _
      · simp at hpt
    refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ fun z hz =>
      Hyb.evalDistEq_of_eq (hstep1 z (hsf_supp z hz))) ?_
    have hmap : Prod.fst <$> (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
          (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
            collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk))
          (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], []) =ᵈ
        (fun u' => (if d.S.TreeValid vp.params.hsf then
            buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
              (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) u'
          else default, Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys)) <$>
          Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u := by
      have h1 := hrun.map Prod.fst
      rw [Functor.map_map, Functor.map_map] at h1
      have h2 : (fun z : (SkIdx vp.params d.S → pr.Y) × List Adrs =>
            (if d.S.TreeValid vp.params.hsf then
              buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
                (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
            else default, Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys)) <$>
            Hyb.runRef (Hyb.udAns pr w pk) (fun t _ => t) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u [] =
          (fun u' => (if d.S.TreeValid vp.params.hsf then
              buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
                (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) u'
            else default, Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys)) <$>
            Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u := by
        rw [← Hyb.map_fst_runRef (Hyb.udAns pr w pk) (fun t _ => t)
          (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u [], Functor.map_map]
      exact h1.trans (Hyb.evalDistEq_of_eq h2)
    have hre : ((simulateQ (unifFwd (SM_DT_UD_State Adrs) +
          (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
            collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk))
          (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], []) >>=
        fun z => ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun uSl =>
          stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
            (fun _ : Unit => (AFEager pr Msg enc A uSl).toFxmssAdversary)
            (fun _ => z.1.1) (fun _ => d)
            (fun _ o => dist3Trace pr (BMsg pr Msg) d.S z.1.1 o) () pk) =
        (Prod.fst <$> (simulateQ (unifFwd (SM_DT_UD_State Adrs) +
          (SM_DT_UD_challengeOracle w (probUD pr (L * vp.params.lsf)) pk +
            collectionOracle id (probUD pr (L * vp.params.lsf)).thColl pk))
          (pickProgPre pr (Hyb.selUD γ) (fun a => min (γ + 1) (a - 1)) d.ys d.u)).run ([], [])) >>=
        fun tblTgs => ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun uSl =>
          stage2RunWithTrace pr (BMsg pr Msg) (slKeygenS pr)
            (fun _ : Unit => (AFEager pr Msg enc A uSl).toFxmssAdversary)
            (fun _ => tblTgs.1) (fun _ => d)
            (fun _ o => dist3Trace pr (BMsg pr Msg) d.S tblTgs.1 o) () pk := by
      simp [bind_map_left]
    refine (Hyb.evalDistEq_of_eq hre).trans ?_
    refine (hmap.bind_left _).trans ?_
    rw [bind_map_left]
    refine EvalDistEq.bind_right _ fun u' => EvalDistEq.bind_right _ fun uSl => ?_
    set tbl := if d.S.TreeValid vp.params.hsf then
      buildSfTableHybDet pr pk (fun a => min (γ + 1) (a - 1))
        (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) u' else default
    have hagree : d.S.TreeValid vp.params.hsf →
        SfTableAgree pr (hon pr d.S pk (digOf pr d.ys) (betaOf pr (γ + 1) pk u')) tbl :=
      fun hS => by
        simp only [tbl, hS, ↓reduceIte]
        exact buildSfTableHybDet_agree pr vp.valid hgc hS pk d.ys u'
          (fun a => min (γ + 1) (a - 1)) (betaOf pr (γ + 1) pk u')
          (fun a _ => by omega) (fun _ _ _ => rfl)
    rw [stage2RunWithTrace_eq_map_stageHyb pr (BMsg pr Msg) (slKeygenS pr)
      (AFEager pr Msg enc A uSl).toFxmssAdversary (betaOf pr (γ + 1) pk u')
      (fun _ : Unit => tbl) (fun _ => d) pk () hagree
      (fun _ o => dist3Trace pr (BMsg pr Msg) d.S tbl o)]
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine EvalDistEq.bind_congr_of_support _ fun o ho => ?_
    rcases o with _ | ⟨tr, H⟩
    · exact Hyb.evalDistEq_of_eq (by
        simp only [Function.comp_apply, dist3Trace]
        exact congrArg pure (decide_eq_false (show ¬ HybEventValid pr (BMsg pr Msg) Honest.E6 none from id)).symm)
    · obtain ⟨hS, rfl⟩ := Hyb.mem_support_stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFEager pr Msg enc A uSl).toFxmssAdversary _ d pk ho
      have h3 := dist3Trace_eq_decide pr (BMsg pr Msg) _ tbl (hagree hS) tr
      cases hσ : tr.σf.2 <;> (
        simp only [hσ] at h3
        exact Hyb.evalDistEq_of_eq (by simp only [Function.comp_apply, hσ]; exact congrArg pure h3))
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_UD_Experiment w (B3Pre pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let u' ← Hyb.fillWith (Hyb.udAns pr w pk) (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          (fun o => decide (HybEventValid pr (BMsg pr Msg) Honest.E6 o)) <$>
            stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl).toFxmssAdversary
              (betaOf pr (γ + 1) pk u') d pk) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B3Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc w γ (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let u' ← Hyb.fillWith (Hyb.udAns pr w pk)
                 (Hyb.targets pr pk (Hyb.selUD γ) d.S d.ys) d.u
               (fun o => decide (HybEventValid pr (BMsg pr Msg) Honest.E6 o)) <$>
                 stageHyb pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl).toFxmssAdversary
                   (betaOf pr (γ + 1) pk u') d pk) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun d => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B4SPre_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B4SPre pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (B4Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let prob := probTcrF pr (L * vp.params.lsf * vp.params.w)
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_TCR_Experiment (B4SPre pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q4Pre pr d.S d.u pk
          let out ← (B4Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return tcrWin prob pk Q out) := by
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B4SPre, SM_DT_TCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordTcr_run prob pk
      (OracleComp.liftComp (prog4Pre pr L d.S d.ys d.u) _) [] []
    have hgood := tcrGood_Q4Pre pr L d.S d.ys d.u pk
      (fun hS => anchors_le_of_mem_support_setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd hS)
    rw [tcr_run_eq _ _ _ (by rw [prog4Pre_perm_run]; exact hgood), prog4Pre_perm_run, map_pure] at hrec
    simp only [SM_DT_TCR_oracles, unifFwd, TcrOracleSpec, prob] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    have hsf : ∀ e ∈ Q4Pre pr d.S d.u pk, Scheme.IsStateful e.1 := by
      intro e he
      unfold Q4Pre at he; split_ifs at he with hS
      · obtain ⟨node, -, he⟩ := List.mem_flatMap.1 he
        rcases node with id | id
        · simp only [entryQ, List.mem_flatMap, List.mem_map] at he
          obtain ⟨ch, -, j, -, rfl⟩ := he; exact SfAdrs.isStateful_toAdrs _
        · simp only [entryQ, combineLog] at he; split at he <;> simp at he
      · simp at he
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_tcr pr (thF pr) (L * vp.params.lsf * vp.params.w)
      pk uSl (Q4Pre pr d.S d.u pk) (C4Pre pr d.S d.ys d.u pk) hsf
    simp only [SM_DT_TCR_oracles] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
    have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)) d pk
    exact Hyb.evalDistEq_of_eq (by
      dsimp only [B4Pre, stage2RunWithTrace]
      rw [hst]
      refine bind_congr fun out => ?_
      rcases out with ⟨j, m⟩
      simp only [tcrWin]; split <;> rename_i h <;> simp [h])
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (B4Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q4Pre pr d.S d.u pk
          let out ← (B4Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return tcrWin prob pk Q out) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B4Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
               let Q := Q4Pre pr d.S d.u pk
               let out ← (B4Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
                 (d, tblSf, Q) pk
               return tcrWin prob pk Q out) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B5SPre_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_PRE_Experiment (B5SPre pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_PRE_Experiment (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_PRE_Experiment (B5SPre pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let z ← Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u []
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tbl := if d.S.TreeValid vp.params.hsf then
            buildSfTableHybDet pr pk id (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
          else default
          let jm ← (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).invert
            ⟨d, tbl, Hyb.targets pr pk Hyb.selPre d.S d.ys⟩ pk
          return Hyb.preWin pr pk z.2 jm) := by
    unfold SM_DT_PRE_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B5SPre, SM_DT_PRE_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hcoll : Hyb.CollAnswers pr (Prod.fst : Adrs × pr.Y → Adrs) pk
        (unifFwd (SM_DT_PRE_State Adrs pr.Y) + (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
          collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk)) := by
      intro q qs tws hq; rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
      exact collectionOracle_run_of_fresh Prod.fst q hq
    have hchal : Hyb.ChalAnswers pr (Prod.fst : Adrs × pr.Y → Adrs) (L * vp.params.lsf)
        (fun t x => pr.F pk t x) (fun t x => (t, x))
        (unifFwd (SM_DT_PRE_State Adrs pr.Y) + (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
          collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk)) := by
      intro t qs tws hlen hfr; rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact SM_DT_PRE_challengeOracle_run_of_fresh hlen hfr
    have hrun := run_pickProgPre pr hcoll hchal (fun _ _ => rfl) Hyb.selPre id
      (fun a _ j hj => by simp only [Hyb.selPre, id_eq] at hj ⊢; split_ifs at hj with h0; cases hj; omega)
      d.ys d.u (Hyb.targets_length_le pr (slKeygenS pr) (AF pr Msg enc A) pk Hyb.selPre hd)
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hsf_supp : ∀ z ∈ support ((simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
        (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
          collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk))
        (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], [])),
        ∀ e ∈ z.2.1, Scheme.IsStateful e.1 := by
      intro z hz e he
      have hm : (z.1, z.2.1) ∈ support ((fun z => (z.1, z.2.1)) <$>
          (simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
            (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
              collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk))
            (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], [])) := by
        rw [support_map]; exact Set.mem_image_of_mem _ hz
      rw [support_eq_of_evalDistEq hrun, support_map, Set.mem_image] at hm
      obtain ⟨w', hw', heq⟩ := hm
      have hqs_eq : z.2.1 = w'.2 := (Prod.mk.inj heq).2.symm
      rw [hqs_eq] at he
      have hmem : ∀ (l : List (SkIdx vp.params d.S × Adrs)) (u₀ : SkIdx vp.params d.S → pr.Y)
          (qs₀ : List (Adrs × pr.Y)) (x : (SkIdx vp.params d.S → pr.Y) × List (Adrs × pr.Y)),
          x ∈ support (Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x)) l u₀ qs₀) →
          (∀ s ∈ qs₀, Scheme.IsStateful s.1) → (∀ pt ∈ l, Scheme.IsStateful pt.2) →
          ∀ s ∈ x.2, Scheme.IsStateful s.1 := by
        intro l; induction l with
        | nil =>
          intro u₀ qs₀ x hx hq _
          simp only [Hyb.runRef, support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact hq
        | cons pt ts ih =>
          intro u₀ qs₀ x hx hq hl
          simp only [Hyb.runRef, mem_support_bind_iff] at hx
          obtain ⟨y, -, hx⟩ := hx
          refine ih _ _ x hx (fun s hs => ?_) (fun pt' h' => hl pt' (by simp [h']))
          rcases List.mem_append.1 hs with hs | hs
          · exact hq s hs
          · rw [List.mem_singleton.1 hs]; exact hl pt (by simp)
      refine hmem _ d.u [] w' hw' (by simp) (fun pt hpt => ?_) e he
      unfold Hyb.targets at hpt; split_ifs at hpt with hS
      · obtain ⟨j, -, hpt2⟩ := (Hyb.mem_targetsOf pr).1 hpt
        rw [hpt2]; exact SfAdrs.isStateful_toAdrs _
      · simp at hpt
    refine EvalDistEq.trans
      (my := (simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
          (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
            collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk))
          (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], []) >>= fun z =>
        ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun uSl =>
          (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).invert
            ⟨d, z.1.1, z.1.2⟩ pk >>= fun jm => pure (Hyb.preWin pr pk z.2.1 jm))
      (EvalDistEq.bind_congr_of_support _ fun z hz => Hyb.evalDistEq_of_eq (by
        have hsf := hsf_supp z hz
        rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
        refine bind_congr fun uSl => ?_
        obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_pre pr (L * vp.params.lsf) pk uSl z.2.1 z.2.2 hsf
        simp only [SM_DT_PRE_oracles] at hvt
        rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
        have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl z.1.1 d pk
        dsimp only [B5Pre, stage2RunWithTrace]
        rw [hst]
        refine bind_congr fun jm => ?_
        simp only [Hyb.preWin]
        cases z.2.1[jm.1]? with
        | none => rfl
        | some tx => obtain ⟨t, x⟩ := tx; rfl)) ?_
    have hre : ((simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
          (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
            collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk))
          (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], []) >>= fun z =>
        ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun uSl =>
          (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).invert
            ⟨d, z.1.1, z.1.2⟩ pk >>= fun jm => pure (Hyb.preWin pr pk z.2.1 jm)) =
        ((fun z => (z.1, z.2.1)) <$> (simulateQ (unifFwd (SM_DT_PRE_State Adrs pr.Y) +
          (SM_DT_PRE_challengeOracle (probPre pr (L * vp.params.lsf)) pk +
            collectionOracle (Q := Adrs × pr.Y) Prod.fst (probPre pr (L * vp.params.lsf)).thColl pk))
          (pickProgPre pr Hyb.selPre id d.ys d.u)).run ([], [])) >>= fun z =>
        ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun uSl =>
          (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).invert
            ⟨d, z.1.1, z.1.2⟩ pk >>= fun jm => pure (Hyb.preWin pr pk z.2 jm) := by
      simp [bind_map_left]
    refine (Hyb.evalDistEq_of_eq hre).trans ?_
    refine (hrun.bind_left _).trans ?_
    rw [bind_map_left]
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_PRE_Experiment (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let z ← Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u []
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tbl := if d.S.TreeValid vp.params.hsf then
            buildSfTableHybDet pr pk id (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
          else default
          let jm ← (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).invert
            ⟨d, tbl, Hyb.targets pr pk Hyb.selPre d.S d.ys⟩ pk
          return Hyb.preWin pr pk z.2 jm) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B5Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let z ← Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
                 (Hyb.targets pr pk Hyb.selPre d.S d.ys) d.u []
               let tbl := if d.S.TreeValid vp.params.hsf then
                 buildSfTableHybDet pr pk id (fun a => WotsC.grind pr pk a.1 (digOf pr d.ys a.1)) z.1
               else default
               let jm ← (B5Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).invert
                 ⟨d, tbl, Hyb.targets pr pk Hyb.selPre d.S d.ys⟩ pk
               return Hyb.preWin pr pk z.2 jm) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun d => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B6SPre_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B6SPre pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (B6Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let prob := probTcrLsf pr L
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_TCR_Experiment (B6SPre pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q6Pre pr d.S d.u pk
          let out ← (B6Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return tcrWin prob pk Q out) := by
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B6SPre, SM_DT_TCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordTcr_run prob pk
      (OracleComp.liftComp (prog6Pre pr L d.S d.ys d.u) _) [] []
    have hgood := tcrGood_Q6Pre pr L d.S d.ys d.u pk
      (fun hS => anchors_le_of_mem_support_setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd hS)
    rw [tcr_run_eq _ _ _ (by rw [prog6Pre_perm_run]; exact hgood), prog6Pre_perm_run, map_pure] at hrec
    simp only [SM_DT_TCR_oracles, unifFwd, TcrOracleSpec, prob] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    have hsf : ∀ e ∈ Q6Pre pr d.S d.u pk, Scheme.IsStateful e.1 := by
      intro e he
      unfold Q6Pre at he; split_ifs at he with hS
      · obtain ⟨node, -, he⟩ := List.mem_flatMap.1 he
        rcases node with id | id
        · simp only [entryQ, List.mem_singleton] at he; rw [he]; exact SfAdrs.isStateful_toAdrs _
        · simp only [entryQ, combineLog] at he; split at he <;> simp at he
      · simp at he
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_tcr pr (thLsf pr) L pk uSl
      (Q6Pre pr d.S d.u pk) (C6Pre pr d.S d.ys d.u pk) hsf
    simp only [SM_DT_TCR_oracles] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
    have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)) d pk
    exact Hyb.evalDistEq_of_eq (by
      dsimp only [B6Pre, stage2RunWithTrace]
      rw [hst]
      refine bind_congr fun out => ?_
      rcases out with ⟨j, m⟩
      simp only [tcrWin]; split <;> rename_i h <;> simp [h])
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (B6Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q6Pre pr d.S d.u pk
          let out ← (B6Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return tcrWin prob pk Q out) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B6Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
               let Q := Q6Pre pr d.S d.u pk
               let out ← (B6Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
                 (d, tblSf, Q) pk
               return tcrWin prob pk Q out) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B7SPre_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B7SPre pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (B7Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let prob := probTcrH pr (L - 1)
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_TCR_Experiment (B7SPre pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q7 pr (BMsg pr Msg) d pk
          let out ← (B7Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return tcrWin prob pk Q out) := by
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B7SPre, SM_DT_TCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordTcr_run prob pk
      (OracleComp.liftComp (prog7Pre pr d.S d.ys d.u) _) [] []
    have hgood7 := tcrGood7 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd pk
    have hgood : TcrGood (L - 1) (Q7 pr (BMsg pr Msg) d pk, C7Pre pr d.S d.ys pk) := by
      refine ⟨hgood7.1, hgood7.2.1, fun t ht hq => ?_⟩
      unfold C7Pre at ht; split_ifs at ht with hS
      · rcases List.mem_append.1 ht with h1 | h2
        · obtain ⟨id, -, h⟩ := List.mem_flatMap.1 h1
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
          obtain ⟨id', -, he1⟩ := mem_Q7 pr he
          rw [he1] at h
          exact SfAdrs.treeAdrs_ne_grindAdrs id' id (mem_grindSearchLog pr pk id _ _ _ h)
        · exact hgood7.2.2 t (by simp [C7, hS, h2]) hq
      · simp at ht
    rw [tcr_run_eq _ _ _ (by rw [prog7Pre_perm_run]; exact hgood), prog7Pre_perm_run, map_pure] at hrec
    simp only [SM_DT_TCR_oracles, unifFwd, TcrOracleSpec, prob] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    have hsf : ∀ e ∈ Q7 pr (BMsg pr Msg) d pk, Scheme.IsStateful e.1 := fun e he => by
      obtain ⟨id, -, he1⟩ := mem_Q7 pr he; rw [he1]; exact SfAdrs.isStateful_toAdrs _
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_tcr pr (thH pr) (L - 1) pk uSl
      (Q7 pr (BMsg pr Msg) d pk) (C7Pre pr d.S d.ys pk) hsf
    simp only [SM_DT_TCR_oracles] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
    have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)) d pk
    exact Hyb.evalDistEq_of_eq (by
      dsimp only [B7Pre, stage2RunWithTrace]
      rw [hst]
      refine bind_congr fun out => ?_
      rcases out with ⟨j, m⟩
      simp only [tcrWin]
      split <;> rename_i h1 <;> split <;> rename_i h2
      · rfl
      · exact absurd (h1.symm.trans h2) (by simp)
      · exact absurd (h1.symm.trans h2) (by simp)
      · have h3 := Option.some.inj (h1.symm.trans h2)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
        rfl)
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (B7Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q7 pr (BMsg pr Msg) d pk
          let out ← (B7Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return tcrWin prob pk Q out) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B7Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
               let Q := Q7 pr (BMsg pr Msg) d pk
               let out ← (B7Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
                 (d, tblSf, Q) pk
               return tcrWin prob pk Q out) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
private theorem B8SPre_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.SMTCRExcl_Experiment (B8SPre pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.SMTCRExcl_Experiment
          (B8Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let prob := probExcl pr (L + (L - 1))
  let g₁ : ProbComp (Setup pr (BMsg pr Msg) A.State) :=
    setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : Notions.SMTCRExcl_Experiment (B8SPre pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q9 pr (BMsg pr Msg) d pk
          let out ← (B8Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return Notions.SMTCRExcl_IsCollision prob pk Q out) := by
    unfold Notions.SMTCRExcl_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B8SPre, Notions.SMTCRExcl_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordExcl_run prob pk
      (OracleComp.liftComp (prog8Pre pr d.S d.ys d.u) _) [] []
    have hgood9 := exclGood9 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd pk
    have hgood : ExclGood shrincsX (L + (L - 1)) (Q9 pr (BMsg pr Msg) d pk, C8Pre pr d.S d.ys pk) := by
      refine ⟨hgood9.1, hgood9.2.1, fun t ht e he hmem => ?_⟩
      unfold C8Pre at ht; split_ifs at ht with hS
      · rcases List.mem_append.1 ht with h1 | h2
        · obtain ⟨id, -, h⟩ := List.mem_flatMap.1 h1
          have htg := mem_grindSearchLog pr pk id _ _ _ h
          subst htg
          rcases mem_Q9 pr he with ⟨id', -, he1⟩ | ⟨id', -, he1⟩
          · rcases hmem with hmem | hmem
            · rw [he1] at hmem; exact SfAdrs.pkAdrs_ne_grindAdrs id' id hmem.symm
            · rw [he1, shrincsX_partner_pkAdrs] at hmem
              exact SfAdrs.treeAdrs_ne_grindAdrs id' id hmem.symm
          · rcases hmem with hmem | hmem
            · rw [he1] at hmem; exact SfAdrs.treeAdrs_ne_grindAdrs id' id hmem.symm
            · rw [he1, shrincsX_partner_treeAdrs] at hmem
              exact SfAdrs.pkAdrs_ne_grindAdrs id' id hmem.symm
        · exact hgood9.2.2 t (by simp [C9, hS, h2]) e he hmem
      · simp at ht
    rw [excl_run_eq _ _ _ (by rw [prog8Pre_perm_run]; exact hgood), prog8Pre_perm_run, map_pure] at hrec
    simp only [Notions.SMTCRExcl_oracles, unifFwd, ExclOracleSpec, prob, probExcl] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    have hsf : ∀ e ∈ Q9 pr (BMsg pr Msg) d pk, Scheme.IsStateful e.1 := fun e he => by
      rcases mem_Q9 pr he with ⟨id, -, h⟩ | ⟨id, -, h⟩ <;> (rw [h]; exact SfAdrs.isStateful_toAdrs _)
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_excl pr (L + (L - 1)) pk uSl
      (Q9 pr (BMsg pr Msg) d pk) (C8Pre pr d.S d.ys pk) hsf
    simp only [Notions.SMTCRExcl_oracles, probExcl] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind]
    have hst := stageHybPre_AFTable_eq_AFEager pr Msg enc A uSl
      (buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)) d pk
    exact Hyb.evalDistEq_of_eq (by dsimp only [B8Pre, stage2RunWithTrace, prob, probExcl]; rw [hst]; rfl)
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.SMTCRExcl_Experiment
          (B8Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
          let Q := Q9 pr (BMsg pr Msg) d pk
          let out ← (B8Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
            (d, tblSf, Q) pk
          return Notions.SMTCRExcl_IsCollision prob pk Q out) := by
    refine (EvalDistEq.bind_right _ fun uSl =>
      B8Pre_exp_eq pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).trans ?_
    change (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
               let pk ← $ᵗ pr.PkSeed
               let d ← g₁
               let tblSf := buildSfTable0Det pr pk d.S (digOf pr d.ys) (skOf pr d.S d.u)
               let Q := Q9 pr (BMsg pr Msg) d pk
               let out ← (B8Pre pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl)).forge
                 (d, tblSf, Q) pk
               return Notions.SMTCRExcl_IsCollision prob pk Q out) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

/-! ### `claim_4_15_precomp` and `theorem_4_1_full_precomp` -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] in
/-- **Claim 4.15 (Stage-1-full-precomputing `B2SPre … B8SPre`)**: bounds stateful-branch wins in
`GAME.4` (`gameHybS`) by the seven Stage-1-full-precomputing augmented reductions
`B2SPre … B8SPre`, each of which satisfies `Stage2ThBound ... (ξ + Vsf vp.params)`. -/
theorem claim_4_15_precomp (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] ≤
      Notions.STCR_Succ (B2SPre pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3SPre pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4SPre pr Msg enc A) +
      SM_DT_PRE_Advantage (B5SPre pr Msg enc A) +
      SM_DT_TCR_Advantage (B6SPre pr Msg enc A) +
      SM_DT_TCR_Advantage (B7SPre pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8SPre pr Msg enc A) := by
  have hmap : Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[
      HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] ≤
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
        WinNotC1 (o.map Prod.fst)] := by
    change _ ≤ Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AFAdv pr Msg enc A.toShrincsAdversary)}[
      WinNotC1 (o.map Prod.fst)]
    rw [← gameHybS_map pr Msg enc A.toShrincsAdversary, prEvent_map]
    refine prEvent_mono _ _ _ fun o h => ?_
    rcases o with _ | ⟨⟨tr, extra⟩, H⟩
    · exact h.elim
    · exact ⟨⟨h.1.2.2.2.1, h.1.2.2.2.2⟩, h.2⟩
  refine hmap.trans ?_
  have hhyb_ev : ∀ (γ : ℕ) (E : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → Prop),
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary}[
        HybEventValid pr (BMsg pr Msg) E o] =
      Pr{let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
         let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ
           (AFEager pr Msg enc A uSl).toFxmssAdversary}[HybEventValid pr (BMsg pr Msg) E o] := by
    intro γ E
    have heq := (gameHyb_AFEager_evalDistEq_gameHyb_AF pr Msg enc A γ).symm
    have h1 : (fun o => decide (HybEventValid pr (BMsg pr Msg) E o)) <$>
        gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary =ᵈ
        (fun o => decide (HybEventValid pr (BMsg pr Msg) E o)) <$>
        ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
          gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl).toFxmssAdversary) :=
      heq.map _
    have hrhs : Pr{let uSl ← $ᵗ (SlSecAdrs vp → pr.Y); let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl).toFxmssAdversary}[
          HybEventValid pr (BMsg pr Msg) E o] =
        Pr{let o ← ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
          gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl).toFxmssAdversary)}[
          HybEventValid pr (BMsg pr Msg) E o] := by
      simp [map_bind]
    rw [prEvent_eq_evalDist_decide, hrhs, prEvent_eq_evalDist_decide]
    simpa [map_eq_bind_pure_comp, bind_assoc] using congrArg (fun μ => μ {true}) h1.evalDist_eq
  have hprob_bind : ∀ (F : (SlSecAdrs vp → pr.Y) → ProbComp Bool)
      (G : (SlSecAdrs vp → pr.Y) → ProbComp (Option (Transcript pr (BMsg pr Msg) × Honest pr)))
      (E : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → Prop),
      (∀ uSl, Pr{let o ← G uSl}[HybEventValid pr (BMsg pr Msg) E o] ≤ 𝒟[F uSl] {true}) →
      Pr{let uSl ← $ᵗ (SlSecAdrs vp → pr.Y); let o ← G uSl}[HybEventValid pr (BMsg pr Msg) E o] ≤
        𝒟[$ᵗ (SlSecAdrs vp → pr.Y) >>= F] {true} := by
    intro F G E hle
    rw [← prEvent_eq_evalDist_singleton]
    simp only [map_bind]
    refine prEvent_bind_mono' _ _ _ fun uSl _ => ?_
    rw [prEvent_eq_evalDist_singleton]
    exact hle uSl
  have h2 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E3 o] ≤ Notions.STCR_Succ (B2SPre pr Msg enc A) := by
    rw [hhyb_ev 0 Honest.E3, Notions.STCR_Succ, (B2SPre_exp_eq pr Msg enc hgc A).evalDist_eq]
    exact hprob_bind _ _ _ fun uSl => claim_4_3_pre pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc
      (AFEager pr Msg enc A uSl)
  have h3 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E6 o] ≤
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) (vp.params.w - 2)
          (AF pr Msg enc A).toFxmssAdversary}[HybEventValid pr (BMsg pr Msg) Honest.E6 o] +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3SPre pr Msg enc γ A) := by
    refine Hyb.telescope
      (fun γ => Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary}[
        HybEventValid pr (BMsg pr Msg) Honest.E6 o])
      (fun γ => SM_DT_UD_Advantage (B3SPre pr Msg enc γ A)) (fun γ => ?_) (vp.params.w - 2)
    have hreal : SM_DT_UD_Experiment .real (B3SPre pr Msg enc γ A) =ᵈ
        (fun o => decide (HybEventValid pr (BMsg pr Msg) Honest.E6 o)) <$>
          gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary := by
      refine (B3SPre_exp_eq pr Msg enc hgc .real γ A).trans ?_
      refine (EvalDistEq.bind_right _ fun uSl =>
        B3Pre_real_eq pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc γ
          (AFEager pr Msg enc A uSl)).trans ?_
      rw [← map_bind]
      exact (gameHyb_AFEager_evalDistEq_gameHyb_AF pr Msg enc A γ).map _
    have hideal : SM_DT_UD_Experiment .ideal (B3SPre pr Msg enc γ A) =ᵈ
        (fun o => decide (HybEventValid pr (BMsg pr Msg) Honest.E6 o)) <$>
          gameHyb pr (BMsg pr Msg) (slKeygenS pr) (γ + 1) (AF pr Msg enc A).toFxmssAdversary := by
      refine (B3SPre_exp_eq pr Msg enc hgc .ideal γ A).trans ?_
      refine (EvalDistEq.bind_right _ fun uSl =>
        B3Pre_ideal_eq pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc γ
          (AFEager pr Msg enc A uSl)).trans ?_
      rw [← map_bind]
      exact (gameHyb_AFEager_evalDistEq_gameHyb_AF pr Msg enc A (γ + 1)).map _
    have hpr : ∀ k, Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) k (AF pr Msg enc A).toFxmssAdversary}[
        HybEventValid pr (BMsg pr Msg) Honest.E6 o] =
        𝒟[(fun o => decide (HybEventValid pr (BMsg pr Msg) Honest.E6 o)) <$>
          gameHyb pr (BMsg pr Msg) (slKeygenS pr) k (AF pr Msg enc A).toFxmssAdversary] {true} :=
      fun k => by rw [prEvent_eq_evalDist_decide, map_eq_bind_pure_comp]; rfl
    rw [hpr γ, hpr (γ + 1), SM_DT_UD_Advantage, MeasureTheory.Measure.boolDist,
      hreal.evalDist_eq, hideal.evalDist_eq]
    exact (ENNReal.absDiff_le_iff.1 le_rfl).1
  have h4 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E5 o] ≤ SM_DT_TCR_Advantage (B4SPre pr Msg enc A) := by
    rw [hhyb_ev 0 Honest.E5, SM_DT_TCR_Advantage, (B4SPre_exp_eq pr Msg enc A).evalDist_eq]
    exact hprob_bind _ _ _ fun uSl => claim_4_5_pre pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc
      (AFEager pr Msg enc A uSl)
  have h5 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) (vp.params.w - 2) (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E6 o] ≤
      SM_DT_PRE_Advantage (B5SPre pr Msg enc A) := by
    rw [hhyb_ev (vp.params.w - 2) Honest.E6, SM_DT_PRE_Advantage,
      (B5SPre_exp_eq pr Msg enc A).evalDist_eq]
    exact hprob_bind _ _ _ fun uSl => claim_4_6_pre pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc
      (AFEager pr Msg enc A uSl)
  have h6 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E7 o] ≤ SM_DT_TCR_Advantage (B6SPre pr Msg enc A) := by
    rw [hhyb_ev 0 Honest.E7, SM_DT_TCR_Advantage, (B6SPre_exp_eq pr Msg enc A).evalDist_eq]
    exact hprob_bind _ _ _ fun uSl => claim_4_7_pre pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc
      (AFEager pr Msg enc A uSl)
  have h7 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E8 o] ≤ SM_DT_TCR_Advantage (B7SPre pr Msg enc A) := by
    rw [hhyb_ev 0 Honest.E8, SM_DT_TCR_Advantage, (B7SPre_exp_eq pr Msg enc A).evalDist_eq]
    exact hprob_bind _ _ _ fun uSl => claim_4_8_pre pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc
      (AFEager pr Msg enc A uSl)
  have h8 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
      HybEventValid pr (BMsg pr Msg) Honest.E9 o] ≤ Notions.SMTCRExcl_Succ (B8SPre pr Msg enc A) := by
    rw [hhyb_ev 0 Honest.E9, Notions.SMTCRExcl_Succ, (B8SPre_exp_eq pr Msg enc A).evalDist_eq]
    exact hprob_bind _ _ _ fun uSl => claim_4_9_pre pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc
      (AFEager pr Msg enc A uSl)
  exact Claim415.telescope
    (gameHyb_winNotC1_le_valid pr (BMsg pr Msg) (slKeygenS pr) vp.valid hinj hgc 0
      (AF pr Msg enc A).toFxmssAdversary) h2 h3 h4 h5 h6 h7 h8

/-- **Theorem 4.1 (complete 21-term SHRINCS EU-CMA bound with Stage-1-full-precomputing
reductions on BOTH branches)**: combines Claim 4.11–4.14, `claim_4_15_precomp` (`B2SPre … B8SPre`,
each bounded by `ξ + Vsf = ξ + 497` via `theorem_4_1_stateful_stage2Bounds`), and `claim_4_16`
(all 9 stateless collection reductions, each bounded by `ξ + Vsl = ξ + 2741` via
`theorem_4_1_stateless_stage2Bounds`). -/
theorem theorem_4_1_full_precomp (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Shrincs.Forger pr Msg enc qs qh₁ qh₂ L) :
    Shrincs.succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) +
      Notions.STCR_Succ (B2SPre pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3SPre pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4SPre pr Msg enc A) +
      SM_DT_PRE_Advantage (B5SPre pr Msg enc A) +
      SM_DT_TCR_Advantage (B6SPre pr Msg enc A) +
      SM_DT_TCR_Advantage (B7SPre pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8SPre pr Msg enc A) +
      (Notions.itsrSucc (Slhdsa.slHmsg pr) (Slhdsa.slMap vp)
          (Slhdsa.B_itsr pr (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        ∑ γ ∈ Finset.range (vp.params.w - 2),
          SM_DT_UD_Advantage (Slhdsa.B_ud pr
            (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) γ) +
        SM_DT_PRE_Advantage (Slhdsa.B_pre pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrF_wots pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_xmss pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThK pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThLsl pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        3 * SM_DT_TCR_Advantage (Slhdsa.B_tcrF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_DSPR_Advantage (Slhdsa.B_dsprF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) := by
  rw [prfAdv_BprfAdv, show Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
      (BprfmsgAdv pr Msg enc A.toShrincsAdversary) =
    (Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage
      (Bprfmsg pr Msg enc A.toShrincsAdversary) from rfl]
  set A' := A.toShrincsAdversary
  have h0 := succ_eq_game0 pr Msg enc A'
  have h1 := claim_4_11 pr Msg enc A'
  have h2 := claim_4_12 pr Msg enc A'
  have h3 := game2_eq_gameS pr Msg enc A'
  have h4 := prEvent_winS_le pr Msg enc A'
  have h5 := claim_4_13 pr Msg enc A
  have h6 := claim_4_14 pr Msg enc A
  have h7 := prEvent_winNotC1S_le pr Msg enc A'
  have h8 := claim_4_15_precomp pr Msg enc hinj hgc A
  have h9 := claim_4_16 pr Msg enc hinj henc A'
  rw [h0]
  refine h1.trans ?_
  calc _ ≤ (Pr{let o ← gameS pr Msg enc A' (implG pr (BMsg pr Msg))}[
          OEv (fun p => Wsf p ∧ p.1.C1) o] +
        (Pr{let o ← gameHybS pr Msg enc A'}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] +
          Pr{let o ← gameHybS pr Msg enc A'}[HEv Wsl o] +
          ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A))) +
        (Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage (Bprfmsg pr Msg enc A')) +
        (Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A') := by
        gcongr
        refine h2.trans ?_
        gcongr
        rw [h3]
        refine h4.trans ?_
        gcongr
        refine h6.trans ?_
        gcongr
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add h5 (add_le_add (add_le_add h8 h9)
          (le_refl (ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A))))))
          (le_refl ((Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage (Bprfmsg pr Msg enc A'))))
          (le_refl ((Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A')))
        refine this.trans (le_of_eq ?_)
        ring

end Theorem41Precomp

end ShrincsSecurity.Complexity

end
