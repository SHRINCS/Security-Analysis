module

public import ShrincsSecurity.Fxmss.Members
public import ShrincsSecurity.Fxmss.Lift
public import ShrincsSecurity.Repro.Lazy
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Common machinery of Claims 4.4 and 4.6

`SHRINCS-Security-Analysis.pdf`, Section 4.7, the hop `F.3 → F.4` (txt lines ~3460–3580,
Fig. 3, Algorithm 7) and Claim 4.6 (Algorithm 9). All declarations live in the helper namespace
`ShrincsSecurity.Fxmss.Rom.Hyb`; only `B3`, `claim_4_4`, `B5`, `claim_4_6` are in `Rom`.

The reductions `B₃,γ` (SM-UD of `F ∈ Th_λ`) and `B₅` (SM-PRE of `F ∈ Th_λ`) share their first
stage: sample the setup of the block games (`setupHyb`: `A₁`, the digests `y_j`, the uniform
table `u`), grind every anchor's digest through the collection oracle (member `H_grind` at
`ADRS^g_j`, counters `0, 1, …` until the target sum: this is `WotsC.grind`), and query the
challenge oracle at one `SF_WOTS_C_HASH` address per selected anchor/chain, writing the answers
into `u`. The selection `sel a` (from the honest digit `a`) gives the hash address of the query:
`γ` when `a − 1 > γ` for `B₃,γ`, `a − 1` when `a > 0` for `B₅`.

* `runRef` / `fillWith`: the challenge phase as a sampling program (one fresh `x` per target,
  answer `ans t x` written at the target's position). `run_pickProg` proves that the first stage
  run against any game whose collection oracle answers grinding tweaks and whose challenge
  oracle answers fresh tweaks by `ans t x`, `x ←$`, is this program (the tweaks are distinct,
  never grinding tweaks, and at most the cap `L · lsf` many).
* `fillWith_couple` (pointwise coupling of two fillings with the same samples) and
  `fillWith_resample` (overwriting cells of a uniform table with fresh uniform values leaves it
  uniform, `Repro.resample` iterated).
* `stageHyb_event_congr`: the event `E6` of a block game depends on the block source only at
  the anchors' honest digits.
* `udExp_evalDistEq`, `preExp_evalDistEq`: the SM-UD and SM-PRE experiments of the shared
  first stage, as the setup followed by the sampling program.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom.Hyb

open Scheme Notions
open ShrincsSecurity.Scheme.Structure (leafIds)

/-! ## The challenge phase as a sampling program -/

section Fill

variable {D T R Q : Type} [DecidableEq D] [SampleableType R]

/-- The challenge phase as a sampling program: for each target `(p, t)` a fresh `x ←$ R`; the
answer `ans t x` is written at position `p` and the record `rec t x` is appended. -/
noncomputable def runRef (ans : T → R → R) (rec : T → R → Q) :
    List (D × T) → (D → R) → List Q → ProbComp ((D → R) × List Q)
  | [], u, qs => pure (u, qs)
  | (p, t) :: ts, u, qs => do
    let x ← $ᵗ R
    runRef ans rec ts (Function.update u p (ans t x)) (qs ++ [rec t x])

/-- `runRef` without the record. -/
noncomputable def fillWith (ans : T → R → R) : List (D × T) → (D → R) → ProbComp (D → R)
  | [], u => pure u
  | (p, t) :: ts, u => do
    let x ← $ᵗ R
    fillWith ans ts (Function.update u p (ans t x))

theorem map_fst_runRef (ans : T → R → R) (rec : T → R → Q) :
    ∀ (l : List (D × T)) (u : D → R) (qs : List Q),
      Prod.fst <$> runRef ans rec l u qs = fillWith ans l u
  | [], u, qs => by simp [runRef, fillWith]
  | (p, t) :: ts, u, qs => by
    simp only [runRef, fillWith, map_bind]
    exact bind_congr fun x => map_fst_runRef ans rec ts _ _

/-- **Pointwise coupling.** Two fillings with the same samples, whose views agree at every
written cell and, before filling, at every cell not written, give the same continuation. -/
theorem fillWith_couple {R' α : Type} (ans₁ ans₂ : T → R → R) (v₁ v₂ : D → R → R')
    (G : (D → R') → ProbComp α) :
    ∀ (l : List (D × T)), (∀ pt ∈ l, ∀ x, v₁ pt.1 (ans₁ pt.2 x) = v₂ pt.1 (ans₂ pt.2 x)) →
      ∀ u₁ u₂ : D → R, (∀ q, q ∉ l.map Prod.fst → v₁ q (u₁ q) = v₂ q (u₂ q)) →
      (fillWith ans₁ l u₁ >>= fun u => G fun q => v₁ q (u q)) =
        (fillWith ans₂ l u₂ >>= fun u => G fun q => v₂ q (u q))
  | [], _, u₁, u₂, h => by
    simp only [fillWith, pure_bind]
    congr 1
    funext q
    exact h q (by simp)
  | (p, t) :: ts, hl, u₁, u₂, h => by
    simp only [fillWith, bind_assoc]
    refine bind_congr fun x => ?_
    refine fillWith_couple ans₁ ans₂ v₁ v₂ G ts (fun pt hpt => hl pt (by simp [hpt])) _ _ ?_
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      simpa using hl (q, t) (by simp) x
    · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
      exact h q (by simp [hqp, hq])

/-- **Iterated uniform resampling.** Overwriting cells of a uniform table with fresh uniform
values (`Repro.resample`, once per target) leaves the table uniform. -/
theorem fillWith_resample [Fintype D] {β : Type} :
    ∀ (l : List (D × T)) (f : (D → R) → ProbComp β),
      ($ᵗ (D → R) >>= fun u => fillWith (fun _ x => x) l u >>= f) =ᵈ ($ᵗ (D → R) >>= f)
  | [], f => by simp only [fillWith, pure_bind]; exact EvalDistEq.refl _
  | (p, t) :: ts, f => by
    simp only [fillWith, bind_assoc]
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine (Repro.resample p fun g => fillWith (fun _ x => x) ts g >>= f).trans ?_
    exact fillWith_resample ts f


/-- **The sampled record.** Along a run of `runRef` (distinct positions), the `i`-th target's
position holds `ans t x` and the record holds `rec t x` at index `i` (after the initial record),
for the same sample `x`; positions not targeted and the initial record are unchanged. -/
theorem runRef_spec (ans : T → R → R) (rec : T → R → Q) :
    ∀ (l : List (D × T)) (u : D → R) (qs : List Q) (z : (D → R) × List Q),
      z ∈ support (runRef ans rec l u qs) → (l.map Prod.fst).Nodup →
      (∀ q, q ∉ l.map Prod.fst → z.1 q = u q) ∧ (∀ i < qs.length, z.2[i]? = qs[i]?) ∧
        ∀ (i : ℕ) (hi : i < l.length), ∃ x, z.1 l[i].1 = ans l[i].2 x ∧
          z.2[qs.length + i]? = some (rec l[i].2 x)
  | [], u, qs, z, hz, _ => by
    simp only [runRef, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | (p, t) :: ts, u, qs, z, hz, hnd => by
    simp only [runRef, mem_support_bind_iff] at hz
    obtain ⟨x, -, hz⟩ := hz
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨h1, h2, h3⟩ := runRef_spec ans rec ts _ _ z hz hnd.2
    refine ⟨fun q hq => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hq
      rw [h1 q hq.2, Function.update_of_ne hq.1]
    · rw [h2 i (by simp; omega), List.getElem?_append_left hi]
    · rcases i with _ | i
      · refine ⟨x, ?_, ?_⟩
        · simp only [List.getElem_cons_zero]
          rw [h1 _ hnd.1, Function.update_self]
        · rw [Nat.add_zero, h2 _ (by simp)]
          simp
      · obtain ⟨y, hy1, hy2⟩ := h3 i (by simpa using hi)
        refine ⟨y, by simpa using hy1, ?_⟩
        rw [List.length_append, List.length_singleton] at hy2
        simp only [List.getElem_cons_succ]
        rw [← hy2]
        congr 1
        omega

end Fill

/-! ## The shared first stage -/

section FirstStage

variable {P : Params} (pr : Primitives P) [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [Inhabited pr.Y] [Inhabited pr.Digest]

/-- The collection `F ∈ Th_λ` of Claims 4.4–4.6. -/
noncomputable abbrev collF := TweakableHashCollection.cons (thF pr) pr.collection

/-- The first-stage oracles of `B₃,γ` and `B₅`: private coins, the challenge oracle (a tweak, an
optional image) and the collection oracle of `F ∈ Th_λ`. -/
noncomputable abbrev FSpec :=
  unifSpec + ((SLHDSA.Adrs →ₒ Option pr.Y) + collectionSpec (collF pr))

/-- A collection query `H_grind(ADRS^g_id, md, c)`. -/
noncomputable def grindQuery (id : LeafId) (md : pr.Digest) (c : Fin (2 ^ P.c)) :
    OracleComp (FSpec pr) (Option pr.Y) :=
  (FSpec pr).query (.inr (.inr ⟨some .grind, (SfAdrs.grindAdrs id).toAdrs, (md, c)⟩))

/-- The counter search of WOTS+C through the collection oracle: the first counter of the list
whose encoded digest meets the target sum. -/
noncomputable def grindSearch (id : LeafId) (md : pr.Digest) :
    List (Fin (2 ^ P.c)) → OracleComp (FSpec pr) (Option (pr.Y × Fin (2 ^ P.c)))
  | [] => pure none
  | c :: cs => do
    let r ← grindQuery pr id md c
    if WotsC.TargetSum pr (r.getD default) then pure (some (r.getD default, c))
    else grindSearch id md cs

/-- The value of `grindSearch` when every collection query is answered. -/
def grindPure (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) :
    List (Fin (2 ^ P.c)) → Option (pr.Y × Fin (2 ^ P.c))
  | [] => none
  | c :: cs => if WotsC.TargetSum pr (WotsC.encode pr pk id md c) then
      some (WotsC.encode pr pk id md c, c) else grindPure pk id md cs

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
theorem grindPure_eq_find (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) :
    ∀ cs : List (Fin (2 ^ P.c)), grindPure pr pk id md cs =
      (cs.find? fun c => decide (WotsC.TargetSum pr (WotsC.encode pr pk id md c))).map
        fun c => (WotsC.encode pr pk id md c, c)
  | [] => rfl
  | c :: cs => by
    simp only [grindPure, List.find?_cons]
    split_ifs with h <;> simp [h, grindPure_eq_find pk id md cs]

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
/-- Searching all counters in order is `WotsC.grind`. -/
theorem grindPure_finRange (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) :
    grindPure pr pk id md (List.finRange (2 ^ P.c)) = WotsC.grind pr pk id md := by
  rw [grindPure_eq_find]
  cases h : (List.finRange (2 ^ P.c)).find?
      (fun c => decide (WotsC.TargetSum pr (WotsC.encode pr pk id md c))) with
  | none =>
    rw [List.find?_eq_none] at h
    symm
    rw [Option.map_none, WotsC.grind_eq_none_iff]
    intro c hc
    exact absurd (decide_eq_true hc) (h c (List.mem_finRange c))
  | some c =>
    rw [List.find?_eq_some_iff_getElem] at h
    obtain ⟨hc, i, hi, hci, hmin⟩ := h
    symm
    rw [Option.map_some, WotsC.grind_eq_some_iff]
    refine ⟨rfl, of_decide_eq_true hc, fun c' hc' hT => ?_⟩
    have hi' : i = c.val := by rw [← hci, List.getElem_finRange]; rfl
    have h' := hmin c'.val (by rw [hi']; exact hc')
    rw [List.getElem_finRange] at h'
    simp only [Fin.cast_mk, Fin.eta, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at h'
    exact h' hT

/-- Grind every listed anchor, collecting the results in a table. -/
noncomputable def grindAll {S : Structure} (ys : Anchor P S → pr.Digest) :
    List (Anchor P S) → OracleComp (FSpec pr) (Anchor P S → Option (pr.Y × Fin (2 ^ P.c)))
  | [] => pure fun _ => none
  | a :: as => do
    let g ← grindSearch pr a.1 (digOf pr ys a.1) (List.finRange (2 ^ P.c))
    let f ← grindAll ys as
    pure (Function.update f a g)

/-- The honest digit of chain `ch` for a grinding result (`0` when grinding failed). -/
def relDigOf (g : Option (pr.Y × Fin (2 ^ P.c))) (ch : ℕ) : ℕ :=
  match g with
  | some (d, _) => WotsC.digit pr d ch
  | none => 0

/-- The honest digit of chain `ch` at `id` for `PK.seed` and the digests `dig`. -/
def relDig (pk : pr.PkSeed) (dig : LeafId → pr.Digest) (id : LeafId) (ch : ℕ) : ℕ :=
  relDigOf pr (WotsC.grind pr pk id (dig id)) ch

/-- The anchors of a structure as a list. -/
noncomputable def anchorsL (S : Structure) : List (Anchor P S) :=
  (Finset.univ : Finset (Anchor P S)).toList

/-- The challenge targets for grinding results `gf` and a selection `sel`: every anchor and chain
whose honest digit `a` is selected (`sel a = some j`), at the hash address `j`. -/
noncomputable def targetsOf (sel : ℕ → Option ℕ) {S : Structure}
    (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c))) : List (SkIdx P S × SLHDSA.Adrs) :=
  (anchorsL S ×ˢ List.finRange P.lsf).filterMap fun ac =>
    (sel (relDigOf pr (gf ac.1) ac.2.val)).map fun j =>
      ((ac.1, ac.2), (SfAdrs.chainAdrs ac.1.1 ac.2.val j).toAdrs)

/-- Query the challenge oracle at every target, writing the answers into the table. -/
noncomputable def queryAll {D : Type} [DecidableEq D] :
    List (D × SLHDSA.Adrs) → (D → pr.Y) → OracleComp (FSpec pr) (D → pr.Y)
  | [], u => pure u
  | (p, t) :: ts, u => do
    let r ← ((FSpec pr).query (.inr (.inl t)) : OracleComp (FSpec pr) (Option pr.Y))
    queryAll ts (Function.update u p (r.getD default))

/-- **The challenge part of the shared first stage**: for a valid structure, grind every anchor
through the collection oracle, then query the challenge oracle at the selected targets. -/
noncomputable def pickProg (sel : ℕ → Option ℕ) {S : Structure} (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : OracleComp (FSpec pr) (SkIdx P S → pr.Y) :=
  if S.TreeValid P.hsf then do
    let gf ← grindAll pr ys (anchorsL S)
    queryAll pr (targetsOf pr sel gf) u
  else pure u

/-- The targets of `pickProg` for `PK.seed = pk`. -/
noncomputable def targets (pk : pr.PkSeed) (sel : ℕ → Option ℕ) (S : Structure)
    (ys : Anchor P S → pr.Digest) : List (SkIdx P S × SLHDSA.Adrs) :=
  if S.TreeValid P.hsf then
    targetsOf pr sel fun a => WotsC.grind pr pk a.1 (digOf pr ys a.1)
  else []

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
theorem mem_targetsOf {sel : ℕ → Option ℕ} {S : Structure}
    {gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c))} {p : SkIdx P S} {t : SLHDSA.Adrs} :
    (p, t) ∈ targetsOf pr sel gf ↔
      ∃ j, sel (relDigOf pr (gf p.1) p.2.val) = some j ∧
        t = (SfAdrs.chainAdrs p.1.1 p.2.val j).toAdrs := by
  simp only [targetsOf, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, c⟩, -, j, hj, rfl, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨p, List.mem_product.2 ⟨Finset.mem_toList.2 (Finset.mem_univ _), List.mem_finRange _⟩,
      j, hj, rfl, rfl⟩

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
theorem mem_map_fst_targetsOf {sel : ℕ → Option ℕ} {S : Structure}
    {gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c))} {p : SkIdx P S} :
    p ∈ (targetsOf pr sel gf).map Prod.fst ↔ (sel (relDigOf pr (gf p.1) p.2.val)).isSome := by
  simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨j, hj, -⟩ := (mem_targetsOf pr).1 ht
    simp [hj]
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h
    exact ⟨_, (mem_targetsOf pr).2 ⟨j, hj, rfl⟩⟩

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
theorem nodup_map_fst_targetsOf (sel : ℕ → Option ℕ) {S : Structure}
    (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c))) :
    ((targetsOf pr sel gf).map Prod.fst).Nodup := by
  refine List.Nodup.map_on ?_ ?_
  · rintro ⟨p, t⟩ hx ⟨p', t'⟩ hy (rfl : p = p')
    obtain ⟨j, hj, rfl⟩ := (mem_targetsOf pr).1 hx
    obtain ⟨j', hj', rfl⟩ := (mem_targetsOf pr).1 hy
    rw [hj] at hj'
    cases hj'
    rfl
  · refine List.Nodup.filterMap ?_ ((Finset.nodup_toList _).product (List.nodup_finRange _))
    rintro ⟨a, c⟩ ⟨a', c'⟩ b hb hb'
    simp only [Option.mem_def, Option.map_eq_some_iff] at hb hb'
    obtain ⟨j, -, rfl⟩ := hb
    obtain ⟨j', -, h⟩ := hb'
    simp only [Prod.mk.injEq] at h
    rw [h.1.1, h.1.2]

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
theorem nodup_map_snd_targetsOf (sel : ℕ → Option ℕ) {S : Structure}
    (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c))) :
    ((targetsOf pr sel gf).map Prod.snd).Nodup := by
  refine List.Nodup.map_on ?_ (List.Nodup.of_map _ (nodup_map_fst_targetsOf pr sel gf))
  rintro ⟨p, t⟩ hx ⟨p', t'⟩ hy (rfl : t = t')
  obtain ⟨j, hj, rfl⟩ := (mem_targetsOf pr).1 hx
  obtain ⟨j', hj', h⟩ := (mem_targetsOf pr).1 hy
  obtain ⟨h1, h2, -⟩ := SfAdrs.chainAdrs_inj.1 h
  have : p = p' := Prod.ext (Subtype.ext h1) (Fin.ext h2)
  subst this
  rfl

omit [SampleableType pr.PkSeed] [SampleableType pr.Y] [Inhabited pr.Y] [Inhabited pr.Digest] in
theorem length_targetsOf_le (sel : ℕ → Option ℕ) {S : Structure}
    (gf : Anchor P S → Option (pr.Y × Fin (2 ^ P.c))) :
    (targetsOf pr sel gf).length ≤ S.anchors.card * P.lsf := by
  refine (List.length_filterMap_le _ _).trans ?_
  rw [List.length_product, List.length_finRange, anchorsL, Finset.length_toList,
    Finset.card_univ, Fintype.card_coe]
  exact Nat.mul_le_mul_right _ Finset.card_image_le

end FirstStage

/-! ## Running the shared first stage -/

section Run

variable {P : Params} (pr : Primitives P) [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [Inhabited pr.Y] [Inhabited pr.Digest]
  {Q : Type} (tweakOf : Q → SLHDSA.Adrs) (N : ℕ) (pk : pr.PkSeed)
  (ans : SLHDSA.Adrs → pr.Y → pr.Y) (rec : SLHDSA.Adrs → pr.Y → Q)
  (impl : QueryImpl (FSpec pr) (StateT (List Q × List SLHDSA.Adrs) ProbComp))

/-- Every collection tweak is a grinding tweak. -/
def GrindOnly (tws : List SLHDSA.Adrs) : Prop :=
  ∀ t ∈ tws, ∃ id, t = (SfAdrs.grindAdrs id).toAdrs

/-- The game's collection oracle answers every query at a tweak the challenge oracle has not
reserved, appending the tweak (VCVio's `collectionOracle`). -/
def CollAnswers : Prop :=
  ∀ (q : (collectionSpec (collF pr)).Domain) (qs : List Q) (tws : List SLHDSA.Adrs),
    ¬ TweakReserved tweakOf qs q.2.1 →
      (impl (.inr (.inr q))).run (qs, tws) =
        pure (some ((collF pr).eval q.1 pk q.2.1 q.2.2), (qs, tws ++ [q.2.1]))

/-- The game's challenge oracle answers a fresh tweak below the cap `N` by `ans t x` for a fresh
uniform `x`, recording `rec t x`. -/
def ChalAnswers : Prop :=
  ∀ (t : SLHDSA.Adrs) (qs : List Q) (tws : List SLHDSA.Adrs), qs.length < N →
    TweakFresh tweakOf qs tws t →
      (impl (.inr (.inl t))).run (qs, tws) =
        (fun x => (some (ans t x), (qs ++ [rec t x], tws))) <$> ($ᵗ pr.Y)

variable {pr tweakOf N pk ans rec impl}

omit [SampleableType pr.Y] [Inhabited pr.Digest] in
theorem run_grindSearch (hcoll : CollAnswers pr tweakOf pk impl) (id : LeafId) (md : pr.Digest) :
    ∀ (cs : List (Fin (2 ^ P.c))) (tws : List SLHDSA.Adrs), GrindOnly tws →
      ∃ tws', GrindOnly tws' ∧ (simulateQ impl (grindSearch pr id md cs)).run ([], tws) =
        pure (grindPure pr pk id md cs, ([], tws'))
  | [], tws, h => ⟨tws, h, by simp [grindSearch, grindPure]⟩
  | c :: cs, tws, h => by
    have hg : GrindOnly (tws ++ [(SfAdrs.grindAdrs id).toAdrs]) := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact h t ht
      · exact ⟨id, List.mem_singleton.1 ht⟩
    simp only [grindSearch, grindQuery]
    rw [run_simulateQ_query_bind, hcoll _ [] tws (by simp [TweakReserved]), pure_bind]
    by_cases hT : WotsC.TargetSum pr (WotsC.encode pr pk id md c)
    · refine ⟨_, hg, ?_⟩
      have hT' : WotsC.TargetSum pr ((some ((collF pr).eval (some .grind) pk
          (SfAdrs.grindAdrs id).toAdrs (md, c))).getD default) := hT
      simp only [hT', ite_true, simulateQ_pure, StateT.run_pure, grindPure, hT]
      rfl
    · have hT' : ¬ WotsC.TargetSum pr ((some ((collF pr).eval (some .grind) pk
          (SfAdrs.grindAdrs id).toAdrs (md, c))).getD default) := hT
      obtain ⟨tws', h', hrun⟩ := run_grindSearch hcoll id md cs _ hg
      refine ⟨tws', h', ?_⟩
      simp only [hT', ite_false, hrun, grindPure, hT]

omit [SampleableType pr.Y] in
theorem run_grindAll (hcoll : CollAnswers pr tweakOf pk impl) {S : Structure}
    (ys : Anchor P S → pr.Digest) :
    ∀ (as : List (Anchor P S)) (tws : List SLHDSA.Adrs), GrindOnly tws →
      ∃ tws', GrindOnly tws' ∧ (simulateQ impl (grindAll pr ys as)).run ([], tws) =
        pure ((fun a => if a ∈ as then WotsC.grind pr pk a.1 (digOf pr ys a.1) else none),
          ([], tws'))
  | [], tws, h => ⟨tws, h, by simp [grindAll]⟩
  | a :: as, tws, h => by
    obtain ⟨tws₁, h₁, hr₁⟩ := run_grindSearch hcoll a.1 (digOf pr ys a.1)
      (List.finRange (2 ^ P.c)) tws h
    obtain ⟨tws₂, h₂, hr₂⟩ := run_grindAll hcoll ys as tws₁ h₁
    refine ⟨tws₂, h₂, ?_⟩
    simp only [grindAll, simulateQ_bind, StateT.run_bind, hr₁, pure_bind, hr₂, simulateQ_pure,
      StateT.run_pure, grindPure_finRange]
    congr 3
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]

omit [Inhabited pr.Digest] in
theorem run_queryAll (hchal : ChalAnswers pr tweakOf N ans rec impl)
    (hrec : ∀ t x, tweakOf (rec t x) = t) {D : Type} [DecidableEq D] :
    ∀ (ts : List (D × SLHDSA.Adrs)) (u : D → pr.Y) (qs : List Q) (tws : List SLHDSA.Adrs),
      (ts.map Prod.snd).Nodup →
      (∀ t ∈ ts.map Prod.snd, ¬ TweakReserved tweakOf qs t ∧ t ∉ tws) →
      qs.length + ts.length ≤ N →
      (simulateQ impl (queryAll pr ts u)).run (qs, tws) =
        (fun z => (z.1, (z.2, tws))) <$> runRef ans rec ts u qs
  | [], u, qs, tws, _, _, _ => by simp [queryAll, runRef]
  | (p, t) :: ts, u, qs, tws, hnd, hfr, hlen => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ht := hfr t (by simp)
    simp only [queryAll, runRef]
    rw [run_simulateQ_query_bind, hchal t qs tws (by simp at hlen; omega) ht, bind_map_left,
      map_bind]
    refine bind_congr fun x => ?_
    rw [Option.getD_some]
    refine run_queryAll hchal hrec ts _ _ tws hnd.2 (fun t' ht' => ⟨?_, (hfr t' (by simp [ht'])).2⟩)
      (by simp at hlen ⊢; omega)
    rintro ⟨e, he, hte⟩
    rcases List.mem_append.1 he with he | he
    · exact (hfr t' (by simp [ht'])).1 ⟨e, he, hte⟩
    · rw [List.mem_singleton.1 he, hrec] at hte
      exact hnd.1 (hte ▸ ht')

/-- **The run of the shared first stage**: against a game whose collection oracle answers
(grinding tweaks are never reserved) and whose challenge oracle answers fresh tweaks below the
cap, the challenge part of the first stage is the sampling program `runRef` on the targets. -/
theorem run_pickProg (hcoll : CollAnswers pr tweakOf pk impl)
    (hchal : ChalAnswers pr tweakOf N ans rec impl) (hrec : ∀ t x, tweakOf (rec t x) = t)
    (sel : ℕ → Option ℕ) {S : Structure} (ys : Anchor P S → pr.Digest) (u : SkIdx P S → pr.Y)
    (hN : (targets pr pk sel S ys).length ≤ N) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ impl (pickProg pr sel ys u)).run ([], []) =
      runRef ans rec (targets pr pk sel S ys) u [] := by
  unfold pickProg
  by_cases hS : S.TreeValid P.hsf
  · obtain ⟨tws, htws, hr⟩ := run_grindAll hcoll ys (anchorsL S) [] (by simp [GrindOnly])
    have hgf : (fun a : Anchor P S => if a ∈ anchorsL S then
        WotsC.grind pr pk a.1 (digOf pr ys a.1) else none) =
        fun a => WotsC.grind pr pk a.1 (digOf pr ys a.1) := by
      funext a
      simp [anchorsL]
    simp only [hS, ite_true, targets] at hN ⊢
    rw [simulateQ_bind, StateT.run_bind, hr, pure_bind, hgf,
      run_queryAll hchal hrec _ _ _ _ (nodup_map_snd_targetsOf pr sel _) ?_ (by simpa using hN),
      Functor.map_map]
    · exact id_map _
    · intro t ht
      refine ⟨by simp [TweakReserved], fun htw => ?_⟩
      obtain ⟨id, rfl⟩ := htws _ htw
      obtain ⟨⟨p, t'⟩, hpt, rfl⟩ := List.mem_map.1 ht
      obtain ⟨j, -, he⟩ := (mem_targetsOf pr).1 hpt
      exact SfAdrs.chainAdrs_ne_grindAdrs _ _ _ _ he.symm
  · simp [hS, targets, runRef]

end Run

/-! ## The event `E6` reads the blocks at the honest digits only -/

section Congr

variable {P : Params}

theorem treeNode_congr {Y : Type} {hsf : ℕ} {S : Structure} {leaf₁ leaf₂ : LeafId → Y}
    (node : LeafId → Y → Y → Y) (h : ∀ id ∈ leafIds hsf S, leaf₁ id = leaf₂ id) :
    ∀ z i, Tree.treeNode hsf S leaf₁ node z i = Tree.treeNode hsf S leaf₂ node z i
  | 0, i => by
    simp only [Tree.treeNode]
    split_ifs with hA
    · rw [h _ (mem_leafIds_of (Nat.zero_le _) (by simpa [Node.ofLeafId] using hA))]
    · rfl
  | z + 1, i => by
    simp only [Tree.treeNode]
    split_ifs with hA hI
    · rw [h _ (mem_leafIds_of (id := ⟨z + 1, i⟩) hA.1 hA.2)]
    · rw [treeNode_congr node h z (2 * i), treeNode_congr node h z (2 * i + 1)]
    · rfl

theorem authPath_congr {Y : Type} {hsf : ℕ} {S : Structure} {leaf₁ leaf₂ : LeafId → Y}
    (node : LeafId → Y → Y → Y) (h : ∀ id ∈ leafIds hsf S, leaf₁ id = leaf₂ id) :
    ∀ z i s, Tree.authPath hsf S leaf₁ node z i s = Tree.authPath hsf S leaf₂ node z i s
  | _, _, 0 => rfl
  | z, i, s + 1 => by
    simp only [Tree.authPath, treeNode_congr node h, authPath_congr node h (z + 1) (i / 2) s]

variable (pr : Primitives P) [Inhabited pr.Y]

/-- Two honest data with the same structure, `PK.seed` and digests that agree at the anchors. -/
structure HonAgree (H₁ H₂ : Honest pr) : Prop where
  S : H₁.S = H₂.S
  pk : H₁.pk = H₂.pk
  dig : H₁.dig = H₂.dig
  leafVal : ∀ id ∈ leafIds P.hsf H₁.S, H₁.leafVal id = H₂.leafVal id
  wots : ∀ id ∈ leafIds P.hsf H₁.S, H₁.wots id = H₂.wots id

variable {pr}

omit [Inhabited pr.Y] in
theorem HonAgree.value {H₁ H₂ : Honest pr} (h : HonAgree pr H₁ H₂) (z i : ℕ) :
    H₁.value z i = H₂.value z i := by
  obtain ⟨S, pk, lv₁, dig, w₁⟩ := H₁
  obtain ⟨S', pk', lv₂, dig', w₂⟩ := H₂
  obtain ⟨hS, hpk, hdig, hlv, -⟩ := h
  dsimp only at hS hpk hdig hlv
  subst hS hpk hdig
  exact treeNode_congr _ hlv z i

theorem HonAgree.pkSf {H₁ H₂ : Honest pr} (h : HonAgree pr H₁ H₂) : H₁.pkSf = H₂.pkSf := by
  simp only [Honest.pkSf, h.value]

omit [Inhabited pr.Y] in
theorem HonAgree.sig {H₁ H₂ : Honest pr} (h : HonAgree pr H₁ H₂) {id : LeafId}
    (hid : id ∈ leafIds P.hsf H₁.S) : H₁.sig id = H₂.sig id := by
  obtain ⟨S, pk, lv₁, dig, w₁⟩ := H₁
  obtain ⟨S', pk', lv₂, dig', w₂⟩ := H₂
  obtain ⟨hS, hpk, hdig, hlv, hw⟩ := h
  dsimp only at hS hpk hdig hlv hw hid
  subst hS hpk hdig
  simp only [Honest.sig, authPath_congr _ hlv, hw id hid]

omit [Inhabited pr.Y] in
theorem HonAgree.E6 {H₁ H₂ : Honest pr} (h : HonAgree pr H₁ H₂) (idf : LeafId)
    (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr) : H₁.E6 idf yf w ↔ H₂.E6 idf yf w := by
  obtain ⟨S, pk, lv₁, dig, w₁⟩ := H₁
  obtain ⟨S', pk', lv₂, dig', w₂⟩ := H₂
  obtain ⟨hS, hpk, hdig, -, hw⟩ := h
  dsimp only at hS hpk hdig hw
  subst hS hpk hdig
  simp only [Honest.E6, Honest.encoded, Honest.block, Honest.fEnc, Honest.fChain]
  constructor
  · rintro ⟨hid, ch, h1, h2⟩
    rw [hw idf hid] at h1 h2
    exact ⟨hid, ch, h1, h2⟩
  · rintro ⟨hid, ch, h1, h2⟩
    rw [← hw idf hid] at h1 h2
    exact ⟨hid, ch, h1, h2⟩

omit [Inhabited pr.Y] in
/-- The honest data of a block game depends on the block source only at the anchors' honest
digits. -/
theorem hon_agree (S : Structure) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (β₁ β₂ : LeafId → ℕ → ℕ → pr.Y)
    (h : ∀ id ∈ leafIds P.hsf S, ∀ ch : Fin P.lsf,
      β₁ id ch (relDig pr pk dig id ch) = β₂ id ch (relDig pr pk dig id ch)) :
    HonAgree pr (hon pr S pk dig β₁) (hon pr S pk dig β₂) := by
  have key : ∀ id ∈ leafIds P.hsf S, (hon pr S pk dig β₁).wots id = (hon pr S pk dig β₂).wots id ∧
      (hon pr S pk dig β₁).leafVal id = (hon pr S pk dig β₂).leafVal id := by
    intro id hid
    have hβ := h id hid
    simp only [relDig] at hβ
    simp only [hon]
    cases hg : WotsC.grind pr pk id (dig id) with
    | none =>
      simp only [hg, relDigOf] at hβ
      simp only [hβ]
      exact ⟨trivial, trivial⟩
    | some dc =>
      obtain ⟨d, c⟩ := dc
      simp only [hg, relDigOf] at hβ
      have hb : blockSig pr β₁ id d c = blockSig pr β₂ id d c := by
        simp only [blockSig, hβ]
      simp only [hb]
      exact ⟨trivial, trivial⟩
  exact ⟨rfl, rfl, rfl, fun id hid => (key id hid).2, fun id hid => (key id hid).1⟩

variable (Msg : Type) [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg]

omit [Inhabited pr.Y] [DecidableEq pr.Y] [DecidableEq pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem signStep_congr (K : Keys pr)
    (dig : LeafId → RoIn pr Msg → StateT (St pr Msg) ProbComp pr.Digest)
    (sig₁ sig₂ : LeafId → pr.Digest → Option (Scheme.Fxmss.Sig pr))
    (h : ∀ id ∈ leafIds P.hsf K.S, ∀ md, sig₁ id md = sig₂ id md) :
    signStep pr Msg K dig sig₁ = signStep pr Msg K dig sig₂ := by
  funext q
  unfold signStep
  congr 1
  funext s
  split_ifs with hc
  · simp only [h q.2 hc.1]
  · rfl

omit [Inhabited pr.Y] [DecidableEq pr.Digest] in
theorem implHyb_congr (K : Keys pr) {H₁ H₂ : Honest pr} (h : HonAgree pr H₁ H₂)
    (hK : K.S = H₁.S) : implHyb pr Msg K H₁ = implHyb pr Msg K H₂ := by
  unfold implHyb impl
  have hs := signStep_congr Msg K (fun id x => progStep pr Msg x (H₁.dig id))
    (fun id _ => H₁.sig id) (fun id _ => H₂.sig id) (fun id hid _ => h.sig (hK ▸ hid))
  rw [hs, h.dig]

variable [SampleableType pr.PkSeed] [Nontrivial Msg] [Inhabited pr.Digest]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

omit [DecidableEq pr.Digest] in
/-- **The event `E6` of a block game depends on the block source only at the anchors' honest
digits.** -/
theorem stageHyb_E6_congr {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β₁ β₂ : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed)
    (h : ∀ id ∈ leafIds P.hsf d.S, ∀ ch : Fin P.lsf,
      β₁ id ch (relDig pr pk (digOf pr d.ys) id ch) =
        β₂ id ch (relDig pr pk (digOf pr d.ys) id ch)) :
    (fun o => decide (HybEvent Honest.E6 o)) <$> stageHyb pr Msg slKeygen A β₁ d pk =
      (fun o => decide (HybEvent Honest.E6 o)) <$> stageHyb pr Msg slKeygen A β₂ d pk := by
  have hA := hon_agree (pr := pr) d.S pk (digOf pr d.ys) β₁ β₂ h
  by_cases hS : d.S.TreeValid P.hsf
  · simp only [stageHyb, hS, not_true_eq_false, ite_false, map_bind]
    refine bind_congr fun pkSl => ?_
    rw [hA.pkSf, implHyb_congr Msg _ hA rfl]
    refine bind_congr fun r => ?_
    simp only [map_pure]
    congr 1
    rw [decide_eq_decide]
    simp only [HybEvent, hA.E6]
  · simp only [stageHyb, hS, not_false_eq_true, ite_true]

end Congr

theorem evalDistEq_of_eq {α : Type} {mx my : ProbComp α} (h : mx = my) : mx =ᵈ my :=
  h ▸ EvalDistEq.refl _

/-! ## The block games and the experiments of the shared first stage -/

section Games

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- The blocks of hybrid `γ` at the honest digits, from the table `u`:
`σ_{j,i} = c_{m, a − m}(u_{j,i})`, `m = min(γ, a − 1)`. -/
def viewOf (γ : ℕ) (pk : pr.PkSeed) {S : Structure} (ys : Anchor P S → pr.Digest)
    (u : SkIdx P S → pr.Y) : SkIdx P S → pr.Y := fun p =>
  blockVal pr pk p.1.1 p.2.val γ (relDig pr pk (digOf pr ys) p.1.1 p.2.val) (u p)

/-- The event `E6` of the block game whose blocks at the honest digits are the table `w`. -/
noncomputable def evE6 {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (pk : pr.PkSeed) (w : SkIdx P d.S → pr.Y) : ProbComp Bool :=
  (fun o => decide (HybEvent Honest.E6 o)) <$>
    stageHyb pr Msg slKeygen A (fun id ch _ => skOf pr d.S w id ch) d pk

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.PkSeed] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] in
theorem skOf_anchor {S : Structure} (w : SkIdx P S → pr.Y) {id : LeafId}
    (hid : id ∈ leafIds P.hsf S) (ch : Fin P.lsf) : skOf pr S w id ch = w (⟨id, hid⟩, ch) := by
  simp [skOf, hid, ch.isLt]

variable {Msg}

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
theorem evE6_of {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed)
    (w : SkIdx P d.S → pr.Y)
    (h : ∀ id (hid : id ∈ leafIds P.hsf d.S) (ch : Fin P.lsf),
      β id ch (relDig pr pk (digOf pr d.ys) id ch) = w (⟨id, hid⟩, ch)) :
    (fun o => decide (HybEvent Honest.E6 o)) <$> stageHyb pr Msg slKeygen A β d pk =
      evE6 pr Msg slKeygen A d pk w :=
  stageHyb_E6_congr Msg slKeygen A _ _ d pk fun id hid ch => by
    rw [h id hid ch, skOf_anchor pr w hid ch]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
theorem betaOf_evE6 (γ : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (pk : pr.PkSeed) (u : SkIdx P d.S → pr.Y) :
    (fun o => decide (HybEvent Honest.E6 o)) <$>
        stageHyb pr Msg slKeygen A (betaOf pr γ pk u) d pk =
      evE6 pr Msg slKeygen A d pk (viewOf pr γ pk d.ys u) :=
  evE6_of pr slKeygen A _ d pk _ fun id hid ch => by
    simp only [betaOf, viewOf, skOf_anchor pr u hid ch]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- `E6` in the hybrid `γ`, as a Boolean game over the setup. -/
theorem gameHyb_E6 (γ : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    (fun o => decide (HybEvent Honest.E6 o)) <$> gameHyb pr Msg slKeygen γ A =
      (do let pk ← $ᵗ pr.PkSeed; let d ← setupHyb pr Msg slKeygen A
          evE6 pr Msg slKeygen A d pk (viewOf pr γ pk d.ys d.u)) := by
  simp only [gameHyb, map_bind, betaOf_evE6]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
theorem evE6_invalid {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (hS : ¬ d.S.TreeValid P.hsf) (pk : pr.PkSeed)
    (w : SkIdx P d.S → pr.Y) : evE6 pr Msg slKeygen A d pk w = pure false := by
  simp only [evE6, stageHyb, hS, not_false_eq_true, ite_true, map_pure]
  exact congrArg pure (decide_eq_false (by simp [HybEvent]))

omit [Fintype pr.Y] [DecidableEq pr.Digest] [Inhabited pr.Digest] [Nontrivial Msg] in
/-- **Resampling the setup's table**: filling cells of the uniform table `u` of `setupHyb` with
fresh uniform values does not change the distribution. -/
theorem setupHyb_resample {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    {T β : Type} (l : (S : Structure) → (Anchor P S → pr.Digest) → List (SkIdx P S × T))
    (K : (d : Setup pr Msg A.State) → (SkIdx P d.S → pr.Y) → ProbComp β)
    (hK : ∀ S st c ys (u₁ u₂ : SkIdx P S → pr.Y) w,
      K ⟨S, st, c, ys, u₁⟩ w = K ⟨S, st, c, ys, u₂⟩ w) :
    (setupHyb pr Msg slKeygen A >>= fun d => fillWith (fun _ x => x) (l d.S d.ys) d.u >>= K d)
      =ᵈ (setupHyb pr Msg slKeygen A >>= fun d => K d d.u) := by
  unfold setupHyb
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun z => EvalDistEq.bind_right _ fun ys => ?_
  have e₁ : (fun u => fillWith (fun _ x => x) (l z.1.1 ys) u >>=
      K ⟨z.1.1, z.1.2, z.2, ys, u⟩) = fun u => fillWith (fun _ x => x) (l z.1.1 ys) u >>=
      K ⟨z.1.1, z.1.2, z.2, ys, fun _ => default⟩ := by
    funext u
    exact bind_congr fun w => hK _ _ _ _ _ _ w
  have e₂ : (fun u => K ⟨z.1.1, z.1.2, z.2, ys, u⟩ u) =
      fun u => K ⟨z.1.1, z.1.2, z.2, ys, fun _ => default⟩ u := by
    funext u
    exact hK _ _ _ _ _ _ u
  simp only [] at e₁ e₂ ⊢
  rw [e₁, e₂]
  exact fillWith_resample _ _

omit [Fintype pr.Y] [DecidableEq pr.Digest] [Nontrivial Msg] in
/-- **The target cap**: the shared first stage makes at most `L · lsf` challenge queries. -/
theorem targets_length_le {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (pk : pr.PkSeed) (sel : ℕ → Option ℕ) {d : Setup pr Msg A.State}
    (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary)) :
    (targets pr pk sel d.S d.ys).length ≤ L * P.lsf := by
  unfold setupHyb at hd
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hd
  obtain ⟨z, hz, ys, -, u, -, rfl⟩ := hd
  have hz' := OracleComp.mem_support_of_mem_support_simulateQ_run _ _ _ hz
  unfold targets
  split_ifs with hS
  · exact (length_targetsOf_le pr _ _).trans
      (Nat.mul_le_mul_right _ (A.anchors_le z.1 hz' hS))
  · exact Nat.zero_le _

variable (Msg)

/-- **The shared first stage**: the setup of the block games, then `pickProg`; the state is the
setup with the table updated by the challenge answers. -/
noncomputable def pickOf (sel : ℕ → Option ℕ) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    OracleComp (FSpec pr) (Setup pr Msg A.State) := do
  let d ← (liftM (setupHyb pr Msg slKeygen A) : OracleComp (FSpec pr) (Setup pr Msg A.State))
  let u' ← pickProg pr sel d.ys d.u
  return {d with u := u'}

/-- An SM-UD adversary against `F ∈ Th_λ` with `L · lsf` targets whose first stage is the shared
first stage. -/
noncomputable def udAdv (sel : ℕ → Option ℕ) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (dist : Setup pr Msg A.State → pr.PkSeed → ProbComp Bool) :
    SM_DT_UD_Adversary (probUD pr (L * P.lsf)) where
  State := Setup pr Msg A.State
  pick := pickOf pr Msg slKeygen sel A.toFxmssAdversary
  distinguish := dist

/-- An SM-PRE adversary against `F ∈ Th_λ` with `L · lsf` targets whose first stage is the
shared first stage. -/
noncomputable def preAdv (sel : ℕ → Option ℕ) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (inv : Setup pr Msg A.State → pr.PkSeed → ProbComp (ℕ × pr.Y)) :
    SM_DT_PRE_Adversary (probPre pr (L * P.lsf)) where
  State := Setup pr Msg A.State
  choose := pickOf pr Msg slKeygen sel A.toFxmssAdversary
  invert := inv

variable {Msg}

/-- The challenge answer of the SM-UD world `w`: `F(PK.seed, T, x)` (real) or `x` (ideal), for
the challenge oracle's fresh uniform `x`. -/
def udAns (w : SM_DT_UD_World) (pk : pr.PkSeed) : SLHDSA.Adrs → pr.Y → pr.Y :=
  match w with
  | .real => fun t x => pr.F pk t x
  | .ideal => fun _ x => x

omit [Fintype pr.Y] [DecidableEq pr.Digest] [Nontrivial Msg] in
/-- **The SM-UD experiment of the shared first stage**: `PK.seed`, the setup, the challenge
answers written into the table, and the distinguisher on the updated setup. -/
theorem udExp_evalDistEq (w : SM_DT_UD_World) (sel : ℕ → Option ℕ) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (dist : Setup pr Msg A.State → pr.PkSeed → ProbComp Bool) :
    SM_DT_UD_Experiment w (udAdv pr Msg slKeygen sel A dist) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let u' ← fillWith (udAns pr w pk) (targets pr pk sel d.S d.ys) d.u
          dist {d with u := u'} pk) := by
  unfold SM_DT_UD_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [udAdv, pickOf, SM_DT_UD_oracles]
  rw [simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  refine evalDistEq_of_eq ?_
  have hcoll : CollAnswers pr (id : SLHDSA.Adrs → SLHDSA.Adrs) pk
      (unifFwd (SM_DT_UD_State SLHDSA.Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
        collectionOracle id (probUD pr (L * P.lsf)).thColl pk)) := by
    intro q qs tws hq
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
    exact collectionOracle_run_of_fresh id q hq
  have hchal : ChalAnswers pr (id : SLHDSA.Adrs → SLHDSA.Adrs) (L * P.lsf) (udAns pr w pk)
      (fun t _ => t)
      (unifFwd (SM_DT_UD_State SLHDSA.Adrs) + (SM_DT_UD_challengeOracle w (probUD pr (L * P.lsf)) pk +
        collectionOracle id (probUD pr (L * P.lsf)).thColl pk)) := by
    intro t qs tws hlen hfr
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    cases w
    · exact SM_DT_UD_challengeOracle_run_of_fresh_real hlen hfr
    · exact SM_DT_UD_challengeOracle_run_of_fresh_ideal hlen hfr
  have hrun := run_pickProg hcoll hchal (fun _ _ => rfl) sel d.ys d.u
    (targets_length_le pr slKeygen A pk sel hd)
  rw [← map_fst_runRef (udAns pr w pk) (fun t _ => t), ← hrun, simulateQ_bind, StateT.run_bind,
    Functor.map_map, bind_map_left, bind_assoc]
  refine bind_congr fun z => ?_
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

/-- The winning check of the SM-PRE experiment on the record `Q` of `(T, x)` pairs. -/
def preWin (pk : pr.PkSeed) (Q : List (SLHDSA.Adrs × pr.Y)) (jm : ℕ × pr.Y) : Bool :=
  match Q[jm.1]? with
  | none => false
  | some (t, x) => decide (pr.F pk t jm.2 = pr.F pk t x)

omit [Fintype pr.Y] [DecidableEq pr.Digest] [Nontrivial Msg] in
/-- **The SM-PRE experiment of the shared first stage**: `PK.seed`, the setup, the sampling
program with its record `(T, x)` of hidden inputs, the inverter on the updated setup, and the
winning check. -/
theorem preExp_evalDistEq (sel : ℕ → Option ℕ) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (inv : Setup pr Msg A.State → pr.PkSeed → ProbComp (ℕ × pr.Y)) :
    SM_DT_PRE_Experiment (preAdv pr Msg slKeygen sel A inv) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← setupHyb pr Msg slKeygen A.toFxmssAdversary
          let z ← runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (targets pr pk sel d.S d.ys) d.u []
          let jm ← inv {d with u := z.1} pk
          return preWin pr pk z.2 jm) := by
  unfold SM_DT_PRE_Experiment
  refine EvalDistEq.bind_right _ fun pk => ?_
  simp only [preAdv, pickOf, SM_DT_PRE_oracles]
  rw [simulateQ_add_liftM_bind_run, bind_assoc]
  refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
  refine evalDistEq_of_eq ?_
  have hcoll : CollAnswers pr (Prod.fst : SLHDSA.Adrs × pr.Y → SLHDSA.Adrs) pk
      (unifFwd (SM_DT_PRE_State SLHDSA.Adrs pr.Y) + (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
        collectionOracle (Q := SLHDSA.Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk)) := by
    intro q qs tws hq
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
    exact collectionOracle_run_of_fresh Prod.fst q hq
  have hchal : ChalAnswers pr (Prod.fst : SLHDSA.Adrs × pr.Y → SLHDSA.Adrs) (L * P.lsf)
      (fun t x => pr.F pk t x) (fun t x => (t, x))
      (unifFwd (SM_DT_PRE_State SLHDSA.Adrs pr.Y) + (SM_DT_PRE_challengeOracle (probPre pr (L * P.lsf)) pk +
        collectionOracle (Q := SLHDSA.Adrs × pr.Y) Prod.fst (probPre pr (L * P.lsf)).thColl pk)) := by
    intro t qs tws hlen hfr
    rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    exact SM_DT_PRE_challengeOracle_run_of_fresh hlen hfr
  have hrun := run_pickProg hcoll hchal (fun _ _ => rfl) sel d.ys d.u
    (targets_length_le pr slKeygen A pk sel hd)
  rw [← hrun, simulateQ_bind, StateT.run_bind, bind_map_left, bind_assoc]
  refine bind_congr fun z => ?_
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  refine bind_congr fun jm => ?_
  simp only [preWin]
  cases z.2.1[jm.1]? with
  | none => rfl
  | some tx => obtain ⟨t, x⟩ := tx; rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
theorem prE6_gameHyb (γ : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E6 o] =
      𝒟[(fun o => decide (HybEvent Honest.E6 o)) <$> gameHyb pr Msg slKeygen γ A] {true} := by
  rw [prEvent_eq_evalDist_decide, map_eq_bind_pure_comp]
  rfl

end Games

end ShrincsSecurity.Fxmss.Rom.Hyb

end
