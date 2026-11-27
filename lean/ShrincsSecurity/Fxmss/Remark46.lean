module

public import ShrincsSecurity.Fxmss.Bridge

/-!
# Remark 4.6: all signing leaves are queried

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Remark 4.6** (txt lines 3171–3190): without loss
of generality a forger signs on every anchor of its structure. A forger `A` is completed by the
wrapper `A' = wrap L A`, which runs `A` through a logging handler (`leafLog`: every query forwarded
unchanged, the leaves of the signing queries recorded), receives its forgery
`(M*, (z*, i*), σ*)`, and only then issues signing queries with the message `M' = otherMsg M* ≠ M*`
on the anchors `A` did not query (`wrapIds`: in the canonical order `anchorList`, capped at `L`),
before outputting `A`'s forgery unchanged. Like the paper's `A'`, it makes no further query to
`H_msg^sf`.

* `succ_wrap`: the forgery is valid for `A'` exactly when it is valid for `A`:
  `Succ(A') = Succ(A)`. The completion logs only `M' ≠ M*` (`completion_log`), and its
  random-oracle queries (made by the signer) are at points with message `M'`, so they never touch
  the verification point, whose message is `M*`: the verifier's digest has the same distribution
  (`completion_roAns`).
* `wrap_signs_all`: after `A'`, every anchor of a structure with at most `L` anchors is used.
* `wrap`'s `signBound`, `length_wrapIds`, `wrap_roBound`, `Forger.wrap`: `A'` makes `A`'s
  signing queries plus `min(L, #anchors A did not query)` more, so at most `q_s + L`; its
  random-oracle queries are exactly `A`'s (`q_{h,2}` unchanged).

## Why the signing budget is `q_s + L` and not the paper's `q_s = L`

The forgers of Definition 4.16 may make signing queries that are answered `⊥` (a leaf outside
the structure, or one already used); their messages are still logged and so still exclude
forgeries. A forger that makes `q_s = L` such queries and none on an anchor needs `L` more queries
to sign every anchor, `2L = q_s + L` in total. A wrapper staying within `L` queries would have to
drop `⊥` queries of `A`; that removes their messages from the log, so a forgery on one of them,
invalid for `A`, becomes valid for the wrapper, and only `Succ(A) ≤ Succ(A')` would hold. The
paper's `q_s = L` is therefore the count of *answered* signing queries; the proof of Theorem 4.2
only uses that every anchor is signed (`wrap_signs_all`), which holds here.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-! ## Query bounds of the completion -/

omit [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
    [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- The completion on `ids` makes `|ids|` signing queries. -/
theorem completion_signBound (M : Msg) (ids : List LeafId) :
    (completion pr Msg M ids).IsQueryBoundP Notions.IsSignQuery ids.length := by
  induction ids with
  | nil => simp [completion]
  | cons id ids ih =>
    simp only [completion]
    rw [isQueryBoundP_query_bind_iff]
    simpa [Notions.IsSignQuery] using ih

omit [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
    [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- The completion makes no random-oracle query. -/
theorem completion_roBound (M : Msg) (ids : List LeafId) :
    (completion pr Msg M ids).IsQueryBoundP (IsRoQuery' pr Msg) 0 := by
  induction ids with
  | nil => simp [completion]
  | cons id ids ih =>
    simp only [completion]
    rw [isQueryBoundP_query_bind_iff]
    simpa [IsRoQuery'] using ih

/-! ## Logging the leaves of the signing queries -/

/-- The leaf log after a query: a signing query on `(M, (z, i))` appends `(z, i)`. -/
def leafUpd : (fullSpec pr Msg).Domain → List LeafId → List LeafId
  | .inl _, l => l
  | .inr q, l => l ++ [q.2]

/-- The logging handler of the wrapper: every query is forwarded unchanged, and the leaves of the
signing queries are recorded. -/
def leafLog : QueryImpl (fullSpec pr Msg) (StateT (List LeafId) (OracleComp (fullSpec pr Msg))) :=
  fun t => StateT.mk fun l =>
    (fun u => (u, leafUpd pr Msg t l)) <$> (liftM ((fullSpec pr Msg).query t) :
      OracleComp (fullSpec pr Msg) _)

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [DecidableEq pr.PkSeed]
    [SampleableType pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- The logging handler forwards a query and records its leaf. -/
theorem leafLog_query_bind {α : Type} (t : (fullSpec pr Msg).Domain)
    (k : (fullSpec pr Msg).Range t → OracleComp (fullSpec pr Msg) α) (l : List LeafId) :
    (simulateQ (leafLog pr Msg) (liftM ((fullSpec pr Msg).query t) >>= k)).run l =
      liftM ((fullSpec pr Msg).query t) >>= fun u =>
        (simulateQ (leafLog pr Msg) (k u)).run (leafUpd pr Msg t l) := by
  simp [leafLog]

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [DecidableEq pr.PkSeed]
    [SampleableType pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- Logging preserves every query bound. -/
theorem leafLog_bound {p : (fullSpec pr Msg).Domain → Prop} [DecidablePred p] {α : Type}
    {oa : OracleComp (fullSpec pr Msg) α} {n : ℕ} (h : oa.IsQueryBoundP p n) (l : List LeafId) :
    ((simulateQ (leafLog pr Msg) oa).run l).IsQueryBoundP p n := by
  induction oa using OracleComp.inductionOn generalizing n l with
  | pure x => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [leafLog_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u) _⟩

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [DecidableEq pr.PkSeed]
    [SampleableType pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- Under any handler, the logged run projects to the plain run. -/
theorem leafLog_run {σ : Type} (impl : QueryImpl (fullSpec pr Msg) (StateT σ ProbComp)) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (l : List LeafId) (s : σ) :
    (fun w => (w.1.1, w.2)) <$> (simulateQ impl ((simulateQ (leafLog pr Msg) oa).run l)).run s =
      (simulateQ impl oa).run s := by
  induction oa using OracleComp.inductionOn generalizing l s with
  | pure x => simp
  | query_bind t k ih =>
    rw [leafLog_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    exact bind_congr fun a => ih a.1 _ a.2

/-! ## The wrapper -/

/-- The completion list of the wrapper: the anchors, in the canonical order, that `A` did not
query, capped at `L`. -/
noncomputable def wrapIds (P : Params) (S : Structure) (L : ℕ) (l : List LeafId) : List LeafId :=
  ((anchorList P S).filter fun id => id ∉ l).take L

/-- The signing phase of the wrapper `A'`: `A₂`, run through the logging handler, then a signing
query with message `≠ M*` on each anchor that `A₂` did not query (at most `L` of them). -/
noncomputable def wrapForge {qs : ℕ} (L : ℕ)
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) (st : A.State) (S : Structure)
    (pk : PK pr) : OracleComp (fullSpec pr Msg) (Msg × LeafId × Sig pr) := do
  let z ← (simulateQ (leafLog pr Msg) (A.forge st S pk)).run []
  completion pr Msg (otherMsg Msg z.1.1) (wrapIds P S L z.2)
  return z.1

/-- **The wrapper `A'` of Remark 4.6**: runs `A` (recording the leaves of its signing queries),
receives its forgery `(M*, (z*, i*), σ*)`, signs a message `≠ M*` on every anchor `A` did not
query (at most `L` of them), and outputs `A`'s forgery. -/
noncomputable def wrap (L : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Notions.FxmssAdversary (scheme pr Msg slKeygen) (qs + L) where
  State := A.State
  chooseShape := A.chooseShape
  forge := wrapForge pr Msg slKeygen L A
  signBound st S pk := by
    refine isQueryBoundP_bind (leafLog_bound pr Msg (A.signBound st S pk) []) fun z _ => ?_
    refine IsQueryBoundP.mono (isQueryBoundP_bind (completion_signBound pr Msg _ _)
      fun _ _ => isQueryBoundP_pure _ _ 0) ?_
    simp [wrapIds]

/-- The number of completion queries of the wrapper: the number of anchors `A` did not query,
capped at `L`. -/
theorem length_wrapIds (S : Structure) (L : ℕ) (l : List LeafId) :
    (wrapIds P S L l).length = min L ((anchorList P S).filter fun id => id ∉ l).length := by
  simp [wrapIds]

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The wrapper makes exactly the random-oracle queries of `A` (the completion makes none). -/
theorem wrap_roBound (L : ℕ) {qs qh₂ : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (h : ∀ st S pk, (A.forge st S pk).IsQueryBoundP (IsRoQuery' pr Msg) qh₂) (st : A.State)
    (S : Structure) (pk : PK pr) :
    ((wrap pr Msg slKeygen L A).forge st S pk).IsQueryBoundP (IsRoQuery' pr Msg) qh₂ := by
  refine IsQueryBoundP.mono (isQueryBoundP_bind (leafLog_bound pr Msg (h st S pk) [])
    fun _ _ => isQueryBoundP_bind_zero _ _ (completion_roBound pr Msg _ _)
      fun _ => isQueryBoundP_pure _ _ 0) (by simp)

/-- The wrapper of a forger of Theorem 4.2 is a forger with `q_s + L` signing queries and the
same random-oracle query bounds. -/
noncomputable def Forger.wrap {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Forger pr Msg slKeygen (qs + L) qh₁ qh₂ L where
  toFxmssAdversary := Rom.wrap pr Msg slKeygen L A.toFxmssAdversary
  roBound₁ := A.roBound₁
  roBound₂ := wrap_roBound pr Msg slKeygen L A.toFxmssAdversary A.roBound₂
  anchors_le := A.anchors_le

/-! ## Every anchor is signed after the wrapper -/

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- A step of the scheme oracles never removes a used leaf, and a signing query on an anchor
leaves it used. -/
theorem oracles_step_used (S : Structure) (k : SK pr) (t : (fullSpec pr Msg).Domain)
    (s : List LeafId × List Msg) :
    ∀ y ∈ support (((scheme pr Msg slKeygen).oracles S k t).run s),
      (∀ x ∈ s.1, x ∈ y.2.1) ∧
        ∀ q : Msg × LeafId, t = .inr q → q.2 ∈ leafIds P.hsf S → q.2 ∈ y.2.1 := by
  intro y hy
  rcases t with t | q
  · simp [Notions.FxmssScheme.oracles] at hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨fun x hx => hx, by simp⟩
  · by_cases h : q.2 ∈ leafIds P.hsf S ∧ q.2 ∉ s.1
    · simp [Notions.FxmssScheme.oracles, Notions.FxmssScheme.signOracle, scheme, h] at hy
      obtain ⟨a, b, -, rfl⟩ := hy
      refine ⟨fun x hx => List.mem_append_left _ hx, ?_⟩
      rintro _ ⟨⟩ -
      simp
    · simp [Notions.FxmssScheme.oracles, Notions.FxmssScheme.signOracle, scheme, h] at hy
      subst hy
      refine ⟨fun x hx => hx, ?_⟩
      rintro _ ⟨⟩ hl
      by_contra hn
      exact h ⟨hl, hn⟩

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- Used leaves stay used. -/
theorem oracles_used_mono (S : Structure) (k : SK pr) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : List LeafId × List Msg) (x : LeafId)
    (hx : x ∈ s.1) :
    ∀ z ∈ support ((simulateQ ((scheme pr Msg slKeygen).oracles S k) oa).run s), x ∈ z.2.1 :=
  simulateQ_run_preserves_inv_of_query _ (fun s => x ∈ s.1)
    (fun t s hs y hy => (oracles_step_used pr Msg slKeygen S k t s y hy).1 x hs) oa s hx

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- After the completion on `ids`, every anchor in `ids` is used. -/
theorem completion_used (S : Structure) (k : SK pr) (M : Msg) :
    ∀ (ids : List LeafId) (s : List LeafId × List Msg),
      ∀ z ∈ support ((simulateQ ((scheme pr Msg slKeygen).oracles S k)
        (completion pr Msg M ids)).run s),
      ∀ id ∈ ids, id ∈ leafIds P.hsf S → id ∈ z.2.1
  | [], _, _, _, _, hid, _ => by simp at hid
  | id₀ :: ids, s, z, hz, id, hid, hl => by
    simp only [completion, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rcases List.mem_cons.1 hid with rfl | hid
    · exact oracles_used_mono pr Msg slKeygen S k _ y.2 _
        ((oracles_step_used pr Msg slKeygen S k (.inr (M, id)) s y hy).2 (M, id) rfl hl) z hz
    · exact completion_used S k M ids y.2 z hz id hid hl

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- Under the scheme oracles, every logged anchor is used. -/
theorem leafLog_used (S : Structure) (k : SK pr) {α : Type} (oa : OracleComp (fullSpec pr Msg) α)
    (l : List LeafId) (s : List LeafId × List Msg)
    (hs : ∀ id ∈ l, id ∈ leafIds P.hsf S → id ∈ s.1) :
    ∀ z ∈ support ((simulateQ ((scheme pr Msg slKeygen).oracles S k)
      ((simulateQ (leafLog pr Msg) oa).run l)).run s),
      ∀ id ∈ z.1.2, id ∈ leafIds P.hsf S → id ∈ z.2.1 := by
  induction oa using OracleComp.inductionOn generalizing l s with
  | pure x =>
    intro z hz
    simp at hz
    subst hz
    exact hs
  | query_bind t cont ih =>
    intro z hz
    rw [leafLog_query_bind] at hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    refine ih y.1 _ y.2 (fun id hid hl => ?_) z hz
    have hstep := oracles_step_used pr Msg slKeygen S k t s y hy
    rcases t with t | q
    · exact hstep.1 id (hs id hid hl)
    · rcases List.mem_append.1 hid with hid | hid
      · exact hstep.1 id (hs id hid hl)
      · rw [List.mem_singleton.1 hid]
        rw [List.mem_singleton.1 hid] at hl
        exact hstep.2 q rfl hl

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- **Remark 4.6, every anchor signed**: after the wrapper's signing phase, every anchor of a
structure with at most `L` anchors is used. -/
theorem wrap_signs_all (L : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (S : Structure) (pk : PK pr) (k : SK pr) (hL : S.anchors.card ≤ L) :
    ∀ z ∈ support ((simulateQ ((scheme pr Msg slKeygen).oracles S k)
      ((wrap pr Msg slKeygen L A).forge st S pk)).run ([], [])),
      ∀ id ∈ leafIds P.hsf S, id ∈ z.2.1 := by
  intro z hz id hid
  simp only [wrap, wrapForge, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w, hw, r, hr, rfl⟩ := hz
  by_cases hl : id ∈ w.1.2
  · exact oracles_used_mono pr Msg slKeygen S k _ w.2 id
      (leafLog_used pr Msg slKeygen S k _ [] ([], []) (by simp) w hw id hl hid) r hr
  · refine completion_used pr Msg slKeygen S k _ _ w.2 r hr id ?_ hid
    have hlen : ((anchorList P S).filter fun id => id ∉ w.1.2).length ≤ L :=
      (List.length_filter_le _ _).trans (by
        simpa [anchorList, leafIds] using Finset.card_image_le.trans hL)
    rw [wrapIds, List.take_of_length_le hlen, List.mem_filter]
    exact ⟨by simpa [anchorList] using hid, by simpa using hl⟩

/-! ## The wrapper does not change the success probability -/

/-- The answer of the lazily sampled random oracle at `x` from the cache `c`. -/
noncomputable def roAns (c : (roSpec pr Msg).QueryCache) (x : RoIn pr Msg) : ProbComp pr.Digest :=
  match c x with
  | some d => pure d
  | none => $ᵗ pr.Digest

omit [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A random-oracle step observed through its answer only. -/
theorem roStep_bind_fst {β : Type} (x : RoIn pr Msg) (s : St pr Msg)
    (f : pr.Digest → ProbComp β) :
    ((roStep pr Msg x).run s >>= fun q => f q.1) = roAns pr Msg s.cache x >>= f := by
  cases h : s.cache.toFn x <;> simp [roStep, roAns, h]

omit [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A random-oracle step at `x'` keeps the cache entry at every `x ≠ x'`. -/
theorem roStep_cache_ne (x x' : RoIn pr Msg) (hx : x ≠ x') (s : St pr Msg) :
    ∀ y ∈ support ((roStep pr Msg x').run s), y.2.cache x = s.cache x := by
  intro y hy
  cases h : s.cache.toFn x' with
  | some d =>
    simp [roStep, h] at hy
    subst hy
    rfl
  | none =>
    simp [roStep, h] at hy
    obtain ⟨d, rfl⟩ := hy
    simp [hx]

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A signing step of `F.0` with message `M` keeps the cache entry at every point whose message
is not `M` (its only random-oracle query has message `M`). -/
theorem implG_sign_cache (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (x : RoIn pr Msg) (hx : x.2.2.2.2 ≠ q.1) (s : St pr Msg) :
    ∀ y ∈ support ((implG pr Msg K sk (.inr q)).run s), y.2.cache x = s.cache x := by
  intro y hy
  by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
  · simp [implG, impl, signStep, h] at hy
    obtain ⟨R, d, b, hb, rfl⟩ := hy
    exact roStep_cache_ne pr Msg x _ (fun he => hx (by rw [he]; rfl)) s (d, b) hb
  · simp [implG, impl, signStep, h] at hy
    subst hy
    rfl

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- **The completion does not affect the random-oracle answer at the verification point**: the
completion with message `M` followed by the answer at a point `x` whose message is not `M` has the
distribution of the answer at `x` before the completion. -/
theorem completion_roAns (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (M : Msg) (x : RoIn pr Msg)
    (hx : x.2.2.2.2 ≠ M) {β : Type} (g : pr.Digest → ProbComp β) :
    ∀ (ids : List LeafId) (s : St pr Msg),
      ((simulateQ (implG pr Msg K sk) (completion pr Msg M ids)).run s >>= fun r =>
        roAns pr Msg r.2.cache x >>= g) =ᵈ (roAns pr Msg s.cache x >>= g)
  | [], s => by simp [completion]
  | id :: ids, s => by
    simp only [completion, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    refine (EvalDistEq.bind_right _ fun (y : Option (Sig pr) × St pr Msg) =>
      completion_roAns K sk M x hx g ids y.2).trans ?_
    refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ fun y hy => ?_)
      (EvalDistEq.bind_const _ (roAns pr Msg s.cache x >>= g))
    have hc := implG_sign_cache pr Msg K sk (M, id) x hx s y hy
    simp only [roAns, hc]
    exact EvalDistEq.rfl

open scoped Classical in
/-- **Remark 4.6, the wrapper is harmless**: `A'` has exactly the success probability of `A`.
Its forgery is `A`'s; the completion only queries messages `≠ M*`, so it neither logs `M*` nor
touches the random oracle at the verification point (whose message is `M*`), and the verifier's
digest has the same distribution. -/
theorem succ_wrap (L : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    succ pr Msg slKeygen (wrap pr Msg slKeygen L A) = succ pr Msg slKeygen A := by
  suffices H : (gameG pr Msg slKeygen (wrap pr Msg slKeygen L A) >>= fun o =>
      pure (decide (WinO o))) =ᵈ (gameG pr Msg slKeygen A >>= fun o => pure (decide (WinO o))) by
    rw [succ_eq_gameG, succ_eq_gameG, prEvent_eq_evalDist_decide, prEvent_eq_evalDist_decide,
      H.evalDist_eq]
  simp only [gameG, bind_assoc]
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.bind_right _ fun z => ?_
  rcases z with ⟨⟨S, st⟩, c⟩
  by_cases hv : S.TreeValid P.hsf
  · simp only [stageG, hv, not_true_eq_false, ↓reduceIte, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun f => EvalDistEq.bind_right _ fun pkSl => ?_
    refine (stage2_win pr Msg slKeygen _ _ _ _ _).trans
      (EvalDistEq.trans ?_ (stage2_win pr Msg slKeygen A _ _ _ _).symm)
    simp only [wrap, wrapForge, simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure,
      StateT.run_pure, pure_bind]
    rw [← leafLog_run pr Msg _ (A.forge st _ _) [] _, bind_map_left]
    refine EvalDistEq.bind_right _ fun w => ?_
    dsimp only
    have key := fun s' => roStep_bind_fst pr Msg
      (roIn pr Msg w.1.1.2.2.1 pk (pkSfOf pr S pk (skOf pr S f)) w.1.1.2.1 w.1.1.1) s'
      (fun y => pure (verifyWith pr pk (pkSfOf pr S pk (skOf pr S f)) w.1.1.2.1 w.1.1.2.2.2 y &&
        !decide (w.1.1.1 ∈ w.2.log)))
    refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ (g := fun r =>
      roAns pr Msg r.2.cache (roIn pr Msg w.1.1.2.2.1 pk (pkSfOf pr S pk (skOf pr S f)) w.1.1.2.1
        w.1.1.1) >>= fun y => pure (verifyWith pr pk (pkSfOf pr S pk (skOf pr S f)) w.1.1.2.1
          w.1.1.2.2.2 y && !decide (w.1.1.1 ∈ w.2.log))) fun r hr => ?_) ?_
    · have hc := completion_log pr Msg _ _ _ w.1.1.1 (otherMsg_ne Msg w.1.1.1) _ _ r hr
      simp only [hc]
      rw [key]
    · rw [key]
      exact completion_roAns pr Msg _ _ _ _ (otherMsg_ne Msg w.1.1.1).symm _ _ _
  · simp [stageG, hv]

end ShrincsSecurity.Fxmss.Rom

end
