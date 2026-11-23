module

public import ShrincsSecurity.Fxmss.Bridge

/-!
# Remark 4.6: all signing leaves are queried

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Remark 4.6** (txt lines 3171–3190): without loss
of generality a forger signs on every anchor of its structure. A forger `A` is completed by the
wrapper `A' = wrap L A`, which runs `A`, receives its forgery `(M*, (z*, i*), σ*)`, and only then
issues signing queries with a message `M' ≠ M*` on the anchors, before outputting `A`'s forgery
unchanged.

* `succ_wrap`: the forgery is valid for `A'` exactly when it is valid for `A`, so
  `Succ(A') = Succ(A)` (proved through `succ_eq_gameG`).
* `wrap_signs_all`: after `A'`, every anchor of a structure with at most `L` anchors is used.
* `wrap`'s `signBound`, `wrap_roBound`, `Forger.wrap`: `A'` makes at most `q_s + L` signing
  queries and `q_{h,2} + 1` random-oracle queries in its signing phase.

Deviations from the paper's wrapper, for a simpler proof: `A'` signs on the first `L` anchors of
the canonical enumeration `anchorList` (already used anchors are answered `⊥`) instead of only on
the still unqueried ones, so its signing budget is `q_s + L` rather than `L`; and `A'` first queries
`H_msg^sf` at the verification point of the forgery (pre-caching the digest the verifier will see),
so it makes one more random-oracle query than `A` (the paper's `A'` makes none). Neither changes
the success probability.
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

/-! ## The wrapper -/

/-- The signing phase of the wrapper `A'`: `A₂`, then the verification query of the forgery,
then a signing query with message `≠ M*` on each of the first `L` anchors. -/
noncomputable def wrapForge {qs : ℕ} (L : ℕ)
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) (st : A.State) (S : Structure)
    (pk : PK pr) :
    OracleComp (fullSpec pr Msg) (Msg × LeafId × Sig pr) := do
  let out ← A.forge st S pk
  let _ ← ((fullSpec pr Msg).query (.inl (.inr (roIn pr Msg out.2.2.1 pk.1 pk.2.2 out.2.1 out.1))) :
    OracleComp (fullSpec pr Msg) pr.Digest)
  completion pr Msg (otherMsg Msg out.1) ((anchorList P S).take L)
  return out

/-- **The wrapper `A'` of Remark 4.6**: runs `A`, queries the random oracle at the verification
point of `A`'s forgery `(M*, (z*, i*), σ*)`, signs a message `≠ M*` on (the first `L` of) all
anchors, and outputs `A`'s forgery. -/
noncomputable def wrap (L : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Notions.FxmssAdversary (scheme pr Msg slKeygen) (qs + L) where
  State := A.State
  chooseShape := A.chooseShape
  forge := wrapForge pr Msg slKeygen L A
  signBound st S pk := by
    refine isQueryBoundP_bind (A.signBound st S pk) fun out _ => ?_
    simp only [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [Notions.IsSignQuery]), fun _ => ?_⟩
    simp only [Notions.IsSignQuery, ↓reduceIte]
    refine IsQueryBoundP.mono (isQueryBoundP_bind (completion_signBound pr Msg _ _)
      fun _ _ => isQueryBoundP_pure _ _ 0) ?_
    simp

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The wrapper makes one random-oracle query more than `A` in its signing phase. -/
theorem wrap_roBound (L : ℕ) {qs qh₂ : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (h : ∀ st S pk, (A.forge st S pk).IsQueryBoundP (IsRoQuery' pr Msg) qh₂) (st : A.State)
    (S : Structure) (pk : PK pr) :
    ((wrap pr Msg slKeygen L A).forge st S pk).IsQueryBoundP (IsRoQuery' pr Msg) (qh₂ + 1) := by
  refine isQueryBoundP_bind (h st S pk) fun out _ => ?_
  simp only [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr Nat.one_pos, fun _ => ?_⟩
  simp only [IsRoQuery', ↓reduceIte]
  exact isQueryBoundP_bind_zero _ _ (completion_roBound pr Msg _ _)
    fun _ => isQueryBoundP_pure _ _ 0

/-- The wrapper of a forger of Theorem 4.2 is a forger with `q_s + L` signing queries and
`q_{h,2} + 1` random-oracle queries in its signing phase. -/
noncomputable def Forger.wrap {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Forger pr Msg slKeygen (qs + L) qh₁ (qh₂ + 1) L where
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

omit [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- **Remark 4.6, every anchor signed**: after the wrapper's signing phase, every anchor of a
structure with at most `L` anchors is used. -/
theorem wrap_signs_all (L : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (S : Structure) (pk : PK pr) (k : SK pr) (hL : S.anchors.card ≤ L) :
    ∀ z ∈ support ((simulateQ ((scheme pr Msg slKeygen).oracles S k)
      ((wrap pr Msg slKeygen L A).forge st S pk)).run ([], [])),
      ∀ id ∈ leafIds P.hsf S, id ∈ z.2.1 := by
  intro z hz id hid
  simp only [wrap, wrapForge, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨p, -, y, -, r, hr, rfl⟩ := hz
  have htake : (anchorList P S).take L = anchorList P S := List.take_of_length_le (by
    simpa [anchorList, leafIds] using Finset.card_image_le.trans hL)
  refine completion_used pr Msg slKeygen S k _ _ y.2 r hr id ?_ hid
  rw [htake]
  simpa [anchorList] using hid

/-! ## The wrapper does not change the success probability -/

omit [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A random-oracle step caches its answer and keeps every cached entry. -/
theorem roStep_cache (x : RoIn pr Msg) (s : St pr Msg) :
    ∀ y ∈ support ((roStep pr Msg x).run s), y.2.cache x = some y.1 ∧
      ∀ x' d, s.cache x' = some d → y.2.cache x' = some d := by
  intro y hy
  cases h : s.cache.toFn x with
  | some d =>
    simp [roStep, h] at hy
    subst hy
    exact ⟨h, fun _ _ h' => h'⟩
  | none =>
    simp [roStep, h] at hy
    obtain ⟨d, rfl⟩ := hy
    refine ⟨by simp, fun x' d' h' => ?_⟩
    have hne : x' ≠ x := by
      rintro rfl
      simp [h] at h'
    simpa [hne] using h'

omit [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A random-oracle step at a cached point answers from the cache. -/
theorem roStep_run_of_cache (x : RoIn pr Msg) (s : St pr Msg) (d : pr.Digest)
    (h : s.cache x = some d) : (roStep pr Msg x).run s = pure (d, s) := by
  simp [roStep, h]

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- Cached entries persist through the signing phase of `F.0`. -/
theorem implG_cache_mono (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : St pr Msg) (x : RoIn pr Msg) (d : pr.Digest)
    (hx : s.cache x = some d) :
    ∀ z ∈ support ((simulateQ (implG pr Msg K sk) oa).run s), z.2.cache x = some d := by
  refine simulateQ_run_preserves_inv_of_query _ (fun s => s.cache x = some d) ?_ oa s hx
  intro t s hs y hy
  rcases t with (n | x') | q
  · simp [implG, impl] at hy
    obtain ⟨u, rfl⟩ := hy
    exact hs
  · exact (roStep_cache pr Msg x' s y hy).2 x d hs
  · by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
    · simp [implG, impl, signStep, h] at hy
      obtain ⟨R, d', b, hb, rfl⟩ := hy
      exact (roStep_cache pr Msg _ s (d', b) hb).2 x d hs
    · simp [implG, impl, signStep, h] at hy
      subst hy
      exact hs

open scoped Classical in
/-- **Remark 4.6, the wrapper is harmless**: `A'` has exactly the success probability of `A`.
Its forgery is `A`'s; the verification point is cached before the completion and the random
oracle never overwrites a cached entry, so the verifier sees the same digest; the completion only
queries messages `≠ M*`. -/
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
    simp only [wrap, wrapForge, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      simulateQ_pure, StateT.run_pure, pure_bind]
    refine EvalDistEq.bind_right _ fun p => ?_
    simp only [Keys.toPK, implG, impl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    refine EvalDistEq.bind_congr_of_support _ fun q hq => ?_
    obtain ⟨hqc, -⟩ := roStep_cache pr Msg _ _ q hq
    have hlog := roStep_log pr Msg _ _ q hq
    refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ fun r hr => ?_)
      (EvalDistEq.bind_const _ _)
    rw [roStep_run_of_cache pr Msg _ _ _ (implG_cache_mono pr Msg _ _ _ _ _ _ hqc r hr), pure_bind]
    have hc := completion_log pr Msg _ _ _ p.1.1 (otherMsg_ne Msg p.1.1) _ _ r hr
    simp only [hc, hlog]
    exact EvalDistEq.rfl
  · simp [stageG, hv]

end ShrincsSecurity.Fxmss.Rom

end
