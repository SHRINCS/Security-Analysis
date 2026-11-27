module

public import ShrincsSecurity.ITSR.Presample
public import ShrincsSecurity.ITSR.Coverage

/-!
# Classification of challenges and the witness structure

`ITSR-Classical.pdf`, Definition 7 (creation indices), the invariant of Lemma 2, Lemma 3
(classification of challenges) and Lemma 4 (witness structure).

`OriginInv` is Definition 7: the creation indices of the direct points are below the counter and
name distinct points. `TapeInv U V` is the invariant of Lemma 2 together with the bookkeeping of
Lemma 3 for a run on the tapes `U` and `V`: every direct point carries the tape value of its
creation index, every fresh-challenge point carries a value of `V` and is a challenge pair, every
challenge digest is the table value of its pair, and the pairs of direct points are pulled. It
holds along every run of a bounded adversary (`inv_run`), which is what rules out the fallback
sampling of the pre-sampled game.

Lemma 4 is `exists_witness_of_wins`: a winning run of the pre-sampled game yields an output entry
`a : Fin (q + 1)` and a witness map `β : Fin k → Option (Fin q)` (the encoding of `(B, (W_b))`
of `Coverage.lean`, with the pulled indices in `[q]`), such that `a ∉ B`, the digest event
`(ii) ∧ (iii) ∧ (iv)` holds and every `b ∈ B` is pulled (event `(i)`). The witness map with no
pulled position is the search structure `E_0(a)`.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

variable {K M D : Type} [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D]

/-! ## The support of a step -/

omit [DecidableEq K] [DecidableEq M] [SampleableType K] in
/-- A nonempty tape yields its head. -/
theorem mem_support_drawTape_cons {u : D} {l : List D} {z : D × List D} :
    z ∈ support (drawTape (u :: l)) ↔ z = (u, l) := by
  simp [drawTape]

/-- A coin query leaves the state unchanged. -/
theorem mem_support_tapeImpl_unif {n : ℕ} {s : TapeState K M D}
    {p : (AdvSpec K M D).Range (Sum.inl n) × TapeState K M D}
    (hp : p ∈ support ((tapeImpl (Sum.inl n : ℕ ⊕ ((K × M) ⊕ M))).run s)) : p.2 = s := by
  rw [tapeImpl_unif_run] at hp
  simp only [support_map, Set.mem_image] at hp
  obtain ⟨u, -, rfl⟩ := hp
  rfl

omit [SampleableType K] in
/-- A direct query either reads the table or creates a direct point (Lemma 2). -/
theorem mem_support_tapeHash {x : K × M} {s : TapeState K M D} {p : D × TapeState K M D}
    (hp : p ∈ support ((tapeHash x).run s)) :
    (∃ e, s.table x = some e ∧ p = (e.1, s)) ∨
      (s.table x = none ∧ ∃ z ∈ support (drawTape s.uTape), p = (z.1, s.hashFresh x z)) := by
  simp only [tapeHash, StateT.run_mk] at hp
  cases h : s.table x with
  | some e =>
    rw [h] at hp
    exact Or.inl ⟨e, rfl, by simpa using hp⟩
  | none =>
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact Or.inr ⟨rfl, z, hz, rfl⟩

/-- A challenge either hits a table point or creates a fresh-challenge point (Lemma 3). -/
theorem mem_support_tapeChal {msg : M} {s : TapeState K M D} {p : (K × D) × TapeState K M D}
    (hp : p ∈ support ((tapeChal msg).run s)) :
    ∃ key, (∃ e, s.table (key, msg) = some e ∧ p = ((key, e.1), s.chalHit (key, msg) e)) ∨
      (s.table (key, msg) = none ∧ ∃ z ∈ support (drawTape s.vTape),
        p = ((key, z.1), s.chalFresh (key, msg) z)) := by
  simp only [tapeChal, StateT.run_mk, mem_support_bind_iff] at hp
  obtain ⟨key, -, hp⟩ := hp
  refine ⟨key, ?_⟩
  simp only [tapeChalAt] at hp
  cases h : s.table (key, msg) with
  | some e =>
    rw [h] at hp
    exact Or.inl ⟨e, rfl, by simpa using hp⟩
  | none =>
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact Or.inr ⟨rfl, z, hz, rfl⟩

/-! ## Definition 7: creation indices -/

/-- **Definition 7** (creation indices): the creation indices of the direct points are below the
counter of fresh direct points, and distinct points have distinct indices. -/
structure OriginInv (s : TapeState K M D) : Prop where
  /-- Every creation index is below the counter. -/
  lt : ∀ y d b, s.table y = some (d, .direct b) → b < s.nU
  /-- A creation index names one point. -/
  inj : ∀ y y' d d' b, s.table y = some (d, .direct b) → s.table y' = some (d', .direct b) →
    y = y'

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- Definition 7 holds initially. -/
theorem OriginInv.init (lu lv : List D) : OriginInv (TapeState.init lu lv : TapeState K M D) :=
  ⟨fun _ _ _ h => by simp [TapeState.init] at h, fun _ _ _ _ _ h => by simp [TapeState.init] at h⟩

omit [SampleableType K] [SampleableType D] in
/-- A new direct point takes a new creation index. -/
theorem OriginInv.hashFresh {s : TapeState K M D} (hs : OriginInv s) {x : K × M}
    (hx : s.table x = none) (z : D × List D) : OriginInv (s.hashFresh x z) := by
  constructor
  · intro y d b hy
    simp only [TapeState.hashFresh] at hy ⊢
    by_cases hyx : y = x
    · subst hyx
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq, Origin.direct.injEq] at hy
      omega
    · rw [Function.update_of_ne hyx] at hy
      have := hs.lt y d b hy
      omega
  · intro y y' d d' b hy hy'
    simp only [TapeState.hashFresh] at hy hy'
    by_cases hyx : y = x <;> by_cases hy'x : y' = x
    · rw [hyx, hy'x]
    · subst hyx
      rw [Function.update_of_ne hy'x] at hy'
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq, Origin.direct.injEq] at hy
      have := hs.lt y' d' b hy'
      omega
    · subst hy'x
      rw [Function.update_of_ne hyx] at hy
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq, Origin.direct.injEq] at hy'
      have := hs.lt y d b hy
      omega
    · rw [Function.update_of_ne hyx] at hy
      rw [Function.update_of_ne hy'x] at hy'
      exact hs.inj y y' d d' b hy hy'

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- A challenge on a table point keeps the creation indices. -/
theorem OriginInv.chalHit {s : TapeState K M D} (hs : OriginInv s) (x : K × M)
    (e : D × Origin) : OriginInv (s.chalHit x e) :=
  ⟨hs.lt, hs.inj⟩

omit [SampleableType K] [SampleableType D] in
/-- A fresh challenge creates no direct point. -/
theorem OriginInv.chalFresh {s : TapeState K M D} (hs : OriginInv s) (x : K × M)
    (z : D × List D) : OriginInv (s.chalFresh x z) := by
  have key : ∀ y d b, (s.chalFresh x z).table y = some (d, .direct b) →
      s.table y = some (d, .direct b) := by
    intro y d b hy
    simp only [TapeState.chalFresh] at hy
    by_cases hyx : y = x
    · subst hyx
      simp at hy
    · rwa [Function.update_of_ne hyx] at hy
  exact ⟨fun y d b hy => hs.lt y d b (key y d b hy),
    fun y y' d d' b hy hy' => hs.inj y y' d d' b (key y d b hy) (key y' d' b hy')⟩

/-- Every step of the pre-sampled game preserves Definition 7. -/
theorem OriginInv.step {s : TapeState K M D} (hs : OriginInv s) (t : ℕ ⊕ ((K × M) ⊕ M))
    {p : (AdvSpec K M D).Range t × TapeState K M D} (hp : p ∈ support ((tapeImpl t).run s)) :
    OriginInv p.2 := by
  rcases t with n | x | msg
  · rw [mem_support_tapeImpl_unif hp]; exact hs
  · rcases mem_support_tapeHash hp with ⟨e, -, rfl⟩ | ⟨hx, z, -, rfl⟩
    · exact hs
    · exact hs.hashFresh hx z
  · obtain ⟨key, ⟨e, -, rfl⟩ | ⟨-, z, -, rfl⟩⟩ := mem_support_tapeChal hp
    · exact hs.chalHit _ e
    · exact hs.chalFresh _ z

/-! ## The invariant of Lemma 2 and the bookkeeping of Lemma 3 -/

/-- The pairs of the challenges so far. -/
abbrev TapeState.pairs (s : TapeState K M D) : List (K × M) := s.challenges.map Prod.fst

/-- **The invariant of Lemma 2** (origin of values) together with the classification of
Lemma 3, for a run on the tapes `U` and `V`. -/
structure TapeInv {n r : ℕ} (U : Fin n → D) (V : Fin r → D) (s : TapeState K M D) : Prop where
  /-- Definition 7. -/
  origin : OriginInv s
  /-- The unused part of `U` follows the fresh direct points. -/
  uTape : s.uTape = (List.ofFn U).drop s.nU
  /-- The unused part of `V` follows the fresh challenges. -/
  vTape : s.vTape = (List.ofFn V).drop s.nV
  /-- A direct point carries the `U`-value of its creation index. -/
  direct : ∀ y d b, s.table y = some (d, .direct b) → ∃ hb : b < n, d = U ⟨b, hb⟩
  /-- A fresh-challenge point is a challenge pair and carries a `V`-value. -/
  fresh : ∀ y d j, s.table y = some (d, .fresh j) → y ∈ s.pairs ∧ ∃ hj : j < r, d = V ⟨j, hj⟩
  /-- A pulled index names a direct point that is a challenge pair. -/
  pulled : ∀ b ∈ s.pulled, ∃ y d, s.table y = some (d, .direct b) ∧ y ∈ s.pairs
  /-- Every challenge digest is the table value of its pair, and a challenge on a direct point
  pulled it (Lemma 3). -/
  chal : ∀ y e, (y, e) ∈ s.challenges → ∃ o, s.table y = some (e, o) ∧
    ∀ b, o = .direct b → b ∈ s.pulled

section TapeInv

variable {n r : ℕ} {U : Fin n → D} {V : Fin r → D}

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- The invariant holds initially. -/
theorem TapeInv.init (U : Fin n → D) (V : Fin r → D) :
    TapeInv U V (TapeState.init (K := K) (M := M) (List.ofFn U) (List.ofFn V)) where
  origin := OriginInv.init _ _
  uTape := rfl
  vTape := rfl
  direct _ _ _ h := by simp [TapeState.init] at h
  fresh _ _ _ h := by simp [TapeState.init] at h
  pulled _ h := by simp [TapeState.init] at h
  chal _ _ h := by simp [TapeState.init] at h

omit [DecidableEq K] [DecidableEq M] [SampleableType K] in
/-- Within its length, the tape `U` yields the value of the next creation index. -/
theorem TapeInv.drawU {s : TapeState K M D} (hs : TapeInv U V s) (hn : s.nU < n) {z : D × List D}
    (hz : z ∈ support (drawTape s.uTape)) :
    z = (U ⟨s.nU, hn⟩, (List.ofFn U).drop (s.nU + 1)) := by
  rw [hs.uTape, List.drop_eq_getElem_cons (by simpa using hn), mem_support_drawTape_cons] at hz
  rw [hz]
  simp

omit [DecidableEq K] [DecidableEq M] [SampleableType K] in
/-- Within its length, the tape `V` yields the value of the next fresh challenge. -/
theorem TapeInv.drawV {s : TapeState K M D} (hs : TapeInv U V s) (hr : s.nV < r) {z : D × List D}
    (hz : z ∈ support (drawTape s.vTape)) :
    z = (V ⟨s.nV, hr⟩, (List.ofFn V).drop (s.nV + 1)) := by
  rw [hs.vTape, List.drop_eq_getElem_cons (by simpa using hr), mem_support_drawTape_cons] at hz
  rw [hz]
  simp

omit [SampleableType K] [SampleableType D] in
/-- A new direct point within the tape `U` keeps the invariant. -/
theorem TapeInv.hashFresh {s : TapeState K M D} (hs : TapeInv U V s) {x : K × M}
    (hx : s.table x = none) (hn : s.nU < n) :
    TapeInv U V (s.hashFresh x (U ⟨s.nU, hn⟩, (List.ofFn U).drop (s.nU + 1))) := by
  have old : ∀ y e, s.table y = some e →
      (s.hashFresh x (U ⟨s.nU, hn⟩, (List.ofFn U).drop (s.nU + 1))).table y = some e := by
    intro y e hy
    have hyx : y ≠ x := by rintro rfl; simp [hx] at hy
    simp [TapeState.hashFresh, Function.update_of_ne hyx, hy]
  constructor
  · exact hs.origin.hashFresh hx _
  · rfl
  · exact hs.vTape
  · intro y d b hy
    simp only [TapeState.hashFresh] at hy
    by_cases hyx : y = x
    · subst hyx
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq, Origin.direct.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨hn, rfl⟩
    · rw [Function.update_of_ne hyx] at hy
      exact hs.direct y d b hy
  · intro y d j hy
    simp only [TapeState.hashFresh] at hy
    by_cases hyx : y = x
    · subst hyx
      simp at hy
    · rw [Function.update_of_ne hyx] at hy
      exact hs.fresh y d j hy
  · intro b hb
    obtain ⟨y, d, hy, hyp⟩ := hs.pulled b hb
    exact ⟨y, d, old y _ hy, hyp⟩
  · intro y e he
    obtain ⟨o, hy, ho⟩ := hs.chal y e he
    exact ⟨o, old y _ hy, ho⟩

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- A challenge on a table point keeps the invariant: it is pulled or repeated (Lemma 3). -/
theorem TapeInv.chalHit {s : TapeState K M D} (hs : TapeInv U V s) {x : K × M} {e : D × Origin}
    (hx : s.table x = some e) : TapeInv U V (s.chalHit x e) := by
  have hpairs : ∀ y, y ∈ s.pairs → y ∈ (s.chalHit x e).pairs := by
    intro y hy
    simp only [TapeState.pairs, TapeState.chalHit, List.map_append, List.mem_append] at hy ⊢
    exact Or.inl hy
  have hpull : ∀ b, b ∈ s.pulled → b ∈ (s.chalHit x e).pulled := by
    intro b hb
    simp only [TapeState.chalHit]
    rcases e with ⟨d, _ | _⟩ <;> simp [Origin.pull, hb]
  constructor
  · exact hs.origin.chalHit x e
  · exact hs.uTape
  · exact hs.vTape
  · exact hs.direct
  · intro y d j hy
    obtain ⟨h1, h2⟩ := hs.fresh y d j hy
    exact ⟨hpairs y h1, h2⟩
  · intro b hb
    simp only [TapeState.chalHit] at hb
    rcases e with ⟨d, b' | j⟩
    · simp only [Origin.pull, Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact ⟨x, d, hx, by simp [TapeState.pairs, TapeState.chalHit]⟩
      · obtain ⟨y, d', hy, hyp⟩ := hs.pulled b hb
        exact ⟨y, d', hy, hpairs y hyp⟩
    · obtain ⟨y, d', hy, hyp⟩ := hs.pulled b hb
      exact ⟨y, d', hy, hpairs y hyp⟩
  · intro y e' he'
    simp only [TapeState.chalHit, List.mem_append, List.mem_singleton, Prod.mk.injEq] at he'
    rcases he' with he' | ⟨rfl, rfl⟩
    · obtain ⟨o, hy, ho⟩ := hs.chal y e' he'
      exact ⟨o, hy, fun b hb => hpull b (ho b hb)⟩
    · refine ⟨e.2, hx, fun b hb => ?_⟩
      simp [TapeState.chalHit, hb, Origin.pull]

omit [SampleableType K] [SampleableType D] in
/-- A fresh challenge within the tape `V` keeps the invariant (Lemma 3). -/
theorem TapeInv.chalFresh {s : TapeState K M D} (hs : TapeInv U V s) {x : K × M}
    (hx : s.table x = none) (hr : s.nV < r) :
    TapeInv U V (s.chalFresh x (V ⟨s.nV, hr⟩, (List.ofFn V).drop (s.nV + 1))) := by
  set s' := s.chalFresh x (V ⟨s.nV, hr⟩, (List.ofFn V).drop (s.nV + 1)) with hs'
  have old : ∀ y e, s.table y = some e → s'.table y = some e := by
    intro y e hy
    have hyx : y ≠ x := by rintro rfl; simp [hx] at hy
    simp [hs', TapeState.chalFresh, Function.update_of_ne hyx, hy]
  have hpairs : ∀ y, y ∈ s.pairs → y ∈ s'.pairs := by
    intro y hy
    simp only [hs', TapeState.pairs, TapeState.chalFresh, List.map_append, List.mem_append] at hy ⊢
    exact Or.inl hy
  constructor
  · exact hs.origin.chalFresh x _
  · exact hs.uTape
  · rfl
  · intro y d b hy
    simp only [hs', TapeState.chalFresh] at hy
    by_cases hyx : y = x
    · subst hyx
      simp at hy
    · rw [Function.update_of_ne hyx] at hy
      exact hs.direct y d b hy
  · intro y d j hy
    simp only [hs', TapeState.chalFresh] at hy
    by_cases hyx : y = x
    · subst hyx
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq, Origin.fresh.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨by simp [hs', TapeState.pairs, TapeState.chalFresh], hr, rfl⟩
    · rw [Function.update_of_ne hyx] at hy
      obtain ⟨h1, h2⟩ := hs.fresh y d j hy
      exact ⟨hpairs y h1, h2⟩
  · intro b hb
    obtain ⟨y, d, hy, hyp⟩ := hs.pulled b hb
    exact ⟨y, d, old y _ hy, hpairs y hyp⟩
  · intro y e he
    simp only [hs', TapeState.chalFresh, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at he
    rcases he with he | ⟨rfl, rfl⟩
    · obtain ⟨o, hy, ho⟩ := hs.chal y e he
      exact ⟨o, old y _ hy, ho⟩
    · exact ⟨.fresh s.nV, by simp [hs', TapeState.chalFresh], fun b hb => by cases hb⟩

/-- **The invariant along a bounded run.** A run with at most `h` direct and `c` challenge
queries, from a state satisfying the invariant whose counters leave room for them on the tapes,
ends in a state satisfying the invariant, with at most `h` new direct points and `c` new fresh
challenges. -/
theorem inv_run {α : Type} (oa : OracleComp (AdvSpec K M D) α) (h c : ℕ)
    (hh : oa.IsQueryBoundP (IsHashQuery K M) h) (hc : oa.IsQueryBoundP (IsChalQuery K M) c)
    (s : TapeState K M D) (hs : TapeInv U V s) (hn : s.nU + h ≤ n) (hr : s.nV + c ≤ r) :
    ∀ z ∈ support ((simulateQ tapeImpl oa).run s),
      TapeInv U V z.2 ∧ z.2.nU ≤ s.nU + h ∧ z.2.nV ≤ s.nV + c := by
  induction oa using OracleComp.inductionOn generalizing h c s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hs, by simp, by simp⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh hc
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rcases t with n' | x | msg
    · have hp2 := mem_support_tapeImpl_unif hp
      have hh' := hh.2 p.1
      have hc' := hc.2 p.1
      simp only [IsHashQuery, IsChalQuery, ite_false] at hh' hc'
      have := ih p.1 h c hh' hc' p.2 (hp2 ▸ hs) (hp2 ▸ hn) (hp2 ▸ hr) z hz
      rw [hp2] at this
      exact this
    · have hh0 : 0 < h := by simpa [IsHashQuery] using hh.1
      have hh' := hh.2 p.1
      have hc' := hc.2 p.1
      simp only [IsHashQuery, IsChalQuery, ite_true, ite_false] at hh' hc'
      rcases mem_support_tapeHash hp with ⟨e, -, rfl⟩ | ⟨hx, w, hw, rfl⟩
      · have := ih e.1 (h - 1) c hh' hc' s hs (by omega) hr z hz
        exact ⟨this.1, by omega, this.2.2⟩
      · have hlt : s.nU < n := by omega
        obtain rfl := hs.drawU hlt hw
        have := ih _ (h - 1) c hh' hc' _ (hs.hashFresh hx hlt)
          (by simp only [TapeState.hashFresh]; omega) (by simpa [TapeState.hashFresh] using hr) z hz
        simp only [TapeState.hashFresh] at this
        exact ⟨this.1, by omega, this.2.2⟩
    · have hc0 : 0 < c := by simpa [IsChalQuery] using hc.1
      have hh' := hh.2 p.1
      have hc' := hc.2 p.1
      simp only [IsHashQuery, IsChalQuery, ite_true, ite_false] at hh' hc'
      obtain ⟨key, ⟨e, he, rfl⟩ | ⟨hx, w, hw, rfl⟩⟩ := mem_support_tapeChal hp
      · have := ih _ h (c - 1) hh' hc' _ (hs.chalHit he)
          (by simpa [TapeState.chalHit] using hn) (by simp only [TapeState.chalHit]; omega) z hz
        simp only [TapeState.chalHit] at this
        exact ⟨this.1, this.2.1, by omega⟩
      · have hlt : s.nV < r := by omega
        obtain rfl := hs.drawV hlt hw
        have := ih _ h (c - 1) hh' hc' _ (hs.chalFresh hx hlt)
          (by simpa [TapeState.chalFresh] using hn) (by simp only [TapeState.chalFresh]; omega) z hz
        simp only [TapeState.chalFresh] at this
        exact ⟨this.1, this.2.1, by omega⟩

end TapeInv

/-! ## The verification query -/

/-- A run of the adversary followed by its verification query is a run of the adversary, then
the verification step. -/
theorem mem_support_withVerify {oa : OracleComp (AdvSpec K M D) (K × M)} {s₀ : TapeState K M D}
    {z : ((K × M) × D) × TapeState K M D}
    (hz : z ∈ support ((simulateQ tapeImpl (withVerify oa)).run s₀)) :
    ∃ s₁, (z.1.1, s₁) ∈ support ((simulateQ tapeImpl oa).run s₀) ∧
      (z.1.2, z.2) ∈ support ((tapeHash z.1.1).run s₁) := by
  simp only [withVerify, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨x, s₁⟩, h₁, ⟨d, s₂⟩, h₂, rfl⟩ := hz
  exact ⟨s₁, h₁, h₂⟩

/-! ## Lemma 4: the witness structure -/

section Witness

variable {ι : Type} [DecidableEq ι] {k t : ℕ}

/-- A witness map into `[q]` (pulled indices are created by the adversary's direct queries),
read as a witness map into `[q + 1]` (the output entry may be the verification point). -/
def castWitness {q : ℕ} (β : Fin k → Option (Fin q)) : Fin k → Option (Fin (q + 1)) :=
  fun i => (β i).map Fin.castSucc

/-- The pulled set of a cast witness map. -/
theorem witnessSet_castWitness {q : ℕ} (β : Fin k → Option (Fin q)) :
    witnessSet (castWitness β) = (witnessSet β).map Fin.castSuccEmb := by
  ext b
  simp only [witnessSet, castWitness, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, Option.map_eq_some_iff, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨i, b', hb', rfl⟩
    exact ⟨b', ⟨i, hb'⟩, rfl⟩
  · rintro ⟨b', ⟨i, hb'⟩, rfl⟩
    exact ⟨i, b', hb', rfl⟩

/-- Casting keeps `m = |B|`. -/
theorem card_witnessSet_castWitness {q : ℕ} (β : Fin k → Option (Fin q)) :
    (witnessSet (castWitness β)).card = (witnessSet β).card := by
  rw [witnessSet_castWitness, Finset.card_map]

/-- Casting keeps `W`, hence `ω = |W|`. -/
theorem pulledPositions_castWitness {q : ℕ} (β : Fin k → Option (Fin q)) :
    pulledPositions (castWitness β) = pulledPositions β := by
  ext i
  simp [pulledPositions, castWitness]

/-- **Lemma 4** (witness structure). A winning run of the pre-sampled game of a bounded adversary
has an output entry `a` and a pull structure `β` (Coverage encoding, pulled indices in `[q]`)
with `a ∉ B`, the digest event `(ii) ∧ (iii) ∧ (iv)`, and every `b ∈ B` pulled (`(i)`). -/
theorem exists_witness_of_wins [SampleableType (Digest ι k t)] {q r : ℕ}
    (U : Fin (q + 1) → Digest ι k t)
    (V : Fin r → Digest ι k t) (oa : OracleComp (AdvSpec K M (Digest ι k t)) (K × M))
    (hh : oa.IsQueryBoundP (IsHashQuery K M) q) (hc : oa.IsQueryBoundP (IsChalQuery K M) r)
    {z : ((K × M) × Digest ι k t) × TapeState K M (Digest ι k t)}
    (hz : z ∈ support ((simulateQ tapeImpl (withVerify oa)).run
      (TapeState.init (K := K) (M := M) (List.ofFn U) (List.ofFn V))))
    (hw : Wins z.2.toGame z.1.1 z.1.2) :
    ∃ a : Fin (q + 1), ∃ β : Fin k → Option (Fin q), a ∉ witnessSet (castWitness β) ∧
      DigestEvent a (castWitness β) U V ∧ ∀ b ∈ witnessSet β, (b : ℕ) ∈ z.2.pulled := by
  obtain ⟨s₁, h₁, h₂⟩ := mem_support_withVerify hz
  obtain ⟨hinv₁, hnU₁, -⟩ := inv_run oa q r hh hc _ (TapeInv.init U V)
    (by simp [TapeState.init]) (by simp [TapeState.init]) _ h₁
  dsimp only at hinv₁ hnU₁
  simp only [TapeState.init, zero_add] at hnU₁
  -- the pulled indices of the adversary's run lie in `[q]`
  have hpq : ∀ b ∈ s₁.pulled, b < q := by
    intro b hb
    obtain ⟨y, d, hy, -⟩ := hinv₁.pulled b hb
    have := hinv₁.origin.lt y d b hy
    omega
  -- the verification step: the output point is a direct point `a` with value `U a`
  obtain ⟨hinv₂, hpull₂, a, hxa, hda⟩ : TapeInv U V z.2 ∧ z.2.pulled = s₁.pulled ∧
      ∃ a : Fin (q + 1), z.2.table z.1.1 = some (z.1.2, .direct a) ∧ z.1.2 = U a := by
    rcases mem_support_tapeHash h₂ with ⟨⟨d, o⟩, he, heq⟩ | ⟨hx, w, hw', heq⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨hd, hs⟩ := heq
      rw [hs]
      refine ⟨hinv₁, rfl, ?_⟩
      cases o with
      | direct b =>
        obtain ⟨hb, hdb⟩ := hinv₁.direct _ d b he
        exact ⟨⟨b, hb⟩, by rw [he, hd], by rw [hd, hdb]⟩
      | fresh j =>
        obtain ⟨hmem, -⟩ := hinv₁.fresh _ d j he
        exact absurd (by rw [hs]; exact hmem) hw.1
    · have hlt : s₁.nU < q + 1 := by omega
      obtain rfl := hinv₁.drawU hlt hw'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hd, hs⟩ := heq
      rw [hs]
      refine ⟨hinv₁.hashFresh hx hlt, rfl, ⟨s₁.nU, hlt⟩, ?_, hd⟩
      simp [TapeState.hashFresh, hd]
  set x := z.1.1
  set s₂ := z.2
  have hxp : x ∉ s₂.pairs := hw.1
  -- pulled indices differ from `a`
  have hne : ∀ b ∈ s₂.pulled, b ≠ (a : ℕ) := by
    rintro b hb rfl
    obtain ⟨y, d, hy, hyp⟩ := hinv₂.pulled _ hb
    obtain rfl := hinv₂.origin.inj y x d _ _ hy hxa
    exact hxp hyp
  -- every challenge digest is a fresh value or a pulled value (Lemma 3)
  have hdig : ∀ u ∈ s₂.toGame.digests, (∃ j, u = V j) ∨
      ∃ b : Fin q, (b : ℕ) ∈ s₂.pulled ∧ u = U b.castSucc := by
    intro u hu
    simp only [GameState.digests, TapeState.toGame_challenges, List.mem_map] at hu
    obtain ⟨⟨y, u'⟩, hyu, rfl⟩ := hu
    obtain ⟨o, hy, ho⟩ := hinv₂.chal y u' hyu
    cases o with
    | direct b =>
      have hb := ho b rfl
      obtain ⟨hbq, hdb⟩ := hinv₂.direct y _ b hy
      refine Or.inr ⟨⟨b, hpq b (hpull₂ ▸ hb)⟩, hb, ?_⟩
      exact hdb
    | fresh j =>
      obtain ⟨-, hj, hdj⟩ := hinv₂.fresh y _ j hy
      exact Or.inl ⟨⟨j, hj⟩, hdj⟩
  -- choose a witness per position
  have hcov := hw.2
  rw [hda] at hcov
  have hchoice : ∀ i : Fin k, ∃ o : Option (Fin q),
      (o = none ∧ ∃ j, (V j).1 = (U a).1 ∧ (V j).2 i = (U a).2 i) ∨
        ∃ b : Fin q, o = some b ∧ (b : ℕ) ∈ s₂.pulled ∧
          (U b.castSucc).1 = (U a).1 ∧ (U b.castSucc).2 i = (U a).2 i := by
    intro i
    have hi := hcov i
    simp only [posSet, Finset.mem_image, Finset.mem_filter, List.mem_toFinset] at hi
    obtain ⟨u, ⟨hu, hu1⟩, hu2⟩ := hi
    rcases hdig u hu with ⟨j, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨none, Or.inl ⟨rfl, j, hu1, hu2⟩⟩
    · exact ⟨some b, Or.inr ⟨b, rfl, hb, hu1, hu2⟩⟩
  choose β hβ using hchoice
  refine ⟨a, β, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [witnessSet_castWitness]
    simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
    intro b hb hba
    simp only [witnessSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨i, hi⟩ := hb
    rcases hβ i with ⟨hn, -⟩ | ⟨b', hb', hpb, -⟩
    · rw [hn] at hi; cases hi
    · rw [hi] at hb'
      cases hb'
      exact hne b hpb (by rw [← hba]; rfl)
  · intro i b hb
    simp only [castWitness, Option.map_eq_some_iff] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    rcases hβ i with ⟨hn, -⟩ | ⟨b'', hb'', -, h1, h2⟩
    · rw [hn] at hb'; cases hb'
    · rw [hb'] at hb''
      cases hb''
      exact ⟨h1, h2⟩
  · intro i hi
    simp only [castWitness, Option.map_eq_none_iff] at hi
    rcases hβ i with ⟨-, j, h1, h2⟩ | ⟨b, hb, -⟩
    · simp only [posSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨V j, ⟨⟨j, rfl⟩, h1⟩, h2⟩
    · rw [hi] at hb; cases hb
  · intro b hb
    simp only [witnessSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨i, hi⟩ := hb
    rcases hβ i with ⟨hn, -⟩ | ⟨b', hb', hpb, -⟩
    · rw [hn] at hi; cases hi
    · rw [hi] at hb'
      cases hb'
      exact hpb

end Witness

end ShrincsSecurity.ITSR

end
