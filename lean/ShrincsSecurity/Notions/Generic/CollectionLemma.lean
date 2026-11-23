module

public import ShrincsSecurity.Notions.Generic.HiddenSlice
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Collection queries are harmless in the ideal model

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Lemma 4.1**, classical part (i) and
the lower bound (lines 2564–2597), proved as in **Section D.2** (lines 6601–6748); the collection
experiments of **Definition 4.12** (lines 2438–2463) and their SM-TCR instance **Definition D.1**
(lines 6553–6598).

## Model

The collection `Th_λ` is one random oracle `Th : P × (T × X) → N`, sampled lazily: a tweak and a
message of the collection. Members are selected by the message (`Th_λ(P, ·, ·)` dispatches on the
message length), so distinct members have disjoint message sets and one random oracle on `T × X`
is the family of independent member oracles `Th_m(P, T, ·)` of the lemma.

A stand-alone property `Prop` is an interface `I` of Lemma C.9 (`HiddenSlice.Interface`): `Σ` is
its challenge oracle and `Φ` its winning condition, both evaluating the hidden slice
`Th(P', ·)`. Its `Reservation` data names the tweaks reserved by the challenge history (`res`),
the tweaks a challenge reserves (`chalRes`: its tweak, and for sm-tcr-excl also the partner
`ω(T)`), the challenge oracle's own refusal test, and the refusal answer `⊥`. The `Discipline`
hypotheses hold for the properties of Definition 4.12 whose challenge refusal depends only on the
challenge state and query (such as SM-TCR, SM-PRE, SM-UD, SM-DSPR, SM-TCR-EXCL; `S-TCR(Prop)` is
excluded because refusal due to no valid counter depends on the random slice values): a refused
challenge is answered `⊥` without effect; an accepted one evaluates the slice only at the tweaks it
reserves and reserves exactly those; `Φ` evaluates the slice only at reserved tweaks.

Note: `standAlone` removes the collection oracle `CollSpec`, while retaining the full collection
oracle `ROSpec P (T × X) N` in the adversary's direct evaluations (Step 3 of Appendix D.2 is
replaced by a second use of Lemma C.9 rather than simulating the other members locally).

The collection experiment (`collInterface`, Definition 4.12) adds the collection oracle to `Σ`
and enforces the reservation rule in both orders: a challenge is refused if a tweak it would
reserve was used by a collection query; a collection query is refused at a reserved tweak.

## Main statements

* `prEvent_game0_collInterface_le`: **Lemma 4.1 (i)**, generic. For every collection adversary
  `A` whose first stage evaluates `Th` at most `q` times, the stand-alone adversary
  `A' = standAlone I R A` (no collection queries, at most `q` first-stage evaluations) satisfies
  `Pr[collection experiment ⇒ 1](A) ≤ Pr[stand-alone experiment ⇒ 1](A') + 2q/|P|`.
* `game0_collInterface_liftAdv`, `prEvent_game0_liftAdv`: the lower bound; a stand-alone adversary
  is a collection adversary (`liftAdv`) with the same success probability.
* `prEvent_smtcrCollGame_le`, `prEvent_smtcrGame_eq`: both directions for SM-TCR of a member
  (Definition D.1), via `smtcr_discipline`.

## Proof

As in Section D.2, with the stand-alone simulation of Step 3 replaced by a second use of
Lemma C.9. (1) Lemma C.9 for the collection experiment: Game 0 to Game 1 costs `q/|P|`.
(2) `game1_collInterface_eq`, exact: in Game 1, `A'` answers collection queries from its own lazily
sampled table `Λ`, decides refusals from its own transcript (it tracks the tweaks reserved by its
accepted challenges and its own collection tweaks), and in the second stage answers evaluations of
`Th'` at `(P', x)` with `x` recorded in `Λ` from `Λ`, forwarding the others. Game 1's slice of the
collection experiment is `Λ` laid over the stand-alone slice (`projJ`); the two are disjoint
because `Λ` holds only unreserved tweaks, which stay unreserved, and the stand-alone slice is
evaluated only at reserved ones (`JInv`). (3) Lemma C.9 for the stand-alone experiment: Game 1 to
Game 0 costs `q/|P|`. Hence `2q/|P|`, where `q` counts first-stage evaluations only; this is the
paper's term `2ξ/|P|` (`q ≤ ξ`).

For the advantage notions (SM-UD, SM-DSPR) the paper charges `2ε` per advantage; applying
`prEvent_game0_collInterface_le` to each of the two branches (the branch fixed inside `Σ` and `Φ`)
gives `4q/|P|` for an advantage along this route. This is not formalised here.

## Deviations from the paper

* Tweak sets `T_m` are not modelled: every member admits every tweak (the paper's default
  `T_m = T`), so neither oracle refuses a tweak outside a tweak set.
* The paper assumes without loss of generality that `A` makes no refused query; here the
  oracles refuse and `A'` answers a clashing challenge locally with `⊥`, so no such assumption is
  needed.
* The bound `q` constrains the first stage's evaluations of `Th`; the second stage is not
  bounded (as in Lemma C.9). `A'` makes the first-stage evaluations of `A` one-for-one.
* SM-TCR (`smtcrInterface`): an index `j` outside `Q` makes the experiment output `0`; the member's
  messages enter the collection's message space through an embedding `emb : M → X`.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

namespace CollectionLemma

open HiddenSlice

/-! ## Simulation lemmas -/

section simulation

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- State projection for a computation whose queries all satisfy `Pq`: the projection need only
commute with the steps of the admitted queries. -/
theorem map_run_simulateQ_eq_of_allQueriesSatisfy {σ₁ σ₂ β : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂) (Pq : ι → Prop)
    (hproj : ∀ t, Pq t → ∀ s, Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec β) (hoa : oa.AllQueriesSatisfy Pq) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [← hproj t hoa.1 s, bind_map_left]
      exact bind_congr fun x => by simpa using ih x.1 (hoa.2 x.1) x.2

/-- Invariant preservation for a computation whose queries all satisfy `Pq`. -/
theorem simulateQ_run_preserves_inv_of_allQueriesSatisfy {τ β : Type}
    (impl : QueryImpl spec (StateT τ ProbComp)) (inv : τ → Prop) (Pq : ι → Prop)
    (hinv : ∀ t, Pq t → ∀ s, inv s → ∀ y ∈ support ((impl t).run s), inv y.2)
    (oa : OracleComp spec β) (hoa : oa.AllQueriesSatisfy Pq) (s : τ) (hs : inv s) :
    ∀ y ∈ support ((simulateQ impl oa).run s), inv y.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simpa using hs
  | query_bind t oa ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      intro y hy
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hy
      obtain ⟨x, hx, hyx⟩ := hy
      exact ih x.1 (hoa.2 x.1) x.2 (hinv t hoa.1 s hs x hx) y hyx

/-- Two nested stateful simulations as one simulation on the product of the states. -/
def fuse {σ τ : Type} (outer : QueryImpl spec' (StateT σ ProbComp))
    (inner : QueryImpl spec (StateT τ (OracleComp spec'))) :
    QueryImpl spec (StateT (σ × τ) ProbComp) := fun t =>
  StateT.mk fun st =>
    (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ outer ((inner t).run st.2)).run st.1

theorem fuse_run {σ τ : Type} (outer : QueryImpl spec' (StateT σ ProbComp))
    (inner : QueryImpl spec (StateT τ (OracleComp spec'))) (t : ι) (st : σ × τ) :
    (fuse outer inner t).run st =
      (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ outer ((inner t).run st.2)).run st.1 :=
  rfl

/-- Flattening two nested stateful simulations. -/
theorem run_simulateQ_run_simulateQ {σ τ β : Type} (outer : QueryImpl spec' (StateT σ ProbComp))
    (inner : QueryImpl spec (StateT τ (OracleComp spec'))) (oa : OracleComp spec β) (s : σ)
    (a : τ) :
    (simulateQ outer ((simulateQ inner oa).run a)).run s =
      (fun z => ((z.1, z.2.2), z.2.1)) <$> (simulateQ (fuse outer inner) oa).run (s, a) := by
  induction oa using OracleComp.inductionOn generalizing s a with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind, fuse_run, bind_map_left]
      exact bind_congr fun x => ih x.1.1 x.2 x.1.2

end simulation

/-! ## Slices read at a restricted set of points -/

section slice

variable {P D N : Type} [DecidableEq P] [DecidableEq D] [SampleableType N]

/-- A query to `unifSpec + SliceSpec D N` that is a private coin or a slice evaluation at a point
of `Q`. -/
def SliceIn (Q : D → Bool) : ℕ ⊕ D → Prop
  | .inl _ => True
  | .inr d => Q d = true

/-- Private coins run on any state leave it unchanged. -/
theorem run_simulateQ_coinImpl (τ : Type) {β : Type} (oa : ProbComp β) (s : τ) :
    (simulateQ (coinImpl τ) oa).run s = (fun x => (x, s)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind n oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, coinImpl_run, bind_assoc, pure_bind,
        ih, map_bind]

/-- The slice table outside `Q` replaced by `g₀`. -/
def patchSt (Q : D → Bool) (g₀ : Slice D N) (st : Table P D N × Slice D N) :
    Table P D N × Slice D N :=
  (st.1, fun d => if Q d then st.2 d else g₀ d)

omit [DecidableEq P] in
/-- A computation reading the slice only on `Q` cannot tell the slice table off `Q`. -/
theorem map_run_simulateQ_sliceImpl₁_patchSt (Q : D → Bool) (g₀ : Slice D N) {β : Type}
    (oa : OracleComp (unifSpec + SliceSpec D N) β) (hoa : oa.AllQueriesSatisfy (SliceIn Q))
    (st : Table P D N × Slice D N) :
    Prod.map id (patchSt Q g₀) <$> (simulateQ sliceImpl₁ oa).run st =
      (simulateQ sliceImpl₁ oa).run (patchSt Q g₀ st) := by
  refine map_run_simulateQ_eq_of_allQueriesSatisfy _ _ _ _ (fun t ht st => ?_) oa hoa st
  rcases t with n | d
  · exact map_coinImpl_run _ n st
  · change Q d = true at ht
    rw [sliceImpl₁_inr_run, sliceImpl₁_inr_run, Functor.map_map]
    refine map_lazyStep_eq _ _ _ _ _ _ _ (by simp [patchSt, ht]) (fun _ _ => rfl) fun v _ => ?_
    simp only [Prod.map_apply, id_eq, patchSt]
    congr 2
    funext d'
    by_cases hd : d' = d
    · subst hd; simp [ht]
    · simp [hd]

omit [DecidableEq P] in
/-- A computation reading the slice only on `Q` leaves the `Th` table and the slice table off `Q`
unchanged. -/
theorem frame_of_mem_support_sliceImpl₁ (Q : D → Bool) {β : Type}
    (oa : OracleComp (unifSpec + SliceSpec D N) β) (hoa : oa.AllQueriesSatisfy (SliceIn Q))
    (st : Table P D N × Slice D N) {z : β × (Table P D N × Slice D N)}
    (hz : z ∈ support ((simulateQ sliceImpl₁ oa).run st)) :
    z.2.1 = st.1 ∧ ∀ d, Q d = false → z.2.2 d = st.2 d := by
  refine simulateQ_run_preserves_inv_of_allQueriesSatisfy sliceImpl₁
    (fun t => t.1 = st.1 ∧ ∀ d, Q d = false → t.2 d = st.2 d) (SliceIn Q) ?_ oa hoa st
    ⟨rfl, fun _ _ => rfl⟩ z hz
  rintro (n | d) ht t hinv w hw
  · rw [mem_support_coinImpl_run hw]; exact hinv
  · change Q d = true at ht
    rw [sliceImpl₁_inr_run, support_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨hinv.1, fun d' hd' => ?_⟩
    rw [(mem_support_lazyStep hu).1, Function.update_of_ne (by rintro rfl; simp_all)]
    exact hinv.2 d' hd'

/-- The overlay of the simulator's table `Λ` over the slice table `g`. -/
def overlay (Λ g : Slice D N) : Slice D N := fun d => (Λ d).or (g d)

/-- An evaluation of `Th` by the patched second stage: at `(P', d)` with `d` recorded in `Λ` it is
answered from `Λ`; every other evaluation is forwarded. -/
def patchStep (Λ : Slice D N) (P' : P) (x : P × D) : OracleComp (unifSpec + ROSpec P D N) N :=
  if x.1 = P' then
    (Λ x.2).elim (liftM ((unifSpec + ROSpec P D N).query (.inr x))) pure
  else liftM ((unifSpec + ROSpec P D N).query (.inr x))

/-- The second stage of the stand-alone adversary: `patchStep` on evaluations, private coins
forwarded. -/
def patchImpl (Λ : Slice D N) (P' : P) :
    QueryImpl (unifSpec + ROSpec P D N) (OracleComp (unifSpec + ROSpec P D N)) :=
  (fun n => (liftM ((unifSpec + ROSpec P D N).query (.inl n)) :
      OracleComp (unifSpec + ROSpec P D N) (unifSpec.Range n)) : QueryImpl unifSpec _) +
    (fun x => patchStep Λ P' x : QueryImpl (ROSpec P D N) _)

omit [DecidableEq D] [SampleableType N] in
theorem patchImpl_inl (Λ : Slice D N) (P' : P) (n : ℕ) :
    patchImpl Λ P' (.inl n) = (liftM ((unifSpec + ROSpec P D N).query (.inl n)) :
      OracleComp (unifSpec + ROSpec P D N) (unifSpec.Range n)) := rfl

omit [DecidableEq D] [SampleableType N] in
theorem patchImpl_inr (Λ : Slice D N) (P' : P) (x : P × D) :
    patchImpl Λ P' (.inr x) = patchStep Λ P' x := rfl

/-- The patched second stage on `Th'` is the second stage on `Th'` with `Λ` laid over `g`. -/
theorem map_run_simulateQ_patchImpl (Λ : Slice D N) (P' : P) {β : Type}
    (oa : OracleComp (unifSpec + ROSpec P D N) β) (st : Table P D N × Slice D N) :
    Prod.map id (fun st : Table P D N × Slice D N => (st.1, overlay Λ st.2)) <$>
        (simulateQ (thPrimeImpl P') (simulateQ (patchImpl Λ P') oa)).run st =
      (simulateQ (thPrimeImpl P') oa).run (st.1, overlay Λ st.2) := by
  rw [← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _
    (fun st : Table P D N × Slice D N => (st.1, overlay Λ st.2)) (fun t st => ?_) oa st
  rcases t with n | x
  · rw [QueryImpl.apply_compose, patchImpl_inl, simulateQ_spec_query]
    exact map_coinImpl_run _ n st
  · rw [QueryImpl.apply_compose, patchImpl_inr, patchStep, thPrimeImpl_inr_run]
    by_cases hx : x.1 = P'
    · simp only [hx, ↓reduceIte]
      cases hΛ : Λ x.2 with
      | some y =>
        simp only [Option.elim_some, simulateQ_pure, StateT.run_pure, map_pure,
          Prod.map_apply, id_eq]
        unfold lazyStep
        simp [overlay, hΛ]
      | none =>
        simp only [Option.elim_none, simulateQ_spec_query, thPrimeImpl_inr_run, hx,
          ↓reduceIte, Functor.map_map]
        refine map_lazyStep_eq _ _ _ _ _ _ _ (by simp [overlay, hΛ]) (fun _ _ => rfl)
          fun v _ => ?_
        simp only [Prod.map_apply, id_eq]
        congr 2
        funext d'
        by_cases hd : d' = x.2
        · subst hd; simp [overlay, hΛ]
        · simp [overlay, hd]
    · simp only [hx, ↓reduceIte, simulateQ_spec_query, thPrimeImpl_inr_run, Functor.map_map]
      rfl

end slice

/-- `f <$> oa = g <$> oa` when `f` and `g` agree on the support of `oa`. -/
theorem map_congr_of_mem_support' {β γ : Type} {oa : ProbComp β} {f g : β → γ}
    (h : ∀ x ∈ support oa, f x = g x) : f <$> oa = g <$> oa := by
  simp only [map_eq_bind_pure_comp]
  exact bind_congr_of_forall_mem_support _ fun x hx => by simp [h x hx]

/-! ## The collection experiment and the stand-alone simulator -/

section collection

variable {P T X N : Type} [DecidableEq P] [DecidableEq T] [DecidableEq X] [SampleableType N]
variable {ιc : Type} {cs : OracleSpec ιc} {σ α S : Type}

/-- The collection oracle `Th_λ(P', ·, ·)` of Definition 4.12: a tweak and a message, answered by
`none` (`⊥`) when refused. -/
abbrev CollSpec (T X N : Type) : OracleSpec (T × X) := (T × X) →ₒ Option N

/-- The oracles of the stand-alone first stage: private coins, `Th`, and the challenge oracle. -/
abbrev SASpec (P T X N : Type) (cs : OracleSpec ιc) := unifSpec + (ROSpec P (T × X) N + cs)

/-- **Reservation data** of a stand-alone property `Prop` (Definition 4.12). -/
structure Reservation (cs : OracleSpec ιc) (σ T : Type) where
  /-- The tweaks reserved by the challenge history recorded in a state of `Σ`. -/
  res : σ → T → Bool
  /-- The tweaks a challenge query reserves: its own tweak (and, for sm-tcr-excl, its partner). -/
  chalRes : ιc → T → Bool
  /-- The challenge oracle's own refusal test (the bound `p`, a repeated tweak, ...). -/
  refused : σ → ιc → Bool
  /-- The refusal answer `⊥`. -/
  refuse : (d : ιc) → cs.Range d
  /-- Whether an answer is not the refusal. -/
  accepted : (d : ιc) → cs.Range d → Bool

/-- **Reservation discipline** of a stand-alone property whose refusal depends only on the
challenge state and query (e.g. SM-TCR, SM-PRE, SM-UD, SM-DSPR, SM-TCR-EXCL; not `S-TCR(Prop)`,
whose refusal depends on the slice values). A refused challenge is answered `⊥` without effect; an
accepted challenge evaluates the slice only at the tweaks it reserves and reserves exactly those;
the winning condition `Φ` evaluates the slice only at reserved tweaks. -/
structure Discipline (I : Interface (T × X) N cs σ α) (R : Reservation cs σ T) : Prop where
  accepted_refuse : ∀ d, R.accepted d (R.refuse d) = false
  run_of_refused : ∀ s d, R.refused s d = true → (I.impl d).run s = pure (R.refuse d, s)
  impl_queries : ∀ s d, R.refused s d = false →
    ((I.impl d).run s).AllQueriesSatisfy (SliceIn fun x : T × X => R.chalRes d x.1)
  impl_support : ∀ s d, R.refused s d = false → ∀ z ∈ support ((I.impl d).run s),
    R.accepted d z.1 = true ∧ R.res z.2 = fun t => R.res s t || R.chalRes d t
  pred_queries : ∀ s a, (I.pred s a).AllQueriesSatisfy (SliceIn fun x : T × X => R.res s x.1)

/-- The challenge oracle in the collection experiment: refused if a collection tweak is among the
tweaks it would reserve, otherwise the stand-alone challenge oracle. -/
def collChal (I : Interface (T × X) N cs σ α) (R : Reservation cs σ T) (d : ιc) :
    StateT (σ × List T) (OracleComp (unifSpec + SliceSpec (T × X) N)) (cs.Range d) :=
  StateT.mk fun st => if st.2.any (R.chalRes d) then pure (R.refuse d, st)
    else (fun z => (z.1, (z.2, st.2))) <$> (I.impl d).run st.1

/-- The collection oracle `Th_λ(P', ·, ·)`: refused at a reserved tweak, otherwise the tweak is
recorded and the slice evaluated. -/
def collEval (R : Reservation cs σ T) (x : T × X) :
    StateT (σ × List T) (OracleComp (unifSpec + SliceSpec (T × X) N)) (Option N) :=
  StateT.mk fun st => if R.res st.1 x.1 then pure (none, st)
    else (fun v => (some v, (st.1, x.1 :: st.2))) <$>
      (liftM ((unifSpec + SliceSpec (T × X) N).query (.inr x)) :
        OracleComp (unifSpec + SliceSpec (T × X) N) N)

/-- **The collection experiment** of Definition 4.12 as an interface of Lemma C.9: `Σ` is the
challenge oracle together with the collection oracle, with the reservation rule enforced in both
orders; `Φ` is the winning condition of the stand-alone property. -/
def collInterface (I : Interface (T × X) N cs σ α) (R : Reservation cs σ T) :
    Interface (T × X) N (cs + CollSpec T X N) (σ × List T) α where
  init := (I.init, [])
  impl := (fun d => collChal I R d : QueryImpl cs _) +
    (fun x => collEval R x : QueryImpl (CollSpec T X N) _)
  pred s a := I.pred s.1 a

/-- The state of the stand-alone simulator: its table `Λ`, its collection tweaks, and the tweaks
reserved by its accepted challenges. -/
abbrev SimState (T X N : Type) := Slice (T × X) N × List T × (T → Bool)

/-- The monad of the stand-alone simulator. -/
abbrev SimM (P T X N : Type) (cs : OracleSpec ιc) :=
  StateT (SimState T X N) (OracleComp (SASpec P T X N cs))

/-- The simulator's challenge query: answered `⊥` locally on a clash with its collection tweaks,
otherwise relayed; an accepted answer reserves the challenge's tweaks. -/
def advChal (R : Reservation cs σ T) (d : ιc) : SimM P T X N cs (cs.Range d) :=
  StateT.mk fun a => if a.2.1.any (R.chalRes d) then pure (R.refuse d, a)
    else (fun r => (r, if R.accepted d r then (a.1, a.2.1, fun t => a.2.2 t || R.chalRes d t)
        else a)) <$>
      (liftM ((SASpec P T X N cs).query (.inr (.inr d))) :
        OracleComp (SASpec P T X N cs) (cs.Range d))

/-- The simulator's collection query: refused at a reserved tweak, otherwise answered from the
lazily sampled table `Λ` and the tweak recorded. -/
def advColl (x : T × X) : SimM P T X N cs (Option N) :=
  StateT.mk fun a => if a.2.2 x.1 then pure (none, a)
    else (fun z => (some z.1, (z.2, x.1 :: a.2.1, a.2.2))) <$>
      (liftM (lazyStep ($ᵗ N) a.1 x) : OracleComp (SASpec P T X N cs) _)

/-- The simulator forwards a private coin. -/
def advCoin (n : ℕ) : SimM P T X N cs (unifSpec.Range n) :=
  StateT.mk fun a => (fun u => (u, a)) <$>
    (liftM ((SASpec P T X N cs).query (.inl n)) :
      OracleComp (SASpec P T X N cs) (unifSpec.Range n))

/-- The simulator forwards an evaluation of `Th`. -/
def advRO (x : P × (T × X)) : SimM P T X N cs N :=
  StateT.mk fun a => (fun u => (u, a)) <$>
    (liftM ((SASpec P T X N cs).query (.inr (.inl x))) : OracleComp (SASpec P T X N cs) N)

/-- The first stage of the stand-alone adversary `A'` runs `A₁` through this handler: coins and
`Th` forwarded, challenges relayed (`advChal`), collection queries simulated (`advColl`). -/
def advImpl (R : Reservation cs σ T) :
    QueryImpl (unifSpec + (ROSpec P (T × X) N + (cs + CollSpec T X N))) (SimM P T X N cs) :=
  (fun n => advCoin n : QueryImpl unifSpec (SimM P T X N cs)) +
  ((fun x => advRO x : QueryImpl (ROSpec P (T × X) N) (SimM P T X N cs)) +
  ((fun d => advChal R d : QueryImpl cs (SimM P T X N cs)) +
    (fun x => advColl x : QueryImpl (CollSpec T X N) (SimM P T X N cs))))

variable [SampleableType P]

/-- **The stand-alone adversary `A'`** built from a collection adversary `A`: it makes no
collection queries and at most as many first-stage evaluations of `Th` as `A`. The first stage
runs `A₁` through `advImpl` and passes `Λ` on; the second stage patches `Th(P', ·)` with `Λ`. -/
def standAlone {q : ℕ} (I : Interface (T × X) N cs σ α) (R : Reservation cs σ T)
    (A : Adversary P (T × X) N (cs + CollSpec T X N) S α q) :
    Adversary P (T × X) N cs (S × Slice (T × X) N) α q where
  A1 := (fun z => (z.1, z.2.1)) <$>
    (simulateQ (advImpl R) A.A1).run ((fun _ => none), [], R.res I.init)
  A2 s P' := simulateQ (patchImpl s.2 P') (A.A2 s.1 P')
  queryBound := by
    rw [isQueryBoundP_map_iff]
    refine IsQueryBoundP.simulateQ_run_of_step A.queryBound (fun t ht a => ?_)
      (fun t ht a => ?_) _
    · rcases t with n | x | d | x
      · exact absurd ht (by simp [IsROQuery])
      · change IsQueryBoundP ((advRO (N := N) (cs := cs) x).run a) (IsROQuery P (T × X)) 1
        rw [advRO, StateT.run_mk, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        exact fun _ => Nat.one_pos
      · exact absurd ht (by simp [IsROQuery])
      · exact absurd ht (by simp [IsROQuery])
    · rcases t with n | x | d | x
      · change IsQueryBoundP ((advCoin (P := P) (T := T) (X := X) (N := N) (cs := cs) n).run a)
          (IsROQuery P (T × X)) 0
        rw [advCoin, StateT.run_mk, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        simp [IsROQuery]
      · exact absurd trivial ht
      · change IsQueryBoundP ((advChal (P := P) (X := X) (N := N) R d).run a)
          (IsROQuery P (T × X)) 0
        unfold advChal
        rw [StateT.run_mk]
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          simp [IsROQuery]
      · change IsQueryBoundP ((advColl (P := P) (cs := cs) x).run a) (IsROQuery P (T × X)) 0
        unfold advColl
        rw [StateT.run_mk]
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · rw [isQueryBoundP_map_iff]
          refine IsQueryBoundP.of_imp (p' := fun t => t.isRight = true) (fun t ht => ?_)
            (isQueryBoundP_liftM_isRight _)
          rcases t with _ | _ | _ <;> simp_all [IsROQuery]

/-! ## Step 2: Game 1 of the collection experiment is Game 1 of `A'` -/

/-- Game 1's first stage run by `A'`: Game 1's handler under the simulator's handler, fused. -/
abbrev jointImpl (I : Interface (T × X) N cs σ α) (R : Reservation cs σ T) :=
  fuse (phase1₁ (P := P) I) (advImpl (P := P) (X := X) (N := N) R)

/-- The state of `jointImpl`: Game 1's tables and the state of `Σ`, and the simulator's state. -/
abbrev JState (P T X N σ : Type) :=
  ((Table P (T × X) N × Slice (T × X) N) × σ) × SimState T X N

/-- The state of the collection experiment's Game 1 seen in a run of `A'`: the slice `g` of the
collection experiment is the simulator's table `Λ` laid over the slice of the stand-alone one. -/
def projJ (st : JState P T X N σ) : (Table P (T × X) N × Slice (T × X) N) × (σ × List T) :=
  ((st.1.1.1, overlay st.2.1 st.1.1.2), (st.1.2, st.2.2.1))

/-- The invariant of a run of `A'` in Game 1: the simulator tracks the reserved tweaks exactly,
the stand-alone slice is filled only at reserved tweaks, `Λ` only at the simulator's collection
tweaks, and those are unreserved. -/
def JInv (R : Reservation cs σ T) (st : JState P T X N σ) : Prop :=
  st.2.2.2 = R.res st.1.2 ∧ (∀ x, st.1.1.2 x ≠ none → R.res st.1.2 x.1 = true) ∧
    (∀ x, st.2.1 x ≠ none → x.1 ∈ st.2.2.1) ∧ ∀ t ∈ st.2.2.1, R.res st.1.2 t = false

variable (I : Interface (T × X) N cs σ α) (R : Reservation cs σ T)

omit [SampleableType P] in
theorem jointImpl_coin_run (n : ℕ) (st : JState P T X N σ) :
    (jointImpl I R (.inl n)).run st =
      (fun u => (u, st)) <$> (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
  rw [fuse_run]
  change (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (phase1₁ I) ((advCoin (P := P) (T := T) (X := X) (N := N) (cs := cs) n).run
      st.2)).run st.1 = _
  rw [advCoin, StateT.run_mk, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  change _ <$> (_ <$> (coinImpl _ n).run st.1) = _
  rw [coinImpl_run]
  simp

omit [SampleableType P] in
theorem jointImpl_ro_run (x : P × (T × X)) (st : JState P T X N σ) :
    (jointImpl I R (.inr (.inl x))).run st =
      (fun z => (z.1, (((z.2, st.1.1.2), st.1.2), st.2))) <$> lazyStep ($ᵗ N) st.1.1.1 x := by
  rw [fuse_run]
  change (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (phase1₁ I) ((advRO (N := N) (cs := cs) x).run st.2)).run st.1 = _
  rw [advRO, StateT.run_mk, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  change _ <$> (_ <$> ((fun z => (z.1, ((z.2, st.1.1.2), st.1.2))) <$>
    lazyStep ($ᵗ N) st.1.1.1 x)) = _
  simp only [Functor.map_map]

omit [SampleableType P] in
theorem jointImpl_chal_run (d : ιc) (st : JState P T X N σ) :
    (jointImpl I R (.inr (.inr (.inl d)))).run st =
      if st.2.2.1.any (R.chalRes d) then pure (R.refuse d, st)
      else (fun z => (z.1.1, ((z.2, z.1.2), if R.accepted d z.1.1 then
          (st.2.1, st.2.2.1, fun t => st.2.2.2 t || R.chalRes d t) else st.2))) <$>
        (simulateQ sliceImpl₁ ((I.impl d).run st.1.2)).run st.1.1 := by
  rw [fuse_run]
  change (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (phase1₁ I) ((advChal (P := P) (X := X) (N := N) R d).run st.2)).run st.1 = _
  rw [advChal, StateT.run_mk]
  split_ifs
  · simp
  · rw [simulateQ_map, simulateQ_spec_query, StateT.run_map]
    change _ <$> (_ <$> (sigmaStep I sliceImpl₁ d).run st.1) = _
    rw [sigmaStep_run]
    simp only [Functor.map_map]

omit [SampleableType P] in
theorem jointImpl_coll_run (x : T × X) (st : JState P T X N σ) :
    (jointImpl I R (.inr (.inr (.inr x)))).run st =
      if st.2.2.2 x.1 then pure (none, st)
      else (fun z => (some z.1, (st.1, (z.2, x.1 :: st.2.2.1, st.2.2.2)))) <$>
        lazyStep ($ᵗ N) st.2.1 x := by
  rw [fuse_run]
  change (fun z => (z.1.1, (z.2, z.1.2))) <$>
    (simulateQ (phase1₁ I) ((advColl (P := P) (cs := cs) x).run st.2)).run st.1 = _
  rw [advColl, StateT.run_mk]
  split_ifs
  · simp
  · rw [simulateQ_map, StateT.run_map, phase1₁, QueryImpl.simulateQ_add_liftM_left,
      run_simulateQ_coinImpl]
    simp only [Functor.map_map]

omit [SampleableType P] in
theorem collInterface_chal_run (d : ιc)
    (st : (Table P (T × X) N × Slice (T × X) N) × (σ × List T)) :
    (phase1₁ (collInterface I R) (.inr (.inr (.inl d)))).run st =
      if st.2.2.any (R.chalRes d) then pure (R.refuse d, st)
      else (fun z => (z.1.1, (z.2, (z.1.2, st.2.2)))) <$>
        (simulateQ sliceImpl₁ ((I.impl d).run st.2.1)).run st.1 := by
  change (sigmaStep (collInterface I R) sliceImpl₁ (.inl d)).run st = _
  rw [sigmaStep_run]
  change _ <$> (simulateQ sliceImpl₁ ((collChal I R d).run st.2)).run st.1 = _
  rw [collChal, StateT.run_mk]
  split_ifs
  · simp
  · rw [simulateQ_map, StateT.run_map, Functor.map_map]

omit [SampleableType P] in
theorem collInterface_coll_run (x : T × X)
    (st : (Table P (T × X) N × Slice (T × X) N) × (σ × List T)) :
    (phase1₁ (collInterface I R) (.inr (.inr (.inr x)))).run st =
      if R.res st.2.1 x.1 then pure (none, st)
      else (fun z => (some z.1, ((st.1.1, z.2), (st.2.1, x.1 :: st.2.2)))) <$>
        lazyStep ($ᵗ N) st.1.2 x := by
  change (sigmaStep (collInterface I R) sliceImpl₁ (.inr x)).run st = _
  rw [sigmaStep_run]
  change _ <$> (simulateQ sliceImpl₁ ((collEval (N := N) R x).run st.2)).run st.1 = _
  rw [collEval, StateT.run_mk]
  split_ifs
  · simp
  · rw [run_simulateQ_sliceImpl₁_query, Functor.map_map]

variable {I R}

omit [DecidableEq T] [DecidableEq X] [SampleableType N] [SampleableType P] in
/-- The invariant keeps `Λ` off the tweaks a challenge that passes the clash test reserves. -/
theorem overlay_eq_of_chalRes {Λ : Slice (T × X) N} {L : List T} {d : ιc}
    (hΛ : ∀ x, Λ x ≠ none → x.1 ∈ L) (hc : ∀ c ∈ L, R.chalRes d c = false) {x : T × X}
    (hx : R.chalRes d x.1 = true) : Λ x = none := by
  by_contra hne
  simp [hc _ (hΛ x hne)] at hx

omit [SampleableType P] in
/-- `projJ` commutes with every step of `jointImpl` under the invariant. -/
theorem jointImpl_proj (hR : Discipline I R) (t : (unifSpec + (ROSpec P (T × X) N +
    (cs + CollSpec T X N))).Domain) (st : JState P T X N σ) (hst : JInv R st) :
    Prod.map id projJ <$> (jointImpl I R t).run st =
      (phase1₁ (collInterface I R) t).run (projJ st) := by
  obtain ⟨⟨⟨H, g⟩, s⟩, Λ, L, ρ⟩ := st
  obtain ⟨hρ, hg, hΛ, hL⟩ := hst
  dsimp only at hρ hg hΛ hL
  subst hρ
  rcases t with n | x | d | x
  · rw [jointImpl_coin_run I R]
    change _ = (coinImpl _ n).run _
    rw [coinImpl_run]
    simp [projJ]
  · rw [jointImpl_ro_run I R]
    change _ = (fun z => (z.1, ((z.2, overlay Λ g), (s, L)))) <$> lazyStep ($ᵗ N) H x
    simp only [Functor.map_map]
    rfl
  · rw [jointImpl_chal_run I R, collInterface_chal_run I R]
    dsimp only [projJ]
    by_cases hc : L.any (R.chalRes d) = true
    · simp [hc, projJ]
    · have hc' : ∀ c ∈ L, R.chalRes d c = false := by simpa using hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      cases hr : R.refused s d
      · have hq := hR.impl_queries s d hr
        have hpatch : patchSt (fun x : T × X => R.chalRes d x.1) (overlay Λ g) (H, g) =
            (H, overlay Λ g) := by
          refine Prod.ext rfl (funext fun x => ?_)
          dsimp only [patchSt]
          split_ifs with hx
          · simp [overlay, overlay_eq_of_chalRes hΛ hc' hx]
          · rfl
        rw [← hpatch, ← map_run_simulateQ_sliceImpl₁_patchSt _ _ _ hq, Functor.map_map,
          Functor.map_map]
        refine map_congr_of_mem_support' fun z hz => ?_
        obtain ⟨-, hfr⟩ := frame_of_mem_support_sliceImpl₁ _ _ hq _ hz
        obtain ⟨hacc, -⟩ := hR.impl_support s d hr z.1
          (mem_support_of_mem_support_simulateQ_run _ _ _ hz)
        simp only [hacc, ↓reduceIte, Prod.map_apply, id_eq, projJ]
        refine Prod.ext rfl (Prod.ext (Prod.ext rfl (funext fun x => ?_)) rfl)
        by_cases hx : R.chalRes d x.1 = true
        · simp [overlay, patchSt, hx, overlay_eq_of_chalRes hΛ hc' hx]
        · simp only [Bool.not_eq_true] at hx
          simp [overlay, patchSt, hx, hfr x hx]
      · rw [hR.run_of_refused s d hr]
        simp [hR.accepted_refuse, projJ]
  · rw [jointImpl_coll_run I R, collInterface_coll_run I R]
    dsimp only [projJ]
    by_cases hx : R.res s x.1 = true
    · simp [hx, projJ]
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, Functor.map_map]
      have hgx : g x = none := by
        by_contra hne
        exact hx (hg x hne)
      refine map_lazyStep_eq _ _ _ _ _ _ _ (by simp [overlay, hgx]) (fun _ _ => rfl)
        fun v _ => ?_
      simp only [Prod.map_apply, id_eq, projJ]
      refine Prod.ext rfl (Prod.ext (Prod.ext rfl (funext fun y => ?_)) rfl)
      by_cases hy : y = x
      · subst hy; simp [overlay]
      · simp [overlay, hy]

omit [SampleableType P] in
/-- Every step of `jointImpl` preserves the invariant. -/
theorem jointImpl_inv (hR : Discipline I R) (t : (unifSpec + (ROSpec P (T × X) N +
    (cs + CollSpec T X N))).Domain) (st : JState P T X N σ) (hst : JInv R st) :
    ∀ y ∈ support ((jointImpl I R t).run st), JInv R y.2 := by
  obtain ⟨⟨⟨H, g⟩, s⟩, Λ, L, ρ⟩ := st
  intro y hy
  rcases t with n | x | d | x
  · rw [jointImpl_coin_run I R, support_map] at hy
    obtain ⟨u, -, rfl⟩ := hy
    exact hst
  · rw [jointImpl_ro_run I R, support_map] at hy
    obtain ⟨u, -, rfl⟩ := hy
    exact hst
  · obtain ⟨hρ, hg, hΛ, hL⟩ := hst
    dsimp only at hρ hg hΛ hL
    subst hρ
    rw [jointImpl_chal_run I R] at hy
    dsimp only at hy
    by_cases hc : L.any (R.chalRes d) = true
    · simp only [hc, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨rfl, hg, hΛ, hL⟩
    · have hc' : ∀ c ∈ L, R.chalRes d c = false := by simpa using hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, support_map, Set.mem_image] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      cases hr : R.refused s d
      · obtain ⟨-, hfr⟩ := frame_of_mem_support_sliceImpl₁ _ _ (hR.impl_queries s d hr) _ hz
        obtain ⟨hacc, hres⟩ := hR.impl_support s d hr z.1
          (mem_support_of_mem_support_simulateQ_run _ _ _ hz)
        simp only [hacc, ↓reduceIte]
        refine ⟨hres.symm, fun x hx => ?_, hΛ, fun t ht => ?_⟩
        · rw [hres]
          by_cases hxc : R.chalRes d x.1 = true
          · simp [hxc]
          · simp only [Bool.not_eq_true] at hxc
            rw [hfr x hxc] at hx
            simp [hg x hx]
        · rw [hres]
          simp [hL t ht, hc' t ht]
      · rw [hR.run_of_refused s d hr] at hz
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        simp only [hR.accepted_refuse, Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, hg, hΛ, hL⟩
  · obtain ⟨hρ, hg, hΛ, hL⟩ := hst
    dsimp only at hρ hg hΛ hL
    subst hρ
    rw [jointImpl_coll_run I R] at hy
    dsimp only at hy
    by_cases hx : R.res s x.1 = true
    · simp only [hx, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨rfl, hg, hΛ, hL⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, support_map, Set.mem_image] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [(mem_support_lazyStep hz).1]
      refine ⟨rfl, hg, fun y hy => ?_, fun t ht => ?_⟩
      · dsimp only at hy ⊢
        by_cases hyx : y = x
        · subst hyx; exact List.mem_cons_self
        · rw [Function.update_of_ne hyx] at hy
          exact List.mem_cons_of_mem _ (hΛ y hy)
      · rcases List.mem_cons.1 ht with rfl | ht
        · simpa using hx
        · exact hL t ht

omit [SampleableType P] in
/-- After the first stage, the two Game 1 runs agree: `A'`'s patched second stage on `Th'` is
`A₂` on `Th'` with `Λ` laid over `g`, and `Φ` reads only reserved tweaks, where `Λ` is empty. -/
theorem tail₁_collInterface_eq (hR : Discipline I R) {q : ℕ}
    (A : Adversary P (T × X) N (cs + CollSpec T X N) S α q) (P' : P)
    (z : S × JState P T X N σ) (hz : JInv R z.2) :
    tail₁ (collInterface I R) A P' (z.1, projJ z.2) =
      tail₁ I (standAlone I R A) P' ((z.1, z.2.2.1), z.2.1) := by
  obtain ⟨x, ⟨⟨H, g⟩, s⟩, Λ, L, ρ⟩ := z
  obtain ⟨-, -, hΛ, hL⟩ := hz
  dsimp only at hΛ hL
  unfold tail₁
  dsimp only [projJ, standAlone]
  rw [← map_run_simulateQ_patchImpl Λ P' (A.A2 x P') (H, g), bind_map_left]
  refine bind_congr fun w => ?_
  have hpatch : patchSt (fun y : T × X => R.res s y.1) (overlay Λ w.2.2) w.2 =
      (w.2.1, overlay Λ w.2.2) := by
    refine Prod.ext rfl (funext fun y => ?_)
    dsimp only [patchSt]
    split_ifs with hy
    · have : Λ y = none := by
        by_contra hne
        simp [hL _ (hΛ y hne)] at hy
      simp [overlay, this]
    · rfl
  change ((simulateQ sliceImpl₁ (I.pred s w.1)).run (w.2.1, overlay Λ w.2.2) >>=
    fun v => pure v.1) = _
  rw [← hpatch, ← map_run_simulateQ_sliceImpl₁_patchSt _ _ _ (hR.pred_queries s w.1),
    bind_map_left]
  rfl

/-- **Step 2 of the proof of Lemma 4.1**: removing the collection oracle in Game 1 is exact. -/
theorem game1_collInterface_eq (hR : Discipline I R) {q : ℕ}
    (A : Adversary P (T × X) N (cs + CollSpec T X N) S α q) :
    game1 (collInterface I R) A = game1 I (standAlone I R A) := by
  unfold game1
  refine bind_congr fun P' => ?_
  have h0 : JInv R ((((fun _ => none, fun _ => none), I.init),
      ((fun _ => none), [], R.res I.init)) : JState P T X N σ) :=
    ⟨rfl, by simp, by simp, by simp⟩
  have hA1 : (simulateQ (phase1₁ I) (standAlone I R A).A1).run
      ((fun _ => none, fun _ => none), I.init) =
      (fun z => ((z.1, z.2.2.1), z.2.1)) <$> (simulateQ (jointImpl I R) A.A1).run
        (((fun _ => none, fun _ => none), I.init), ((fun _ => none), [], R.res I.init)) := by
    simp only [standAlone, simulateQ_map, StateT.run_map, run_simulateQ_run_simulateQ,
      Functor.map_map]
  have hproj0 : (((fun _ => none, fun _ => none), (collInterface I R).init) :
      (Table P (T × X) N × Slice (T × X) N) × (σ × List T)) =
      projJ (((fun _ => none, fun _ => none), I.init), ((fun _ => none), [], R.res I.init)) :=
    rfl
  rw [hA1, bind_map_left, hproj0, ← map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (JInv R) projJ
    (jointImpl_inv hR) (jointImpl_proj hR) A.A1 _ h0, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  exact tail₁_collInterface_eq hR A P' z
    (simulateQ_run_preserves_inv_of_query _ (JInv R) (jointImpl_inv hR) A.A1 _ h0 z hz)

/-- **Lemma 4.1 (i)**, generic form (main paper lines 2564–2597, proof Section D.2, lines
6601–6748). In the random-oracle model, for every collection adversary `A` whose first stage
evaluates `Th` at most `q` times, the stand-alone adversary `A'` (`standAlone`, no collection
queries, at most `q` first-stage evaluations) satisfies
`Pr[collection experiment ⇒ 1](A) ≤ Pr[stand-alone experiment ⇒ 1](A') + 2q/|P|`. -/
theorem prEvent_game0_collInterface_le [Fintype P] (hR : Discipline I R) {q : ℕ}
    (A : Adversary P (T × X) N (cs + CollSpec T X N) S α q) :
    Pr{let b ← game0 (collInterface I R) A}[b = true] ≤
      Pr{let b ← game0 I (standAlone I R A)}[b = true] + 2 * q / Fintype.card P := by
  have h1 := (prEvent_game_le (collInterface I R) A).1
  have h2 := (prEvent_game_le I (standAlone I R A)).2
  rw [game1_collInterface_eq hR A] at h1
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add_left h2 _
    _ = _ := by rw [add_assoc, ← ENNReal.add_div, ← two_mul]

/-! ## The other direction: an adversary may ignore the collection oracle -/

/-- The oracles of the collection first stage: private coins, `Th`, the challenge oracle and the
collection oracle. -/
abbrev CSpec (P T X N : Type) (cs : OracleSpec ιc) :=
  unifSpec + (ROSpec P (T × X) N + (cs + CollSpec T X N))

/-- A stand-alone first stage seen as a collection first stage that never queries the collection
oracle. -/
def liftImpl : QueryImpl (SASpec P T X N cs) (OracleComp (CSpec P T X N cs)) :=
  (fun n => (liftM ((CSpec P T X N cs).query (.inl n)) :
      OracleComp (CSpec P T X N cs) (unifSpec.Range n)) : QueryImpl unifSpec _) +
  ((fun x => (liftM ((CSpec P T X N cs).query (.inr (.inl x))) : OracleComp (CSpec P T X N cs) N) :
      QueryImpl (ROSpec P (T × X) N) _) +
    (fun d => (liftM ((CSpec P T X N cs).query (.inr (.inr (.inl d)))) :
      OracleComp (CSpec P T X N cs) (cs.Range d)) : QueryImpl cs _))

/-- A stand-alone adversary as a collection adversary that ignores the collection oracle. -/
def liftAdv {q : ℕ} (B : Adversary P (T × X) N cs S α q) :
    Adversary P (T × X) N (cs + CollSpec T X N) S α q where
  A1 := simulateQ liftImpl B.A1
  A2 := B.A2
  queryBound := by
    refine IsQueryBoundP.simulateQ_of_step B.queryBound (fun t ht => ?_) (fun t ht => ?_)
    · rcases t with n | x | d
      · exact absurd ht (by simp [IsROQuery])
      · change IsQueryBoundP (liftM ((CSpec P T X N cs).query (.inr (.inl x))) :
          OracleComp (CSpec P T X N cs) N) (IsROQuery P (T × X)) 1
        rw [isQueryBoundP_query_iff]
        exact fun _ => Nat.one_pos
      · exact absurd ht (by simp [IsROQuery])
    · rcases t with n | x | d
      · change IsQueryBoundP (liftM ((CSpec P T X N cs).query (.inl n)) :
          OracleComp (CSpec P T X N cs) (unifSpec.Range n)) (IsROQuery P (T × X)) 0
        rw [isQueryBoundP_query_iff]
        simp [IsROQuery]
      · exact absurd trivial ht
      · change IsQueryBoundP (liftM ((CSpec P T X N cs).query (.inr (.inr (.inl d)))) :
          OracleComp (CSpec P T X N cs) (cs.Range d)) (IsROQuery P (T × X)) 0
        rw [isQueryBoundP_query_iff]
        simp [IsROQuery]

/-- **Lemma 4.1, lower bound** ("an adversary may ignore the collection oracle", lines 2582 and
6652): the collection experiment run by the lifted adversary is the stand-alone experiment. -/
theorem game0_collInterface_liftAdv {q : ℕ} (I : Interface (T × X) N cs σ α)
    (R : Reservation cs σ T) (B : Adversary P (T × X) N cs S α q) :
    game0 (collInterface I R) (liftAdv B) = game0 I B := by
  unfold game0
  refine bind_congr fun P' => ?_
  have h := map_run_simulateQ_eq_of_query_map_eq (phase1₀ I P')
    (QueryImpl.compose (phase1₀ (collInterface I R) P') liftImpl)
    (fun st : Table P (T × X) N × σ => (st.1, (st.2, ([] : List T)))) (fun t st => ?_) B.A1
    (fun _ => none, I.init)
  · change (simulateQ (phase1₀ (collInterface I R) P') (simulateQ liftImpl B.A1)).run
      (fun _ => none, (I.init, [])) >>= _ = _
    rw [← QueryImpl.simulateQ_compose, ← h, bind_map_left]
    rfl
  · rcases t with n | x | d
    · change _ = (simulateQ (phase1₀ (collInterface I R) P')
        (liftM ((CSpec P T X N cs).query (.inl n)))).run _
      rw [simulateQ_spec_query]
      exact map_coinImpl_run _ n st
    · change Prod.map id _ <$> ((fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) st.1 x) =
        (simulateQ (phase1₀ (collInterface I R) P')
          (liftM ((CSpec P T X N cs).query (.inr (.inl x))))).run _
      rw [simulateQ_spec_query, Functor.map_map]
      rfl
    · change Prod.map id _ <$> (sigmaStep I (sliceImpl₀ P') d).run st =
        (simulateQ (phase1₀ (collInterface I R) P')
          (liftM ((CSpec P T X N cs).query (.inr (.inr (.inl d)))))).run _
      rw [simulateQ_spec_query]
      change _ = (sigmaStep (collInterface I R) (sliceImpl₀ P') (.inl d)).run _
      rw [sigmaStep_run, sigmaStep_run]
      change _ = _ <$> (simulateQ (sliceImpl₀ P') ((collChal I R d).run (st.2, []))).run st.1
      rw [collChal, StateT.run_mk]
      simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, simulateQ_map, StateT.run_map,
        Functor.map_map]
      rfl

/-- **Lemma 4.1, lower bound**, in probabilities. -/
theorem prEvent_game0_liftAdv {q : ℕ} (I : Interface (T × X) N cs σ α)
    (R : Reservation cs σ T) (B : Adversary P (T × X) N cs S α q) :
    Pr{let b ← game0 I B}[b = true] =
      Pr{let b ← game0 (collInterface I R) (liftAdv B)}[b = true] := by
  rw [game0_collInterface_liftAdv]

end collection

/-! ## Definition D.1: SM-TCR of a member of the collection, in the random-oracle model -/

section smtcr

variable {P T X M N : Type} [DecidableEq P] [DecidableEq T] [DecidableEq X] [DecidableEq N]
  [SampleableType N]

/-- The challenge oracle `O(·, ·)` of SM-TCR: a tweak and a message of the member `Th_m`, answered
by `none` (`⊥`) when refused. -/
abbrev SMTCRSpec (T M N : Type) : OracleSpec (T × M) := (T × M) →ₒ Option N

/-- The stand-alone refusal test of `O` (Definition D.1, step 3): `|Q| ≥ p`, or the tweak was
already challenged. -/
def smtcrRefused (p : ℕ) (Q : List (T × M)) (d : T × M) : Bool :=
  decide (p ≤ Q.length) || Q.any fun e => decide (e.1 = d.1)

/-- One evaluation of the hidden slice `Th(P', ·)` at a tweak and a message of the collection. -/
abbrev sliceQuery (x : T × X) : OracleComp (unifSpec + SliceSpec (T × X) N) N :=
  liftM ((unifSpec + SliceSpec (T × X) N).query (.inr x))

/-- The challenge oracle `O(T, m)` of Definition D.1 on the slice: refused by `smtcrRefused`,
otherwise `(T, m)` is appended to `Q` and `Th_m(P', T, m)` returned. The member's messages are
embedded in the collection's message space by `emb` (for `Th_λ`, `m ↦ ⟨|m|, m⟩`). -/
def smtcrChal (emb : M → X) (p : ℕ) (d : T × M) :
    StateT (List (T × M)) (OracleComp (unifSpec + SliceSpec (T × X) N)) (Option N) :=
  StateT.mk fun Q => if smtcrRefused p Q d then pure (none, Q)
    else (fun y => (some y, Q ++ [d])) <$> sliceQuery (d.1, emb d.2)

/-- The winning condition of Definition D.1, step 6: with `(T_j, m_j) = Q[j]`, output `1` iff
`m* ≠ m_j` and `Th_m(P', T_j, m*) = Th_m(P', T_j, m_j)`. -/
def smtcrPred (emb : M → X) [DecidableEq M] (Q : List (T × M)) (out : ℕ × M) :
    OracleComp (unifSpec + SliceSpec (T × X) N) Bool :=
  match Q[out.1]? with
  | none => pure false
  | some e => if out.2 = e.2 then pure false else
      sliceQuery (e.1, emb e.2) >>= fun y =>
        (fun y' => decide (y = y')) <$> sliceQuery (e.1, emb out.2)

/-- **The stand-alone SM-TCR experiment** of a member `Th_m` in the random-oracle model, as an
interface of Lemma C.9 (Definition D.1 without the collection oracle). -/
def smtcrInterface (emb : M → X) [DecidableEq M] (p : ℕ) :
    Interface (T × X) N (SMTCRSpec T M N) (List (T × M)) (ℕ × M) where
  init := []
  impl := smtcrChal emb p
  pred := smtcrPred emb

/-- The reservation data of SM-TCR: a challenge `(T, m)` reserves `T`; `Q` reserves its tweaks. -/
def smtcrReservation (p : ℕ) : Reservation (SMTCRSpec T M N) (List (T × M)) T where
  res Q t := Q.any fun e => decide (e.1 = t)
  chalRes d t := decide (d.1 = t)
  refused := smtcrRefused p
  refuse _ := none
  accepted _ a := a.isSome

omit [DecidableEq X] [SampleableType N] in
/-- SM-TCR obeys the reservation discipline. -/
theorem smtcr_discipline (emb : M → X) [DecidableEq M] (p : ℕ) :
    Discipline (smtcrInterface (T := T) (N := N) emb p)
      (smtcrReservation (T := T) (M := M) (N := N) p) where
  accepted_refuse _ := rfl
  run_of_refused Q d h := by
    change (smtcrChal emb p d).run Q = _
    have h' : smtcrRefused p Q d = true := h
    rw [smtcrChal, StateT.run_mk]
    simp only [h', ↓reduceIte]
    rfl
  impl_queries Q d h := by
    change ((smtcrChal emb p d).run Q).AllQueriesSatisfy _
    have h' : smtcrRefused p Q d = false := h
    rw [smtcrChal, StateT.run_mk]
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    rw [map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 (by simp [SliceIn,
      smtcrReservation])) fun _ => allQueriesSatisfy_pure _ _
  impl_support Q d h z hz := by
    change z ∈ support ((smtcrChal emb p d).run Q) at hz
    have h' : smtcrRefused p Q d = false := h
    rw [smtcrChal, StateT.run_mk] at hz
    simp only [h', Bool.false_eq_true, ↓reduceIte, support_map] at hz
    obtain ⟨y, -, rfl⟩ := hz
    refine ⟨rfl, funext fun t => ?_⟩
    simp [smtcrReservation, List.any_append]
  pred_queries Q out := by
    change (smtcrPred emb Q out).AllQueriesSatisfy _
    unfold smtcrPred
    cases he : Q[out.1]? with
    | none => exact allQueriesSatisfy_pure _ _
    | some e =>
      dsimp only
      have hres : (smtcrReservation (N := N) p).res Q e.1 = true :=
        List.any_eq_true.2 ⟨e, List.mem_of_getElem? he, by simp⟩
      split_ifs
      · exact allQueriesSatisfy_pure _ _
      · refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 hres) fun _ => ?_
        rw [map_eq_bind_pure_comp]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 hres)
          fun _ => allQueriesSatisfy_pure _ _

variable [SampleableType P] [DecidableEq M] {S : Type} {q : ℕ}

/-- **Definition D.1** in the random-oracle model: the SM-TCR experiment of `Th_m` as a member of
the collection `Th_λ`, `SM-TCR_{Th_m ∈ Th_λ, p}(A)`. -/
abbrev smtcrCollGame (emb : M → X) (p : ℕ)
    (A : Adversary P (T × X) N (SMTCRSpec T M N + CollSpec T X N) S (ℕ × M) q) :
    ProbComp Bool :=
  game0 (collInterface (smtcrInterface emb p) (smtcrReservation p)) A

/-- The stand-alone SM-TCR experiment `SM-TCR_{Th_m, p}(A)` in the random-oracle model. -/
abbrev smtcrGame (emb : M → X) (p : ℕ) (A : Adversary P (T × X) N (SMTCRSpec T M N) S (ℕ × M) q) :
    ProbComp Bool :=
  game0 (smtcrInterface emb p) A

/-- **Lemma 4.1 (i) for SM-TCR** (Definition D.1): the collection oracle costs at most `2q/|P|`,
where `q` bounds the first stage's evaluations of `Th_λ`. -/
theorem prEvent_smtcrCollGame_le [Fintype P] (emb : M → X) (p : ℕ)
    (A : Adversary P (T × X) N (SMTCRSpec T M N + CollSpec T X N) S (ℕ × M) q) :
    Pr{let b ← smtcrCollGame emb p A}[b = true] ≤
      Pr{let b ← smtcrGame emb p (standAlone (smtcrInterface emb p) (smtcrReservation p) A)}[
        b = true] + 2 * q / Fintype.card P :=
  prEvent_game0_collInterface_le (smtcr_discipline emb p) A

/-- **Lemma 4.1, lower bound, for SM-TCR**: every stand-alone adversary is a collection adversary
with the same success probability. -/
theorem prEvent_smtcrGame_eq (emb : M → X) (p : ℕ)
    (B : Adversary P (T × X) N (SMTCRSpec T M N) S (ℕ × M) q) :
    Pr{let b ← smtcrGame emb p B}[b = true] =
      Pr{let b ← smtcrCollGame emb p (liftAdv B)}[b = true] :=
  prEvent_game0_liftAdv _ _ B

end smtcr

end CollectionLemma

end ShrincsSecurity.Notions.Generic

end
