module

public import ShrincsSecurity.Notions.Generic.ZeroDist
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Hidden-slice reprogramming

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), Appendix C, *Hidden-slice
reprogramming*: the games Game 0 and Game 1 (lines 6435–6470) and **Lemma C.9**, classical case
(lines 6471–6480, proof lines 6481–6535).

A collection of tweakable hash functions is modelled as one random oracle `Th : P × D → N`: a
member index, tweak and message are folded into `D` (for a collection, `D = Σ m, T × {0,1}^m`).
`Th` is sampled lazily on a table. A *classical interface* `Σ` (`Interface`) answers the first
stage's mediated queries; it may evaluate the *slice* `D → N` at one fixed parameter and draw
private coins, and it keeps its own state. The predicate `Φ` reads the final state of `Σ` and the
output of the second stage, evaluates the slice too, and produces the reported bit.

* **Game 0** (`game0`): `P' ←$ P`; `A₁` evaluates `Th` and queries `Σ`, which runs on the true
  hidden slice `Th(P', ·)`; `A₂(P')` evaluates `Th`; `Φ` runs on `Th(P', ·)`. One table.
* **Game 1** (`game1`): `P' ←$ P` and an independent lazily sampled `g : D → N`; `A₁` evaluates
  `Th` and queries `Σ`, which runs on `g`; `A₂(P')` evaluates `Th'`, which is `g` at `P'` and `Th`
  elsewhere; `Φ` runs on `g`. Two tables, one for `Th` and one for `g`.

## Main statements

* `HiddenSlice.reduction`: the ZeroDist adversary `B` of the proof, which makes at most `q`
  queries (`q` bounds the first stage's evaluations of `Th`); `experiment_true_reduction` and
  `experiment_false_reduction`: with `f_{P'}` it runs Game 0, with `f₀` it runs Game 1.
* `HiddenSlice.abs_game_sub_eq_advantage`: **Lemma C.9**, reduction form,
  `|Pr[G0 ⇒ 1] − Pr[G1 ⇒ 1]| = Adv^{ZeroDist}(B)`.
* `HiddenSlice.prEvent_game_le`: the one-sided bounds `Pr[G0 ⇒ 1] ≤ Pr[G1 ⇒ 1] + q/|P|` and
  `Pr[G1 ⇒ 1] ≤ Pr[G0 ⇒ 1] + q/|P|`.
* `HiddenSlice.abs_game_sub_le`: **Lemma C.9** (classical), `|Pr[G0 ⇒ 1] − Pr[G1 ⇒ 1]| ≤ q/|P|`.

## Proof

As in the paper. `B₁` keeps lazy tables for `Tĥ` and `g` and runs `A₁`; an evaluation of `Th` at
`(P, x)` asks `f(P)` and is answered from `g` if `f(P) = 1` and from `Tĥ` otherwise; `Σ` runs on
`g`. `B₂` receives `P'`, runs `A₂(P')` on `Th'` (`g` at `P'`, `Tĥ` elsewhere) and `Φ` on `g`.
With `f₀`, `B` is literally Game 1 (`answeredImpl_fZero`). With `f_{P'}`, merging `g` into `Tĥ` at
`P'` maps every step of `B` to the corresponding step of Game 0 on its single table
(`map_run_simulateQ_answeredImpl_fHidden`, `map_run_simulateQ_thPrimeImpl`,
`map_run_simulateQ_sliceImpl₁`), so `B` runs Game 0 exactly. Lemma C.7
(`ZeroDist.advantage_le`) gives the bound. The second stage's evaluations are free, as in the
paper: `B₂` answers them without its oracle.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

/-- A lazy evaluation commutes with maps of the output and the table that read the evaluated
entry alike and commute with storing a fresh value. -/
theorem map_lazyStep_eq {X Y V β : Type} [DecidableEq X] [DecidableEq Y] (fresh : ProbComp V)
    (tbl : X → Option V) (x : X) (tbl' : Y → Option V) (y : Y)
    (F : V × (X → Option V) → β) (G : V × (Y → Option V) → β) (hread : tbl' y = tbl x)
    (hpure : ∀ v, tbl x = some v → F (v, tbl) = G (v, tbl'))
    (hfresh : ∀ v, tbl x = none →
      F (v, Function.update tbl x (some v)) = G (v, Function.update tbl' y (some v))) :
    F <$> lazyStep fresh tbl x = G <$> lazyStep fresh tbl' y := by
  unfold lazyStep
  rw [hread]
  cases h : tbl x with
  | some v => simp only [map_pure, hpure v h]
  | none =>
    simp only [Functor.map_map]
    exact congrArg (· <$> fresh) (funext fun v => hfresh v h)

/-- `map_lazyStep_eq` with the identity on the right. -/
theorem map_lazyStep_eq_id {X Y V : Type} [DecidableEq X] [DecidableEq Y] (fresh : ProbComp V)
    (tbl : X → Option V) (x : X) (tbl' : Y → Option V) (y : Y)
    (F : V × (X → Option V) → V × (Y → Option V)) (hread : tbl' y = tbl x)
    (hpure : ∀ v, tbl x = some v → F (v, tbl) = (v, tbl'))
    (hfresh : ∀ v, tbl x = none →
      F (v, Function.update tbl x (some v)) = (v, Function.update tbl' y (some v))) :
    F <$> lazyStep fresh tbl x = lazyStep fresh tbl' y := by
  rw [← id_map (lazyStep fresh tbl' y)]
  exact map_lazyStep_eq fresh tbl x tbl' y F id hread hpure hfresh

namespace HiddenSlice

variable (P D N : Type)

/-- Direct evaluations of the collection `Th : P × D → N`. -/
abbrev ROSpec : OracleSpec (P × D) := (P × D) →ₒ N

/-- Evaluations of one slice `D → N`. -/
abbrev SliceSpec : OracleSpec D := D →ₒ N

/-- The table of the lazily sampled `Th`. -/
abbrev Table : Type := P × D → Option N

/-- The table of the lazily sampled `g`. -/
abbrev Slice : Type := D → Option N

/-- **The classical interface `Σ` and the predicate `Φ`** of Lemma C.9. `Σ` answers the queries
`ISpec` of the first stage from a state `σ`, evaluating the slice at the fixed parameter
(`SliceSpec`) and drawing private coins; `Φ` reads the final state of `Σ` and the output of the
second stage, evaluates the slice, and returns the reported bit. -/
structure Interface {ιI : Type} (ISpec : OracleSpec ιI) (σ α : Type) where
  /-- The initial state of `Σ`. -/
  init : σ
  /-- `Σ`: one answer to a mediated query of the first stage. -/
  impl : QueryImpl ISpec (StateT σ (OracleComp (unifSpec + SliceSpec D N)))
  /-- `Φ`: the reported bit. -/
  pred : σ → α → OracleComp (unifSpec + SliceSpec D N) Bool

/-- A direct evaluation of `Th` by the first stage. -/
def IsROQuery {ιI : Type} : ℕ ⊕ ((P × D) ⊕ ιI) → Prop
  | .inr (.inl _) => True
  | _ => False

instance {ιI : Type} : DecidablePred (IsROQuery P D (ιI := ιI)) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsROQuery] <;> infer_instance

/-- A two-stage adversary `A = (A₁, A₂)` for the games of Lemma C.9. The first stage evaluates
`Th` at most `q` times and queries `Σ` freely; the second stage receives `P'` and evaluates `Th`
(or `Th'`) without restriction. -/
structure Adversary {ιI : Type} (ISpec : OracleSpec ιI) (S α : Type) (q : ℕ) where
  /-- The first stage, with access to `Th` and `Σ`. -/
  A1 : OracleComp (unifSpec + (ROSpec P D N + ISpec)) S
  /-- The second stage, with access to `Th` (Game 0) or `Th'` (Game 1). -/
  A2 : S → P → OracleComp (unifSpec + ROSpec P D N) α
  /-- The first stage evaluates `Th` at most `q` times. -/
  queryBound : A1.IsQueryBoundP (IsROQuery P D) q

variable {P D N} [DecidableEq P] [DecidableEq D] [SampleableType N]
variable {ιI : Type} {ISpec : OracleSpec ιI} {σ α S : Type}

/-! ## Handlers -/

/-- Private coins, on any state. -/
def coinImpl (τ : Type) : QueryImpl unifSpec (StateT τ ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT τ ProbComp)

/-- Run one query of `Σ` through a slice handler `inner`, carrying the state of `Σ`. -/
def sigmaStep {τ : Type} (I : Interface D N ISpec σ α)
    (inner : QueryImpl (unifSpec + SliceSpec D N) (StateT τ ProbComp)) (i : ιI) :
    StateT (τ × σ) ProbComp (ISpec.Range i) :=
  StateT.mk fun st =>
    (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ inner ((I.impl i).run st.2)).run st.1

/-- Game 0: `Th` and its private coins, on the single table. -/
def roImpl₀ : QueryImpl (unifSpec + ROSpec P D N) (StateT (Table P D N) ProbComp) :=
  coinImpl (Table P D N) + (fun x => StateT.mk fun K => lazyStep ($ᵗ N) K x :
    QueryImpl (ROSpec P D N) (StateT (Table P D N) ProbComp))

/-- Game 0: the hidden slice `Th(P', ·)` and private coins, on the single table. -/
def sliceImpl₀ (P' : P) : QueryImpl (unifSpec + SliceSpec D N) (StateT (Table P D N) ProbComp) :=
  coinImpl (Table P D N) + (fun d => StateT.mk fun K => lazyStep ($ᵗ N) K (P', d) :
    QueryImpl (SliceSpec D N) (StateT (Table P D N) ProbComp))

/-- Game 0, first stage: `Th` on the single table and `Σ` on the hidden slice. -/
def phase1₀ (I : Interface D N ISpec σ α) (P' : P) :
    QueryImpl (unifSpec + (ROSpec P D N + ISpec)) (StateT (Table P D N × σ) ProbComp) :=
  coinImpl (Table P D N × σ) + ((fun x => StateT.mk fun st =>
      (fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) st.1 x :
        QueryImpl (ROSpec P D N) (StateT (Table P D N × σ) ProbComp)) +
    (fun i => sigmaStep I (sliceImpl₀ P') i : QueryImpl ISpec (StateT (Table P D N × σ) ProbComp)))

/-- Game 1: `g` and private coins, on the pair of tables. -/
def sliceImpl₁ : QueryImpl (unifSpec + SliceSpec D N)
    (StateT (Table P D N × Slice D N) ProbComp) :=
  coinImpl (Table P D N × Slice D N) + (fun d => StateT.mk fun st =>
    (fun z => (z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 d :
      QueryImpl (SliceSpec D N) (StateT (Table P D N × Slice D N) ProbComp))

/-- Game 1, second stage: `Th'`, which is `g` at `P'` and `Th` elsewhere. -/
def thPrimeImpl (P' : P) : QueryImpl (unifSpec + ROSpec P D N)
    (StateT (Table P D N × Slice D N) ProbComp) :=
  coinImpl (Table P D N × Slice D N) + (fun x => StateT.mk fun st =>
    if x.1 = P' then (fun z => (z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 x.2
    else (fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) st.1 x :
      QueryImpl (ROSpec P D N) (StateT (Table P D N × Slice D N) ProbComp))

/-- Game 1: a first-stage evaluation of `Th`, on the `Th` table. -/
def roStep₁ (x : P × D) : StateT ((Table P D N × Slice D N) × σ) ProbComp N :=
  StateT.mk fun st => (fun z => (z.1, ((z.2, st.1.2), st.2))) <$> lazyStep ($ᵗ N) st.1.1 x

/-- Game 1, first stage: `Th` on its table and `Σ` on `g`. It does not depend on `P'`. -/
def phase1₁ (I : Interface D N ISpec σ α) : QueryImpl (unifSpec + (ROSpec P D N + ISpec))
    (StateT ((Table P D N × Slice D N) × σ) ProbComp) :=
  coinImpl ((Table P D N × Slice D N) × σ) +
    ((fun x => roStep₁ x : QueryImpl (ROSpec P D N)
        (StateT ((Table P D N × Slice D N) × σ) ProbComp)) +
      (fun i => sigmaStep I sliceImpl₁ i :
        QueryImpl ISpec (StateT ((Table P D N × Slice D N) × σ) ProbComp)))

variable [SampleableType P]

/-- **Game 0** of Lemma C.9. -/
def game0 {q : ℕ} (I : Interface D N ISpec σ α) (A : Adversary P D N ISpec S α q) :
    ProbComp Bool := do
  let P' ← $ᵗ P
  let z ← (simulateQ (phase1₀ I P') A.A1).run (fun _ => none, I.init)
  let w ← (simulateQ roImpl₀ (A.A2 z.1 P')).run z.2.1
  let v ← (simulateQ (sliceImpl₀ P') (I.pred z.2.2 w.1)).run w.2
  return v.1

/-- The part of Game 1 after the first stage: `A₂(P')` on `Th'`, then `Φ` on `g`. -/
def tail₁ {q : ℕ} (I : Interface D N ISpec σ α) (A : Adversary P D N ISpec S α q) (P' : P)
    (z : S × ((Table P D N × Slice D N) × σ)) : ProbComp Bool := do
  let w ← (simulateQ (thPrimeImpl P') (A.A2 z.1 P')).run z.2.1
  let v ← (simulateQ sliceImpl₁ (I.pred z.2.2 w.1)).run w.2
  return v.1

/-- **Game 1** of Lemma C.9. -/
def game1 {q : ℕ} (I : Interface D N ISpec σ α) (A : Adversary P D N ISpec S α q) :
    ProbComp Bool := do
  let P' ← $ᵗ P
  let z ← (simulateQ (phase1₁ I) A.A1).run ((fun _ => none, fun _ => none), I.init)
  tail₁ I A P' z

/-! ## Proof of Lemma C.9 -/

omit [SampleableType N] [SampleableType P] in
theorem coinImpl_run (τ : Type) (n : ℕ) (s : τ) :
    (coinImpl τ n).run s =
      (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) >>= fun u => pure (u, s) := rfl

omit [SampleableType N] [SampleableType P] in
theorem mem_support_coinImpl_run {τ : Type} {n : ℕ} {s : τ} {z : unifSpec.Range n × τ}
    (hz : z ∈ support ((coinImpl τ n).run s)) : z.2 = s := by
  rw [coinImpl_run, mem_support_bind_iff] at hz
  obtain ⟨_, -, hz⟩ := hz
  rw [mem_support_pure_iff] at hz
  rw [hz]

omit [SampleableType N] [SampleableType P] in
theorem map_coinImpl_run {τ τ' : Type} (f : τ → τ') (n : ℕ) (s : τ) :
    Prod.map id f <$> (coinImpl τ n).run s = (coinImpl τ' n).run (f s) := by
  simp only [coinImpl_run, map_bind, map_pure, Prod.map_apply, id_eq]

omit [DecidableEq P] [SampleableType P] in
theorem sliceImpl₁_inr_run (d : D) (st : Table P D N × Slice D N) :
    (sliceImpl₁ (.inr d)).run st = (fun z => (z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 d :=
  rfl

omit [SampleableType P] in
theorem thPrimeImpl_inr_run (P' : P) (x : P × D) (st : Table P D N × Slice D N) :
    (thPrimeImpl P' (.inr x)).run st =
      if x.1 = P' then (fun z => (z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 x.2
      else (fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) st.1 x :=
  rfl

omit [DecidableEq D] [SampleableType N] [SampleableType P] in
theorem sigmaStep_run {τ : Type} (I : Interface D N ISpec σ α)
    (inner : QueryImpl (unifSpec + SliceSpec D N) (StateT τ ProbComp)) (i : ιI) (st : τ × σ) :
    (sigmaStep I inner i).run st =
      (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ inner ((I.impl i).run st.2)).run st.1 :=
  rfl

omit [DecidableEq P] [SampleableType P] in
/-- A slice evaluation under `sliceImpl₁` is a lazy evaluation of `g`. -/
theorem run_simulateQ_sliceImpl₁_query {β : Type} (d : D) (f : N → β)
    (st : Table P D N × Slice D N) :
    (simulateQ sliceImpl₁ (f <$> (liftM ((unifSpec + SliceSpec D N).query (.inr d)) :
        OracleComp (unifSpec + SliceSpec D N) N))).run st =
      (fun z => (f z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 d := by
  rw [simulateQ_map, StateT.run_map, simulateQ_query]
  change (fun p => (f p.1, p.2)) <$> (id <$> (sliceImpl₁ (.inr d))).run st = _
  rw [id_map, sliceImpl₁_inr_run, Functor.map_map]

/-- The single table seen through the pair of tables: `g` at `P'`, the `Th` table elsewhere. -/
def merge (P' : P) (H : Table P D N) (g : Slice D N) : Table P D N :=
  fun x => if x.1 = P' then g x.2 else H x

section merge

omit [DecidableEq D] [SampleableType N] [SampleableType P]

theorem merge_of_eq {P' : P} {x : P × D} (h : x.1 = P') (H : Table P D N) (g : Slice D N) :
    merge P' H g x = g x.2 := by simp only [merge, h, ↓reduceIte]

theorem merge_of_ne {P' : P} {x : P × D} (h : x.1 ≠ P') (H : Table P D N) (g : Slice D N) :
    merge P' H g x = H x := by simp only [merge, h, ↓reduceIte]

theorem merge_empty (P' : P) : merge P' (fun _ => none) (fun _ => none : Slice D N) =
    fun _ => none := by
  funext x
  unfold merge
  split_ifs <;> rfl

variable [DecidableEq D]

theorem merge_update_H_of_ne {P' : P} {x : P × D} (h : x.1 ≠ P') (H : Table P D N)
    (g : Slice D N) (v : Option N) :
    merge P' (Function.update H x v) g = Function.update (merge P' H g) x v := by
  funext y
  unfold merge
  by_cases hyx : y = x
  · subst hyx
    simp only [h, ↓reduceIte, Function.update_self]
  · rw [Function.update_of_ne hyx, Function.update_of_ne hyx]

theorem merge_update_g {P' : P} {x : P × D} (h : x.1 = P') (H : Table P D N)
    (g : Slice D N) (v : Option N) :
    merge P' H (Function.update g x.2 v) = Function.update (merge P' H g) x v := by
  funext y
  unfold merge
  by_cases hyx : y = x
  · subst hyx
    simp only [h, ↓reduceIte, Function.update_self]
  · rw [Function.update_of_ne hyx]
    split_ifs with hy
    · refine Function.update_of_ne (fun e => hyx ?_) _ _
      exact Prod.ext (hy.trans h.symm) e
    · rfl

end merge

omit [SampleableType P] in
/-- `g` merged into the `Th` table at `P'` is the hidden slice of Game 0. -/
theorem map_run_simulateQ_sliceImpl₁ (P' : P) {β : Type}
    (oa : OracleComp (unifSpec + SliceSpec D N) β) (st : Table P D N × Slice D N) :
    Prod.map id (fun st : Table P D N × Slice D N => merge P' st.1 st.2) <$>
        (simulateQ sliceImpl₁ oa).run st =
      (simulateQ (sliceImpl₀ P') oa).run (merge P' st.1 st.2) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t st => ?_) oa st
  rcases t with n | d
  · exact map_coinImpl_run _ n st
  · change Prod.map id _ <$> ((fun z => (z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 d) =
      lazyStep ($ᵗ N) (merge P' st.1 st.2) (P', d)
    rw [Functor.map_map]
    refine map_lazyStep_eq_id _ _ _ _ _ _ (merge_of_eq rfl _ _) (fun _ _ => rfl) fun v _ => ?_
    simp only [Prod.map_apply, id_eq]
    exact congrArg _ (merge_update_g (x := (P', d)) rfl _ _ _)

omit [SampleableType P] in
/-- `Th'` is the single table of Game 0 seen through the pair of tables. -/
theorem map_run_simulateQ_thPrimeImpl (P' : P) {β : Type}
    (oa : OracleComp (unifSpec + ROSpec P D N) β) (st : Table P D N × Slice D N) :
    Prod.map id (fun st : Table P D N × Slice D N => merge P' st.1 st.2) <$>
        (simulateQ (thPrimeImpl P') oa).run st =
      (simulateQ roImpl₀ oa).run (merge P' st.1 st.2) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t st => ?_) oa st
  rcases t with n | x
  · exact map_coinImpl_run _ n st
  · change Prod.map id _ <$> (if x.1 = P' then
        (fun z => (z.1, (st.1, z.2))) <$> lazyStep ($ᵗ N) st.2 x.2
      else (fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) st.1 x) =
      lazyStep ($ᵗ N) (merge P' st.1 st.2) x
    split_ifs with hx
    · rw [Functor.map_map]
      refine map_lazyStep_eq_id _ _ _ _ _ _ (merge_of_eq hx _ _) (fun _ _ => rfl) fun v _ => ?_
      simp only [Prod.map_apply, id_eq]
      exact congrArg _ (merge_update_g hx _ _ _)
    · rw [Functor.map_map]
      refine map_lazyStep_eq_id _ _ _ _ _ _ (merge_of_ne hx _ _) (fun _ _ => rfl) fun v _ => ?_
      simp only [Prod.map_apply, id_eq]
      exact congrArg _ (merge_update_H_of_ne hx _ _ _)

omit [SampleableType P] in
theorem mem_support_roStep₁ (x : P × D) (st : (Table P D N × Slice D N) × σ)
    {z : N × ((Table P D N × Slice D N) × σ)} (hz : z ∈ support ((roStep₁ x).run st)) :
    z.2 = ((Function.update st.1.1 x (some z.1), st.1.2), st.2) := by
  change z ∈ support ((fun z => (z.1, ((z.2, st.1.2), st.2))) <$> lazyStep ($ᵗ N) st.1.1 x) at hz
  rw [support_map] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  dsimp only
  rw [(mem_support_lazyStep hu).1]

/-! ### The ZeroDist adversary -/

/-- An evaluation of `Th` at a parameter that `B`'s oracle marks: the slice `g`. -/
def roStepG (x : P × D) : StateT ((Table P D N × Slice D N) × σ) ProbComp N :=
  StateT.mk fun st => (fun z => (z.1, ((st.1.1, z.2), st.2))) <$> lazyStep ($ᵗ N) st.1.2 x.2

/-- `B₁`'s handler for `A₁` (proof of Lemma C.9): `B₁` keeps lazy tables for `Tĥ` and `g`, and
answers an evaluation of `Th` at `(P, x)` from `g` if its oracle `f` marks `P` and from `Tĥ`
otherwise, at the cost of one query to `f`; `Σ` runs on `g`. -/
def reductionImpl (I : Interface D N ISpec σ α) :
    QueryImpl (unifSpec + (ROSpec P D N + ISpec))
      (StateT ((Table P D N × Slice D N) × σ) (OracleComp (ZeroDist.AdvSpec P))) :=
  (fun n => StateT.mk fun st =>
      (liftM ((coinImpl ((Table P D N × Slice D N) × σ) n).run st) :
        OracleComp (ZeroDist.AdvSpec P) _) :
    QueryImpl unifSpec
      (StateT ((Table P D N × Slice D N) × σ) (OracleComp (ZeroDist.AdvSpec P)))) +
  ((fun x => StateT.mk fun st =>
      (liftM ((ZeroDist.AdvSpec P).query (.inr x.1)) : OracleComp (ZeroDist.AdvSpec P) Bool) >>=
        fun b => liftM ((if b then roStepG x else roStep₁ x).run st) :
    QueryImpl (ROSpec P D N)
      (StateT ((Table P D N × Slice D N) × σ) (OracleComp (ZeroDist.AdvSpec P)))) +
   (fun i => StateT.mk fun st => liftM ((sigmaStep I sliceImpl₁ i).run st) :
    QueryImpl ISpec
      (StateT ((Table P D N × Slice D N) × σ) (OracleComp (ZeroDist.AdvSpec P)))))

/-- `B₁`'s handler with its oracle answered by `ans`. -/
def answeredImpl (I : Interface D N ISpec σ α) (ans : P → Bool) :
    QueryImpl (unifSpec + (ROSpec P D N + ISpec))
      (StateT ((Table P D N × Slice D N) × σ) ProbComp) :=
  coinImpl ((Table P D N × Slice D N) × σ) +
    ((fun x => if ans x.1 then roStepG x else roStep₁ x : QueryImpl (ROSpec P D N)
        (StateT ((Table P D N × Slice D N) × σ) ProbComp)) +
      (fun i => sigmaStep I sliceImpl₁ i :
        QueryImpl ISpec (StateT ((Table P D N × Slice D N) × σ) ProbComp)))

omit [SampleableType P] in
theorem simulateQ_oracle_reductionImpl (I : Interface D N ISpec σ α) (ans : P → Bool)
    {β : Type} (oa : OracleComp (unifSpec + (ROSpec P D N + ISpec)) β)
    (st : (Table P D N × Slice D N) × σ) :
    simulateQ (ZeroDist.oracle ans) ((simulateQ (reductionImpl I) oa).run st) =
      (simulateQ (answeredImpl I ans) oa).run st := by
  refine simulateQ_StateT_compose _ _ _ (fun t st => ?_) oa st
  rcases t with n | x | i
  · change simulateQ (ZeroDist.oracle ans) (liftM ((coinImpl _ n).run st)) = _
    rw [ZeroDist.oracle]
    erw [QueryImpl.simulateQ_add_liftM_left, simulateQ_ofLift_eq_self]
    rfl
  · change simulateQ (ZeroDist.oracle ans)
        ((liftM ((ZeroDist.AdvSpec P).query (.inr x.1)) : OracleComp (ZeroDist.AdvSpec P) Bool) >>=
          fun b => liftM ((if b then roStepG x else roStep₁ x).run st)) = _
    rw [simulateQ_bind, simulateQ_spec_query, ZeroDist.oracle_inr, pure_bind, ZeroDist.oracle]
    erw [QueryImpl.simulateQ_add_liftM_left, simulateQ_ofLift_eq_self]
    rfl
  · change simulateQ (ZeroDist.oracle ans) (liftM ((sigmaStep I sliceImpl₁ i).run st)) = _
    rw [ZeroDist.oracle]
    erw [QueryImpl.simulateQ_add_liftM_left, simulateQ_ofLift_eq_self]
    rfl

omit [SampleableType P] in
/-- With `f₀`, `B₁` runs Game 1's first stage. -/
theorem answeredImpl_fZero (I : Interface D N ISpec σ α) :
    answeredImpl I (ZeroDist.fZero : P → Bool) = phase1₁ I := by
  funext t
  rcases t with n | x | i <;> rfl

omit [SampleableType P] in
/-- With `f_{P'}`, `B₁` runs Game 0's first stage, seen through `merge`. -/
theorem map_run_simulateQ_answeredImpl_fHidden (I : Interface D N ISpec σ α) (P' : P)
    {β : Type} (oa : OracleComp (unifSpec + (ROSpec P D N + ISpec)) β)
    (st : (Table P D N × Slice D N) × σ) :
    Prod.map id (fun st : (Table P D N × Slice D N) × σ => (merge P' st.1.1 st.1.2, st.2)) <$>
        (simulateQ (answeredImpl I (ZeroDist.fHidden P')) oa).run st =
      (simulateQ (phase1₀ I P') oa).run (merge P' st.1.1 st.1.2, st.2) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t st => ?_) oa st
  rcases t with n | x | i
  · exact map_coinImpl_run _ n st
  · change Prod.map id _ <$> (if ZeroDist.fHidden P' x.1 then roStepG x else roStep₁ x).run st =
      (fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) (merge P' st.1.1 st.1.2) x
    by_cases hx : x.1 = P'
    · simp only [ZeroDist.fHidden, hx, decide_true, ↓reduceIte]
      change Prod.map id _ <$> ((fun z => (z.1, ((st.1.1, z.2), st.2))) <$>
        lazyStep ($ᵗ N) st.1.2 x.2) = _
      rw [Functor.map_map]
      refine map_lazyStep_eq _ _ _ _ _ _ _ (merge_of_eq hx _ _) (fun _ _ => rfl) fun v _ => ?_
      simp only [Prod.map_apply, id_eq, merge_update_g hx]
    · simp only [ZeroDist.fHidden, hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      change Prod.map id _ <$> ((fun z => (z.1, ((z.2, st.1.2), st.2))) <$>
        lazyStep ($ᵗ N) st.1.1 x) = _
      rw [Functor.map_map]
      refine map_lazyStep_eq _ _ _ _ _ _ _ (merge_of_ne hx _ _) (fun _ _ => rfl) fun v _ => ?_
      simp only [Prod.map_apply, id_eq, merge_update_H_of_ne hx]
  · change Prod.map id _ <$> ((fun z => (z.1.1, (z.2, z.1.2))) <$>
        (simulateQ sliceImpl₁ ((I.impl i).run st.2)).run st.1) =
      (fun z => (z.1.1, (z.2, z.1.2))) <$>
        (simulateQ (sliceImpl₀ P') ((I.impl i).run st.2)).run (merge P' st.1.1 st.1.2)
    rw [← map_run_simulateQ_sliceImpl₁, Functor.map_map, Functor.map_map]
    rfl

omit [SampleableType P] in
/-- `B₁` asks its oracle once per evaluation of `Th` by `A₁`. -/
theorem isQueryBoundP_reductionImpl {q : ℕ} (I : Interface D N ISpec σ α)
    (A : Adversary P D N ISpec S α q) (st : (Table P D N × Slice D N) × σ) :
    ((simulateQ (reductionImpl I) A.A1).run st).IsQueryBoundP (ZeroDist.IsFQuery P) q := by
  have hlift : ∀ {β : Type} (mx : ProbComp β),
      (liftM mx : OracleComp (ZeroDist.AdvSpec P) β).IsQueryBoundP (ZeroDist.IsFQuery P) 0 :=
    fun mx => (isQueryBoundP_liftM_isRight mx).of_imp fun t ht => by
      rcases t with _ | _
      · exact ht.elim
      · rfl
  refine IsQueryBoundP.simulateQ_run_StateT_of_step A.queryBound (fun t st => ?_) st
  rcases t with n | x | i
  · exact hlift _
  · change IsQueryBoundP ((liftM ((ZeroDist.AdvSpec P).query (.inr x.1)) :
        OracleComp (ZeroDist.AdvSpec P) Bool) >>= _) _ 1
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨.inr Nat.one_pos, fun _ => hlift _⟩
  · exact hlift _

/-- **The ZeroDist adversary `B = (B₁, B₂)`** of the proof of Lemma C.9. `B₁` runs `A₁` on
`reductionImpl` and makes at most `q` queries; `B₂` receives `P'`, assembles `Th'` from its two
tables, runs `A₂(P')` and evaluates `Φ` on `g`, without its oracle. -/
def reduction {q : ℕ} (I : Interface D N ISpec σ α) (A : Adversary P D N ISpec S α q) :
    ZeroDist.Adversary P (S × ((Table P D N × Slice D N) × σ)) q where
  A1 := (simulateQ (reductionImpl I) A.A1).run ((fun _ => none, fun _ => none), I.init)
  A2 z P' := tail₁ I A P' z
  queryBound := isQueryBoundP_reductionImpl I A _

/-- With `f = f_{P'}`, `B` runs Game 0 for `A`. -/
theorem experiment_true_reduction {q : ℕ} (I : Interface D N ISpec σ α)
    (A : Adversary P D N ISpec S α q) :
    ZeroDist.experiment true (reduction I A) = game0 I A := by
  unfold ZeroDist.experiment game0
  refine bind_congr fun P' => ?_
  simp only [↓reduceIte, reduction]
  rw [simulateQ_oracle_reductionImpl]
  have hrun := map_run_simulateQ_answeredImpl_fHidden I P' A.A1
    ((fun _ => none, fun _ => none), I.init)
  dsimp only at hrun
  rw [merge_empty] at hrun
  rw [← hrun, bind_map_left]
  refine bind_congr fun ⟨x, ⟨H, g⟩, s⟩ => ?_
  unfold tail₁
  dsimp only [Prod.map, id]
  rw [← map_run_simulateQ_thPrimeImpl P' _ (H, g), bind_map_left]
  refine bind_congr fun ⟨w, H', g'⟩ => ?_
  dsimp only [Prod.map, id]
  rw [← map_run_simulateQ_sliceImpl₁ P' _ (H', g'), bind_map_left]
  rfl

/-- With `f = f₀`, `B` runs Game 1 for `A`. -/
theorem experiment_false_reduction {q : ℕ} (I : Interface D N ISpec σ α)
    (A : Adversary P D N ISpec S α q) :
    ZeroDist.experiment false (reduction I A) = game1 I A := by
  unfold ZeroDist.experiment game1
  refine bind_congr fun P' => ?_
  simp only [Bool.false_eq_true, ↓reduceIte, reduction]
  rw [simulateQ_oracle_reductionImpl, answeredImpl_fZero]

/-- **Lemma C.9** (hidden-slice reprogramming), reduction form: the difference of the two game
probabilities is the ZeroDist advantage of `B = reduction I A`, which makes at most `q` queries. -/
theorem abs_game_sub_eq_advantage {q : ℕ} (I : Interface D N ISpec σ α)
    (A : Adversary P D N ISpec S α q) :
    |(Pr{let b ← game0 I A}[b = true]).toReal - (Pr{let b ← game1 I A}[b = true]).toReal| =
      ZeroDist.advantage (reduction I A) := by
  rw [ZeroDist.advantage, experiment_true_reduction, experiment_false_reduction]

/-- **Lemma C.9** (hidden-slice reprogramming, classical case), one-sided forms. If the first
stage evaluates `Th` at most `q` times, the probabilities that Game 0 and Game 1 report `1` differ
by at most `q / |P|`, in either direction. Queries to `Σ` and the second stage's evaluations are
not counted. -/
theorem prEvent_game_le [Fintype P] {q : ℕ} (I : Interface D N ISpec σ α)
    (A : Adversary P D N ISpec S α q) :
    Pr{let b ← game0 I A}[b = true] ≤ Pr{let b ← game1 I A}[b = true] + q / Fintype.card P ∧
      Pr{let b ← game1 I A}[b = true] ≤ Pr{let b ← game0 I A}[b = true] + q / Fintype.card P := by
  rw [← experiment_true_reduction I A, ← experiment_false_reduction I A]
  exact ZeroDist.prEvent_experiment_le (reduction I A)

/-- **Lemma C.9** (hidden-slice reprogramming, classical case). If the first stage evaluates `Th`
at most `q` times, `|Pr[A^{G0} ⇒ 1] − Pr[A^{G1} ⇒ 1]| ≤ q / |P|`. -/
theorem abs_game_sub_le [Fintype P] {q : ℕ} (I : Interface D N ISpec σ α)
    (A : Adversary P D N ISpec S α q) :
    |(Pr{let b ← game0 I A}[b = true]).toReal - (Pr{let b ← game1 I A}[b = true]).toReal| ≤
      q / Fintype.card P := by
  rw [abs_game_sub_eq_advantage]
  exact ZeroDist.advantage_le (reduction I A)

end HiddenSlice

end ShrincsSecurity.Notions.Generic

end
