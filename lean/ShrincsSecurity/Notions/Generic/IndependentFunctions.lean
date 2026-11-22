module

public import ShrincsSecurity.Notions.Generic.CollectionLemma
public import ShrincsSecurity.Repro.Defs
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Evaluations of independent functions are harmless in the ideal model

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Lemma 4.2** (lines 2608–2620), proved
in **Section D.3** (lines 6761–6801).

## Model

The paper's attacked function `G` is whatever the experiment `Prop` evaluates: its challenger,
auxiliary oracles and win condition. Here an experiment is a handler `impl` of the experiment's
oracles `spec` on a state `σ`, behind the adversary's private coins (`coinImpl σ + impl`, the form
of every experiment in this development), with an initial state and a win condition that read
`σ` only. A further function, modelled as a random oracle independent of the experiment, is the
*extra* function `E : X → Y` (`ExtSpec X Y`), sampled lazily by VCVio's
`OracleSpec.randomOracle` on its own cache (`withExt impl`, which runs `impl` and the random
oracle side by side with `QueryImpl.parallelStateT`). Several independent functions are one extra
function on the sum of their domains, so one extra function is no loss of generality.

## Main statements

* `run_simulateQ_simExt`: the simulation, step by step. `A'` runs `A` through `simExt`: it
  forwards its coins and the experiment's oracles and answers `E` itself by lazy sampling with its
  own coins. Run against the experiment, `A'` produces exactly the joint distribution of `A`'s
  output, the experiment's state, and `E`'s table. It composes over stages (the table is passed
  on), which is how the two-stage instances use it.
* `gameExt_eq_game_dropExt`: **Lemma 4.2, `≤` direction**, for a one-stage experiment: the
  experiment with `E` run by `A` is the experiment without `E` run by `A' = dropExt A`, an equality
  of distributions, hence of success probabilities (`prEvent_gameExt_eq`).
* `isQueryBoundP_dropExt`: `A'` makes no more queries to the experiment's oracles than `A`: any
  query bound of `A` that counts no private coins and no evaluation of `E` (`liftPred p`) holds for
  `A'` (`p`). `A'` makes no query to `E` at all.
* `gameExt_addExt`, `isQueryBoundP_addExt`: **Lemma 4.2, `≥` direction**: an adversary without
  `E` is an adversary with `E` (`addExt`) under the same bounds and with the same success
  probability.
* Instances: the first-stage handler of Lemma C.9's Game 0 and hence **SM-TCR of a member**
  (`smtcrGameExt_eq`, `smtcrGameExt_addAdv`, Definition D.1 / Definition 4.12 stand-alone), where
  the reduction's own evaluations of further tweakable hashes are the extra function; **adaptive
  reprogramming** (`reproAdvantageExt_eq`, Definition C.1) and **DI-Repro**
  (`diAdvantageExt_eq`, Definition C.2), where the reductions' own evaluations of `H^sl_msg` (or
  of the tweakable hashes) are the extra function. In each case the bounds `q` (and `R`) of the
  experiment carry over unchanged.

## Deviations from the paper

* Classical adversaries only; the superposition case of the lemma is not formalised.
* "Time measured in function evaluations" is modelled by query bounds: the bounds of the
  experiment's oracles carry over, and `A'` makes no query to `E`. `A'` draws private coins to
  answer `E`; the private coins are unbounded in every experiment here, as in the paper (`ξ`
  counts function evaluations, and the simulated answers "cost no evaluation").
* The paper's parameter `ξ` (all evaluations, `q_G ≤ ξ`) is not a separate bound: an adversary
  with `E` is bounded only on the experiment's oracles, so `InSec(G; ξ, p, q_G)` and
  `InSec(G; q_G, p)` range over the same experiment bounds.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

namespace IndependentFunctions

open HiddenSlice (coinImpl coinImpl_run)
open CollectionLemma (fuse fuse_run run_simulateQ_run_simulateQ run_simulateQ_coinImpl)

/-! ## The generic simulation -/

section generic

variable {ι : Type} {spec : OracleSpec ι} {X Y : Type} [DecidableEq X] [SampleableType Y]

/-- Evaluations of the extra function `E : X → Y`, independent of the experiment. -/
abbrev ExtSpec (X Y : Type) : OracleSpec X := X →ₒ Y

/-- The table of the lazily sampled `E`. -/
abbrev ExtCache (X Y : Type) : Type := (ExtSpec X Y).QueryCache

/-- The experiment's handler extended by the independent random oracle `E`: private coins, the
experiment's oracles `impl` on its state, and `E` sampled lazily on its own cache. -/
def withExt {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + (spec + ExtSpec X Y)) (StateT (σ × ExtCache X Y) ProbComp) :=
  coinImpl (σ × ExtCache X Y) + QueryImpl.parallelStateT impl (ExtSpec X Y).randomOracle

/-- The handler of `A'` (Section D.3): private coins and the experiment's oracles are forwarded;
an evaluation of `E` is answered by lazy sampling with `A'`'s own coins, on `A'`'s table. -/
def simExt : QueryImpl (unifSpec + (spec + ExtSpec X Y))
    (StateT (ExtCache X Y) (OracleComp (unifSpec + spec))) :=
  (fun n => StateT.mk fun c => (fun u => (u, c)) <$>
      (liftM ((unifSpec + spec).query (.inl n)) : OracleComp (unifSpec + spec) (unifSpec.Range n)) :
    QueryImpl unifSpec (StateT (ExtCache X Y) (OracleComp (unifSpec + spec)))) +
  ((fun t => StateT.mk fun c => (fun u => (u, c)) <$>
      (liftM ((unifSpec + spec).query (.inr t)) : OracleComp (unifSpec + spec) (spec.Range t)) :
    QueryImpl spec (StateT (ExtCache X Y) (OracleComp (unifSpec + spec)))) +
   (fun x => StateT.mk fun c =>
      (liftM (((ExtSpec X Y).randomOracle x).run c) : OracleComp (unifSpec + spec) (Y × ExtCache X Y)) :
    QueryImpl (ExtSpec X Y) (StateT (ExtCache X Y) (OracleComp (unifSpec + spec)))))

/-- **The adversary `A'`** of Section D.3: `A` run through `simExt` from the empty table. -/
def dropExt {α : Type} (A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α) :
    OracleComp (unifSpec + spec) α :=
  (simulateQ simExt A).run' ∅

/-- A lifted `ProbComp` run by the experiment draws only private coins and leaves its state. -/
theorem run_simulateQ_liftM {σ β : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : ProbComp β) (s : σ) :
    (simulateQ (coinImpl σ + impl) (liftM oa : OracleComp (unifSpec + spec) β)).run s =
      (fun b => (b, s)) <$> oa := by
  rw [show simulateQ (coinImpl σ + impl) (liftM oa : OracleComp (unifSpec + spec) β) =
      simulateQ (coinImpl σ) oa from QueryImpl.simulateQ_add_liftComp_left _ _ oa]
  exact run_simulateQ_coinImpl σ oa s

/-- One step of `A'` run by the experiment is one step of the experiment extended by `E`. -/
theorem fuse_simExt {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) :
    fuse (coinImpl σ + impl) (simExt (X := X) (Y := Y)) = withExt impl := by
  funext t
  refine StateT.ext fun st => ?_
  obtain ⟨s, c⟩ := st
  rw [fuse_run]
  rcases t with n | t | x
  · change (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ (coinImpl σ + impl)
        ((fun u => (u, c)) <$> (liftM ((unifSpec + spec).query (.inl n)) :
          OracleComp (unifSpec + spec) (unifSpec.Range n)))).run s = (coinImpl _ n).run (s, c)
    rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    change _ <$> (coinImpl σ n).run s = _
    simp only [coinImpl_run, map_bind, map_pure]
  · change (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ (coinImpl σ + impl)
        ((fun u => (u, c)) <$> (liftM ((unifSpec + spec).query (.inr t)) :
          OracleComp (unifSpec + spec) (spec.Range t)))).run s =
      Prod.map id (·, c) <$> (impl t).run s
    rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    rfl
  · change (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ (coinImpl σ + impl)
        (liftM (((ExtSpec X Y).randomOracle x).run c) :
          OracleComp (unifSpec + spec) (Y × ExtCache X Y))).run s =
      Prod.map id (s, ·) <$> ((ExtSpec X Y).randomOracle x).run c
    rw [run_simulateQ_liftM, Functor.map_map]
    rfl

/-- **The simulation of Section D.3**, for a whole run: `A` run through `simExt` on the table
`c`, run by the experiment from `s`, is `A` run by the experiment extended by `E` from `(s, c)`,
up to rearranging the output; the joint distribution of the output, the experiment's state and
`E`'s table is unchanged. -/
theorem run_simulateQ_simExt {σ α : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α) (s : σ) (c : ExtCache X Y) :
    (simulateQ (coinImpl σ + impl) ((simulateQ simExt A).run c)).run s =
      (fun z => ((z.1, z.2.2), z.2.1)) <$> (simulateQ (withExt impl) A).run (s, c) := by
  rw [run_simulateQ_run_simulateQ, fuse_simExt]

/-- **The simulation of Section D.3**, from the empty table, forgetting the table. -/
theorem run_simulateQ_dropExt {σ α : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α) (s : σ) :
    (simulateQ (coinImpl σ + impl) (dropExt A)).run s =
      Prod.map id Prod.fst <$> (simulateQ (withExt impl) A).run (s, ∅) := by
  rw [dropExt, StateT.run'_eq, simulateQ_map, StateT.run_map, run_simulateQ_simExt,
    Functor.map_map]
  rfl

/-- A query of the experiment extended by `E` counted by a predicate `p` of the experiment
without `E`; evaluations of `E` are not counted. -/
def liftPred (p : ℕ ⊕ ι → Prop) : ℕ ⊕ (ι ⊕ X) → Prop
  | .inl n => p (.inl n)
  | .inr (.inl t) => p (.inr t)
  | .inr (.inr _) => False

instance (p : ℕ ⊕ ι → Prop) [DecidablePred p] : DecidablePred (liftPred (X := X) p) :=
  fun x => by rcases x with _ | _ | _ <;> simp only [liftPred] <;> infer_instance

omit [DecidableEq X] [SampleableType Y] in
/-- A lifted `ProbComp` queries only private coins. -/
theorem isQueryBoundP_liftM_zero {β : Type} {p : ℕ ⊕ ι → Prop} [DecidablePred p]
    (hcoin : ∀ n, ¬ p (.inl n)) (oa : ProbComp β) :
    (liftM oa : OracleComp (unifSpec + spec) β).IsQueryBoundP p 0 := by
  refine IsQueryBoundP.of_imp (p' := fun t => t.isRight = true) (fun t ht => ?_)
    (isQueryBoundP_liftM_isRight _)
  rcases t with n | t
  · exact absurd ht (hcoin n)
  · rfl

/-- **Query bounds of `A'`** (Section D.3): every query bound of `A` on the experiment's oracles
holds for `A'` run from any table, provided it counts no private coins. -/
theorem isQueryBoundP_run_simExt {α : Type} {p : ℕ ⊕ ι → Prop} [DecidablePred p]
    (hcoin : ∀ n, ¬ p (.inl n)) {A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α} {q : ℕ}
    (h : A.IsQueryBoundP (liftPred p) q) (c : ExtCache X Y) :
    ((simulateQ simExt A).run c).IsQueryBoundP p q := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht c => ?_) (fun t ht c => ?_) c
  · rcases t with n | t | x
    · exact absurd ht (hcoin n)
    · change IsQueryBoundP ((fun u => (u, c)) <$> (liftM ((unifSpec + spec).query (.inr t)) :
        OracleComp (unifSpec + spec) (spec.Range t))) p 1
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · exact absurd ht id
  · rcases t with n | t | x
    · change IsQueryBoundP ((fun u => (u, c)) <$> (liftM ((unifSpec + spec).query (.inl n)) :
        OracleComp (unifSpec + spec) (unifSpec.Range n))) p 0
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun h => absurd h (hcoin n)
    · change IsQueryBoundP ((fun u => (u, c)) <$> (liftM ((unifSpec + spec).query (.inr t)) :
        OracleComp (unifSpec + spec) (spec.Range t))) p 0
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun h => absurd h ht
    · exact isQueryBoundP_liftM_zero hcoin _

/-- **Query bounds of `A'`** from the empty table. -/
theorem isQueryBoundP_dropExt {α : Type} {p : ℕ ⊕ ι → Prop} [DecidablePred p]
    (hcoin : ∀ n, ¬ p (.inl n)) {A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α} {q : ℕ}
    (h : A.IsQueryBoundP (liftPred p) q) : (dropExt A).IsQueryBoundP p q := by
  rw [dropExt, StateT.run'_eq, isQueryBoundP_map_iff]
  exact isQueryBoundP_run_simExt hcoin h ∅

/-- An adversary without `E` seen as an adversary with `E` that never evaluates it. -/
def addExtImpl : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + (spec + ExtSpec X Y))) :=
  (fun n => (liftM ((unifSpec + (spec + ExtSpec X Y)).query (.inl n)) :
      OracleComp (unifSpec + (spec + ExtSpec X Y)) (unifSpec.Range n)) : QueryImpl unifSpec _) +
  (fun t => (liftM ((unifSpec + (spec + ExtSpec X Y)).query (.inr (.inl t))) :
      OracleComp (unifSpec + (spec + ExtSpec X Y)) (spec.Range t)) : QueryImpl spec _)

/-- The adversary `B` with access to `E`, which it never evaluates. -/
def addExt {α : Type} (B : OracleComp (unifSpec + spec) α) :
    OracleComp (unifSpec + (spec + ExtSpec X Y)) α :=
  simulateQ addExtImpl B

/-- An adversary that never evaluates `E` leaves `E`'s table untouched. -/
theorem run_simulateQ_addExt {σ α : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (B : OracleComp (unifSpec + spec) α) (s : σ) (c : ExtCache X Y) :
    (simulateQ (withExt impl) (addExt B)).run (s, c) =
      Prod.map id (·, c) <$> (simulateQ (coinImpl σ + impl) B).run s := by
  rw [addExt, ← QueryImpl.simulateQ_compose]
  refine (map_run_simulateQ_eq_of_query_map_eq _ _ (·, c) (fun t s => ?_) B s).symm
  rcases t with n | t
  · change _ = (simulateQ (withExt impl) (liftM ((unifSpec + (spec + ExtSpec X Y)).query
      (.inl n)))).run (s, c)
    rw [simulateQ_spec_query]
    exact HiddenSlice.map_coinImpl_run _ n s
  · change _ = (simulateQ (withExt impl) (liftM ((unifSpec + (spec + ExtSpec X Y)).query
      (.inr (.inl t))))).run (s, c)
    rw [simulateQ_spec_query]
    rfl

omit [DecidableEq X] [SampleableType Y] in
/-- `addExt B` satisfies every query bound of `B`, with evaluations of `E` not counted. -/
theorem isQueryBoundP_addExt {α : Type} {p : ℕ ⊕ ι → Prop} [DecidablePred p]
    {B : OracleComp (unifSpec + spec) α} {q : ℕ} (h : B.IsQueryBoundP p q) :
    (addExt (X := X) (Y := Y) B).IsQueryBoundP (liftPred p) q := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | t
    · change IsQueryBoundP (liftM ((unifSpec + (spec + ExtSpec X Y)).query (.inl n)) :
        OracleComp (unifSpec + (spec + ExtSpec X Y)) (unifSpec.Range n)) (liftPred p) 1
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
    · change IsQueryBoundP (liftM ((unifSpec + (spec + ExtSpec X Y)).query (.inr (.inl t))) :
        OracleComp (unifSpec + (spec + ExtSpec X Y)) (spec.Range t)) (liftPred p) 1
      rw [isQueryBoundP_query_iff]
      exact fun _ => Nat.one_pos
  · rcases t with n | t
    · change IsQueryBoundP (liftM ((unifSpec + (spec + ExtSpec X Y)).query (.inl n)) :
        OracleComp (unifSpec + (spec + ExtSpec X Y)) (unifSpec.Range n)) (liftPred p) 0
      rw [isQueryBoundP_query_iff]
      exact fun h => absurd h ht
    · change IsQueryBoundP (liftM ((unifSpec + (spec + ExtSpec X Y)).query (.inr (.inl t))) :
        OracleComp (unifSpec + (spec + ExtSpec X Y)) (spec.Range t)) (liftPred p) 0
      rw [isQueryBoundP_query_iff]
      exact fun h => absurd h ht

/-! ### One-stage experiments -/

/-- A one-stage experiment `Prop`: sample the initial state, run the adversary against private
coins and the experiment's oracles `impl`, and decide from the adversary's output and the final
state. -/
def game {σ α β : Type} (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (fin : α → σ → ProbComp β) (A : OracleComp (unifSpec + spec) α) : ProbComp β := do
  let s ← init
  let z ← (simulateQ (coinImpl σ + impl) A).run s
  fin z.1 z.2

/-- The experiment `Prop` for an adversary that may also evaluate the independent random
oracle `E`. The challenger, the oracles and the win condition do not read `E`. -/
def gameExt {σ α β : Type} (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (fin : α → σ → ProbComp β) (A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α) :
    ProbComp β := do
  let s ← init
  let z ← (simulateQ (withExt impl) A).run (s, ∅)
  fin z.1 z.2.1

/-- **Lemma 4.2, `≤` direction** (Section D.3): the experiment run by `A`, which also evaluates
the independent random oracle `E`, is the experiment run by `A' = dropExt A`, which simulates
`E` with its own coins. -/
theorem gameExt_eq_game_dropExt {σ α β : Type} (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp)) (fin : α → σ → ProbComp β)
    (A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α) :
    gameExt init impl fin A = game init impl fin (dropExt A) := by
  unfold gameExt game
  refine bind_congr fun s => ?_
  rw [run_simulateQ_dropExt, bind_map_left]
  rfl

/-- **Lemma 4.2, `≤` direction**, in probabilities. -/
theorem prEvent_gameExt_eq {σ α β : Type} (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp)) (fin : α → σ → ProbComp β)
    (A : OracleComp (unifSpec + (spec + ExtSpec X Y)) α) (E : β → Prop) :
    Pr{let b ← gameExt init impl fin A}[E b] = Pr{let b ← game init impl fin (dropExt A)}[E b] := by
  rw [gameExt_eq_game_dropExt]

/-- **Lemma 4.2, `≥` direction**: an adversary without `E` is an adversary with `E`. -/
theorem gameExt_addExt {σ α β : Type} (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp)) (fin : α → σ → ProbComp β)
    (B : OracleComp (unifSpec + spec) α) :
    gameExt init impl fin (addExt (X := X) (Y := Y) B) = game init impl fin B := by
  unfold gameExt game
  refine bind_congr fun s => ?_
  rw [run_simulateQ_addExt, bind_map_left]
  rfl

end generic

/-! ## Instance: Game 0 of Lemma C.9 and SM-TCR of a member -/

section hiddenSlice

open HiddenSlice

variable {P D N : Type} [DecidableEq P] [DecidableEq D] [SampleableType N]
variable {ιI : Type} {ISpec : OracleSpec ιI} {σ α S : Type}
variable {X Y : Type} [DecidableEq X] [SampleableType Y]

/-- Game 0's first-stage oracles: `Th` on the table and `Σ` on the hidden slice. -/
def phase1Oracles (I : Interface D N ISpec σ α) (P' : P) :
    QueryImpl (ROSpec P D N + ISpec) (StateT (Table P D N × σ) ProbComp) :=
  (fun x => StateT.mk fun st =>
      (fun z => (z.1, (z.2, st.2))) <$> lazyStep ($ᵗ N) st.1 x :
    QueryImpl (ROSpec P D N) (StateT (Table P D N × σ) ProbComp)) +
  (fun i => sigmaStep I (sliceImpl₀ P') i : QueryImpl ISpec (StateT (Table P D N × σ) ProbComp))

theorem phase1₀_eq (I : Interface D N ISpec σ α) (P' : P) :
    phase1₀ I P' = coinImpl (Table P D N × σ) + phase1Oracles I P' := rfl

/-- Game 0's second-stage oracle `Th` on the table. -/
def roOracle : QueryImpl (ROSpec P D N) (StateT (Table P D N) ProbComp) :=
  fun x => StateT.mk fun K => lazyStep ($ᵗ N) K x

theorem roImpl₀_eq :
    roImpl₀ (P := P) (D := D) (N := N) =
      coinImpl (Table P D N) + roOracle (P := P) (D := D) (N := N) :=
  rfl

variable (P D N) in
/-- An adversary for Game 0 of Lemma C.9 that may also evaluate the independent random oracle
`E : X → Y` in both stages; its first stage evaluates `Th` at most `q` times. -/
structure AdversaryExt (ISpec : OracleSpec ιI) (S α : Type) (q : ℕ) (X Y : Type) where
  /-- The first stage, with access to `Th`, `Σ` and `E`. -/
  A1 : OracleComp (unifSpec + ((ROSpec P D N + ISpec) + ExtSpec X Y)) S
  /-- The second stage, with access to `Th` and `E`. -/
  A2 : S → P → OracleComp (unifSpec + (ROSpec P D N + ExtSpec X Y)) α
  /-- The first stage evaluates `Th` at most `q` times; evaluations of `E` are not counted. -/
  queryBound : A1.IsQueryBoundP (liftPred (IsROQuery P D)) q

variable [SampleableType P]

/-- **Game 0 of Lemma C.9 with the independent random oracle `E`**: as `game0`, with one lazily
sampled `E` shared by both stages; `Σ` and `Φ` do not read `E`. -/
def game0Ext {q : ℕ} (I : Interface D N ISpec σ α) (A : AdversaryExt P D N ISpec S α q X Y) :
    ProbComp Bool := do
  let P' ← $ᵗ P
  let z ← (simulateQ (withExt (phase1Oracles I P')) A.A1).run ((fun _ => none, I.init), ∅)
  let w ← (simulateQ (withExt roOracle) (A.A2 z.1 P')).run (z.2.1.1, z.2.2)
  let v ← (simulateQ (sliceImpl₀ P') (I.pred z.2.1.2 w.1)).run w.2.1
  return v.1

/-- **The adversary `A'`** for Game 0: both stages simulate `E` with their own coins; the first
stage hands its table to the second. -/
def dropAdv {q : ℕ} (A : AdversaryExt P D N ISpec S α q X Y) :
    Adversary P D N ISpec (S × ExtCache X Y) α q where
  A1 := (simulateQ simExt A.A1).run ∅
  A2 s P' := (simulateQ simExt (A.A2 s.1 P')).run' s.2
  queryBound := isQueryBoundP_run_simExt (fun _ h => h) A.queryBound ∅

/-- An adversary for Game 0 seen as one that never evaluates `E`. -/
def addAdv {q : ℕ} (B : Adversary P D N ISpec S α q) : AdversaryExt P D N ISpec S α q X Y where
  A1 := addExt B.A1
  A2 s P' := addExt (B.A2 s P')
  queryBound := isQueryBoundP_addExt B.queryBound

/-- **Lemma 4.2 for Game 0 of Lemma C.9**, `≤` direction. -/
theorem game0Ext_eq {q : ℕ} (I : Interface D N ISpec σ α)
    (A : AdversaryExt P D N ISpec S α q X Y) : game0Ext I A = game0 I (dropAdv A) := by
  unfold game0Ext game0
  refine bind_congr fun P' => ?_
  rw [phase1₀_eq]
  change _ = (simulateQ (coinImpl (Table P D N × σ) + phase1Oracles I P')
    ((simulateQ simExt A.A1).run ∅)).run
    (fun _ => none, I.init) >>= _
  rw [run_simulateQ_simExt, bind_map_left]
  refine bind_congr fun z => ?_
  change _ = (simulateQ (roImpl₀ (N := N)) ((simulateQ simExt (A.A2 z.1 P')).run' z.2.2)).run
    z.2.1.1 >>= _
  rw [roImpl₀_eq, StateT.run'_eq, simulateQ_map, StateT.run_map, run_simulateQ_simExt,
    Functor.map_map, bind_map_left]

/-- **Lemma 4.2 for Game 0 of Lemma C.9**, `≥` direction. -/
theorem game0Ext_addAdv {q : ℕ} (I : Interface D N ISpec σ α) (B : Adversary P D N ISpec S α q) :
    game0Ext I (addAdv (X := X) (Y := Y) B) = game0 I B := by
  unfold game0Ext game0
  refine bind_congr fun P' => ?_
  change (simulateQ (withExt (phase1Oracles I P')) (addExt B.A1)).run _ >>= _ = _
  rw [run_simulateQ_addExt, ← phase1₀_eq, bind_map_left]
  refine bind_congr fun z => ?_
  change (simulateQ (withExt roOracle) (addExt (B.A2 z.1 P'))).run _ >>= _ = _
  rw [run_simulateQ_addExt, ← roImpl₀_eq, bind_map_left]
  rfl

end hiddenSlice

section smtcr

open HiddenSlice CollectionLemma

variable {P T X M N : Type} [DecidableEq P] [DecidableEq T] [DecidableEq X] [DecidableEq N]
  [SampleableType N] [SampleableType P] [DecidableEq M] {S : Type} {q : ℕ}
variable {U W : Type} [DecidableEq U] [SampleableType W]

/-- **SM-TCR of a member** (Definition D.1 without the collection oracle) for an adversary that
may also evaluate an independent random oracle `E : U → W`, e.g. further tweakable hashes that
the reduction evaluates itself. -/
abbrev smtcrGameExt (emb : M → X) (p : ℕ)
    (A : AdversaryExt P (T × X) N (SMTCRSpec T M N) S (ℕ × M) q U W) : ProbComp Bool :=
  game0Ext (smtcrInterface emb p) A

/-- **Lemma 4.2 for SM-TCR of a member**, `≤` direction: `A'` evaluates `Th` in its first stage
at most `q` times, as `A`, and wins with the same probability. -/
theorem smtcrGameExt_eq (emb : M → X) (p : ℕ)
    (A : AdversaryExt P (T × X) N (SMTCRSpec T M N) S (ℕ × M) q U W) :
    smtcrGameExt emb p A = smtcrGame emb p (dropAdv A) :=
  game0Ext_eq _ A

/-- **Lemma 4.2 for SM-TCR of a member**, in probabilities. -/
theorem prEvent_smtcrGameExt_eq (emb : M → X) (p : ℕ)
    (A : AdversaryExt P (T × X) N (SMTCRSpec T M N) S (ℕ × M) q U W) :
    Pr{let b ← smtcrGameExt emb p A}[b = true] =
      Pr{let b ← smtcrGame emb p (dropAdv A)}[b = true] := by
  rw [smtcrGameExt_eq]

/-- **Lemma 4.2 for SM-TCR of a member**, `≥` direction. -/
theorem smtcrGameExt_addAdv (emb : M → X) (p : ℕ)
    (B : Adversary P (T × X) N (SMTCRSpec T M N) S (ℕ × M) q) :
    smtcrGameExt emb p (addAdv (X := U) (Y := W) B) = smtcrGame emb p B :=
  game0Ext_addAdv _ B

end smtcr

/-! ## Instance: adaptive reprogramming (Definitions C.1 and C.2) -/

section repro

open ShrincsSecurity.Repro

variable {X₁ X₂ Y : Type} [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y]
variable {U W : Type} [DecidableEq U] [SampleableType W]

/-- The oracles of `Repro_b` other than private coins: `O_b` and `Reprogram`. -/
def reproOracles (b : Bool) :
    QueryImpl (HashSpec X₁ X₂ Y + ReproSpec X₁ X₂) (StateT (X₁ × X₂ → Y) ProbComp) :=
  (fun x => hashImpl id x : QueryImpl (HashSpec X₁ X₂ Y) (StateT (X₁ × X₂ → Y) ProbComp)) +
    (fun x₂ => reproImpl b x₂ : QueryImpl (ReproSpec X₁ X₂) (StateT (X₁ × X₂ → Y) ProbComp))

theorem gameImpl_eq (b : Bool) :
    gameImpl (X₁ := X₁) (X₂ := X₂) (Y := Y) b =
      coinImpl (X₁ × X₂ → Y) + reproOracles (X₁ := X₁) (X₂ := X₂) (Y := Y) b := rfl

/-- The oracles of `DI-Repro_b` other than private coins: `O_b` and the guarded `Reprogram`. -/
def diReproOracles (b : Bool) : QueryImpl (HashSpec X₁ X₂ Y + DIReproSpec X₁ X₂)
    (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp) :=
  (fun x => hashImpl Prod.fst x :
      QueryImpl (HashSpec X₁ X₂ Y) (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp)) +
    (fun x₂ => diReproImpl b x₂ :
      QueryImpl (DIReproSpec X₁ X₂) (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp))

theorem diGameImpl_eq (b : Bool) :
    diGameImpl (X₁ := X₁) (X₂ := X₂) (Y := Y) b =
      coinImpl ((X₁ × X₂ → Y) × Finset X₂) + diReproOracles (X₁ := X₁) (X₂ := X₂) (Y := Y) b :=
      rfl

/-- A `Repro` adversary that may also evaluate an independent random oracle `E : U → W` (e.g.
the reduction's own evaluations of `H^sl_msg` or of tweakable hashes): at most `q` queries to
`O_b` and at most `R` calls to `Reprogram`; evaluations of `E` are not counted. -/
structure ReproAdversaryExt (X₁ X₂ Y : Type) (q R : ℕ) (U W : Type) where
  /-- The distinguisher. -/
  run : OracleComp (unifSpec + ((HashSpec X₁ X₂ Y + ReproSpec X₁ X₂) + ExtSpec U W)) Bool
  /-- At most `q` queries to `O_b`. -/
  hashBound : run.IsQueryBoundP (liftPred (IsHashQuery X₁ X₂)) q
  /-- At most `R` calls to `Reprogram`. -/
  reproBound : run.IsQueryBoundP (liftPred (IsReproQuery X₁ X₂)) R

/-- A `DI-Repro` adversary that may also evaluate an independent random oracle `E : U → W`. -/
structure DIAdversaryExt (X₁ X₂ Y : Type) (q R : ℕ) (U W : Type) where
  /-- The distinguisher. -/
  run : OracleComp (unifSpec + ((HashSpec X₁ X₂ Y + DIReproSpec X₁ X₂) + ExtSpec U W)) Bool
  /-- At most `q` queries to `O_b`. -/
  hashBound : run.IsQueryBoundP (liftPred (IsHashQuery X₁ X₂)) q
  /-- At most `R` calls to `Reprogram`, refused calls included. -/
  reproBound : run.IsQueryBoundP (liftPred (IsReproQuery X₁ X₂)) R

/-- **The adversary `A'`** for `Repro`: same bounds `q` and `R`. -/
def dropReproAdv {q R : ℕ} (A : ReproAdversaryExt X₁ X₂ Y q R U W) : Adversary X₁ X₂ Y q R where
  run := dropExt A.run
  hashBound := isQueryBoundP_dropExt (fun _ h => h) A.hashBound
  reproBound := isQueryBoundP_dropExt (fun _ h => h) A.reproBound

/-- **The adversary `A'`** for `DI-Repro`: same bounds `q` and `R`. -/
def dropDIAdv {q R : ℕ} (A : DIAdversaryExt X₁ X₂ Y q R U W) : DIAdversary X₁ X₂ Y q R where
  run := dropExt A.run
  hashBound := isQueryBoundP_dropExt (fun _ h => h) A.hashBound
  reproBound := isQueryBoundP_dropExt (fun _ h => h) A.reproBound

/-- A `Repro` adversary seen as one that never evaluates `E`. -/
def addReproAdv {q R : ℕ} (B : Adversary X₁ X₂ Y q R) : ReproAdversaryExt X₁ X₂ Y q R U W where
  run := addExt B.run
  hashBound := isQueryBoundP_addExt B.hashBound
  reproBound := isQueryBoundP_addExt B.reproBound

/-- A `DI-Repro` adversary seen as one that never evaluates `E`. -/
def addDIAdv {q R : ℕ} (B : DIAdversary X₁ X₂ Y q R) : DIAdversaryExt X₁ X₂ Y q R U W where
  run := addExt B.run
  hashBound := isQueryBoundP_addExt B.hashBound
  reproBound := isQueryBoundP_addExt B.reproBound

variable [Fintype X₁] [Fintype X₂]

/-- **`Repro_b(A)`** (Definition C.1) with the independent random oracle `E`. -/
noncomputable def experimentExt (b : Bool)
    (A : OracleComp (unifSpec + ((HashSpec X₁ X₂ Y + ReproSpec X₁ X₂) + ExtSpec U W)) Bool) :
    ProbComp Bool := do
  let O ← $ᵗ (X₁ × X₂ → Y)
  (simulateQ (withExt (reproOracles b)) A).run' (O, ∅)

/-- **`DI-Repro_b(A)`** (Definition C.2) with the independent random oracle `E`. -/
noncomputable def diExperimentExt (b : Bool)
    (A : OracleComp (unifSpec + ((HashSpec X₁ X₂ Y + DIReproSpec X₁ X₂) + ExtSpec U W)) Bool) :
    ProbComp Bool := do
  let O ← $ᵗ (X₁ × X₂ → Y)
  (simulateQ (withExt (diReproOracles b)) A).run' ((O, ∅), ∅)

/-- `Adv^Repro_{R,q}(A)` for an adversary with the independent random oracle `E`. -/
noncomputable def advantageExt {q R : ℕ} (A : ReproAdversaryExt X₁ X₂ Y q R U W) : ℝ :=
  |(Pr{let b ← experimentExt false A.run}[b = true]).toReal -
    (Pr{let b ← experimentExt true A.run}[b = true]).toReal|

/-- `Adv^DI-Repro_{R,q}(A)` for an adversary with the independent random oracle `E`. -/
noncomputable def diAdvantageExt {q R : ℕ} (A : DIAdversaryExt X₁ X₂ Y q R U W) : ℝ :=
  |(Pr{let b ← diExperimentExt false A.run}[b = true]).toReal -
    (Pr{let b ← diExperimentExt true A.run}[b = true]).toReal|

theorem experimentExt_eq (b : Bool)
    (A : OracleComp (unifSpec + ((HashSpec X₁ X₂ Y + ReproSpec X₁ X₂) + ExtSpec U W)) Bool) :
    experimentExt b A = experiment b (dropExt A) := by
  unfold experimentExt experiment
  refine bind_congr fun O => ?_
  rw [gameImpl_eq, StateT.run'_eq, StateT.run'_eq, run_simulateQ_dropExt, Functor.map_map]
  rfl

theorem diExperimentExt_eq (b : Bool)
    (A : OracleComp (unifSpec + ((HashSpec X₁ X₂ Y + DIReproSpec X₁ X₂) + ExtSpec U W)) Bool) :
    diExperimentExt b A = diExperiment b (dropExt A) := by
  unfold diExperimentExt diExperiment
  refine bind_congr fun O => ?_
  rw [diGameImpl_eq, StateT.run'_eq, StateT.run'_eq, run_simulateQ_dropExt, Functor.map_map]
  rfl

/-- **Lemma 4.2 for adaptive reprogramming** (Definition C.1), `≤` direction: `A'` makes at most
`q` hash queries and `R` reprogramming calls, as `A`, and has the same advantage. -/
theorem advantageExt_eq {q R : ℕ} (A : ReproAdversaryExt X₁ X₂ Y q R U W) :
    advantageExt A = advantage (dropReproAdv A) := by
  simp only [advantageExt, advantage, dropReproAdv, experimentExt_eq]

/-- **Lemma 4.2 for DI-Repro** (Definition C.2), `≤` direction: `A'` makes at most `q` hash
queries and `R` reprogramming calls, as `A`, and has the same advantage. -/
theorem diAdvantageExt_eq {q R : ℕ} (A : DIAdversaryExt X₁ X₂ Y q R U W) :
    diAdvantageExt A = diAdvantage (dropDIAdv A) := by
  simp only [diAdvantageExt, diAdvantage, dropDIAdv, diExperimentExt_eq]

theorem experimentExt_addExt (b : Bool)
    (B : OracleComp (unifSpec + (HashSpec X₁ X₂ Y + ReproSpec X₁ X₂)) Bool) :
    experimentExt b (addExt (X := U) (Y := W) B) = experiment b B := by
  unfold experimentExt experiment
  refine bind_congr fun O => ?_
  rw [gameImpl_eq, StateT.run'_eq, StateT.run'_eq, run_simulateQ_addExt, Functor.map_map]
  rfl

theorem diExperimentExt_addExt (b : Bool)
    (B : OracleComp (unifSpec + (HashSpec X₁ X₂ Y + DIReproSpec X₁ X₂)) Bool) :
    diExperimentExt b (addExt (X := U) (Y := W) B) = diExperiment b B := by
  unfold diExperimentExt diExperiment
  refine bind_congr fun O => ?_
  rw [diGameImpl_eq, StateT.run'_eq, StateT.run'_eq, run_simulateQ_addExt, Functor.map_map]
  rfl

/-- **Lemma 4.2 for adaptive reprogramming**, `≥` direction. -/
theorem advantageExt_addReproAdv {q R : ℕ} (B : Adversary X₁ X₂ Y q R) :
    advantageExt (addReproAdv (U := U) (W := W) B) = advantage B := by
  simp only [advantageExt, advantage, addReproAdv, experimentExt_addExt]

/-- **Lemma 4.2 for DI-Repro**, `≥` direction. -/
theorem diAdvantageExt_addDIAdv {q R : ℕ} (B : DIAdversary X₁ X₂ Y q R) :
    diAdvantageExt (addDIAdv (U := U) (W := W) B) = diAdvantage B := by
  simp only [diAdvantageExt, diAdvantage, addDIAdv, diExperimentExt_addExt]

end repro

end IndependentFunctions

end ShrincsSecurity.Notions.Generic

end
