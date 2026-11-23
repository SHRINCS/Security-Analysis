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

/-! ## Step 3 of Lemma 4.1 (Appendix D.2): splitting a collection into one member and the rest -/

section singleMember

open HiddenSlice CollectionLemma

variable {P T M Rest N : Type} [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest]
  [SampleableType N]
variable {ιc : Type} {cs : OracleSpec ιc} {σ α S : Type}

/-- Lift slice queries of a single member `T × M` into the collection slice `T × (M ⊕ Rest)`. -/
def embedSliceImpl :
    QueryImpl (unifSpec + SliceSpec (T × M) N)
      (OracleComp (unifSpec + SliceSpec (T × (M ⊕ Rest)) N)) :=
  (fun n => (liftM ((unifSpec + SliceSpec (T × (M ⊕ Rest)) N).query (.inl n)) :
      OracleComp (unifSpec + SliceSpec (T × (M ⊕ Rest)) N) (unifSpec.Range n)) :
    QueryImpl unifSpec _) +
  (fun x => (liftM ((unifSpec + SliceSpec (T × (M ⊕ Rest)) N).query (.inr (x.1, .inl x.2))) :
      OracleComp (unifSpec + SliceSpec (T × (M ⊕ Rest)) N) N) :
    QueryImpl (SliceSpec (T × M) N) _)

/-- Lift a slice computation of a single member `T × M` into `T × (M ⊕ Rest)`. -/
def embedSliceComp {β : Type} (oa : OracleComp (unifSpec + SliceSpec (T × M) N) β) :
    OracleComp (unifSpec + SliceSpec (T × (M ⊕ Rest)) N) β :=
  simulateQ embedSliceImpl oa

/-- Embed a single-member interface `I` on `T × M` into the collection domain `T × (M ⊕ Rest)`. -/
def embedInterface (I : Interface (T × M) N cs σ α) :
    Interface (T × (M ⊕ Rest)) N cs σ α where
  init := I.init
  impl d := StateT.mk fun s => embedSliceComp ((I.impl d).run s)
  pred s a := embedSliceComp (I.pred s a)

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest] [SampleableType N] in
theorem support_embedSliceComp {β : Type} (oa : OracleComp (unifSpec + SliceSpec (T × M) N) β) :
    support (embedSliceComp (Rest := Rest) oa) = support oa := by
  unfold embedSliceComp
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rcases t with n | ⟨t, m⟩
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, support_bind]
        ext y
        simp only [Set.mem_iUnion, support_query, Set.mem_univ]
        exact exists_congr fun u => by
          rw [ih u]
          simp [embedSliceImpl]
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, support_bind]
        ext y
        simp only [Set.mem_iUnion, support_query, Set.mem_univ]
        exact exists_congr fun u => by
          rw [ih u]
          simp [embedSliceImpl]

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest] [SampleableType N] in
theorem allQueriesSatisfy_embedSliceComp {β : Type} (p : T → Bool)
    {oa : OracleComp (unifSpec + SliceSpec (T × M) N) β}
    (hoa : oa.AllQueriesSatisfy (SliceIn fun x : T × M => p x.1)) :
    (embedSliceComp (Rest := Rest) oa).AllQueriesSatisfy
      (SliceIn fun x : T × (M ⊕ Rest) => p x.1) := by
  unfold embedSliceComp
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hoa
      rcases t with n | ⟨t, m⟩
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        refine allQueriesSatisfy_bind ?_ fun u => ih u (hoa.2 u)
        exact (allQueriesSatisfy_query_iff _ _).2 trivial
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        refine allQueriesSatisfy_bind ?_ fun u => ih u (hoa.2 u)
        exact (allQueriesSatisfy_query_iff _ _).2 hoa.1

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest] [SampleableType N] in
/-- Embedding a single-member interface into `T × (M ⊕ Rest)` preserves `Discipline`. -/
theorem discipline_embedInterface {I : Interface (T × M) N cs σ α} {R : Reservation cs σ T}
    (hR : Discipline I R) :
    Discipline (embedInterface (Rest := Rest) I) R where
  accepted_refuse := hR.accepted_refuse
  run_of_refused s d h := by
    change embedSliceComp ((I.impl d).run s) = _
    rw [hR.run_of_refused s d h]
    exact simulateQ_pure _ _
  impl_queries s d h :=
    allQueriesSatisfy_embedSliceComp (R.chalRes d) (hR.impl_queries s d h)
  impl_support s d h z hz := by
    change z ∈ support (embedSliceComp ((I.impl d).run s)) at hz
    rw [support_embedSliceComp] at hz
    exact hR.impl_support s d h z hz
  pred_queries s a :=
    allQueriesSatisfy_embedSliceComp (R.res s) (hR.pred_queries s a)

/-- The split first-stage oracle signature: coins, member RO + challenge oracle, and extra-member RO. -/
abbrev SplitSpec1 (P T M Rest N : Type) (cs : OracleSpec ιc) :=
  unifSpec + ((ROSpec P (T × M) N + cs) + ExtSpec (P × T × Rest) N)

/-- The split second-stage oracle signature: coins, member RO, and extra-member RO. -/
abbrev SplitSpec2 (P T M Rest N : Type) :=
  unifSpec + (ROSpec P (T × M) N + ExtSpec (P × T × Rest) N)

/-- Split direct collection queries in `P × (T × (M ⊕ Rest))` into member queries in
`ROSpec P (T × M) N` and extra-member queries in `ExtSpec (P × T × Rest) N` (first stage). -/
def splitRO1Impl :
    QueryImpl (unifSpec + (ROSpec P (T × (M ⊕ Rest)) N + cs))
      (OracleComp (SplitSpec1 P T M Rest N cs)) :=
  (fun n => (liftM ((SplitSpec1 P T M Rest N cs).query (.inl n)) :
      OracleComp (SplitSpec1 P T M Rest N cs) (unifSpec.Range n)) : QueryImpl unifSpec _) +
  ((fun x => match x with
    | (p, (t, .inl m)) =>
        (liftM ((SplitSpec1 P T M Rest N cs).query (.inr (.inl (.inl (p, (t, m)))))) :
          OracleComp (SplitSpec1 P T M Rest N cs) N)
    | (p, (t, .inr r)) =>
        (liftM ((SplitSpec1 P T M Rest N cs).query (.inr (.inr (p, t, r)))) :
          OracleComp (SplitSpec1 P T M Rest N cs) N) :
      QueryImpl (ROSpec P (T × (M ⊕ Rest)) N) _) +
   (fun d => (liftM ((SplitSpec1 P T M Rest N cs).query (.inr (.inl (.inr d)))) :
      OracleComp (SplitSpec1 P T M Rest N cs) (cs.Range d)) : QueryImpl cs _))

/-- Split direct collection queries in `P × (T × (M ⊕ Rest))` into member queries and extra-member
queries (second stage). -/
def splitRO2Impl :
    QueryImpl (unifSpec + ROSpec P (T × (M ⊕ Rest)) N)
      (OracleComp (SplitSpec2 P T M Rest N)) :=
  (fun n => (liftM ((SplitSpec2 P T M Rest N).query (.inl n)) :
      OracleComp (SplitSpec2 P T M Rest N) (unifSpec.Range n)) : QueryImpl unifSpec _) +
  (fun x => match x with
    | (p, (t, .inl m)) =>
        (liftM ((SplitSpec2 P T M Rest N).query (.inr (.inl (p, (t, m))))) :
          OracleComp (SplitSpec2 P T M Rest N) N)
    | (p, (t, .inr r)) =>
        (liftM ((SplitSpec2 P T M Rest N).query (.inr (.inr (p, t, r)))) :
          OracleComp (SplitSpec2 P T M Rest N) N) :
      QueryImpl (ROSpec P (T × (M ⊕ Rest)) N) _)

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest] [SampleableType N] in
/-- Re-route a stand-alone adversary over the full collection `T × (M ⊕ Rest)` to an extended
adversary over the single member `T × M` plus the independent extra oracle `P × T × Rest → N`,
preserving the first-stage query bound `q`. -/
def splitAdv {q : ℕ} (B : Adversary P (T × (M ⊕ Rest)) N cs S α q) :
    AdversaryExt P (T × M) N cs S α q (P × T × Rest) N where
  A1 := simulateQ splitRO1Impl B.A1
  A2 s P' := simulateQ splitRO2Impl (B.A2 s P')
  queryBound := by
    refine IsQueryBoundP.simulateQ_of_step B.queryBound (fun t ht => ?_) (fun t ht => ?_)
    · rcases t with n | ⟨p, ⟨t, m | r⟩⟩ | d
      · exact absurd ht (by simp [IsROQuery])
      · change IsQueryBoundP (liftM ((SplitSpec1 P T M Rest N cs).query
            (.inr (.inl (.inl (p, (t, m)))))) :
            OracleComp (SplitSpec1 P T M Rest N cs) N) (liftPred (IsROQuery P (T × M))) 1
        rw [isQueryBoundP_query_iff]
        exact fun _ => Nat.one_pos
      · change IsQueryBoundP (liftM ((SplitSpec1 P T M Rest N cs).query
            (.inr (.inr (p, t, r)))) :
            OracleComp (SplitSpec1 P T M Rest N cs) N) (liftPred (IsROQuery P (T × M))) 1
        rw [isQueryBoundP_query_iff]
        exact fun h => absurd h id
      · exact absurd ht (by simp [IsROQuery])
    · rcases t with n | x | d
      · change IsQueryBoundP (liftM ((SplitSpec1 P T M Rest N cs).query (.inl n)) :
            OracleComp (SplitSpec1 P T M Rest N cs) (unifSpec.Range n))
            (liftPred (IsROQuery P (T × M))) 0
        rw [isQueryBoundP_query_iff]
        simp [liftPred, IsROQuery]
      · exact absurd trivial ht
      · change IsQueryBoundP (liftM ((SplitSpec1 P T M Rest N cs).query
            (.inr (.inl (.inr d)))) :
            OracleComp (SplitSpec1 P T M Rest N cs) (cs.Range d))
            (liftPred (IsROQuery P (T × M))) 0
        rw [isQueryBoundP_query_iff]
        simp [liftPred, IsROQuery]

/-- Merge the member table on `P × (T × M)` and the extra-member cache on `P × T × Rest` into a
single collection table on `P × (T × (M ⊕ Rest))`. -/
def mergeTable (K : Table P (T × M) N) (c : ExtCache (P × T × Rest) N) :
    Table P (T × (M ⊕ Rest)) N
  | (p, (t, .inl m)) => K (p, (t, m))
  | (p, (t, .inr r)) => c (p, t, r)

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest] [SampleableType N] in
theorem mergeTable_empty :
    mergeTable (P := P) (T := T) (M := M) (Rest := Rest) (N := N) (fun _ => none) ∅ =
      fun _ => none := by
  funext ⟨p, t, x⟩
  rcases x with m | r <;> rfl

omit [SampleableType N] in
private theorem mergeTable_update_inl (K : Table P (T × M) N) (c : ExtCache (P × T × Rest) N)
    (p : P) (t : T) (m : M) (v : N) :
    mergeTable (Function.update K (p, (t, m)) (some v)) c =
      Function.update (mergeTable K c) (p, (t, (.inl m : M ⊕ Rest))) (some v) := by
  funext ⟨p', t', x'⟩
  rcases x' with m' | r'
  · by_cases h : (p', (t', m')) = (p, (t, m))
    · cases h; simp [mergeTable]
    · have h' : (p', (t', (Sum.inl m' : M ⊕ Rest))) ≠ (p, (t, (Sum.inl m : M ⊕ Rest))) := by
        intro heq; apply h; cases heq; rfl
      simp [mergeTable, Function.update_of_ne h, Function.update_of_ne h']
  · simp [mergeTable]

omit [SampleableType N] in
private theorem mergeTable_cacheQuery_inr (K : Table P (T × M) N) (c : ExtCache (P × T × Rest) N)
    (p : P) (t : T) (r : Rest) (v : N) :
    mergeTable K (c.cacheQuery (p, t, r) v) =
      Function.update (mergeTable K c) (p, (t, (.inr r : M ⊕ Rest))) (some v) := by
  funext ⟨p', t', x'⟩
  rcases x' with m' | r'
  · simp [mergeTable]
  · by_cases h : (p', t', r') = (p, t, r)
    · cases h; simp [mergeTable, OracleSpec.QueryCache.cacheQuery]
    · have h' : (p', (t', (Sum.inr r' : M ⊕ Rest))) ≠ (p, (t, (Sum.inr r : M ⊕ Rest))) := by
        intro heq; apply h; cases heq; rfl
      simp [mergeTable, OracleSpec.QueryCache.cacheQuery, Function.update_of_ne h,
        Function.update_of_ne h']

theorem map_run_simulateQ_embedSliceComp {β : Type} (P' : P)
    (oa : OracleComp (unifSpec + SliceSpec (T × M) N) β)
    (K : Table P (T × M) N) (c : ExtCache (P × T × Rest) N) :
    Prod.map id (fun K' => mergeTable K' c) <$> (simulateQ (sliceImpl₀ P') oa).run K =
      (simulateQ (sliceImpl₀ P') (embedSliceComp oa)).run (mergeTable K c) := by
  rw [embedSliceComp, ← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ (fun K' => mergeTable K' c) (fun t K' => ?_)
    oa K
  rcases t with n | ⟨t, m⟩
  · change Prod.map id _ <$> (coinImpl _ n).run K' =
      (simulateQ (sliceImpl₀ P') (liftM ((unifSpec + SliceSpec (T × (M ⊕ Rest)) N).query
        (.inl n)))).run (mergeTable K' c)
    rw [simulateQ_spec_query]
    exact HiddenSlice.map_coinImpl_run _ n K'
  · change Prod.map id _ <$> lazyStep ($ᵗ N) K' (P', (t, m)) =
      (simulateQ (sliceImpl₀ P') (liftM ((unifSpec + SliceSpec (T × (M ⊕ Rest)) N).query
        (.inr (t, .inl m))))).run (mergeTable K' c)
    rw [simulateQ_spec_query]
    change _ = lazyStep ($ᵗ N) (mergeTable K' c) (P', (t, .inl m))
    refine map_lazyStep_eq_id _ _ _ _ _ _ rfl (fun _ _ => rfl) fun v _ => ?_
    exact Prod.ext rfl (mergeTable_update_inl K' c P' t m v)

/-- Splitting the full collection `T × (M ⊕ Rest)` into the single member `T × M` plus the
independent extra oracle `P × T × Rest → N` is exact in Game 0. -/
theorem game0_embedInterface_eq_game0Ext [SampleableType P] {q : ℕ}
    (I : Interface (T × M) N cs σ α) (B : Adversary P (T × (M ⊕ Rest)) N cs S α q) :
    game0 (embedInterface (Rest := Rest) I) B = game0Ext I (splitAdv B) := by
  unfold game0 game0Ext
  refine bind_congr fun P' => ?_
  have h1 :
      Prod.map id (fun st : (Table P (T × M) N × σ) × ExtCache (P × T × Rest) N =>
          (mergeTable st.1.1 st.2, st.1.2)) <$>
        (simulateQ (withExt (phase1Oracles I P')) (splitAdv B).A1).run ((fun _ => none, I.init), ∅) =
      (simulateQ (phase1₀ (embedInterface (Rest := Rest) I) P') B.A1).run
        (fun _ => none, (embedInterface (Rest := Rest) I).init) := by
    rw [← mergeTable_empty (P := P) (T := T) (M := M) (Rest := Rest) (N := N)]
    rw [splitAdv, ← QueryImpl.simulateQ_compose]
    refine map_run_simulateQ_eq_of_query_map_eq _ _
      (fun st : (Table P (T × M) N × σ) × ExtCache (P × T × Rest) N =>
        (mergeTable st.1.1 st.2, st.1.2)) (fun t st => ?_) B.A1 ((fun _ => none, I.init), ∅)
    obtain ⟨⟨K, s⟩, c⟩ := st
    rcases t with n | ⟨p, ⟨t, m | r⟩⟩ | d
    · change Prod.map id _ <$> (simulateQ (withExt (phase1Oracles I P'))
        (liftM ((SplitSpec1 P T M Rest N cs).query (.inl n)))).run ((K, s), c) =
        (coinImpl _ n).run (mergeTable K c, s)
      rw [simulateQ_spec_query]
      exact HiddenSlice.map_coinImpl_run _ n ((K, s), c)
    · change Prod.map id _ <$> (simulateQ (withExt (phase1Oracles I P'))
        (liftM ((SplitSpec1 P T M Rest N cs).query (.inr (.inl (.inl (p, (t, m)))))))).run
          ((K, s), c) =
        (fun z => (z.1, (z.2, s))) <$> lazyStep ($ᵗ N) (mergeTable K c) (p, (t, .inl m))
      rw [simulateQ_spec_query]
      change Prod.map id _ <$> (Prod.map id (·, c) <$>
        ((fun z => (z.1, (z.2, s))) <$> lazyStep ($ᵗ N) K (p, (t, m)))) = _
      simp only [Functor.map_map]
      refine map_lazyStep_eq _ _ _ _ _ _ _ rfl (fun _ _ => rfl) fun v _ => ?_
      exact Prod.ext rfl (Prod.ext (mergeTable_update_inl K c p t m v) rfl)
    · change Prod.map id _ <$> (simulateQ (withExt (phase1Oracles I P'))
        (liftM ((SplitSpec1 P T M Rest N cs).query (.inr (.inr (p, t, r)))))).run ((K, s), c) =
        (fun z => (z.1, (z.2, s))) <$> lazyStep ($ᵗ N) (mergeTable K c) (p, (t, .inr r))
      rw [simulateQ_spec_query]
      change Prod.map id _ <$> (Prod.map id ((K, s), ·) <$>
        ((ExtSpec (P × T × Rest) N).randomOracle (p, t, r)).run c) = _
      rw [randomOracle.run_eq, Functor.map_map]
      unfold lazyStep
      dsimp only [mergeTable]
      cases hc : c (p, t, r) with
      | some v => simp
      | none =>
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          refine bind_congr fun v => ?_
          congr 1
          exact Prod.ext rfl (Prod.ext (mergeTable_cacheQuery_inr K c p t r v) rfl)
    · change Prod.map id _ <$> (simulateQ (withExt (phase1Oracles I P'))
        (liftM ((SplitSpec1 P T M Rest N cs).query (.inr (.inl (.inr d)))))).run ((K, s), c) =
        (sigmaStep (embedInterface (Rest := Rest) I) (sliceImpl₀ P') d).run (mergeTable K c, s)
      rw [simulateQ_spec_query]
      change Prod.map id _ <$> (Prod.map id (·, c) <$>
        (sigmaStep I (sliceImpl₀ P') d).run (K, s)) = _
      rw [sigmaStep_run, sigmaStep_run, Functor.map_map, Functor.map_map]
      change _ <$> (simulateQ (sliceImpl₀ P') ((I.impl d).run s)).run K =
        _ <$> (simulateQ (sliceImpl₀ P') (embedSliceComp ((I.impl d).run s))).run (mergeTable K c)
      rw [← map_run_simulateQ_embedSliceComp P' ((I.impl d).run s) K c, Functor.map_map]
      rfl
  rw [← h1, bind_map_left]
  refine bind_congr fun z => ?_
  obtain ⟨x, ⟨K, s⟩, c⟩ := z
  have h2 :
      Prod.map id (fun st : Table P (T × M) N × ExtCache (P × T × Rest) N =>
          mergeTable st.1 st.2) <$>
        (simulateQ (withExt roOracle) ((splitAdv B).A2 x P')).run (K, c) =
      (simulateQ (roImpl₀ (N := N)) (B.A2 x P')).run (mergeTable K c) := by
    rw [splitAdv, ← QueryImpl.simulateQ_compose]
    refine map_run_simulateQ_eq_of_query_map_eq _ _
      (fun st : Table P (T × M) N × ExtCache (P × T × Rest) N => mergeTable st.1 st.2)
      (fun t st => ?_) (B.A2 x P') (K, c)
    obtain ⟨K', c'⟩ := st
    rcases t with n | ⟨p, ⟨t, m | r⟩⟩
    · change Prod.map id _ <$> (simulateQ (withExt roOracle)
        (liftM ((SplitSpec2 P T M Rest N).query (.inl n)))).run (K', c') =
        (coinImpl _ n).run (mergeTable K' c')
      rw [simulateQ_spec_query]
      exact HiddenSlice.map_coinImpl_run _ n (K', c')
    · change Prod.map id _ <$> (simulateQ (withExt roOracle)
        (liftM ((SplitSpec2 P T M Rest N).query (.inr (.inl (p, (t, m))))))).run (K', c') =
        lazyStep ($ᵗ N) (mergeTable K' c') (p, (t, .inl m))
      rw [simulateQ_spec_query]
      change Prod.map id _ <$> (Prod.map id (·, c') <$> lazyStep ($ᵗ N) K' (p, (t, m))) = _
      rw [Functor.map_map]
      refine map_lazyStep_eq_id _ _ _ _ _ _ rfl (fun _ _ => rfl) fun v _ => ?_
      exact Prod.ext rfl (mergeTable_update_inl K' c' p t m v)
    · change Prod.map id _ <$> (simulateQ (withExt roOracle)
        (liftM ((SplitSpec2 P T M Rest N).query (.inr (.inr (p, t, r)))))).run (K', c') =
        lazyStep ($ᵗ N) (mergeTable K' c') (p, (t, .inr r))
      rw [simulateQ_spec_query]
      change Prod.map id _ <$> (Prod.map id (K', ·) <$>
        ((ExtSpec (P × T × Rest) N).randomOracle (p, t, r)).run c') = _
      rw [randomOracle.run_eq, Functor.map_map]
      unfold lazyStep
      dsimp only [mergeTable]
      cases hc : c' (p, t, r) with
      | some v => simp
      | none =>
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          refine bind_congr fun v => ?_
          congr 1
          exact Prod.ext rfl (mergeTable_cacheQuery_inr K' c' p t r v)
  change (simulateQ (roImpl₀ (N := N)) (B.A2 x P')).run (mergeTable K c) >>= _ = _
  rw [← h2, bind_map_left]
  refine bind_congr fun w => ?_
  change (simulateQ (sliceImpl₀ P') (embedSliceComp (I.pred s w.1))).run
      (mergeTable w.2.1 w.2.2) >>= _ = _
  rw [← map_run_simulateQ_embedSliceComp P' (I.pred s w.1) w.2.1 w.2.2, bind_map_left]
  rfl

/-- **Full stand-alone single-member adversary (Appendix D.2, Steps 1–3)**: given a collection
adversary `A` over `T × (M ⊕ Rest)` with collection oracle `CollSpec`, removes both `CollSpec` and
the other collection members `Rest`, producing a genuine stand-alone adversary over the single
member `ROSpec P (T × M) N` alone with the same first-stage query bound `q`. -/
def singleMemberStandAlone [SampleableType P] {q : ℕ} (I : Interface (T × M) N cs σ α)
    (R : Reservation cs σ T)
    (A : Adversary P (T × (M ⊕ Rest)) N (cs + CollSpec T (M ⊕ Rest) N) S α q) :
    Adversary P (T × M) N cs
      ((S × Slice (T × (M ⊕ Rest)) N) × ExtCache (P × T × Rest) N) α q :=
  dropAdv (splitAdv (standAlone (embedInterface (Rest := Rest) I) R A))

/-- **Lemma 4.1 (i), complete (Appendix D.2, Steps 1–3)**: reducing a collection adversary over
`T × (M ⊕ Rest)` to a single-member stand-alone adversary over `T × M` alone costs at most
`2q / |P|`. -/
theorem prEvent_game0_collInterface_singleMember_le [SampleableType P] [Fintype P]
    {I : Interface (T × M) N cs σ α} {R : Reservation cs σ T} (hR : Discipline I R) {q : ℕ}
    (A : Adversary P (T × (M ⊕ Rest)) N (cs + CollSpec T (M ⊕ Rest) N) S α q) :
    Pr{let b ← game0 (collInterface (embedInterface (Rest := Rest) I) R) A}[b = true] ≤
      Pr{let b ← game0 I (singleMemberStandAlone I R A)}[b = true] + 2 * q / Fintype.card P := by
  have h := prEvent_game0_collInterface_le (discipline_embedInterface (Rest := Rest) hR) A
  rw [game0_embedInterface_eq_game0Ext, game0Ext_eq] at h
  exact h

omit [DecidableEq P] [DecidableEq Rest] [SampleableType N] in
/-- `embedInterface` on the single-member SM-TCR interface is `smtcrInterface Sum.inl p`. -/
theorem embedInterface_smtcrInterface [DecidableEq N] (p : ℕ) :
    embedInterface (Rest := Rest) (smtcrInterface (T := T) (M := M) (N := N) id p) =
      smtcrInterface (T := T) (X := M ⊕ Rest) (M := M) (N := N) Sum.inl p := by
  unfold embedInterface smtcrInterface
  congr 1
  · funext d
    refine StateT.ext fun Q => ?_
    change embedSliceComp ((smtcrChal id p d).run Q) = (smtcrChal Sum.inl p d).run Q
    unfold smtcrChal embedSliceComp
    simp only [StateT.run_mk]
    split_ifs
    · exact simulateQ_pure _ _
    · rw [simulateQ_map, simulateQ_spec_query]
      rfl
  · funext Q out
    change embedSliceComp (smtcrPred id Q out) = smtcrPred Sum.inl Q out
    unfold smtcrPred embedSliceComp
    cases Q[out.1]? with
    | none => exact simulateQ_pure _ _
    | some e =>
        dsimp only
        split_ifs
        · exact simulateQ_pure _ _
        · rw [simulateQ_bind, simulateQ_spec_query]
          refine bind_congr fun y => ?_
          rw [simulateQ_map, simulateQ_spec_query]
          rfl

/-- **Lemma 4.1 (i) for SM-TCR, single-member form (Steps 1–3)**: reduces a collection SM-TCR
adversary over `T × (M ⊕ Rest)` directly to a stand-alone SM-TCR adversary over `T × M` alone. -/
theorem prEvent_smtcrCollGame_singleMember_le [SampleableType P] [Fintype P] [DecidableEq N]
    {q : ℕ} (p : ℕ)
    (A : Adversary P (T × (M ⊕ Rest)) N (SMTCRSpec T M N + CollSpec T (M ⊕ Rest) N) S (ℕ × M) q) :
    Pr{let b ← smtcrCollGame (Sum.inl : M → M ⊕ Rest) p A}[b = true] ≤
      Pr{let b ← smtcrGame (id : M → M) p (singleMemberStandAlone (smtcrInterface id p)
        (smtcrReservation p) A)}[b = true] + 2 * q / Fintype.card P := by
  have h := prEvent_game0_collInterface_singleMember_le (Rest := Rest)
    (smtcr_discipline (T := T) (M := M) (N := N) id p) A
  rwa [embedInterface_smtcrInterface] at h

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq Rest] [SampleableType N] in
private theorem embedSliceComp_stcrSearchAux {B : ℕ} (prop : N → Bool) (t : T) (m : M) :
    ∀ (i rem : ℕ) (h : i + rem = B),
      embedSliceComp (Rest := Rest) (stcrSearchAux (N := N) id prop t m i rem h) =
        stcrSearchAux (N := N) Sum.inl prop t m i rem h
  | _, 0, _ => simulateQ_pure _ _
  | i, rem + 1, h => by
      unfold stcrSearchAux embedSliceComp
      rw [simulateQ_bind, simulateQ_spec_query]
      refine bind_congr fun y => ?_
      split_ifs
      · exact simulateQ_pure _ _
      · exact embedSliceComp_stcrSearchAux prop t m (i + 1) rem (by omega)

omit [DecidableEq P] [DecidableEq Rest] [SampleableType N] in
/-- `embedInterface` on the single-member bounded `S-TCR(Prop)` interface is
`stcrInterface Sum.inl prop p`. -/
theorem embedInterface_stcrInterface [DecidableEq N] {B : ℕ} (prop : N → Bool) (p : ℕ) :
    embedInterface (Rest := Rest)
        (stcrInterface (T := T) (M := M) (N := N) (B := B) id prop p) =
      stcrInterface (T := T) (X := (M × Fin B) ⊕ Rest) (M := M) (N := N) (B := B)
        Sum.inl prop p := by
  unfold embedInterface stcrInterface
  congr 1
  · funext d
    refine StateT.ext fun Q => ?_
    change embedSliceComp ((stcrChal id prop p d).run Q) = (stcrChal Sum.inl prop p d).run Q
    unfold stcrChal
    simp only [StateT.run_mk]
    split_ifs
    · exact simulateQ_pure _ _
    · rw [embedSliceComp, simulateQ_map]
      congr 1
      exact embedSliceComp_stcrSearchAux prop d.1 d.2 0 B (Nat.zero_add B)
  · funext Q out
    change embedSliceComp (stcrPred id Q out) = stcrPred Sum.inl Q out
    unfold stcrPred embedSliceComp
    cases Q[out.1]? with
    | none => exact simulateQ_pure _ _
    | some e =>
        rcases e with ⟨tj, none | ⟨mj, ctrj⟩⟩
        · exact simulateQ_pure _ _
        · dsimp only
          split_ifs
          · exact simulateQ_pure _ _
          · rw [simulateQ_bind, simulateQ_spec_query]
            refine bind_congr fun y => ?_
            rw [simulateQ_map, simulateQ_spec_query]
            rfl

/-- **Lemma 4.1 (i) for bounded `S-TCR(Prop)`, single-member form (Steps 1–3)**: reduces a
collection `S-TCR(Prop)` adversary over `T × ((M × Fin B) ⊕ Rest)` directly to a stand-alone
bounded `S-TCR(Prop)` adversary over `T × (M × Fin B)` alone. -/
theorem prEvent_stcrCollGame_singleMember_le [SampleableType P] [Fintype P] [DecidableEq N]
    {q B : ℕ} (prop : N → Bool) (p : ℕ)
    (A : Adversary P (T × ((M × Fin B) ⊕ Rest)) N
      (STCRSpec T M N B + CollSpec T ((M × Fin B) ⊕ Rest) N) S (ℕ × M × Fin B) q) :
    Pr{let b ← stcrCollGame (Sum.inl : M × Fin B → (M × Fin B) ⊕ Rest) prop p A}[b = true] ≤
      Pr{let b ← stcrGame (id : M × Fin B → M × Fin B) prop p (singleMemberStandAlone
        (stcrInterface id prop p) (stcrReservation p) A)}[b = true] + 2 * q / Fintype.card P := by
  have h := prEvent_game0_collInterface_singleMember_le (Rest := Rest)
    (stcr_discipline (T := T) (M := M) (N := N) (B := B) id prop p) A
  rwa [embedInterface_stcrInterface] at h

end singleMember

end IndependentFunctions

end ShrincsSecurity.Notions.Generic

end
