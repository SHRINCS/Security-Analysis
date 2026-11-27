module

public import ShrincsSecurity.ITSR.Defs
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The ITSR experiment in the classical random-oracle model

`ITSR-Classical.pdf`, Definition 4 and Section 2.2.

The keyed hash `H' : K × M → Digest ι k t` is a lazily sampled random oracle. The adversary has
three oracles: private uniform randomness, the hash `H'` itself (*direct queries*), and the
challenge oracle `O`, which on `M̃` draws a uniform key `K̃`, records `(K̃, M̃)`, and returns
`(K̃, H'(K̃, M̃))`. Direct and challenge queries share one table. The experiment ends with one
more evaluation of `H'` at the adversary's output `(K, M)` (the verification query that the
paper counts as the `+ 1` of `q + 1`), and the adversary wins when `(K, M)` is not a challenge
pair and its digest is covered by the challenge digests.

The paper's oracle refuses challenges beyond the `r`-th. We bound the adversary instead
(`Adversary.chalBound`); the two formulations agree on bounded adversaries.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

variable (K M D : Type)

/-- Direct queries to the keyed hash `H'`. -/
abbrev HashSpec : OracleSpec (K × M) := (K × M) →ₒ D

/-- Challenge queries: a message is answered with a fresh key and the digest of the pair. -/
abbrev ChalSpec : OracleSpec M := M →ₒ (K × D)

/-- The adversary's oracles: private coins, direct hash queries, challenge queries. -/
abbrev AdvSpec : OracleSpec (ℕ ⊕ ((K × M) ⊕ M)) := unifSpec + (HashSpec K M D + ChalSpec K M D)

/-- A direct hash query. -/
def IsHashQuery : ℕ ⊕ ((K × M) ⊕ M) → Prop
  | .inr (.inl _) => True
  | _ => False

/-- A challenge query. -/
def IsChalQuery : ℕ ⊕ ((K × M) ⊕ M) → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (IsHashQuery K M) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsHashQuery] <;> infer_instance

instance : DecidablePred (IsChalQuery K M) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsChalQuery] <;> infer_instance

/-- The experiment's state: the random oracle's table and the challenge list `Q` (each entry with
the digest it was answered with), in issue order. -/
structure GameState where
  /-- The lazily sampled table of `H'`. -/
  table : K × M → Option D
  /-- The challenge pairs and their digests, in issue order. -/
  challenges : List ((K × M) × D)

namespace GameState

variable {K M D}

/-- The initial state: empty table, no challenges. -/
def init : GameState K M D := ⟨fun _ => none, []⟩

/-- The challenge pairs `Q`. -/
def pairs (s : GameState K M D) : List (K × M) := s.challenges.map Prod.fst

/-- The challenge digests `H_final`. -/
def digests (s : GameState K M D) : List D := s.challenges.map Prod.snd

end GameState

variable {K M D}
variable [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D]

/-- The lazily sampled random oracle `H'`. -/
def hashImpl (x : K × M) : StateT (GameState K M D) ProbComp D := do
  let s ← get
  match s.table x with
  | some d => return d
  | none => do
    let d ← (monadLift ($ᵗ D) : StateT (GameState K M D) ProbComp D)
    set { s with table := Function.update s.table x (some d) }
    return d

/-- The challenge oracle `O`: a fresh uniform key, the digest of the pair, and the record. -/
def chalImpl (m : M) : StateT (GameState K M D) ProbComp (K × D) := do
  let key ← (monadLift ($ᵗ K) : StateT (GameState K M D) ProbComp K)
  let d ← hashImpl (key, m)
  modify fun s => { s with challenges := s.challenges ++ [((key, m), d)] }
  return (key, d)

/-- The experiment's handler for all three oracles. -/
def gameImpl : QueryImpl (AdvSpec K M D) (StateT (GameState K M D) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState K M D) ProbComp) +
    ((fun x => hashImpl x : QueryImpl (HashSpec K M D) (StateT (GameState K M D) ProbComp)) +
      (fun m => chalImpl m : QueryImpl (ChalSpec K M D) (StateT (GameState K M D) ProbComp)))

/-- An ITSR adversary making at most `q` direct queries and at most `r` challenge queries on every
execution path, adaptively interleaved. Repeated messages and pairs are allowed. -/
structure Adversary (K M D : Type) (q r : ℕ) where
  /-- The adversary: it outputs a candidate pair `(K, M)`. -/
  run : OracleComp (AdvSpec K M D) (K × M)
  /-- At most `q` direct queries. -/
  hashBound : run.IsQueryBoundP (IsHashQuery K M) q
  /-- At most `r` challenge queries. -/
  chalBound : run.IsQueryBoundP (IsChalQuery K M) r

variable {ι : Type} {k t : ℕ} [DecidableEq ι]

/-- The winning condition of Definition 4, step 4: the output pair is not a challenge pair and its
digest is covered by the challenge digests. -/
def Wins (s : GameState K M (Digest ι k t)) (x : K × M) (d : Digest ι k t) : Prop :=
  x ∉ s.pairs ∧ Covered s.digests.toFinset d

instance (s : GameState K M (Digest ι k t)) (x : K × M) (d : Digest ι k t) :
    Decidable (Wins s x d) :=
  inferInstanceAs (Decidable (x ∉ s.pairs ∧ Covered s.digests.toFinset d))

/-- **The ITSR experiment** `ITSR_{H',r}(A)` with `H'` a random oracle. -/
def experiment {q r : ℕ} [SampleableType (Digest ι k t)]
    (A : Adversary K M (Digest ι k t) q r) : ProbComp Bool := do
  let (x, s) ← (simulateQ gameImpl A.run).run GameState.init
  let (d, s') ← (hashImpl x).run s
  return decide (Wins s' x d)

/-- **`Succ^ITSR_{H'}(A)`**, the probability that the experiment outputs `1`. -/
noncomputable def advantage {q r : ℕ} [SampleableType (Digest ι k t)]
    (A : Adversary K M (Digest ι k t) q r) : ℝ≥0∞ :=
  Pr{let b ← experiment A}[b = true]

end ShrincsSecurity.ITSR

end
