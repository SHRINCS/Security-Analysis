module

public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Adaptive reprogramming experiments (classical)

`SHRINCS-Security-Analysis.pdf`, Appendix C: **Definition C.1** (`Repro_b`, after [GHHM21]) and
**Definition C.2** (`DI-Repro_b`, distinct second inputs).

The random oracle `O₀ : X₁ × X₂ → Y` is a uniformly random function, sampled eagerly as a full
table. The adversary has three oracles: private uniform randomness, the oracle `O_b` (*hash
queries*), and `Reprogram(x₂)` (*reprogramming calls*), which samples `(x₁, y) ← X₁ × Y`, sets
`O₁(x₁, x₂) := y` and returns `x₁`.

Encoding notes.
* Only `O_b` is ever read in `Repro_b`: `O₁` is invisible in `Repro_0` and `O₀` in `Repro_1`. The
  experiments therefore keep a single table, the one the adversary reads: `Repro_0` never changes
  it (`Reprogram` still samples `(x₁, y)` and returns `x₁`), `Repro_1` reprograms it.
* The paper bounds the adversary to `q` queries and `R` calls; as in the ITSR experiment we bound
  the adversary (`Adversary.hashBound`, `Adversary.reproBound`) on every execution path.
* `DI-Repro` answers a refused call with `none` (the paper's `⊥`); every call, refused or not,
  counts toward `R`.
* The advantage is the real number `|Pr[Repro_0(A) ⇒ 1] − Pr[Repro_1(A) ⇒ 1]|`.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Repro

variable (X₁ X₂ Y : Type)

/-- Queries to the random oracle `O_b`. -/
abbrev HashSpec : OracleSpec (X₁ × X₂) := (X₁ × X₂) →ₒ Y

/-- Calls `Reprogram(x₂)`, answered with the sampled seed `x₁`. -/
abbrev ReproSpec : OracleSpec X₂ := X₂ →ₒ X₁

/-- Calls `Reprogram(x₂)` of `DI-Repro`, answered with `some x₁`, or `none` (`⊥`) when refused. -/
abbrev DIReproSpec : OracleSpec X₂ := X₂ →ₒ Option X₁

/-- The oracles of a `Repro` adversary: private coins, `O_b`, `Reprogram`. -/
abbrev AdvSpec : OracleSpec (ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) :=
  unifSpec + (HashSpec X₁ X₂ Y + ReproSpec X₁ X₂)

/-- The oracles of a `DI-Repro` adversary: private coins, `O_b`, the guarded `Reprogram`. -/
abbrev DIAdvSpec : OracleSpec (ℕ ⊕ ((X₁ × X₂) ⊕ X₂)) :=
  unifSpec + (HashSpec X₁ X₂ Y + DIReproSpec X₁ X₂)

/-- A query to `O_b`. -/
def IsHashQuery : ℕ ⊕ ((X₁ × X₂) ⊕ X₂) → Prop
  | .inr (.inl _) => True
  | _ => False

/-- A call to `Reprogram`. -/
def IsReproQuery : ℕ ⊕ ((X₁ × X₂) ⊕ X₂) → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (IsHashQuery X₁ X₂) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsHashQuery] <;> infer_instance

instance : DecidablePred (IsReproQuery X₁ X₂) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsReproQuery] <;> infer_instance

variable {X₁ X₂ Y}
variable [DecidableEq X₁] [DecidableEq X₂] [SampleableType X₁] [SampleableType Y]

/-- **`n_j` of Lemma C.4**: given the queries `log` issued to `O_b` before a call
`Reprogram(x₂)`, the number of seeds `x₁` such that `(x₁, x₂)` has been queried. -/
def seedCount (log : List (X₁ × X₂)) (x₂ : X₂) : ℕ :=
  (log.toFinset.filter fun p => p.2 = x₂).card

/-- **The share of `q_pre` of Corollary C.2** charged to the first call `Reprogram(x₂)`: the number
of queries in `log` (with multiplicity) whose second input is `x₂`. Summed over the calls that are
not refused, these are exactly the queries whose second input is submitted for the first time after
the query. -/
def preCount (log : List (X₁ × X₂)) (x₂ : X₂) : ℕ :=
  log.countP fun p => p.2 = x₂

/-- The oracle `O_b`: read the current table. -/
def hashImpl {σ : Type} (tbl : σ → X₁ × X₂ → Y) (x : X₁ × X₂) : StateT σ ProbComp Y := do
  return tbl (← get) x

/-- `Reprogram(x₂)` of **Definition C.1**: sample `(x₁, y) ← X₁ × Y`; in `Repro_1` set
`O₁(x₁, x₂) := y`; return `x₁`. -/
def reproImpl (b : Bool) (x₂ : X₂) : StateT (X₁ × X₂ → Y) ProbComp X₁ := do
  let (x₁, y) ← (monadLift ($ᵗ (X₁ × Y)) : StateT (X₁ × X₂ → Y) ProbComp (X₁ × Y))
  if b then modify fun O => Function.update O (x₁, x₂) y
  return x₁

/-- The handler of `Repro_b` (**Definition C.1**); the state is the table `O_b`. -/
def gameImpl (b : Bool) : QueryImpl (AdvSpec X₁ X₂ Y) (StateT (X₁ × X₂ → Y) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (X₁ × X₂ → Y) ProbComp) +
    ((fun x => hashImpl id x : QueryImpl (HashSpec X₁ X₂ Y) (StateT (X₁ × X₂ → Y) ProbComp)) +
      (fun x₂ => reproImpl b x₂ : QueryImpl (ReproSpec X₁ X₂) (StateT (X₁ × X₂ → Y) ProbComp)))

/-- `Reprogram(x₂)` of **Definition C.2**: refuse (`⊥`) an already submitted `x₂`; otherwise record
`x₂` in `L` and proceed as in Definition C.1. -/
def diReproImpl (b : Bool) (x₂ : X₂) :
    StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp (Option X₁) := do
  if x₂ ∈ (← get).2 then return none
  let (x₁, y) ← (monadLift ($ᵗ (X₁ × Y)) :
    StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp (X₁ × Y))
  modify fun s => (if b then Function.update s.1 (x₁, x₂) y else s.1, insert x₂ s.2)
  return some x₁

/-- The handler of `DI-Repro_b` (**Definition C.2**); the state is the table `O_b` and the list
`L` of submitted second inputs. -/
def diGameImpl (b : Bool) :
    QueryImpl (DIAdvSpec X₁ X₂ Y) (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp) +
    ((fun x => hashImpl Prod.fst x :
        QueryImpl (HashSpec X₁ X₂ Y) (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp)) +
      (fun x₂ => diReproImpl b x₂ :
        QueryImpl (DIReproSpec X₁ X₂) (StateT ((X₁ × X₂ → Y) × Finset X₂) ProbComp)))

/-- A classical `Repro` adversary making at most `q` queries to `O_b` and at most `R` calls to
`Reprogram` on every execution path, adaptively interleaved, and outputting a bit. -/
structure Adversary (X₁ X₂ Y : Type) (q R : ℕ) where
  /-- The distinguisher. -/
  run : OracleComp (AdvSpec X₁ X₂ Y) Bool
  /-- At most `q` queries to `O_b`. -/
  hashBound : run.IsQueryBoundP (IsHashQuery X₁ X₂) q
  /-- At most `R` calls to `Reprogram`. -/
  reproBound : run.IsQueryBoundP (IsReproQuery X₁ X₂) R

/-- A classical `DI-Repro` adversary: at most `q` queries to `O_b` and at most `R` calls to
`Reprogram`, refused calls included. -/
structure DIAdversary (X₁ X₂ Y : Type) (q R : ℕ) where
  /-- The distinguisher. -/
  run : OracleComp (DIAdvSpec X₁ X₂ Y) Bool
  /-- At most `q` queries to `O_b`. -/
  hashBound : run.IsQueryBoundP (IsHashQuery X₁ X₂) q
  /-- At most `R` calls to `Reprogram`, refused calls included. -/
  reproBound : run.IsQueryBoundP (IsReproQuery X₁ X₂) R

variable [Fintype X₁] [Fintype X₂]

/-- **The experiment `Repro_b(A)`** of Definition C.1: sample `O₀` uniformly, run `A`. -/
noncomputable def experiment (b : Bool) (A : OracleComp (AdvSpec X₁ X₂ Y) Bool) : ProbComp Bool := do
  let O ← $ᵗ (X₁ × X₂ → Y)
  (simulateQ (gameImpl b) A).run' O

/-- **The experiment `DI-Repro_b(A)`** of Definition C.2: sample `O₀` uniformly, start with
`L = ∅`, run `A`. -/
noncomputable def diExperiment (b : Bool) (A : OracleComp (DIAdvSpec X₁ X₂ Y) Bool) : ProbComp Bool := do
  let O ← $ᵗ (X₁ × X₂ → Y)
  (simulateQ (diGameImpl b) A).run' (O, ∅)

/-- **`Adv^Repro_{R,q}(A)`** (Definition C.1): `|Pr[Repro_0(A) ⇒ 1] − Pr[Repro_1(A) ⇒ 1]|`. -/
noncomputable def advantage {q R : ℕ} (A : Adversary X₁ X₂ Y q R) : ℝ :=
  |(Pr{let b ← experiment false A.run}[b = true]).toReal -
    (Pr{let b ← experiment true A.run}[b = true]).toReal|

/-- **`Adv^DI-Repro_{R,q}(A)`** (Definition C.2):
`|Pr[DI-Repro_0(A) ⇒ 1] − Pr[DI-Repro_1(A) ⇒ 1]|`. -/
noncomputable def diAdvantage {q R : ℕ} (A : DIAdversary X₁ X₂ Y q R) : ℝ :=
  |(Pr{let b ← diExperiment false A.run}[b = true]).toReal -
    (Pr{let b ← diExperiment true A.run}[b = true]).toReal|

end ShrincsSecurity.Repro

end
