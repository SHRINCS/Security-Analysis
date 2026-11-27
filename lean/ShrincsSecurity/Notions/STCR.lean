module

public import ShrincsSecurity.Notions.MultiTarget

/-!
# Special target-collision resistance S-TCR(Prop)

Main paper, Section 4.2, **Definition 4.8** (txt lines 2268–2297), with the collection variant of
**Definition 4.12**. In SHRINCS, `Prop` is the WOTS+C target-sum condition and the attacked
function is the grinding hash `H_grind` (Claim 4.3).

The tweakable hash takes a message together with a counter, `Th : P × T × (M × ℕ) → N` (the
paper's `m ∥ i`). On a fresh `(T, m)` the challenge oracle finds the **least** `i ∈ ℕ` with
`Prop(Th(P, T, m ∥ i)) = 1` (`leastCounter`), records `((T, m), (y, i))` and returns `(y, i)`.
The adversary wins with `(j, m*, ctr)` if `Th(P, Tⱼ, mⱼ ∥ iⱼ) = Th(P, Tⱼ, m* ∥ ctr)` and
`m* ≠ mⱼ` (the printed condition is message inequality; a different counter on the same message
does not win).

This notion is not in VCVio and is defined here in the style of
`TweakableHash.SM_DT_TCR_Experiment`, with VCVio's collection oracle and tweak discipline
(`TweakFresh`, `collectionOracle`) for Definition 4.12.

## Deviation: searches that do not terminate

The paper's search has no cap and is undefined when no counter satisfies `Prop`. We make the
oracle total: if no counter exists, the query is refused (`none`) and nothing is recorded. Under
Conjecture 3.1 (every admissible input has a valid counter below `2^c`) this branch never fires
for the scheme's inputs, and then also the least counter is `< 2^c`, so the oracle agrees with the
scheme's bounded search; without the conjecture, a reduction must treat a failing search
explicitly (paper-structure.md §5, Definition 4.8).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Notions

variable {ι P T M N : Type}

/-- The least counter `i` with `Prop(Th(P, T, m ∥ i))`, if one exists. -/
noncomputable def leastCounter (th : TweakableHash P T (M × ℕ) N) (prop : N → Bool) (pk : P)
    (t : T) (m : M) : Option ℕ := by
  classical
  exact if h : ∃ i, prop (th.eval pk t (m, i)) = true then some (Nat.find h) else none

theorem leastCounter_spec {th : TweakableHash P T (M × ℕ) N} {prop : N → Bool} {pk : P} {t : T}
    {m : M} {i : ℕ} (h : leastCounter th prop pk t m = some i) :
    prop (th.eval pk t (m, i)) = true ∧ ∀ i' < i, prop (th.eval pk t (m, i')) = false := by
  classical
  unfold leastCounter at h
  split_ifs at h with hex
  cases h
  exact ⟨Nat.find_spec hex, fun i' hi' => by simpa using Nat.find_min hex hi'⟩

theorem leastCounter_eq_none_iff {th : TweakableHash P T (M × ℕ) N} {prop : N → Bool} {pk : P}
    {t : T} {m : M} :
    leastCounter th prop pk t m = none ↔ ∀ i, prop (th.eval pk t (m, i)) = false := by
  classical
  unfold leastCounter
  split_ifs with hex
  · simp only [false_iff, not_forall, Bool.not_eq_false]
    exact hex
  · simpa using hex

/-- The challenge oracle's signature: `(tweak, message)` answered by `Option (N × ℕ)`. -/
abbrev STCR_challengeSpec (T M N : Type) : OracleSpec (T × M) := (T × M) →ₒ Option (N × ℕ)

/-- An S-TCR(Prop) problem (**Definition 4.8**, with the collection of Definition 4.12). -/
structure STCRProblem (ι P T M N : Type) where
  /-- The attacked tweakable hash on message–counter pairs (in SHRINCS, `H_grind`). -/
  th : TweakableHash P T (M × ℕ) N
  /-- The predicate `Prop` on the output space. -/
  prop : N → Bool
  /-- The collection evaluable by the first stage. -/
  thColl : TweakableHashCollection ι P T N
  /-- The target cap `p`. -/
  numTargets : ℕ

/-- The stand-alone problem of Definition 4.8. -/
def STCRProblem.standalone (th : TweakableHash P T (M × ℕ) N) (prop : N → Bool) (p : ℕ) :
    STCRProblem Empty P T M N where
  th := th
  prop := prop
  thColl := .empty P T N
  numTargets := p

/-- State: the history `((T, m), (y, i))` in issue order, and the collection tweaks. -/
abbrev STCRState (T M N : Type) : Type := List ((T × M) × (N × ℕ)) × List T

/-- The challenge oracle `O_Prop` of **Definition 4.8**: refuse at the cap, at a tweak already
challenged or spent on the collection oracle, or when no counter exists; otherwise answer the
least-counter digest `(y, i)` and record `((T, m), (y, i))`. -/
noncomputable def STCR_challengeOracle [DecidableEq T] (prob : STCRProblem ι P T M N) (pk : P) :
    QueryImpl (STCR_challengeSpec T M N) (StateT (STCRState T M N) ProbComp) :=
  fun tm => do
    let (qsChal, twsColl) ← get
    if prob.numTargets ≤ qsChal.length ∨
        ¬ TweakFresh (fun e : (T × M) × (N × ℕ) => e.1.1) qsChal twsColl tm.1 then
      return none
    else
      match leastCounter prob.th prob.prop pk tm.1 tm.2 with
      | none => return none
      | some i =>
          let y := prob.th.eval pk tm.1 (tm.2, i)
          set (qsChal ++ [(tm, (y, i))], twsColl)
          return some (y, i)

/-- All first-stage oracles: private randomness, the challenge oracle, VCVio's collection
oracle. -/
noncomputable def STCR_oracles [DecidableEq T] (prob : STCRProblem ι P T M N) (pk : P) :
    QueryImpl (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl))
      (StateT (STCRState T M N) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (STCRState T M N) ProbComp) +
    (STCR_challengeOracle prob pk +
      collectionOracle (Q := (T × M) × (N × ℕ)) (fun e => e.1.1) prob.thColl pk)

/-- An S-TCR(Prop) adversary, outputting `(j, m*, ctr)` in its second stage. -/
structure STCRAdversary (prob : STCRProblem ι P T M N) where
  /-- State shared by the two stages. -/
  State : Type
  /-- The first stage `A₁`. -/
  choose : OracleComp (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) State
  /-- The second stage `A₂`, outputting `(j, m*, ctr)`. -/
  forge : State → P → ProbComp (ℕ × M × ℕ)

/-- The winning condition of Definition 4.8, step 6. -/
def STCR_IsCollision [DecidableEq M] [DecidableEq N] (prob : STCRProblem ι P T M N) (pk : P)
    (Q : List ((T × M) × (N × ℕ))) (out : ℕ × M × ℕ) : Bool :=
  match Q[out.1]? with
  | none => false
  | some ((tj, mj), (_, ij)) =>
      decide (prob.th.eval pk tj (mj, ij) = prob.th.eval pk tj out.2 ∧ out.2.1 ≠ mj)

/-- **Definition 4.8**: the experiment `S-TCR(Prop)_{Th,p}(A)`. -/
noncomputable def STCR_Experiment [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {prob : STCRProblem ι P T M N} (A : STCRAdversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, qsChal, _) ← (simulateQ (STCR_oracles prob pk) A.choose).run ([], [])
  let out ← A.forge st pk
  return STCR_IsCollision prob pk qsChal out

/-- **Definition 4.8**: `Succ^{S-TCR(Prop)}_{Th,p}(A)`. -/
noncomputable def STCR_Succ [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {prob : STCRProblem ι P T M N} (A : STCRAdversary prob) : ℝ≥0∞ :=
  𝒟[STCR_Experiment A] {true}

/-- Every recorded entry carries the least valid counter and its digest. -/
theorem STCR_challengeOracle_mem_support_record [DecidableEq T] {prob : STCRProblem ι P T M N}
    {pk : P} {tm : T × M} {s : STCRState T M N} {z : Option (N × ℕ) × STCRState T M N}
    (hz : z ∈ support ((STCR_challengeOracle prob pk tm).run s)) :
    z.2 = s ∨ ∃ i, leastCounter prob.th prob.prop pk tm.1 tm.2 = some i ∧
      z = (some (prob.th.eval pk tm.1 (tm.2, i), i),
        (s.1 ++ [(tm, (prob.th.eval pk tm.1 (tm.2, i), i))], s.2)) := by
  unfold STCR_challengeOracle at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · left; simp at hz; rw [hz]
  · cases hlc : leastCounter prob.th prob.prop pk tm.1 tm.2 with
    | none => left; simp [hlc] at hz; rw [hz]
    | some i => right; exact ⟨i, rfl, by simpa [hlc] using hz⟩

end ShrincsSecurity.Notions

end
