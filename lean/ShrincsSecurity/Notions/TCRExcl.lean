module

public import ShrincsSecurity.Notions.TweakPartition
public import ShrincsSecurity.Notions.MultiTarget

/-!
# SM-TCR with exclusive tweaks (sm-tcr-excl)

Main paper, Section 4.2, **Definition 4.7** (txt lines 2226–2262, restated at 7235–7268), and
its collection variant from **Definition 4.12** (lines 2438–2463: a challenge at `T` also
reserves the partner tweak `ω(T)`, respectively `ω⁻¹(T)`, against collection queries, and a
challenge is refused if its tweak or its partner was used by a collection query).

This notion is not in VCVio and is defined here, in the style of VCVio's
`TweakableHash.SM_DT_TCR_Experiment`: an issue-ordered challenge history, refusals as `none`, the
public parameter withheld from the first stage by typing, and the collection as a parameter (the
stand-alone notion is the instance at `TweakableHashCollection.empty`).

## Encoding of the guards

With `Ω(T) = {T, partner T}` (`ExclusiveTweaks.Omega`):

* the paper's three challenge guards ("`(T, m') ∈ Q`", "`T ∈ T₂` and `(ω(T), m') ∈ Q`",
  "`T ∈ T₃` and `(ω⁻¹(T), m') ∈ Q`") say exactly that some recorded tweak lies in `Ω(T)`
  (`ExclReserved`, and `exclReserved_iff_cases`);
* the winning clauses of steps 6–8 say `T* ∈ Ω(Tⱼ)` (`ExclusiveTweaks.mem_Omega_iff_cases`);
* the freshness condition is the printed *message* inequality `m* ≠ mⱼ`, not
  `(T*, m*) ≠ (Tⱼ, mⱼ)`.

## Deviations

* The paper bounds the target count by `p ≤ |T₁ ∪ T₂|`; the game is well defined for every `p`
  (the guards make at most `|T₁ ∪ T₂|` challenges admissible anyway), so no hypothesis is carried.
* Collection: as in VCVio's games, the collection oracle names the member by an index rather than
  by message length (Definition 4.12 selects by length, and lengths are pairwise distinct, so the
  two agree up to relabelling), and admits every tweak for every member (the paper's default
  `T_m = T`); restricting member tweak sets only removes adversary queries.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Notions

variable {ι P T M N : Type}

/-- The challenge oracle's signature: a `(tweak, message)` pair, answered by `Option N`. -/
abbrev SMTCRExcl_challengeSpec (T M N : Type) : OracleSpec (T × M) := (T × M) →ₒ Option N

/-- An sm-tcr-excl problem (**Definition 4.7**, with the collection of **Definition 4.12**): the
attacked tweakable hash, the exclusive tweak data, the collection evaluable by the first stage,
and the target cap `p`. -/
structure SMTCRExclProblem (ι P T M N : Type) where
  /-- The tweakable hash under attack (`Th`, in SHRINCS `Th_{2∪lsf}`). -/
  th : TweakableHash P T M N
  /-- The partition `T₁ ∪ T₂ ∪ T₃` and the bijection `ω`. -/
  X : ExclusiveTweaks T
  /-- The collection `Th_λ`, evaluable at the hidden parameter by the first stage. -/
  thColl : TweakableHashCollection ι P T N
  /-- The target cap `p`. -/
  numTargets : ℕ

/-- The stand-alone problem of Definition 4.7 (empty collection). -/
def SMTCRExclProblem.standalone (th : TweakableHash P T M N) (X : ExclusiveTweaks T) (p : ℕ) :
    SMTCRExclProblem Empty P T M N where
  th := th
  X := X
  thColl := .empty P T N
  numTargets := p

/-- The game state: the challenge history `Q` of accepted `(tweak, message)` targets in issue
order, and the tweaks spent on the collection oracle. -/
abbrev SMTCRExclState (T M : Type) : Type := List (T × M) × List T

/-- A tweak `t` is reserved by the challenge history: some recorded tweak `t'` has
`t ∈ Ω(t')`, i.e. `t = t'` or `t` is the partner of `t'`. -/
def ExclReserved (X : ExclusiveTweaks T) (Q : List (T × M)) (t : T) : Prop :=
  ∃ e ∈ Q, t ∈ X.Omega e.1

instance [DecidableEq T] (X : ExclusiveTweaks T) (Q : List (T × M)) (t : T) :
    Decidable (ExclReserved X Q t) :=
  inferInstanceAs (Decidable (∃ e ∈ Q, t ∈ X.Omega e.1))

/-- The three challenge guards of Definition 4.7 (step 3) are `ExclReserved`. -/
theorem exclReserved_iff_cases (X : ExclusiveTweaks T) (Q : List (T × M)) (t : T) :
    ExclReserved X Q t ↔
      (∃ m', (t, m') ∈ Q) ∨
      (X.cls t = .two ∧ ∃ m', (X.partner t, m') ∈ Q) ∨
      (X.cls t = .three ∧ ∃ m', (X.partner t, m') ∈ Q) := by
  constructor
  · rintro ⟨⟨t', m'⟩, hmem, ht⟩
    rw [X.mem_Omega_comm] at ht
    rcases ht with rfl | rfl
    · exact Or.inl ⟨m', hmem⟩
    · cases hc : X.cls t
      · exact Or.inl ⟨m', by rwa [X.partner_of_one t hc] at hmem⟩
      · exact Or.inr (Or.inl ⟨rfl, m', hmem⟩)
      · exact Or.inr (Or.inr ⟨rfl, m', hmem⟩)
  · rintro (⟨m', h⟩ | ⟨_, m', h⟩ | ⟨_, m', h⟩)
    · exact ⟨(t, m'), h, X.self_mem_Omega t⟩
    · exact ⟨(X.partner t, m'), h, Or.inr (X.partner_partner t).symm⟩
    · exact ⟨(X.partner t, m'), h, Or.inr (X.partner_partner t).symm⟩

/-- A challenge at `t` clashes with the collection history when `t` or its partner was used by a
collection query (**Definition 4.12**, "the rule applies in both orders"). -/
def ExclCollectionClash (X : ExclusiveTweaks T) (twsColl : List T) (t : T) : Prop :=
  ∃ c ∈ twsColl, c ∈ X.Omega t

instance [DecidableEq T] (X : ExclusiveTweaks T) (twsColl : List T) (t : T) :
    Decidable (ExclCollectionClash X twsColl t) :=
  inferInstanceAs (Decidable (∃ c ∈ twsColl, c ∈ X.Omega t))

/-- The challenge oracle of **Definition 4.7** at a public parameter: refuse (`none`, state
untouched) at the target cap, at a tweak reserved by an earlier challenge (itself or through its
partner), or at a tweak clashing with the collection history; otherwise record `(t, m)` and answer
`Th(P, t, m)`. -/
def SMTCRExcl_challengeOracle [DecidableEq T] (prob : SMTCRExclProblem ι P T M N) (pk : P) :
    QueryImpl (SMTCRExcl_challengeSpec T M N) (StateT (SMTCRExclState T M) ProbComp) :=
  fun tm => do
    let (qsChal, twsColl) ← get
    if prob.numTargets ≤ qsChal.length ∨ ExclReserved prob.X qsChal tm.1 ∨
        ExclCollectionClash prob.X twsColl tm.1 then
      return none
    else
      set (qsChal ++ [tm], twsColl)
      return some (prob.th.eval pk tm.1 tm.2)

/-- The collection oracle of **Definition 4.12** for sm-tcr-excl: as VCVio's `collectionOracle`,
but a challenge at `T` also reserves its partner. -/
def SMTCRExcl_collectionOracle [DecidableEq T] (prob : SMTCRExclProblem ι P T M N) (pk : P) :
    QueryImpl (collectionSpec prob.thColl) (StateT (SMTCRExclState T M) ProbComp) :=
  fun q => do
    let (qsChal, twsColl) ← get
    if ExclReserved prob.X qsChal q.2.1 then
      return none
    else
      set (qsChal, twsColl ++ [q.2.1])
      return some (prob.thColl.eval q.1 pk q.2.1 q.2.2)

/-- All oracles of the first stage. -/
def SMTCRExcl_oracles [DecidableEq T] (prob : SMTCRExclProblem ι P T M N) (pk : P) :
    QueryImpl (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl))
      (StateT (SMTCRExclState T M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SMTCRExclState T M) ProbComp) +
    (SMTCRExcl_challengeOracle prob pk + SMTCRExcl_collectionOracle prob pk)

/-- An sm-tcr-excl adversary `A = (A₁, A₂)`: `choose` is the first stage (no access to `P`),
`forge` the second (given `P`, no oracle), outputting `(j, T*, m*)`. -/
structure SMTCRExclAdversary (prob : SMTCRExclProblem ι P T M N) where
  /-- State shared by the two stages. -/
  State : Type
  /-- The first stage `A₁`. -/
  choose : OracleComp
    (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl)) State
  /-- The second stage `A₂`, outputting `(j, T*, m*)`. -/
  forge : State → P → ProbComp (ℕ × T × M)

/-- The winning condition of Definition 4.7, steps 6–9, on the challenge history and the output
`(j, T*, m*)`: `T* ∈ Ω(Tⱼ)`, `m* ≠ mⱼ` and `Th(P, Tⱼ, mⱼ) = Th(P, T*, m*)`; an index outside the
history loses. -/
def SMTCRExcl_IsCollision [DecidableEq T] [DecidableEq M] [DecidableEq N]
    (prob : SMTCRExclProblem ι P T M N) (pk : P) (Q : List (T × M)) (out : ℕ × T × M) : Bool :=
  match Q[out.1]? with
  | none => false
  | some (tj, mj) =>
      decide (out.2.1 ∈ prob.X.Omega tj ∧ out.2.2 ≠ mj ∧
        prob.th.eval pk tj mj = prob.th.eval pk out.2.1 out.2.2)

/-- **Definition 4.7**: the experiment `SM-TCR-EXCL_{Th,p}(A)` (with collection access as in
Definition 4.12; stand-alone at the empty collection). -/
def SMTCRExcl_Experiment [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {prob : SMTCRExclProblem ι P T M N} (A : SMTCRExclAdversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, qsChal, _) ← (simulateQ (SMTCRExcl_oracles prob pk) A.choose).run ([], [])
  let out ← A.forge st pk
  return SMTCRExcl_IsCollision prob pk qsChal out

/-- **Definition 4.7**: `Succ^{sm-tcr-excl}_{Th,p}(A)`. -/
noncomputable def SMTCRExcl_Succ [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {prob : SMTCRExclProblem ι P T M N} (A : SMTCRExclAdversary prob) : ℝ≥0∞ :=
  𝒟[SMTCRExcl_Experiment A] {true}

/-! ## Basic properties -/

section Basic

variable [DecidableEq T] {prob : SMTCRExclProblem ι P T M N} {pk : P} {t : T} {m : M}
  {qsChal : List (T × M)} {twsColl : List T}

/-- An admissible challenge is answered with the hash and appended to the history. -/
theorem SMTCRExcl_challengeOracle_run_of_fresh (hlen : qsChal.length < prob.numTargets)
    (hres : ¬ ExclReserved prob.X qsChal t) (hcoll : ¬ ExclCollectionClash prob.X twsColl t) :
    (SMTCRExcl_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (some (prob.th.eval pk t m), (qsChal ++ [(t, m)], twsColl)) := by
  simp [SMTCRExcl_challengeOracle, Nat.not_le.mpr hlen, hres, hcoll]

/-- A challenge at the partner of a recorded tweak is refused, the state unchanged. -/
theorem SMTCRExcl_challengeOracle_run_of_partner (m' : M) (hmem : (prob.X.partner t, m') ∈ qsChal) :
    (SMTCRExcl_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  have hres : ExclReserved prob.X qsChal t :=
    ⟨(prob.X.partner t, m'), hmem, Or.inr (prob.X.partner_partner t).symm⟩
  simp [SMTCRExcl_challengeOracle, hres]

/-- A collection query at the partner of a challenged tweak is refused, the state unchanged. -/
theorem SMTCRExcl_collectionOracle_run_of_partner (q : (i : ι) × T × prob.thColl.Msg i)
    (m' : M) (hmem : (prob.X.partner q.2.1, m') ∈ qsChal) :
    (SMTCRExcl_collectionOracle prob pk q).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  have hres : ExclReserved prob.X qsChal q.2.1 :=
    ⟨(prob.X.partner q.2.1, m'), hmem, Or.inr (prob.X.partner_partner q.2.1).symm⟩
  simp [SMTCRExcl_collectionOracle, hres]

omit [DecidableEq T] in
/-- At the trivial partition (`T = T₁`) the reservation rule is VCVio's `TweakReserved`, so the
challenge oracle of sm-tcr-excl is the SM-TCR challenge oracle of Definition 4.4. -/
theorem exclReserved_trivial_iff (Q : List (T × M)) (t : T) :
    ExclReserved (ExclusiveTweaks.trivial T) Q t ↔ TweakReserved Prod.fst Q t := by
  simp only [ExclReserved, TweakReserved, ExclusiveTweaks.mem_Omega_iff,
    ExclusiveTweaks.trivial, id, or_self]
  exact ⟨fun ⟨e, h, he⟩ => ⟨e, h, he.symm⟩, fun ⟨e, h, he⟩ => ⟨e, h, he.symm⟩⟩

theorem SMTCRExcl_challengeOracle_trivial (th : TweakableHash P T M N)
    (thColl : TweakableHashCollection ι P T N) (p : ℕ) (pk : P) (tm : T × M)
    (s : SMTCRExclState T M) :
    (SMTCRExcl_challengeOracle ⟨th, ExclusiveTweaks.trivial T, thColl, p⟩ pk tm).run s =
      (SM_DT_TCR_challengeOracle ⟨th, thColl, p⟩ pk tm).run s := by
  have hc : ∀ l : List T, ExclCollectionClash (ExclusiveTweaks.trivial T) l tm.1 ↔ tm.1 ∈ l := by
    simp [ExclCollectionClash, ExclusiveTweaks.mem_Omega_iff, ExclusiveTweaks.trivial]
  simp only [SMTCRExcl_challengeOracle, SM_DT_TCR_challengeOracle, TweakFresh,
    exclReserved_trivial_iff, hc, not_and_or, not_not]

end Basic

end ShrincsSecurity.Notions

end
