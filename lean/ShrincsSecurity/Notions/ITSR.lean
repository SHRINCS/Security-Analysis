module

public import ShrincsSecurity.ITSR.Defs
public import ShrincsSecurity.Notions.PRF
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR

/-!
# Interleaved target-subset resilience (ITSR), standard model

Main paper, Section 4.2, **Definition 4.11** (txt lines 2394–2422).

`H : K × {0,1}^α → {0,1}^m` is a keyed hash function and `MAP_{h,k,t}` a deterministic map to a
digest `(I, J₁, …, J_k)`; `G = MAP ∘ H`, and `G(K, M)` is identified with the set
`{(I, i, J_i) : i ∈ [k]}` (`digestSet`). The challenge oracle answers a message `M` with a fresh
uniform key `K` and `(K, G(K, M))`, recording `(K, M)`; the adversary wins with a pair
`(K*, M*) ∉ Q` whose set `G(K*, M*)` is contained in the union of the challenge sets.

We keep the message space `Msg`, the hash output `Dg` and the instance type `ι` abstract (the
paper's `{0,1}^α`, `{0,1}^m` and `[0, 2^h − 1]`), and reuse the digest type
`ShrincsSecurity.ITSR.Digest ι k t` of the ITSR development.

## Relation to VCVio's `KeyedHash.ITSRExperiment`

VCVio's standard-model ITSR game (`VCVio/CryptoFoundations/HardnessAssumptions/KeyedHash/ITSR.lean`)
is the same experiment with two presentational differences: its oracle answers with the key only
(the adversary can evaluate the public function `G` itself), and coverage is phrased through index
lists. `itsrProblem H MAP` is the VCVio problem with uniform keys and index list
`[(I, i, J_i)]_i`; `ITSRAdversary.toVCVio` converts a paper adversary by computing `G(K, M)`
locally after each key; and `itsrSucc_eq_ITSRAdvantage` proves that the success probabilities
coincide. The winning conditions agree by `itsrWins_iff_vcvio`.

## Relation to the random-oracle game of `ShrincsSecurity.ITSR.Game`

The ROM game of the ITSR development (ITSR-Classical, Definition 4) is this experiment with `G`
replaced by a lazily sampled random oracle on `K × M` with values in `Digest ι k t`, to which the
adversary also has direct access; it ends with one verification query. This matches the paper's
analysis of Appendix F, which assumes that `MAP` maps the uniform distribution to the uniform
distribution, so that `G = MAP ∘ H` with `H` a random oracle is itself a random oracle on digests.
Coverage there is `ShrincsSecurity.ITSR.Covered`, and `digestSet_subset_iff_covered` shows it is the
paper's set inclusion.

## Budget

The paper refuses challenges after the `q`-th. We bound the adversary instead
(`ITSRAdversary.chalBound`); on adversaries within budget the two agree.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Notions

open ShrincsSecurity.ITSR (Digest Covered posSet)

variable {K Msg Dg ι : Type} {k t : ℕ}

/-- The set view `{(I, i, J_i) : i ∈ [k]}` of a digest `(I, J)` (Definition 4.11). -/
def digestSet [DecidableEq ι] (u : Digest ι k t) : Finset (ι × Fin k × Fin t) :=
  Finset.univ.image fun i => (u.1, i, u.2 i)

/-- The composed function `G = MAP ∘ H`. -/
def itsrG (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) (x : K × Msg) : Digest ι k t :=
  MAP (H x.1 x.2)

/-- The challenge oracle's signature: a message, answered with `(K, G(K, M))`. -/
abbrev ITSRChalSpec (K Msg : Type) (ι : Type) (k t : ℕ) : OracleSpec Msg :=
  Msg →ₒ (K × Digest ι k t)

/-- A challenge query (as opposed to private randomness). -/
def IsITSRChal {Msg : Type} : ℕ ⊕ Msg → Prop
  | .inr _ => True
  | .inl _ => False

instance {Msg : Type} : DecidablePred (IsITSRChal (Msg := Msg)) := fun x => by
  rcases x with _ | _ <;> simp only [IsITSRChal] <;> infer_instance

/-- The challenge oracle `O` of **Definition 4.11**: a fresh uniform key, the record `(K, M)`,
and the answer `(K, G(K, M))`. -/
def itsrOracle [SampleableType K] (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) :
    QueryImpl (ITSRChalSpec K Msg ι k t) (StateT (List (K × Msg)) ProbComp) :=
  fun m => do
    let key ← (monadLift ($ᵗ K) : StateT (List (K × Msg)) ProbComp K)
    modify fun Q => Q ++ [(key, m)]
    return (key, itsrG H MAP (key, m))

/-- The oracles of the ITSR experiment: private randomness and the challenge oracle. -/
def itsrOracles [SampleableType K] (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) :
    QueryImpl (unifSpec + ITSRChalSpec K Msg ι k t) (StateT (List (K × Msg)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List (K × Msg)) ProbComp) +
    itsrOracle H MAP

/-- An ITSR adversary of **Definition 4.11** making at most `q` challenge queries. -/
structure ITSRAdversary (K Msg ι : Type) (k t q : ℕ) where
  /-- The adversary, outputting a candidate `(K*, M*)`. -/
  run : OracleComp (unifSpec + ITSRChalSpec K Msg ι k t) (K × Msg)
  /-- At most `q` challenge queries on every path. -/
  chalBound : run.IsQueryBoundP IsITSRChal q

/-- The winning condition of Definition 4.11, step 4:
`(K*, M*) ∉ Q ∧ G(K*, M*) ⊆ ⋃_{(Kᵢ, Mᵢ) ∈ Q} G(Kᵢ, Mᵢ)`. -/
def ITSRWins [DecidableEq K] [DecidableEq Msg] [DecidableEq ι] (H : KeyedHash K Msg Dg)
    (MAP : Dg → Digest ι k t) (Q : List (K × Msg)) (x : K × Msg) : Prop :=
  x ∉ Q ∧ digestSet (itsrG H MAP x) ⊆ Q.toFinset.biUnion fun y => digestSet (itsrG H MAP y)

instance [DecidableEq K] [DecidableEq Msg] [DecidableEq ι] (H : KeyedHash K Msg Dg)
    (MAP : Dg → Digest ι k t) (Q : List (K × Msg)) (x : K × Msg) :
    Decidable (ITSRWins H MAP Q x) := by
  unfold ITSRWins; infer_instance

/-- **Definition 4.11**: the experiment `ITSR_{H,q}(A)`. -/
def itsrExperiment [SampleableType K] [DecidableEq K] [DecidableEq Msg] [DecidableEq ι]
    (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) {q : ℕ} (A : ITSRAdversary K Msg ι k t q) :
    ProbComp Bool := do
  let (x, Q) ← (simulateQ (itsrOracles H MAP) A.run).run []
  return decide (ITSRWins H MAP Q x)

/-- **Definition 4.11**: `Succ^{itsr}_{H,q}(A)`. -/
noncomputable def itsrSucc [SampleableType K] [DecidableEq K] [DecidableEq Msg] [DecidableEq ι]
    (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) {q : ℕ}
    (A : ITSRAdversary K Msg ι k t q) : ℝ≥0∞ :=
  𝒟[itsrExperiment H MAP A] {true}

/-! ## Coverage -/

/-- The set inclusion of Definition 4.11 is the covered-set relation `u ∈ S(G)` of the ITSR
development (ITSR-Classical, Definition 2). -/
theorem digestSet_subset_iff_covered [DecidableEq ι] (G : Finset (Digest ι k t))
    (u : Digest ι k t) :
    digestSet u ⊆ G.biUnion digestSet ↔ Covered G u := by
  simp only [digestSet, Covered, posSet, Finset.subset_iff, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_biUnion, Finset.mem_filter, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h i
    obtain ⟨v, hv, j, hj⟩ := h i
    simp only [Prod.mk.injEq] at hj
    obtain ⟨h1, rfl, h3⟩ := hj
    exact ⟨v, ⟨hv, h1⟩, h3⟩
  · intro h i
    obtain ⟨v, ⟨hv, h1⟩, h3⟩ := h i
    exact ⟨v, hv, i, by simp [h1, h3]⟩

/-! ## Relation to VCVio -/

/-- The VCVio ITSR problem for `G = MAP ∘ H`: uniform keys, index list `[(I, i, J_i)]_i`. -/
def itsrProblem [SampleableType K] (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) :
    KeyedHash.ITSRProblem K Msg Dg (ι × Fin k × Fin t) where
  khf := ⟨$ᵗ K, H⟩
  indices y := List.ofFn fun i => ((MAP y).1, i, (MAP y).2 i)

/-- The paper's winning condition is VCVio's. -/
theorem itsrWins_iff_vcvio [SampleableType K] [DecidableEq K] [DecidableEq Msg] [DecidableEq ι]
    (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) (Q : List (K × Msg)) (x : K × Msg) :
    ITSRWins H MAP Q x ↔ (itsrProblem H MAP).Wins Q x := by
  simp only [ITSRWins, KeyedHash.ITSRProblem.Wins, KeyedHash.ITSRProblem.indexSet,
    KeyedHash.ITSRProblem.targetIndexSet, itsrProblem, digestSet, itsrG, Finset.subset_iff,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_flatMap, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]

/-- The paper adversary's oracles implemented through VCVio's: a challenge `M` queries the key
and computes `(K, G(K, M))` locally. -/
def itsrToVCVio (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) :
    QueryImpl (unifSpec + ITSRChalSpec K Msg ι k t)
      (OracleComp (unifSpec + KeyedHash.ITSRTargetSpec Msg K)) :=
  fun
  | .inl n => ((unifSpec + KeyedHash.ITSRTargetSpec Msg K).query (.inl n) :
      OracleComp (unifSpec + KeyedHash.ITSRTargetSpec Msg K) (Fin (n + 1)))
  | .inr m => do
      let key ← ((unifSpec + KeyedHash.ITSRTargetSpec Msg K).query (.inr m) :
        OracleComp (unifSpec + KeyedHash.ITSRTargetSpec Msg K) K)
      return (key, itsrG H MAP (key, m))

/-- A paper ITSR adversary as a VCVio ITSR adversary. -/
def ITSRAdversary.toVCVio [SampleableType K] {H : KeyedHash K Msg Dg} {MAP : Dg → Digest ι k t}
    {q : ℕ} (A : ITSRAdversary K Msg ι k t q) : KeyedHash.ITSRAdversary (itsrProblem H MAP) where
  main := simulateQ (itsrToVCVio H MAP) A.run

/-- **Definition 4.11 is VCVio's ITSR game**: the success probability of a paper adversary equals
the VCVio ITSR advantage of its conversion. -/
theorem itsrSucc_eq_ITSRAdvantage [SampleableType K] [DecidableEq K] [DecidableEq Msg]
    [DecidableEq ι] (H : KeyedHash K Msg Dg) (MAP : Dg → Digest ι k t) {q : ℕ}
    (A : ITSRAdversary K Msg ι k t q) :
    itsrSucc H MAP A = KeyedHash.ITSRAdvantage (A.toVCVio (H := H) (MAP := MAP)) := by
  have hsim : simulateQ (KeyedHash.ITSROracles (itsrProblem H MAP))
      (simulateQ (itsrToVCVio H MAP) A.run) = simulateQ (itsrOracles H MAP) A.run := by
    refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.run
    rcases x with n | m
    · simp [itsrToVCVio, KeyedHash.ITSROracles, itsrOracles]
    · simp [itsrToVCVio, KeyedHash.ITSROracles, itsrOracles, itsrOracle,
        KeyedHash.ITSRTargetOracle, itsrProblem]
  rw [KeyedHash.ITSRAdvantage_eq_evalDist_experiment]
  unfold itsrSucc itsrExperiment KeyedHash.ITSRExperiment KeyedHash.ITSRAdversary.run
    ITSRAdversary.toVCVio
  rw [hsim]
  simp only [itsrWins_iff_vcvio]

end ShrincsSecurity.Notions

end
