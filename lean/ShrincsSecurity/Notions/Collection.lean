module

public import ShrincsSecurity.Notions.TCRExcl
public import ShrincsSecurity.Notions.STCR

/-!
# Security of members of a collection

Main paper, Section 4.3, **Definition 4.12** (txt lines 2423–2470; the explicit SM-TCR instance is
**Definition D.1**, lines 6553–6598) and the unconditional half of **Conjecture 4.1** /
**Lemma 4.1** (`InSec^Prop(Th_m; ξ, p) ≤ InSec^Prop(Th_m ∈ Th_λ; ξ, p, q_λ)`, "an adversary may
ignore the collection oracle", lines 2548 and 6652).

## The collection experiments

A collection `Th_λ = {Th_{mᵢ}}` shares the public parameter and the tweak space; it is VCVio's
`TweakableHashCollection ι P T N`. Every game of this development (VCVio's SM-TCR, SM-PRE, SM-UD,
SM-DSPR and our sm-tcr-excl and S-TCR(Prop)) is parameterised by a collection, and its first
stage has the collection oracle `Th_λ(P, ·, ·)` beside the challenge oracle, with the bidirectional
reservation rule of Definition 4.12 enforced in both oracles (VCVio's `collectionOracle` and
`TweakFresh`; for sm-tcr-excl the partner-reserving `SMTCRExcl_collectionOracle`). The stand-alone
experiments of Section 4.2 are the instances at the empty collection.

`Th_m ∈ Th_λ` (the attacked function is itself a member, so the collection oracle also evaluates
it at non-challenge tweaks) is the instance at `TweakableHashCollection.cons th rest`, as in
VCVio; the constructors below package it. For `Th_{2∪lsf}`, which is *not* a member but the
length-selected combination of the members `H` and `Th_{lsf}` (`combine`), the attacked function
is `combine` and the collection is `Th_λ` itself (it already contains `H` and `Th_{lsf}`).

Differences from the printed definition:
* members are named by an index `i : ι` instead of being selected by message length. For a
  length-indexed collection (`Collection.ofLengths`) the two coincide exactly:
  `Collection.lengthQueryEquiv` identifies the index-named queries `(i, T, x)` with the pairs
  `(T, m)`, `m ∈ {0,1}*`, and the answer is that of the member `Th_{|m|}`;
* every member admits every tweak (the paper's default `T_m = T`; SHRINCS restricts only the tweak
  set of `H_grind`), and the challenge oracle admits every tweak. This only enlarges the adversary
  class: a paper adversary is simulated by one that skips the queries the paper's oracles would
  refuse (it can decide refusal from its own transcript), with the same success.

## The unconditional direction

`SM_DT_TCR_Advantage_liftCollection` (and its siblings) show that every stand-alone adversary is a
collection adversary, for any collection, with the same success: the lift is a `simulateQ` that
forwards the two genuine oracles and never reaches the (uninhabited) empty collection oracle.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Notions

variable {ι P T M N : Type}

/-! ## Members and combinations -/

namespace Collection

/-- The member `Th_{mᵢ}` of a collection as a stand-alone tweakable hash, with a public-parameter
sampler. -/
def member (C : TweakableHashCollection ι P T N) (i : ι) (seedGen : ProbComp P) :
    TweakableHash P T (C.Msg i) N where
  seedGen := seedGen
  eval := C.eval i

/-- The length-selected combination of two members (the paper's `Th_{2∪lsf}`: `H` on messages of
length `2n`, `Th_{lsf}` on messages of length `l_sf · n`). -/
def combine (C : TweakableHashCollection ι P T N) (i j : ι) (seedGen : ProbComp P) :
    TweakableHash P T (C.Msg i ⊕ C.Msg j) N where
  seedGen := seedGen
  eval pk t
    | .inl x => C.eval i pk t x
    | .inr y => C.eval j pk t y

@[simp] theorem combine_eval_inl (C : TweakableHashCollection ι P T N) (i j : ι)
    (seedGen : ProbComp P) (pk : P) (t : T) (x : C.Msg i) :
    (combine C i j seedGen).eval pk t (.inl x) = C.eval i pk t x := rfl

@[simp] theorem combine_eval_inr (C : TweakableHashCollection ι P T N) (i j : ι)
    (seedGen : ProbComp P) (pk : P) (t : T) (y : C.Msg j) :
    (combine C i j seedGen).eval pk t (.inr y) = C.eval j pk t y := rfl

/-- A collection indexed by message length, as in Definition 4.12: the member `Th_m` takes bit
strings of length `m`. -/
def ofLengths (f : (m : ℕ) → P → T → {l : List Bool // l.length = m} → N) :
    TweakableHashCollection ℕ P T N where
  Msg m := {l : List Bool // l.length = m}
  eval := f

/-- For a length-indexed collection, a collection-oracle query `(i, T, x)` is exactly a pair
`(T, m)` with `m ∈ {0,1}*`, the member being `i = |m|`: VCVio's index-named oracle is the paper's
length-selected oracle `Th_λ(P, T, m) = Th_{|m|}(P, T, m)`. -/
def lengthQueryEquiv (f : (m : ℕ) → P → T → {l : List Bool // l.length = m} → N) :
    ((i : ℕ) × T × (ofLengths f).Msg i) ≃ T × List Bool where
  toFun q := (q.2.1, q.2.2.1)
  invFun q := ⟨q.2.length, q.1, ⟨q.2, rfl⟩⟩
  left_inv := by
    rintro ⟨i, t, l, rfl⟩
    rfl
  right_inv _ := rfl

/-- Under `lengthQueryEquiv`, the collection evaluates the member selected by the length. -/
theorem ofLengths_eval_symm (f : (m : ℕ) → P → T → {l : List Bool // l.length = m} → N) (pk : P)
    (q : T × List Bool) :
    (ofLengths f).eval ((lengthQueryEquiv f).symm q).1 pk ((lengthQueryEquiv f).symm q).2.1
      ((lengthQueryEquiv f).symm q).2.2 = f q.2.length pk q.1 ⟨q.2, rfl⟩ := rfl

end Collection

/-! ## Definition 4.12: the collection problems -/

/-- **Definition 4.12** for SM-TCR (= **Definition D.1**): `Th_m ∈ Th_λ` with `p` targets. -/
abbrev smTcrMemberProblem (th : TweakableHash P T M N) (rest : TweakableHashCollection ι P T N)
    (p : ℕ) : SM_DT_TCR_Problem (Option ι) P T M N :=
  ⟨th, TweakableHashCollection.cons th rest, p⟩

/-- **Definition 4.12** for SM-PRE. -/
abbrev smPreMemberProblem (th : TweakableHash P T M N) (rest : TweakableHashCollection ι P T N)
    (p : ℕ) : SM_DT_PRE_Problem (Option ι) P T M M N :=
  ⟨th, id, Function.injective_id, TweakableHashCollection.cons th rest, p⟩

/-- **Definition 4.12** for SM-UD (uniform inputs against uniform outputs). -/
noncomputable abbrev smUdMemberProblem [SampleableType M] [SampleableType N]
    (th : TweakableHash P T M N) (rest : TweakableHashCollection ι P T N) (p : ℕ) :
    SM_DT_UD_Problem (Option ι) P T M M N :=
  ⟨th, id, Function.injective_id, $ᵗ M, $ᵗ N, TweakableHashCollection.cons th rest, p⟩

/-- **Definition 4.12** for SM-DSPR. -/
abbrev smDsprMemberProblem (th : TweakableHash P T M N) (rest : TweakableHashCollection ι P T N)
    (p : ℕ) : SM_DT_DSPR_Problem (Option ι) P T M N :=
  ⟨th, TweakableHashCollection.cons th rest, p⟩

/-- **Definition 4.12** for S-TCR(Prop). -/
abbrev sTcrMemberProblem (th : TweakableHash P T (M × ℕ) N) (prop : N → Bool)
    (rest : TweakableHashCollection ι P T N) (p : ℕ) : STCRProblem (Option ι) P T M N :=
  ⟨th, prop, TweakableHashCollection.cons th rest, p⟩

/-- **Definition 4.12** for sm-tcr-excl, attacking an arbitrary function (in SHRINCS the
non-member `Th_{2∪lsf} = Collection.combine C H Th_lsf`) against the collection `C`, with the
partner reservation rule. -/
abbrev smTcrExclCollectionProblem (th : TweakableHash P T M N) (X : ExclusiveTweaks T)
    (C : TweakableHashCollection ι P T N) (p : ℕ) : SMTCRExclProblem ι P T M N :=
  ⟨th, X, C, p⟩

/-! ## The unconditional direction: ignoring the collection oracle -/

/-- Forward a first-stage computation written against the empty collection to an arbitrary
collection: the private-randomness and challenge queries are forwarded unchanged, and the empty
collection oracle cannot be queried. -/
def liftCollection {D : Type} (cs : OracleSpec D) (C : TweakableHashCollection ι P T N) :
    QueryImpl (unifSpec + (cs + collectionSpec (TweakableHashCollection.empty P T N)))
      (OracleComp (unifSpec + (cs + collectionSpec C))) :=
  fun
  | .inl n => ((unifSpec + (cs + collectionSpec C)).query (.inl n) :
      OracleComp (unifSpec + (cs + collectionSpec C)) (Fin (n + 1)))
  | .inr (.inl d) => ((unifSpec + (cs + collectionSpec C)).query (.inr (.inl d)) :
      OracleComp (unifSpec + (cs + collectionSpec C)) (cs.Range d))
  | .inr (.inr q) => q.1.elim

/-- A stand-alone SM-TCR adversary as an adversary against `Th ∈ Th_λ` for any collection. -/
def liftTcrAdversary {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th p))
    (C : TweakableHashCollection ι P T N) : SM_DT_TCR_Adversary (⟨th, C, p⟩ :
      SM_DT_TCR_Problem ι P T M N) where
  State := A.State
  choose := simulateQ (Notions.liftCollection (SM_DT_TCR_challengeSpec T M N) C) A.choose
  forge := A.forge

/-- **Conjecture 4.1, direction `≥` (unconditional), for SM-TCR**: a stand-alone adversary, lifted
to any collection, has the same success; hence `InSec(Th; ξ, p) ≤ InSec(Th ∈ Th_λ; ξ, p, q_λ)`. -/
theorem SM_DT_TCR_Advantage_liftCollection [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th p))
    (C : TweakableHashCollection ι P T N) :
    SM_DT_TCR_Advantage (liftTcrAdversary A C) = SM_DT_TCR_Advantage A := by
  have hsim : ∀ pk, simulateQ (SM_DT_TCR_oracles (⟨th, C, p⟩ : SM_DT_TCR_Problem ι P T M N) pk)
      (simulateQ (Notions.liftCollection (SM_DT_TCR_challengeSpec T M N) C) A.choose) =
      simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone th p) pk) A.choose := by
    intro pk
    refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.choose
    rcases x with n | tm | c
    · simp only [Notions.liftCollection, SM_DT_TCR_oracles]
      simp
    · simp only [Notions.liftCollection, SM_DT_TCR_oracles]
      simp [SM_DT_TCR_challengeOracle, SM_DT_TCR_Problem.standalone]
      rfl
    · exact c.1.elim
  unfold SM_DT_TCR_Advantage SM_DT_TCR_Experiment liftTcrAdversary
  simp only [hsim]
  rfl

/-- A stand-alone SM-PRE adversary as an adversary against `Th ∈ Th_λ` for any collection. -/
def liftPreAdversary {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_PRE_Adversary (SM_DT_PRE_Problem.standalone th id Function.injective_id p))
    (C : TweakableHashCollection ι P T N) : SM_DT_PRE_Adversary (⟨th, id,
      Function.injective_id, C, p⟩ : SM_DT_PRE_Problem ι P T M M N) where
  State := A.State
  choose := simulateQ (Notions.liftCollection (SM_DT_PRE_challengeSpec T N) C) A.choose
  invert := A.invert

/-- **Conjecture 4.1, direction `≥`, for SM-PRE.** -/
theorem SM_DT_PRE_Advantage_liftCollection [DecidableEq T] [DecidableEq N] [SampleableType M]
    {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_PRE_Adversary (SM_DT_PRE_Problem.standalone th id Function.injective_id p))
    (C : TweakableHashCollection ι P T N) :
    SM_DT_PRE_Advantage (liftPreAdversary A C) = SM_DT_PRE_Advantage A := by
  have hsim : ∀ pk, simulateQ (SM_DT_PRE_oracles (⟨th, id, Function.injective_id, C, p⟩ :
      SM_DT_PRE_Problem ι P T M M N) pk)
      (simulateQ (Notions.liftCollection (SM_DT_PRE_challengeSpec T N) C) A.choose) =
      simulateQ (SM_DT_PRE_oracles (SM_DT_PRE_Problem.standalone th id Function.injective_id p)
        pk) A.choose := by
    intro pk
    refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.choose
    rcases x with n | t | c
    · simp only [Notions.liftCollection, SM_DT_PRE_oracles]
      simp
    · simp only [Notions.liftCollection, SM_DT_PRE_oracles]
      simp [SM_DT_PRE_challengeOracle, SM_DT_PRE_Problem.standalone]
      rfl
    · exact c.1.elim
  unfold SM_DT_PRE_Advantage SM_DT_PRE_Experiment liftPreAdversary
  simp only [hsim]
  rfl

/-- A stand-alone SM-DSPR adversary as an adversary against `Th ∈ Th_λ` for any collection. -/
def liftDsprAdversary {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_DSPR_Adversary (SM_DT_DSPR_Problem.standalone th p))
    (C : TweakableHashCollection ι P T N) :
    SM_DT_DSPR_Adversary (⟨th, C, p⟩ : SM_DT_DSPR_Problem ι P T M N) where
  State := A.State
  choose := simulateQ (Notions.liftCollection (SM_DT_DSPR_challengeSpec T M N) C) A.choose
  guess := A.guess

private theorem simulateQ_dspr_lift [DecidableEq T] {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_DSPR_Adversary (SM_DT_DSPR_Problem.standalone th p))
    (C : TweakableHashCollection ι P T N) (pk : P) :
    simulateQ (SM_DT_DSPR_oracles (⟨th, C, p⟩ : SM_DT_DSPR_Problem ι P T M N) pk)
      (simulateQ (Notions.liftCollection (SM_DT_DSPR_challengeSpec T M N) C) A.choose) =
      simulateQ (SM_DT_DSPR_oracles (SM_DT_DSPR_Problem.standalone th p) pk) A.choose := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.choose
  rcases x with n | tm | c
  · simp only [Notions.liftCollection, SM_DT_DSPR_oracles]
    simp
  · simp only [Notions.liftCollection, SM_DT_DSPR_oracles]
    simp [SM_DT_DSPR_challengeOracle, SM_DT_DSPR_Problem.standalone]
    rfl
  · exact c.1.elim

/-- **Conjecture 4.1, direction `≥`, for SM-DSPR**: both `succ` and `triv` are preserved, hence
so is the advantage. -/
theorem SM_DT_DSPR_Advantage_liftCollection [Fintype M] [DecidableEq T] [DecidableEq M]
    [DecidableEq N] {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_DSPR_Adversary (SM_DT_DSPR_Problem.standalone th p))
    (C : TweakableHashCollection ι P T N) :
    SM_DT_DSPR_Advantage (liftDsprAdversary A C) = SM_DT_DSPR_Advantage A := by
  unfold SM_DT_DSPR_Advantage SM_DT_DSPR_Success SM_DT_DSPR_SPProbability
    SM_DT_DSPR_Experiment SM_DT_DSPR_SPExperiment liftDsprAdversary
  simp only [simulateQ_dspr_lift]
  rfl

/-- A stand-alone SM-UD adversary as an adversary against `Th ∈ Th_λ` for any collection. -/
def liftUdAdversary {M' : Type} {th : TweakableHash P T M N} {emb : M' → M}
    {hemb : Function.Injective emb} {inputGen : ProbComp M'} {outputGen : ProbComp N} {p : ℕ}
    (A : SM_DT_UD_Adversary (SM_DT_UD_Problem.standalone th emb hemb inputGen outputGen p))
    (C : TweakableHashCollection ι P T N) :
    SM_DT_UD_Adversary (⟨th, emb, hemb, inputGen, outputGen, C, p⟩ :
      SM_DT_UD_Problem ι P T M M' N) where
  State := A.State
  pick := simulateQ (Notions.liftCollection (SM_DT_UD_challengeSpec T N) C) A.pick
  distinguish := A.distinguish

private theorem simulateQ_ud_lift [DecidableEq T] {M' : Type} {th : TweakableHash P T M N}
    {emb : M' → M} {hemb : Function.Injective emb} {inputGen : ProbComp M'}
    {outputGen : ProbComp N} {p : ℕ}
    (A : SM_DT_UD_Adversary (SM_DT_UD_Problem.standalone th emb hemb inputGen outputGen p))
    (C : TweakableHashCollection ι P T N) (w : SM_DT_UD_World) (pk : P) :
    simulateQ (SM_DT_UD_oracles w (⟨th, emb, hemb, inputGen, outputGen, C, p⟩ :
        SM_DT_UD_Problem ι P T M M' N) pk)
      (simulateQ (Notions.liftCollection (SM_DT_UD_challengeSpec T N) C) A.pick) =
      simulateQ (SM_DT_UD_oracles w
        (SM_DT_UD_Problem.standalone th emb hemb inputGen outputGen p) pk) A.pick := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.pick
  rcases x with n | t | c
  · simp only [Notions.liftCollection, SM_DT_UD_oracles]
    simp
  · simp only [Notions.liftCollection, SM_DT_UD_oracles]
    rw [simulateQ_spec_query]
    rfl
  · exact c.1.elim

/-- **Conjecture 4.1, direction `≥`, for SM-UD**: both worlds are preserved, hence so is the
advantage. -/
theorem SM_DT_UD_Advantage_liftCollection [DecidableEq T] {M' : Type}
    {th : TweakableHash P T M N} {emb : M' → M} {hemb : Function.Injective emb}
    {inputGen : ProbComp M'} {outputGen : ProbComp N} {p : ℕ}
    (A : SM_DT_UD_Adversary (SM_DT_UD_Problem.standalone th emb hemb inputGen outputGen p))
    (C : TweakableHashCollection ι P T N) :
    SM_DT_UD_Advantage (liftUdAdversary A C) = SM_DT_UD_Advantage A := by
  unfold SM_DT_UD_Advantage SM_DT_UD_Experiment liftUdAdversary
  simp only [simulateQ_ud_lift]
  rfl

/-- A stand-alone sm-tcr-excl adversary as an adversary against any collection. -/
def liftExclAdversary {th : TweakableHash P T M N} {X : ExclusiveTweaks T} {p : ℕ}
    (A : SMTCRExclAdversary (SMTCRExclProblem.standalone th X p))
    (C : TweakableHashCollection ι P T N) :
    SMTCRExclAdversary (⟨th, X, C, p⟩ : SMTCRExclProblem ι P T M N) where
  State := A.State
  choose := simulateQ (Notions.liftCollection (SMTCRExcl_challengeSpec T M N) C) A.choose
  forge := A.forge

/-- **Conjecture 4.1, direction `≥`, for sm-tcr-excl.** -/
theorem SMTCRExcl_Succ_liftCollection [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {th : TweakableHash P T M N} {X : ExclusiveTweaks T} {p : ℕ}
    (A : SMTCRExclAdversary (SMTCRExclProblem.standalone th X p))
    (C : TweakableHashCollection ι P T N) :
    SMTCRExcl_Succ (liftExclAdversary A C) = SMTCRExcl_Succ A := by
  have hsim : ∀ pk, simulateQ (SMTCRExcl_oracles (⟨th, X, C, p⟩ : SMTCRExclProblem ι P T M N) pk)
      (simulateQ (Notions.liftCollection (SMTCRExcl_challengeSpec T M N) C) A.choose) =
      simulateQ (SMTCRExcl_oracles (SMTCRExclProblem.standalone th X p) pk) A.choose := by
    intro pk
    refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.choose
    rcases x with n | tm | c
    · simp only [Notions.liftCollection, SMTCRExcl_oracles]
      simp
    · simp only [Notions.liftCollection, SMTCRExcl_oracles]
      simp [SMTCRExcl_challengeOracle, SMTCRExclProblem.standalone]
      rfl
    · exact c.1.elim
  unfold SMTCRExcl_Succ SMTCRExcl_Experiment liftExclAdversary
  simp only [hsim]
  rfl

/-- A stand-alone S-TCR(Prop) adversary as an adversary against any collection. -/
def liftSTcrAdversary {th : TweakableHash P T (M × ℕ) N} {prop : N → Bool} {p : ℕ}
    (A : STCRAdversary (STCRProblem.standalone th prop p))
    (C : TweakableHashCollection ι P T N) :
    STCRAdversary (⟨th, prop, C, p⟩ : STCRProblem ι P T M N) where
  State := A.State
  choose := simulateQ (Notions.liftCollection (STCR_challengeSpec T M N) C) A.choose
  forge := A.forge

/-- **Conjecture 4.1, direction `≥`, for S-TCR(Prop).** -/
theorem STCR_Succ_liftCollection [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {th : TweakableHash P T (M × ℕ) N} {prop : N → Bool} {p : ℕ}
    (A : STCRAdversary (STCRProblem.standalone th prop p))
    (C : TweakableHashCollection ι P T N) :
    STCR_Succ (liftSTcrAdversary A C) = STCR_Succ A := by
  have hsim : ∀ pk, simulateQ (STCR_oracles (⟨th, prop, C, p⟩ : STCRProblem ι P T M N) pk)
      (simulateQ (Notions.liftCollection (STCR_challengeSpec T M N) C) A.choose) =
      simulateQ (STCR_oracles (STCRProblem.standalone th prop p) pk) A.choose := by
    intro pk
    refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => ?_) A.choose
    rcases x with n | tm | c
    · simp only [Notions.liftCollection, STCR_oracles]
      simp
    · simp only [Notions.liftCollection, STCR_oracles]
      simp [STCR_challengeOracle, STCRProblem.standalone]
      rfl
    · exact c.1.elim
  unfold STCR_Succ STCR_Experiment liftSTcrAdversary
  simp only [hsim]
  rfl

end ShrincsSecurity.Notions

end
