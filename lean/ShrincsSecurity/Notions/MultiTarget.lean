module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTRTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Tweakable hash functions and the multi-target notions reused from VCVio

Main paper, Section 4.1–4.2: **Definition 4.2** (tweakable hash function), **Definition 4.4**
(SM-TCR), **Definition 4.5** (SM-PRE), **Definition 4.6** (SM-UD), **Definition 4.9** (SM-rTCR)
and **Definition 4.10** (SM-DSPR), txt lines 2009–2384.

All five notions are VCVio games (`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/`),
at the empty collection for the stand-alone notions of Section 4.2 (the collection variants of
Definition 4.12 are in `ShrincsSecurity.Notions.Collection`). This file records, per notion, why
the VCVio game is the paper's game, and proves the equivalences that are not literally
definitional.

## Common conventions (all notions)

* **Public parameter.** The paper samples `P ←$ P`; VCVio samples `th.seedGen`. The paper's games
  are the instances with `th.seedGen = $ᵗ P` (`TweakableHash.UniformSeed`, and the constructor
  `TweakableHash.ofFun`).
* **Index `j`.** The paper's `j ∈ [|Q|]` is 1-based; VCVio indexes the issue-ordered history from
  `0`. For success notions (`SM-TCR`, `SM-PRE`, `SM-rTCR`) an out-of-range index loses; for
  `SM-DSPR` an out-of-range index returns `false` in both `Experiment` and `SPExperiment`,
  contributing `0 − 0 = 0` to the net advantage (matching `[BHK+19]`'s `(0, true)` fallback).
* **Refusals.** VCVio's challenge oracles return `Option`, `none` being the paper's `⊥`, with
  exactly the paper's refusal conditions (`|Q| ≥ p` or a repeated tweak), leaving the state
  untouched; the additional collection-clash refusal is vacuous at the empty collection.
* **Two stages.** `A₁` and `A₂` share a state: VCVio's adversary carries an explicit `State`
  type passed from the first to the second stage; the second stage receives `P` and has no
  oracle (it is a `ProbComp`). Private randomness is `unifSpec`.

## Per notion

* **SM-TCR** (Definition 4.4): `TweakableHash.SM_DT_TCR_Experiment` at
  `SM_DT_TCR_Problem.standalone th p`. Oracle and winning condition coincide verbatim
  (`Th(P,Tⱼ,mⱼ) = Th(P,Tⱼ,m*) ∧ m* ≠ mⱼ`).
* **SM-PRE** (Definition 4.5): `TweakableHash.SM_DT_PRE_Experiment` at `M' := M`, `emb := id`.
  The paper records `(T, y)` with `y = Th(P,T,m)` and wins on `Th(P,Tⱼ,m*) = yⱼ`; VCVio records
  `(T, m)` and wins on `Th(P,Tⱼ,m*) = Th(P,Tⱼ,mⱼ)`. The paper-literal game is `smPrePaperExperiment`
  and `smPrePaperExperiment_eq` proves it equal to VCVio's.
* **SM-UD** (Definition 4.6): `TweakableHash.SM_DT_UD_Experiment` with uniform inputs and outputs
  (`SM_DT_UD_Problem.HasUniformInputs`, `HasUniformOutputs`, both built in by `smUdProblem`). The
  paper's branch `b = 0` is `.real`, `b = 1` is `.ideal`, and the *absolute* advantage of
  Definition 4.6 is VCVio's `boolDist` (`smUdAdv_toReal`), matching both the main paper and the
  undetectability companion paper (Definition 4).
* **SM-rTCR** (Definition 4.9): `TweakableHash.SM_DT_RTCR_Experiment`. `numRetries` is the
  sampling budget `K`, `prop` the predicate `Prop`; the public parameter is given at the start and
  there is no collection oracle (as in the paper). An exhausted challenge records `(T, m, ⊥)`,
  consumes a target, and loses if named (the paper's interpretation at txt lines 7684–7687).
  Winning requires `(m*, ρ*) ≠ (mⱼ, ρⱼ)`.
* **SM-DSPR** (Definition 4.10): `TweakableHash.SM_DT_DSPR_Experiment` and
  `SM_DT_DSPR_SPExperiment`. `SecondPreimageExists` is the paper's `SP_{P,T}(x) = 1`
  (`secondPreimageExists_iff_card_fiber`), and VCVio's truncated difference is the paper's
  `max{0, succ − triv}` (`smDsprAdv_toReal`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace TweakableHash

variable {P T M N : Type}

/-- The public parameter of a tweakable hash is sampled uniformly, as in step 2 of every
experiment of Section 4.2 (`P ←$ P`). -/
def UniformSeed [SampleableType P] (th : TweakableHash P T M N) : Prop :=
  th.seedGen = $ᵗ P

/-- **Definition 4.2** (tweakable hash function `Th : P × T × M → N`), with the uniformly
sampled public parameter of the security experiments. -/
def ofFun [SampleableType P] (f : P → T → M → N) : TweakableHash P T M N where
  seedGen := $ᵗ P
  eval := f

theorem ofFun_uniformSeed [SampleableType P] (f : P → T → M → N) : (ofFun f).UniformSeed := rfl

/-- The paper's second-preimage predicate `SP_{P,T}(x) = 1 ⟺ |Th_{P,T}⁻¹(Th_{P,T}(x))| ≥ 2`
(Definition 4.10) is VCVio's `SecondPreimageExists`. -/
theorem secondPreimageExists_iff_card_fiber [Fintype M] [DecidableEq N]
    (th : TweakableHash P T M N) (pk : P) (t : T) (x : M) :
    SecondPreimageExists th pk t x ↔
      2 ≤ (Finset.univ.filter fun m => th.eval pk t m = th.eval pk t x).card := by
  classical
  change _ ↔ 1 < _
  rw [SecondPreimageExists]
  constructor
  · rintro ⟨m', hne, heq⟩
    exact Finset.one_lt_card.mpr ⟨x, by simp, m', by simp [heq], hne⟩
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_cases hax : a = x
    · exact ⟨b, fun h => hab (hax.trans h), hb.symm⟩
    · exact ⟨a, fun h => hax h.symm, ha.symm⟩

end TweakableHash

namespace ShrincsSecurity.Notions

open TweakableHash

variable {P T M N : Type}

/-! ## Definition 4.4: SM-TCR -/

/-- **Definition 4.4** (SM-TCR), the stand-alone problem with `p` targets. -/
abbrev smTcrProblem (th : TweakableHash P T M N) (p : ℕ) : SM_DT_TCR_Problem Empty P T M N :=
  SM_DT_TCR_Problem.standalone th p

/-- **Definition 4.4**: `Succ^{sm-tcr}_{Th,p}(A)`. -/
noncomputable abbrev smTcrSucc [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {th : TweakableHash P T M N} {p : ℕ} (A : SM_DT_TCR_Adversary (smTcrProblem th p)) : ℝ≥0∞ :=
  SM_DT_TCR_Advantage A

/-! ## Definition 4.5: SM-PRE -/

/-- **Definition 4.5** (SM-PRE), the stand-alone problem with `p` targets and hidden inputs
uniform on all of `M`. -/
abbrev smPreProblem (th : TweakableHash P T M N) (p : ℕ) : SM_DT_PRE_Problem Empty P T M M N :=
  SM_DT_PRE_Problem.standalone th id Function.injective_id p

/-- **Definition 4.5**: `Succ^{sm-pre}_{Th,p}(A)`. -/
noncomputable abbrev smPreSucc [DecidableEq T] [DecidableEq N] [SampleableType M]
    {th : TweakableHash P T M N} {p : ℕ} (A : SM_DT_PRE_Adversary (smPreProblem th p)) : ℝ≥0∞ :=
  SM_DT_PRE_Advantage A

section PaperPRE

variable [DecidableEq T] [SampleableType M]

/-- The challenge oracle of Definition 4.5 as printed: it records the pair `(T, y)` of the queried
tweak and the returned image (`y = Th(P, T, m)` for a hidden uniform `m`). The second state
component is the (always empty) collection-tweak list of the stand-alone game. -/
noncomputable def smPrePaperChallenge (th : TweakableHash P T M N) (p : ℕ) (pk : P) :
    QueryImpl (SM_DT_PRE_challengeSpec T N) (StateT (List (T × N) × List T) ProbComp) :=
  fun t => do
    let s ← get
    if p ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 t then
      return none
    else
      let m ← (($ᵗ M : ProbComp M) : StateT (List (T × N) × List T) ProbComp M)
      set (s.1 ++ [(t, th.eval pk t m)], s.2)
      return some (th.eval pk t m)

/-- All oracles of the printed SM-PRE game (the collection oracle is unqueryable). -/
noncomputable def smPrePaperOracles (th : TweakableHash P T M N) (p : ℕ) (pk : P) :
    QueryImpl (unifSpec + (SM_DT_PRE_challengeSpec T N +
        collectionSpec (smPreProblem th p).thColl))
      (StateT (List (T × N) × List T) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List (T × N) × List T) ProbComp) +
    (smPrePaperChallenge th p pk +
      (fun q => q.1.elim : QueryImpl (collectionSpec (smPreProblem th p).thColl)
        (StateT (List (T × N) × List T) ProbComp)))

/-- **Definition 4.5** as printed: the experiment records `(Tⱼ, yⱼ)` and wins on
`Th(P, Tⱼ, m*) = yⱼ`. -/
noncomputable def smPrePaperExperiment [DecidableEq N] {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_PRE_Adversary (smPreProblem th p)) : ProbComp Bool := do
  let pk ← th.seedGen
  let (st, Q, _) ← (simulateQ (smPrePaperOracles th p pk) A.choose).run ([], [])
  let (j, m) ← A.invert st pk
  match Q[j]? with
  | none => return false
  | some (t, y) => return decide (th.eval pk t m = y)

omit [DecidableEq T] [SampleableType M] in
private lemma tweakFresh_map_iff (pk : P) (th : TweakableHash P T M N) (Q : List (T × M))
    (tw : List T) (t : T) :
    TweakFresh Prod.fst (Q.map fun e => (e.1, th.eval pk e.1 e.2)) tw t ↔
      TweakFresh Prod.fst Q tw t := by
  simp [TweakFresh, TweakReserved]

/-- The printed SM-PRE experiment of Definition 4.5 is VCVio's SM-PRE experiment: recording the
image instead of the hidden input changes nothing observable. -/
theorem smPrePaperExperiment_eq [DecidableEq N] {th : TweakableHash P T M N} {p : ℕ}
    (A : SM_DT_PRE_Adversary (smPreProblem th p)) :
    smPrePaperExperiment A = SM_DT_PRE_Experiment A := by
  let proj : P → List (T × M) × List T → List (T × N) × List T := fun pk s =>
    (s.1.map fun e => (e.1, th.eval pk e.1 e.2), s.2)
  have hstep : ∀ pk, ∀ (q : (unifSpec + (SM_DT_PRE_challengeSpec T N +
      collectionSpec (smPreProblem th p).thColl)).Domain) (s : List (T × M) × List T),
      Prod.map id (proj pk) <$> ((SM_DT_PRE_oracles (smPreProblem th p) pk) q).run s =
        ((smPrePaperOracles th p pk) q).run (proj pk s) := by
    intro pk q s
    rcases q with n | t | c
    · simp only [SM_DT_PRE_oracles, smPrePaperOracles]
      rw [QueryImpl.add_apply_inl, QueryImpl.add_apply_inl]
      simp [proj]
    · simp only [SM_DT_PRE_oracles, smPrePaperOracles]
      rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        QueryImpl.add_apply_inl]
      simp only [SM_DT_PRE_challengeOracle, smPrePaperChallenge, StateT.run_bind, StateT.run_get,
        pure_bind, proj, List.length_map, tweakFresh_map_iff, smPreProblem,
        SM_DT_PRE_Problem.standalone]
      split_ifs with h <;> simp [h]
    · exact c.1.elim
  unfold smPrePaperExperiment SM_DT_PRE_Experiment
  refine bind_congr fun pk => ?_
  have h := map_run_simulateQ_eq_of_query_map_eq _ _ (proj pk) (hstep pk) A.choose ([], [])
  rw [show (simulateQ (smPrePaperOracles th p pk) A.choose).run ([], []) =
    Prod.map id (proj pk) <$>
      (simulateQ (SM_DT_PRE_oracles (smPreProblem th p) pk) A.choose).run ([], []) from h.symm,
    bind_map_left]
  refine bind_congr fun r => ?_
  refine bind_congr fun jm => ?_
  simp only [List.getElem?_map]
  cases r.2.1[jm.1]? with
  | none => simp
  | some e => simp only [Option.map_some]; exact congrArg pure (decide_eq_decide.mpr Iff.rfl)

end PaperPRE

/-! ## Definition 4.6: SM-UD -/

/-- **Definition 4.6** (SM-UD), the stand-alone problem: hidden inputs uniform on `M` (`b = 0`)
against outputs uniform on `N` (`b = 1`). -/
noncomputable abbrev smUdProblem [SampleableType M] [SampleableType N]
    (th : TweakableHash P T M N) (p : ℕ) : SM_DT_UD_Problem Empty P T M M N :=
  SM_DT_UD_Problem.standalone th id Function.injective_id ($ᵗ M) ($ᵗ N) p

theorem smUdProblem_hasUniformInputs [SampleableType M] [SampleableType N]
    (th : TweakableHash P T M N) (p : ℕ) : (smUdProblem th p).HasUniformInputs := rfl

/-- **Definition 4.6**: `Adv^{sm-ud}_{Th,p}(A)`. -/
noncomputable abbrev smUdAdv [DecidableEq T] [SampleableType M] [SampleableType N]
    {th : TweakableHash P T M N} {p : ℕ} (A : SM_DT_UD_Adversary (smUdProblem th p)) : ℝ≥0∞ :=
  SM_DT_UD_Advantage A

/-- The advantage of Definition 4.6 is the *absolute* difference
`|Pr[⇒1 | b=1] − Pr[⇒1 | b=0]|` of the two branches. -/
theorem smUdAdv_toReal [DecidableEq T] [SampleableType M] [SampleableType N]
    {th : TweakableHash P T M N} {p : ℕ} (A : SM_DT_UD_Adversary (smUdProblem th p)) :
    (smUdAdv A).toReal =
      |(𝒟[SM_DT_UD_Experiment .ideal A] {true}).toReal -
        (𝒟[SM_DT_UD_Experiment .real A] {true}).toReal| := by
  unfold smUdAdv SM_DT_UD_Advantage
  rw [MeasureTheory.Measure.toReal_boolDist, abs_sub_comm]

/-! ## Definition 4.9: SM-rTCR -/

/-- **Definition 4.9** (SM-rTCR with sampling budget `K` and predicate `Prop`). -/
def smRtcrProblem {R : Type} (th : TweakableHash P T (M × R) N) (prop : N → Bool) (p K : ℕ) :
    SM_DT_RTCR_Problem P T M R N where
  th := th
  prop := prop
  numTargets := p
  numRetries := K

/-- **Definition 4.9**: `Succ^{SM-rTCR,K}_{Th,p,Prop}(A)`. -/
noncomputable abbrev smRtcrSucc {R : Type} [DecidableEq T] [DecidableEq M] [DecidableEq R]
    [DecidableEq N] [SampleableType R] {th : TweakableHash P T (M × R) N} {prop : N → Bool}
    {p K : ℕ} (A : SM_DT_RTCR_Adversary (smRtcrProblem th prop p K)) : ℝ≥0∞ :=
  SM_DT_RTCR_Advantage A

/-! ## Definition 4.10: SM-DSPR -/

/-- **Definition 4.10** (SM-DSPR), the stand-alone problem with `p` targets. -/
abbrev smDsprProblem (th : TweakableHash P T M N) (p : ℕ) : SM_DT_DSPR_Problem Empty P T M N :=
  SM_DT_DSPR_Problem.standalone th p

/-- **Definition 4.10**: `Adv^{sm-dspr}_{Th,p}(A) = max{0, succ − triv}`. -/
noncomputable abbrev smDsprAdv [Fintype M] [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {th : TweakableHash P T M N} {p : ℕ} (A : SM_DT_DSPR_Adversary (smDsprProblem th p)) :
    ℝ≥0∞ :=
  SM_DT_DSPR_Advantage A

/-- VCVio's truncated `ℝ≥0∞` difference is the paper's `max{0, succ − triv}`. -/
theorem smDsprAdv_toReal [Fintype M] [DecidableEq T] [DecidableEq M] [DecidableEq N]
    {th : TweakableHash P T M N} {p : ℕ} (A : SM_DT_DSPR_Adversary (smDsprProblem th p)) :
    (smDsprAdv A).toReal =
      max 0 ((SM_DT_DSPR_Success A).toReal - (SM_DT_DSPR_SPProbability A).toReal) := by
  have h1 : SM_DT_DSPR_Success A ≠ ⊤ := by
    unfold SM_DT_DSPR_Success; exact MeasureTheory.measure_ne_top _ _
  have h2 : SM_DT_DSPR_SPProbability A ≠ ⊤ := by
    unfold SM_DT_DSPR_SPProbability; exact MeasureTheory.measure_ne_top _ _
  unfold smDsprAdv SM_DT_DSPR_Advantage
  rcases le_total (SM_DT_DSPR_Success A) (SM_DT_DSPR_SPProbability A) with h | h
  · rw [tsub_eq_zero_of_le h, ENNReal.toReal_zero, eq_comm, max_eq_left]
    exact sub_nonpos.mpr ((ENNReal.toReal_le_toReal h1 h2).mpr h)
  · rw [ENNReal.toReal_sub_of_le h h1, eq_comm, max_eq_right]
    exact sub_nonneg.mpr ((ENNReal.toReal_le_toReal h2 h1).mpr h)

end ShrincsSecurity.Notions

end
