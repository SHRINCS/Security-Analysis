module

public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Keyed hash functions and pseudorandomness

Main paper, Section 4.1–4.2: **Definition 4.1** (keyed hash function) and **Definition 4.3**
(PRF), txt lines 2002–2068.

## Reuse of VCVio

Definition 4.3 is VCVio's `PRFScheme.prfAdvantage`, with the keyed hash `F` packaged as the
`PRFScheme` whose key generation is uniform (`KeyedHash.toPRF`). The match is exact:

* the paper's experiment samples `k ←$ K`, a uniform function `G : M → N` and a bit `b`, and
  answers queries with `F(k, ·)` for `b = 0` and with `G` for `b = 1`. VCVio's
  `prfRealExperiment` is the `b = 0` branch and `prfIdealExperiment` the `b = 1` branch, where the
  uniform function is the lazily sampled random oracle (`OracleSpec.romImpl`), which is
  distributed as a uniform function and consistent on repeated inputs (the paper's remark that
  repeated inputs to the ideal oracle return the same value);
* `Adv^prf_{F,p}(A) = |Pr[⇒1 | b=1] − Pr[⇒1 | b=0]|` is `Measure.boolDist` of the two branches
  (`prfAdv_toReal`).

The paper's oracle answers `⊥` after `p` queries. We bound the adversary instead
(`PRFAdversary.queryBound`, an `IsQueryBoundP` budget on function queries); on adversaries within
budget the refusal never fires, so the two formulations agree. Private randomness of the
adversary is VCVio's `unifSpec`, which the paper leaves implicit.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Notions

/-- **Definition 4.1** (keyed hash function) `F : K × M → N`, written curried. -/
abbrev KeyedHash (K M N : Type) := K → M → N

namespace KeyedHash

variable {K M N : Type}

/-- A keyed hash function viewed as a PRF candidate with uniformly sampled key, as in step 1 of
Definition 4.3 (`k ←$ K`). -/
def toPRF [SampleableType K] (F : KeyedHash K M N) : PRFScheme K M N where
  keygen := $ᵗ K
  eval := F

theorem toPRF_uniformKey [SampleableType K] (F : KeyedHash K M N) : (toPRF F).UniformKey := rfl

end KeyedHash

/-- A query of a PRF distinguisher is a function query (as opposed to private randomness). -/
def IsPRFQuery {D : Type} : ℕ ⊕ D → Prop
  | .inr _ => True
  | .inl _ => False

instance {D : Type} : DecidablePred (IsPRFQuery (D := D)) := fun x => by
  rcases x with _ | _ <;> simp only [IsPRFQuery] <;> infer_instance

/-- A PRF adversary of **Definition 4.3** making at most `p` (classical) oracle queries. -/
structure PRFAdversary (D R : Type) (p : ℕ) where
  /-- The distinguisher, with private randomness and the challenge oracle `O(·, b)`. -/
  run : PRFScheme.PRFAdversary D R
  /-- At most `p` challenge-oracle queries on every execution path. -/
  queryBound : run.IsQueryBoundP IsPRFQuery p

variable {K D R : Type}

/-- **Definition 4.3**: `Adv^prf_{F,p}(A)`, the distinguishing advantage between the real
(`b = 0`) and the ideal (`b = 1`) branch. -/
noncomputable def prfAdv [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R) {p : ℕ}
    (A : PRFAdversary D R p) : ℝ≥0∞ :=
  prf.prfAdvantage A.run

/-- The advantage of Definition 4.3 is the absolute difference of the two output-one
probabilities. -/
theorem prfAdv_toReal [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R) {p : ℕ}
    (A : PRFAdversary D R p) :
    (prfAdv prf A).toReal =
      |(𝒟[prf.prfRealExperiment A.run] {true}).toReal -
        (𝒟[PRFScheme.prfIdealExperiment A.run] {true}).toReal| := by
  unfold prfAdv PRFScheme.prfAdvantage
  rw [MeasureTheory.Measure.toReal_boolDist]

end ShrincsSecurity.Notions

end
