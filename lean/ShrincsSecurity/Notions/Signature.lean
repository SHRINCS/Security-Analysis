module

public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Signature schemes and EU-CMA games

Main paper, Section 4.5: **Definition 4.13** (digital signature scheme), **Definition 4.14**
(EU-CMA), **Definition 4.15** (SHRINCS EU-CMA), and Section 4.7, **Definition 4.16** (FXMSS
EU-CMA), txt lines 2759–2837 and 3116–3155.

## Definitions 4.13 and 4.14: reused from VCVio

A digital signature scheme `(Kg, Sign, Verify)` is VCVio's `SignatureAlg (OracleComp spec)`, the
ambient oracles `spec` carrying the random oracles of the model (for a standard-model scheme,
`spec := unifSpec`). EU-CMA is `SignatureAlg.unforgeableExperiment`: the adversary gets `pk` and a
logged signing oracle and wins with a valid `(M*, σ*)` such that `M*` was never submitted to the
signing oracle, exactly the event `Verify(pk, σ*, M*) = 1 ∧ M* ∉ {Mᵢ}` of Definition 4.14. The
paper's "making `q` signing queries" is the budget `EUCMAAdversary.signBound`.

## Definitions 4.15 and 4.16: an abstract interface

The concrete SHRINCS and FXMSS algorithms live in `ShrincsSecurity.Scheme`; to keep the games
independent of them, they are stated over minimal interfaces (`ShrincsScheme`, `FxmssScheme`)
that the concrete schemes instantiate:

* **SHRINCS** (Definition 4.15): key generation from a shape descriptor `Π`, a *stateful* signer
  (the next unused stateful key, `⊥` when all are exhausted; the state is threaded through the
  signing oracle) and a *stateless* signer, chosen per query by the path bit `b`
  (`b = 0` stateful, `b = 1` stateless; we write `false`/`true`), and verification.
* **FXMSS** (Definition 4.16): key generation from `Π` (in the paper, with idealized uniform
  secrets and the full SHRINCS public key; that is the instantiation's business), and a signer
  that signs at an adversarially named leaf. Queried leaves must be pairwise distinct and belong to
  the structure; other queries are answered `⊥`.

Both games are two-stage: `A₁` outputs a shape descriptor (and a state passed to `A₂`); an
invalid descriptor loses (the paper restricts to valid descriptors). `A₂` receives `Π` and `pk`
and has the ambient oracles and the signing oracle. The forgery's message must differ from every
*queried* message (`M* ∉ {Mᵢ}_{i=1}^{q_s}`); we record every queried message, answered or not,
which is the literal reading (a query answered `⊥` can be skipped by the adversary at no cost, so
the choice does not affect the notion).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Notions

universe u

/-! ## Definitions 4.13 and 4.14 -/

/-- A signing query, as opposed to an ambient-oracle query. -/
def IsSignQuery {ι : Type u} {M : Type} : ι ⊕ M → Prop
  | .inr _ => True
  | .inl _ => False

instance {ι : Type u} {M : Type} : DecidablePred (IsSignQuery (ι := ι) (M := M)) := fun x => by
  rcases x with _ | _ <;> simp only [IsSignQuery] <;> infer_instance

section EUCMA

variable {ι : Type} {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EU-CMA adversary of **Definition 4.14** making at most `q` signing queries. -/
structure EUCMAAdversary (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) (q : ℕ) where
  /-- The forger. -/
  adv : SignatureAlg.UnforgeableAdversary sigAlg
  /-- At most `q` signing queries for every public key. -/
  signBound : ∀ pk, (adv.main pk).IsQueryBoundP IsSignQuery q

/-- **Definition 4.14**: `Succ^{EU-CMA}_{Dss,q}(A)`. -/
noncomputable def euCmaSucc {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec)) {q : ℕ} (A : EUCMAAdversary sigAlg q) : ℝ≥0∞ :=
  SignatureAlg.unforgeableAdvantage runtime A.adv

end EUCMA

/-! ## Definition 4.15: SHRINCS EU-CMA -/

/-- The interface of the SHRINCS scheme consumed by **Definition 4.15**. `Shape` is the type of
shape descriptors `Π`, `St` the signer's evolving state (the stateful-key counter). -/
structure ShrincsScheme {ι : Type} (spec : OracleSpec ι) (Shape M PK SK St Sig : Type) where
  /-- `Π` describes a valid structure (Section 2.5). -/
  ValidShape : Shape → Prop
  /-- Validity is decidable. -/
  decValidShape : DecidablePred ValidShape
  /-- `Kg(1ⁿ, Π)`: public key, secret key and initial signer state. -/
  keygen : Shape → OracleComp spec (PK × SK × St)
  /-- `Sign_sf`: sign with the next unused stateful key; `none` (`⊥`) when exhausted. -/
  signSF : SK → St → M → OracleComp spec (Option Sig × St)
  /-- `Sign_sl`: sign on the stateless path. -/
  signSL : SK → M → OracleComp spec Sig
  /-- `Verify(pk, σ, M)`. -/
  verify : PK → M → Sig → OracleComp spec Bool

namespace ShrincsScheme

variable {ι : Type} {spec : OracleSpec ι} {Shape M PK SK St Sig : Type}

/-- The SHRINCS signing oracle's signature: a message and the path bit `b`
(`false` = stateful, `true` = stateless). -/
abbrev signSpec (M Sig : Type) : OracleSpec (M × Bool) := (M × Bool) →ₒ Option Sig

/-- The signing oracle `O_sk(·, ·)` of Definition 4.15, over the state (signer state, queried
messages). -/
def signOracle (scheme : ShrincsScheme spec Shape M PK SK St Sig) (sk : SK) :
    QueryImpl (signSpec M Sig) (StateT (St × List M) (OracleComp spec)) :=
  fun q => do
    let (st, log) ← get
    if q.2 then
      let σ ← (scheme.signSL sk q.1 : OracleComp spec Sig)
      set (st, log ++ [q.1])
      return some σ
    else
      let (σ?, st') ← (scheme.signSF sk st q.1 : OracleComp spec (Option Sig × St))
      set (st', log ++ [q.1])
      return σ?

/-- The forger's oracles: ambient oracles forwarded, and the signing oracle. -/
def oracles (scheme : ShrincsScheme spec Shape M PK SK St Sig) (sk : SK) :
    QueryImpl (spec + signSpec M Sig) (StateT (St × List M) (OracleComp spec)) :=
  (QueryImpl.id' spec).liftTarget (StateT (St × List M) (OracleComp spec)) +
    scheme.signOracle sk

end ShrincsScheme

/-- A two-stage SHRINCS EU-CMA adversary of **Definition 4.15** with `q_s` signing queries. -/
structure ShrincsAdversary {ι : Type} {spec : OracleSpec ι} {Shape M PK SK St Sig : Type}
    (_scheme : ShrincsScheme spec Shape M PK SK St Sig) (qs : ℕ) where
  /-- State passed from `A₁` to `A₂`. -/
  State : Type
  /-- `A₁`: the structure phase, outputting a shape descriptor `Π`. -/
  chooseShape : OracleComp spec (Shape × State)
  /-- `A₂(Π, pk)`: the signing phase and forgery `(M*, σ*)`. -/
  forge : State → Shape → PK → OracleComp (spec + ShrincsScheme.signSpec M Sig) (M × Sig)
  /-- At most `q_s` signing queries. -/
  signBound : ∀ st sh pk, (forge st sh pk).IsQueryBoundP IsSignQuery qs

namespace ShrincsScheme

variable {ι : Type} {spec : OracleSpec ι} {Shape M PK SK St Sig : Type}

/-- **Definition 4.15**: the SHRINCS EU-CMA experiment. -/
def experiment [DecidableEq M] (scheme : ShrincsScheme spec Shape M PK SK St Sig) {qs : ℕ}
    (A : ShrincsAdversary scheme qs) : OracleComp spec Bool := do
  let (sh, st) ← A.chooseShape
  have := scheme.decValidShape
  if ¬ scheme.ValidShape sh then return false
  else
    let (pk, sk, s₀) ← scheme.keygen sh
    let ((m, σ), (_, log)) ← (simulateQ (scheme.oracles sk) (A.forge st sh pk)).run (s₀, [])
    let ok ← scheme.verify pk m σ
    return (ok && !(decide (m ∈ log)))

/-- **Definition 4.15**: `Succ^{SHRINCS-EU-CMA}_{SHRINCS,q_s}(A)`. -/
noncomputable def succ [DecidableEq M] (scheme : ShrincsScheme spec Shape M PK SK St Sig)
    (runtime : ProbCompRuntime (OracleComp spec)) {qs : ℕ} (A : ShrincsAdversary scheme qs) :
    ℝ≥0∞ :=
  runtime.evalDist (scheme.experiment A) {true}

end ShrincsScheme

/-! ## Definition 4.16: FXMSS EU-CMA -/

/-- The interface of the stateful component FXMSS consumed by **Definition 4.16**. `Leaf` is the
type of leaf identifiers `(z*, i*)`. -/
structure FxmssScheme {ι : Type} (spec : OracleSpec ι) (Shape Leaf M PK SK Sig : Type) where
  /-- `Π` describes a valid structure. -/
  ValidShape : Shape → Prop
  /-- Validity is decidable. -/
  decValidShape : DecidablePred ValidShape
  /-- The leaf `(z*, i*)` is a signing leaf (anchor) of the structure `Π`. -/
  IsLeaf : Shape → Leaf → Prop
  /-- Leaf membership is decidable. -/
  decIsLeaf : ∀ sh, DecidablePred (IsLeaf sh)
  /-- `K̃g(1ⁿ, Π)`, the (idealized) key generation. -/
  keygen : Shape → OracleComp spec (PK × SK)
  /-- `FXMSS.Sign(sk, M, (z*, i*))`, sampling its randomizer. -/
  sign : SK → M → Leaf → OracleComp spec Sig
  /-- `FXMSS.Verify(pk, M, (z*, i*), σ)`. -/
  verify : PK → M → Leaf → Sig → OracleComp spec Bool

namespace FxmssScheme

variable {ι : Type} {spec : OracleSpec ι} {Shape Leaf M PK SK Sig : Type}

/-- The FXMSS signing oracle's signature: a message and a named leaf. -/
abbrev signSpec (M Leaf Sig : Type) : OracleSpec (M × Leaf) := (M × Leaf) →ₒ Option Sig

/-- The signing oracle of Definition 4.16 over the state (used leaves, queried messages): a leaf
outside the structure or already used is answered `⊥`. -/
def signOracle [DecidableEq Leaf] (scheme : FxmssScheme spec Shape Leaf M PK SK Sig) (sh : Shape)
    (sk : SK) :
    QueryImpl (signSpec M Leaf Sig) (StateT (List Leaf × List M) (OracleComp spec)) :=
  fun q => do
    let (used, log) ← get
    have := scheme.decIsLeaf sh
    if scheme.IsLeaf sh q.2 ∧ q.2 ∉ used then
      let σ ← (scheme.sign sk q.1 q.2 : OracleComp spec Sig)
      set (used ++ [q.2], log ++ [q.1])
      return some σ
    else
      set (used, log ++ [q.1])
      return none

/-- The forger's oracles: ambient oracles forwarded, and the signing oracle. -/
def oracles [DecidableEq Leaf] (scheme : FxmssScheme spec Shape Leaf M PK SK Sig) (sh : Shape)
    (sk : SK) :
    QueryImpl (spec + signSpec M Leaf Sig) (StateT (List Leaf × List M) (OracleComp spec)) :=
  (QueryImpl.id' spec).liftTarget (StateT (List Leaf × List M) (OracleComp spec)) +
    scheme.signOracle sh sk

end FxmssScheme

/-- A two-stage FXMSS EU-CMA adversary of **Definition 4.16** with `q_s` signing queries. -/
structure FxmssAdversary {ι : Type} {spec : OracleSpec ι} {Shape Leaf M PK SK Sig : Type}
    (_scheme : FxmssScheme spec Shape Leaf M PK SK Sig) (qs : ℕ) where
  /-- State passed from `A₁` to `A₂`. -/
  State : Type
  /-- `A₁`: the structure phase. -/
  chooseShape : OracleComp spec (Shape × State)
  /-- `A₂(Π, pk)`: signing queries `(Mᵢ, (zᵢ*, iᵢ*))` and forgery `(M*, (z*, i*), σ*)`. -/
  forge : State → Shape → PK →
    OracleComp (spec + FxmssScheme.signSpec M Leaf Sig) (M × Leaf × Sig)
  /-- At most `q_s` signing queries. -/
  signBound : ∀ st sh pk, (forge st sh pk).IsQueryBoundP IsSignQuery qs

namespace FxmssScheme

variable {ι : Type} {spec : OracleSpec ι} {Shape Leaf M PK SK Sig : Type}

/-- **Definition 4.16**: the FXMSS EU-CMA experiment. -/
def experiment [DecidableEq Leaf] [DecidableEq M]
    (scheme : FxmssScheme spec Shape Leaf M PK SK Sig) {qs : ℕ} (A : FxmssAdversary scheme qs) :
    OracleComp spec Bool := do
  let (sh, st) ← A.chooseShape
  have := scheme.decValidShape
  if ¬ scheme.ValidShape sh then return false
  else
    let (pk, sk) ← scheme.keygen sh
    let ((m, leaf, σ), (_, log)) ←
      (simulateQ (scheme.oracles sh sk) (A.forge st sh pk)).run ([], [])
    let ok ← scheme.verify pk m leaf σ
    return (ok && !(decide (m ∈ log)))

/-- **Definition 4.16**: `Succ^{FXMSS-EU-CMA}_{FXMSS,q_s}(A)`. -/
noncomputable def succ [DecidableEq Leaf] [DecidableEq M]
    (scheme : FxmssScheme spec Shape Leaf M PK SK Sig)
    (runtime : ProbCompRuntime (OracleComp spec)) {qs : ℕ} (A : FxmssAdversary scheme qs) :
    ℝ≥0∞ :=
  runtime.evalDist (scheme.experiment A) {true}

end FxmssScheme

end ShrincsSecurity.Notions

end
