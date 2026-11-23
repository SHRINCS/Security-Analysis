module

public import ShrincsSecurity.Shrincs.Model
public import ShrincsSecurity.Notions.PRF

/-!
# The games `GAME.0`–`GAME.2` of the proof of Theorem 4.1 and the PRF reductions

`SHRINCS-Security-Analysis.pdf`, Section 4.8 (txt lines 3940–3990): `GAME.0` (the experiment),
`GAME.1` (uniform secret elements on both paths, Claim 4.11) and `GAME.2` (uniform randomizers on
both paths, Claim 4.12), with the reductions `B_prf` (the paper's `B₁` of the first hop) and
`B_prfmsg` (the paper's `B₂`).

## One handler for all modes

All three games, and both reductions, run the signing phase of the forger through **one**
handler `implC`, generic in the monad `m` and parametric in two sources:

* `sec : PK.seed × SecAdrs → m Y`, the secret element at a secret-key address of the stateless
  path (`PRF(PK.seed, SK.seed, ADRS)` in `GAME.0`, a lazily sampled uniform function from
  `GAME.1` on, a `PRF` oracle query in `B_prf`);
* `rnd : PrfMsgInput → m Y`, the combined randomizer function `PRF_msg(SK.prf, ·)` (`GAME.0`,
  `GAME.1`), a lazily sampled uniform function (`GAME.2`), a `PRF_msg` oracle query in
  `B_prfmsg`.

The WOTS+C secrets of the stateful path form a table on anchors × chains (`SkIdx`): the
PRF values at the `SF_WOTS_C_PRF` addresses in `GAME.0`, a uniform table from `GAME.1` on, and the
answers of `|SkIdx|` oracle queries in `B_prf` (`tableList`). The random oracle `H_msg^sf` is
lazily sampled on the handler's state (`CSt.cache`), continuing the cache of the structure phase.

A reduction is the same program in the monad `OracleComp (unifSpec + (D →ₒ Y))` with its source
a query, so its real world is a game by interpretation (`simulateQ` of the real PRF is a monad
morphism under which the handler is natural), and its ideal world is the next game by lazy
sampling.

The order of the samples is chosen so that each reduction's worlds line up with the games:
`SK.seed` first (the PRF key of `B_prf`), then the structure phase `A₁`, `PK.seed`, `SK.prf`.
`Bridge0.lean` shows that the experiment of Definition 4.15 is `GAME.0`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte)
open Fxmss.Rom (roIn verifyWith pkSfOf skOf SkIdx Keys roSpec RoIn)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)

/-! ## Lazily sampled functions -/

/-- A lazily sampled uniform function `D → R` on a cache, in any monad that can sample. -/
def lazyRO {D R : Type} [DecidableEq D] [SampleableType R] {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] (x : D) : StateT (D →ₒ R).QueryCache m R :=
  StateT.mk fun c => match c x with
    | some v => pure (v, c)
    | none => (fun v => (v, c.cacheQuery x v)) <$> (liftM ($ᵗ R : ProbComp R) : m R)

/-- The cache of the lazily sampled stateless secrets. -/
abbrev SecCache : Type := (pr.PkSeed × SecAdrs →ₒ pr.Y).QueryCache

/-- The cache of the lazily sampled randomizers. -/
abbrev RndCache : Type := (PrfMsgInput pr.PkSeed pr.Y →ₒ pr.Y).QueryCache

/-- Query a source at every element of a list, returning the table (`default` off the list). -/
def tableList {m : Type → Type} [Monad m] {T R : Type} [DecidableEq T] [Inhabited R]
    (q : T → m R) : List T → m (T → R)
  | [] => pure fun _ => default
  | t :: ts => do
    let v ← q t
    let g ← tableList q ts
    return Function.update g t v

/-- Query a source at every element of a finite type, returning the table. -/
noncomputable def tableM {m : Type → Type} [Monad m] {T R : Type} [Fintype T] [DecidableEq T]
    [Inhabited R] (q : T → m R) : m (T → R) :=
  tableList q (Finset.univ : Finset T).toList

/-- The `SF_WOTS_C_PRF` address of a stateful secret element (Section 2.4, Table 3). -/
def sfPrfAdrs {S : Structure} (i : SkIdx vp.params S) : Adrs :=
  (SfAdrs.prfAdrs S.tag i.1.1 i.2.val).toAdrs

/-! ## The signing-phase handler -/

/-- The state of the signing phase: the random-oracle cache, the stateful counter and the
queried messages (both paths). -/
structure CSt where
  /-- The cache of `H_msg^sf`. -/
  cache : (roSpec pr (BMsg pr Msg)).QueryCache
  /-- The stateful counter `ctr`. -/
  ctr : ℕ
  /-- The queried messages, answered or not, of both paths. -/
  log : List Msg

/-- The initial state of the signing phase, continuing the cache `c` of the structure phase. -/
def CSt.init (c : (roSpec pr (BMsg pr Msg)).QueryCache) : CSt pr Msg := ⟨c, 0, []⟩

/-- The forger's oracles in its signing phase: private coins, `H_msg^sf`, and the SHRINCS signing
oracle with the path bit (Definition 4.15). -/
abbrev advSpec := spec pr Msg + Notions.ShrincsScheme.signSpec Msg (Sig pr)

variable [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

section Handler

variable {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]

/-- The lazily sampled random oracle `H_msg^sf` on the cache of the state. -/
def roStepC (x : RoIn pr (BMsg pr Msg)) : StateT (CSt pr Msg) m pr.Digest :=
  StateT.mk fun s => match s.cache x with
    | some d => pure (d, s)
    | none => (fun d => (d, { s with cache := s.cache.cacheQuery x d })) <$>
        (liftM ($ᵗ pr.Digest : ProbComp pr.Digest) : m pr.Digest)

/-- The SHRINCS signing oracle (Definition 4.15) over the sources `sec`, `rnd` and the stateful
secret table `sk`: the stateless path signs with `slSignM`; the stateful path takes the anchor
`leafSelect(ctr)` (`⊥` when exhausted), `R = rnd(sf, PK.seed, idx, M̃)`,
`md = H_msg^sf(R, PK.seed, PK.sf, idx, M̃)` and `FXMSS.sign`. Every queried message is logged. -/
def signStepC (sec : pr.PkSeed × SecAdrs → m pr.Y) (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y)
    (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × Bool) :
    StateT (CSt pr Msg) m (Option (Sig pr)) :=
  if q.2 then do
    let σ ← (liftM (slSignM pr Msg enc sec rnd K.pk K.pkSl K.pkSf q.1) :
      StateT (CSt pr Msg) m (Stateless.Sig pr))
    modify fun s => { s with log := s.log ++ [q.1] }
    return some (.stateless σ)
  else do
    let s ← get
    match K.S.leafSelect s.ctr with
    | none =>
      modify fun s => { s with log := s.log ++ [q.1] }
      return none
    | some v =>
      let id := v.toLeafId vp.params.hsf
      let R ← (liftM (rnd (.sf K.pk id (bmBytes pr Msg enc K.pkSl q.1))) :
        StateT (CSt pr Msg) m pr.Y)
      let md ← roStepC pr Msg (roIn pr (BMsg pr Msg) R K.pk K.pkSf id (K.pkSl, q.1))
      modify fun s => { s with ctr := s.ctr + 1, log := s.log ++ [q.1] }
      return (Scheme.Fxmss.sign pr K.S K.pk sk md id).map
        (Scheme.Shrincs.Signature.stateful id.height id.index R)

/-- The handler of the signing phase: private coins, `H_msg^sf`, and the signing oracle. -/
def implC (sec : pr.PkSeed × SecAdrs → m pr.Y) (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y)
    (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (advSpec pr Msg) (StateT (CSt pr Msg) m) :=
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CSt pr Msg) m) +
    (fun x => roStepC pr Msg x :
      QueryImpl (roSpec pr (BMsg pr Msg)) (StateT (CSt pr Msg) m))) +
  (fun q => signStepC pr Msg enc sec rnd K sk q :
    QueryImpl (Notions.ShrincsScheme.signSpec Msg (Sig pr)) (StateT (CSt pr Msg) m))

/-- **Verification** of the forgery (Algorithm 3) on the state: the stateful branch reads
`H_msg^sf` from the cache. -/
def verifyC (K : Keys pr) (msg : Msg) (σ : Sig pr) : StateT (CSt pr Msg) m Bool :=
  match σ with
  | .stateless σ' => pure (slVerify pr Msg enc K.pk K.pkSl K.pkSf msg σ')
  | .stateful z i R σt => do
    let md ← roStepC pr Msg (roIn pr (BMsg pr Msg) R K.pk K.pkSf ⟨z, i⟩ (K.pkSl, msg))
    return verifyWith pr K.pk K.pkSf ⟨z, i⟩ (some σt) md

/-- **The signing phase** of the experiment: `A₂`, then the verification of the forgery and the
freshness check `M* ∉ {Mᵢ}` (Definition 4.15). -/
def phase2C {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) (st : A.State)
    (K : Keys pr) (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y) (sk : LeafId → ℕ → pr.Y) :
    StateT (CSt pr Msg) m Bool := do
  let out ← simulateQ (implC pr Msg enc sec rnd K sk) (A.forge st K.S K.toPK)
  let ok ← verifyC pr Msg enc K out.1 out.2
  let s ← get
  return (ok && !decide (out.1 ∈ s.log))

end Handler

/-- The structure phase `A₁` against the lazily sampled random oracle `H_msg^sf`. -/
noncomputable def stage1S {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp ((Structure × A.State) × (roSpec pr (BMsg pr Msg)).QueryCache) :=
  (simulateQ (roSpec pr (BMsg pr Msg)).romImpl A.chooseShape).run ∅

/-! ## The games -/

/-- The PRF table of the stateful secrets: `PRF(PK.seed, SK.seed, ADRS)` at the `SF_WOTS_C_PRF`
address of every anchor and chain. -/
def prfTable (S : Structure) (pk : pr.PkSeed) (skSeed : pr.SkSeed) : SkIdx vp.params S → pr.Y :=
  fun i => pr.PRF pk skSeed (sfPrfAdrs i)

/-- **`GAME.0`**: the experiment of Definition 4.15 with every secret element derived by `PRF`
and every randomizer by `PRF_msg` (`SK.seed` drawn first). -/
noncomputable def game0 {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp Bool := do
  let skSeed ← $ᵗ pr.SkSeed
  let z ← stage1S pr Msg enc A
  if ¬ z.1.1.Valid vp.params.hsf then return false else do
  let pk ← $ᵗ pr.PkSeed
  let skPrf ← $ᵗ pr.SkPrf
  let sec : pr.PkSeed × SecAdrs → ProbComp pr.Y := fun x => pure (pr.PRF x.1 skSeed x.2.1)
  let rnd : PrfMsgInput pr.PkSeed pr.Y → ProbComp pr.Y := fun x => pure (pr.PRFmsg skPrf x)
  let sk := skOf pr z.1.1 (prfTable pr z.1.1 pk skSeed)
  let pkSl ← slRootM pr sec pk
  let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
  (phase2C pr Msg enc A z.1.2 K sec rnd sk).run' (CSt.init pr Msg z.2)

/-- **`GAME.1`**: every secret element is uniform: the stateful table is sampled, the stateless
secrets are a lazily sampled uniform function (Claim 4.11). -/
noncomputable def game1 {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp Bool := do
  let z ← stage1S pr Msg enc A
  if ¬ z.1.1.Valid vp.params.hsf then return false else do
  let pk ← $ᵗ pr.PkSeed
  let skPrf ← $ᵗ pr.SkPrf
  let f ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
  let sk := skOf pr z.1.1 f
  let sec : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y := lazyRO
  let rnd : PrfMsgInput pr.PkSeed pr.Y → StateT (SecCache pr) ProbComp pr.Y :=
    fun x => pure (pr.PRFmsg skPrf x)
  (do
    let pkSl ← slRootM pr sec pk
    let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
    (phase2C pr Msg enc A z.1.2 K sec rnd sk).run' (CSt.init pr Msg z.2) :
      StateT (SecCache pr) ProbComp Bool).run' ∅

/-- The monad of `GAME.2`: lazily sampled secrets over lazily sampled randomizers. -/
abbrev M2 : Type → Type := StateT (SecCache pr) (StateT (RndCache pr) ProbComp)

/-- **`GAME.2`**: additionally every randomizer is a lazily sampled uniform function of the
`PRF_msg` input, on both paths (Claim 4.12). -/
noncomputable def game2 {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp Bool := do
  let z ← stage1S pr Msg enc A
  if ¬ z.1.1.Valid vp.params.hsf then return false else do
  let pk ← $ᵗ pr.PkSeed
  let f ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
  let sk := skOf pr z.1.1 f
  let sec : pr.PkSeed × SecAdrs → M2 pr pr.Y := lazyRO
  let rnd : PrfMsgInput pr.PkSeed pr.Y → M2 pr pr.Y :=
    fun x => liftM (lazyRO x : StateT (RndCache pr) ProbComp pr.Y)
  ((do
    let pkSl ← slRootM pr sec pk
    let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
    (phase2C pr Msg enc A z.1.2 K sec rnd sk).run' (CSt.init pr Msg z.2) : M2 pr Bool).run'
      ∅).run' ∅

/-! ## The PRF reductions -/

/-- The secret-derivation function `PRF(PK.seed, SK.seed, ADRS)` as a keyed hash with key
`SK.seed` and input `(PK.seed, ADRS)` (Definitions 4.1, 4.3). -/
def prfF : Notions.KeyedHash pr.SkSeed (pr.PkSeed × Adrs) pr.Y := fun k x => pr.PRF x.1 k x.2

/-- The combined randomizer function `PRF_msg(SK.prf, ·)` as a keyed hash (Section 2.2). -/
def prfMsgF : Notions.KeyedHash pr.SkPrf (PrfMsgInput pr.PkSeed pr.Y) pr.Y := pr.PRFmsg

/-- The oracles of a distinguisher against `PRF`. -/
abbrev PrfSpec := PRFScheme.PRFOracleSpec (pr.PkSeed × Adrs) pr.Y

/-- The oracles of a distinguisher against `PRF_msg`. -/
abbrev PrfMsgSpec := PRFScheme.PRFOracleSpec (PrfMsgInput pr.PkSeed pr.Y) pr.Y

/-- **The reduction `B_prf` of Claim 4.11** (the paper's `B₁` of the hop `GAME.0 → GAME.1`): it
runs the structure phase, samples `PK.seed` and `SK.prf` itself, obtains every stateful secret
element by one oracle query at its `SF_WOTS_C_PRF` address, and answers every stateless secret
draw (at a secret-key address) by an oracle query; the rest of the experiment it simulates
honestly. -/
noncomputable def Bprf {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    OracleComp (PrfSpec pr) Bool := do
  let z ← (liftM (stage1S pr Msg enc A) : OracleComp (PrfSpec pr) _)
  if ¬ z.1.1.Valid vp.params.hsf then return false else do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (PrfSpec pr) _)
  let skPrf ← (liftM ($ᵗ pr.SkPrf : ProbComp pr.SkPrf) : OracleComp (PrfSpec pr) _)
  let f ← tableM (fun i : SkIdx vp.params z.1.1 =>
    (PRFScheme.functionQuery (pk, sfPrfAdrs i) : OracleComp (PrfSpec pr) pr.Y))
  let sk := skOf pr z.1.1 f
  let sec : pr.PkSeed × SecAdrs → OracleComp (PrfSpec pr) pr.Y :=
    fun x => PRFScheme.functionQuery (x.1, x.2.1)
  let rnd : PrfMsgInput pr.PkSeed pr.Y → OracleComp (PrfSpec pr) pr.Y :=
    fun x => pure (pr.PRFmsg skPrf x)
  let pkSl ← slRootM pr sec pk
  let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
  (phase2C pr Msg enc A z.1.2 K sec rnd sk).run' (CSt.init pr Msg z.2)

/-- **The reduction `B_prfmsg` of Claim 4.12** (the paper's `B₂`): it samples the secret elements
of `GAME.1` itself (the stateful table, and the stateless secrets lazily) and answers every
`PRF_msg` call, on either path, by an oracle query. -/
noncomputable def Bprfmsg {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    OracleComp (PrfMsgSpec pr) Bool := do
  let z ← (liftM (stage1S pr Msg enc A) : OracleComp (PrfMsgSpec pr) _)
  if ¬ z.1.1.Valid vp.params.hsf then return false else do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (PrfMsgSpec pr) _)
  let f ← (liftM ($ᵗ (SkIdx vp.params z.1.1 → pr.Y) : ProbComp _) : OracleComp (PrfMsgSpec pr) _)
  let sk := skOf pr z.1.1 f
  let sec : pr.PkSeed × SecAdrs → StateT (SecCache pr) (OracleComp (PrfMsgSpec pr)) pr.Y := lazyRO
  let rnd : PrfMsgInput pr.PkSeed pr.Y → StateT (SecCache pr) (OracleComp (PrfMsgSpec pr)) pr.Y :=
    fun x => liftM (PRFScheme.functionQuery x : OracleComp (PrfMsgSpec pr) pr.Y)
  (do
    let pkSl ← slRootM pr sec pk
    let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
    (phase2C pr Msg enc A z.1.2 K sec rnd sk).run' (CSt.init pr Msg z.2) :
      StateT (SecCache pr) (OracleComp (PrfMsgSpec pr)) Bool).run' ∅

end ShrincsSecurity.Shrincs

end
