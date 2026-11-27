module

public import ShrincsSecurity.Shrincs.Games

/-!
# The augmented games: the FXMSS games of Section 4.7 extended by the stateless path

`SHRINCS-Security-Analysis.pdf`, Section 4.8, hops `GAME.2 → GAME.5` (txt lines 4010–4260):
"The games of Section 4.7 have no stateless path, so we extend them. For `k ∈ {2, …, 9}` let
`F.k⁺` be the game `F.k` of Section 4.7 for the structure `Π`, extended by the stateless path"
and "the augmented reductions … additionally sample the stateless secret elements uniformly at
random … and answer stateless signing queries".

## The FXMSS forger `A_F` of a SHRINCS forger

Section 4.8 identifies `GAME.4`, restricted to the stateful branch, with `F.2⁺` "played by the
forger `A_F` that runs `A`, forms `M̃` from the context, `PK.sl` and the message of each stateful
query, and names the leaves in the signer's order". `forgeExt` is that forger, made explicit: it
receives `(PK.seed, ·, PK.sf)` from the FXMSS challenger, samples the stateless secrets itself
(lazily, uniform: `GAME.1`), computes `PK.sl`, and runs `A` on `(PK.seed, PK.sl, PK.sf)`
(`implAF`):

* a stateless signing query is answered by `A_F` itself, with lazily sampled uniform
  randomizers cached per `PRF_msg^sl` input (`GAME.2`);
* a stateful signing query at counter `ctr` becomes the FXMSS signing query on the bound message
  `(PK.sl, m)` at the leaf `leafSelect(ctr)` (`⊥` when exhausted);
* queries to `H_msg^sf` are forwarded.

The forgery of `A` becomes the FXMSS forgery `((PK.sl, M*), (z*, i*), (R*, σ*))` when it is on the
stateful branch, and a dummy that never verifies otherwise; the extra output `Ext` records the
branch, freshness with respect to **both** paths, and the stateless verification.

`A_F`'s `PK.sl` replaces the FXMSS challenger's: the FXMSS games of Section 4.7 draw `PK.sl` by an
arbitrary procedure `slKeygen` that the proof never inspects; here `slKeygenS` returns a constant,
and `A_F` computes the genuine `PK.sl` from its own uniform stateless secrets.

## The augmented games

`progS` is the signing phase `stage2Prog` of Section 4.7 run with `A_F`, keeping `Ext`.
With it, `gameS implG` is `F.0⁺ = GAME.2` (the honest random oracle, uniform secrets and
randomizers), `gameS implG2` is `GAME.4` lazily (fresh programmed digests), and `gameHybS` is
`GAME.4 = F.2⁺` with presampled digests (Remark 4.7). Their events:

* `Wsf`: the structure is valid, the forgery is on the stateful branch, fresh for both paths, and
  `A_F` wins FXMSS (it verifies under `PK.sf` and `(PK.sl, M*)` was never an FXMSS query);
* `Wsl`: the structure is valid, the forgery is on the stateless branch, fresh for both paths, and
  verifies under `(PK.seed, PK.sl)`.

## The augmented distinguisher `B₁⁺` (Claim 4.14)

`B1Srun` is the distinguisher `B₁` of Algorithm 5 (`Claim42.implB`) run on `progS`, with output
the success event of `GAME.3`, `(Wsf ∧ ¬C₁) ∨ Wsl`: the stateless path is simulated inside `A_F`
and evaluates no `H_msg^sf`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte)
open Fxmss.Rom (roIn verifyWith pkSfOf skOf SkIdx Keys roSpec RoIn St Transcript completion
  otherMsg anchorList implG implG2 implHyb Setup hon digOf betaOf fullSpec)
open ShrincsSecurity.Scheme.Structure (leafIds)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)

/-- `A_F`'s extra output: the branch of the forgery, its freshness with respect to the signing
queries of both paths, and the stateless verification. -/
structure Ext where
  /-- The forgery is on the stateless branch. -/
  sl : Bool
  /-- `M*` was not queried on either path. -/
  fresh : Bool
  /-- The stateless verification accepts (`false` on the stateful branch). -/
  slOk : Bool

/-- `A_F`'s state: the counter, the queried messages of both paths, and the caches of the
stateless secrets and randomizers. -/
structure AFSt where
  /-- The stateful counter `ctr`. -/
  ctr : ℕ
  /-- The queried messages of both paths. -/
  log : List Msg
  /-- The lazily sampled stateless secrets. -/
  sec : SecCache pr
  /-- The lazily sampled randomizers. -/
  rnd : RndCache pr

variable [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

/-- The FXMSS messages of `A_F`, the bound messages `(PK.sl, m)`. -/
abbrev FSpec := fullSpec pr (BMsg pr Msg)

/-- The stateless signer with lazily sampled secrets and randomizers (`GAME.2`), on the caches. -/
noncomputable def slStepP (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (sc : SecCache pr)
    (rc : RndCache pr) : ProbComp ((Stateless.Sig pr × SecCache pr) × RndCache pr) :=
  ((slSignM pr Msg enc (lazyRO : pr.PkSeed × SecAdrs → M2 pr pr.Y)
    (fun x => liftM (lazyRO x : StateT (RndCache pr) ProbComp pr.Y)) pk pkSl pkSf msg).run
      sc).run rc

/-- The stateless key generation with lazily sampled secrets (`GAME.1`), from the cache `sc`. -/
noncomputable def slRootP (pk : pr.PkSeed) (sc : SecCache pr) : ProbComp (pr.Y × SecCache pr) :=
  (slRootM pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk).run sc

/-- `A_F`'s answer to a signing query of `A` (keys `K` with `A_F`'s own `PK.sl`). -/
noncomputable def signAF (K : Keys pr) (q : Msg × Bool) :
    StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)) (Option (Sig pr)) := do
  let s ← get
  if q.2 then
    let r ← (liftM (slStepP pr Msg enc K.pk K.pkSl K.pkSf q.1 s.sec s.rnd) :
      StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)) _)
    set { s with sec := r.1.2, rnd := r.2, log := s.log ++ [q.1] }
    return some (.stateless r.1.1)
  else
    match K.S.leafSelect s.ctr with
    | none =>
      set { s with log := s.log ++ [q.1] }
      return none
    | some v =>
      let id := v.toLeafId vp.params.hsf
      let a ← (liftM ((FSpec pr Msg).query (.inr ((K.pkSl, q.1), id))) :
        StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)) (Option (Fxmss.Rom.Sig pr)))
      set { s with ctr := s.ctr + 1, log := s.log ++ [q.1] }
      return a.bind fun a => a.2.map (Scheme.Shrincs.Signature.stateful id.height id.index a.1)

/-- `A_F`'s handler for `A`'s oracles: coins and `H_msg^sf` forwarded, signing by `signAF`. -/
noncomputable def implAF (K : Keys pr) :
    QueryImpl (advSpec pr Msg) (StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg))) :=
  ((fun n => liftM ((FSpec pr Msg).query (.inl (.inl n))) :
      QueryImpl unifSpec (StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)))) +
    (fun x => liftM ((FSpec pr Msg).query (.inl (.inr x))) :
      QueryImpl (roSpec pr (BMsg pr Msg)) (StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg))))) +
  (fun q => signAF pr Msg enc K q :
    QueryImpl (Notions.ShrincsScheme.signSpec Msg (Sig pr))
      (StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg))))

/-- The FXMSS forgery of `A_F` for `A`'s forgery `(M*, σ*)`: the stateful branch's forgery on the
bound message, or a dummy that never verifies (`σ_tree = ⊥`). -/
def outOf (K : Keys pr) (msg : Msg) : Sig pr → BMsg pr Msg × LeafId × Fxmss.Rom.Sig pr
  | .stateful z i R σt => ((K.pkSl, msg), ⟨z, i⟩, (R, some σt))
  | .stateless _ => ((K.pkSl, msg), ⟨0, 0⟩, (default, none))

/-- `A_F`'s extra output for `A`'s forgery. -/
def extOf (K : Keys pr) (msg : Msg) (fresh : Bool) : Sig pr → Ext
  | .stateful _ _ _ _ => ⟨false, fresh, false⟩
  | .stateless σ' => ⟨true, fresh, slVerify pr Msg enc K.pk K.pkSl K.pkSf msg σ'⟩

/-- **The forger `A_F`** with its extra output: on `(PK.seed, ·, PK.sf)` and the structure `S`,
stateless key generation with its own uniform secrets, then `A` through `implAF`. -/
noncomputable def forgeExt {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (S : Structure) (pk' : Fxmss.Rom.PK pr) :
    OracleComp (FSpec pr Msg) ((BMsg pr Msg × LeafId × Fxmss.Rom.Sig pr) × Ext) := do
  let r ← (liftM (slRootP pr pk'.1 ∅) : OracleComp (FSpec pr Msg) _)
  let K : Keys pr := ⟨S, pk'.1, r.1, pk'.2.2⟩
  let o ← (simulateQ (implAF pr Msg enc K) (A.forge st S K.toPK)).run ⟨0, [], r.2, ∅⟩
  let fresh := !decide (o.1.1 ∈ o.2.log)
  return (outOf pr Msg K o.1.1 o.1.2, extOf pr Msg enc K o.1.1 fresh o.1.2)

/-- `PK.sl` of the FXMSS games (`slKeygen` of Section 4.7): a constant; `A_F` uses its own. -/
def slKeygenS : pr.PkSeed → ProbComp pr.Y := fun _ => pure default

/-- **The augmented signing phase** (`stage2Prog` of Section 4.7 with `A_F`): `A_F`, the
verification query of its forgery, and the completion of Remark 4.6; keeps `Ext`. -/
noncomputable def progS [Nontrivial Msg] {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) (st : A.State) (K : Keys pr) :
    OracleComp (FSpec pr Msg) ((BMsg pr Msg × LeafId × Fxmss.Rom.Sig pr × pr.Digest) × Ext) := do
  let out ← forgeExt pr Msg enc A st K.S K.toPK
  let yf ← ((FSpec pr Msg).query
    (.inl (.inr (roIn pr (BMsg pr Msg) out.1.2.2.1 K.pk K.pkSf out.1.2.1 out.1.1))) :
      OracleComp (FSpec pr Msg) pr.Digest)
  completion pr (BMsg pr Msg) (otherMsg (BMsg pr Msg) out.1.1) (anchorList vp.params K.S)
  return ((out.1.1, out.1.2.1, out.1.2.2, yf), out.2)

/-! ## The augmented games -/

variable [Nontrivial Msg]

/-- The signing phase of `GAME.2`/`GAME.4` (lazy) in the form of Section 4.7 (`stageG`), with
`progS`. -/
noncomputable def stageGS {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (mode : Keys pr → (LeafId → ℕ → pr.Y) →
      QueryImpl (FSpec pr Msg) (StateT (St pr (BMsg pr Msg)) ProbComp))
    (pk : pr.PkSeed) (z : (Structure × A.State) × (roSpec pr (BMsg pr Msg)).QueryCache) :
    ProbComp (Option (Transcript pr (BMsg pr Msg) × Ext)) :=
  if ¬ z.1.1.TreeValid vp.params.hsf then pure none else do
    let f ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
    let pkSl ← slKeygenS pr pk
    let sk := skOf pr z.1.1 f
    let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
    let r ← (simulateQ (mode K sk) (progS pr Msg enc A z.1.2 K)).run
      (St.init pr (BMsg pr Msg) z.2)
    return some (Transcript.ofRun pr (BMsg pr Msg) K (r.1.1, r.2), r.1.2)

/-- **`GAME.2` in the form of Section 4.7** (`mode = implG`, the honest random oracle) and
**`GAME.4`, lazily** (`mode = implG2`, fresh programmed digests): `PK.seed` first, `A₁`, then
the augmented signing phase. -/
noncomputable def gameS {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (mode : Keys pr → (LeafId → ℕ → pr.Y) →
      QueryImpl (FSpec pr Msg) (StateT (St pr (BMsg pr Msg)) ProbComp)) :
    ProbComp (Option (Transcript pr (BMsg pr Msg) × Ext)) := do
  let pk ← $ᵗ pr.PkSeed
  let z ← stage1S pr Msg enc A
  stageGS pr Msg enc A mode pk z

variable [Inhabited pr.Digest]

/-- The setup of `GAME.4` with presampled digests (`setupHyb` of Section 4.7 for `A_F`). -/
noncomputable def setupHybS {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp (Setup pr (BMsg pr Msg) A.State) := do
  let z ← stage1S pr Msg enc A
  let ys ← $ᵗ (Fxmss.Rom.Anchor vp.params z.1.1 → pr.Digest)
  let u ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
  return ⟨z.1.1, z.1.2, z.2, ys, u⟩

/-- The signing phase of `GAME.4` with presampled digests (`stageHyb` with `progS`). -/
noncomputable def stageHybS {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr (BMsg pr Msg) A.State) (pk : pr.PkSeed) :
    ProbComp (Option ((Transcript pr (BMsg pr Msg) × Ext) × Fxmss.Rom.Honest pr)) :=
  if ¬ d.S.TreeValid vp.params.hsf then pure none else do
    let pkSl ← slKeygenS pr pk
    let H := hon pr d.S pk (digOf pr d.ys) β
    let K : Keys pr := ⟨d.S, pk, pkSl, H.pkSf⟩
    let r ← (simulateQ (implHyb pr (BMsg pr Msg) K H) (progS pr Msg enc A d.st K)).run
      (St.init pr (BMsg pr Msg) d.cache)
    return some ((Transcript.ofRun pr (BMsg pr Msg) K (r.1.1, r.2), r.1.2), H)

/-- **`GAME.4` (= `GAME.5` for stateless-branch forgeries)**, with presampled digests: the game
`F.2⁺` of Section 4.8, i.e. `F.2` of Section 4.7 for `A_F` extended by the stateless path. -/
noncomputable def gameHybS {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp (Option ((Transcript pr (BMsg pr Msg) × Ext) × Fxmss.Rom.Honest pr)) := do
  let pk ← $ᵗ pr.PkSeed
  let d ← setupHybS pr Msg enc A
  stageHybS pr Msg enc A (betaOf pr 0 pk d.u) d pk

/-! ## Events -/

variable {pr Msg}

/-- **`W_sf`**: a valid structure, a fresh forgery on the stateful branch, and `A_F` wins FXMSS. -/
def Wsf (p : Transcript pr (BMsg pr Msg) × Ext) : Prop :=
  p.1.K.S.Valid vp.params.hsf ∧ p.2.sl = false ∧ p.2.fresh = true ∧ p.1.Win

/-- **`W_sl`**: a valid structure and a fresh forgery that verifies on the stateless branch. -/
def Wsl (p : Transcript pr (BMsg pr Msg) × Ext) : Prop :=
  p.1.K.S.Valid vp.params.hsf ∧ p.2.sl = true ∧ p.2.fresh = true ∧ p.2.slOk = true

/-- An event of an augmented game's outcome (`⊥` satisfies none). -/
def OEv (E : Transcript pr (BMsg pr Msg) × Ext → Prop) :
    Option (Transcript pr (BMsg pr Msg) × Ext) → Prop
  | some p => E p
  | none => False

/-- An event of `GAME.4`'s outcome, ignoring the honest data. -/
def HEv (E : Transcript pr (BMsg pr Msg) × Ext → Prop) :
    Option ((Transcript pr (BMsg pr Msg) × Ext) × Fxmss.Rom.Honest pr) → Prop
  | some p => E p.1
  | none => False

/-- **The success event of `GAME.2`**: a forgery on either branch. -/
def WinS (p : Transcript pr (BMsg pr Msg) × Ext) : Prop := Wsf p ∨ Wsl p

/-- **The success event of `GAME.3`** (and `GAME.4`): `(W_sf ∧ ¬C₁) ∨ W_sl`, the abort of
`GAME.3` concerning the stateful branch only. -/
def WinNotC1S (p : Transcript pr (BMsg pr Msg) × Ext) : Prop := (Wsf p ∧ ¬ p.1.C1) ∨ Wsl p

/-! ## The augmented distinguisher `B₁⁺` -/

variable (pr Msg)

/-- `B₁⁺` after the structure phase: Algorithm 5 (`Claim42.implB`) on `progS`, with output the
success event of `GAME.3`. -/
noncomputable def B1Scont {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (pk : pr.PkSeed) (z : Structure × A.State) :
    OracleComp (Fxmss.Rom.Claim42.DSpec pr (BMsg pr Msg)) Bool :=
  if ¬ z.1.TreeValid vp.params.hsf then return false else do
  let f ← (liftM ($ᵗ (SkIdx vp.params z.1 → pr.Y) : ProbComp _) :
    OracleComp (Fxmss.Rom.Claim42.DSpec pr (BMsg pr Msg)) _)
  let pkSl ← (liftM (slKeygenS pr pk) : OracleComp (Fxmss.Rom.Claim42.DSpec pr (BMsg pr Msg)) pr.Y)
  let sk := skOf pr z.1 f
  let K : Keys pr := ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk sk⟩
  let r ← (simulateQ (Fxmss.Rom.Claim42.implB pr (BMsg pr Msg) K sk)
    (progS pr Msg enc A z.2 K)).run (St.init pr (BMsg pr Msg) ∅)
  return decide (WinNotC1S (Transcript.ofRun pr (BMsg pr Msg) K (r.1.1, r.2), r.1.2))

/-- **The augmented distinguisher `B₁⁺` of Claim 4.14** against `DI-Repro` for `H_msg^sf`:
`PK.seed ←$`, the structure phase with its queries forwarded to `O_b`, then `B1Scont`. -/
noncomputable def B1Srun {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    OracleComp (Fxmss.Rom.Claim42.DSpec pr (BMsg pr Msg)) Bool := do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) :
    OracleComp (Fxmss.Rom.Claim42.DSpec pr (BMsg pr Msg)) pr.PkSeed)
  let z ← simulateQ (Fxmss.Rom.Claim42.fwd pr (BMsg pr Msg)) A.chooseShape
  B1Scont pr Msg enc A pk z

end ShrincsSecurity.Shrincs

end
