module

public import ShrincsSecurity.Fxmss.Theorem42
public import ShrincsSecurity.Scheme.Shrincs
public import HashSig.SLHDSA.SecretProvider

/-!
# SHRINCS in the random-oracle model: the scheme of Theorem 4.1

`SHRINCS-Security-Analysis.pdf`, **Definition 4.15** (SHRINCS EU-CMA), **Theorem 4.1** (txt lines
2874–2948) and the model of Section 4.8 (txt lines 3940–3950).

This file instantiates the interface `Notions.ShrincsScheme` of Definition 4.15 with the scheme
model of `ShrincsSecurity.Scheme` (Algorithms 1–3), in the setting of Theorem 4.1:

* **`H_msg^sf` is a random oracle**, exactly as in Theorem 4.2 (`Fxmss/Model.lean`): the oracle
  `roSpec` with input `(R, (PK.seed, PK.sf, idx, M̃))`.
* **Every other named function is a fixed function of the primitive bundle `pr`**: the collection
  `Th_λ` (with `H_grind`), `PRF`, `PRF_msg` and `H_msg^sl`. This is the reading of Assumption 4.1
  used by the formalisation of Theorem 4.2 for `Th_λ`: the functions are distinct and independent
  of the random oracle by construction, the collection is attacked through standard-model
  (collection) games, and the two PRFs through Definition 4.3. `H_msg^sl` is treated like `Th_λ`:
  a public function, whose security enters only through the quoted stateless bound (Claim 4.16,
  `StatelessBound`). The reductions evaluate it directly; time is not modelled (as for Theorem
  4.2), so Lemma 4.2, which only removes these evaluations from the time accounting, has nothing
  to discharge.

## Messages

Definition 4.15 signs pairs `(ctx, M)`. The model fixes a **finite** message type `Msg` with an
encoding `MsgEnc` into such pairs (contexts of at most 255 bytes, as Algorithm 2 requires). The
random oracle needs a finite input space (`X₂` of Definition C.2), hence the finite type. The
stateful path binds the **bound message** `M̃ = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ PK.sl ‖ M`; its
random-oracle input is the structured value `(PK.sl, m) : BMsg`, which determines `M̃` and is
determined by it (`Scheme.Shrincs.boundMessage_injective`), and `PRF_msg^sf` receives the byte
string `M̃` itself (`bmBytes`). The stateless path signs `PK.sf ‖ M` under `ctx` with SLH-DSA
(FIPS 205 pure mode; `slMsg` is the encoded `M'`).

## The scheme (`scheme`)

* `keygen Π`: `SK.seed, SK.prf, PK.seed ←$`; `PK.sl` is the hypertree root, `PK.sf` the FXMSS
  root of the PRF-derived WOTS+C secrets (Algorithm 1); the counter starts at `0`.
* `signSF`: the anchor `leafSelect(ctr)` (or `⊥` when exhausted), `R = PRF_msg^sf(…, M̃)`,
  `md = H_msg^sf(R, PK.seed, PK.sf, idx, M̃)` from the random oracle, `FXMSS.sign` (Algorithm 2,
  stateful branch; a failed counter search is `⊥`).
* `signSL`: `opt_rand ←$` (hedged mode), and the FIPS 205 signer (Algorithm 2, stateless branch).
* `verify`: Algorithm 3, dispatching on the indicator byte (the constructor of
  `Scheme.Shrincs.Signature`); the stateful branch queries the random oracle.

## Secret providers

The proof replaces the PRF-derived secrets by uniform ones (Claim 4.11). The stateless signer is
therefore also written over a *secret provider* (`slSignM`, `slRootM`): VCVio's
`signInternalWithSecretRandomizerM` / `keygenInternalWithSecretM`, with the public hashes answered
by `pr` (`pubQ`) and the secrets drawn from a monadic source at **secret-key addresses**
(`Adrs.IsSecretKey`, types `WOTS_PRF` and `FORS_PRF`) only (`guardSec`; the programs read secrets
only there). The randomizer `R` is drawn from a monadic source of `PRF_msg` values.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte)
open Fxmss.Rom (roIn verifyWith pkSfOf skOf SkIdx Keys)

deriving instance DecidableEq for Scheme.PrfMsgInput

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-! ## Messages -/

/-- A finite message space with its encoding into the pairs `(ctx, M)` of Definition 4.15. -/
structure MsgEnc (Msg : Type) where
  /-- The context string `ctx`. -/
  ctx : Msg → List Byte
  /-- The message `M`. -/
  body : Msg → List Byte
  /-- Contexts have at most 255 bytes (Algorithm 2). -/
  ctx_le : ∀ m, (ctx m).length ≤ 255

variable (Msg : Type) (enc : MsgEnc Msg)

/-- The structured bound message `(PK.sl, m)`, the message of the stateful path. -/
abbrev BMsg : Type := pr.Y × Msg

/-- The ambient oracles: private coins and the random oracle `H_msg^sf`. -/
abbrev spec := Fxmss.Rom.spec pr (BMsg pr Msg)

/-- The byte string `M̃ = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ PK.sl ‖ M` (input of `PRF_msg^sf`). -/
def bmBytes (pkSl : pr.Y) (m : Msg) : List Byte :=
  Scheme.Shrincs.boundMessage pr (enc.ctx m) pkSl (enc.body m)

/-- The FIPS 205 encoded message `M' = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ (PK.sf ‖ M)` of the stateless
path (pure mode). -/
def slMsg (pkSf : pr.Y) (m : Msg) : List Byte :=
  [0, UInt8.ofNat (enc.ctx m).length] ++ enc.ctx m ++
    Scheme.Shrincs.statelessMessage pr pkSf (enc.body m)

/-! ## The stateless path over a secret provider -/

/-- Secret-key addresses (types `WOTS_PRF`, `FORS_PRF`): the only addresses at which the stateless
programs read a secret. -/
abbrev SecAdrs : Type := {a : Adrs // a.IsSecretKey}

/-- The public hashes of the stateless path, answered by the functions of `pr`. -/
@[instance_reducible] def pubQ (m : Type → Type) [Monad m] : HasQuery (SLHDSA.publicHashSpec pr.toSLHDSA.core) m :=
  ⟨fun q => pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)⟩

/-- A secret provider at `PK.seed = pk` that draws secrets at secret-key addresses only. -/
def guardSec {m : Type → Type} [Monad m] [Inhabited pr.Y] (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (pk : pr.PkSeed) (a : Adrs) : m pr.Y :=
  if h : a.IsSecretKey then sec (pk, ⟨a, h⟩) else pure default

/-- **Stateless key generation** over a secret provider: `PK.sl`, the top-layer root of the
hypertree (Algorithm 1, line 3). -/
def slRootM {m : Type → Type} [Monad m] [Inhabited pr.Y] (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (pk : pr.PkSeed) : m pr.Y :=
  letI := pubQ pr m
  SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core (guardSec pr sec pk) pk

/-- **Stateless signing** over a secret provider and a randomizer source (Algorithm 2, stateless
branch): `opt_rand ←$`, `R = PRF_msg^sl(SK.prf, opt_rand, M')`, and the FIPS 205 internal signer
on `M'`. -/
def slSignM {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] [Inhabited pr.Y]
    [SampleableType pr.Y] (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y) (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) :
    m (Stateless.Sig pr) := do
  let optRand ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : m pr.Y)
  let R ← rnd (.sl optRand (slMsg pr Msg enc pkSf msg))
  letI := pubQ pr m
  SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core (guardSec pr sec pk)
    (slMsg pr Msg enc pkSf msg) pk pkSl R

/-- **Stateless verification** (Algorithm 3, stateless branch): `slh.verify(PK.sf ‖ M, σ, ctx,
PK.seed, PK.sl)`. -/
def slVerify [DecidableEq pr.Y] (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg)
    (σ : Stateless.Sig pr) : Bool :=
  Stateless.verify pr (Scheme.Shrincs.statelessMessage pr pkSf (enc.body msg)) (enc.ctx msg) σ pk
    pkSl

/-! ## The scheme of Definition 4.15 -/

/-- The SHRINCS public key `(PK.seed, PK.sl, PK.sf)`. -/
abbrev PK : Type := pr.PkSeed × pr.Y × pr.Y

/-- The SHRINCS secret key: seeds, public values and the committed structure. -/
structure SK where
  /-- The structure. -/
  S : Structure
  /-- `SK.seed`. -/
  skSeed : pr.SkSeed
  /-- `SK.prf`. -/
  skPrf : pr.SkPrf
  /-- `PK.seed`. -/
  pk : pr.PkSeed
  /-- `PK.sl`. -/
  pkSl : pr.Y
  /-- `PK.sf`. -/
  pkSf : pr.Y

/-- The SHRINCS signature (Section 3). -/
abbrev Sig : Type := Scheme.Shrincs.Signature pr

variable [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

set_option synthInstance.maxSize 1024 in
/-- Decidable equality of the random-oracle inputs (instance search exceeds the default size
bound on the nested product). -/
instance instDecidableEqRoIn : DecidableEq (Fxmss.Rom.RoIn pr (BMsg pr Msg)) := inferInstance

/-- The PRF-derived WOTS+C secrets `sk_{(z,i),ch} = PRF(PK.seed, SK.seed, ADRS)` (Section 2.4). -/
def SK.wots (k : SK pr) : LeafId → ℕ → pr.Y := Scheme.Fxmss.prfSecret pr k.pk k.skSeed k.S

/-- **Algorithm 1** (`SHRINCS.KeyGen`) for a structure: `SK.seed, SK.prf, PK.seed ←$`, the
stateless root `PK.sl` and the FXMSS root `PK.sf`; the counter starts at `0`. -/
noncomputable def keygen (S : Structure) : OracleComp (spec pr Msg) (PK pr × SK pr × ℕ) := do
  let skSeed ← (liftM ($ᵗ pr.SkSeed : ProbComp pr.SkSeed) : OracleComp (spec pr Msg) _)
  let skPrf ← (liftM ($ᵗ pr.SkPrf : ProbComp pr.SkPrf) : OracleComp (spec pr Msg) _)
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (spec pr Msg) _)
  let pkSl := Stateless.root pr skSeed pk
  let pkSf := pkSfOf pr S pk (Scheme.Fxmss.prfSecret pr pk skSeed S)
  return ((pk, pkSl, pkSf), ⟨S, skSeed, skPrf, pk, pkSl, pkSf⟩, 0)

/-- **Stateful signing** (Algorithm 2, stateful branch): the anchor `leafSelect(ctr)`, or `⊥` when
the stateful keys are exhausted. -/
noncomputable def signSF (k : SK pr) (ctr : ℕ) (msg : Msg) :
    OracleComp (spec pr Msg) (Option (Sig pr) × ℕ) :=
  match k.S.leafSelect ctr with
  | none => pure (none, ctr)
  | some v => do
    let id := v.toLeafId vp.params.hsf
    let R := pr.PRFmsgSf k.skPrf k.pk id (bmBytes pr Msg enc k.pkSl msg)
    let md ← ((spec pr Msg).query (.inr (roIn pr (BMsg pr Msg) R k.pk k.pkSf id (k.pkSl, msg))) :
      OracleComp (spec pr Msg) pr.Digest)
    return ((Scheme.Fxmss.sign pr k.S k.pk k.wots md id).map
      (Scheme.Shrincs.Signature.stateful id.height id.index R), ctr + 1)

/-- The stateless signature of Algorithm 2 for `opt_rand` (FIPS 205, Algorithms 19 and 22). -/
def slSign (k : SK pr) (optRand : pr.Y) (msg : Msg) : Stateless.Sig pr :=
  SLHDSA.GeneralScheme.signInternal vp.sl pr.toSLHDSA (slMsg pr Msg enc k.pkSf msg)
    (Stateless.secretKey pr k.skSeed k.skPrf k.pk k.pkSl) optRand

/-- **Stateless signing** (Algorithm 2, stateless branch), hedged: `opt_rand ←$`. -/
noncomputable def signSL (k : SK pr) (msg : Msg) : OracleComp (spec pr Msg) (Sig pr) := do
  let optRand ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : OracleComp (spec pr Msg) pr.Y)
  return .stateless (slSign pr Msg enc k optRand msg)

/-- **Verification** (Algorithm 3). -/
noncomputable def verify (pk : PK pr) (msg : Msg) (σ : Sig pr) : OracleComp (spec pr Msg) Bool :=
  match σ with
  | .stateless σ' => pure (slVerify pr Msg enc pk.1 pk.2.1 pk.2.2 msg σ')
  | .stateful z i R σt => do
    let md ← ((spec pr Msg).query
      (.inr (roIn pr (BMsg pr Msg) R pk.1 pk.2.2 ⟨z, i⟩ (pk.2.1, msg))) :
        OracleComp (spec pr Msg) pr.Digest)
    return verifyWith pr pk.1 pk.2.2 ⟨z, i⟩ (some σt) md

/-- **SHRINCS** as the scheme of Definition 4.15: shapes are structures, valid when they form a
valid structure with an admissible leaf selection (Section 2.5, footnote 6). -/
noncomputable def scheme :
    Notions.ShrincsScheme (spec pr Msg) Structure Msg (PK pr) (SK pr) ℕ (Sig pr) where
  ValidShape S := S.Valid vp.params.hsf
  decValidShape := Classical.decPred _
  keygen := keygen pr Msg
  signSF := signSF pr Msg enc
  signSL := signSL pr Msg enc
  verify := verify pr Msg enc

/-- The random-oracle-model runtime: `H_msg^sf` is a lazily sampled random oracle. -/
noncomputable abbrev runtime : ProbCompRuntime (OracleComp (spec pr Msg)) :=
  ProbCompRuntime.rom (Fxmss.Rom.roSpec pr (BMsg pr Msg))

/-- A query to `H_msg^sf` in the signing phase of a SHRINCS forger. -/
def IsRoQueryS : (ℕ ⊕ Fxmss.Rom.RoIn pr (BMsg pr Msg)) ⊕ (Msg × Bool) → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred (IsRoQueryS pr Msg) := fun x => by
  rcases x with (_ | _) | _ <;> simp only [IsRoQueryS] <;> infer_instance

/-- **The forgers of Theorem 4.1**: SHRINCS EU-CMA adversaries (Definition 4.15) with at most
`q_s` signing queries, at most `q_{h,1}` and `q_{h,2}` queries to `H_msg^sf` in the two stages
(`q_h = q_{h,1} + q_{h,2}`), committing to structures with at most `L` anchors. -/
structure Forger (qs qh₁ qh₂ L : ℕ) extends Notions.ShrincsAdversary (scheme pr Msg enc) qs where
  /-- At most `q_{h,1}` random-oracle queries in the structure phase. -/
  roBound₁ : chooseShape.IsQueryBoundP (Fxmss.Rom.IsRoQuery pr (BMsg pr Msg)) qh₁
  /-- At most `q_{h,2}` random-oracle queries in the signing phase. -/
  roBound₂ : ∀ st S pk, (forge st S pk).IsQueryBoundP (IsRoQueryS pr Msg) qh₂
  /-- Every committed structure that forms a tree has at most `L` anchors. -/
  anchors_le : ∀ z ∈ support chooseShape, z.1.TreeValid vp.params.hsf → z.1.anchors.card ≤ L

/-- `Succ^{SHRINCS-EU-CMA}_{SHRINCS,q_s}(A)` in the random-oracle model (Definition 4.15). -/
noncomputable abbrev succ {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) : ℝ≥0∞ :=
  (scheme pr Msg enc).succ (runtime pr Msg) A

/-! ## Correspondence with `Scheme.Shrincs` (Algorithms 1–3) -/

section SchemeBridge

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- Convert a model secret key to a `Scheme.Shrincs.SecretKey`. -/
def SK.toSchemeSK (k : SK pr) : Scheme.Shrincs.SecretKey pr :=
  ⟨k.skSeed, k.skPrf, k.pk, k.pkSl, k.S, k.pkSf⟩

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- Convert a model public key to a `Scheme.Shrincs.PublicKey`. -/
def PK.toSchemePK (pk : PK pr) : Scheme.Shrincs.PublicKey pr :=
  ⟨pk.1, pk.2.1, pk.2.2⟩

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- Algorithm 1 (`Scheme.Shrincs.keygen`) on a valid structure produces the exact `(SK, PK)` of
`Shrincs.Model.keygen`. -/
theorem keygen_eq_scheme {S : Structure} (hS : S.TreeValid vp.params.hsf) (skSeed : pr.SkSeed)
    (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) :
    let pkSl := Stateless.root pr skSeed pkSeed
    let pkSf := pkSfOf pr S pkSeed (Scheme.Fxmss.prfSecret pr pkSeed skSeed S)
    Scheme.Shrincs.keygen pr S skSeed skPrf pkSeed =
      some (SK.toSchemeSK pr ⟨S, skSeed, skPrf, pkSeed, pkSl, pkSf⟩,
        PK.toSchemePK pr (pkSeed, pkSl, pkSf)) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    (Scheme.Fxmss.root_isSome hS pkSeed (Scheme.Fxmss.prfSecret pr pkSeed skSeed S))
  simp [Scheme.Shrincs.keygen, pkSfOf, hr, SK.toSchemeSK, PK.toSchemePK]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- The model's stateless signer (`slSign`) equals the stateless branch of Algorithm 2
(`Scheme.Shrincs.sign` at state `⊥`). -/
theorem slSign_eq_scheme_sign (k : SK pr) (optRand : pr.Y) (msg : Msg) :
    (Scheme.Shrincs.sign pr (enc.body msg) (enc.ctx msg) (k.toSchemeSK pr) none optRand).1 =
      some (.stateless (slSign pr Msg enc k optRand msg)) := by
  simp only [Scheme.Shrincs.sign, enc.ctx_le msg, ↓reduceIte, Option.bind_none,
    Stateless.sign, SLHDSA.External.signPureWithRandomizer,
    SLHDSA.External.encodePureMessage_eq_ok _ _ (enc.ctx_le msg)]
  rfl

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- The model's stateless verifier (`slVerify`) is definitionally the stateless branch of
Algorithm 3 (`Scheme.Shrincs.verify`). -/
theorem slVerify_eq_scheme_verify (pk : PK pr) (msg : Msg) (σ' : Stateless.Sig pr) :
    slVerify pr Msg enc pk.1 pk.2.1 pk.2.2 msg σ' =
      Scheme.Shrincs.verify pr (enc.body msg) (enc.ctx msg) (.stateless σ') (PK.toSchemePK pr pk) :=
  rfl

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- When the random oracle returns `H_msg^sf(R, PK.seed, PK.sf, (z, i), M̃)`, the model's stateful
verifier (`verifyWith`) equals the stateful branch of Algorithm 3 (`Scheme.Shrincs.verify`). -/
theorem verifyWith_eq_scheme_verify (pk : PK pr) (msg : Msg) (z i : ℕ) (R : pr.Y)
    (σt : Scheme.Fxmss.Sig pr) :
    verifyWith pr pk.1 pk.2.2 ⟨z, i⟩ (some σt)
        (pr.HmsgSf R pk.1 pk.2.2 ⟨z, i⟩ (bmBytes pr Msg enc pk.2.1 msg)) =
      Scheme.Shrincs.verify pr (enc.body msg) (enc.ctx msg) (.stateful z i R σt)
        (PK.toSchemePK pr pk) := by
  unfold Scheme.Shrincs.verify Scheme.Fxmss.verifyMessage verifyWith bmBytes PK.toSchemePK
  simp only [enc.ctx_le msg, decide_true, Bool.true_and]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  cases Scheme.Fxmss.pkFromSig pr pk.1
    (pr.HmsgSf R pk.1 pk.2.2 ⟨z, i⟩
      (Scheme.Shrincs.boundMessage pr (enc.ctx msg) pk.2.1 (enc.body msg)))
    ⟨z, i⟩ σt <;> simp

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- When `leafSelect ctr = some v` and the random oracle returns `H_msg^sf`, the stateful branch of
`signSF` produces the exact signature of Algorithm 2 (`Scheme.Shrincs.sign`). -/
theorem signSF_eq_scheme_sign (k : SK pr) (ctr : ℕ) {v : Node}
    (hv : k.S.leafSelect ctr = some v) (optRand : pr.Y) (msg : Msg) :
    let id := v.toLeafId vp.params.hsf
    let R := pr.PRFmsgSf k.skPrf k.pk id (bmBytes pr Msg enc k.pkSl msg)
    let md := pr.HmsgSf R k.pk k.pkSf id (bmBytes pr Msg enc k.pkSl msg)
    (Scheme.Fxmss.sign pr k.S k.pk (k.wots pr) md id).map
        (Scheme.Shrincs.Signature.stateful id.height id.index R) =
      (Scheme.Shrincs.sign pr (enc.body msg) (enc.ctx msg) (k.toSchemeSK pr) (some ctr) optRand).1 := by
  simp only [Scheme.Shrincs.sign, enc.ctx_le msg, ↓reduceIte, SK.toSchemeSK, Option.bind_some, hv,
    Scheme.Fxmss.signMessage, Scheme.Shrincs.statefulRandomizer, bmBytes, SK.wots,
    Scheme.Shrincs.SecretKey.wotsSecret]

end SchemeBridge

end ShrincsSecurity.Shrincs

end
