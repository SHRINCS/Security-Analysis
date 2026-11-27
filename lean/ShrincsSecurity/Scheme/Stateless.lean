module

public import ShrincsSecurity.Scheme.Primitives
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.WotsInjectivity

/-!
# The stateless component: SLH-DSA from VCVio

`SHRINCS-Security-Analysis.pdf`, Section 2.3 (WOTS-TW), Section 2.5 (XMSS, stateless path),
Section 2.6 (FORS), Section 2.7 (hypertree and SLH-DSA, context wrapper), Section 3.1 (proof of
Lemma 3.1, Step 6).

"All algorithms in this subsection coincide with those of FIPS-205" (Section 2.7), and every hash
call of the stateless path is bit-identical to SLH-DSA-SHA2 with a non-standard parameter set
(Section 2.2). We therefore **reuse VCVio's SLH-DSA development** rather than re-defining
WOTS-TW, XMSS, FORS and the hypertree: the stateless path is VCVio's general-depth FIPS 205
scheme (`SLHDSA.GeneralScheme`, `SLHDSA.GeneralHypertree`, FORS, XMSS, WOTS+), together with the
pure-mode context wrapper of `SLHDSA.External` (Algorithms 22/24), at the validated parameter set
`vp.sl` (for SHRINCS: `d = 5`, `h' = 9`, `k = 10`, `a = 13`, `w = 16`, `n = 16` bytes; see
`shrincs_slParams`) and the primitive bundle `pr.toSLHDSA`, which shares `PK.seed`, `F`, `H`,
`Th_ℓ`, `PRF` with the stateful path and whose tweak space is the common address format.

This file packages the three algorithms the composite scheme calls, transports VCVio's
completeness theorem (`verify_sign`), and records the facts about the stateless path that the
reductions use: the WOTS-TW checksum incomparability (Section 2.3) at the SHRINCS parameters and
the fact that every address the stateless path hashes at is a stateless address (types 0–6).
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.Stateless

open SLHDSA (Adrs Byte)

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- The stateless signature `σ_slh = R ‖ σ_FORS ‖ σ_HT` (VCVio's intrinsically shaped type). -/
abbrev Sig := SLHDSA.GeneralScheme.SignatureCore vp.sl pr.toSLHDSA.core

/-- **`PK.sl`**: the root of the single top-layer XMSS tree of the hypertree (layer `d − 1`,
tree `0`; Algorithm 1, line 3). -/
def root (skSeed : pr.SkSeed) (pkSeed : pr.PkSeed) : pr.Y :=
  SLHDSA.GeneralHypertree.root vp.sl pr.toSLHDSA skSeed pkSeed

/-- The SLH-DSA secret key `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.sl`. -/
def secretKey (skSeed : pr.SkSeed) (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) (pkSl : pr.Y) :
    SLHDSA.SecretKeyCore pr.toSLHDSA.core :=
  ⟨skSeed, skPrf, pkSeed, pkSl⟩

/-- The SLH-DSA public key `PK.seed ‖ PK.sl`. -/
def publicKey (pkSeed : pr.PkSeed) (pkSl : pr.Y) : SLHDSA.PublicKeyCore pr.toSLHDSA.core :=
  ⟨pkSeed, pkSl⟩

/-- **`slh.sign(M, ctx, SK.seed, SK.prf, PK.seed, PK.sl, opt_rand)`** (Section 2.7): the FIPS 205
pure-mode wrapper `M' = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ M` around the internal signer; `⊥` if
`|ctx| > 255`. -/
def sign (M ctx : List Byte) (skSeed : pr.SkSeed) (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed)
    (pkSl : pr.Y) (optRand : pr.Y) : Option (Sig pr) :=
  match SLHDSA.External.signPureWithRandomizer vp.sl pr.toSLHDSA M ctx
      (secretKey pr skSeed skPrf pkSeed pkSl) optRand with
  | .ok σ => some σ
  | .error _ => none

/-- **`slh.verify(M, σ, ctx, PK.seed, PK.sl)`** (Section 2.7). -/
def verify [DecidableEq pr.Y] (M ctx : List Byte) (σ : Sig pr) (pkSeed : pr.PkSeed)
    (pkSl : pr.Y) : Bool :=
  SLHDSA.External.verifyPure vp.sl pr.toSLHDSA M σ ctx (publicKey pr pkSeed pkSl)

/-- VCVio's FIPS 205 key generation from seeds produces exactly the SHRINCS stateless keys. -/
theorem keygenWithSeeds_eq (skSeed : pr.SkSeed) (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) :
    SLHDSA.External.keygenWithSeeds vp.sl pr.toSLHDSA skSeed skPrf pkSeed =
      (secretKey pr skSeed skPrf pkSeed (root pr skSeed pkSeed),
        publicKey pr pkSeed (root pr skSeed pkSeed)) := by
  have h1 := SLHDSA.GeneralScheme.keygenInternal_fst vp.sl pr.toSLHDSA skSeed skPrf pkSeed
  have h2 := SLHDSA.GeneralScheme.keygenInternal_snd vp.sl pr.toSLHDSA skSeed skPrf pkSeed
  unfold SLHDSA.External.keygenWithSeeds
  generalize SLHDSA.GeneralScheme.keygenInternal vp.sl pr.toSLHDSA skSeed skPrf pkSeed = kp
    at h1 h2 ⊢
  obtain ⟨pk, sk⟩ := kp
  simp only at h1 h2
  subst h1 h2
  rfl

/-- Stateless signing never fails under the context bound (Lemma 3.1 (i): `slh.sign` has no
failing step). -/
theorem sign_isSome {M ctx : List Byte} (hctx : ctx.length ≤ 255) (skSeed : pr.SkSeed)
    (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) (pkSl optRand : pr.Y) :
    (sign pr M ctx skSeed skPrf pkSeed pkSl optRand).isSome := by
  unfold sign SLHDSA.External.signPureWithRandomizer
  rw [SLHDSA.External.encodePureMessage_eq_ok ctx M hctx]
  rfl

/-- **Stateless correctness** (Lemma 3.1, Step 6): a signature produced under the honest
`PK.sl` verifies, for every message, context within the bound, seeds and randomizer. This is
VCVio's general-depth FIPS 205 external completeness theorem. -/
theorem verify_sign [DecidableEq pr.Y] {M ctx : List Byte} (hctx : ctx.length ≤ 255)
    {skSeed : pr.SkSeed} {skPrf : pr.SkPrf} {pkSeed : pr.PkSeed} {optRand : pr.Y}
    {σ : Sig pr} (h : sign pr M ctx skSeed skPrf pkSeed (root pr skSeed pkSeed) optRand = some σ) :
    verify pr M ctx σ pkSeed (root pr skSeed pkSeed) = true := by
  have hc := SLHDSA.External.verifyPure_signPureWithRandomizer vp.sl pr.toSLHDSA M ctx
    skSeed skPrf pkSeed optRand hctx
  rw [keygenWithSeeds_eq] at hc
  unfold sign at h
  unfold verify
  split at h
  · rename_i σ' hσ'
    cases h
    rw [hσ'] at hc
    simpa [Except.map] using hc
  · cases h

/-! ## WOTS-TW at the SHRINCS parameters (Section 2.3) -/

/-- WOTS-TW encodes an `n`-bit message into `lsl = l1 + l2` base-`w` digits. -/
theorem chainLengths_length (msg : pr.Y) :
    (SLHDSA.chainLengthsCore pr.toSLHDSA.core msg).length = vp.params.lsl := by
  rw [SLHDSA.chainLengthsCore_length, Params.lsl_eq_len vp.valid]

/-- **WOTS-TW checksum incomparability** (Section 2.3): if every digit of the encoding of `m'`
were at least the corresponding digit of the encoding of `m ≠ m'`, the checksum would force
equality; hence neither encoding dominates the other. VCVio's
`SLHDSA.chainLengthsCore_incomparable` at the SHRINCS stateless parameters. -/
theorem wotsTW_incomparable (hinj : Function.Injective pr.yToBytes) {m m' : pr.Y}
    (hne : m ≠ m') :
    ¬ List.Forall₂ (· ≤ ·) (SLHDSA.chainLengthsCore pr.toSLHDSA.core m)
        (SLHDSA.chainLengthsCore pr.toSLHDSA.core m') ∧
      ¬ List.Forall₂ (· ≤ ·) (SLHDSA.chainLengthsCore pr.toSLHDSA.core m')
        (SLHDSA.chainLengthsCore pr.toSLHDSA.core m) :=
  SLHDSA.chainLengthsCore_incomparable (core := pr.toSLHDSA.core) vp.valid.slValid ⟨hinj⟩ hne

end ShrincsSecurity.Scheme.Stateless

/-! ## Stateless addresses (Table 2, types 0–6) -/

namespace ShrincsSecurity.Scheme

open SLHDSA (Adrs)

/-- Every address at which the stateless path evaluates `F`, `H`, `Th_ℓ` or `PRF` is built by a
FIPS 205 type change followed by field setters, hence is a stateless address. -/
theorem isStateless_wotsSkAdrs (a : Adrs) (i : ℕ) : IsStateless (SLHDSA.wotsSkAdrs a i) :=
  ⟨.wotsPrf, rfl⟩

theorem isStateless_wotsChainAdrs (a : Adrs) (i j : ℕ) :
    IsStateless ((SLHDSA.wotsChainAdrs a i).setHashAddress j) :=
  ⟨.wotsHash, rfl⟩

theorem isStateless_wotsPkAdrs (a : Adrs) : IsStateless (SLHDSA.wotsPkAdrs a) := ⟨.wotsPk, rfl⟩

theorem isStateless_xmssNodeAdrs (a : Adrs) (z t : ℕ) : IsStateless (SLHDSA.xmssNodeAdrs a z t) :=
  ⟨.tree, rfl⟩

theorem isStateless_forsSkAdrs (a : Adrs) (t : ℕ) : IsStateless (SLHDSA.forsSkAdrs a t) :=
  ⟨.forsPrf, rfl⟩

theorem isStateless_forsNodeAdrs (a : Adrs) (z t : ℕ) : IsStateless (SLHDSA.forsNodeAdrs a z t) :=
  ⟨.forsTree, rfl⟩

theorem isStateless_forsPkAdrs (a : Adrs) : IsStateless (SLHDSA.forsPkAdrs a) := ⟨.forsRoots, rfl⟩

/-- **Tweak disjointness between the paths**: no stateful address (WOTS+C chains, compressions,
tree nodes, secret derivation, grinding) coincides with an address of the stateless path. -/
theorem SfAdrs.toAdrs_ne_wotsChainAdrs (s : SfAdrs) (a : Adrs) (i j : ℕ) :
    s.toAdrs ≠ (SLHDSA.wotsChainAdrs a i).setHashAddress j :=
  s.toAdrs_ne_of_isStateless (isStateless_wotsChainAdrs a i j)

theorem SfAdrs.toAdrs_ne_xmssNodeAdrs (s : SfAdrs) (a : Adrs) (z t : ℕ) :
    s.toAdrs ≠ SLHDSA.xmssNodeAdrs a z t :=
  s.toAdrs_ne_of_isStateless (isStateless_xmssNodeAdrs a z t)

theorem SfAdrs.toAdrs_ne_wotsPkAdrs (s : SfAdrs) (a : Adrs) : s.toAdrs ≠ SLHDSA.wotsPkAdrs a :=
  s.toAdrs_ne_of_isStateless (isStateless_wotsPkAdrs a)

theorem SfAdrs.toAdrs_ne_forsNodeAdrs (s : SfAdrs) (a : Adrs) (z t : ℕ) :
    s.toAdrs ≠ SLHDSA.forsNodeAdrs a z t :=
  s.toAdrs_ne_of_isStateless (isStateless_forsNodeAdrs a z t)

theorem SfAdrs.toAdrs_ne_forsPkAdrs (s : SfAdrs) (a : Adrs) : s.toAdrs ≠ SLHDSA.forsPkAdrs a :=
  s.toAdrs_ne_of_isStateless (isStateless_forsPkAdrs a)

theorem SfAdrs.toAdrs_ne_wotsSkAdrs (s : SfAdrs) (a : Adrs) (i : ℕ) :
    s.toAdrs ≠ SLHDSA.wotsSkAdrs a i :=
  s.toAdrs_ne_of_isStateless (isStateless_wotsSkAdrs a i)

theorem SfAdrs.toAdrs_ne_forsSkAdrs (s : SfAdrs) (a : Adrs) (t : ℕ) :
    s.toAdrs ≠ SLHDSA.forsSkAdrs a t :=
  s.toAdrs_ne_of_isStateless (isStateless_forsSkAdrs a t)

end ShrincsSecurity.Scheme
