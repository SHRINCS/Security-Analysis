module

public import ShrincsSecurity.Scheme.Fxmss
public import ShrincsSecurity.Scheme.Stateless

/-!
# The complete SHRINCS scheme

`SHRINCS-Security-Analysis.pdf`, Section 3 (keys, cross-binding, contexts, state and recovery
rules, Algorithms 1–3), Section 3.1 (Definition 3.1, Lemma 3.1 (i)).

* `keygen` is **Algorithm 1** from the three seeds and a structure: `PK.sl` is the top-layer XMSS
  root of the hypertree (VCVio's `GeneralHypertree.root`), `PK.sf` the FXMSS root. It returns `⊥`
  only for structures whose root is `⊥`, never for valid ones (`keygen_isSome`).
* `sign` is **Algorithm 2**: with the state `ctr` (or `⊥`), `leafSelect` decides the path; the
  stateful path increments the counter even when grinding fails, and binds the digest to the
  bound message `M̃ = 0x00 ‖ toByte(|ctx|, 1) ‖ ctx ‖ PK.sl ‖ M`; the stateless path signs
  `PK.sf ‖ M` with SLH-DSA under the caller's context.
* `verify` is **Algorithm 3**. The indicator byte is modelled by the constructor of `Signature`
  (`b = hsf` for the stateless constructor, `b = z*` for the stateful one, see
  `Signature.indicator`); the byte-length checks are replaced by the typed signature shapes and
  the authentication-path length check of `FXMSS.pkFromSig`.
* `execute` is an honest execution (**Definition 3.1**), in which the signer may replace its state
  by `⊥` before any call.

**Lemma 3.1 (i)** is `verify_sign` (single call, every state, every valid structure),
`execute_correct` (every honest execution) and `sign_eq_none` (`⊥` only on the stateful path and
only when the WOTS+C grinding returns `⊥`).

Byte-level serialisation, the message-length cap `|M| ≤ 2^61 − 384` and the public-key length
check are out of scope (the model is typed). Inputs with `|ctx| > 255` are outside the domain of
Algorithm 2; `sign` returns `⊥` on them and leaves the state unchanged.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.Shrincs

open SLHDSA (Byte)

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- The SHRINCS public key `PK = PK.seed ‖ PK.sl ‖ PK.sf`. -/
structure PublicKey (pr : Primitives vp.params) where
  pkSeed : pr.PkSeed
  /-- The stateless root (top-layer XMSS root of the hypertree). -/
  pkSl : pr.Y
  /-- The stateful root (FXMSS root). -/
  pkSf : pr.Y

/-- The SHRINCS secret key `SK = SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.sl ‖ structure ‖ PK.sf`. -/
structure SecretKey (pr : Primitives vp.params) where
  skSeed : pr.SkSeed
  skPrf : pr.SkPrf
  pkSeed : pr.PkSeed
  pkSl : pr.Y
  /-- The structure of the stateful tree (part of the secret key, Remark 2.1). -/
  sfStructure : Structure
  pkSf : pr.Y

/-- The signer's state: the counter `ctr` of stateful signatures issued, or `⊥` (stateless-only
mode). -/
abbrev State := Option ℕ

/-- The initial state `ctr = 0` returned by Algorithm 1. -/
def initialState : State := some 0

/-- A SHRINCS signature: `toByte(hsf, 1) ‖ σ_slh` on the stateless path, or
`toByte(z*, 1) ‖ R ‖ toByte(i*, ℓ_idx(δ*)) ‖ σ_tree` on the stateful path. -/
inductive Signature (pr : Primitives vp.params) where
  | stateless (σ : Stateless.Sig pr)
  | stateful (z i : ℕ) (R : pr.Y) (σ : Fxmss.Sig pr)

/-- The indicator byte `b`: `hsf` selects the stateless path, `z* < hsf` the stateful one. -/
def Signature.indicator : Signature pr → ℕ
  | .stateless _ => vp.params.hsf
  | .stateful z _ _ _ => z

/-- The `n/8`-byte encoding of an `n`-bit value. -/
def encodeY (y : pr.Y) : List Byte := (pr.yToBytes y).toList

/-- The **bound message** `M̃ = toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ PK.sl ‖ M` digested on the
stateful path (Section 3, "Contexts"). -/
def boundMessage (ctx : List Byte) (pkSl : pr.Y) (M : List Byte) : List Byte :=
  [0, UInt8.ofNat ctx.length] ++ ctx ++ encodeY pr pkSl ++ M

/-- The message `PK.sf ‖ M` signed on the stateless path (Section 3, "Cross-binding"). -/
def statelessMessage (pkSf : pr.Y) (M : List Byte) : List Byte := encodeY pr pkSf ++ M

/-- **Algorithm 1** (`SHRINCS.KeyGen`) from the seeds `SK.seed`, `SK.prf`, `PK.seed` and a
structure. -/
def keygen (S : Structure) (skSeed : pr.SkSeed) (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) :
    Option (SecretKey pr × PublicKey pr) :=
  let pkSl := Stateless.root pr skSeed pkSeed
  (Fxmss.root pr S pkSeed (Fxmss.prfSecret pr pkSeed skSeed S)).map fun pkSf =>
    (⟨skSeed, skPrf, pkSeed, pkSl, S, pkSf⟩, ⟨pkSeed, pkSl, pkSf⟩)

/-- The secret chain starts of the stateful WOTS+C instances of a secret key. -/
def SecretKey.wotsSecret (sk : SecretKey pr) : LeafId → ℕ → pr.Y :=
  Fxmss.prfSecret pr sk.pkSeed sk.skSeed sk.sfStructure

/-- The stateful randomizer `R = PRF_msg^sf(SK.prf, PK.seed, idx, M̃)` (Algorithm 2, line 10). -/
def statefulRandomizer (sk : SecretKey pr) (id : LeafId) (ctx M : List Byte) : pr.Y :=
  pr.PRFmsgSf sk.skPrf sk.pkSeed id (boundMessage pr ctx sk.pkSl M)

/-- The stateful digest `md = H_msg^sf(R, PK.seed, PK.sf, idx, M̃)` (Algorithm 2, line 11). -/
def statefulDigest (sk : SecretKey pr) (id : LeafId) (ctx M : List Byte) : pr.Digest :=
  pr.HmsgSf (statefulRandomizer pr sk id ctx M) sk.pkSeed sk.pkSf id (boundMessage pr ctx sk.pkSl M)

/-- **Algorithm 2** (`SHRINCS.Sign`): returns the signature (or `⊥`) and the updated state. -/
def sign (M ctx : List Byte) (sk : SecretKey pr) (st : State) (optRand : pr.Y) :
    Option (Signature pr) × State :=
  if ctx.length ≤ 255 then
    match st.bind sk.sfStructure.leafSelect with
    | none =>
      ((Stateless.sign pr (statelessMessage pr sk.pkSf M) ctx sk.skSeed sk.skPrf sk.pkSeed
          sk.pkSl optRand).map .stateless, st)
    | some v =>
      let id := v.toLeafId vp.params.hsf
      let R := statefulRandomizer pr sk id ctx M
      ((Fxmss.signMessage pr sk.sfStructure sk.pkSeed sk.wotsSecret sk.pkSf R
          (boundMessage pr ctx sk.pkSl M) id).map (.stateful id.height id.index R),
        st.map (· + 1))
  else (none, st)

/-- **Algorithm 3** (`SHRINCS.Verify`). -/
def verify [DecidableEq pr.Y] (M ctx : List Byte) (σ : Signature pr) (pk : PublicKey pr) : Bool :=
  match σ with
  | .stateless σ' =>
    Stateless.verify pr (statelessMessage pr pk.pkSf M) ctx σ' pk.pkSeed pk.pkSl
  | .stateful z i R σt =>
    decide (ctx.length ≤ 255) &&
      Fxmss.verifyMessage pr pk.pkSeed pk.pkSf (boundMessage pr ctx pk.pkSl M) ⟨z, i⟩ R σt

/-! ## Basic facts -/

variable {pr}

/-- Key generation succeeds for every valid structure. -/
theorem keygen_isSome {S : Structure} (hS : S.TreeValid vp.params.hsf) (skSeed : pr.SkSeed)
    (skPrf : pr.SkPrf) (pkSeed : pr.PkSeed) : (keygen pr S skSeed skPrf pkSeed).isSome := by
  simp only [keygen, Option.isSome_map]
  exact Fxmss.root_isSome hS _ _

/-- The keys produced by Algorithm 1. -/
theorem keygen_eq_some {S : Structure} {skSeed : pr.SkSeed} {skPrf : pr.SkPrf}
    {pkSeed : pr.PkSeed} {sk : SecretKey pr} {pk : PublicKey pr}
    (hk : keygen pr S skSeed skPrf pkSeed = some (sk, pk)) :
    sk.skSeed = skSeed ∧ sk.skPrf = skPrf ∧ sk.pkSeed = pkSeed ∧
      sk.pkSl = Stateless.root pr skSeed pkSeed ∧ sk.sfStructure = S ∧
      Fxmss.root pr S pkSeed (Fxmss.prfSecret pr pkSeed skSeed S) = some sk.pkSf ∧
      pk = ⟨sk.pkSeed, sk.pkSl, sk.pkSf⟩ := by
  simp only [keygen, Option.map_eq_some_iff, Prod.mk.injEq] at hk
  obtain ⟨pkSf, hroot, rfl, rfl⟩ := hk
  exact ⟨rfl, rfl, rfl, rfl, rfl, hroot, rfl⟩

/-- The bound message encoding is injective in `(ctx, M)` for contexts within the bound
(Section 3, "Contexts"). -/
theorem boundMessage_injective {ctx ctx' M M' : List Byte} {pkSl : pr.Y}
    (hctx : ctx.length ≤ 255) (hctx' : ctx'.length ≤ 255)
    (h : boundMessage pr ctx pkSl M = boundMessage pr ctx' pkSl M') : ctx = ctx' ∧ M = M' := by
  simp only [boundMessage, List.cons_append, List.nil_append, List.cons.injEq, true_and,
    List.append_assoc] at h
  obtain ⟨hlen, h⟩ := h
  have hlen' : ctx.length = ctx'.length := by
    have := congrArg UInt8.toNat hlen
    simp only [UInt8.toNat_ofNat'] at this
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hlen'
  exact ⟨h1, List.append_cancel_left h2⟩

/-! ## Lemma 3.1 (i): correctness -/

/-- **Lemma 3.1 (i)**, one call: for every valid structure, every key pair output by
Algorithm 1, every state (a counter or `⊥`), every message, context within the bound and
randomness, a non-`⊥` signature output by Algorithm 2 verifies under Algorithm 3. Both paths are
covered: the stateless path by VCVio's FIPS 205 completeness, the stateful path by FXMSS
correctness. -/
theorem verify_sign [DecidableEq pr.Y] {S : Structure} (hS : S.Valid vp.params.hsf)
    {skSeed : pr.SkSeed} {skPrf : pr.SkPrf} {pkSeed : pr.PkSeed} {sk : SecretKey pr}
    {pk : PublicKey pr} (hk : keygen pr S skSeed skPrf pkSeed = some (sk, pk)) (st : State)
    {M ctx : List Byte} (optRand : pr.Y) (hctx : ctx.length ≤ 255) {σ : Signature pr}
    (hσ : (sign pr M ctx sk st optRand).1 = some σ) : verify pr M ctx σ pk = true := by
  obtain ⟨rfl, rfl, rfl, hsl, rfl, hroot, rfl⟩ := keygen_eq_some hk
  simp only [sign, hctx, ↓reduceIte] at hσ
  split at hσ
  · -- stateless path
    obtain ⟨σ', hσ', rfl⟩ := Option.map_eq_some_iff.1 hσ
    rw [hsl] at hσ' ⊢
    exact Stateless.verify_sign pr hctx hσ'
  · -- stateful path
    rename_i v hv
    obtain ⟨σt, hσt, rfl⟩ := Option.map_eq_some_iff.1 hσ
    simp only [verify, hctx, decide_true, Bool.true_and]
    exact Fxmss.verifyMessage_signMessage hS.toTreeValid hroot hσt

/-- **Lemma 3.1 (i)**, failures: under the context bound, `σ = ⊥` occurs only on the stateful
path (some anchor `v` was selected), and only when the WOTS+C grinding at that anchor returns `⊥`
on the stateful digest. -/
theorem sign_eq_none {S : Structure} (hS : S.Valid vp.params.hsf) {skSeed : pr.SkSeed}
    {skPrf : pr.SkPrf} {pkSeed : pr.PkSeed} {sk : SecretKey pr} {pk : PublicKey pr}
    (hk : keygen pr S skSeed skPrf pkSeed = some (sk, pk)) (st : State) {M ctx : List Byte}
    (optRand : pr.Y) (hctx : ctx.length ≤ 255) (h : (sign pr M ctx sk st optRand).1 = none) :
    ∃ v, st.bind S.leafSelect = some v ∧
      WotsC.grind pr sk.pkSeed (v.toLeafId vp.params.hsf)
        (statefulDigest pr sk (v.toLeafId vp.params.hsf) ctx M) = none := by
  obtain ⟨rfl, rfl, rfl, -, rfl, -, rfl⟩ := keygen_eq_some hk
  simp only [sign, hctx, ↓reduceIte] at h
  split at h
  · simp only [Option.map_eq_none_iff] at h
    have := Stateless.sign_isSome pr (M := statelessMessage pr sk.pkSf M) hctx sk.skSeed sk.skPrf
      sk.pkSeed sk.pkSl optRand
    rw [h] at this
    cases this
  · rename_i v hv
    refine ⟨v, hv, ?_⟩
    simp only [Option.map_eq_none_iff] at h
    obtain ⟨q, -, hq⟩ := Option.bind_eq_some_iff.1 hv
    have hA := hS.leafSelect_mem q v hq
    have hdepth := hS.anchor_depth_le v hA
    have hz : (v.toLeafId vp.params.hsf).height ≤ vp.params.hsf := Nat.sub_le _ _
    have hA' : Node.ofLeafId vp.params.hsf (v.toLeafId vp.params.hsf) ∈ sk.sfStructure.anchors := by
      rwa [Node.ofLeafId_toLeafId hdepth]
    exact (Fxmss.sign_eq_none_iff hS.toTreeValid hz hA').1 h

/-- The state update of Algorithm 2: the stateless path leaves the state unchanged. -/
theorem sign_state_of_stateless {sk : SecretKey pr} {st : State} {M ctx : List Byte}
    {optRand : pr.Y} (h : st.bind sk.sfStructure.leafSelect = none) :
    (sign pr M ctx sk st optRand).2 = st := by
  unfold sign
  split_ifs
  · rw [h]
  · rfl

/-- The state update of Algorithm 2: the stateful path increments the counter, also when the
counter search fails (footnote 7: the leaf stays consumed). -/
theorem sign_state_of_stateful {sk : SecretKey pr} {ctr : ℕ} {v : Node} {M ctx : List Byte}
    {optRand : pr.Y} (hctx : ctx.length ≤ 255) (h : sk.sfStructure.leafSelect ctr = some v) :
    (sign pr M ctx sk (some ctr) optRand).2 = some (ctr + 1) := by
  simp only [sign, hctx, ↓reduceIte, Option.bind_some, h, Option.map_some]

/-! ## Definition 3.1: honest executions -/

/-- One call of an honest execution: message, context, optional randomness, and whether the
signer replaces its state by `⊥` before the call (Definition 3.1). -/
structure CallInput (pr : Primitives vp.params) where
  M : List Byte
  ctx : List Byte
  optRand : pr.Y
  dropState : Bool

variable (pr) in
/-- **Honest execution** (Definition 3.1): the sequence of calls
`(σ_i, ctr_i) ← SHRINCS.Sign(M_i, ctx_i, SK, st_{i−1}, opt_rand_i)`, where `st_{i−1}` is the
state returned by the previous call or `⊥`. -/
def execute (sk : SecretKey pr) : State → List (CallInput pr) → List (Option (Signature pr))
  | _, [] => []
  | st, c :: cs =>
    let out := sign pr c.M c.ctx sk (if c.dropState then none else st) c.optRand
    out.1 :: execute sk out.2 cs

/-- **Lemma 3.1 (i)** (SHRINCS is correct, Definition 3.1): in every honest execution from any
state, for every valid structure, every non-`⊥` signature verifies. -/
theorem execute_correct [DecidableEq pr.Y] {S : Structure} (hS : S.Valid vp.params.hsf)
    {skSeed : pr.SkSeed} {skPrf : pr.SkPrf} {pkSeed : pr.PkSeed} {sk : SecretKey pr}
    {pk : PublicKey pr} (hk : keygen pr S skSeed skPrf pkSeed = some (sk, pk)) :
    ∀ (inputs : List (CallInput pr)) (st : State), (∀ c ∈ inputs, c.ctx.length ≤ 255) →
      ∀ p ∈ inputs.zip (execute pr sk st inputs), ∀ σ, p.2 = some σ →
        verify pr p.1.M p.1.ctx σ pk = true
  | [], _, _, p, hp, _, _ => by simp [execute] at hp
  | c :: cs, st, hctx, p, hp, σ, hσ => by
    simp only [execute, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact verify_sign hS hk _ c.optRand (hctx c (by simp)) hσ
    · exact execute_correct hS hk cs _ (fun c' hc' => hctx c' (by simp [hc'])) p hp σ hσ

/-- **Lemma 3.1 (i)** as stated, for the two prescribed shapes: every honest execution under a
key generated with an admissible UXMSS or BXMSS structure `(shape, depth)` is correct. -/
theorem execute_correct_of_admissible [DecidableEq pr.Y] {desc : Descriptor}
    (hdesc : desc.Admissible vp.params.hsf) {skSeed : pr.SkSeed} {skPrf : pr.SkPrf}
    {pkSeed : pr.PkSeed} {sk : SecretKey pr} {pk : PublicKey pr}
    (hk : keygen pr desc.toStructure skSeed skPrf pkSeed = some (sk, pk))
    (inputs : List (CallInput pr)) (st : State) (hctx : ∀ c ∈ inputs, c.ctx.length ≤ 255) :
    ∀ p ∈ inputs.zip (execute pr sk st inputs), ∀ σ, p.2 = some σ →
      verify pr p.1.M p.1.ctx σ pk = true :=
  execute_correct (Descriptor.valid hdesc) hk inputs st hctx

end ShrincsSecurity.Scheme.Shrincs
