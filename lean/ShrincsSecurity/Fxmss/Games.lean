module

public import ShrincsSecurity.Fxmss.Model

/-!
# The games of the proof of Theorem 4.2

`SHRINCS-Security-Analysis.pdf`, Section 4.7: the games `F.0`, `F.2` and the chain-value hybrids
between `F.3` and `F.4`, written as explicit `ProbComp` programs over one shared signing-phase
handler.

## Shared structure

All games run the forger in two phases. The structure phase `A₁` runs against the lazily sampled
random oracle `H_msg^sf` (`romImpl`, cache `c`); the signing phase runs `stage2Prog`: the second
stage `A₂`, then **one verification query** `y* = H_msg^sf(R*, PK.seed, PK.sf, idx*, M*)` of the
forgery, then the **completion of Remark 4.6**: a signing query on every anchor of the structure,
with a message different from `M*` (already used anchors are answered `⊥`). The completion comes
after the forgery and does not affect it; it makes every anchor signed in every execution, which is
what the extraction of Claim 4.10 and the reduction `B₀` need (this is the wrapper `A'` of
Remark 4.6 run inside the games, see `Remark46.lean` for the wrapper as an adversary).

The signing phase is simulated by `impl K dig sigOf` over the state `St` (random-oracle cache,
used leaves, queried messages, and a record of every answered signing query). Its two parameters
are the only differences between the games:

| game | digest of a signing query at leaf `j` (`dig`) | WOTS+C/tree signature (`sigOf`) |
|---|---|---|
| `gameG` (`F.0`) | `H_msg^sf(R, …)` from the random oracle | `FXMSS.sign(sk, md)` |
| `gameG2` (`F.2`, lazily) | fresh uniform `md`, programmed at `(R, …)` | `FXMSS.sign(sk, md)` |
| `gameHyb γ` (`F.2`–`F.4`) | presampled `y_j`, programmed at `(R, …)` | precomputed from blocks |

In every game `PK.seed` is sampled **first**, before `A₁` (which never sees it); this is the order
in which the two-stage reductions of Claims 4.3–4.9 meet it (the public parameter is drawn by
their challenger before their first stage). `Bridge.lean` proves that the EU-CMA experiment of
Definition 4.16, which samples `PK.seed` in key generation, has the success probability of
`gameG`.

## The block games

`gameHyb γ` is `F.2` (presampled digests `y_j`, one per anchor, `Anchor P S → Digest`) in the
block form of the hop `F.3 → F.4`: with `u` uniform on anchors × chains and the encoded digests'
digits `a_{j,i}`, the revealed blocks are `σ_{j,i} = c_{m, a − m}(u_{j,i})`, `m = min(γ, a − 1)`
(`blockVal`), the public keys are completed from the blocks, and the tree is built over the
compressions. `γ = 0` gives the secret-key game `F.2 = F.3` with `sk = u`
(`σ = c_{0,a}(sk)`), and `γ = w − 2` gives `F.4` (`σ = F(u)` at position `a − 1`, or `u` when
`a = 0`). The honest data of a block game (`Honest`) is a pure function of the setup and
`PK.seed` (`hon`).

`gameHyb γ` factors as `PK.seed ←$; d ← setupHyb A; stageHyb (β γ) d PK.seed`, with `setupHyb`
independent of `PK.seed`: this is the split along which the two-stage reductions are built.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

variable {P : Params}

section Defs

variable (pr : Primitives P) (Msg : Type)

/-- The record of an answered signing query: message, randomizer, digest and signature. -/
structure Rec where
  /-- The signed message `M̃_j`. -/
  msg : Msg
  /-- The randomizer `R_j`. -/
  rand : pr.Y
  /-- The digest `y_j`. -/
  digest : pr.Digest
  /-- The WOTS+C/tree signature. -/
  sig : Option (Scheme.Fxmss.Sig pr)

/-- The state of the signing phase. -/
structure St where
  /-- The random-oracle cache. -/
  cache : (roSpec pr Msg).QueryCache
  /-- The used leaves, in order. -/
  used : List LeafId
  /-- The queried messages, answered or not. -/
  log : List Msg
  /-- The record of the answered signing query at each used leaf. -/
  recs : LeafId → Option (Rec pr Msg)

/-- The initial state of the signing phase, continuing the random-oracle cache `c` of the
structure phase. -/
def St.init (c : (roSpec pr Msg).QueryCache) : St pr Msg := ⟨c, [], [], fun _ => none⟩

/-- The public data of the signing phase. -/
structure Keys where
  /-- The structure. -/
  S : Structure
  /-- `PK.seed`. -/
  pk : pr.PkSeed
  /-- `PK.sl`. -/
  pkSl : pr.Y
  /-- `PK.sf`. -/
  pkSf : pr.Y

/-- The public key handed to `A₂`. -/
def Keys.toPK {pr : Primitives P} (K : Keys pr) : PK pr := (K.pk, K.pkSl, K.pkSf)

variable [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg]

/-- The lazily sampled random oracle on the cache of the state. -/
def roStep (x : RoIn pr Msg) : StateT (St pr Msg) ProbComp pr.Digest := StateT.mk fun s =>
  match s.cache x with
  | some d => pure (d, s)
  | none => (fun d => (d, { s with cache := s.cache.cacheQuery x d })) <$> ($ᵗ pr.Digest)

/-- Program the random oracle at `x` with `d` and answer `d`. -/
def progStep (x : RoIn pr Msg) (d : pr.Digest) : StateT (St pr Msg) ProbComp pr.Digest :=
  StateT.mk fun s => pure (d, { s with cache := s.cache.cacheQuery x d })

/-- Sample a fresh digest and program it at `x` (the reprogramming of `F.2`, lazily). -/
def freshProgStep (x : RoIn pr Msg) : StateT (St pr Msg) ProbComp pr.Digest := StateT.mk fun s =>
  (fun d => (d, { s with cache := s.cache.cacheQuery x d })) <$> ($ᵗ pr.Digest)

/-- The signing oracle of Definition 4.16 over `St`: a leaf of the structure not used before is
signed (`R ←$ Y`, digest by `dig`, signature by `sigOf`) and recorded; any other query is
answered `⊥`. Every query's message is logged. -/
def signStep (K : Keys pr) (dig : LeafId → RoIn pr Msg → StateT (St pr Msg) ProbComp pr.Digest)
    (sigOf : LeafId → pr.Digest → Option (Scheme.Fxmss.Sig pr)) (q : Msg × LeafId) :
    StateT (St pr Msg) ProbComp (Option (Sig pr)) := do
  let s ← get
  if q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used then
    let R ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : StateT (St pr Msg) ProbComp pr.Y)
    let md ← dig q.2 (roIn pr Msg R K.pk K.pkSf q.2 q.1)
    modify fun s => { s with
      used := s.used ++ [q.2]
      log := s.log ++ [q.1]
      recs := Function.update s.recs q.2 (some ⟨q.1, R, md, sigOf q.2 md⟩) }
    return some (R, sigOf q.2 md)
  else
    modify fun s => { s with log := s.log ++ [q.1] }
    return none

/-- The handler of the signing phase: private coins, the random oracle, the signing oracle. -/
def impl (K : Keys pr) (dig : LeafId → RoIn pr Msg → StateT (St pr Msg) ProbComp pr.Digest)
    (sigOf : LeafId → pr.Digest → Option (Scheme.Fxmss.Sig pr)) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp) :=
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (St pr Msg) ProbComp) +
    (fun x => roStep pr Msg x : QueryImpl (roSpec pr Msg) (StateT (St pr Msg) ProbComp))) +
  (fun q => signStep pr Msg K dig sigOf q :
    QueryImpl (Notions.FxmssScheme.signSpec Msg LeafId (Sig pr)) (StateT (St pr Msg) ProbComp))

/-- The anchors of a structure in a fixed (canonical) order. -/
noncomputable def anchorList (P : Params) (S : Structure) : List LeafId := (leafIds P.hsf S).toList

/-- A message different from `M` (the completion messages of Remark 4.6). -/
noncomputable def otherMsg [Nontrivial Msg] (M : Msg) : Msg := Classical.choose (exists_ne M)

omit [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem otherMsg_ne [Nontrivial Msg] (M : Msg) : otherMsg Msg M ≠ M :=
  Classical.choose_spec (exists_ne M)

/-- The completion of Remark 4.6: a signing query with message `M` on every listed leaf. -/
def completion (M : Msg) : List LeafId → OracleComp (fullSpec pr Msg) Unit
  | [] => pure ()
  | id :: ids => do
    let _ ← ((fullSpec pr Msg).query (.inr (M, id)) : OracleComp (fullSpec pr Msg) (Option (Sig pr)))
    completion M ids

variable [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- **The signing phase**: `A₂`, the verification query of the forgery, and the completion of
Remark 4.6. Returns `(M*, (z*, i*), σ*, y*)`. -/
noncomputable def stage2Prog {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (K : Keys pr) :
    OracleComp (fullSpec pr Msg) (Msg × LeafId × Sig pr × pr.Digest) := do
  let out ← A.forge st K.S K.toPK
  let yf ← ((fullSpec pr Msg).query (.inl (.inr (roIn pr Msg out.2.2.1 K.pk K.pkSf out.2.1 out.1))) :
    OracleComp (fullSpec pr Msg) pr.Digest)
  completion pr Msg (otherMsg Msg out.1) (anchorList P K.S)
  return (out.1, out.2.1, out.2.2, yf)

/-- The transcript of a game: the keys, the forgery `(M*, (z*, i*), σ*)`, its digest `y*`, and the
final state of the signing phase. -/
structure Transcript where
  /-- The public data. -/
  K : Keys pr
  /-- `M*`. -/
  Mf : Msg
  /-- `(z*, i*)`. -/
  idf : LeafId
  /-- `σ* = (R*, σ*_tree)`. -/
  σf : Sig pr
  /-- `y* = H_msg^sf(R*, PK.seed, PK.sf, idx*, M*)`. -/
  yf : pr.Digest
  /-- The final state. -/
  st : St pr Msg

/-- Package a run of the signing phase. -/
def Transcript.ofRun (K : Keys pr) (z : (Msg × LeafId × Sig pr × pr.Digest) × St pr Msg) :
    Transcript pr Msg :=
  ⟨K, z.1.1, z.1.2.1, z.1.2.2.1, z.1.2.2.2, z.2⟩

variable {pr Msg} in
/-- The forger wins: the forgery verifies and its message was never queried. -/
def Transcript.Win (tr : Transcript pr Msg) : Prop :=
  verifyWith pr tr.K.pk tr.K.pkSf tr.idf tr.σf.2 tr.yf = true ∧ tr.Mf ∉ tr.st.log

variable {pr Msg} in
/-- **The abort event of F.1**: the forgery's leaf was signed with the same digest `y_j = y*`. -/
def Transcript.C1 (tr : Transcript pr Msg) : Prop :=
  ∃ r, tr.st.recs tr.idf = some r ∧ r.digest = tr.yf

/-- The honest mode of `F.0`: the digest is the random oracle's answer and the signature is
`FXMSS.sign` with the secret table `sk`. -/
noncomputable def implG (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp) :=
  impl pr Msg K (fun _ x => roStep pr Msg x) (fun id md => Scheme.Fxmss.sign pr K.S K.pk sk md id)

/-- The mode of `F.2`, lazily: the digest is fresh and programmed. -/
noncomputable def implG2 (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp) :=
  impl pr Msg K (fun _ x => freshProgStep pr Msg x)
    (fun id md => Scheme.Fxmss.sign pr K.S K.pk sk md id)

/-- The structure phase `A₁` against the lazily sampled random oracle. -/
noncomputable def stage1 {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ProbComp ((Structure × A.State) × (roSpec pr Msg).QueryCache) :=
  (simulateQ (roSpec pr Msg).romImpl A.chooseShape).run ∅

/-- The signing phase of `F.0`/`F.2` from the structure-phase output, `PK.seed` and a signing
mode (`implG` or `implG2`). -/
noncomputable def stageG {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (mode : Keys pr → (LeafId → ℕ → pr.Y) → QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp))
    (pk : pr.PkSeed) (z : (Structure × A.State) × (roSpec pr Msg).QueryCache) :
    ProbComp (Option (Transcript pr Msg)) :=
  if ¬ z.1.1.TreeValid P.hsf then pure none else do
    let f ← $ᵗ (SkIdx P z.1.1 → pr.Y)
    let pkSl ← slKeygen pk
    let sk := skOf pr z.1.1 f
    let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk sk⟩
    let r ← (simulateQ (mode K sk) (stage2Prog pr Msg slKeygen A z.1.2 K)).run
      (St.init pr Msg z.2)
    return some (Transcript.ofRun pr Msg K r)

/-- **Game F.0** (the EU-CMA experiment of Definition 4.16 with the completion of Remark 4.6 and
`PK.seed` drawn first). -/
noncomputable def gameG {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ProbComp (Option (Transcript pr Msg)) := do
  let pk ← $ᵗ pr.PkSeed
  let z ← stage1 pr Msg slKeygen A
  stageG pr Msg slKeygen A (implG pr Msg) pk z

/-- **Game F.2**, lazy form: every signing digest is a fresh uniform value, programmed into the
random oracle at the signing query's input (the world `b = 1` of Definition C.2). -/
noncomputable def gameG2 {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ProbComp (Option (Transcript pr Msg)) := do
  let pk ← $ᵗ pr.PkSeed
  let z ← stage1 pr Msg slKeygen A
  stageG pr Msg slKeygen A (implG2 pr Msg) pk z

end Defs

/-! ## Honest data of the block games -/

section Honest

variable (pr : Primitives P)

/-- The honest data of a block game: the structure, `PK.seed`, the anchor values, and per anchor
the digest `y_j` and the WOTS+C signature `(c_j, σ_{j,0}, …, σ_{j,lsf−1})`. -/
structure Honest where
  /-- The structure. -/
  S : Structure
  /-- `PK.seed`. -/
  pk : pr.PkSeed
  /-- The anchor values (compressed WOTS+C public keys). -/
  leafVal : LeafId → pr.Y
  /-- The digest `y_j` of each anchor. -/
  dig : LeafId → pr.Digest
  /-- The WOTS+C signature of each anchor. -/
  wots : LeafId → WotsC.Sig pr

namespace Honest

variable {pr} (H : Honest pr)

/-- The honest node value `treeNode_structure(z, i)`. -/
def value (z i : ℕ) : Option pr.Y :=
  Tree.treeNode P.hsf H.S H.leafVal (Scheme.Fxmss.node pr H.pk) z i

/-- `PK.sf`. -/
def pkSf [Inhabited pr.Y] : pr.Y := (H.value P.hsf 0).getD default

/-- The honest encoded digest `d_j = H_grind(PK.seed, ADRS^g_j, y_j, c_j)`. -/
def encoded (id : LeafId) : pr.Y := WotsC.encode pr H.pk id (H.dig id) (H.wots id).ctr

/-- The honest uncompressed WOTS+C public key, completed from the blocks. -/
def tops (id : LeafId) : Vector pr.Y P.lsf :=
  WotsC.topsFromSig pr H.pk id (H.encoded id) (H.wots id)

/-- The revealed block `σ_{j,ch}`. -/
def block (id : LeafId) (ch : Fin P.lsf) : pr.Y := (H.wots id).chains[ch.val]

/-- The honest value of chain `ch` at position `p ≥ a_{j,ch}`, completed from the block. -/
def chainValue (id : LeafId) (ch : Fin P.lsf) (p : ℕ) : pr.Y :=
  WotsC.chain pr H.pk id ch.val (H.block id ch) (WotsC.digit pr (H.encoded id) ch.val)
    (p - WotsC.digit pr (H.encoded id) ch.val)

/-- The honest FXMSS signature at an anchor (as `Scheme.Fxmss.sign`: `⊥` when grinding fails). -/
def sig (id : LeafId) : Option (Scheme.Fxmss.Sig pr) :=
  (WotsC.grind pr H.pk id (H.dig id)).bind fun _ =>
    (Tree.authPath P.hsf H.S H.leafVal (Scheme.Fxmss.node pr H.pk) id.height id.index
      (P.hsf - id.height)).map fun auth => ⟨H.wots id, auth⟩

/-- Consistency of honest data: the tree has a root, and the honest signature at every anchor
recovers the anchor value under the honest digest. -/
structure Consistent : Prop where
  root : (H.value P.hsf 0).isSome
  sig : ∀ id ∈ leafIds P.hsf H.S,
    WotsC.pkFromSig pr H.pk id (H.dig id) (H.wots id) = some (H.leafVal id)

end Honest

/-- The value of block `σ_{j,ch}` with digit `a` in hybrid `γ` from the uniform value `v` at
position `m = min(γ, a − 1)`: `c_{m, a − m}(v)`. -/
def blockVal (pk : pr.PkSeed) (id : LeafId) (ch γ a : ℕ) (v : pr.Y) : pr.Y :=
  WotsC.chain pr pk id ch v (min γ (a - 1)) (a - min γ (a - 1))

/-- The block signature for an encoded digest `d` and counter `c` from a block source
`β id ch a`. -/
def blockSig (β : LeafId → ℕ → ℕ → pr.Y) (id : LeafId) (d : pr.Y) (c : Fin (2 ^ P.c)) :
    WotsC.Sig pr :=
  ⟨c, Vector.ofFn fun ch => β id ch.val (WotsC.digit pr d ch.val)⟩

/-- **The honest data of a block game** from the structure, `PK.seed`, the digests and a block
source `β id ch a` (the block of chain `ch` at anchor `id` for digit `a`). A failed counter search
(excluded by Conjecture 3.1) gives a dummy signature and the all-zero-digit completion. -/
def hon (S : Structure) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (β : LeafId → ℕ → ℕ → pr.Y) : Honest pr where
  S := S
  pk := pk
  dig := dig
  wots id := match WotsC.grind pr pk id (dig id) with
    | some (d, c) => blockSig pr β id d c
    | none => ⟨⟨0, Nat.two_pow_pos _⟩, Vector.ofFn fun ch => β id ch.val 0⟩
  leafVal id := match WotsC.grind pr pk id (dig id) with
    | some (d, c) => pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs
        (WotsC.topsFromSig pr pk id d (blockSig pr β id d c))
    | none => pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs
        (Vector.ofFn fun ch => WotsC.chain pr pk id ch.val (β id ch.val 0) 0 (P.w - 1))

end Honest

/-! ## The block games -/

section Hyb

variable (pr : Primitives P) (Msg : Type)
  [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg]
  [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg]
  [Inhabited pr.Digest]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- The `PK.seed`-independent setup of the block games: the structure phase, one digest per
anchor (`F.2`'s presampled `y_j`) and one uniform value per anchor and chain. -/
structure Setup (State : Type) where
  /-- The structure. -/
  S : Structure
  /-- The state of `A₁`. -/
  st : State
  /-- The random-oracle cache after `A₁`. -/
  cache : (roSpec pr Msg).QueryCache
  /-- The presampled digests `y_j`. -/
  ys : Anchor P S → pr.Digest
  /-- The uniform values `u_{j,i}`. -/
  u : SkIdx P S → pr.Y

/-- The setup of the block games: `A₁`, then `y ←$ Digest^A`, then `u ←$ Y^{A × [lsf]}`. -/
noncomputable def setupHyb {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ProbComp (Setup pr Msg A.State) := do
  let z ← stage1 pr Msg slKeygen A
  let ys ← $ᵗ (Anchor P z.1.1 → pr.Digest)
  let u ← $ᵗ (SkIdx P z.1.1 → pr.Y)
  return ⟨z.1.1, z.1.2, z.2, ys, u⟩

/-- The digest of an anchor from the presampled table (`default` off the anchors). -/
def digOf {S : Structure} (ys : Anchor P S → pr.Digest) (id : LeafId) : pr.Digest :=
  if h : id ∈ leafIds P.hsf S then ys ⟨id, h⟩ else default

/-- The block source of hybrid `γ` from the uniform values `u`. -/
def betaOf (γ : ℕ) {S : Structure} (pk : pr.PkSeed) (u : SkIdx P S → pr.Y) :
    LeafId → ℕ → ℕ → pr.Y :=
  fun id ch a => blockVal pr pk id ch γ a (skOf pr S u id ch)

/-- The signing mode of a block game with honest data `H`: the digest `y_j` is programmed, the
signature is the precomputed one. -/
def implHyb (K : Keys pr) (H : Honest pr) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp) :=
  impl pr Msg K (fun id x => progStep pr Msg x (H.dig id)) (fun id _ => H.sig id)

/-- The signing phase of a block game, for a block source `β` (a function of `PK.seed`). -/
noncomputable def stageHyb {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed) :
    ProbComp (Option (Transcript pr Msg × Honest pr)) :=
  if ¬ d.S.TreeValid P.hsf then pure none else do
    let pkSl ← slKeygen pk
    let H := hon pr d.S pk (digOf pr d.ys) β
    let K : Keys pr := ⟨d.S, pk, pkSl, H.pkSf⟩
    let r ← (simulateQ (implHyb pr Msg K H) (stage2Prog pr Msg slKeygen A d.st K)).run
      (St.init pr Msg d.cache)
    return some (Transcript.ofRun pr Msg K r, H)

/-- **The hybrid `F.3_γ`**: the block game with blocks `c_{m, a−m}(u)`, `m = min(γ, a − 1)`.
`gameHyb 0` is `F.2 = F.3` (secret key `u`), `gameHyb (w − 2)` is `F.4`. -/
noncomputable def gameHyb (γ : ℕ) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ProbComp (Option (Transcript pr Msg × Honest pr)) := do
  let pk ← $ᵗ pr.PkSeed
  let d ← setupHyb pr Msg slKeygen A
  stageHyb pr Msg slKeygen A (betaOf pr γ pk d.u) d pk

end Hyb

end ShrincsSecurity.Fxmss.Rom

end
