module

public import ShrincsSecurity.Scheme.Params
public import ShrincsSecurity.Scheme.Address
public import HashSig.SLHDSA.Primitives
public import VCVio.CryptoFoundations.TweakableHash

/-!
# SHRINCS function families

`SHRINCS-Security-Analysis.pdf`, Section 2.2 ("Cryptographic (Hash) Function Families"),
Definitions 4.1 and 4.2, Assumption 4.1 (the five named random objects).

The scheme is parametric in its function families, which are the fields of `Primitives`:

* the tweakable-hash collection `Th_λ` keyed by the shared public seed: one variable-arity function
  `Th : PK.seed → ADRS → Y^ℓ → Y` whose restrictions to message length `ℓ ∈ {1, 2, k, lsl, lsf}`
  are the members `F`, `H`, `Th_k`, `Th_lsl`, `Th_lsf` ("the message length determines the
  member"), together with the grinding hash `H_grind`, the sixth member, whose tweak is a
  `SF_WOTS_C_GRIND` address and whose message is a pair `(md, ctr)`;
* the PRF for secret values `PRF(PK.seed, SK.seed, ADRS)`;
* the combined randomizer function `PRF_msg(SK.prf, b, ·)` with selector `b ∈ {sl, sf}`, whose
  two restrictions are `PRF_msg^sl` and `PRF_msg^sf` (Section 2.2, "Randomizer generation");
* the message digests `H_msg^sl` (truncated to the `m` bits consumed by the stateless path) and
  `H_msg^sf`.

The carrier types are abstract, mirroring VCVio's `SLHDSA.Primitives`; no byte layout is modelled.
`Primitives.toSLHDSA` packages the stateless restrictions as a VCVio `SLHDSA.Primitives` bundle at
`P.slParams`, with tweak space the common address format, so that the stateless path *is* VCVio's
SLH-DSA development and its `F`, `H`, `T_ℓ` are definitionally SHRINCS's `F`, `H`, `Th_ℓ`.
`Primitives.collection` exposes the six members as a VCVio `TweakableHashCollection`.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme

open SLHDSA (Adrs Byte Bytes)

/-- The input of the combined randomizer function `PRF_msg` (Section 2.2): the selector `b` and
the arguments of the selected variant. -/
inductive PrfMsgInput (PkSeed Y : Type) where
  /-- `PRF_msg^sl(SK.prf, opt_rand, M)`. -/
  | sl (optRand : Y) (msg : List Byte)
  /-- `PRF_msg^sf(SK.prf, PK.seed, idx, M)`. -/
  | sf (pkSeed : PkSeed) (idx : LeafId) (msg : List Byte)

/-- The function families of SHRINCS (Section 2.2), with abstract carrier types. -/
structure Primitives (P : Params) where
  /-- Public seed `PK.seed`. -/
  PkSeed : Type
  /-- Secret seed `SK.seed`. -/
  SkSeed : Type
  /-- Randomizer key `SK.prf`. -/
  SkPrf : Type
  /-- `n`-bit values: chain values, tree nodes, roots, randomizers, encoded digests. -/
  Y : Type
  /-- `2n`-bit message digests `md` produced by `H_msg^sf`. -/
  Digest : Type
  /-- The tweakable-hash collection `Th_λ` without `H_grind`: `Th(PK.seed, ADRS, M_ℓ)`. -/
  Th : PkSeed → Adrs → List Y → Y
  /-- The grinding hash `H_grind(PK.seed, ADRS, md, ctr)`. -/
  Hgrind : PkSeed → Adrs → Digest → Fin (2 ^ P.c) → Y
  /-- `PRF(PK.seed, SK.seed, ADRS)`. -/
  PRF : PkSeed → SkSeed → Adrs → Y
  /-- The combined randomizer function `PRF_msg`. -/
  PRFmsg : SkPrf → PrfMsgInput PkSeed Y → Y
  /-- `H_msg^sl(R, PK.seed, PK.sl, M)`, truncated to the `m` bits consumed by the stateless path. -/
  HmsgSl : Y → PkSeed → Y → List Byte → Bytes P.slParams.m
  /-- `H_msg^sf(R, PK.seed, PK.sf, idx, M)`. -/
  HmsgSf : Y → PkSeed → Y → LeafId → List Byte → Digest
  /-- The `n/8`-byte encoding of an `n`-bit value (used for digits and for `PK.sf ‖ M`). -/
  yToBytes : Y → Bytes P.slParams.n

namespace Primitives

variable {P : Params} (pr : Primitives P)

/-- `F = Th_1`. -/
def F (pk : pr.PkSeed) (a : Adrs) (x : pr.Y) : pr.Y := pr.Th pk a [x]

/-- `H = Th_2`. -/
def H (pk : pr.PkSeed) (a : Adrs) (l r : pr.Y) : pr.Y := pr.Th pk a [l, r]

/-- `Th_k`, compressing the `k` FORS roots. -/
def ThK (pk : pr.PkSeed) (a : Adrs) (v : Vector pr.Y P.k) : pr.Y := pr.Th pk a v.toList

/-- `Th_lsl`, compressing WOTS-TW public keys. -/
def ThLsl (pk : pr.PkSeed) (a : Adrs) (v : Vector pr.Y P.lsl) : pr.Y := pr.Th pk a v.toList

/-- `Th_lsf`, compressing WOTS+C public keys. -/
def ThLsf (pk : pr.PkSeed) (a : Adrs) (v : Vector pr.Y P.lsf) : pr.Y := pr.Th pk a v.toList

/-- `PRF_msg^sl`, the stateless restriction of `PRF_msg`. -/
def PRFmsgSl (key : pr.SkPrf) (optRand : pr.Y) (msg : List Byte) : pr.Y :=
  pr.PRFmsg key (.sl optRand msg)

/-- `PRF_msg^sf`, the stateful restriction of `PRF_msg`. -/
def PRFmsgSf (key : pr.SkPrf) (pk : pr.PkSeed) (idx : LeafId) (msg : List Byte) : pr.Y :=
  pr.PRFmsg key (.sf pk idx msg)

/-- The stateless restrictions as a VCVio SLH-DSA primitive bundle at `P.slParams`. The tweak
space is the common address format (`AdrsKey := Adrs`, `adrsToKey := id`), so VCVio's
`F`/`H`/`T_ℓ` are SHRINCS's `F`/`H`/`Th_ℓ`. -/
@[reducible] def toSLHDSA : SLHDSA.Primitives P.slParams where
  PkSeed := pr.PkSeed
  SkSeed := pr.SkSeed
  SkPrf := pr.SkPrf
  Y := pr.Y
  AdrsKey := Adrs
  adrsToKey := id
  PRF := pr.PRF
  PRFmsg := pr.PRFmsgSl
  yToBytes := pr.yToBytes
  Thash := pr.Th
  Hmsg := pr.HmsgSl

@[simp] theorem toSLHDSA_F (pk : pr.PkSeed) (a : Adrs) (x : pr.Y) :
    pr.toSLHDSA.F pk a x = pr.F pk a x := rfl

@[simp] theorem toSLHDSA_H (pk : pr.PkSeed) (a : Adrs) (l r : pr.Y) :
    pr.toSLHDSA.H pk a l r = pr.H pk a l r := rfl

@[simp] theorem toSLHDSA_Tl (pk : pr.PkSeed) (a : Adrs) (xs : List pr.Y) :
    pr.toSLHDSA.Tl pk a xs = pr.Th pk a xs := rfl

/-! ## The collection `Th_λ` (Section 2.2, Section 4.3) -/

/-- The six members of the SHRINCS tweakable-hash collection. -/
inductive Member where
  /-- `F = Th_1`: chains (both paths) and FORS leaves. -/
  | F
  /-- `H = Th_2`: internal nodes of every Merkle tree. -/
  | H
  /-- `Th_k`: FORS root compression. -/
  | thK
  /-- `Th_lsl`: WOTS-TW public-key compression. -/
  | thLsl
  /-- `Th_lsf`: WOTS+C public-key compression. -/
  | thLsf
  /-- `H_grind`: WOTS+C digest grinding. -/
  | grind
deriving DecidableEq, Repr

/-- The message type of each member. -/
def MemberMsg : Member → Type
  | .F => pr.Y
  | .H => pr.Y × pr.Y
  | .thK => Vector pr.Y P.k
  | .thLsl => Vector pr.Y P.lsl
  | .thLsf => Vector pr.Y P.lsf
  | .grind => pr.Digest × Fin (2 ^ P.c)

/-- Evaluation of each member. -/
def memberEval : (i : Member) → pr.PkSeed → Adrs → pr.MemberMsg i → pr.Y
  | .F => fun pk a x => pr.F pk a x
  | .H => fun pk a x => pr.H pk a x.1 x.2
  | .thK => fun pk a x => pr.ThK pk a x
  | .thLsl => fun pk a x => pr.ThLsl pk a x
  | .thLsf => fun pk a x => pr.ThLsf pk a x
  | .grind => fun pk a x => pr.Hgrind pk a x.1 x.2

/-- The collection `Th_λ` as a VCVio `TweakableHashCollection` over the common tweak space. -/
def collection : TweakableHashCollection Member pr.PkSeed Adrs pr.Y where
  Msg := pr.MemberMsg
  eval := pr.memberEval

/-- A single member as a VCVio `TweakableHash`, given the public-seed sampler. -/
def member (seedGen : ProbComp pr.PkSeed) (i : Member) :
    TweakableHash pr.PkSeed Adrs (pr.MemberMsg i) pr.Y where
  seedGen := seedGen
  eval := pr.memberEval i

/-- The members `Th_ℓ` with `ℓ ∈ {1, 2, k, lsl, lsf}` occupy pairwise disjoint inputs of `Th`
(Section 2.2: "the message length determines the member"), as their message lengths are pairwise
distinct at the SHRINCS parameters. -/
theorem shrincs_member_lengths_nodup :
    [1, 2, shrincs.k, shrincs.lsl, shrincs.lsf].Nodup := by
  decide

end Primitives

end ShrincsSecurity.Scheme
