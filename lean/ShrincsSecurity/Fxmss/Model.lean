module

public import ShrincsSecurity.Fxmss.Extraction
public import ShrincsSecurity.Notions.Signature
public import ShrincsSecurity.Scheme.Grinding
public import ShrincsSecurity.Repro.Defs
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# FXMSS in the random-oracle model: the scheme of Theorem 4.2

`SHRINCS-Security-Analysis.pdf`, **Definition 4.16** (FXMSS EU-CMA with idealized key generation)
and the setting of **Theorem 4.2** (`H_msg^sf` a random oracle, every other function a public
function of `PK.seed`).

This file instantiates the interface `Notions.FxmssScheme` with the typed scheme model of
`ShrincsSecurity.Scheme`:

* **The random oracle.** `H_msg^sf(R, PK.seed, PK.sf, idx, M)` is the oracle `roSpec` with input
  `(R, (PK.seed, PK.sf, idx, M))`: the randomness `R ∈ X₁ = Y` first and the remaining inputs
  `X₂ = PK.seed × Y × Idx × Msg` second, the input split of the reprogramming experiment
  (Definition C.2) used by Claim 4.2. `idx = toByte(z, 1) ‖ toByte(i, 8)` is the 9-byte leaf
  identifier `Idx = Fin 256 × Fin 2^64` (`toIdx`, injective on every leaf identifier the scheme
  signs or the verifier accepts). Messages range over an arbitrary finite type `Msg` (the bound
  messages of Section 3), so that `X₂` is finite, as Definition C.2 requires.
* **Idealized key generation** (`keygen`): `PK.seed ←$`, one uniform secret element per anchor
  and chain (`SkIdx S`, the anchors × chains of the structure, and nothing else), and `PK.sl`.
  `PK.sl` is modelled as an extra public value drawn by an arbitrary procedure
  `slKeygen : PK.seed → ProbComp Y`, independent of the FXMSS secrets: the stateless key
  generation of Definition 4.16 is such a procedure, and the proof never inspects it.
* **Signing** samples `R ←$ Y`, queries the random oracle for the digest and calls
  `Scheme.Fxmss.sign`; a failed counter search (impossible under Conjecture 3.1) is the `⊥`
  signature `(R, none)`. **Verification** queries the random oracle and runs
  `Scheme.Fxmss.pkFromSig`.

`Forger` is the adversary class of Theorem 4.2: an FXMSS EU-CMA adversary with `q_s` signing
queries, `q_{h,1}`/`q_{h,2}` random-oracle queries in its two stages, committing to structures
with at most `L` anchors.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

variable {P : Params}

/-- The 9-byte leaf identifier `idx = toByte(z*, 1) ‖ toByte(i*, 8)` (Section 2.2). -/
abbrev Idx : Type := Fin 256 × Fin (2 ^ 64)

/-- The leaf identifier bytes of a position `(z, i)`. -/
def toIdx (id : LeafId) : Idx := (Fin.ofNat 256 id.height, Fin.ofNat (2 ^ 64) id.index)

theorem toIdx_inj {a b : LeafId} (ha : a.height < 256) (ha' : a.index < 2 ^ 64)
    (hb : b.height < 256) (hb' : b.index < 2 ^ 64) (h : toIdx a = toIdx b) : a = b := by
  simp only [toIdx, Prod.mk.injEq, Fin.ext_iff, Fin.val_ofNat] at h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h
  exact LeafId.ext h.1 h.2

section Types

variable (pr : Primitives P) (Msg : Type)

/-- The second input `X₂ = (PK.seed, PK.sf, idx, M)` of `H_msg^sf`. -/
abbrev X2 : Type := pr.PkSeed × pr.Y × Idx × Msg

/-- The inputs `(R, (PK.seed, PK.sf, idx, M))` of `H_msg^sf`. -/
abbrev RoIn : Type := pr.Y × X2 pr Msg

/-- The random oracle `H_msg^sf : X₁ × X₂ → {0,1}^{2n}`, in the shape of `Repro.HashSpec`. -/
abbrev roSpec : OracleSpec (RoIn pr Msg) := Repro.HashSpec pr.Y (X2 pr Msg) pr.Digest

/-- The ambient oracles of the forger: private coins and `H_msg^sf`. -/
abbrev spec : OracleSpec (ℕ ⊕ RoIn pr Msg) := unifSpec + roSpec pr Msg

/-- The input of `H_msg^sf(R, PK.seed, PK.sf, idx, M)` for the leaf `id`. -/
def roIn (R : pr.Y) (pk : pr.PkSeed) (pkSf : pr.Y) (id : LeafId) (M : Msg) : RoIn pr Msg :=
  (R, (pk, pkSf, toIdx id, M))

/-- The public key `(PK.seed, PK.sl, PK.sf)`. -/
abbrev PK : Type := pr.PkSeed × pr.Y × pr.Y

/-- The FXMSS secret key of the idealized key generation. -/
structure SK where
  /-- The committed structure. -/
  S : Structure
  /-- `PK.seed`. -/
  pk : pr.PkSeed
  /-- The secret chain starts `sk_{(z,i), ch}`. -/
  sk : LeafId → ℕ → pr.Y
  /-- `PK.sf`. -/
  pkSf : pr.Y

/-- A signature `(R, σ_tree)`; `σ_tree = none` is `⊥` (a failed counter search). -/
abbrev Sig : Type := pr.Y × Option (Scheme.Fxmss.Sig pr)

/-- The secret-key index set of a structure: anchors × chains. -/
abbrev SkIdx (P : Params) (S : Structure) : Type := {id // id ∈ leafIds P.hsf S} × Fin P.lsf

/-- The anchors of a structure as a type (the signing leaves). -/
abbrev Anchor (P : Params) (S : Structure) : Type := {id // id ∈ leafIds P.hsf S}

variable [Inhabited pr.Y]

/-- The secret table `sk : LeafId → ℕ → Y` of a sample on anchors × chains. -/
def skOf (S : Structure) (f : SkIdx P S → pr.Y) : LeafId → ℕ → pr.Y := fun id ch =>
  if h : id ∈ leafIds P.hsf S ∧ ch < P.lsf then f (⟨id, h.1⟩, ⟨ch, h.2⟩) else default

/-- `PK.sf`, the root of the FXMSS tree (Algorithm 1); `default` for an invalid structure. -/
def pkSfOf (S : Structure) (pk : pr.PkSeed) (sk : LeafId → ℕ → pr.Y) : pr.Y :=
  (Scheme.Fxmss.root pr S pk sk).getD default

end Types

section Scheme

variable (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- **Idealized key generation** `K̃g(1ⁿ, Π)` (Definition 4.16, item 1): `PK.seed ←$`, a uniform
secret element for every chain of every anchor, `PK.sl ← slKeygen(PK.seed)`, and the FXMSS root
`PK.sf`. -/
noncomputable def keygen (S : Structure) : OracleComp (spec pr Msg) (PK pr × SK pr) := do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (spec pr Msg) pr.PkSeed)
  let f ← (liftM ($ᵗ (SkIdx P S → pr.Y) : ProbComp _) : OracleComp (spec pr Msg) _)
  let pkSl ← (liftM (slKeygen pk) : OracleComp (spec pr Msg) pr.Y)
  let sk := skOf pr S f
  let pkSf := pkSfOf pr S pk sk
  return ((pk, pkSl, pkSf), ⟨S, pk, sk, pkSf⟩)

/-- **Signing** `FXMSS.Sign(sk, M, (z*, i*))` (Definition 4.16, item 2): `R ←$ Y`,
`md = H_msg^sf(R, PK.seed, PK.sf, idx, M)`, and `σ_tree ← FXMSS.sign(md, …)`. -/
noncomputable def sign (k : SK pr) (M : Msg) (id : LeafId) : OracleComp (spec pr Msg) (Sig pr) := do
  let R ← (liftM ($ᵗ pr.Y : ProbComp pr.Y) : OracleComp (spec pr Msg) pr.Y)
  let md ← ((spec pr Msg).query (.inr (roIn pr Msg R k.pk k.pkSf id M)) :
    OracleComp (spec pr Msg) pr.Digest)
  return (R, Scheme.Fxmss.sign pr k.S k.pk k.sk md id)

/-- The verifier's decision on a recomputed digest. -/
def verifyWith (pk : pr.PkSeed) (pkSf : pr.Y) (id : LeafId) (σ : Option (Scheme.Fxmss.Sig pr))
    (md : pr.Digest) : Bool :=
  match σ with
  | some σ => decide (Scheme.Fxmss.pkFromSig pr pk md id σ = some pkSf)
  | none => false

/-- **Verification** `FXMSS.Verify(pk, M, (z*, i*), (R, σ_tree))`. -/
noncomputable def verify (pk : PK pr) (M : Msg) (id : LeafId) (σ : Sig pr) :
    OracleComp (spec pr Msg) Bool := do
  let md ← ((spec pr Msg).query (.inr (roIn pr Msg σ.1 pk.1 pk.2.2 id M)) :
    OracleComp (spec pr Msg) pr.Digest)
  return verifyWith pr pk.1 pk.2.2 id σ.2 md

/-- **FXMSS** as the scheme of Definition 4.16: shapes are structures, valid when they form a
valid tree (Section 2.5), and the signing leaves of a structure are its anchors. -/
noncomputable def scheme :
    Notions.FxmssScheme (spec pr Msg) Structure LeafId Msg (PK pr) (SK pr) (Sig pr) where
  ValidShape S := S.TreeValid P.hsf
  decValidShape := Classical.decPred _
  IsLeaf S id := id ∈ leafIds P.hsf S
  decIsLeaf _ := inferInstance
  keygen := keygen pr Msg slKeygen
  sign := sign pr Msg
  verify := verify pr Msg

/-- The random-oracle-model runtime: `H_msg^sf` is a lazily sampled random oracle. -/
noncomputable abbrev runtime : ProbCompRuntime (OracleComp (spec pr Msg)) :=
  ProbCompRuntime.rom (roSpec pr Msg)

/-- The forger's oracles in its signing phase. -/
abbrev fullSpec := spec pr Msg + Notions.FxmssScheme.signSpec Msg LeafId (Sig pr)

/-- A query to `H_msg^sf` in the structure phase. -/
def IsRoQuery : ℕ ⊕ RoIn pr Msg → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred (IsRoQuery pr Msg) := fun x => by
  rcases x with _ | _ <;> simp only [IsRoQuery] <;> infer_instance

/-- A query to `H_msg^sf` in the signing phase. -/
def IsRoQuery' : (ℕ ⊕ RoIn pr Msg) ⊕ (Msg × LeafId) → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred (IsRoQuery' pr Msg) := fun x => by
  rcases x with (_ | _) | _ <;> simp only [IsRoQuery'] <;> infer_instance

/-- **The forgers of Theorem 4.2**: FXMSS EU-CMA adversaries with at most `q_s` signing queries,
at most `q_{h,1}` and `q_{h,2}` queries to `H_msg^sf` in the two stages (`q_h = q_{h,1} + q_{h,2}`),
committing to structures with at most `L` anchors (and so at most `I = L − 1` internal nodes). -/
structure Forger (qs qh₁ qh₂ L : ℕ) extends
    Notions.FxmssAdversary (scheme pr Msg slKeygen) qs where
  /-- At most `q_{h,1}` random-oracle queries in the structure phase. -/
  roBound₁ : chooseShape.IsQueryBoundP (IsRoQuery pr Msg) qh₁
  /-- At most `q_{h,2}` random-oracle queries in the signing phase. -/
  roBound₂ : ∀ st S pk, (forge st S pk).IsQueryBoundP (IsRoQuery' pr Msg) qh₂
  /-- Every valid committed structure has at most `L` anchors. -/
  anchors_le : ∀ z ∈ support chooseShape, z.1.TreeValid P.hsf → z.1.anchors.card ≤ L

/-- `Succ^{FXMSS-EU-CMA}_{FXMSS,q_s}(A)` in the random-oracle model. -/
noncomputable abbrev succ {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ℝ≥0∞ :=
  (scheme pr Msg slKeygen).succ (runtime pr Msg) A

end Scheme

end ShrincsSecurity.Fxmss.Rom

end
