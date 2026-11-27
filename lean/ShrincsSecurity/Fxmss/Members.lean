module

public import ShrincsSecurity.Fxmss.Events
public import ShrincsSecurity.Notions.Collection

/-!
# The attacked functions and problems of Claims 4.3–4.9

`SHRINCS-Security-Analysis.pdf`, Section 4.7, Claims 4.3–4.9, and Section 4.3 (collections).

Each claim attacks one function of the collection `Th_λ` (`pr.collection`, the six members of
SHRINCS) with `Th_λ` itself as the collection the reduction may evaluate:

| claim | function | problem | targets |
|---|---|---|---|
| 4.3 | `H_grind ∈ Th_λ`, counters in `ℕ` (`thGrind`) | S-TCR(Prop), `Prop` = target sum | `q_s ≤ L` |
| 4.4 | `F ∈ Th_λ` (`thF`) | SM-UD (uniform inputs and outputs) | `q₁ ≤ L · lsf` |
| 4.5 | `F ∈ Th_λ` | SM-TCR | `q₂ ≤ L · lsf · w` |
| 4.6 | `F ∈ Th_λ` | SM-PRE | `q₁ ≤ L · lsf` |
| 4.7 | `Th_lsf ∈ Th_λ` (`thLsf`) | SM-TCR | `q₄ ≤ L` |
| 4.8 | `H ∈ Th_λ` (`thH`) | SM-TCR | `q₃ ≤ I = L − 1` |
| 4.9 | `Th_{2∪lsf}` against `Th_λ` (`thExcl`) | sm-tcr-excl with `ω` (`shrincsX`) | `q₅ ≤ L + I` |

The public parameter is `PK.seed ←$` (`TweakableHash.ofFun`). `H_grind` is extended to counters
`i ∈ ℕ` (as Definition 4.8 requires) by reading the counter modulo `2^c`; the challenge oracle's
least valid counter is then the scheme's, below `2^c` under Conjecture 3.1.

`shrincsX` is the tweak data of Claim 4.9 on the common address format: `T₂` the addresses of
type `SF_FXMSS_TREE`, `T₃` those of type `SF_WOTS_C_PK`, `T₁` the rest, and `ω` replaces the type
byte (`Scheme.omega`, `Scheme.omegaInv`), keeping the node identifier and the payload.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash
open SLHDSA (Adrs)

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions

variable {P : Params} (pr : Primitives P) [SampleableType pr.PkSeed]

/-- `F ∈ Th_λ` with `PK.seed ←$`. -/
noncomputable def thF : TweakableHash pr.PkSeed Adrs pr.Y pr.Y :=
  TweakableHash.ofFun fun pk a x => pr.F pk a x

/-- `H ∈ Th_λ` with `PK.seed ←$`. -/
noncomputable def thH : TweakableHash pr.PkSeed Adrs (pr.Y × pr.Y) pr.Y :=
  TweakableHash.ofFun fun pk a x => pr.H pk a x.1 x.2

/-- `Th_lsf ∈ Th_λ` with `PK.seed ←$`. -/
noncomputable def thLsf : TweakableHash pr.PkSeed Adrs (Vector pr.Y P.lsf) pr.Y :=
  TweakableHash.ofFun fun pk a x => pr.ThLsf pk a x

/-- `H_grind ∈ Th_λ` on message–counter pairs `(md, i)`, `i ∈ ℕ` read modulo `2^c`. -/
noncomputable def thGrind : TweakableHash pr.PkSeed Adrs (pr.Digest × ℕ) pr.Y :=
  TweakableHash.ofFun fun pk a x => pr.Hgrind pk a x.1 ⟨x.2 % 2 ^ P.c, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `Th_{2∪lsf}`: `H` on pairs, `Th_lsf` on `lsf`-tuples. -/
noncomputable def thExcl :
    TweakableHash pr.PkSeed Adrs ((pr.Y × pr.Y) ⊕ Vector pr.Y P.lsf) pr.Y :=
  TweakableHash.ofFun fun pk a x => match x with
    | .inl lr => pr.H pk a lr.1 lr.2
    | .inr v => pr.ThLsf pk a v

/-- The WOTS+C target-sum predicate `Prop` of Claim 4.3. -/
def targetSumProp : pr.Y → Bool := fun y => decide (WotsC.TargetSum pr y)

/-! ## The tweak data of Claim 4.9 -/

/-- The class of an address: `T₂` (tree nodes), `T₃` (WOTS+C compressions) or `T₁`. -/
def shrincsCls (a : Adrs) : TweakClass :=
  if a.type = SfType.fxmssTree.toCode then .two
  else if a.type = SfType.wotsCPk.toCode then .three else .one

/-- `ω` on `T₂`, `ω⁻¹` on `T₃`, the identity on `T₁`. -/
def shrincsPartner (a : Adrs) : Adrs :=
  if a.type = SfType.fxmssTree.toCode then omega a
  else if a.type = SfType.wotsCPk.toCode then omegaInv a else a

/-- **The tweak partition of Claim 4.9**: `T₂ = SF_FXMSS_TREE`, `T₃ = SF_WOTS_C_PK`, and
`ω` exchanges the two type bytes at the same node identifier. -/
def shrincsX : ExclusiveTweaks Adrs where
  cls := shrincsCls
  partner := shrincsPartner
  partner_partner a := by
    obtain ⟨l, t, ty, w1, w2, w3⟩ := a
    unfold shrincsPartner
    by_cases h18 : ty = SfType.fxmssTree.toCode
    · subst h18; simp [omega, omegaInv, SfType.toCode]
    · by_cases h17 : ty = SfType.wotsCPk.toCode
      · subst h17; simp [omega, omegaInv, SfType.toCode]
      · simp [h18, h17]
  cls_partner a := by
    unfold shrincsCls shrincsPartner
    by_cases h18 : a.type = SfType.fxmssTree.toCode
    · simp [h18, omega, SfType.toCode, TweakClass.swap]
    · by_cases h17 : a.type = SfType.wotsCPk.toCode
      · simp [h17, omegaInv, SfType.toCode, TweakClass.swap]
      · simp [h18, h17, TweakClass.swap]
  partner_of_one a h := by
    unfold shrincsCls at h
    unfold shrincsPartner
    split_ifs at h ⊢; simp_all

@[simp] theorem shrincsX_partner_treeAdrs (id : LeafId) :
    shrincsX.partner (SfAdrs.treeAdrs id).toAdrs = (SfAdrs.pkAdrs id).toAdrs := by
  simp [shrincsX, shrincsPartner, SfAdrs.treeAdrs, SfAdrs.toAdrs, omega, SfAdrs.pkAdrs]

@[simp] theorem shrincsX_partner_pkAdrs (id : LeafId) :
    shrincsX.partner (SfAdrs.pkAdrs id).toAdrs = (SfAdrs.treeAdrs id).toAdrs := by
  simp [shrincsX, shrincsPartner, SfAdrs.treeAdrs, SfAdrs.toAdrs, omegaInv, SfAdrs.pkAdrs,
    SfType.toCode]

/-! ## The problems -/

/-- Claim 4.3: S-TCR(Prop) of `H_grind ∈ Th_λ` with `p` targets. -/
noncomputable abbrev probGrind (p : ℕ) :=
  sTcrMemberProblem (thGrind pr) (targetSumProp pr) pr.collection p

/-- Claim 4.4: SM-UD of `F ∈ Th_λ` with `p` targets. -/
noncomputable abbrev probUD [SampleableType pr.Y] (p : ℕ) :=
  smUdMemberProblem (thF pr) pr.collection p

/-- Claim 4.5: SM-TCR of `F ∈ Th_λ` with `p` targets. -/
noncomputable abbrev probTcrF (p : ℕ) := smTcrMemberProblem (thF pr) pr.collection p

/-- Claim 4.6: SM-PRE of `F ∈ Th_λ` with `p` targets. -/
noncomputable abbrev probPre (p : ℕ) := smPreMemberProblem (thF pr) pr.collection p

/-- Claim 4.7: SM-TCR of `Th_lsf ∈ Th_λ` with `p` targets. -/
noncomputable abbrev probTcrLsf (p : ℕ) := smTcrMemberProblem (thLsf pr) pr.collection p

/-- Claim 4.8: SM-TCR of `H ∈ Th_λ` with `p` targets. -/
noncomputable abbrev probTcrH (p : ℕ) := smTcrMemberProblem (thH pr) pr.collection p

/-- Claim 4.9: sm-tcr-excl of `Th_{2∪lsf}` against `Th_λ` with `p` targets. -/
noncomputable abbrev probExcl (p : ℕ) :=
  smTcrExclCollectionProblem (thExcl pr) shrincsX pr.collection p

end ShrincsSecurity.Fxmss.Rom

end
