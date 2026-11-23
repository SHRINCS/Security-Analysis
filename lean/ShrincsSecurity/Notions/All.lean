module

public import ShrincsSecurity.Notions.PRF
public import ShrincsSecurity.Notions.MultiTarget
public import ShrincsSecurity.Notions.TweakPartition
public import ShrincsSecurity.Notions.TCRExcl
public import ShrincsSecurity.Notions.STCR
public import ShrincsSecurity.Notions.ITSR
public import ShrincsSecurity.Notions.Collection
public import ShrincsSecurity.Notions.Signature
public import ShrincsSecurity.Notions.Generic.AvgSearch
public import ShrincsSecurity.Notions.Generic.ZeroDist
public import ShrincsSecurity.Notions.Generic.HiddenSlice
public import ShrincsSecurity.Notions.Generic.ExclusiveTweaks
public import ShrincsSecurity.Notions.Generic.RandomSamplingTCR
public import ShrincsSecurity.Notions.Generic.CollectionLemma
public import ShrincsSecurity.Notions.Generic.IndependentFunctions

/-!
# Security notions of the main paper, Sections 4.2–4.5, and their classical generic bounds

Umbrella module for `ShrincsSecurity.Notions`:

| Paper | Lean | Origin |
|---|---|---|
| Def. 4.1 keyed hash | `Notions.KeyedHash` | fresh (abbreviation) |
| Def. 4.2 tweakable hash | `TweakableHash`, `TweakableHash.ofFun`, `UniformSeed` | VCVio |
| Def. 4.3 PRF | `Notions.prfAdv` = `PRFScheme.prfAdvantage` | VCVio |
| Def. 4.4 SM-TCR | `Notions.smTcrSucc` = `SM_DT_TCR_Advantage` | VCVio |
| Def. 4.5 SM-PRE | `Notions.smPreSucc`; printed form `smPrePaperExperiment` (proved equal) | VCVio |
| Def. 4.6 SM-UD | `Notions.smUdAdv` = `SM_DT_UD_Advantage` (absolute) | VCVio |
| Def. 4.7 sm-tcr-excl | `Notions.SMTCRExcl_Experiment`, `ExclusiveTweaks` | fresh |
| Def. 4.8 S-TCR(Prop) | `Notions.STCR_Experiment` | fresh |
| Def. 4.9 SM-rTCR | `Notions.smRtcrSucc` = `SM_DT_RTCR_Advantage` | VCVio |
| Def. 4.10 SM-DSPR | `Notions.smDsprAdv` = `SM_DT_DSPR_Advantage` (`max(0, succ − triv)`) | VCVio |
| Def. 4.11 ITSR | `Notions.itsrSucc`; proved equal to `KeyedHash.ITSRAdvantage` | fresh + VCVio |
| Def. 4.12 collections | `Notions.*MemberProblem`, lifts in `Notions.Collection` | VCVio + fresh |
| Defs. 4.13/4.14 | `SignatureAlg`, `Notions.euCmaSucc` | VCVio |
| Def. 4.15 SHRINCS EU-CMA | `Notions.ShrincsScheme.succ` | fresh (interface) |
| Def. 4.16 FXMSS EU-CMA | `Notions.FxmssScheme.succ` | fresh (interface) |

The classical random-oracle generic bounds (Appendices C, D, E, G) are in
`ShrincsSecurity.Notions.Generic`:

| Paper | Lean |
|---|---|
| Def. C.3, Lemma C.6 (classical) | `Generic.AvgSearch.succ_le`, `succ_bernUniform_le` |
| Def. C.4, Lemma C.7 | `Generic.ZeroDist.advantage_le` |
| Lemma C.9 (classical) | `Generic.HiddenSlice.abs_game_sub_le`, `abs_game_sub_eq_advantage` |
| Lemma 4.1 (i) (classical, ideal collection) | `Generic.CollectionLemma.prEvent_game0_collInterface_le`, SM-TCR instance `prEvent_smtcrCollGame_le` |
| Lemma 4.2 (classical, independent functions) | `Generic.IndependentFunctions.gameExt_eq_game_dropExt`, `smtcrGameExt_eq`, `diAdvantageExt_eq` |
| Thm. E.1 (classical) | `Generic.SmTcrExcl.succ_le`, `succ_le_of_le_each`, `succ_le_of_le` |
| Cor. G.1 | `Generic.RandomSamplingTCR.advantage_le`, `advantage_le_of_one` |
-/
