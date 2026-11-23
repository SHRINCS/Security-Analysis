module

public import ShrincsSecurity.Concrete.Generic
public import ShrincsSecurity.Concrete.Conventions
public import ShrincsSecurity.Concrete.Paths
public import ShrincsSecurity.Concrete.Figures
public import ShrincsSecurity.Concrete.Comparison
public import ShrincsSecurity.Concrete.ConventionM

/-!
# Section 6: concrete classical security of the proposed parameters

Umbrella module for `ShrincsSecurity.Concrete` (main paper, Section 6, classical columns; see
`ShrincsSecurity.Concrete.Quantum.All` for the quantum columns).

| Paper | Lean |
|---|---|
| Table 6, classical column | `prfBound`, `smTcrBound`, `smPreBound`, `smUdBound`, `smTcrExclBound`, `sTcrPropBound`, `smDsprBound` (conjectured), `smRtcrBound`, `itsrBound` (= `ITSR.mainBound`) |
| Table 7, classical column | `pullSum` (itsr), `smRtcrRand`, `diReproBound` |
| Section 6.1, `ξ*` | `xiStar`, `xiStar_bracket` |
| Section 6.3 (conventions), Lemma 5.1 | `Vsf`, `Vsl`, `smax`, `SfCharge.uniform`, `SlCharge.uniform`, `Gam_le`, `le_Gam`, `epsDs` |
| Theorems 4.2, 4.3, Claim 6.3 Eq. (6) instantiated | `sfSum`, `slSum`, `fullSum`; `sfBound`, `slBound`, `fullBound` |
| Claims 6.1, 6.2, 6.4 (classical closed forms) | `slBound_eq`, `sfBound_eq`, `fullBound_eq`, `claim_6_*_affine` |
| Table 5, classical column | `table5_sl`, `table5_sf`, `table5_full` |
| Section 6.1 core levels | `section_6_1_core_*`, `section_6_1_repro_cost` |
| Section 6.4 constants | `sfBound_zero`, `slBound_zero`, `fullBound_zero`, `section_6_4_constants`, `section_6_4_crossover` |
| Footnote 15 | `footnote_15_units`, `footnote_15_values` |
| Remark 6.1 (classical) | `remark_6_1_F2_sl`, `remark_6_1_F2_full`, `remark_6_1_C2_sf`, `remark_6_1_C2_full`, `remark_6_1_all_full` |
| Section 6.8, Table 8 | `sfSum_budget`, `slSum_budget`, `table8_*`, `section_6_8_xiStar` |
-/
