module

public import ShrincsSecurity.Concrete.Quantum.Generic
public import ShrincsSecurity.Concrete.Quantum.Enc
public import ShrincsSecurity.Concrete.Quantum.Paths
public import ShrincsSecurity.Concrete.Quantum.Figures
public import ShrincsSecurity.Concrete.Quantum.Comparison

/-!
# Section 6: concrete quantum security of the proposed parameters

Umbrella module for `ShrincsSecurity.Concrete.Quantum` (main paper, Section 6, quantum columns and
statements; the classical figures are in `ShrincsSecurity.Concrete`).

| Paper | Lean |
|---|---|
| Table 6, quantum column | `prfQ`, `smTcrQ`, `smPreQ` (= Undetectability Corollary 12, `smPreQ_corollary12`), `smUdQ` (= Undetectability Theorem 16, `smUdQ_theorem16`), `smTcrExclQ`, `sTcrPropQ`, `smDsprQ` (conjectured), `smRtcrQ` (Theorem G.1, Eqs. (16)–(18)), `itsrQ` (Theorems F.2, F.3) |
| Table 7, quantum columns; Corollary C.3 | `reproS`, `diReproQ`, `Form` (`one`, `half`, `ghhm`), `Form.factor` |
| `‡` note of Table 6 | `smUdQOld`, `smPreQOld`, `Rows` |
| Theorems 4.1–4.3 and Claim 6.3 (Eqs. (7), (8)), quantum, Section 6.3 | `slSumQ`, `sfSumQ`, `fullSumQ`; `slQ`, `sfQ`, `fullQ`; `slMin`, `sfMin`, `fullMin` |
| Claims 6.1, 6.2, 6.4, closed forms | `slQ_half_eq` (Eq. (2)), `sfQ_half_half_eq` (Eq. (4)), `sfQ_half_one_le` (Eq. (5)), `fullQ_half_half_half_eq` (Eq. (10)), `fullQ_half_half_one_le` (Eq. (11)) |
| Claims 6.1, 6.2, 6.4, rounded forms | `claim_6_1_rounded`, `claim_6_2_rounded_bx`, `claim_6_2_rounded_ux`, `claim_6_4_rounded_bx`, `claim_6_4_rounded_ux` |
| Claims 6.1, 6.2, 6.4, figures | `table5_sl_half`, `claim_6_2_figures_*`, `claim_6_4_figures_*`, `claim_6_2_switch_*`, `claim_6_4_switch_bx`, `claim_6_1_switch`, `claim_6_1_one_vs_half` |
| Table 5, quantum columns | `table5_sl_one`, `table5_sl_half`, `table5_sl_min`, `table5_sf_{bx,ux}_{one,half,min}`, `table5_full_{bx,ux}_{one,half,min}` |
| Section 6.1, abstract | `abstract_quantum`, `section_6_1_half_loss`, `section_6_1_core_min`, `section_6_1_core_one` |
| Remark 6.1, quantum | `remark_6_1_*_ghhm`, `remark_6_1_*_old_min`, `remark_6_1_*_old_ghhm`, `remark_6_1_ghhm_gain`, `remark_6_1_ghhm_sf`, `remark_6_1_ghhm_floor`, `remark_6_1_old_gain` |
| Footnote 15, quantum | `footnote_15_quantum` |
| Section 6.4, quantum items 1 and 3 | `section_6_4_quantum_verification`, `section_6_4_quantum_verification_doubled`, `section_6_4_quantum_msg`, `repro_growth_lt` |
-/
