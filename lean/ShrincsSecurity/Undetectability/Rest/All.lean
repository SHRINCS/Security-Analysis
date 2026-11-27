module

public import ShrincsSecurity.Undetectability.Rest.Lemma8Comb
public import ShrincsSecurity.Undetectability.Rest.SelectionOracle
public import ShrincsSecurity.Undetectability.Rest.ReproHalf

/-!
# Remaining results: Lemma 8 for combs, Lemma 2, Corollaries C.1 and C.3

| Paper | Lean | File |
|---|---|---|
| Undetectability, Lemma 8 (combs) | `QuantumComb.zero_vs_one_marked`, `QuantumComb.zero_vs_one_marked_zmod2`, `IsMarginalLinear.comp_injective` | `Lemma8Comb` |
| Undetectability, Lemma 2 (one query per selection) | `Selection.selection_mulVec_single`, `Selection.selection_mul_ancillaEmbed`, `Selection.selection_one_query_linearMap`, `Selection.selection_two_values` | `SelectionOracle` |
| Undetectability, proof of Lemma 2: first and second facts | `Selection.hadamard_mul_phase_mul_hadamard`, `Selection.phase_kickback` | `SelectionOracle` |
| Main, Remark C.4 | `ReproHalf.remarkC4` | `ReproHalf` |
| Main, Corollary C.1 (Lemma C.3 as hypothesis) | `ReproHalf.corollaryC1` | `ReproHalf` |
| Main, Corollary C.3 (QROM lines; Lemmas C.1, C.3 as hypotheses) | `ReproHalf.corollaryC3_adv_le`, `ReproHalf.corollaryC3_adv_le_min`, `ReproHalf.corollaryC3_half`, `ReproHalf.corollaryC3_class_adv_le` | `ReproHalf` |
-/
