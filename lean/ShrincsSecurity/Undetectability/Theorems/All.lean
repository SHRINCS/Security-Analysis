module

public import ShrincsSecurity.Undetectability.Marginal.Basic
public import ShrincsSecurity.Undetectability.Marginal.Comb
public import ShrincsSecurity.Undetectability.Theorems.SmUd
public import ShrincsSecurity.Undetectability.Theorems.SmPre

/-!
# Quantum part of the quadratic sm-ud bound

Umbrella module for Lemma 1 and the game-level results of `notes/txt/Undetectability.txt`, on top
of the polynomial method in `ShrincsSecurity.Undetectability.Poly.All`:

| Paper | Lean | File |
|---|---|---|
| Lemma 1, bookkeeping | `IsMarginalPoly`, `IsMarginalPoly.smul`, `IsMarginalPoly.mono` | `Marginal/Basic` |
| Lemma 1, combs | `QuantumComb.isMarginalLinear_outcome`, `TwoStageAdversary.isMarginalLinear_outProb` | `Marginal/Comb` |
| Definition 4 (sm-ud) | `smUdReal`, `smUdRand`, `smUdAdv` | `Theorems/SmUd` |
| Appendix A.1, planted family | `plantedOracle`, `plantedEndpoint`, `plantedFamily`, `plantedFamily_eq_mixture` | `Theorems/SmUd` |
| Lemma 13 (endpoints) | `plantedEndpoint_zero`, `plantedEndpoint_one` | `Theorems/SmUd` |
| Lemma 15 (degree), game form | `isPolyOnUnitInterval_plantedFamily` | `Theorems/SmUd` |
| Theorem 16 | `smUdAdv_le_of_marginalLinear`, `TwoStageAdversary.smUdAdv_le` | `Theorems/SmUd` |
| Theorem 9 | `TwoStageAdversary.smUdAdv_le_xor` | `Theorems/SmUd` |
| Definitions 5, 6 | `TwoStageAdversary.succPre`, `TwoStageAdversary.succOw` | `Theorems/SmPre` |
| Lemma 11 | `TwoStageAdversary.lemma11`, `TwoStageAdversary.isMarginalLinear_hopAccept` | `Theorems/SmPre` |
| Corollary 12 (Lemma 10 as hypothesis) | `TwoStageAdversary.corollary12`, `TwoStageAdversary.corollary12_xor` | `Theorems/SmPre` |

Program model: VCVio quantum combs (fixed query slots, arbitrary instruments between them, final
measurement) with the standard oracle `Quantum.oracleUnitary` over an additive commutative group;
see the module docstrings of `Marginal/Comb` and `Theorems/SmUd`.
-/
