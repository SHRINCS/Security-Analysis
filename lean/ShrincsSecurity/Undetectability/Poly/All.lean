module

public import ShrincsSecurity.Undetectability.Poly.Markov
public import ShrincsSecurity.Undetectability.Poly.PlantedFamily
public import ShrincsSecurity.Undetectability.Poly.Boolean
public import ShrincsSecurity.Undetectability.Poly.Acceptance

/-!
# Polynomial method of the quadratic sm-ud bound (classical part)

Umbrella module for the pure-mathematics part of `notes/txt/Undetectability.txt`:

| Paper | Lean | File |
|---|---|---|
| Lemma 3 (Markov), endpoint form | `abs_derivative_eval_one_le`, `abs_derivative_eval_neg_one_le`, `abs_derivative_eval_zero_le_of_unitInterval` | `Markov` |
| Lemma 7 (planted family) | `planted_family`, `planted_family_event`, `planted_family_real` | `PlantedFamily` |
| Section 4.1, `D_λ`, `E_k`, equation (3) | `boolWeight`, `sliceWeight`, `boolExpect_eq_mixture`, `sliceExpect_zero`, `sliceExpect_one` | `Boolean` |
| Lemma 14 (events on few points) | `events_on_few_points`, `natDegree_boolExpectPoly_comp_le` | `Boolean` |
| Lemma 1 (conclusion, as hypothesis) | `IsMarginalLinear`, `IsMarginalLinear.expect_eq` | `Acceptance` |
| Lemma 15 (degree) | `isPolyOnUnitInterval_planted_of_marginalLinear` | `Acceptance` |
| Theorem 16 / Lemma 8 given Lemma 1 | `planted_bound_of_marginalLinear_two_mul`, `zero_vs_one_marked_of_marginalLinear` | `Acceptance` |

The interior form of Lemma 3 (`|h'(t)| ≤ d²` for all `t ∈ [-1, 1]`) is not formalised; no result
of the paper uses it.
-/
