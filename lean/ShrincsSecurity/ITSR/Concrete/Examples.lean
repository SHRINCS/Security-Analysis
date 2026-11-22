module

public import ShrincsSecurity.ITSR.Concrete.Certify
import Mathlib.Tactic.NormNum

/-!
# The worked example `(h, t, k) = (1, 2, 2)`

`ITSR-Classical.pdf`, Section 3.3 (the values of `Γ_j`) and Section 4 (the comparison of
Theorems 1 and 2 after their statements). Here `θ = 2^-1 = 1/2` (`theta_fin_two_pow 1`).

* `(Γ_0(1), Γ_1(1), Γ_2(1)) = (1, 1/4, 1/8)` and `(Γ_0(2), Γ_1(2), Γ_2(2)) = (1, 7/16, 17/64)`;
* at `|K| = 4` and `q = 2`: the bound of Theorem 2 is `3/4` against `7/8` for Theorem 1 when
  `r = 1`, and `15/8` against `115/64` when `r = 2`, so neither theorem implies the other.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.Example

open Finset

theorem theta_eq : theta (Fin (2 ^ 1)) = 1 / 2 := by
  rw [theta_fin_two_pow]; norm_num

/-- Section 3.3: `(Γ_0(1), Γ_1(1), Γ_2(1)) = (1, 1/4, 1/8)` at `(h, t) = (1, 2)`. -/
theorem gamma_r1 :
    gamma (1 / 2) 2 1 0 = 1 ∧ gamma (1 / 2) 2 1 1 = 1 / 4 ∧ gamma (1 / 2) 2 1 2 = 1 / 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [gamma, sum_range_succ]

/-- Section 3.3: `(Γ_0(2), Γ_1(2), Γ_2(2)) = (1, 7/16, 17/64)` at `(h, t) = (1, 2)`. -/
theorem gamma_r2 :
    gamma (1 / 2) 2 2 0 = 1 ∧ gamma (1 / 2) 2 2 1 = 7 / 16 ∧ gamma (1 / 2) 2 2 2 = 17 / 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [gamma, sum_range_succ, Nat.choose]

/-- Section 4: at `(h, t, k) = (1, 2, 2)`, `|K| = 4`, `q = 2`, `r = 1`, the bound of Theorem 2 is
`3/4` and the bound of Theorem 1 is `7/8`. -/
theorem bounds_r1 : mainBound (1 / 2) 2 2 1 2 4 = 3 / 4 ∧ crudeBound (1 / 2) 2 2 1 2 4 = 7 / 8 := by
  have hI : Icc 1 (min 2 (min 2 1)) = {1} := by decide
  refine ⟨?_, ?_⟩
  · rw [mainBound, hI, sum_singleton]
    norm_num [searchTerm, pullTerm, pullHarm, gamma, sum_range_succ, Nat.choose,
      Nat.stirlingSecond, show Icc 1 2 = {1, 2} by decide]
  · norm_num [crudeBound, searchTerm, gamma, sum_range_succ]

/-- Section 4: at `(h, t, k) = (1, 2, 2)`, `|K| = 4`, `q = 2`, `r = 2`, the bound of Theorem 2 is
`15/8` and the bound of Theorem 1 is `115/64`. -/
theorem bounds_r2 :
    mainBound (1 / 2) 2 2 2 2 4 = 15 / 8 ∧ crudeBound (1 / 2) 2 2 2 2 4 = 115 / 64 := by
  have hI : Icc 1 (min 2 (min 2 2)) = {1, 2} := by decide
  refine ⟨?_, ?_⟩
  · rw [mainBound, hI]
    norm_num [searchTerm, pullTerm, pullHarm, gamma, sum_range_succ, Nat.choose,
      Nat.stirlingSecond, show Icc 1 2 = {1, 2} by decide, show Icc 2 2 = {2} by decide]
  · norm_num [crudeBound, searchTerm, gamma, sum_range_succ, Nat.choose]

end ShrincsSecurity.ITSR.Concrete.Example

end
