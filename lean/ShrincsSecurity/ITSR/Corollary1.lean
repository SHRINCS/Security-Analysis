module

public import ShrincsSecurity.ITSR.Theorem2
public import ShrincsSecurity.ITSR.OnePull

/-!
# Corollary 1 of `ITSR-Classical.pdf` (one-pull form)

The bound of Theorem 2 with the summand `m = 1` written as the expected increment of the covered
set: `Succ ≤ (q + 1) Γ_k(r) + r q (q + 1) E[Δ*] / (|K| N') + R₂`, `N' = |ι| t^k`.
-/

@[expose] public section

open OracleComp
open scoped ENNReal

namespace ShrincsSecurity.ITSR

/-- **Corollary 1** (one-pull form). -/
theorem advantage_le_onePull {K M : Type} [DecidableEq K] [DecidableEq M] [SampleableType K]
    [Fintype K] {ι : Type} [Fintype ι] [DecidableEq ι] [SampleableType ι] {k t : ℕ} [NeZero t]
    {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    advantage A ≤ ENNReal.ofReal
      (searchTerm (theta ι) t k r q +
        (r : ℝ) * q * (q + 1) * expectedDelta ι k t r /
          ((Fintype.card K : ℝ) * ((Fintype.card ι : ℝ) * (t : ℝ) ^ k)) +
        remainderTwo (theta ι) t k r q (Fintype.card K)) := by
  have : Nonempty ι := SampleableType.nonempty ι
  rw [← mainBound_eq_onePull]
  exact advantage_le_mainBound A

end ShrincsSecurity.ITSR

end
