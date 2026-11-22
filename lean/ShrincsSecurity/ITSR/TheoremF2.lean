module

public import ShrincsSecurity.ITSR.Theorem1

/-!
# Theorem F.2 of the main paper (classical part)

`SHRINCS-Security-Analysis.pdf`, Appendix F.2: for `p` challenge and `q` direct queries,
`Succ^itsr ≤ p (q + p + 1) / |K| + (q + 1) Γ`. The paper proves it by adaptive reprogramming; in the
classical random-oracle model it follows from Theorem 1 of `ITSR-Classical.pdf`, whose pull term
`p · min(q, |K|) / |K|` is at most `p (q + p + 1) / |K|`.

The statement is for the experiment of `Game.lean`, whose random oracle outputs uniform digests.
The paper's `H : K × {0,1}^α → {0,1}^m` composed with `MAP_{h,k,t}` is such an oracle when `MAP`
has fibres of equal size (Remark F.1), which holds at the proposed parameters.
-/

@[expose] public section

open OracleComp
open scoped ENNReal

namespace ShrincsSecurity.ITSR

/-- **Theorem F.2**, classical part. -/
theorem advantage_le_theoremF2 {K M : Type} [DecidableEq K] [DecidableEq M] [SampleableType K]
    [Fintype K] {ι : Type} [Fintype ι] [DecidableEq ι] [SampleableType ι] {k t : ℕ} [NeZero t]
    {q p : ℕ} (A : Adversary K M (Digest ι k t) q p) :
    advantage A ≤ ENNReal.ofReal
      ((p : ℝ) * (q + p + 1) / Fintype.card K + (q + 1) * gamma (theta ι) t p k) := by
  refine (advantage_le_crudeBound A).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [crudeBound, searchTerm, add_comm]
  gcongr
  exact_mod_cast (min_le_left q (Fintype.card K)).trans (by omega)

end ShrincsSecurity.ITSR

end
