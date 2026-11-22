module

public import VCVio.OracleComp.QueryTracking.QueryBound.Hazard
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The HRS framework for sets: average-case search

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), Appendix C, *HRS-Framework for Sets*:
**Definition C.3** (lines 6324–6342) and **Lemma C.6**, classical case (lines 6344–6350).

A function `f : S → {0, 1}` drawn from `D_λ` takes, independently at every point, the value `1`
with probability `λ`. We sample it lazily: the first evaluation at a point draws a fresh bit from
a sampler `bern : ProbComp Bool` and stores it, later evaluations read the stored bit. `D_λ` is the
case `Pr[bern = true] = λ`; the bound only needs `Pr[bern = true] ≤ λ`.

The adversary has private coins and at most `q` queries to `f`. It wins when `f(x) = 1` at its
output `x`, read through the same table; this final evaluation is the `+ 1` of `λ(q + 1)`.

## Main statements

* `AvgSearch.succ_le`: **Lemma C.6** (classical), `Succ^{Avg-Search_λ}(A) ≤ λ (q + 1)`.
* `AvgSearch.succ_bernUniform_le`: the instance `λ = 1/|N|` used for Theorem E.1.

The proof is the per-query hazard bound: a state is *bad* when the table holds a `1`; a fresh
draw makes it bad with probability at most `λ`, and a won game ends in a bad state.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

/-- One lazy evaluation of a table `tbl : X → Option V`: the stored value at `x`, or a fresh draw
from `fresh`, which is then stored. -/
def lazyStep {X V : Type} [DecidableEq X] (fresh : ProbComp V) (tbl : X → Option V) (x : X) :
    ProbComp (V × (X → Option V)) :=
  match tbl x with
  | some v => pure (v, tbl)
  | none => (fun v => (v, Function.update tbl x (some v))) <$> fresh

theorem mem_support_lazyStep {X V : Type} [DecidableEq X] {fresh : ProbComp V}
    {tbl : X → Option V} {x : X} {z : V × (X → Option V)}
    (hz : z ∈ support (lazyStep fresh tbl x)) :
    z.2 = Function.update tbl x (some z.1) ∧ (∀ v, tbl x = some v → z.1 = v) := by
  unfold lazyStep at hz
  cases h : tbl x with
  | some v =>
    rw [h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨(Function.update_eq_self_iff.2 h.symm).symm, fun _ h' => Option.some_inj.1 h'⟩
  | none =>
    rw [h] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨v, -, rfl⟩ := hz
    exact ⟨rfl, fun _ h' => nomatch h'⟩

namespace AvgSearch

variable (S : Type)

/-- Oracle access to the boolean function `f : S → {0, 1}`. -/
abbrev FSpec : OracleSpec S := S →ₒ Bool

/-- The adversary's oracles: private coins and `f`. -/
abbrev AdvSpec : OracleSpec (ℕ ⊕ S) := unifSpec + FSpec S

/-- A query to `f`. -/
def IsFQuery : ℕ ⊕ S → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred (IsFQuery S) := fun x => by
  rcases x with _ | _ <;> simp only [IsFQuery] <;> infer_instance

/-- An Avg-Search adversary making at most `q` queries to `f` on every execution path. -/
structure Adversary (q : ℕ) where
  /-- The adversary: it outputs a candidate `x ∈ S`. -/
  run : OracleComp (AdvSpec S) S
  /-- At most `q` queries to `f`. -/
  queryBound : run.IsQueryBoundP (IsFQuery S) q

variable {S} [DecidableEq S]

/-- The lazily sampled `f ← D_λ`: one evaluation reads the table or draws a fresh bit. -/
def fImpl (bern : ProbComp Bool) : QueryImpl (FSpec S) (StateT (S → Option Bool) ProbComp) :=
  fun x => StateT.mk fun tbl => lazyStep bern tbl x

/-- The experiment's handler: private coins and `f`. -/
def impl (bern : ProbComp Bool) : QueryImpl (AdvSpec S) (StateT (S → Option Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (S → Option Bool) ProbComp) +
    fImpl (S := S) bern

/-- **The Avg-Search experiment** of Definition C.3: run `A^f` and evaluate `f` at its output. -/
def experiment {q : ℕ} (bern : ProbComp Bool) (A : Adversary S q) : ProbComp Bool := do
  let z ← (simulateQ (impl bern) A.run).run fun _ => none
  let w ← lazyStep bern z.2 z.1
  return w.1

/-- **`Succ^{Avg-Search_λ}(A)`** (Definition C.3), with `f` drawn bitwise from `bern`. -/
noncomputable def succ {q : ℕ} (bern : ProbComp Bool) (A : Adversary S q) : ℝ≥0∞ :=
  Pr{let b ← experiment bern A}[b = true]

/-- The table holds a `1`. -/
def HasOne (tbl : S → Option Bool) : Prop := ∃ x, tbl x = some true

/-- **Lemma C.6** (classical case, `[HRS16]`, `[Kud25, Lemma 6.1.5]`). If each bit of `f` is `1`
with probability at most `λ`, an adversary making at most `q` queries to `f` finds a preimage of
`1` with probability at most `λ (q + 1)`. -/
theorem succ_le {q : ℕ} (bern : ProbComp Bool) {lam : ℝ≥0∞}
    (hbern : Pr{let b ← bern}[b = true] ≤ lam) (A : Adversary S q) :
    succ bern A ≤ lam * (q + 1) := by
  classical
  -- The adversary followed by the final evaluation of `f`.
  let oa : OracleComp (AdvSpec S) Bool :=
    A.run >>= fun x => liftM ((AdvSpec S).query (.inr x))
  have hoa : oa.IsQueryBoundP (IsFQuery S) (q + 1) :=
    isQueryBoundP_bind A.queryBound fun x _ =>
      (isQueryBoundP_query_iff (spec := AdvSpec S) (IsFQuery S) (.inr x) 1).2
        fun _ => Nat.one_pos
  have hrun : (simulateQ (impl bern) oa).run (fun _ => none) =
      (simulateQ (impl bern) A.run).run (fun _ => none) >>= fun z => lazyStep bern z.2 z.1 := by
    simp only [oa, simulateQ_bind, StateT.run_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, impl, QueryImpl.add_apply_inr]
    rfl
  have hhaz := prEvent_simulateQ_run_le_sum_of_isQueryBoundP (impl bern) (IsFQuery S)
    (fun _ => 0) (fun _ => True) HasOne (fun _ => lam) (fun _ _ _ => le_rfl)
    (QueryImpl.PreservesInv.trivial _)
    (by
      rintro (n | x) s hfree - hs z hz
      · refine ⟨rfl, ?_⟩
        simp only [impl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          QueryImpl.ofLift_apply, StateT.run_monadLift, support_bind,
          Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨_, -, rfl⟩ := hz
        exact hs
      · exact absurd trivial hfree)
    (fun _ _ _ _ _ _ _ => Nat.le_succ _)
    (by
      rintro (n | x) s hc - hs
      · exact absurd hc id
      · rw [impl, QueryImpl.add_apply_inr]
        change Pr{let z ← lazyStep bern s x}[HasOne z.2] ≤ lam
        unfold lazyStep
        cases h : s x with
        | some v =>
          simp only
          rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
            simp only [support_pure, Set.mem_singleton_iff] at hz
            exact hz ▸ hs]
          exact zero_le
        | none =>
          simp only
          rw [prEvent_map]
          refine le_trans (prEvent_mono _ _ _ fun b hb => ?_) hbern
          obtain ⟨y, hy⟩ := hb
          by_cases hyx : y = x
          · subst hyx
            simpa using hy
          · exact absurd ⟨y, by simpa [Function.update_of_ne hyx] using hy⟩ hs)
    oa hoa (fun _ => none) trivial (fun ⟨_, h⟩ => nomatch h)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    at hhaz
  rw [mul_comm]
  refine le_trans ?_ hhaz
  have hexp : experiment bern A = Prod.fst <$> (simulateQ (impl bern) oa).run fun _ => none := by
    rw [hrun, experiment, map_bind]
    simp only [bind_pure_comp]
  rw [succ, hexp, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun z hz hzb => ?_
  rw [hrun] at hz
  simp only [support_bind, Set.mem_iUnion] at hz
  obtain ⟨w, -, hz⟩ := hz
  obtain ⟨h1, -⟩ := mem_support_lazyStep hz
  exact ⟨w.1, by rw [h1, Function.update_self, hzb]⟩

/-- A bit that is `1` exactly when a uniform draw from `N` hits the fixed `y₀`: `λ = 1/|N|`. -/
def bernUniform {N : Type} [SampleableType N] [DecidableEq N] (y₀ : N) : ProbComp Bool :=
  (fun y => decide (y = y₀)) <$> ($ᵗ N)

theorem prEvent_bernUniform {N : Type} [SampleableType N] [DecidableEq N] [Fintype N] (y₀ : N) :
    Pr{let b ← bernUniform y₀}[b = true] = (Fintype.card N : ℝ≥0∞)⁻¹ := by
  rw [bernUniform, prEvent_map]
  simp only [decide_eq_true_eq]
  exact SampleableType.prEvent_uniformSample_eq_singleton y₀

/-- **Lemma C.6** (classical) for `Avg-Search_{1/|N|}`, the instance of Theorem E.1. -/
theorem succ_bernUniform_le {N : Type} [SampleableType N] [DecidableEq N] [Fintype N] (y₀ : N)
    {q : ℕ} (A : Adversary S q) :
    succ (bernUniform y₀) A ≤ (q + 1) / Fintype.card N := by
  rw [ENNReal.div_eq_inv_mul]
  exact succ_le _ (prEvent_bernUniform y₀).le A

end AvgSearch

end ShrincsSecurity.Notions.Generic

end
