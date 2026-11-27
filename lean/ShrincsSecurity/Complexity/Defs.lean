module

public import ShrincsSecurity.Slhdsa.Theorem43
public import ShrincsSecurity.Shrincs.Theorem41

/-!
# Formal Stage-2 `Th_λ`-evaluation complexity tracking (`Complexity/Defs.lean`)

Main Paper, Section 4.6–4.8 and Lemma 5.1: every reduction `B` from a `ξ`-query adversary `A`
(making at most `ξ` Stage-2 evaluations of the tweakable-hash collection `Th_λ`) incurs at most:
* `ξ̃_sl ≤ ξ + V_sl` Stage-2 `Th_λ` evaluations for every stateless collection reduction
  (`V_sl = 2741` at SHRINCS parameters, `Slhdsa.Vsl`), and
* `ξ̃_sf ≤ ξ + V_sf` Stage-2 `Th_λ` evaluations for every stateful collection reduction
  (`V_sf = 497` at SHRINCS parameters, `VerifyCount.Vsf`).

## Architecture

1. **Explicit Stage-2 `Th_λ` oracle (`Stage2ThSpec`, `stage2ThImpl`)**: augments `unifSpec` with
   `Slhdsa.thSpec pr` (all six members of `Th_λ`: `F, H, Th_k, Th_lsl, Th_lsf, H_grind`). Erasing
   the `thSpec` queries via `pr.memberEval pk` (`stage2ThImpl pr pk`) recovers `ProbComp`.
2. **Stage-2 hash-evaluation bound witness (`Stage2ThBound`)**: for any Stage-2 procedure
   `stage2 : St → pr.PkSeed → ProbComp Out`, witnesses an explicit-`Stage2ThSpec` program `progM`
   such that:
   * `simulateQ (stage2ThImpl pr pk) (progM st pk) = stage2 st pk` (exact equality with the actual
     reduction's Stage 2), and
   * `(progM st pk).IsQueryBoundP (IsThQuery pr) budget` (worst-case `Th_λ` evaluation bound).
3. **Universal budgeted-adversary lifting (`WithThSpec`, `liftStateThImpl`, `liftStateThPassImpl`)**:
   any adversary whose Stage-2 computation is given over `spec + thSpec pr` with `≤ ξ` `Th_λ`
   queries can be simulated through any `Th_λ`-free `StateT σ ProbComp` handler (e.g., Stage-1
   precomputed signing tables) in `≤ ξ` Stage-2 `Th_λ` queries, or forwarded through any `Th_λ`-free
   `StateT σ (OracleComp spec₂)` adapter (e.g., `slAdvWrapImpl`, `slSimImpl`, `AFTable`) while
   preserving the `≤ ξ` `Th_λ`-query bound identically.
4. **Budgeted adversary classes**: `BudgetedPostPrfAdv`, `BudgetedSlhdsaAdv`, `BudgetedFxmssForger`,
   and `BudgetedShrincsForger`, together with zero-overhead liftings `.toPostPrf` and `.toAFTable`
   matching `Slhdsa.slPostPrfAdv`, `Shrincs.shrincsSlAdv`, and `Shrincs.AFTable` definitionally.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Complexity

open Scheme Slhdsa Shrincs

/-! ## 1. Explicit Stage-2 `Th_λ` oracle specification and erasure -/

section Stage2Oracle

variable {P : Params} (pr : Primitives P)

/-- Stage-2 oracle specification: private coins (`unifSpec`) plus explicit `Th_λ` evaluations
(`Slhdsa.thSpec pr`). -/
abbrev Stage2ThSpec : OracleSpec (ℕ ⊕ ThQuery pr) :=
  unifSpec + thSpec pr

/-- Predicate selecting `Th_λ` queries in `Stage2ThSpec pr`. -/
def IsThQuery : (Stage2ThSpec pr).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (IsThQuery pr) := fun q => by
  rcases q with _ | _ <;> simp only [IsThQuery] <;> infer_instance

/-- Erasure of `Stage2ThSpec pr` back to `ProbComp` by evaluating `Th_λ` at `pk`. -/
def stage2ThImpl (pk : pr.PkSeed) : QueryImpl (Stage2ThSpec pr) ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr q => pure (thRealImpl pr pk q)

/-- Lift a `Th_λ`-free `ProbComp` into `OracleComp (Stage2ThSpec pr)`. -/
def liftProb {α : Type} (p : ProbComp α) : OracleComp (Stage2ThSpec pr) α :=
  simulateQ (fun n => (Stage2ThSpec pr).query (.inl n)) p

/-- Lift a pure explicit-`thSpec` computation into `OracleComp (Stage2ThSpec pr)`. -/
def liftTh {α : Type} (oa : OracleComp (thSpec pr) α) : OracleComp (Stage2ThSpec pr) α :=
  simulateQ (fun q => (Stage2ThSpec pr).query (.inr q)) oa

theorem simulateQ_stage2ThImpl_liftProb (pk : pr.PkSeed) {α : Type} (p : ProbComp α) :
    simulateQ (stage2ThImpl pr pk) (liftProb pr p) = p := by
  unfold liftProb
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, stage2ThImpl]
    exact bind_congr fun x => ih x

theorem simulateQ_stage2ThImpl_liftTh (pk : pr.PkSeed) {α : Type} (oa : OracleComp (thSpec pr) α) :
    simulateQ (stage2ThImpl pr pk) (liftTh pr oa) =
      pure (Id.run (simulateQ (thRealImpl pr pk) oa)) := by
  unfold liftTh
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, stage2ThImpl, pure_bind, Id.run_bind]
    exact ih (thRealImpl pr pk q)

theorem isQueryBoundP_liftProb {α : Type} (p : ProbComp α) :
    (liftProb pr p).IsQueryBoundP (IsThQuery pr) 0 := by
  unfold liftProb
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [IsThQuery]), fun u => ?_⟩
    simp only [IsThQuery, ↓reduceIte]
    exact ih u

theorem isQueryBoundP_liftTh {α : Type} {oa : OracleComp (thSpec pr) α} {n : ℕ}
    (h : IsTotalQueryBound oa n) :
    (liftTh pr oa).IsQueryBoundP (IsThQuery pr) n := by
  unfold liftTh
  have h' : oa.IsQueryBoundP (fun _ => True) n := (isQueryBoundP_true_iff oa n).2 h
  clear h
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at h'
    obtain ⟨hn, hk⟩ := h'
    have hpos : 0 < n := hn.resolve_left (not_not.2 trivial)
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr hpos, fun y => ?_⟩
    simp only [IsThQuery, ↓reduceIte]
    exact ih y (by simpa using hk y)

end Stage2Oracle

/-! ## 2. Universal budgeted oracle-program lifting (`WithThSpec`) -/

section WithTh

variable {P : Params} (pr : Primitives P)

/-- Augment any oracle specification `spec` with explicit `Th_λ` queries (`thSpec pr`). -/
abbrev WithThSpec {ι : Type} (spec : OracleSpec ι) : OracleSpec (ι ⊕ ThQuery pr) :=
  spec + thSpec pr

/-- Predicate selecting the explicit `Th_λ` queries in `WithThSpec pr spec`. -/
def IsRightThQuery {ι : Type} (spec : OracleSpec ι) : (WithThSpec pr spec).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance {ι : Type} (spec : OracleSpec ι) : DecidablePred (IsRightThQuery pr spec) := fun q => by
  rcases q with _ | _ <;> simp only [IsRightThQuery] <;> infer_instance

/-- Erase the explicit `Th_λ` oracle of `WithThSpec pr spec` by evaluating `pr.memberEval pk`. -/
def eraseThImpl {ι : Type} (spec : OracleSpec ι) (pk : pr.PkSeed) :
    QueryImpl (WithThSpec pr spec) (OracleComp spec)
  | .inl t => liftM (spec.query t)
  | .inr q => pure (thRealImpl pr pk q)

/-- Lift a `spec`-only computation into `WithThSpec pr spec` (`0` explicit `Th_λ` queries). -/
def liftLeftWithTh {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α) :
    OracleComp (WithThSpec pr spec) α :=
  simulateQ (fun t => (liftM ((WithThSpec pr spec).query (.inl t)) :
    OracleComp (WithThSpec pr spec) _)) oa

theorem simulateQ_eraseThImpl_liftLeft {ι : Type} {spec : OracleSpec ι} (pk : pr.PkSeed)
    {α : Type} (oa : OracleComp spec α) :
    simulateQ (eraseThImpl pr spec pk) (liftLeftWithTh pr oa) = oa := by
  unfold liftLeftWithTh
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, eraseThImpl]
    exact bind_congr fun x => ih x

theorem isQueryBoundP_liftLeftWithTh {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) :
    (liftLeftWithTh pr oa).IsQueryBoundP (IsRightThQuery pr spec) 0 := by
  unfold liftLeftWithTh
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [IsRightThQuery]), fun u => ?_⟩
    simp only [IsRightThQuery, ↓reduceIte]
    exact ih u

/-- Lift a `Th_λ`-free stateful handler `impl : QueryImpl spec (StateT σ ProbComp)` to handle
`WithThSpec pr spec` in `StateT σ (OracleComp (Stage2ThSpec pr))`, forwarding `.inr` (`Th_λ`)
queries directly to `Stage2ThSpec pr`. -/
def liftStateThImpl {ι σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (WithThSpec pr spec) (StateT σ (OracleComp (Stage2ThSpec pr)))
  | .inl q => StateT.mk fun s => liftProb pr ((impl q).run s)
  | .inr q => StateT.mk fun s => (fun y => (y, s)) <$> (Stage2ThSpec pr).query (.inr q)

/-- **Exact erasure theorem for `liftStateThImpl`**: erasing Stage-2 `Th_λ` queries after running
a budgeted adversary through a `Th_λ`-free stateful handler recovers the exact `ProbComp` run on
the erased adversary. -/
theorem simulateQ_stage2ThImpl_runStateTh {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (pk : pr.PkSeed)
    (oa : OracleComp (WithThSpec pr spec) α) (s : σ) :
    simulateQ (stage2ThImpl pr pk) ((simulateQ (liftStateThImpl pr impl) oa).run s) =
      (simulateQ impl (simulateQ (eraseThImpl pr spec pk) oa)).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with q | q
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftStateThImpl,
        StateT.run_mk, eraseThImpl]
      rw [simulateQ_stage2ThImpl_liftProb]
      refine bind_congr fun z => ih z.1 z.2
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftStateThImpl,
        StateT.run_mk, eraseThImpl, pure_bind, bind_map_left]
      simp only [stage2ThImpl, pure_bind]
      exact ih (thRealImpl pr pk q) s

/-- **Query-bound preservation for `liftStateThImpl`**: running a `ξ`-`Th_λ`-query program through
any `Th_λ`-free `StateT σ ProbComp` handler issues at most `ξ` Stage-2 `Th_λ` queries. -/
theorem isQueryBoundP_runStateTh {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    {oa : OracleComp (WithThSpec pr spec) α} {ξ : ℕ}
    (h : oa.IsQueryBoundP (IsRightThQuery pr spec) ξ) (s : σ) :
    ((simulateQ (liftStateThImpl pr impl) oa).run s).IsQueryBoundP (IsThQuery pr) ξ := by
  induction oa using OracleComp.inductionOn generalizing s ξ with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    obtain ⟨hξ, hk⟩ := h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with q | q
    · simp only [IsRightThQuery, ↓reduceIte] at hk
      simp only [liftStateThImpl, StateT.run_mk]
      exact (isQueryBoundP_bind (n := 0) (m := ξ) (isQueryBoundP_liftProb pr _)
        fun z _ => ih z.1 (hk z.1) z.2).mono (by omega)
    · have hpos : 0 < ξ := hξ.resolve_left (not_not.2 trivial)
      simp only [IsRightThQuery, ↓reduceIte] at hk
      simp only [liftStateThImpl, StateT.run_mk, bind_map_left]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr hpos, fun y => ?_⟩
      simp only [IsThQuery, ↓reduceIte]
      exact ih y (hk y) s

/-- Lift a `Th_λ`-free adapter `impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))` to an
adapter `QueryImpl (WithThSpec pr spec₁) (StateT σ (OracleComp (WithThSpec pr spec₂)))` that
passes `.inr` (`Th_λ`) queries straight through. -/
def liftStateThPassImpl {ι₁ ι₂ σ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) :
    QueryImpl (WithThSpec pr spec₁) (StateT σ (OracleComp (WithThSpec pr spec₂)))
  | .inl q => StateT.mk fun s => liftLeftWithTh pr ((impl q).run s)
  | .inr q => StateT.mk fun s => (fun y => (y, s)) <$> (WithThSpec pr spec₂).query (.inr q)

/-- **Exact erasure theorem for `liftStateThPassImpl`**: erasing `Th_λ` after passing through a
`Th_λ`-free adapter equals running the adapter on the erased program. -/
theorem simulateQ_eraseTh_runStatePass {ι₁ ι₂ σ α : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))) (pk : pr.PkSeed)
    (oa : OracleComp (WithThSpec pr spec₁) α) (s : σ) :
    simulateQ (eraseThImpl pr spec₂ pk) ((simulateQ (liftStateThPassImpl pr impl) oa).run s) =
      (simulateQ impl (simulateQ (eraseThImpl pr spec₁ pk) oa)).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with q | q
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftStateThPassImpl,
        StateT.run_mk, eraseThImpl]
      rw [simulateQ_eraseThImpl_liftLeft]
      exact bind_congr fun z => ih z.1 z.2
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftStateThPassImpl,
        StateT.run_mk, eraseThImpl, pure_bind, bind_map_left]
      exact ih (thRealImpl pr pk q) s

/-- **Query-bound preservation for `liftStateThPassImpl`**: passing a `ξ`-`Th_λ`-query program
through any `Th_λ`-free adapter preserves the `≤ ξ` `Th_λ`-query bound identically. -/
theorem isQueryBoundP_runStatePass {ι₁ ι₂ σ α : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    {oa : OracleComp (WithThSpec pr spec₁) α} {ξ : ℕ}
    (h : oa.IsQueryBoundP (IsRightThQuery pr spec₁) ξ) (s : σ) :
    ((simulateQ (liftStateThPassImpl pr impl) oa).run s).IsQueryBoundP
      (IsRightThQuery pr spec₂) ξ := by
  induction oa using OracleComp.inductionOn generalizing s ξ with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    obtain ⟨hξ, hk⟩ := h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with q | q
    · simp only [IsRightThQuery, ↓reduceIte] at hk
      simp only [liftStateThPassImpl, StateT.run_mk]
      exact (isQueryBoundP_bind (n := 0) (m := ξ) (isQueryBoundP_liftLeftWithTh pr _)
        fun z _ => ih z.1 (hk z.1) z.2).mono (by omega)
    · have hpos : 0 < ξ := hξ.resolve_left (not_not.2 trivial)
      simp only [IsRightThQuery, ↓reduceIte] at hk
      simp only [liftStateThPassImpl, StateT.run_mk, bind_map_left]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr hpos, fun y => ?_⟩
      simp only [IsRightThQuery, ↓reduceIte]
      exact ih y (hk y) s

end WithTh

/-! ## 3. Stage-2 `Th_λ`-evaluation bound witness (`Stage2ThBound`) -/

section Stage2Bound

variable {P : Params} (pr : Primitives P)

/-- **Stage-2 `Th_λ`-evaluation bound witness**: certifies that the Stage-2 procedure
`stage2 : St → pr.PkSeed → ProbComp Out` of a two-stage collection reduction is realized by an
explicit-`Stage2ThSpec` program `progM` issuing at most `budget` evaluations of `Th_λ` on every
execution path. -/
structure Stage2ThBound {St Out : Type} (stage2 : St → pr.PkSeed → ProbComp Out) (budget : ℕ) where
  /-- Explicit-`Th_λ`-oracle Stage-2 program. -/
  progM : St → pr.PkSeed → OracleComp (Stage2ThSpec pr) Out
  /-- Erasing `Th_λ` via `pr.memberEval pk` recovers `stage2` identically. -/
  simulate_eq : ∀ st pk, simulateQ (stage2ThImpl pr pk) (progM st pk) = stage2 st pk
  /-- At most `budget` `Th_λ` queries on every execution path. -/
  queryBound : ∀ st pk, (progM st pk).IsQueryBoundP (IsThQuery pr) budget

/-- Monotonicity of `Stage2ThBound` in the budget. -/
def Stage2ThBound.mono {St Out : Type} {stage2 : St → pr.PkSeed → ProbComp Out} {b₁ b₂ : ℕ}
    (hb : Stage2ThBound pr stage2 b₁) (hle : b₁ ≤ b₂) : Stage2ThBound pr stage2 b₂ where
  progM := hb.progM
  simulate_eq := hb.simulate_eq
  queryBound st pk := (hb.queryBound st pk).mono hle

/-- Post-composition by a pure (`0`-`Th_λ`-query) function preserves `Stage2ThBound`. -/
def Stage2ThBound.map {St Out Out' : Type} {stage2 : St → pr.PkSeed → ProbComp Out} {b : ℕ}
    (hb : Stage2ThBound pr stage2 b) (f : St → pr.PkSeed → Out → Out') :
    Stage2ThBound pr (fun st pk => f st pk <$> stage2 st pk) b where
  progM st pk := f st pk <$> hb.progM st pk
  simulate_eq st pk := by
    rw [map_eq_bind_pure_comp, simulateQ_bind, hb.simulate_eq st pk]
    simp [map_eq_bind_pure_comp]
  queryBound st pk := by
    rw [isQueryBoundP_map_iff]
    exact hb.queryBound st pk

/-- Sequential composition of a Stage-2 simulation (`≤ ξ` `Th_λ` queries) with a deterministic
explicit-`thSpec` post-processing extractor (`≤ V` `Th_λ` queries) yields `≤ ξ + V`. -/
def Stage2ThBound.bindTh {St Mid Out : Type}
    {sim : St → pr.PkSeed → ProbComp Mid} {ξ V : ℕ}
    (hsim : Stage2ThBound pr sim ξ)
    (extM : St → pr.PkSeed → Mid → OracleComp (thSpec pr) Out)
    (hext : ∀ st pk mid, IsTotalQueryBound (extM st pk mid) V) :
    Stage2ThBound pr
      (fun st pk => (fun mid => Id.run (simulateQ (thRealImpl pr pk) (extM st pk mid))) <$>
        sim st pk)
      (ξ + V) where
  progM st pk := do
    let mid ← hsim.progM st pk
    liftTh pr (extM st pk mid)
  simulate_eq st pk := by
    rw [simulateQ_bind, hsim.simulate_eq st pk, map_eq_bind_pure_comp]
    refine bind_congr fun mid => ?_
    exact simulateQ_stage2ThImpl_liftTh pr pk (extM st pk mid)
  queryBound st pk :=
    isQueryBoundP_bind (hsim.queryBound st pk) fun mid _ =>
      isQueryBoundP_liftTh pr (hext st pk mid)

/-! ### Convenience aliases for all six two-stage collection adversary interfaces -/

/-- Stage-2 `Th_λ`-evaluation bound for an `SM-TCR` reduction (`A.forge`). -/
abbrev TcrStage2Bound {ι T M N : Type} {prob : SM_DT_TCR_Problem ι pr.PkSeed T M N}
    (A : SM_DT_TCR_Adversary prob) (budget : ℕ) :=
  Stage2ThBound pr A.forge budget

/-- Stage-2 `Th_λ`-evaluation bound for an `SM-PRE` reduction (`A.invert`). -/
abbrev PreStage2Bound {ι T M M' N : Type} {prob : SM_DT_PRE_Problem ι pr.PkSeed T M M' N}
    (A : SM_DT_PRE_Adversary prob) (budget : ℕ) :=
  Stage2ThBound pr A.invert budget

/-- Stage-2 `Th_λ`-evaluation bound for an `SM-UD` reduction (`A.distinguish`). -/
abbrev UdStage2Bound {ι T M M' N : Type} {prob : SM_DT_UD_Problem ι pr.PkSeed T M M' N}
    (A : SM_DT_UD_Adversary prob) (budget : ℕ) :=
  Stage2ThBound pr A.distinguish budget

/-- Stage-2 `Th_λ`-evaluation bound for an `SM-DSPR` reduction (`A.guess`). -/
abbrev DsprStage2Bound {ι T M N : Type} {prob : SM_DT_DSPR_Problem ι pr.PkSeed T M N}
    (A : SM_DT_DSPR_Adversary prob) (budget : ℕ) :=
  Stage2ThBound pr A.guess budget

/-- Stage-2 `Th_λ`-evaluation bound for an `S-TCR(Prop)` reduction (`A.forge`). -/
abbrev STcrStage2Bound {ι T M N : Type} {prob : Notions.STCRProblem ι pr.PkSeed T M N}
    (A : Notions.STCRAdversary prob) (budget : ℕ) :=
  Stage2ThBound pr A.forge budget

/-- Stage-2 `Th_λ`-evaluation bound for an `SM-TCR-EXCL` reduction (`A.forge`). -/
abbrev ExclStage2Bound {ι T M N : Type} {prob : Notions.SMTCRExclProblem ι pr.PkSeed T M N}
    (A : Notions.SMTCRExclAdversary prob) (budget : ℕ) :=
  Stage2ThBound pr A.forge budget

end Stage2Bound

/-! ## 4. Budgeted adversary classes (`≤ ξ` Stage-2 `Th_λ` evaluations) -/

section BudgetedAdversaries

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- A `qs`-query post-PRF stateless adversary whose Stage-2 computation makes at most `ξ` explicit
`Th_λ` evaluations. -/
structure BudgetedPostPrfAdv (D E : Type) (qs ξ : ℕ) extends PostPrfAdv pr D E qs where
  /-- Explicit-`Th_λ`-oracle version of `run`. -/
  runM : D → E → pr.PkSeed → pr.Y →
    OracleComp (WithThSpec pr (SlAdvSpec pr)) (Option (List SLHDSA.Byte × Stateless.Sig pr))
  /-- Erasing explicit `Th_λ` queries recovers `run` identically. -/
  runM_eq : ∀ d sf pk pkSl, simulateQ (eraseThImpl pr (SlAdvSpec pr) pk) (runM d sf pk pkSl) =
    run d sf pk pkSl
  /-- At most `ξ` `Th_λ` evaluations on every execution path. -/
  thBound : ∀ d sf pk pkSl, (runM d sf pk pkSl).IsQueryBoundP (IsRightThQuery pr (SlAdvSpec pr)) ξ

/-- A standalone SLH-DSA EU-CMA adversary (`Theorem 4.3`) whose main execution makes at most `ξ`
explicit `Th_λ` evaluations. -/
structure BudgetedSlhdsaAdv (Msg : Type) (enc : MsgEnc Msg)
    [DecidableEq pr.Y] [SampleableType pr.Y] [SampleableType pr.PkSeed]
    [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] (qs ξ : ℕ) extends
    Notions.EUCMAAdversary (slhdsaScheme pr Msg enc) qs where
  /-- Explicit-`Th_λ`-oracle version of `adv.main`. -/
  mainM : pr.PkSeed × pr.Y →
    OracleComp (WithThSpec pr (SlStandaloneSpec pr Msg)) (Msg × Stateless.Sig pr)
  /-- Erasing explicit `Th_λ` queries recovers `adv.main` identically. -/
  mainM_eq : ∀ pk pkSl,
    simulateQ (eraseThImpl pr (SlStandaloneSpec pr Msg) pk) (mainM (pk, pkSl)) =
      adv.main (pk, pkSl)
  /-- At most `ξ` `Th_λ` evaluations on every execution path. -/
  thBound : ∀ pk pkSl,
    (mainM (pk, pkSl)).IsQueryBoundP (IsRightThQuery pr (SlStandaloneSpec pr Msg)) ξ

/-- Lift a `BudgetedSlhdsaAdv` to a `BudgetedPostPrfAdv` whose underlying `PostPrfAdv` is
definitionally `Slhdsa.slPostPrfAdv`. -/
noncomputable def BudgetedSlhdsaAdv.toPostPrf {Msg : Type} {enc : MsgEnc Msg}
    [DecidableEq pr.Y] [SampleableType pr.Y] [SampleableType pr.PkSeed]
    [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq Msg] {qs ξ : ℕ}
    (A : BudgetedSlhdsaAdv pr Msg enc qs ξ) :
    BudgetedPostPrfAdv pr Unit Unit qs ξ where
  toPostPrfAdv := slPostPrfAdv pr Msg enc A.toEUCMAAdversary
  runM _ _ pk pkSl := do
    let ((m, σ), log) ← (simulateQ (liftStateThPassImpl pr (slAdvWrapImpl pr Msg enc))
      (A.mainM (pk, pkSl))).run []
    return (if m ∉ log then some (pureMsg Msg enc m, σ) else none)
  runM_eq _ _ pk pkSl := by
    simp only [slPostPrfAdv, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_eraseTh_runStatePass, A.mainM_eq pk pkSl]
    exact bind_congr fun _ => by simp
  thBound _ _ pk pkSl := by
    rw [bind_pure_comp, isQueryBoundP_map_iff]
    exact isQueryBoundP_runStatePass pr (slAdvWrapImpl pr Msg enc) (A.thBound pk pkSl) []

/-- An FXMSS forger (`Theorem 4.2`) whose Stage-2 `forge` procedure makes at most `ξ` explicit
`Th_λ` evaluations. -/
structure BudgetedFxmssForger {P : Params} (pr : Primitives P) (Msg : Type)
    [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
    [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg]
    (slKeygen : pr.PkSeed → ProbComp pr.Y) (qs qh₁ qh₂ L ξ : ℕ) extends
    Fxmss.Rom.Forger pr Msg slKeygen qs qh₁ qh₂ L where
  /-- Explicit-`Th_λ`-oracle version of `forge`. -/
  forgeM : State → Structure → Fxmss.Rom.PK pr →
    OracleComp (WithThSpec pr (Fxmss.Rom.fullSpec pr Msg)) (Msg × LeafId × Fxmss.Rom.Sig pr)
  /-- Erasing explicit `Th_λ` queries recovers `forge` identically. -/
  forgeM_eq : ∀ st S pk pkSl pkSf,
    simulateQ (eraseThImpl pr (Fxmss.Rom.fullSpec pr Msg) pk) (forgeM st S (pk, pkSl, pkSf)) =
      forge st S (pk, pkSl, pkSf)
  /-- At most `ξ` `Th_λ` evaluations on every execution path. -/
  thBound : ∀ st S pk,
    (forgeM st S pk).IsQueryBoundP (IsRightThQuery pr (Fxmss.Rom.fullSpec pr Msg)) ξ

/-- A SHRINCS forger (`Theorem 4.1`) whose Stage-2 `forge` procedure makes at most `ξ` explicit
`Th_λ` evaluations. -/
structure BudgetedShrincsForger (Msg : Type) (enc : MsgEnc Msg)
    [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
    [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
    [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg]
    (qs qh₁ qh₂ L ξ : ℕ) extends
    Shrincs.Forger pr Msg enc qs qh₁ qh₂ L where
  /-- Explicit-`Th_λ`-oracle version of `forge`. -/
  forgeM : State → Structure → Shrincs.PK pr →
    OracleComp (WithThSpec pr (Shrincs.advSpec pr Msg)) (Msg × Shrincs.Sig pr)
  /-- Erasing explicit `Th_λ` queries recovers `forge` identically. -/
  forgeM_eq : ∀ st S pk pkSl pkSf,
    simulateQ (eraseThImpl pr (Shrincs.advSpec pr Msg) pk) (forgeM st S (pk, pkSl, pkSf)) =
      forge st S (pk, pkSl, pkSf)
  /-- At most `ξ` `Th_λ` evaluations on every execution path. -/
  thBound : ∀ st S pk,
    (forgeM st S pk).IsQueryBoundP (IsRightThQuery pr (Shrincs.advSpec pr Msg)) ξ

/-- Lift a `BudgetedShrincsForger` to a `BudgetedPostPrfAdv` whose underlying `PostPrfAdv` is
definitionally `Shrincs.shrincsSlAdv` (used by Claim 4.16 / Theorem 4.1). -/
noncomputable def BudgetedShrincsForger.toPostPrf {Msg : Type} {enc : MsgEnc Msg}
    [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
    [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
    [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
    [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedShrincsForger pr Msg enc qs qh₁ qh₂ L ξ) :
    BudgetedPostPrfAdv pr (Fxmss.Rom.Setup pr (Shrincs.BMsg pr Msg) A.State) (SfPrecomp pr) qs ξ where
  toPostPrfAdv := Shrincs.shrincsSlAdv pr Msg enc A.toShrincsAdversary
  runM d sf pk pkSl :=
    if ¬ d.S.TreeValid vp.params.hsf then pure none else do
      let o ← (simulateQ (liftStateThPassImpl pr (Shrincs.slSimImpl pr Msg enc d sf pk pkSl))
        (A.forgeM d.st d.S (pk, pkSl, sf.pkSf))).run ⟨d.cache, [], 0, []⟩
      return if d.S.Valid vp.params.hsf ∧ o.1.1 ∉ o.2.log then
        match o.1.2 with
        | .stateless σ => some (Shrincs.slMsg pr Msg enc sf.pkSf o.1.1, σ)
        | .stateful _ _ _ _ => none
      else none
  runM_eq d sf pk pkSl := by
    unfold Shrincs.shrincsSlAdv
    by_cases hS : d.S.TreeValid vp.params.hsf
    · simp only [hS, not_true_eq_false, ↓reduceIte, simulateQ_bind, simulateQ_pure]
      rw [simulateQ_eraseTh_runStatePass, A.forgeM_eq d.st d.S pk pkSl sf.pkSf]
      exact bind_congr fun _ => by congr 1
    · simp only [hS, not_false_eq_true, ↓reduceIte, simulateQ_pure]
  thBound d sf pk pkSl := by
    by_cases hS : d.S.TreeValid vp.params.hsf
    · simp only [hS, not_true_eq_false, ↓reduceIte, bind_pure_comp, isQueryBoundP_map_iff]
      exact isQueryBoundP_runStatePass pr (Shrincs.slSimImpl pr Msg enc d sf pk pkSl)
        (A.thBound d.st d.S (pk, pkSl, sf.pkSf)) _
    · simp only [hS, not_false_eq_true, ↓reduceIte]
      exact isQueryBoundP_pure (p := IsRightThQuery pr (SlAdvSpec pr)) none ξ

/-- Lift a `BudgetedShrincsForger` to a `BudgetedFxmssForger` whose underlying `Forger` is
definitionally `Shrincs.AFTable` (zero stateless `Th_λ` evaluations in Stage 2). -/
noncomputable def BudgetedShrincsForger.toAFTable {Msg : Type} {enc : MsgEnc Msg}
    [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
    [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
    [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
    [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] {qs qh₁ qh₂ L ξ : ℕ}
    (A : BudgetedShrincsForger pr Msg enc qs qh₁ qh₂ L ξ)
    (u : SlSecAdrs vp → pr.Y) (pkSl : pr.Y) (tbl : SLHDSA.Adrs → Option pr.Y) :
    BudgetedFxmssForger pr (Shrincs.BMsg pr Msg) (Shrincs.slKeygenS pr) qs qh₁ qh₂ L ξ where
  toForger := Shrincs.AFTable pr Msg enc A.toForger u pkSl tbl
  forgeM st S pk' :=
    let K : Fxmss.Rom.Keys pr := ⟨S, pk'.1, pkSl, pk'.2.2⟩
    let signFn : pr.PkSeed → pr.Y → List SLHDSA.Byte → pr.Y → Stateless.Sig pr :=
      fun p pkSl' m R => slSignTable pr tbl p pkSl' u m R
    (fun o => Shrincs.outOf pr Msg K o.1.1 o.1.2) <$>
      (simulateQ (liftStateThPassImpl pr (Shrincs.implAFDet pr Msg enc signFn K))
        (A.forgeM st S K.toPK)).run ⟨0, [], ∅⟩
  forgeM_eq st S pk pkSl' pkSf := by
    have hst : simulateQ (eraseThImpl pr (Shrincs.advSpec pr Msg) pk)
        (A.forgeM st S (pk, pkSl, pkSf)) = A.forge st S (pk, pkSl, pkSf) :=
      A.forgeM_eq st S pk pkSl pkSf
    simp only [Shrincs.AFTable, Shrincs.forgeExtDet, Fxmss.Rom.Keys.toPK,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, simulateQ_bind]
    rw [simulateQ_eraseTh_runStatePass, hst]
    exact bind_congr fun _ => by simp [Function.comp_apply]
  thBound st S pk' := by
    rw [isQueryBoundP_map_iff]
    exact isQueryBoundP_runStatePass pr _ (A.thBound st S _) _

end BudgetedAdversaries

end ShrincsSecurity.Complexity

end
