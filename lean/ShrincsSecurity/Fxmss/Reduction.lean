module

public import ShrincsSecurity.Fxmss.Lift
public import ShrincsSecurity.Notions.Collection

/-!
# Two-stage reductions from a sampled setup and deterministic challenge queries

The reductions `B₂`, `B₄`, `B₆`, `B₇`, `B₈` of Section 4.7 (Claims 4.3, 4.5, 4.7–4.9) share one
shape. Their first stage samples a setup `d ← g₁` that does not depend on the hidden public
parameter (the forger's structure phase, the uniform secrets, the presampled digests), then makes
challenge (and collection) queries that are a deterministic function of `d` and the hidden
parameter while **recording every accepted challenge query and answer into its own state**
(`recordTcrImpl`, `recordSTcrImpl`, `recordExclImpl`); their second stage receives `(d, savedQ)` and
the parameter, simulates the rest of the game for the forger itself, and searches `savedQ` directly
without recomputing targets (in particular, `B₂` never calls `Notions.leastCounter` in Stage 2).

`mkTcrAdv`, `mkSTcrAdv` and `mkExclAdv` build such adversaries for SM-TCR (Definition 4.4),
S-TCR(Prop) (Definition 4.8) and sm-tcr-excl (Definition 4.7); the `_advantage`/`_succ` lemmas
compute their success: if the queries are never refused and record the target list `Q d pk`, the
experiment is `pk ← P; d ← g₁; out ← forge (d, Q d pk) pk` followed by the winning check on
`Q d pk`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Fxmss

open Notions

variable {ι P T M N D : Type}

/-! ## SM-TCR -/

section TCR

variable [DecidableEq T] [DecidableEq M] [DecidableEq N]

/-- First-stage oracle signature for SM-TCR. -/
abbrev TcrOracleSpec (prob : SM_DT_TCR_Problem ι P T M N) :=
  unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl)

/-- First-stage query recorder for SM-TCR: forwards all oracle queries and appends every accepted
challenge query `(t, m)` to the reduction's own local list. -/
def recordTcrImpl (prob : SM_DT_TCR_Problem ι P T M N) :
    QueryImpl (TcrOracleSpec prob) (StateT (List (T × M)) (OracleComp (TcrOracleSpec prob)))
  | .inl n => StateT.mk fun acc => (fun u => (u, acc)) <$>
      (liftM ((TcrOracleSpec prob).query (.inl n)) :
        OracleComp (TcrOracleSpec prob) (unifSpec.Range n))
  | .inr (.inl tm) => StateT.mk fun acc => do
      let r ← (liftM ((TcrOracleSpec prob).query (.inr (.inl tm))) :
        OracleComp (TcrOracleSpec prob) (Option N))
      return (r, if r.isSome then acc ++ [tm] else acc)
  | .inr (.inr q) => StateT.mk fun acc => (fun r => (r, acc)) <$>
      (liftM ((TcrOracleSpec prob).query (.inr (.inr q))) :
        OracleComp (TcrOracleSpec prob) (Option N))

omit [DecidableEq M] [DecidableEq N] in
/-- The local challenge log maintained by `recordTcrImpl` always matches the oracle's target list. -/
theorem simulateQ_recordTcr_run (prob : SM_DT_TCR_Problem ι P T M N) (pk : P) {α : Type}
    (oa : OracleComp (TcrOracleSpec prob) α) (qs : List (T × M)) (tws : List T) :
    (simulateQ (SM_DT_TCR_oracles prob pk) ((simulateQ (recordTcrImpl prob) oa).run qs)).run
        (qs, tws) =
      (fun z => ((z.1, z.2.1), z.2)) <$> (simulateQ (SM_DT_TCR_oracles prob pk) oa).run (qs, tws) := by
  induction oa using OracleComp.inductionOn generalizing qs tws with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | tm | q
    · simp only [simulateQ_bind, simulateQ_spec_query, recordTcrImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hcoin : (SM_DT_TCR_oracles prob pk (.inl n)).run (qs, tws) =
          (fun u => (u, (qs, tws))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp [SM_DT_TCR_oracles, StateT.run_monadLift]
      rw [hcoin, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u qs tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordTcrImpl, StateT.run_bind, StateT.run_mk,
        bind_assoc, map_bind]
      have hch : (SM_DT_TCR_oracles prob pk (.inr (.inl tm))).run (qs, tws) =
          (SM_DT_TCR_challengeOracle prob pk tm).run (qs, tws) := rfl
      rw [hch]
      unfold SM_DT_TCR_challengeOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind, simulateQ_pure, Option.isSome_none,
          Bool.false_eq_true, ↓reduceIte]
        exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
          Option.isSome_some, ↓reduceIte]
        exact ih (some (prob.th.eval pk tm.1 tm.2)) (qs ++ [tm]) tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordTcrImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hco : (SM_DT_TCR_oracles prob pk (.inr (.inr q))).run (qs, tws) =
          (collectionOracle (Q := T × M) Prod.fst prob.thColl pk q).run (qs, tws) := rfl
      rw [hco]
      unfold collectionOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind]
        exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact ih (some (prob.thColl.eval q.1 pk q.2.1 q.2.2)) qs (tws ++ [q.2.1])

/-- An SM-TCR adversary whose first stage samples `d ← g₁`, runs `qs d` while recording every
accepted challenge query in `savedQ`, and passes `(d, savedQ)` to `forge`. -/
def mkTcrAdv (prob : SM_DT_TCR_Problem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D × List (T × M) → P → ProbComp (ℕ × M)) : SM_DT_TCR_Adversary prob where
  State := D × List (T × M)
  choose := do
    let d ← (liftM g₁ : OracleComp
      (unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl)) D)
    let (_, savedQ) ← (simulateQ (recordTcrImpl prob) (qs d)).run []
    return (d, savedQ)
  forge := forge

/-- The winning check of the SM-TCR experiment on a target list. -/
def tcrWin (prob : SM_DT_TCR_Problem ι P T M N) (pk : P) (Q : List (T × M)) (out : ℕ × M) :
    Bool :=
  match Q[out.1]? with
  | none => false
  | some (t, mj) => decide (out.2 ≠ mj ∧ prob.th.eval pk t out.2 = prob.th.eval pk t mj)

/-- **Success of `mkTcrAdv`**: if, for every parameter and every reachable setup, the queries run
without refusal and record the targets `Q d pk`, the experiment is the setup, the second stage
receiving `(d, Q d pk)` from Stage 1, and the winning check on `Q d pk`. -/
theorem mkTcrAdv_advantage (prob : SM_DT_TCR_Problem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D × List (T × M) → P → ProbComp (ℕ × M)) (Q : D → P → List (T × M))
    (C : D → P → List T)
    (hq : ∀ pk, ∀ d ∈ support g₁,
      (simulateQ (SM_DT_TCR_oracles prob pk) (qs d)).run ([], []) = pure ((), (Q d pk, C d pk))) :
    SM_DT_TCR_Advantage (mkTcrAdv prob g₁ qs forge) =
      Pr{let pk ← prob.th.seedGen; let d ← g₁; let out ← forge (d, Q d pk) pk}[
        tcrWin prob pk (Q d pk) out = true] := by
  classical
  have hrun : ∀ pk, (simulateQ (SM_DT_TCR_oracles prob pk) (mkTcrAdv prob g₁ qs forge).choose).run
      ([], []) =ᵈ (g₁ >>= fun d => pure ((d, Q d pk), (Q d pk, C d pk))) := by
    intro pk
    simp only [mkTcrAdv, SM_DT_TCR_oracles]
    rw [simulateQ_add_liftM_bind_run]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordTcr_run prob pk (qs d) [] []
    rw [hq pk d hd, map_pure] at hrec
    simp only [SM_DT_TCR_oracles] at hrec
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    simp
  have hexp : SM_DT_TCR_Experiment (mkTcrAdv prob g₁ qs forge) =ᵈ
      (do let pk ← prob.th.seedGen; let d ← g₁; let out ← forge (d, Q d pk) pk
          return decide (tcrWin prob pk (Q d pk) out = true)) := by
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine EvalDistEq.trans (EvalDistEq.bind_left (hrun pk) _) ?_
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun out => ?_
    rcases out with ⟨j, m⟩
    simp only [tcrWin]
    split <;> rename_i h <;> simp [h]
  unfold SM_DT_TCR_Advantage
  rw [hexp.evalDist_eq, ← prEvent_eq_evalDist_singleton]
  simp [map_bind]

end TCR

/-! ## S-TCR(Prop) -/

section STCR

variable [DecidableEq T] [DecidableEq M] [DecidableEq N]

/-- First-stage oracle signature for S-TCR(Prop). -/
abbrev STcrOracleSpec (prob : STCRProblem ι P T M N) :=
  unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)

/-- First-stage query recorder for S-TCR(Prop): forwards all oracle queries and appends every
accepted challenge query `((t, m), (y, i))` to the reduction's own local list. -/
def recordSTcrImpl (prob : STCRProblem ι P T M N) :
    QueryImpl (STcrOracleSpec prob)
      (StateT (List ((T × M) × (N × ℕ))) (OracleComp (STcrOracleSpec prob)))
  | .inl n => StateT.mk fun acc => (fun u => (u, acc)) <$>
      (liftM ((STcrOracleSpec prob).query (.inl n)) :
        OracleComp (STcrOracleSpec prob) (unifSpec.Range n))
  | .inr (.inl tm) => StateT.mk fun acc => do
      let r ← (liftM ((STcrOracleSpec prob).query (.inr (.inl tm))) :
        OracleComp (STcrOracleSpec prob) (Option (N × ℕ)))
      return (r, match r with | none => acc | some yi => acc ++ [(tm, yi)])
  | .inr (.inr q) => StateT.mk fun acc => (fun r => (r, acc)) <$>
      (liftM ((STcrOracleSpec prob).query (.inr (.inr q))) :
        OracleComp (STcrOracleSpec prob) (Option N))

omit [DecidableEq M] [DecidableEq N] in
/-- The local challenge log maintained by `recordSTcrImpl` always matches the oracle's target list. -/
theorem simulateQ_recordSTcr_run (prob : STCRProblem ι P T M N) (pk : P) {α : Type}
    (oa : OracleComp (STcrOracleSpec prob) α) (qs : List ((T × M) × (N × ℕ))) (tws : List T) :
    (simulateQ (STCR_oracles prob pk) ((simulateQ (recordSTcrImpl prob) oa).run qs)).run (qs, tws) =
      (fun z => ((z.1, z.2.1), z.2)) <$> (simulateQ (STCR_oracles prob pk) oa).run (qs, tws) := by
  induction oa using OracleComp.inductionOn generalizing qs tws with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | tm | q
    · simp only [simulateQ_bind, simulateQ_spec_query, recordSTcrImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hcoin : (STCR_oracles prob pk (.inl n)).run (qs, tws) =
          (fun u => (u, (qs, tws))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp [STCR_oracles, StateT.run_monadLift]
      rw [hcoin, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u qs tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordSTcrImpl, StateT.run_bind, StateT.run_mk,
        bind_assoc, map_bind]
      have hch : (STCR_oracles prob pk (.inr (.inl tm))).run (qs, tws) =
          (STCR_challengeOracle prob pk tm).run (qs, tws) := rfl
      rw [hch]
      unfold STCR_challengeOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind, simulateQ_pure]
        exact ih none qs tws
      · cases hlc : leastCounter prob.th prob.prop pk tm.1 tm.2 with
        | none =>
          simp only [StateT.run_pure, pure_bind, simulateQ_pure]
          exact ih none qs tws
        | some i =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
          exact ih (some (prob.th.eval pk tm.1 (tm.2, i), i))
            (qs ++ [(tm, (prob.th.eval pk tm.1 (tm.2, i), i))]) tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordSTcrImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hco : (STCR_oracles prob pk (.inr (.inr q))).run (qs, tws) =
          (collectionOracle (Q := (T × M) × (N × ℕ)) (fun e => e.1.1) prob.thColl pk q).run
            (qs, tws) := rfl
      rw [hco]
      unfold collectionOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind]
        exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact ih (some (prob.thColl.eval q.1 pk q.2.1 q.2.2)) qs (tws ++ [q.2.1])

/-- An S-TCR(Prop) adversary whose first stage samples `d ← g₁`, runs `qs d` while recording every
accepted challenge query and answer `((t, m), (y, i))` in `savedQ`, and passes `(d, savedQ)` to
`forge`. -/
def mkSTcrAdv (prob : STCRProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) Unit)
    (forge : D × List ((T × M) × (N × ℕ)) → P → ProbComp (ℕ × M × ℕ)) : STCRAdversary prob where
  State := D × List ((T × M) × (N × ℕ))
  choose := do
    let d ← (liftM g₁ : OracleComp
      (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) D)
    let (_, savedQ) ← (simulateQ (recordSTcrImpl prob) (qs d)).run []
    return (d, savedQ)
  forge := forge

/-- **Success of `mkSTcrAdv`**, as `mkTcrAdv_advantage`. -/
theorem mkSTcrAdv_succ (prob : STCRProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) Unit)
    (forge : D × List ((T × M) × (N × ℕ)) → P → ProbComp (ℕ × M × ℕ))
    (Q : D → P → List ((T × M) × (N × ℕ))) (C : D → P → List T)
    (hq : ∀ pk, ∀ d ∈ support g₁,
      (simulateQ (STCR_oracles prob pk) (qs d)).run ([], []) = pure ((), (Q d pk, C d pk))) :
    STCR_Succ (mkSTcrAdv prob g₁ qs forge) =
      Pr{let pk ← prob.th.seedGen; let d ← g₁; let out ← forge (d, Q d pk) pk}[
        STCR_IsCollision prob pk (Q d pk) out = true] := by
  have hrun : ∀ pk, (simulateQ (STCR_oracles prob pk) (mkSTcrAdv prob g₁ qs forge).choose).run
      ([], []) =ᵈ (g₁ >>= fun d => pure ((d, Q d pk), (Q d pk, C d pk))) := by
    intro pk
    simp only [mkSTcrAdv, STCR_oracles]
    rw [simulateQ_add_liftM_bind_run]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordSTcr_run prob pk (qs d) [] []
    rw [hq pk d hd, map_pure] at hrec
    simp only [STCR_oracles] at hrec
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    simp
  have hexp : STCR_Experiment (mkSTcrAdv prob g₁ qs forge) =ᵈ
      (do let pk ← prob.th.seedGen; let d ← g₁; let out ← forge (d, Q d pk) pk
          return STCR_IsCollision prob pk (Q d pk) out) := by
    unfold STCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine EvalDistEq.trans (EvalDistEq.bind_left (hrun pk) _) ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl
  unfold STCR_Succ
  rw [hexp.evalDist_eq, ← prEvent_eq_evalDist_singleton]
  simp [map_bind]

end STCR

/-! ## sm-tcr-excl -/

section Excl

variable [DecidableEq T] [DecidableEq M] [DecidableEq N]

/-- First-stage oracle signature for sm-tcr-excl. -/
abbrev ExclOracleSpec (prob : SMTCRExclProblem ι P T M N) :=
  unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl)

/-- First-stage query recorder for sm-tcr-excl: forwards all oracle queries and appends every
accepted challenge query `(t, m)` to the reduction's own local list. -/
def recordExclImpl (prob : SMTCRExclProblem ι P T M N) :
    QueryImpl (ExclOracleSpec prob) (StateT (List (T × M)) (OracleComp (ExclOracleSpec prob)))
  | .inl n => StateT.mk fun acc => (fun u => (u, acc)) <$>
      (liftM ((ExclOracleSpec prob).query (.inl n)) :
        OracleComp (ExclOracleSpec prob) (unifSpec.Range n))
  | .inr (.inl tm) => StateT.mk fun acc => do
      let r ← (liftM ((ExclOracleSpec prob).query (.inr (.inl tm))) :
        OracleComp (ExclOracleSpec prob) (Option N))
      return (r, if r.isSome then acc ++ [tm] else acc)
  | .inr (.inr q) => StateT.mk fun acc => (fun r => (r, acc)) <$>
      (liftM ((ExclOracleSpec prob).query (.inr (.inr q))) :
        OracleComp (ExclOracleSpec prob) (Option N))

omit [DecidableEq M] [DecidableEq N] in
/-- The local challenge log maintained by `recordExclImpl` always matches the oracle's target list. -/
theorem simulateQ_recordExcl_run (prob : SMTCRExclProblem ι P T M N) (pk : P) {α : Type}
    (oa : OracleComp (ExclOracleSpec prob) α) (qs : List (T × M)) (tws : List T) :
    (simulateQ (SMTCRExcl_oracles prob pk) ((simulateQ (recordExclImpl prob) oa).run qs)).run
        (qs, tws) =
      (fun z => ((z.1, z.2.1), z.2)) <$>
        (simulateQ (SMTCRExcl_oracles prob pk) oa).run (qs, tws) := by
  induction oa using OracleComp.inductionOn generalizing qs tws with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | tm | q
    · simp only [simulateQ_bind, simulateQ_spec_query, recordExclImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hcoin : (SMTCRExcl_oracles prob pk (.inl n)).run (qs, tws) =
          (fun u => (u, (qs, tws))) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        simp [SMTCRExcl_oracles, StateT.run_monadLift]
      rw [hcoin, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u qs tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordExclImpl, StateT.run_bind, StateT.run_mk,
        bind_assoc, map_bind]
      have hch : (SMTCRExcl_oracles prob pk (.inr (.inl tm))).run (qs, tws) =
          (SMTCRExcl_challengeOracle prob pk tm).run (qs, tws) := rfl
      rw [hch]
      unfold SMTCRExcl_challengeOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind, simulateQ_pure, Option.isSome_none,
          Bool.false_eq_true, ↓reduceIte]
        exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
        exact ih (some (prob.th.eval pk tm.1 tm.2)) (qs ++ [tm]) tws
    · simp only [simulateQ_bind, simulateQ_spec_query, recordExclImpl, StateT.run_bind, StateT.run_mk,
        map_bind, bind_map_left]
      have hco : (SMTCRExcl_oracles prob pk (.inr (.inr q))).run (qs, tws) =
          (SMTCRExcl_collectionOracle prob pk q).run (qs, tws) := rfl
      rw [hco]
      unfold SMTCRExcl_collectionOracle
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · simp only [StateT.run_pure, pure_bind]
        exact ih none qs tws
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact ih (some (prob.thColl.eval q.1 pk q.2.1 q.2.2)) qs (tws ++ [q.2.1])

/-- An sm-tcr-excl adversary whose first stage samples `d ← g₁`, runs `qs d` while recording every
accepted challenge query in `savedQ`, and passes `(d, savedQ)` to `forge`. -/
def mkExclAdv (prob : SMTCRExclProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D × List (T × M) → P → ProbComp (ℕ × T × M)) : SMTCRExclAdversary prob where
  State := D × List (T × M)
  choose := do
    let d ← (liftM g₁ : OracleComp
      (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl)) D)
    let (_, savedQ) ← (simulateQ (recordExclImpl prob) (qs d)).run []
    return (d, savedQ)
  forge := forge

/-- **Success of `mkExclAdv`**, as `mkTcrAdv_advantage`. -/
theorem mkExclAdv_succ (prob : SMTCRExclProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D × List (T × M) → P → ProbComp (ℕ × T × M)) (Q : D → P → List (T × M))
    (C : D → P → List T)
    (hq : ∀ pk, ∀ d ∈ support g₁,
      (simulateQ (SMTCRExcl_oracles prob pk) (qs d)).run ([], []) = pure ((), (Q d pk, C d pk))) :
    SMTCRExcl_Succ (mkExclAdv prob g₁ qs forge) =
      Pr{let pk ← prob.th.seedGen; let d ← g₁; let out ← forge (d, Q d pk) pk}[
        SMTCRExcl_IsCollision prob pk (Q d pk) out = true] := by
  have hrun : ∀ pk, (simulateQ (SMTCRExcl_oracles prob pk) (mkExclAdv prob g₁ qs forge).choose).run
      ([], []) =ᵈ (g₁ >>= fun d => pure ((d, Q d pk), (Q d pk, C d pk))) := by
    intro pk
    simp only [mkExclAdv, SMTCRExcl_oracles]
    rw [simulateQ_add_liftM_bind_run]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := simulateQ_recordExcl_run prob pk (qs d) [] []
    rw [hq pk d hd, map_pure] at hrec
    simp only [SMTCRExcl_oracles] at hrec
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    simp
  have hexp : SMTCRExcl_Experiment (mkExclAdv prob g₁ qs forge) =ᵈ
      (do let pk ← prob.th.seedGen; let d ← g₁; let out ← forge (d, Q d pk) pk
          return SMTCRExcl_IsCollision prob pk (Q d pk) out) := by
    unfold SMTCRExcl_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine EvalDistEq.trans (EvalDistEq.bind_left (hrun pk) _) ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl
  unfold SMTCRExcl_Succ
  rw [hexp.evalDist_eq, ← prEvent_eq_evalDist_singleton]
  simp [map_bind]

end Excl

end ShrincsSecurity.Fxmss

end
