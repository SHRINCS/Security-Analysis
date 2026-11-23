module

public import ShrincsSecurity.Fxmss.Lift
public import ShrincsSecurity.Notions.Collection

/-!
# Two-stage reductions from a sampled setup and deterministic challenge queries

The reductions `B₂`, `B₄`, `B₆`, `B₇`, `B₈` of Section 4.7 (Claims 4.3, 4.5, 4.7–4.9) share one
shape. Their first stage samples a setup `d ← g₁` that does not depend on the hidden public
parameter (the forger's structure phase, the uniform secrets, the presampled digests), then makes
challenge (and collection) queries that are a deterministic function of `d` and the hidden
parameter; their second stage receives the parameter, simulates the rest of the game for the
forger itself, and outputs a collision read off the forgery.

`mkTcrAdv`, `mkSTcrAdv` and `mkExclAdv` build such adversaries for SM-TCR (Definition 4.4),
S-TCR(Prop) (Definition 4.8) and sm-tcr-excl (Definition 4.7); the `_advantage` lemmas compute
their success: if the queries are never refused and record the target list `Q d pk`, the
experiment is `pk ← P; d ← g₁; out ← forge d pk` followed by the winning check on `Q d pk`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Fxmss

open Notions

variable {ι P T M N D : Type}

/-! ## SM-TCR -/

section TCR

variable [DecidableEq T] [DecidableEq M] [DecidableEq N]

/-- An SM-TCR adversary whose first stage samples `d ← g₁` and then makes the queries `qs d`. -/
def mkTcrAdv (prob : SM_DT_TCR_Problem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D → P → ProbComp (ℕ × M)) : SM_DT_TCR_Adversary prob where
  State := D
  choose := do
    let d ← (liftM g₁ : OracleComp
      (unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl)) D)
    qs d
    return d
  forge := forge

/-- The winning check of the SM-TCR experiment on a target list. -/
def tcrWin (prob : SM_DT_TCR_Problem ι P T M N) (pk : P) (Q : List (T × M)) (out : ℕ × M) :
    Bool :=
  match Q[out.1]? with
  | none => false
  | some (t, mj) => decide (out.2 ≠ mj ∧ prob.th.eval pk t out.2 = prob.th.eval pk t mj)

/-- **Success of `mkTcrAdv`**: if, for every parameter and every reachable setup, the queries run
without refusal and record the targets `Q d pk`, the experiment is the setup, the second stage and
the winning check on `Q d pk`. -/
theorem mkTcrAdv_advantage (prob : SM_DT_TCR_Problem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D → P → ProbComp (ℕ × M)) (Q : D → P → List (T × M)) (C : D → P → List T)
    (hq : ∀ pk, ∀ d ∈ support g₁,
      (simulateQ (SM_DT_TCR_oracles prob pk) (qs d)).run ([], []) = pure ((), (Q d pk, C d pk))) :
    SM_DT_TCR_Advantage (mkTcrAdv prob g₁ qs forge) =
      Pr{let pk ← prob.th.seedGen; let d ← g₁; let out ← forge d pk}[
        tcrWin prob pk (Q d pk) out = true] := by
  classical
  have hrun : ∀ pk, (simulateQ (SM_DT_TCR_oracles prob pk) (mkTcrAdv prob g₁ qs forge).choose).run
      ([], []) =ᵈ (g₁ >>= fun d => pure (d, (Q d pk, C d pk))) := by
    intro pk
    simp only [mkTcrAdv, SM_DT_TCR_oracles]
    rw [simulateQ_add_liftM_bind_run]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have h := hq pk d hd
    simp only [SM_DT_TCR_oracles] at h
    rw [simulateQ_bind, StateT.run_bind, h, pure_bind]
    simp
  have hexp : SM_DT_TCR_Experiment (mkTcrAdv prob g₁ qs forge) =ᵈ
      (do let pk ← prob.th.seedGen; let d ← g₁; let out ← forge d pk
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

/-- An S-TCR(Prop) adversary whose first stage samples `d ← g₁` and then makes the queries
`qs d`. -/
def mkSTcrAdv (prob : STCRProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) Unit)
    (forge : D → P → ProbComp (ℕ × M × ℕ)) : STCRAdversary prob where
  State := D
  choose := do
    let d ← (liftM g₁ : OracleComp
      (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) D)
    qs d
    return d
  forge := forge

/-- **Success of `mkSTcrAdv`**, as `mkTcrAdv_advantage`. -/
theorem mkSTcrAdv_succ (prob : STCRProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)) Unit)
    (forge : D → P → ProbComp (ℕ × M × ℕ)) (Q : D → P → List ((T × M) × (N × ℕ)))
    (C : D → P → List T)
    (hq : ∀ pk, ∀ d ∈ support g₁,
      (simulateQ (STCR_oracles prob pk) (qs d)).run ([], []) = pure ((), (Q d pk, C d pk))) :
    STCR_Succ (mkSTcrAdv prob g₁ qs forge) =
      Pr{let pk ← prob.th.seedGen; let d ← g₁; let out ← forge d pk}[
        STCR_IsCollision prob pk (Q d pk) out = true] := by
  have hrun : ∀ pk, (simulateQ (STCR_oracles prob pk) (mkSTcrAdv prob g₁ qs forge).choose).run
      ([], []) =ᵈ (g₁ >>= fun d => pure (d, (Q d pk, C d pk))) := by
    intro pk
    simp only [mkSTcrAdv, STCR_oracles]
    rw [simulateQ_add_liftM_bind_run]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have h := hq pk d hd
    simp only [STCR_oracles] at h
    rw [simulateQ_bind, StateT.run_bind, h, pure_bind]
    simp
  have hexp : STCR_Experiment (mkSTcrAdv prob g₁ qs forge) =ᵈ
      (do let pk ← prob.th.seedGen; let d ← g₁; let out ← forge d pk
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

/-- An sm-tcr-excl adversary whose first stage samples `d ← g₁` and then makes the queries
`qs d`. -/
def mkExclAdv (prob : SMTCRExclProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D → P → ProbComp (ℕ × T × M)) : SMTCRExclAdversary prob where
  State := D
  choose := do
    let d ← (liftM g₁ : OracleComp
      (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl)) D)
    qs d
    return d
  forge := forge

/-- **Success of `mkExclAdv`**, as `mkTcrAdv_advantage`. -/
theorem mkExclAdv_succ (prob : SMTCRExclProblem ι P T M N) (g₁ : ProbComp D)
    (qs : D → OracleComp (unifSpec + (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl))
      Unit)
    (forge : D → P → ProbComp (ℕ × T × M)) (Q : D → P → List (T × M)) (C : D → P → List T)
    (hq : ∀ pk, ∀ d ∈ support g₁,
      (simulateQ (SMTCRExcl_oracles prob pk) (qs d)).run ([], []) = pure ((), (Q d pk, C d pk))) :
    SMTCRExcl_Succ (mkExclAdv prob g₁ qs forge) =
      Pr{let pk ← prob.th.seedGen; let d ← g₁; let out ← forge d pk}[
        SMTCRExcl_IsCollision prob pk (Q d pk) out = true] := by
  have hrun : ∀ pk, (simulateQ (SMTCRExcl_oracles prob pk) (mkExclAdv prob g₁ qs forge).choose).run
      ([], []) =ᵈ (g₁ >>= fun d => pure (d, (Q d pk, C d pk))) := by
    intro pk
    simp only [mkExclAdv, SMTCRExcl_oracles]
    rw [simulateQ_add_liftM_bind_run]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have h := hq pk d hd
    simp only [SMTCRExcl_oracles] at h
    rw [simulateQ_bind, StateT.run_bind, h, pure_bind]
    simp
  have hexp : SMTCRExcl_Experiment (mkExclAdv prob g₁ qs forge) =ᵈ
      (do let pk ← prob.th.seedGen; let d ← g₁; let out ← forge d pk
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
