module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Lifted sampling under stateful game oracles

Every reduction of Section 4.7 runs a plain `ProbComp` part (the structure phase of the forger
against its own random-oracle simulation, the uniform secrets and digests) inside its first stage,
whose oracles are private coins plus the game's oracles. The game's handler forwards the private
coins (`(QueryImpl.ofLift unifSpec ProbComp).liftTarget _`), so the lifted part is sampled as is
and leaves the game state unchanged (`simulateQ_add_liftM_run`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace ShrincsSecurity.Fxmss

variable {σ α β : Type}

/-- The forwarding handler of private coins into a stateful `ProbComp`. -/
abbrev unifFwd (σ : Type) : QueryImpl unifSpec (StateT σ ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)

theorem unifFwd_eq_toQueryImpl :
    unifFwd σ = (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT σ ProbComp) := by
  unfold unifFwd
  congr 1

/-- Simulating a `ProbComp` through the forwarding handler samples it and keeps the state. -/
theorem simulateQ_unifFwd_run (oa : ProbComp α) (s : σ) :
    (simulateQ (unifFwd σ) oa).run s = (fun x => (x, s)) <$> oa := by
  rw [unifFwd_eq_toQueryImpl]
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [← ih]

/-- **A lifted `ProbComp` under a game handler** (private coins forwarded, any other oracles):
it is sampled as is and the game state is unchanged. -/
theorem simulateQ_add_liftM_run {ι : Type} {X : OracleSpec ι}
    (rest : QueryImpl X (StateT σ ProbComp)) (oa : ProbComp α) (s : σ) :
    (simulateQ (unifFwd σ + rest) (liftM oa : OracleComp (unifSpec + X) α)).run s =
      (fun x => (x, s)) <$> oa := by
  rw [show simulateQ (unifFwd σ + rest) (liftM oa : OracleComp (unifSpec + X) α) =
      simulateQ (unifFwd σ) oa from
    QueryImpl.simulateQ_add_liftComp_left (m' := StateT σ ProbComp) (unifFwd σ) rest oa]
  exact simulateQ_unifFwd_run oa s

/-- A lifted `ProbComp` prefix under a game handler: sample it, then continue from the same
state. -/
theorem simulateQ_add_liftM_bind_run {ι : Type} {X : OracleSpec ι}
    (rest : QueryImpl X (StateT σ ProbComp)) (oa : ProbComp α)
    (k : α → OracleComp (unifSpec + X) β) (s : σ) :
    (simulateQ (unifFwd σ + rest) ((liftM oa : OracleComp (unifSpec + X) α) >>= k)).run s =
      oa >>= fun x => (simulateQ (unifFwd σ + rest) (k x)).run s := by
  rw [simulateQ_bind, StateT.run_bind, simulateQ_add_liftM_run, bind_map_left]

end ShrincsSecurity.Fxmss

end
