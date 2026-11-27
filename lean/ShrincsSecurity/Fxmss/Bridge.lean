module

public import ShrincsSecurity.Fxmss.Events

/-!
# The EU-CMA experiment of Definition 4.16 is the game `F.0`

`SHRINCS-Security-Analysis.pdf`, Section 4.7, the start of the proof of **Theorem 4.2**
(txt lines ~3116–3160): `F.0` is the FXMSS EU-CMA experiment of **Definition 4.16** in the
random-oracle model. `succ_eq_gameG` proves that the success probability `succ` of the interface
experiment `Notions.FxmssScheme.experiment` under the random-oracle runtime is the winning
probability of the explicit game `gameG` of `Games.lean`. The two programs differ in four
inessential ways, each handled by one lemma:

* **(a) Handler shape** (`implG_step`, `forge_run`). The experiment runs the forger against the
  scheme oracles (a `StateT (used, log)` handler over the oracles `unifSpec + H_msg^sf`), which the
  runtime then simulates with `romImpl` (state: the random-oracle cache). Flattening the two
  `StateT` layers gives one handler on `(used, log) × cache`, and it is the projection of `F.0`'s
  handler `implG` on `St` (which also records every answered query in `recs`).
* **(b) Order of `PK.seed`.** The experiment samples `PK.seed` in key generation, after `A₁`;
  `gameG` samples it first. `A₁` under `romImpl` is a `ProbComp` independent of `PK.seed`, so the
  two samples commute (`EvalDistEq.bind_bind_swap`).
* **(c) The completion of Remark 4.6** (`stage2_win`). `gameG` runs, after the verification query
  of the forgery, a signing query with message `M' ≠ M*` on every anchor. The win
  (`Verify ∧ M* ∉ log`) is decided at the verification query: the completion only appends
  `M' ≠ M*` to the log (`completion_log`) and is lossless.
* **(d) Decidability instances** of the `if`s differ syntactically; `simp` normalizes them.

Verification is one random-oracle query followed by `verifyWith`, the same as the verification
query of `stage2Prog` followed by `Transcript.Win`.
-/
@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- The scheme oracle's state and the random-oracle cache read off a signing-phase state. -/
def St.proj (s : St pr Msg) : (List LeafId × List Msg) × (roSpec pr Msg).QueryCache :=
  ((s.used, s.log), s.cache)

/-- The nested handler of the EU-CMA experiment (scheme oracles over `romImpl`), flattened. -/
noncomputable def flatImpl (k : SK pr) :
    QueryImpl (fullSpec pr Msg)
      (StateT ((List LeafId × List Msg) × (roSpec pr Msg).QueryCache) ProbComp) :=
  ((roSpec pr Msg).romImpl.mapStateTBase ((scheme pr Msg slKeygen).oracles k.S k)).flattenStateT

omit [Nontrivial Msg] in
/-- One step of `F.0`'s handler, projected to `(used, log) × cache`, is one step of the flattened
handler of the experiment. -/
theorem implG_step (k : SK pr) (pkSl : pr.Y) (t : (fullSpec pr Msg).Domain) (s : St pr Msg) :
    Prod.map id (St.proj pr Msg) <$> (implG pr Msg ⟨k.S, k.pk, pkSl, k.pkSf⟩ k.sk t).run s =
      (flatImpl pr Msg slKeygen k t).run (St.proj pr Msg s) := by
  rcases t with (n | x) | q
  · simp [implG, impl, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      Notions.FxmssScheme.oracles, St.proj, unifFwdImpl]
  · cases h : s.cache.toFn x <;>
      simp [implG, impl, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Notions.FxmssScheme.oracles, St.proj, roStep, h]
  · by_cases h : q.2 ∈ leafIds P.hsf k.S ∧ q.2 ∉ s.used
    · simp [implG, impl, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Notions.FxmssScheme.oracles, St.proj, signStep, Notions.FxmssScheme.signOracle, h, scheme,
        sign, roStep, OracleSpec.simulateQ_romImpl_liftM_run]
      refine bind_congr fun R => ?_
      cases s.cache.toFn (roIn pr Msg R k.pk k.pkSf q.2 q.1) <;> simp
    · simp [implG, impl, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Notions.FxmssScheme.oracles, St.proj, signStep, Notions.FxmssScheme.signOracle, h, scheme]

omit [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- The random-oracle step of the signing phase is `randomOracle` on the cache. -/
theorem roStep_run_map (x : RoIn pr Msg) (s : St pr Msg) :
    Prod.map id St.cache <$> (roStep pr Msg x).run s =
      ((roSpec pr Msg).randomOracle x).run s.cache := by
  cases h : s.cache.toFn x <;> simp [roStep, h]

omit [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A random-oracle step leaves the message log unchanged. -/
theorem roStep_log (x : RoIn pr Msg) (s : St pr Msg) :
    ∀ z ∈ support ((roStep pr Msg x).run s), z.2.log = s.log := by
  cases h : s.cache.toFn x <;> simp [roStep, h]

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- A signing step of `F.0` appends the queried message to the log. -/
theorem implG_sign_log (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId) (s : St pr Msg) :
    ∀ z ∈ support ((implG pr Msg K sk (.inr q)).run s), z.2.log = s.log ++ [q.1] := by
  intro z hz
  by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
  · simp [implG, impl, signStep, h] at hz
    obtain ⟨R, d, b, hb, rfl⟩ := hz
    simpa using roStep_log pr Msg _ s (d, b) hb
  · simp [implG, impl, signStep, h] at hz
    simp [hz]

omit [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg] in
/-- The completion of Remark 4.6 with message `M ≠ Mf` does not log `Mf`. -/
theorem completion_log (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (M Mf : Msg) (hM : M ≠ Mf) :
    ∀ (ids : List LeafId) (s : St pr Msg),
      ∀ z ∈ support ((simulateQ (implG pr Msg K sk) (completion pr Msg M ids)).run s),
        (Mf ∈ z.2.log ↔ Mf ∈ s.log) := by
  intro ids
  induction ids with
  | nil => intro s z hz; simp [completion] at hz; simp [hz]
  | cons id ids ih =>
    intro s z hz
    simp only [completion, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [ih y.2 z hz, implG_sign_log pr Msg K sk (M, id) s y hy]
    simp [Ne.symm hM]

omit [Nontrivial Msg] in
/-- **Flattening and projection** (difference (a)): the scheme oracles of Definition 4.16 run
under `romImpl` are the signing-phase handler of `F.0` with its state projected to (used leaves,
queried messages) and the random-oracle cache; the records `recs` are dropped. -/
theorem forge_run {α : Type} (k : SK pr) (pkSl : pr.Y) (oa : OracleComp (fullSpec pr Msg) α)
    (c : (roSpec pr Msg).QueryCache) :
    (simulateQ (roSpec pr Msg).romImpl
      ((simulateQ ((scheme pr Msg slKeygen).oracles k.S k) oa).run ([], []))).run c =
      (fun z => ((z.1, (z.2.used, z.2.log)), z.2.cache)) <$>
        (simulateQ (implG pr Msg ⟨k.S, k.pk, pkSl, k.pkSf⟩ k.sk) oa).run (St.init pr Msg c) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change _ <$> (simulateQ (flatImpl pr Msg slKeygen k) oa).run
    (St.proj pr Msg (St.init pr Msg c)) = _
  rw [← map_run_simulateQ_eq_of_query_map_eq _ _ _ (implG_step pr Msg slKeygen k pkSl),
    Functor.map_map]
  rfl

open scoped Classical in
/-- **The winning check of `F.0` is decided at the verification query** (difference (c)): the
completion of Remark 4.6 after it only logs messages `≠ M*` and is lossless, so the signing phase
of `F.0` followed by its winning check is `A₂`, the verification query, and the check
`Verify ∧ M* ∉ log` on the log before the completion. -/
theorem stage2_win {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (s : St pr Msg) :
    ((simulateQ (implG pr Msg K sk) (stage2Prog pr Msg slKeygen A st K)).run s >>=
      fun r => pure (decide (WinO (some (Transcript.ofRun pr Msg K r))))) =ᵈ
      ((simulateQ (implG pr Msg K sk) (A.forge st K.S K.toPK)).run s >>= fun p =>
        (roStep pr Msg (roIn pr Msg p.1.2.2.1 K.pk K.pkSf p.1.2.1 p.1.1)).run p.2 >>= fun q =>
          pure (verifyWith pr K.pk K.pkSf p.1.2.1 p.1.2.2.2 q.1 && !decide (p.1.1 ∈ p.2.log))) := by
  simp only [stage2Prog, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
    simulateQ_pure, StateT.run_pure, pure_bind]
  refine EvalDistEq.bind_right _ fun p => ?_
  simp only [implG, impl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  refine EvalDistEq.bind_congr_of_support _ fun q hq => ?_
  have hlog := roStep_log pr Msg _ _ q hq
  refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ fun r hr => ?_)
    (EvalDistEq.bind_const _ _)
  have hc := completion_log pr Msg _ _ _ p.1.1 (otherMsg_ne Msg p.1.1) _ _ r hr
  simp only [WinO, Transcript.Win, Transcript.ofRun, hc, hlog]
  cases verifyWith pr K.pk K.pkSf p.1.2.1 p.1.2.2.2 q.1 <;> simp

open scoped Classical in
/-- The signing phase of the EU-CMA experiment (forgery, then verification) under `romImpl` is
the signing phase of `F.0` followed by its winning check (differences (a) and (c)). -/
theorem signPhase_evalDistEq {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (k : SK pr) (pkSl : pr.Y) (c : (roSpec pr Msg).QueryCache) :
    ((simulateQ (roSpec pr Msg).romImpl
      ((simulateQ ((scheme pr Msg slKeygen).oracles k.S k)
        (A.forge st k.S (k.pk, pkSl, k.pkSf))).run ([], []))).run c >>= fun a =>
      (simulateQ (roSpec pr Msg).romImpl
        (verify pr Msg (k.pk, pkSl, k.pkSf) a.1.1.1 a.1.1.2.1 a.1.1.2.2)).run a.2 >>= fun a₁ =>
      Prod.fst <$> (pure (a₁.1 && !decide (a.1.1.1 ∈ a.1.2.2), a₁.2) :
        ProbComp (Bool × (roSpec pr Msg).QueryCache))) =ᵈ
      ((simulateQ (implG pr Msg ⟨k.S, k.pk, pkSl, k.pkSf⟩ k.sk)
        (stage2Prog pr Msg slKeygen A st ⟨k.S, k.pk, pkSl, k.pkSf⟩)).run (St.init pr Msg c) >>=
          fun r => pure (decide (WinO (some
            (Transcript.ofRun pr Msg ⟨k.S, k.pk, pkSl, k.pkSf⟩ r))))) := by
  refine EvalDistEq.trans ?_ (stage2_win pr Msg slKeygen A st _ _ _).symm
  rw [forge_run pr Msg slKeygen k pkSl, bind_map_left]
  refine EvalDistEq.bind_right _ fun p => ?_
  simp only [verify, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, map_pure]
  rw [OracleSpec.romImpl_apply_inr, ← roStep_run_map, bind_map_left]
  simp only [bind_assoc, pure_bind, Prod.map_fst, id_eq]
  exact EvalDistEq.rfl

open scoped Classical in
/-- **The EU-CMA experiment of Definition 4.16 is `F.0`**: under the random-oracle runtime, the
FXMSS EU-CMA success probability is the winning probability of `gameG`. -/
theorem succ_eq_gameG {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    succ pr Msg slKeygen A = Pr{let o ← gameG pr Msg slKeygen A}[WinO o] := by
  have H : (simulateQ (roSpec pr Msg).romImpl
      (Notions.FxmssScheme.experiment (scheme pr Msg slKeygen) A)).run' ∅ =ᵈ
      (gameG pr Msg slKeygen A >>= fun o => pure (decide (WinO o))) := by
    simp only [gameG, bind_assoc]
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _)
    rw [Notions.FxmssScheme.experiment, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine EvalDistEq.bind_right _ fun z => ?_
    rcases z with ⟨⟨S, st⟩, c⟩
    dsimp only
    by_cases hv : S.TreeValid P.hsf
    · simp only [scheme, hv, not_true_eq_false, ↓reduceIte, stageG, keygen, simulateQ_bind,
        StateT.run_bind, OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left, simulateQ_pure,
        StateT.run_pure, pure_bind, map_bind, bind_assoc]
      refine EvalDistEq.bind_right _ fun pk => EvalDistEq.bind_right _ fun f =>
        EvalDistEq.bind_right _ fun pkSl => ?_
      exact signPhase_evalDistEq pr Msg slKeygen A st
        ⟨S, pk, skOf pr S f, pkSfOf pr S pk (skOf pr S f)⟩ pkSl c
    · simp only [scheme, hv, not_false_eq_true, ↓reduceIte, stageG, simulateQ_pure, StateT.run_pure,
        map_pure, pure_bind]
      rw [decide_eq_false (fun h : WinO (pr := pr) (Msg := Msg) none => h)]
      exact (EvalDistEq.bind_const ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) _).symm
  rw [succ, Notions.FxmssScheme.succ, runtime, ProbCompRuntime.rom_evalDist, H.evalDist_eq,
    prEvent_eq_evalDist_decide]

end ShrincsSecurity.Fxmss.Rom

end
