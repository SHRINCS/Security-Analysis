module

public import ShrincsSecurity.ITSR.Game
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The pre-sampled lazy oracle

`ITSR-Classical.pdf`, Lemma 2 (pre-sampled lazy oracle) and Definition 7 (creation indices).

The pre-sampled game answers like the real game of `Game.lean`, except that its fresh digests
are taken off two tapes supplied ahead of time: a fresh *direct* point (including the verification
point) takes the next entry of the tape `U`, and a fresh *challenge* point takes the next entry of
the tape `V`. Each table point records its *origin*: `direct a` for the `a`-th fresh direct point
(its creation index, Definition 7) and `fresh j` for the `j`-th fresh challenge. The state also
records the *pulled* creation indices (Lemma 3): the direct points that a challenge has hit.

Once a tape is exhausted, the game falls back to fresh uniform sampling; on bounded adversaries
this never happens (`Classification.lean`), and with the fallback the identification with the
real game (`gameImpl_evalDistEq_tapeRun`, Lemma 2) needs no query bound. For the experiment
itself, `advantage_eq_presampled` reads the success probability off uniform tapes
`U : Fin (q + 1) → Digest` and `V : Fin r → Digest`.

Encoding: the paper indexes the fresh challenge digests by the challenge index `j`; we index them
by the number of fresh challenges before, so that `V` is consumed in order. Both give fresh
challenge digests in `{V_1, …, V_r}`, which is all the proof uses.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

/-- The origin of a table point (Lemma 2, invariant): the `a`-th fresh direct point, or the
`j`-th fresh challenge point. -/
inductive Origin where
  /-- Created by the `a`-th direct query to a new point (Definition 7). -/
  | direct (a : ℕ)
  /-- Created by the `j`-th fresh challenge. -/
  | fresh (j : ℕ)
  deriving DecidableEq

/-- A challenge on a table point with this origin pulls its creation index (Lemma 3). -/
def Origin.pull : Origin → Finset ℕ → Finset ℕ
  | .direct b, P => insert b P
  | .fresh _, P => P

/-- The state of the pre-sampled game (Lemma 2). -/
structure TapeState (K M D : Type) where
  /-- The table of `H'`: each point with its value and its origin. -/
  table : K × M → Option (D × Origin)
  /-- The challenge pairs and their digests, in issue order. -/
  challenges : List ((K × M) × D)
  /-- The unused part of the tape `U` of direct-query values. -/
  uTape : List D
  /-- The unused part of the tape `V` of fresh-challenge values. -/
  vTape : List D
  /-- The number of fresh direct points created so far. -/
  nU : ℕ
  /-- The number of fresh challenges so far. -/
  nV : ℕ
  /-- The creation indices of the direct points pulled by a challenge (Lemma 3). -/
  pulled : Finset ℕ

namespace TapeState

variable {K M D : Type}

/-- The initial state of the pre-sampled game on tapes `lu` and `lv`. -/
def init (lu lv : List D) : TapeState K M D := ⟨fun _ => none, [], lu, lv, 0, 0, ∅⟩

/-- The real-game state that a pre-sampled state represents. -/
def toGame (s : TapeState K M D) : GameState K M D :=
  ⟨fun x => (s.table x).map Prod.fst, s.challenges⟩

/-- The real-game table forgets the origins. -/
@[simp] theorem toGame_table (s : TapeState K M D) (x : K × M) :
    s.toGame.table x = (s.table x).map Prod.fst := rfl

/-- The real-game challenge list is the pre-sampled one. -/
@[simp] theorem toGame_challenges (s : TapeState K M D) :
    s.toGame.challenges = s.challenges := rfl

/-- The initial pre-sampled state represents the initial real-game state. -/
@[simp] theorem toGame_init (lu lv : List D) :
    (init lu lv : TapeState K M D).toGame = GameState.init := rfl

/-- Replace both tapes. -/
def withTapes (s : TapeState K M D) (lu lv : List D) : TapeState K M D :=
  { s with uTape := lu, vTape := lv }

/-- Replacing the tapes keeps the table. -/
@[simp] theorem withTapes_table (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).table = s.table := rfl

/-- Replacing the tapes keeps the challenges. -/
@[simp] theorem withTapes_challenges (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).challenges = s.challenges := rfl

/-- The new tape `U`. -/
@[simp] theorem withTapes_uTape (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).uTape = lu := rfl

/-- The new tape `V`. -/
@[simp] theorem withTapes_vTape (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).vTape = lv := rfl

/-- Replacing the tapes keeps the direct counter. -/
@[simp] theorem withTapes_nU (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).nU = s.nU := rfl

/-- Replacing the tapes keeps the challenge counter. -/
@[simp] theorem withTapes_nV (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).nV = s.nV := rfl

/-- Replacing the tapes keeps the pulled set. -/
@[simp] theorem withTapes_pulled (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).pulled = s.pulled := rfl

/-- The tapes are invisible in the real game. -/
@[simp] theorem toGame_withTapes (s : TapeState K M D) (lu lv : List D) :
    (s.withTapes lu lv).toGame = s.toGame := rfl

variable [DecidableEq K] [DecidableEq M]

/-- The state after a new direct point `x` takes the value `z.1` off the tape `U`, leaving
`z.2`: it is the `nU`-th fresh direct point. -/
def hashFresh (s : TapeState K M D) (x : K × M) (z : D × List D) : TapeState K M D :=
  { s with
    table := Function.update s.table x (some (z.1, .direct s.nU))
    uTape := z.2
    nU := s.nU + 1 }

/-- The state after a challenge on the table point `x` with entry `e`: the pair is recorded,
and a direct point is pulled. -/
def chalHit (s : TapeState K M D) (x : K × M) (e : D × Origin) : TapeState K M D :=
  { s with
    challenges := s.challenges ++ [(x, e.1)]
    pulled := e.2.pull s.pulled }

/-- The state after a challenge on a new point `x` takes the value `z.1` off the tape `V`,
leaving `z.2`: it is the `nV`-th fresh challenge. -/
def chalFresh (s : TapeState K M D) (x : K × M) (z : D × List D) : TapeState K M D :=
  { s with
    table := Function.update s.table x (some (z.1, .fresh s.nV))
    vTape := z.2
    nV := s.nV + 1
    challenges := s.challenges ++ [(x, z.1)] }


end TapeState

variable {K M D : Type} [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D]

/-- Take the next value off a tape, or sample a fresh one once the tape is exhausted. -/
def drawTape (l : List D) : ProbComp (D × List D) :=
  match l with
  | u :: l => pure (u, l)
  | [] => (fun u => (u, [])) <$> ($ᵗ D)

/-- The pre-sampled hash oracle: a new point receives the next value of `U` and the next
creation index. -/
def tapeHash (x : K × M) : StateT (TapeState K M D) ProbComp D := StateT.mk fun s =>
  match s.table x with
  | some e => pure (e.1, s)
  | none => (fun z => (z.1, s.hashFresh x z)) <$> drawTape s.uTape

/-- The pre-sampled challenge oracle at a drawn key: a point already in the table returns its
value (pulling its creation index if it is a direct point), a new point receives the next value
of `V`. -/
def tapeChalAt (key : K) (msg : M) (s : TapeState K M D) :
    ProbComp ((K × D) × TapeState K M D) :=
  match s.table (key, msg) with
  | some e => pure ((key, e.1), s.chalHit (key, msg) e)
  | none => (fun z => ((key, z.1), s.chalFresh (key, msg) z)) <$> drawTape s.vTape

/-- The pre-sampled challenge oracle: a uniform key, then `tapeChalAt`. -/
def tapeChal (msg : M) : StateT (TapeState K M D) ProbComp (K × D) := StateT.mk fun s => do
  let key ← ($ᵗ K : ProbComp K)
  tapeChalAt key msg s

/-- The handler of the pre-sampled game. -/
def tapeImpl : QueryImpl (AdvSpec K M D) (StateT (TapeState K M D) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (TapeState K M D) ProbComp) +
    ((fun x => tapeHash x : QueryImpl (HashSpec K M D) (StateT (TapeState K M D) ProbComp)) +
      (fun m => tapeChal m : QueryImpl (ChalSpec K M D) (StateT (TapeState K M D) ProbComp)))

/-! ## Tapes -/

/-- A tape of `n` independent uniform values, as a list. -/
def tape (D : Type) [SampleableType D] (n : ℕ) : ProbComp (List D) :=
  List.ofFn <$> Fin.mOfFn n (fun _ => ($ᵗ D : ProbComp D))

/-- The empty tape. -/
theorem tape_zero : tape D 0 = pure [] := by
  simp [tape, Fin.mOfFn]

/-- A tape of `n + 1` values is a uniform head followed by a tape of `n` values. -/
theorem tape_succ (n : ℕ) :
    tape D (n + 1) = (do let u ← ($ᵗ D : ProbComp D); let l ← tape D n; return u :: l) := by
  simp [tape, Fin.mOfFn, List.ofFn_succ]

/-- Drawing from a fresh tape is a uniform draw followed by a shorter fresh tape. -/
theorem tape_bind_drawTape {β : Type} (n : ℕ) (g : D → List D → ProbComp β) :
    (do let l ← tape D n; let z ← drawTape l; g z.1 z.2) =
      (do let u ← ($ᵗ D : ProbComp D); let l ← tape D (n - 1); g u l) := by
  cases n with
  | zero => simp [tape_zero, drawTape]
  | succ n => simp [tape_succ, drawTape]

/-- Independent countable draws commute. -/
theorem evalDistEq_bind_swap {α β γ : Type} [Countable α] [Countable β] (mx : ProbComp α)
    (my : ProbComp β) (f : α → β → ProbComp γ) :
    (mx >>= fun a => my >>= fun b => f a b) =ᵈ (my >>= fun b => mx >>= fun a => f a b) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  exact EvalDistEq.of_evalDist_eq (evalDist_bind_bind_swap_of_countable mx my f)

/-- Independent countable draws commute with the two tapes. -/
theorem tapes_bind_swap {β γ : Type} [Countable β] (c : ProbComp β) (m₁ m₂ : ℕ)
    (F : List D → List D → β → ProbComp γ) :
    (do let lu ← tape D m₁; let lv ← tape D m₂; let x ← c; F lu lv x) =ᵈ
      (do let x ← c; let lu ← tape D m₁; let lv ← tape D m₂; F lu lv x) := by
  refine (EvalDistEq.bind_right _ fun lu => evalDistEq_bind_swap (tape D m₂) c (F lu)).trans ?_
  exact evalDistEq_bind_swap (tape D m₁) c (fun lu x => tape D m₂ >>= fun lv => F lu lv x)

/-! ## The steps of the two games -/

/-- The real game answers a coin query with a uniform coin. -/
theorem gameImpl_unif_run (n : ℕ) (s : GameState K M D) :
    (gameImpl (Sum.inl n : ℕ ⊕ ((K × M) ⊕ M))).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [gameImpl]

omit [SampleableType K] in
/-- The lazy random oracle of the real game, step by step. -/
theorem hashImpl_run (x : K × M) (s : GameState K M D) :
    (hashImpl x).run s = match s.table x with
      | some d => pure (d, s)
      | none => (fun d => (d, { s with table := Function.update s.table x (some d) })) <$>
          ($ᵗ D) := by
  unfold hashImpl
  cases h : s.table x <;> simp [h]

/-- The real challenge oracle at a drawn key. -/
def chalAt (key : K) (msg : M) (s : GameState K M D) : ProbComp ((K × D) × GameState K M D) :=
  match s.table (key, msg) with
  | some d => pure ((key, d), { s with challenges := s.challenges ++ [((key, msg), d)] })
  | none => (fun d => ((key, d), GameState.mk (Function.update s.table (key, msg) (some d))
      (s.challenges ++ [((key, msg), d)]))) <$> ($ᵗ D)

/-- The real challenge oracle: a uniform key, then `chalAt`. -/
theorem chalImpl_run (msg : M) (s : GameState K M D) :
    (chalImpl msg).run s = ($ᵗ K : ProbComp K) >>= fun key => chalAt key msg s := by
  simp only [chalImpl, StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
  refine bind_congr fun key => ?_
  rw [hashImpl_run, chalAt]
  cases s.table (key, msg) <;> simp

/-- The pre-sampled game answers a coin query with a uniform coin. -/
theorem tapeImpl_unif_run (n : ℕ) (s : TapeState K M D) :
    (tapeImpl (Sum.inl n : ℕ ⊕ ((K × M) ⊕ M))).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [tapeImpl]

/-- The pre-sampled game answers a direct query with `tapeHash`. -/
theorem tapeImpl_hash_run (x : K × M) (s : TapeState K M D) :
    (tapeImpl (Sum.inr (Sum.inl x) : ℕ ⊕ ((K × M) ⊕ M))).run s = (tapeHash x).run s := rfl

/-- The pre-sampled game answers a challenge query with `tapeChal`. -/
theorem tapeImpl_chal_run (msg : M) (s : TapeState K M D) :
    (tapeImpl (Sum.inr (Sum.inr msg) : ℕ ⊕ ((K × M) ⊕ M))).run s = (tapeChal msg).run s := rfl

/-- The real game answers a direct query with `hashImpl`. -/
theorem gameImpl_hash_run (x : K × M) (s : GameState K M D) :
    (gameImpl (Sum.inr (Sum.inl x) : ℕ ⊕ ((K × M) ⊕ M))).run s = (hashImpl x).run s := rfl

/-- The real game answers a challenge query with `chalImpl`. -/
theorem gameImpl_chal_run (msg : M) (s : GameState K M D) :
    (gameImpl (Sum.inr (Sum.inr msg) : ℕ ⊕ ((K × M) ⊕ M))).run s = (chalImpl msg).run s := rfl

/-! ## Lemma 2 -/

omit [SampleableType K] [SampleableType D] in
/-- Storing a new point in the pre-sampled table stores its value in the real table. -/
theorem toGame_update (s : TapeState K M D) (x : K × M) (d : D)
    (o : Origin) :
    (fun y => (Function.update s.table x (some (d, o)) y).map Prod.fst) =
      Function.update s.toGame.table x (some d) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · simp [Function.update_of_ne hy]

/-- The pre-sampled run on fresh tapes of lengths `m₁` and `m₂`, with the state read as a
real-game state. -/
def tapeRun {α : Type} (oa : OracleComp (AdvSpec K M D) α) (s : TapeState K M D) (m₁ m₂ : ℕ) :
    ProbComp (α × GameState K M D) := do
  let lu ← tape D m₁
  let lv ← tape D m₂
  let z ← (simulateQ tapeImpl oa).run (s.withTapes lu lv)
  return (z.1, z.2.toGame)

/-- **Lemma 2** (pre-sampled lazy oracle): running the real game from the state that a
pre-sampled state represents has the distribution of the pre-sampled game averaged over fresh
tapes, jointly in the output and the real-game state. -/
theorem gameImpl_evalDistEq_tapeRun {α : Type} (oa : OracleComp (AdvSpec K M D) α)
    (s : TapeState K M D) (m₁ m₂ : ℕ) :
    (simulateQ gameImpl oa).run s.toGame =ᵈ tapeRun oa s m₁ m₂ := by
  induction oa using OracleComp.inductionOn generalizing s m₁ m₂ with
  | pure a =>
    simp only [tapeRun, simulateQ_pure, StateT.run_pure, pure_bind, TapeState.toGame_withTapes]
    exact ((EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.bind_const _ _).trans
      (OracleComp.EvalDistEq.bind_const _ _)).symm
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rcases t with n | x | msg
    · calc _ = ((liftM (unifSpec.query n) : ProbComp _) >>= fun u =>
                (simulateQ gameImpl (k u)).run s.toGame) := by
              rw [gameImpl_unif_run]
              simp
        _ =ᵈ ((liftM (unifSpec.query n) : ProbComp _) >>= fun u =>
                tapeRun (k u) s m₁ m₂) :=
              EvalDistEq.bind_right _ fun u => ih u s m₁ m₂
        _ =ᵈ _ := by
              refine (tapes_bind_swap _ m₁ m₂ _).symm.trans ?_
              simp only [tapeRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                OracleQuery.cont_query, id_map, StateT.run_bind, tapeImpl_unif_run]
              simp
    · rw [gameImpl_hash_run, hashImpl_run]
      simp only [TapeState.toGame_table]
      cases h : s.table x with
      | some e =>
        simp only [Option.map_some, pure_bind]
        refine (ih e.1 s m₁ m₂).trans ?_
        simp only [tapeRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, tapeImpl_hash_run, tapeHash,
          StateT.run_mk, TapeState.withTapes_table, h, pure_bind]
        exact .rfl
      | none =>
        let sU : D → TapeState K M D := fun d =>
          { s with table := Function.update s.table x (some (d, .direct s.nU)), nU := s.nU + 1 }
        calc _ = (($ᵗ D : ProbComp D) >>= fun d =>
                (simulateQ gameImpl (k d)).run (sU d).toGame) := by
              simp only [Option.map_none, bind_map_left]
              refine bind_congr fun d => ?_
              congr 1
              simp only [sU, TapeState.toGame]
              congr 1
              exact (toGame_update s x d _).symm
          _ =ᵈ (($ᵗ D : ProbComp D) >>= fun d => tapeRun (k d) (sU d) (m₁ - 1) m₂) :=
              EvalDistEq.bind_right _ fun d => ih d (sU d) (m₁ - 1) m₂
          _ = (do let lu ← tape D m₁; let z ← drawTape lu; let lv ← tape D m₂
                  let w ← (simulateQ tapeImpl (k z.1)).run ((sU z.1).withTapes z.2 lv)
                  return (w.1, w.2.toGame)) := by
              exact (tape_bind_drawTape m₁ (fun (d : D) l => do
                let lv ← tape D m₂
                let w ← (simulateQ tapeImpl (k d)).run ((sU d).withTapes l lv)
                return (w.1, w.2.toGame))).symm
          _ =ᵈ _ := by
              refine (EvalDistEq.bind_right _ fun lu =>
                evalDistEq_bind_swap (drawTape lu) (tape D m₂) _).trans ?_
              simp only [tapeRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                OracleQuery.cont_query, id_map, StateT.run_bind, tapeImpl_hash_run, tapeHash,
                StateT.run_mk, TapeState.withTapes_table, h, bind_map_left, bind_assoc,
                TapeState.withTapes_uTape]
              exact .rfl
    · rw [gameImpl_chal_run, chalImpl_run, bind_assoc]
      let R : K → ProbComp (α × GameState K M D) := fun key => do
        let lu ← tape D m₁
        let lv ← tape D m₂
        let p ← tapeChalAt key msg (s.withTapes lu lv)
        let w ← (simulateQ tapeImpl (k p.1)).run p.2
        return (w.1, w.2.toGame)
      refine (EvalDistEq.bind_right _ (g := R) fun key => ?_).trans ?_
      · cases h : s.table (key, msg) with
        | some e =>
          let sC : TapeState K M D := { s with
            challenges := s.challenges ++ [((key, msg), e.1)], pulled := e.2.pull s.pulled }
          calc _ = (simulateQ gameImpl (k (key, e.1))).run sC.toGame := by
                simp [chalAt, h]; rfl
            _ =ᵈ tapeRun (k (key, e.1)) sC m₁ m₂ := ih _ sC m₁ m₂
            _ = R key := by
                simp [R, tapeRun, tapeChalAt, h]; rfl
        | none =>
          let sF : D → TapeState K M D := fun d => { s with
            table := Function.update s.table (key, msg) (some (d, .fresh s.nV))
            nV := s.nV + 1
            challenges := s.challenges ++ [((key, msg), d)] }
          let G : List D → D → List D → ProbComp (α × GameState K M D) := fun lu d l => do
            let w ← (simulateQ tapeImpl (k (key, d))).run ((sF d).withTapes lu l)
            return (w.1, w.2.toGame)
          calc _ = (($ᵗ D : ProbComp D) >>= fun d =>
                  (simulateQ gameImpl (k (key, d))).run (sF d).toGame) := by
                simp only [chalAt, h, TapeState.toGame_table, Option.map_none, bind_map_left]
                refine bind_congr fun d => ?_
                congr 1
                simp only [sF, TapeState.toGame]
                congr 1
                exact (toGame_update s (key, msg) d _).symm
            _ =ᵈ (($ᵗ D : ProbComp D) >>= fun d => tapeRun (k (key, d)) (sF d) m₁ (m₂ - 1)) :=
                EvalDistEq.bind_right _ fun d => ih _ (sF d) m₁ (m₂ - 1)
            _ = (($ᵗ D : ProbComp D) >>= fun u => tape D m₁ >>= fun lu =>
                  tape D (m₂ - 1) >>= fun l => G lu u l) := rfl
            _ =ᵈ (tape D m₁ >>= fun lu => ($ᵗ D : ProbComp D) >>= fun u =>
                  tape D (m₂ - 1) >>= fun l => G lu u l) :=
                evalDistEq_bind_swap _ _ _
            _ = (tape D m₁ >>= fun lu => tape D m₂ >>= fun lv => drawTape lv >>= fun z =>
                  G lu z.1 z.2) := by
                refine bind_congr fun lu => ?_
                exact (tape_bind_drawTape m₂ (G lu)).symm
            _ = R key := by
                simp only [R, tapeChalAt, TapeState.withTapes_table, h, bind_map_left,
                  TapeState.withTapes_vTape]
                rfl
      · refine (tapes_bind_swap ($ᵗ K) m₁ m₂ _).symm.trans ?_
        simp only [tapeRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, tapeImpl_chal_run, tapeChal,
          StateT.run_mk, bind_assoc]
        exact .rfl

/-! ## The experiment in pre-sampled form -/

/-- A tape is a uniform tuple read as a list. -/
theorem tape_evalDistEq (n : ℕ) :
    tape D n =ᵈ (List.ofFn <$> ($ᵗ (Fin n → D) : ProbComp (Fin n → D))) := by
  refine EvalDistEq.map_congr _ ?_
  let : MeasurableSpace D := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  exact (evalDist_mOfFn_const_uniform n ($ᵗ D : ProbComp D)
    SampleableType.evalDist_uniformSample).trans SampleableType.evalDist_uniformSample.symm

/-- The adversary followed by the verification query of its output (Definition 4, step 4). -/
def withVerify (oa : OracleComp (AdvSpec K M D) (K × M)) :
    OracleComp (AdvSpec K M D) ((K × M) × D) := do
  let x ← oa
  let d ← (liftM ((AdvSpec K M D).query (Sum.inr (Sum.inl x))) : OracleComp (AdvSpec K M D) D)
  return (x, d)

variable {ι : Type} {k t : ℕ} [DecidableEq ι]

/-- The experiment is the winning event of the real game run on the adversary followed by the
verification query. -/
theorem experiment_eq {q r : ℕ} [SampleableType (Digest ι k t)]
    (A : Adversary K M (Digest ι k t) q r) :
    experiment A = (fun z => decide (Wins z.2 z.1.1 z.1.2)) <$>
      (simulateQ gameImpl (withVerify A.run)).run GameState.init := by
  simp only [experiment, withVerify, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind,
    map_pure]
  rfl

/-- **Lemma 2**, for the experiment: the success probability is the winning probability of the
pre-sampled game on uniform tapes `U` of `q + 1` direct values and `V` of `r` challenge values. -/
theorem advantage_eq_presampled {q r : ℕ} [SampleableType (Digest ι k t)]
    (A : Adversary K M (Digest ι k t) q r) :
    advantage A =
      Pr{let U ← $ᵗ (Fin (q + 1) → Digest ι k t)
         let V ← $ᵗ (Fin r → Digest ι k t)
         let z ← (simulateQ tapeImpl (withVerify A.run)).run
           (TapeState.init (K := K) (M := M) (List.ofFn U) (List.ofFn V))}[
        Wins z.2.toGame z.1.1 z.1.2] := by
  have h2 : tapeRun (withVerify A.run) (TapeState.init (K := K) (M := M) [] []) (q + 1) r =ᵈ
      (do let U ← $ᵗ (Fin (q + 1) → Digest ι k t)
          let V ← $ᵗ (Fin r → Digest ι k t)
          let z ← (simulateQ tapeImpl (withVerify A.run)).run
            (TapeState.init (K := K) (M := M) (List.ofFn U) (List.ofFn V))
          return (z.1, z.2.toGame)) := by
    unfold tapeRun
    refine (EvalDistEq.bind_left (tape_evalDistEq (q + 1)) _).trans ?_
    rw [bind_map_left]
    refine EvalDistEq.bind_right _ fun U => ?_
    refine (EvalDistEq.bind_left (tape_evalDistEq r) _).trans ?_
    rw [bind_map_left]
    exact .rfl
  have h := ((gameImpl_evalDistEq_tapeRun (withVerify A.run)
    (TapeState.init (K := K) (M := M) [] []) (q + 1) r).trans h2).prEvent_eq
      fun z => Wins z.2 z.1.1 z.1.2
  rw [TapeState.toGame_init] at h
  rw [advantage, experiment_eq, Functor.map_map]
  simp only [decide_eq_true_eq]
  rw [h]
  simp only [map_bind, bind_pure_comp, Functor.map_map]

end ShrincsSecurity.ITSR

end
