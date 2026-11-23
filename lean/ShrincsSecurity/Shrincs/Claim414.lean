module

public import ShrincsSecurity.Shrincs.AFBounds

/-!
# Claim 4.14: `GAME.3 → GAME.4`, the shared adaptive-reprogramming hop

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.14** (txt lines 4040–4080): the
distinguisher `B₄` "is the distinguisher `B₁` of Algorithm 5 extended by the stateless path"; it
outputs `1` exactly when `A` outputs a fresh valid forgery (on either branch) on which the abort
of `GAME.3` does not fire, so one DI-Repro term covers both branches.

`B1S` is that distinguisher (`B1Srun`, `Wrapper.lean`): Algorithm 5 (`Claim42.implB`) on the
augmented signing phase `progS`, with output `(W_sf ∧ ¬C₁) ∨ W_sl`.

* `B1Srun_hashBound`, `B1Srun_reproBound`: at most `q_{h,1} + q_{h,2} + L + 1` queries to `O_b`
  and at most `L` reprogramming calls (the counts of `B₁` in Claim 4.2).
* `claim_4_14`: `Pr_{GAME.3}[success] ≤ Pr_{GAME.4}[success] + Adv^{DI-Repro}(B₁⁺)`, where
  `GAME.3`'s success is `(W_sf ∧ ¬C₁) ∨ W_sl` in `GAME.2` (`gameS implG`) and `GAME.4` is taken in
  its presampled form (`gameHybS`): world `0` of `B₁⁺` is `gameS implG`, world `1` is
  `gameS implG2` (lazy `GAME.4`, as `Claim42.stage2_lazy`), which is `gameHybS` by presampling
  (as `Claim42.presample`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys implG X2)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

open Fxmss.Rom (IsRoQuery' St completion otherMsg anchorList skOf pkSfOf SkIdx Transcript
  implG2 implHyb hon digOf betaOf Anchor)
open Fxmss.Rom.Claim42 (DSpec fwd implB unusedCount implB_hash_step implB_repro_step
  isQueryBoundP_run_potential unusedCount_init liftM_bound isQueryBoundP_zero_bind LS projSt
  modeOf InvB stage2_lazy stage1_lazy stage1_submitted evalDistEq_of_eq presample)

namespace Claim414

variable {pr Msg enc}

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Fintype pr.Y]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The augmented signing phase makes at most `q_{h,2} + 1` queries to `H_msg^sf`: `A_F`'s
(`A`'s) queries and the verification query; the completion makes none. -/
theorem progS_roBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) (st : A.State)
    (K : Keys pr) :
    (progS pr Msg enc A.toShrincsAdversary st K).IsQueryBoundP
      (IsRoQuery' pr (BMsg pr Msg)) (qh₂ + 1) := by
  unfold progS
  refine isQueryBoundP_bind (forgeExt_roBound pr Msg enc A st K.S K.toPK) fun out _ => ?_
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr (by omega), fun _ => ?_⟩
  simp only [IsRoQuery', ↓reduceIte, Nat.sub_self]
  simpa using Fxmss.Rom.Claim42.completion_roBound (otherMsg (BMsg pr Msg) out.1.1)
    (anchorList vp.params K.S)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg]
  [DecidableEq Msg] [Nontrivial Msg] in
/-- The structure phase of `B₁⁺` makes at most `q_{h,1}` queries to `O_b`. -/
theorem fwd_hashBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    (simulateQ (fwd pr (BMsg pr Msg)) A.chooseShape).IsQueryBoundP
      (Repro.IsHashQuery pr.Y (X2 pr (BMsg pr Msg))) qh₁ := by
  refine A.roBound₁.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | x
    · exact ht.elim
    · simp [fwd, Repro.IsHashQuery]
  · rcases t with n | x
    · simp [fwd, Repro.IsHashQuery]
    · exact (ht trivial).elim


/-! ## World `b` of `B₁⁺` is `GAME.2` / lazy `GAME.4` -/

variable (pr Msg enc) in
/-- The game simulated by `B₁⁺` in world `b`: `GAME.2` (`gameS implG`) for `b = 0`, lazy
`GAME.4` (`gameS implG2`) for `b = 1`. -/
noncomputable def gameOfS (b : Bool) {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    ProbComp (Option (Transcript pr (BMsg pr Msg) × Ext)) := do
  let pk ← $ᵗ pr.PkSeed
  let z ← stage1S pr Msg enc A
  stageGS pr Msg enc A (fun K sk => modeOf b K sk) pk z

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] in
/-- `B₁⁺` after the structure phase, in the lazy world `b`, is the game after the structure
phase (port of `Claim42.lazy_B1cont`, generic `stage2_lazy` on the program `progS`). -/
theorem lazy_B1Scont (b : Bool) {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (pk : pr.PkSeed) (z : Structure × A.State) (ls : LS pr (BMsg pr Msg))
    (hls : ls.submitted = ∅) :
    Prod.fst <$> (simulateQ (Repro.lazyDIImpl b) (B1Scont pr Msg enc A pk z)).run ls =ᵈ
      (fun o => decide (OEv WinNotC1S o)) <$>
        stageGS pr Msg enc A (fun K sk => modeOf b K sk) pk (z, Fxmss.Rom.Claim42.LS.cache ls) := by
  have hl : ∀ {β : Type} (oa : ProbComp β) (s : LS pr (BMsg pr Msg)),
      (simulateQ (Repro.lazyDIImpl b)
        (liftM oa : OracleComp (DSpec pr (BMsg pr Msg)) β)).run s =
        (fun x => (x, s)) <$> oa := fun oa s => Fxmss.simulateQ_add_liftM_run _ oa s
  unfold B1Scont stageGS
  by_cases hv : z.1.TreeValid vp.params.hsf
  swap
  · rw [ite_eq_left hv, ite_eq_left hv]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact evalDistEq_of_eq (by rw [decide_eq_false (by simp [OEv])])
  rw [ite_eq_right (not_not.2 hv), ite_eq_right (not_not.2 hv)]
  simp only [simulateQ_bind, StateT.run_bind, hl, bind_map_left, map_bind]
  refine EvalDistEq.bind_right _ fun f => EvalDistEq.bind_right _ fun pkSl => ?_
  have hi : InvB (Msg := BMsg pr Msg) ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ ls
      (St.init pr (BMsg pr Msg) ∅) :=
    ⟨fun _ h => by simp [St.init] at h, fun _ h => by simp [hls] at h⟩
  have h2 := (stage2_lazy vp.valid b hv (skOf pr z.1 f)
    (progS pr Msg enc A z.2 ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩) ls
    (St.init pr (BMsg pr Msg) ∅) hi).map (fun r => decide (WinNotC1S
      (Transcript.ofRun pr (BMsg pr Msg) ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩
        (r.1.1, r.2), r.1.2)))
  simp only [Functor.map_map] at h2
  simp only [simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]
  exact h2

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] in
/-- **World `b` of `DI-Repro` run by `B₁⁺` is `GAME.2` / lazy `GAME.4`** on the output bit. -/
theorem lazy_B1Srun (b : Bool) {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    (simulateQ (Repro.lazyDIImpl b) (B1Srun pr Msg enc A)).run' Repro.LazyState.init =ᵈ
      (fun o => decide (OEv WinNotC1S o)) <$> gameOfS pr Msg enc b A := by
  have hl : ∀ {β : Type} (oa : ProbComp β) (s : LS pr (BMsg pr Msg)),
      (simulateQ (Repro.lazyDIImpl b)
        (liftM oa : OracleComp (DSpec pr (BMsg pr Msg)) β)).run s =
        (fun x => (x, s)) <$> oa := fun oa s => Fxmss.simulateQ_add_liftM_run _ oa s
  unfold B1Srun gameOfS
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, StateT.run_bind, hl, bind_map_left, map_bind]
  refine EvalDistEq.bind_right _ fun pk => ?_
  have hst : stage1S pr Msg enc A = Prod.map id Fxmss.Rom.Claim42.LS.cache <$>
      (simulateQ (Repro.lazyDIImpl b) (simulateQ (fwd pr (BMsg pr Msg)) A.chooseShape)).run
        Repro.LazyState.init := by
    rw [stage1_lazy]; rfl
  rw [hst, bind_map_left]
  refine EvalDistEq.bind_congr_of_support _ fun p hp => ?_
  have hsub := stage1_submitted b A.chooseShape _ p hp
  exact lazy_B1Scont b A pk p.1 p.2 hsub

omit [Fintype pr.Digest] [DecidableEq pr.Digest] [Inhabited pr.Digest] in
/-- `Pr[GAME.2 or lazy GAME.4 ⇒ (W_sf ∧ ¬C₁) ∨ W_sl] = Pr[DI-Repro_b(B₁⁺) ⇒ 1]`. -/
theorem prEvent_gameOfS (b : Bool) {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let o ← gameOfS pr Msg enc b A}[OEv WinNotC1S o] =
      Pr{let x ← Repro.diExperiment b (B1Srun pr Msg enc A)}[x = true] := by
  have h := ((Repro.diExperiment_evalDistEq_lazy b _).trans
    (lazy_B1Srun b A)).prEvent_eq (· = true)
  rw [h, Functor.map_map]
  congr 2
  funext o
  simp

/-! ## Lazy `GAME.4` is `GAME.4` with presampled digests -/

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y]
  [DecidableEq pr.Digest] in
/-- **Lazy `GAME.4` is `gameHybS`** (honest data dropped), as distributions of outcomes (port of
`Claim42.gameG2_evalDistEq_gameHyb`, generic `presample` on the program `progS`). -/
theorem gameS_implG2_evalDistEq {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    gameS pr Msg enc A (implG2 pr (BMsg pr Msg)) =ᵈ
      Option.map Prod.fst <$> gameHybS pr Msg enc A := by
  unfold gameS gameHybS setupHybS
  simp only [bind_assoc, pure_bind, map_bind]
  refine EvalDistEq.bind_right _ fun pk => EvalDistEq.bind_right _ fun z => ?_
  unfold stageGS stageHybS
  by_cases hv : z.1.1.TreeValid vp.params.hsf
  swap
  · simp only [hv, not_false_eq_true, ↓reduceIte, map_pure, Option.map_none]
    exact ((EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_const _ _)).symm
  simp only [hv, not_true_eq_false, ↓reduceIte, map_bind, map_pure, Option.map_some,
    Fxmss.Rom.Claim42.hon_pkSf]
  refine EvalDistEq.symm ?_
  refine (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun pkSl => ?_)
  have h := (presample (K := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 u)⟩) hv u
    (progS pr Msg enc A z.1.2 ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 u)⟩)
    (St.init pr (BMsg pr Msg) z.2) rfl).map
      (fun r => some (Transcript.ofRun pr (BMsg pr Msg)
        ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 u)⟩ (r.1.1, r.2), r.1.2))
  simp only [map_bind] at h
  simp only [bind_pure_comp]
  exact h

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Y]
  [SampleableType pr.Y] [Inhabited pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- `HEv E o ↔ OEv E (o.map Prod.fst)`. -/
theorem hEv_eq_oEv (E : Transcript pr (BMsg pr Msg) × Ext → Prop)
    (o : Option ((Transcript pr (BMsg pr Msg) × Ext) × Fxmss.Rom.Honest pr)) :
    HEv E o = OEv E (o.map Prod.fst) := by
  cases o <;> rfl

end Claim414

open Claim414

-- The instance arguments of the statement are kept as given (used by `B1S`, `Theorem41.lean`).
set_option linter.unusedSectionVars false in
/-- `B₁⁺` makes at most `q_{h,1} + q_{h,2} + L + 1` queries to `O_b`. -/
theorem B1Srun_hashBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    (B1Srun pr Msg enc A.toShrincsAdversary).IsQueryBoundP
      (Repro.IsHashQuery pr.Y (X2 pr (BMsg pr Msg))) (qh₁ + qh₂ + L + 1) := by
  have hnot : ∀ n, ¬ Repro.IsHashQuery pr.Y (X2 pr (BMsg pr Msg)) (.inl n) := fun _ h => h
  have h1 := fwd_hashBound A
  unfold B1Srun
  refine (isQueryBoundP_bind (n := 0) (m := qh₁ + (qh₂ + 1 + L)) (liftM_bound _ _ hnot)
    fun pk _ => isQueryBoundP_bind (n := qh₁) (m := qh₂ + 1 + L) h1 fun z hz => ?_).mono
      (by omega)
  have hz' : z ∈ support A.chooseShape := support_simulateQ_subset _ _ hz
  unfold B1Scont
  by_cases hv : z.1.TreeValid vp.params.hsf
  swap
  · rw [ite_eq_left hv]; simp
  rw [ite_eq_right (not_not.2 hv)]
  refine isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun f _ =>
    isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun pkSl _ => ?_
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  refine (isQueryBoundP_run_potential (implB pr (BMsg pr Msg) _ _) (unusedCount _)
    (fun t s _ m k hk => implB_hash_step _ _ t s m k hk)
    (progS_roBound A z.2 _) _).mono ?_
  have := (unusedCount_init (Msg := BMsg pr Msg)
    ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ ∅).trans (A.anchors_le z hz' hv)
  omega

-- The instance arguments of the statement are kept as given (used by `B1S`, `Theorem41.lean`).
set_option linter.unusedSectionVars false in
/-- `B₁⁺` makes at most `L` reprogramming calls. -/
theorem B1Srun_reproBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    (B1Srun pr Msg enc A.toShrincsAdversary).IsQueryBoundP
      (Repro.IsReproQuery pr.Y (X2 pr (BMsg pr Msg))) L := by
  have hnot : ∀ n, ¬ Repro.IsReproQuery pr.Y (X2 pr (BMsg pr Msg)) (.inl n) := fun _ h => h
  have h1 : (simulateQ (fwd pr (BMsg pr Msg)) A.chooseShape).IsQueryBoundP
      (Repro.IsReproQuery pr.Y (X2 pr (BMsg pr Msg))) 0 :=
    isQueryBoundP_simulateQ_zero _ fun t => by
      rcases t with n | x <;> simp [fwd, Repro.IsReproQuery]
  unfold B1Srun
  refine (isQueryBoundP_bind (n := 0) (m := 0 + L) (liftM_bound _ _ hnot)
    fun pk _ => isQueryBoundP_bind (n := 0) (m := L) h1 fun z hz => ?_).mono (by omega)
  have hz' : z ∈ support A.chooseShape := support_simulateQ_subset _ _ hz
  unfold B1Scont
  by_cases hv : z.1.TreeValid vp.params.hsf
  swap
  · rw [ite_eq_left hv]; simp
  rw [ite_eq_right (not_not.2 hv)]
  refine isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun f _ =>
    isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun pkSl _ => ?_
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  refine (isQueryBoundP_run_potential (p := fun _ => False) (implB pr (BMsg pr Msg) _ _)
    (unusedCount _) (fun t s _ m k hk => implB_repro_step _ _ t s m k hk)
    (isQueryBoundP_false _ 0) _).mono ?_
  have := (unusedCount_init (Msg := BMsg pr Msg)
    ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ ∅).trans (A.anchors_le z hz' hv)
  omega

/-- **The augmented distinguisher `B₁⁺` of Claim 4.14** against `DI-Repro` (Definition C.2) for
`H_msg^sf`, with `X₁ = Y`, `X₂ = (PK.seed, PK.sf, idx, M̃)`. -/
noncomputable def B1S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Repro.DIAdversary pr.Y (X2 pr (BMsg pr Msg)) pr.Digest (qh₁ + qh₂ + L + 1) L where
  run := B1Srun pr Msg enc A.toShrincsAdversary
  hashBound := B1Srun_hashBound pr Msg enc A
  reproBound := B1Srun_reproBound pr Msg enc A

/-- **Claim 4.14** (`GAME.3 → GAME.4`): the success of `GAME.3`, `(W_sf ∧ ¬C₁) ∨ W_sl` in `GAME.2`,
is at most the success of `GAME.4` plus the DI-Repro advantage of `B₁⁺`. -/
theorem claim_4_14 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Pr{let o ← gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg))}[OEv WinNotC1S o] ≤
      Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv WinNotC1S o] +
        ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) := by
  have h0 := prEvent_gameOfS false A.toShrincsAdversary
  have h1 := prEvent_gameOfS true A.toShrincsAdversary
  have e0 : gameOfS pr Msg enc false A.toShrincsAdversary =
      gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg)) := rfl
  have e1 : gameOfS pr Msg enc true A.toShrincsAdversary =
      gameS pr Msg enc A.toShrincsAdversary (implG2 pr (BMsg pr Msg)) := rfl
  rw [e0] at h0
  rw [e1] at h1
  have h2 : Pr{let o ← gameS pr Msg enc A.toShrincsAdversary (implG2 pr (BMsg pr Msg))}[
      OEv WinNotC1S o] = Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv WinNotC1S o] := by
    rw [(gameS_implG2_evalDistEq A.toShrincsAdversary).prEvent_eq (OEv WinNotC1S),
      Functor.map_map]
    congr 2
    funext o
    rw [hEv_eq_oEv]
  rw [← h2, h0, h1, B1S, Repro.diAdvantage]
  exact Fxmss.Rom.Claim42.le_add_ofReal_abs (prEvent_ne_top _) (prEvent_ne_top _)

end ShrincsSecurity.Shrincs

end
