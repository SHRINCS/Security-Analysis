module

public import ShrincsSecurity.Shrincs.AFBounds
public import ShrincsSecurity.Shrincs.VirtualTree

/-!
# Claim 4.15: `GAME.4 → GAME.5`, the stateful-branch forgeries

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.15** (p. 65, txt lines 4180–4215):
`Succ₄ − Succ₅ = Pr_{GAME.4}[W_sf]` is at most the seven collection summands of Theorem 4.2 for
the augmented reductions `B₂⁺, B₃,γ⁺, B₄⁺, B₅⁺, B₆⁺, B₇⁺, B₈⁺` (`B2S … B8S`).

As required by M Claim 4.15 (p. 65), every augmented collection reduction `B2S … B8S`:
* **Stage 1:** runs the Section 4.7 FXMSS first stage (whose challenge tweaks are exclusively
  stateful: `grindAdrs`, `chainAdrs`, `pkAdrs`, `treeAdrs`), samples the uniform stateless secret
  table `u_sl ←$ (SlSecAdrs vp → Y)`, and precomputes `PK.sl` together with the full virtual
  SLH-DSA hypertree table `tbl` by querying the game's collection oracle `O_coll` via
  `slVirtualTreeM`. By stateless-vs-stateful tweak disjointness (`not_isStateful_of_isStateless`
  and `isStateful_of_mem_shrincsX_Omega` for `B₈⁺`), no collection query is refused and the
  stateful challenge log is unchanged (`simulateQ_slVirtualTreeM_{stcr,ud,tcr,pre,excl}`).
* **Stage 2:** runs the Section 4.7 FXMSS second stage with `AFTable` (using the precomputed
  `PK.sl` and `tbl` via `tablePubQ` / `slSignTable`), making **zero** stateless `Th_λ` evaluations
  in Stage 2.

By `stageHyb_AFTable_eq_AFEager`, each augmented reduction's experiment has the exact same output
distribution as sampling `u_sl ←$ (SlSecAdrs vp → Y)` and running the Section 4.7 reduction on
`AFEager u_sl`, and `gameHyb_AFEager_evalDistEq_gameHyb_AF` bridges back to `gameHyb 0 (AF A)`
and `gameHybS A`.

* `B2S`, `B3S`, `B4S`, `B5S`, `B6S`, `B7S`, `B8S`: the seven Stage-1-precomputing augmented
  reductions.
* `gameHybS_map`: `GAME.4` with presampled digests (`gameHybS`), with `A_F`'s extra output
  dropped, **is** `F.2` for `A_F` (`gameHyb 0`).
* `claim_4_15`: `Pr_{GAME.4}[W_sf ∧ ¬C₁] ≤ Succ(B2S) + Σ_{γ < w−2} Adv(B3S γ) + … + Succ(B8S)`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys gameHyb)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

namespace Claim415

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Fintype pr.Y]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The signing phase `stage2Prog` of Section 4.7 played by `A_F` is `progS` with `A_F`'s extra
output dropped. -/
theorem stage2Prog_AFAdv {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : (AFAdv pr Msg enc A).State) (K : Keys pr) :
    Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A) st K =
      (fun r => r.1) <$> progS pr Msg enc A st K := by
  simp [Fxmss.Rom.stage2Prog, progS, AFAdv, map_bind]

/-- The arithmetic of the telescope of Theorem 4.2 after Claim 4.10. -/
theorem telescope {h e3 e5 e6 e6' e7 e8 e9 a2 ud a4 a5 a6 a7 a8 : ℝ≥0∞}
    (hx : h ≤ e3 + e5 + e6 + e7 + e8 + e9)
    (h3 : e3 ≤ a2) (h4 : e6 ≤ e6' + ud) (h5 : e5 ≤ a4) (h6 : e6' ≤ a5) (h7 : e7 ≤ a6)
    (h8 : e8 ≤ a7) (h9 : e9 ≤ a8) :
    h ≤ a2 + ud + a4 + a5 + a6 + a7 + a8 := by
  calc h ≤ e3 + e5 + e6 + e7 + e8 + e9 := hx
    _ ≤ a2 + a4 + (a5 + ud) + a6 + a7 + a8 := by
        gcongr
        exact h4.trans (by gcongr)
    _ = a2 + ud + a4 + a5 + a6 + a7 + a8 := by ring

/-! ## Helpers for Stage-1 virtual-tree precomputation -/

/-- Every record appended by `runRef` satisfies a predicate respected by `rec` on the target list. -/
private theorem mem_runRef_snd {D T R Q : Type} [DecidableEq D] [SampleableType R]
    (ans : T → R → R) (rec : T → R → Q) (P : Q → Prop) :
    ∀ (l : List (D × T)) (u : D → R) (qs : List Q) (z : (D → R) × List Q),
      z ∈ support (Fxmss.Rom.Hyb.runRef ans rec l u qs) →
      (∀ q ∈ qs, P q) → (∀ pt ∈ l, ∀ x, P (rec pt.2 x)) →
      ∀ q ∈ z.2, P q
  | [], _, qs, z, hz, hqs, _ => by
    simp only [Fxmss.Rom.Hyb.runRef, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hqs
  | (p, t) :: ts, u, qs, z, hz, hqs, hl => by
    simp only [Fxmss.Rom.Hyb.runRef, mem_support_bind_iff] at hz
    obtain ⟨x, -, hz⟩ := hz
    refine mem_runRef_snd ans rec P ts _ _ z hz ?_ (fun pt hpt => hl pt (by simp [hpt]))
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hqs q hq
    · rw [List.mem_singleton.1 hq]; exact hl (p, t) (by simp) x

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- Every target produced by `Hyb.targets` has a stateful tweak (`SfAdrs.chainAdrs`). -/
private theorem isStateful_of_mem_targets (pk : pr.PkSeed) (sel : ℕ → Option ℕ) (S : Structure)
    (ys : Fxmss.Rom.Anchor vp.params S → pr.Digest)
    {pt : Fxmss.Rom.SkIdx vp.params S × SLHDSA.Adrs}
    (hpt : pt ∈ Fxmss.Rom.Hyb.targets pr pk sel S ys) :
    Scheme.IsStateful pt.2 := by
  unfold Fxmss.Rom.Hyb.targets at hpt
  split_ifs at hpt with hS
  · obtain ⟨j, -, h⟩ := (Fxmss.Rom.Hyb.mem_targetsOf pr).1 hpt
    rw [h]
    exact SfAdrs.isStateful_toAdrs _
  · simp at hpt

/-- Generic Stage-1 precomputing SM-TCR reduction builder: runs Stage-1 queries `qs` (recording
accepted challenges), samples `uSl ←$ (SlSecAdrs vp → pr.Y)`, precomputes `(pkSl, tbl)` via
`slVirtualTreeM` against `O_coll`, and runs `forge` in Stage 2. -/
noncomputable def mkTcrAdvS {M : Type} [DecidableEq M]
    (th : TweakableHash pr.PkSeed SLHDSA.Adrs M pr.Y) (p : ℕ)
    {qs_n : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs_n)
    (qs : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State →
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)) Unit)
    (forge : (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State × List (SLHDSA.Adrs × M)) ×
        (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y)) →
      pr.PkSeed → ProbComp (ℕ × M)) :
    SM_DT_TCR_Adversary (Notions.smTcrMemberProblem th pr.collection p) where
  State := (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State × List (SLHDSA.Adrs × M)) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A)) :
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)) _)
    let (_, savedQ) ← (simulateQ
        (Fxmss.recordTcrImpl (Notions.smTcrMemberProblem th pr.collection p)) (qs d)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)) _)
    let vt ← slVirtualTreeM pr (tcrCollCall pr th p) uSl
    return ((d, savedQ), uSl, vt)
  forge := forge

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
/-- Whenever the FXMSS Stage-1 queries `qs` deterministically record a list `Q d pk` of stateful
targets, `mkTcrAdvS` has the same SM-TCR experiment distribution as sampling `uSl ←$ _` and
running `mkTcrAdv` with `forge'` agreeing with `forge` at `slVirtualTreeDet pr pk uSl`. -/
theorem mkTcrAdvS_exp_eq {M : Type} [DecidableEq M]
    (th : TweakableHash pr.PkSeed SLHDSA.Adrs M pr.Y) (p : ℕ)
    {qs_n : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs_n)
    (qs : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State →
      OracleComp (Fxmss.TcrOracleSpec (Notions.smTcrMemberProblem th pr.collection p)) Unit)
    (forge : (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State × List (SLHDSA.Adrs × M)) ×
        (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y)) →
      pr.PkSeed → ProbComp (ℕ × M))
    (forge' : (SlSecAdrs vp → pr.Y) →
      Fxmss.Rom.Setup pr (BMsg pr Msg) A.State × List (SLHDSA.Adrs × M) →
      pr.PkSeed → ProbComp (ℕ × M))
    (Q : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State → pr.PkSeed → List (SLHDSA.Adrs × M))
    (C : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State → pr.PkSeed → List SLHDSA.Adrs)
    (hq : ∀ pk, ∀ d ∈ support (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A)),
      (simulateQ (SM_DT_TCR_oracles (Notions.smTcrMemberProblem th pr.collection p) pk)
        (qs d)).run ([], []) = pure ((), (Q d pk, C d pk)))
    (hsf : ∀ pk, ∀ d ∈ support (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A)),
      ∀ e ∈ Q d pk, Scheme.IsStateful e.1)
    (hforge : ∀ d uSl pk,
      forge ((d, Q d pk), uSl, slVirtualTreeDet pr pk uSl) pk = forge' uSl (d, Q d pk) pk) :
    SM_DT_TCR_Experiment (mkTcrAdvS pr Msg enc th p A qs forge) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (Fxmss.mkTcrAdv (Notions.smTcrMemberProblem th pr.collection p)
          (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A))
          qs (forge' uSl))) := by
  let prob := Notions.smTcrMemberProblem th pr.collection p
  let g₁ : ProbComp (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) :=
    Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A)
  have hLHS : SM_DT_TCR_Experiment (mkTcrAdvS pr Msg enc th p A qs forge) =ᵈ
      (do let pk ← prob.th.seedGen
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let out ← forge' uSl (d, Q d pk) pk
          return Fxmss.tcrWin prob pk (Q d pk) out) := by
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right prob.th.seedGen fun pk => ?_
    simp only [mkTcrAdvS, SM_DT_TCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := Fxmss.simulateQ_recordTcr_run prob pk (qs d) [] []
    rw [hq pk d hd, map_pure] at hrec
    simp only [SM_DT_TCR_oracles] at hrec
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_tcr pr th p pk uSl (Q d pk) (C d pk)
      (hsf pk d hd)
    simp only [SM_DT_TCR_oracles] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure,
      pure_bind, hforge d uSl pk]
    refine EvalDistEq.bind_right _ fun out => ?_
    rcases out with ⟨j, m⟩
    simp only [Fxmss.tcrWin]
    split <;> rename_i h <;> simp [h, prob]
  have hRHS1 : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (Fxmss.mkTcrAdv prob g₁ qs (forge' uSl))) =ᵈ
      (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let pk ← prob.th.seedGen
          let d ← g₁
          let out ← forge' uSl (d, Q d pk) pk
          return Fxmss.tcrWin prob pk (Q d pk) out) := by
    refine EvalDistEq.bind_right _ fun uSl => ?_
    unfold SM_DT_TCR_Experiment
    refine EvalDistEq.bind_right prob.th.seedGen fun pk => ?_
    simp only [Fxmss.mkTcrAdv, SM_DT_TCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support g₁ fun d hd => ?_
    have hrec := Fxmss.simulateQ_recordTcr_run prob pk (qs d) [] []
    rw [hq pk d hd, map_pure] at hrec
    simp only [SM_DT_TCR_oracles] at hrec
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure,
      pure_bind]
    refine EvalDistEq.bind_right _ fun out => ?_
    rcases out with ⟨j, m⟩
    simp only [Fxmss.tcrWin]
    split <;> rename_i h <;> simp [h]
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment (Fxmss.mkTcrAdv prob g₁ qs (forge' uSl))) =ᵈ
      (do let pk ← prob.th.seedGen
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let out ← forge' uSl (d, Q d pk) pk
          return Fxmss.tcrWin prob pk (Q d pk) out) := by
    refine hRHS1.trans ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

end Claim415

open Claim415

/-! ## The seven Stage-1-precomputing augmented reductions `B2S … B8S` -/

/-- **Augmented `B₂` (`B2S`)** for Claim 4.15 (S-TCR(Prop) of `H_grind ∈ Th_λ`, `L` targets):
runs `B₂`'s Stage-1 grinding challenges (recording `savedQ`), samples `uSl`, precomputes
`(PK.sl, tbl)` via `O_coll` (`slVirtualTreeM`), and runs Stage 2 using `AFTable` (zero stateless
`Th_λ` evaluations in Stage 2). -/
noncomputable def B2S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.STCRAdversary (Fxmss.Rom.probGrind pr L) where
  State :=
    (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State ×
      List ((SLHDSA.Adrs × pr.Digest) × (pr.Y × ℕ))) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (Fxmss.STcrOracleSpec (Fxmss.Rom.probGrind pr L)) _)
    let (_, savedQ) ← (simulateQ (Fxmss.recordSTcrImpl (Fxmss.Rom.probGrind pr L))
      (Fxmss.Rom.B2queries pr (BMsg pr Msg) L d)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Fxmss.STcrOracleSpec (Fxmss.Rom.probGrind pr L)) _)
    let vt ← slVirtualTreeM pr
      (stcrCollCall pr (Fxmss.Rom.thGrind pr) (Fxmss.Rom.targetSumProp pr) L) uSl
    return ((d, savedQ), uSl, vt)
  forge st pk :=
    let ((d, savedQ), uSl, (pkSl, tbl)) := st
    Fxmss.Rom.B2extract pr (BMsg pr Msg) savedQ pk <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk

/-- **Augmented `B₃,γ` (`B3S γ`)** for Claim 4.15 (SM-UD of `F ∈ Th_λ`, `L · lsf` targets):
runs `B₃,γ`'s Stage-1 grinding + challenge phase (`pickProg`), samples `uSl`, precomputes
`(PK.sl, tbl)` via `O_coll` (`slVirtualTreeM`), and runs Stage 2 using `AFTable` (zero stateless
`Th_λ` evaluations in Stage 2). -/
noncomputable def B3S (γ : ℕ) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_UD_Adversary (Fxmss.Rom.probUD pr (L * vp.params.lsf)) where
  State := Fxmss.Rom.Setup pr (BMsg pr Msg) A.State ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y))
  pick := do
    let d ← (liftM (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (Fxmss.Rom.Hyb.FSpec pr) _)
    let u' ← Fxmss.Rom.Hyb.pickProg pr (Fxmss.Rom.Hyb.selUD γ) d.ys d.u
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Fxmss.Rom.Hyb.FSpec pr) _)
    let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
    return ({ d with u := u' }, uSl, vt)
  distinguish st pk :=
    let (d, uSl, (pkSl, tbl)) := st
    (fun o => decide (Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o)) <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary
        (Fxmss.Rom.betaOf pr (γ + 1) pk d.u) d pk

/-- **Augmented `B₄` (`B4S`)** for Claim 4.15 (SM-TCR of `F ∈ Th_λ`, `L · lsf · w` targets):
precomputes `(PK.sl, tbl)` in Stage 1 via `O_coll` and runs Stage 2 using `AFTable`. -/
noncomputable def B4S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (Fxmss.Rom.probTcrF pr (L * vp.params.lsf * vp.params.w)) :=
  mkTcrAdvS pr Msg enc (Fxmss.Rom.thF pr) (L * vp.params.lsf * vp.params.w) A.toShrincsAdversary
    (Fxmss.Rom.B4queries pr (BMsg pr Msg) L)
    fun st pk =>
      let ((d, savedQ), uSl, (pkSl, tbl)) := st
      Fxmss.Rom.B4extract pr (BMsg pr Msg) savedQ pk <$>
        Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
          (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk

/-- **Augmented `B₅` (`B5S`)** for Claim 4.15 (SM-PRE of `F ∈ Th_λ`, `L · lsf` targets):
runs `B₅`'s Stage-1 grinding + challenge phase (`pickProg`), samples `uSl`, precomputes
`(PK.sl, tbl)` via `O_coll` (`slVirtualTreeM`), and runs Stage 2 using `AFTable` (zero stateless
`Th_λ` evaluations in Stage 2). -/
noncomputable def B5S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_PRE_Adversary (Fxmss.Rom.probPre pr (L * vp.params.lsf)) where
  State := Fxmss.Rom.Setup pr (BMsg pr Msg) A.State ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (Fxmss.Rom.Hyb.FSpec pr) _)
    let u' ← Fxmss.Rom.Hyb.pickProg pr Fxmss.Rom.Hyb.selPre d.ys d.u
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Fxmss.Rom.Hyb.FSpec pr) _)
    let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
    return ({ d with u := u' }, uSl, vt)
  invert st pk :=
    let (d, uSl, (pkSl, tbl)) := st
    Fxmss.Rom.Hyb.extract5 pr (BMsg pr Msg) pk d.ys <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary
        (fun id ch _ => Fxmss.Rom.skOf pr d.S d.u id ch) d pk

/-- **Augmented `B₆` (`B6S`)** for Claim 4.15 (SM-TCR of `Th_lsf ∈ Th_λ`, `L` targets):
precomputes `(PK.sl, tbl)` in Stage 1 via `O_coll` and runs Stage 2 using `AFTable`. -/
noncomputable def B6S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (Fxmss.Rom.probTcrLsf pr L) :=
  mkTcrAdvS pr Msg enc (Fxmss.Rom.thLsf pr) L A.toShrincsAdversary
    (Fxmss.Rom.B6queries pr (BMsg pr Msg) L)
    fun st pk =>
      let ((d, savedQ), uSl, (pkSl, tbl)) := st
      Fxmss.Rom.B6extract pr (BMsg pr Msg) savedQ pk <$>
        Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
          (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk

/-- **Augmented `B₇` (`B7S`)** for Claim 4.15 (SM-TCR of `H ∈ Th_λ`, `L − 1` targets):
precomputes `(PK.sl, tbl)` in Stage 1 via `O_coll` and runs Stage 2 using `AFTable`. -/
noncomputable def B7S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (Fxmss.Rom.probTcrH pr (L - 1)) :=
  mkTcrAdvS pr Msg enc (Fxmss.Rom.thH pr) (L - 1) A.toShrincsAdversary
    (fun d => OracleComp.liftComp (Fxmss.Rom.prog7 pr (BMsg pr Msg) d) _)
    fun st pk =>
      let ((d, savedQ), uSl, (pkSl, tbl)) := st
      Fxmss.Rom.extract7 pr (BMsg pr Msg) savedQ pk <$>
        Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
          (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk

/-- **Augmented `B₈` (`B8S`)** for Claim 4.15 (sm-tcr-excl of `Th_{2∪lsf} ∈ Th_λ`,
`L + (L − 1)` targets): runs `B₈`'s Stage-1 tree challenges (recording `savedQ`), samples `uSl`,
precomputes `(PK.sl, tbl)` via `O_coll` (`slVirtualTreeM`, never colliding with `Ω` of any
stateful target), and runs Stage 2 using `AFTable` (zero stateless `Th_λ` evaluations in Stage 2). -/
noncomputable def B8S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.SMTCRExclAdversary (Fxmss.Rom.probExcl pr (L + (L - 1))) where
  State :=
    (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State ×
      List (SLHDSA.Adrs × Fxmss.Rom.Msg9 pr)) ×
    (SlSecAdrs vp → pr.Y) × (pr.Y × (SLHDSA.Adrs → Option pr.Y))
  choose := do
    let d ← (liftM (Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFAdv pr Msg enc A.toShrincsAdversary)) :
      OracleComp (Fxmss.ExclOracleSpec (Fxmss.Rom.probExcl pr (L + (L - 1)))) _)
    let (_, savedQ) ← (simulateQ (Fxmss.recordExclImpl (Fxmss.Rom.probExcl pr (L + (L - 1))))
      (OracleComp.liftComp (Fxmss.Rom.prog9 pr (BMsg pr Msg) d) _)).run []
    let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
      OracleComp (Fxmss.ExclOracleSpec (Fxmss.Rom.probExcl pr (L + (L - 1)))) _)
    let vt ← slVirtualTreeM pr (exclCollCall pr (L + (L - 1))) uSl
    return ((d, savedQ), uSl, vt)
  forge st pk :=
    let ((d, savedQ), uSl, (pkSl, tbl)) := st
    Fxmss.Rom.extract9 pr (BMsg pr Msg) savedQ pk <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFTable pr Msg enc A uSl pkSl tbl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk

/-! ## Exact experiment equivalences between `B2S … B8S` and `uSl ←$ _; B2 … B8 (AFEager uSl)` -/

namespace Claim415

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] in
/-- `B2S` experiment = sampling `uSl` and running `B2 (AFEager uSl)`. -/
theorem B2S_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.STCR_Experiment (B2S pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.STCR_Experiment
          (Fxmss.Rom.B2 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let prob := Fxmss.Rom.probGrind pr L
  let g₁ : ProbComp (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) :=
    Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hsf : ∀ {σ : Type} (pk : pr.PkSeed) (d : Fxmss.Rom.Setup pr (BMsg pr Msg) σ),
      ∀ e ∈ Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk, Scheme.IsStateful e.1.1 := by
    intro σ pk d e he
    unfold Fxmss.Rom.B2targets at he
    split_ifs at he with hS
    · obtain ⟨tm, htm, hrec⟩ := List.mem_filterMap.1 he
      obtain ⟨id, -, rfl⟩ := List.mem_map.1 htm
      simp only [Fxmss.stcrRecord] at hrec
      cases hlc : Notions.leastCounter (Fxmss.Rom.thGrind pr) (Fxmss.Rom.targetSumProp pr) pk
          (SfAdrs.grindAdrs id).toAdrs (Fxmss.Rom.digOf pr d.ys id) with
      | none => simp [hlc] at hrec
      | some c =>
        simp only [hlc, Option.map_some, Option.some.injEq] at hrec
        rw [← hrec]
        exact SfAdrs.isStateful_toAdrs _
    · simp at he
  have hLHS : Notions.STCR_Experiment (B2S pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let out ← Fxmss.Rom.B2extract pr (BMsg pr Msg)
              (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) pk <$>
            Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk
          return Notions.STCR_IsCollision prob pk
            (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) out) := by
    unfold Notions.STCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B2S, Notions.STCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := Fxmss.simulateQ_recordSTcr_run (Fxmss.Rom.probGrind pr L) pk
      (Fxmss.Rom.B2queries pr (BMsg pr Msg) L d) [] []
    have hq' : (simulateQ (Notions.STCR_oracles (Fxmss.Rom.probGrind pr L) pk)
        (Fxmss.Rom.B2queries pr (BMsg pr Msg) L d)).run ([], []) =
        pure ((), (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk, [])) :=
      Fxmss.Rom.B2queries_run pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) pk d hd
    rw [hq', map_pure] at hrec
    simp only [Notions.STCR_oracles, Fxmss.unifFwd, Fxmss.Rom.probGrind] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_stcr pr (Fxmss.Rom.thGrind pr)
      (Fxmss.Rom.targetSumProp pr) L pk uSl (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) []
      (hsf pk d)
    simp only [Notions.STCR_oracles] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure,
      pure_bind, stageHyb_AFTable_eq_AFEager pr Msg enc A uSl]
    exact EvalDistEq.refl _
  have hRHS1 : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.STCR_Experiment
          (Fxmss.Rom.B2 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let out ← Fxmss.Rom.B2extract pr (BMsg pr Msg)
              (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) pk <$>
            Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk
          return Notions.STCR_IsCollision prob pk
            (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) out) := by
    refine EvalDistEq.bind_right _ fun uSl => ?_
    unfold Notions.STCR_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [Fxmss.Rom.B2, Fxmss.mkSTcrAdv, Notions.STCR_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := Fxmss.simulateQ_recordSTcr_run (Fxmss.Rom.probGrind pr L) pk
      (Fxmss.Rom.B2queries pr (BMsg pr Msg) L d) [] []
    rw [Fxmss.Rom.B2queries_run pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl) pk d hd,
      map_pure] at hrec
    simp only [Notions.STCR_oracles, Fxmss.unifFwd, Fxmss.Rom.probGrind] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure,
      pure_bind]
    exact EvalDistEq.refl _
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.STCR_Experiment
          (Fxmss.Rom.B2 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let out ← Fxmss.Rom.B2extract pr (BMsg pr Msg)
              (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) pk <$>
            Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk
          return Notions.STCR_IsCollision prob pk
            (Fxmss.Rom.B2targets pr (BMsg pr Msg) L d pk) out) := by
    refine hRHS1.trans ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- `B3S γ` experiment in world `w` = sampling `uSl` and running `B3 γ (AFEager uSl)`. -/
theorem B3S_exp_eq (w : SM_DT_UD_World) (γ : ℕ) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment w (B3S pr Msg enc γ A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_UD_Experiment w
          (Fxmss.Rom.B3 pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl))) := by
  let g₁ : ProbComp (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) :=
    Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_UD_Experiment w (B3S pr Msg enc γ A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let u' ← Fxmss.Rom.Hyb.fillWith (Fxmss.Rom.Hyb.udAns pr w pk)
            (Fxmss.Rom.Hyb.targets pr pk (Fxmss.Rom.Hyb.selUD γ) d.S d.ys) d.u
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          Fxmss.Rom.Hyb.dist3 pr (BMsg pr Msg) (slKeygenS pr) γ
            (AFEager pr Msg enc A uSl).toFxmssAdversary { d with u := u' } pk) := by
    unfold SM_DT_UD_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B3S, SM_DT_UD_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hcoll : Fxmss.Rom.Hyb.CollAnswers pr (id : SLHDSA.Adrs → SLHDSA.Adrs) pk
        (Fxmss.unifFwd (SM_DT_UD_State SLHDSA.Adrs) +
          (SM_DT_UD_challengeOracle w (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk +
            collectionOracle id (Fxmss.Rom.probUD pr (L * vp.params.lsf)).thColl pk)) := by
      intro q qs tws hq
      rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
      exact collectionOracle_run_of_fresh id q hq
    have hchal : Fxmss.Rom.Hyb.ChalAnswers pr (id : SLHDSA.Adrs → SLHDSA.Adrs)
        (L * vp.params.lsf) (Fxmss.Rom.Hyb.udAns pr w pk) (fun t _ => t)
        (Fxmss.unifFwd (SM_DT_UD_State SLHDSA.Adrs) +
          (SM_DT_UD_challengeOracle w (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk +
            collectionOracle id (Fxmss.Rom.probUD pr (L * vp.params.lsf)).thColl pk)) := by
      intro t qs tws hlen hfr
      rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      cases w
      · exact SM_DT_UD_challengeOracle_run_of_fresh_real hlen hfr
      · exact SM_DT_UD_challengeOracle_run_of_fresh_ideal hlen hfr
    have hrun := Fxmss.Rom.Hyb.run_pickProg hcoll hchal (fun _ _ => rfl)
      (Fxmss.Rom.Hyb.selUD γ) d.ys d.u
      (Fxmss.Rom.Hyb.targets_length_le pr (slKeygenS pr) (AF pr Msg enc A) pk _ hd)
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hstep : ∀ z ∈ support ((simulateQ (SM_DT_UD_oracles w
          (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk)
          (Fxmss.Rom.Hyb.pickProg pr (Fxmss.Rom.Hyb.selUD γ) d.ys d.u)).run ([], [])),
        ((simulateQ (SM_DT_UD_oracles w (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk)
          (do let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
                OracleComp (Fxmss.Rom.Hyb.FSpec pr) _)
              let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
              return (({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State), uSl, vt))).run
          z.2 >>= fun s =>
            (fun o => decide (Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o)) <$>
              Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
                (AFTable pr Msg enc A s.1.2.1 s.1.2.2.1 s.1.2.2.2).toFxmssAdversary
                (Fxmss.Rom.betaOf pr (γ + 1) pk s.1.1.u) s.1.1 pk) =
        ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
          Fxmss.Rom.Hyb.dist3 pr (BMsg pr Msg) (slKeygenS pr) γ
            (AFEager pr Msg enc A uSl).toFxmssAdversary
            ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk) := by
      intro z hz
      have hz' : (z.1, z.2.1) ∈ support (Fxmss.Rom.Hyb.runRef (Fxmss.Rom.Hyb.udAns pr w pk)
          (fun t _ => t) (Fxmss.Rom.Hyb.targets pr pk (Fxmss.Rom.Hyb.selUD γ) d.S d.ys) d.u []) := by
        rw [← hrun, support_map]
        exact ⟨z, hz, rfl⟩
      have hqs_sf : ∀ t ∈ z.2.1, Scheme.IsStateful t :=
        mem_runRef_snd _ _ Scheme.IsStateful _ _ _ _ hz' (by simp)
          (fun pt hpt _ => isStateful_of_mem_targets pr pk _ d.S d.ys hpt)
      simp only [SM_DT_UD_oracles]
      rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
      refine bind_congr fun uSl => ?_
      obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_ud pr w (L * vp.params.lsf) pk uSl
        z.2.1 z.2.2 hqs_sf
      simp only [SM_DT_UD_oracles] at hvt
      rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure,
        pure_bind]
      exact congrArg (Functor.map _) (stageHyb_AFTable_eq_AFEager pr Msg enc A uSl
        (Fxmss.Rom.betaOf pr (γ + 1) pk z.1)
        ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk)
    have hmid :
        ((simulateQ (SM_DT_UD_oracles w (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk)
            (Fxmss.Rom.Hyb.pickProg pr (Fxmss.Rom.Hyb.selUD γ) d.ys d.u)).run ([], []) >>=
          fun z =>
            (simulateQ (SM_DT_UD_oracles w (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk)
              (do let uSl ← (liftM ($ᵗ (SlSecAdrs vp → pr.Y) : ProbComp _) :
                    OracleComp (Fxmss.Rom.Hyb.FSpec pr) _)
                  let vt ← slVirtualTreeM pr (hybCollCall pr) uSl
                  return (({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State),
                    uSl, vt))).run z.2 >>= fun s =>
              (fun o => decide (Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o)) <$>
                Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
                  (AFTable pr Msg enc A s.1.2.1 s.1.2.2.1 s.1.2.2.2).toFxmssAdversary
                  (Fxmss.Rom.betaOf pr (γ + 1) pk s.1.1.u) s.1.1 pk) =ᵈ
        ((simulateQ (SM_DT_UD_oracles w (Fxmss.Rom.probUD pr (L * vp.params.lsf)) pk)
            (Fxmss.Rom.Hyb.pickProg pr (Fxmss.Rom.Hyb.selUD γ) d.ys d.u)).run ([], []) >>=
          fun z =>
            $ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
              Fxmss.Rom.Hyb.dist3 pr (BMsg pr Msg) (slKeygenS pr) γ
                (AFEager pr Msg enc A uSl).toFxmssAdversary
                ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk) :=
      EvalDistEq.bind_congr_of_support _ fun z hz => by rw [hstep z hz]
    refine hmid.trans ?_
    rw [← Fxmss.Rom.Hyb.map_fst_runRef (Fxmss.Rom.Hyb.udAns pr w pk) (fun t _ => t), ← hrun,
      Functor.map_map, bind_map_left]
    rfl
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_UD_Experiment w
          (Fxmss.Rom.B3 pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let u' ← Fxmss.Rom.Hyb.fillWith (Fxmss.Rom.Hyb.udAns pr w pk)
            (Fxmss.Rom.Hyb.targets pr pk (Fxmss.Rom.Hyb.selUD γ) d.S d.ys) d.u
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          Fxmss.Rom.Hyb.dist3 pr (BMsg pr Msg) (slKeygenS pr) γ
            (AFEager pr Msg enc A uSl).toFxmssAdversary { d with u := u' } pk) := by
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun uSl =>
      Fxmss.Rom.Hyb.udExp_evalDistEq pr (slKeygenS pr) w (Fxmss.Rom.Hyb.selUD γ)
        (AFEager pr Msg enc A uSl) _) ?_
    change ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl => do
        let pk ← $ᵗ pr.PkSeed
        let d ← g₁
        let u' ← Fxmss.Rom.Hyb.fillWith (Fxmss.Rom.Hyb.udAns pr w pk)
          (Fxmss.Rom.Hyb.targets pr pk (Fxmss.Rom.Hyb.selUD γ) d.S d.ys) d.u
        Fxmss.Rom.Hyb.dist3 pr (BMsg pr Msg) (slKeygenS pr) γ
          (AFEager pr Msg enc A uSl).toFxmssAdversary { d with u := u' } pk) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun d => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- `B4S` experiment = sampling `uSl` and running `B4 (AFEager uSl)`. -/
theorem B4S_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B4S pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment
          (Fxmss.Rom.B4 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  refine mkTcrAdvS_exp_eq pr Msg enc (Fxmss.Rom.thF pr) (L * vp.params.lsf * vp.params.w)
    A.toShrincsAdversary (Fxmss.Rom.B4queries pr (BMsg pr Msg) L) _
    (fun uSl st pk => Fxmss.Rom.B4extract pr (BMsg pr Msg) st.2 pk <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk st.1.u) st.1 pk)
    (fun d pk => Fxmss.Rom.B4targets pr (BMsg pr Msg) d pk) (fun _ _ => [])
    (fun pk d hd => Fxmss.Rom.B4queries_run pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) pk d hd)
    (fun pk d _ e he => by
      unfold Fxmss.Rom.B4targets at he
      split_ifs at he with hS
      · obtain ⟨a, -, he⟩ := List.mem_flatMap.1 he
        rw [Fxmss.Rom.B4chainTargets, Fxmss.iterTargets_eq] at he
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
        exact SfAdrs.isStateful_toAdrs _
      · simp at he)
    (fun d uSl pk => by
      dsimp only
      rw [stageHyb_AFTable_eq_AFEager pr Msg enc A uSl])

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- `B5S` experiment = sampling `uSl` and running `B5 (AFEager uSl)`. -/
theorem B5S_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_PRE_Experiment (B5S pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_PRE_Experiment
          (Fxmss.Rom.B5 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let g₁ : ProbComp (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) :=
    Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hLHS : SM_DT_PRE_Experiment (B5S pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let z ← Fxmss.Rom.Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (Fxmss.Rom.Hyb.targets pr pk Fxmss.Rom.Hyb.selPre d.S d.ys) d.u []
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let jm ← Fxmss.Rom.Hyb.inv5 pr (BMsg pr Msg) (slKeygenS pr)
            (AFEager pr Msg enc A uSl).toFxmssAdversary { d with u := z.1 } pk
          return Fxmss.Rom.Hyb.preWin pr pk z.2 jm) := by
    unfold SM_DT_PRE_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B5S, SM_DT_PRE_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support g₁ fun d hd => ?_
    have hcoll : Fxmss.Rom.Hyb.CollAnswers pr (Prod.fst : SLHDSA.Adrs × pr.Y → SLHDSA.Adrs) pk
        (Fxmss.unifFwd (SM_DT_PRE_State SLHDSA.Adrs pr.Y) +
          (SM_DT_PRE_challengeOracle (Fxmss.Rom.probPre pr (L * vp.params.lsf)) pk +
            collectionOracle (Q := SLHDSA.Adrs × pr.Y) Prod.fst
              (Fxmss.Rom.probPre pr (L * vp.params.lsf)).thColl pk)) := by
      intro q qs tws hq
      rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
      exact collectionOracle_run_of_fresh Prod.fst q hq
    have hchal : Fxmss.Rom.Hyb.ChalAnswers pr (Prod.fst : SLHDSA.Adrs × pr.Y → SLHDSA.Adrs)
        (L * vp.params.lsf) (fun t x => pr.F pk t x) (fun t x => (t, x))
        (Fxmss.unifFwd (SM_DT_PRE_State SLHDSA.Adrs pr.Y) +
          (SM_DT_PRE_challengeOracle (Fxmss.Rom.probPre pr (L * vp.params.lsf)) pk +
            collectionOracle (Q := SLHDSA.Adrs × pr.Y) Prod.fst
              (Fxmss.Rom.probPre pr (L * vp.params.lsf)).thColl pk)) := by
      intro t qs tws hlen hfr
      rw [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact SM_DT_PRE_challengeOracle_run_of_fresh hlen hfr
    have hrun := Fxmss.Rom.Hyb.run_pickProg hcoll hchal (fun _ _ => rfl)
      Fxmss.Rom.Hyb.selPre d.ys d.u
      (Fxmss.Rom.Hyb.targets_length_le pr (slKeygenS pr) (AF pr Msg enc A) pk _ hd)
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support
        (g := fun z => do
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let jm ← Fxmss.Rom.Hyb.inv5 pr (BMsg pr Msg) (slKeygenS pr)
            (AFEager pr Msg enc A uSl).toFxmssAdversary
            ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk
          return Fxmss.Rom.Hyb.preWin pr pk z.2.1 jm)
        _ fun z hz => ?_) ?_
    · have hz' : (z.1, z.2.1) ∈ support (Fxmss.Rom.Hyb.runRef (fun t x => pr.F pk t x)
          (fun t x => (t, x)) (Fxmss.Rom.Hyb.targets pr pk Fxmss.Rom.Hyb.selPre d.S d.ys) d.u []) := by
        rw [← hrun, support_map]
        exact ⟨z, hz, rfl⟩
      have hqs_sf : ∀ e ∈ z.2.1, Scheme.IsStateful e.1 :=
        mem_runRef_snd _ _ (fun e => Scheme.IsStateful e.1) _ _ _ _ hz' (by simp)
          (fun pt hpt _ => isStateful_of_mem_targets pr pk _ d.S d.ys hpt)
      rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
      refine EvalDistEq.bind_right _ fun uSl => ?_
      obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_pre pr (L * vp.params.lsf) pk uSl
        z.2.1 z.2.2 hqs_sf
      simp only [SM_DT_PRE_oracles, Fxmss.Rom.probPre] at hvt
      simp only [Fxmss.unifFwd]
      rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure,
        pure_bind]
      have hst : Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
            (AFTable pr Msg enc A uSl (slVirtualTreeDet pr pk uSl).1
              (slVirtualTreeDet pr pk uSl).2).toFxmssAdversary
            (fun id ch _ => Fxmss.Rom.skOf pr d.S z.1 id ch)
            ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk =
          Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
            (AFEager pr Msg enc A uSl).toFxmssAdversary
            (fun id ch _ => Fxmss.Rom.skOf pr d.S z.1 id ch)
            ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk :=
        stageHyb_AFTable_eq_AFEager pr Msg enc A uSl
          (fun id ch _ => Fxmss.Rom.skOf pr d.S z.1 id ch)
          ({ d with u := z.1 } : Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) pk
      dsimp only
      rw [hst]
      refine EvalDistEq.bind_right _ fun jm => ?_
      simp only [Fxmss.Rom.Hyb.preWin]
      cases z.2.1[jm.1]? with
      | none => exact EvalDistEq.refl _
      | some tx => obtain ⟨t, x⟩ := tx; exact EvalDistEq.refl _
    · rw [← hrun, bind_map_left]
      exact EvalDistEq.refl _
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_PRE_Experiment
          (Fxmss.Rom.B5 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let z ← Fxmss.Rom.Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
            (Fxmss.Rom.Hyb.targets pr pk Fxmss.Rom.Hyb.selPre d.S d.ys) d.u []
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let jm ← Fxmss.Rom.Hyb.inv5 pr (BMsg pr Msg) (slKeygenS pr)
            (AFEager pr Msg enc A uSl).toFxmssAdversary { d with u := z.1 } pk
          return Fxmss.Rom.Hyb.preWin pr pk z.2 jm) := by
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun uSl =>
      Fxmss.Rom.Hyb.preExp_evalDistEq pr (slKeygenS pr) Fxmss.Rom.Hyb.selPre
        (AFEager pr Msg enc A uSl) _) ?_
    change ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl => do
        let pk ← $ᵗ pr.PkSeed
        let d ← g₁
        let z ← Fxmss.Rom.Hyb.runRef (fun t x => pr.F pk t x) (fun t x => (t, x))
          (Fxmss.Rom.Hyb.targets pr pk Fxmss.Rom.Hyb.selPre d.S d.ys) d.u []
        let jm ← Fxmss.Rom.Hyb.inv5 pr (BMsg pr Msg) (slKeygenS pr)
          (AFEager pr Msg enc A uSl).toFxmssAdversary { d with u := z.1 } pk
        return Fxmss.Rom.Hyb.preWin pr pk z.2 jm) =ᵈ _
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun d => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- `B6S` experiment = sampling `uSl` and running `B6 (AFEager uSl)`. -/
theorem B6S_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B6S pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment
          (Fxmss.Rom.B6 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  refine mkTcrAdvS_exp_eq pr Msg enc (Fxmss.Rom.thLsf pr) L
    A.toShrincsAdversary (Fxmss.Rom.B6queries pr (BMsg pr Msg) L) _
    (fun uSl st pk => Fxmss.Rom.B6extract pr (BMsg pr Msg) st.2 pk <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk st.1.u) st.1 pk)
    (fun d pk => Fxmss.Rom.B6targets pr (BMsg pr Msg) d pk)
    (fun d _ => Fxmss.Rom.B6collTargets pr (BMsg pr Msg) d)
    (fun pk d hd => Fxmss.Rom.B6queries_run pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) pk d hd)
    (fun pk d _ e he => by
      unfold Fxmss.Rom.B6targets at he
      split_ifs at he with hS
      · obtain ⟨id, -, rfl⟩ := List.mem_map.1 he
        exact SfAdrs.isStateful_toAdrs _
      · simp at he)
    (fun d uSl pk => by
      dsimp only
      rw [stageHyb_AFTable_eq_AFEager pr Msg enc A uSl])

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- `B7S` experiment = sampling `uSl` and running `B7 (AFEager uSl)`. -/
theorem B7S_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    SM_DT_TCR_Experiment (B7S pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        SM_DT_TCR_Experiment
          (Fxmss.Rom.B7 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  refine mkTcrAdvS_exp_eq pr Msg enc (Fxmss.Rom.thH pr) (L - 1)
    A.toShrincsAdversary
    (fun d => OracleComp.liftComp (Fxmss.Rom.prog7 pr (BMsg pr Msg) d) _) _
    (fun uSl st pk => Fxmss.Rom.extract7 pr (BMsg pr Msg) st.2 pk <$>
      Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
        (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk st.1.u) st.1 pk)
    (fun d pk => Fxmss.Rom.Q7 pr (BMsg pr Msg) d pk)
    (fun d _ => Fxmss.Rom.C7 pr (BMsg pr Msg) d)
    (fun pk d hd => by
      change (simulateQ (SM_DT_TCR_oracles (Fxmss.Rom.probTcrH pr (L - 1)) pk)
          (OracleComp.liftComp (Fxmss.Rom.prog7 pr (BMsg pr Msg) d) _)).run ([], []) = _
      rw [Fxmss.tcr_run_eq _ _ _ (by
        rw [Fxmss.Rom.prog7_run]
        exact Fxmss.Rom.tcrGood7 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd pk),
        Fxmss.Rom.prog7_run]
      rfl)
    (fun pk d _ e he => by
      obtain ⟨id, -, he1⟩ := Fxmss.Rom.mem_Q7 pr he
      rw [he1]
      exact SfAdrs.isStateful_toAdrs _)
    (fun d uSl pk => by
      dsimp only
      rw [stageHyb_AFTable_eq_AFEager pr Msg enc A uSl])

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- `B8S` experiment = sampling `uSl` and running `B8 (AFEager uSl)`. -/
theorem B8S_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.SMTCRExcl_Experiment (B8S pr Msg enc A) =ᵈ
      ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.SMTCRExcl_Experiment
          (Fxmss.Rom.B8 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) := by
  let prob := Fxmss.Rom.probExcl pr (L + (L - 1))
  let g₁ : ProbComp (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) :=
    Fxmss.Rom.setupHyb pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A.toShrincsAdversary)
  have hsf : ∀ {σ : Type} (pk : pr.PkSeed) (d : Fxmss.Rom.Setup pr (BMsg pr Msg) σ),
      ∀ e ∈ Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk, Scheme.IsStateful e.1 := by
    intro σ pk d e he
    rcases Fxmss.Rom.mem_Q9 pr he with ⟨id, -, h⟩ | ⟨id, -, h⟩
    · rw [h]; exact SfAdrs.isStateful_toAdrs _
    · rw [h]; exact SfAdrs.isStateful_toAdrs _
  have hLHS : Notions.SMTCRExcl_Experiment (B8S pr Msg enc A) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let out ← Fxmss.Rom.extract9 pr (BMsg pr Msg)
              (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) pk <$>
            Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk
          return Notions.SMTCRExcl_IsCollision prob pk
            (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) out) := by
    unfold Notions.SMTCRExcl_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [B8S, Notions.SMTCRExcl_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := Fxmss.simulateQ_recordExcl_run prob pk
      (OracleComp.liftComp (Fxmss.Rom.prog9 pr (BMsg pr Msg) d) _) [] []
    rw [Fxmss.excl_run_eq _ _ _ (by
      rw [Fxmss.Rom.prog9_run]
      exact Fxmss.Rom.exclGood9 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A) hd pk),
      Fxmss.Rom.prog9_run, map_pure] at hrec
    simp only [Notions.SMTCRExcl_oracles, Fxmss.unifFwd, Fxmss.ExclOracleSpec, prob,
      Fxmss.Rom.probExcl] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_right _ fun uSl => ?_
    obtain ⟨tws', hvt⟩ := simulateQ_slVirtualTreeM_excl pr (L + (L - 1)) pk uSl
      (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) (Fxmss.Rom.C9 pr (BMsg pr Msg) d) (hsf pk d)
    simp only [Notions.SMTCRExcl_oracles, Fxmss.Rom.probExcl] at hvt
    rw [simulateQ_bind, StateT.run_bind, hvt, pure_bind, simulateQ_pure, StateT.run_pure,
      pure_bind, stageHyb_AFTable_eq_AFEager pr Msg enc A uSl]
    exact EvalDistEq.refl _
  have hRHS1 : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.SMTCRExcl_Experiment
          (Fxmss.Rom.B8 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let out ← Fxmss.Rom.extract9 pr (BMsg pr Msg)
              (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) pk <$>
            Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk
          return Notions.SMTCRExcl_IsCollision prob pk
            (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) out) := by
    refine EvalDistEq.bind_right _ fun uSl => ?_
    unfold Notions.SMTCRExcl_Experiment
    refine EvalDistEq.bind_right _ fun pk => ?_
    simp only [Fxmss.Rom.B8, Fxmss.mkExclAdv, Notions.SMTCRExcl_oracles]
    rw [Fxmss.simulateQ_add_liftM_bind_run, bind_assoc]
    refine EvalDistEq.bind_congr_of_support _ fun d hd => ?_
    have hrec := Fxmss.simulateQ_recordExcl_run prob pk
      (OracleComp.liftComp (Fxmss.Rom.prog9 pr (BMsg pr Msg) d) _) [] []
    rw [Fxmss.excl_run_eq _ _ _ (by
      rw [Fxmss.Rom.prog9_run]
      exact Fxmss.Rom.exclGood9 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl) hd pk),
      Fxmss.Rom.prog9_run, map_pure] at hrec
    simp only [Notions.SMTCRExcl_oracles, Fxmss.unifFwd, Fxmss.ExclOracleSpec, prob,
      Fxmss.Rom.probExcl] at hrec ⊢
    rw [simulateQ_bind, StateT.run_bind, hrec, pure_bind, simulateQ_pure, StateT.run_pure,
      pure_bind]
    exact EvalDistEq.refl _
  have hRHS : ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        Notions.SMTCRExcl_Experiment
          (Fxmss.Rom.B8 pr (BMsg pr Msg) (slKeygenS pr) (AFEager pr Msg enc A uSl))) =ᵈ
      (do let pk ← $ᵗ pr.PkSeed
          let d ← g₁
          let uSl ← $ᵗ (SlSecAdrs vp → pr.Y)
          let out ← Fxmss.Rom.extract9 pr (BMsg pr Msg)
              (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) pk <$>
            Fxmss.Rom.stageHyb pr (BMsg pr Msg) (slKeygenS pr)
              (AFEager pr Msg enc A uSl).toFxmssAdversary (Fxmss.Rom.betaOf pr 0 pk d.u) d pk
          return Notions.SMTCRExcl_IsCollision prob pk
            (Fxmss.Rom.Q9 pr (BMsg pr Msg) d pk) out) := by
    refine hRHS1.trans ?_
    refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.bind_right _ fun pk => ?_
    exact EvalDistEq.bind_bind_swap _ _ _
  exact hLHS.trans hRHS.symm

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- Generic bridge from a pointwise `AFEager` bound to a Stage-1-precomputing reduction bound. -/
theorem prEvent_hyb_le_of_exp_eq {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (γ : ℕ) (E : Fxmss.Rom.Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → Prop)
    (expS : ProbComp Bool) (expE : (SlSecAdrs vp → pr.Y) → ProbComp Bool)
    (hexp : expS =ᵈ ($ᵗ (SlSecAdrs vp → pr.Y) >>= expE))
    (hpt : ∀ uSl,
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl).toFxmssAdversary}[
        Fxmss.Rom.HybEvent E o] ≤ 𝒟[expE uSl] {true}) :
    Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary}[
        Fxmss.Rom.HybEvent E o] ≤ 𝒟[expS] {true} := by
  have h1 : Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary}[
        Fxmss.Rom.HybEvent E o] =
      prEvent ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl =>
        (fun o => Fxmss.Rom.HybEvent E o) <$>
          gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl).toFxmssAdversary) := by
    have hE := (gameHyb_AFEager_evalDistEq_gameHyb_AF pr Msg enc A γ).symm
    rw [hE.prEvent_eq (fun o => Fxmss.Rom.HybEvent E o), map_bind]
  have h2 : 𝒟[expS] {true} =
      prEvent ($ᵗ (SlSecAdrs vp → pr.Y) >>= fun uSl => (fun b => b = true) <$> expE uSl) := by
    rw [hexp.evalDist_eq, ← prEvent_eq_evalDist_singleton, map_bind]
  rw [h1, h2]
  refine Fxmss.prEvent_bind_mono' _ _ _ fun uSl _ => ?_
  rw [prEvent_eq_evalDist_singleton]
  exact hpt uSl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- Hybrid `E6` telescope using the Stage-1-precomputing `B3S γ` reductions. -/
theorem claim_4_4_S {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AF pr Msg enc A).toFxmssAdversary}[
        Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o] ≤
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) (vp.params.w - 2) (AF pr Msg enc A).toFxmssAdversary}[
        Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o] +
        ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A) := by
  refine Fxmss.Rom.Hyb.telescope
    (fun γ => Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary}[
      Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o])
    (fun γ => SM_DT_UD_Advantage (B3S pr Msg enc γ A)) (fun γ => ?_) (vp.params.w - 2)
  have hreal : SM_DT_UD_Experiment .real (B3S pr Msg enc γ A) =ᵈ
      (fun o => decide (Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o)) <$>
        gameHyb pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A).toFxmssAdversary := by
    refine (B3S_exp_eq pr Msg enc .real γ A).trans ?_
    refine (EvalDistEq.bind_right _ fun uSl =>
      Fxmss.Rom.Hyb.B3_real pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl)).trans ?_
    rw [← map_bind]
    exact EvalDistEq.map (gameHyb_AFEager_evalDistEq_gameHyb_AF pr Msg enc A γ) _
  have hideal : SM_DT_UD_Experiment .ideal (B3S pr Msg enc γ A) =ᵈ
      (fun o => decide (Fxmss.Rom.HybEvent Fxmss.Rom.Honest.E6 o)) <$>
        gameHyb pr (BMsg pr Msg) (slKeygenS pr) (γ + 1) (AF pr Msg enc A).toFxmssAdversary := by
    refine (B3S_exp_eq pr Msg enc .ideal γ A).trans ?_
    refine (EvalDistEq.bind_right _ fun uSl =>
      Fxmss.Rom.Hyb.B3_ideal pr (BMsg pr Msg) (slKeygenS pr) γ (AFEager pr Msg enc A uSl)).trans ?_
    rw [← map_bind]
    exact EvalDistEq.map (gameHyb_AFEager_evalDistEq_gameHyb_AF pr Msg enc A (γ + 1)) _
  rw [Fxmss.Rom.Hyb.prE6_gameHyb pr (slKeygenS pr), Fxmss.Rom.Hyb.prE6_gameHyb pr (slKeygenS pr),
    SM_DT_UD_Advantage, MeasureTheory.Measure.boolDist, hreal.evalDist_eq, hideal.evalDist_eq]
  exact (ENNReal.absDiff_le_iff.1 le_rfl).1

end Claim415

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **`GAME.4` is `F.2` for `A_F`**: dropping `A_F`'s extra output from the augmented block game
gives the block game `F.2 = gameHyb 0` of Section 4.7 played by `A_F`. -/
theorem gameHybS_map {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Option.map (fun p => (p.1.1, p.2)) <$> gameHybS pr Msg enc A =
      gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AFAdv pr Msg enc A) := by
  simp only [gameHybS, gameHyb, map_bind]
  refine bind_congr fun pk => ?_
  change _ = setupHybS pr Msg enc A >>= _
  refine bind_congr fun d => ?_
  unfold stageHybS Fxmss.Rom.stageHyb
  split_ifs
  · simp only [map_bind]
    refine bind_congr fun pkSl => ?_
    rw [stage2Prog_AFAdv]
    simp [simulateQ_map, StateT.run_map]
  · simp

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y] in
/-- **Claim 4.15**: the stateful-branch wins of `GAME.4` without the abort of `GAME.3` have
probability at most the seven collection summands of Theorem 4.2 for the Stage-1-precomputing
augmented reductions `B2S, B3S γ, B4S, B5S, B6S, B7S, B8S` (each precomputing `PK.sl` and the full
virtual SLH-DSA hypertree in Stage 1 via `O_coll` using stateless-vs-stateful tweak disjointness,
with zero stateless `Th_λ` evaluations in Stage 2). -/
theorem claim_4_15 (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] ≤
      Notions.STCR_Succ (B2S pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) := by
  set A' := AF pr Msg enc A
  have hF : Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[
        HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] ≤
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 A'.toFxmssAdversary}[
        Fxmss.Rom.WinNotC1 (o.map Prod.fst)] := by
    calc Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o]
        ≤ Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[
            Fxmss.Rom.WinNotC1 ((o.map (fun p => (p.1.1, p.2))).map Prod.fst)] := by
          refine prEvent_mono _ _ _ fun o h => ?_
          rcases o with _ | p
          · exact h.elim
          · exact ⟨h.1.2.2.2, h.2⟩
      _ = Pr{let o ← Option.map (fun p => (p.1.1, p.2)) <$> gameHybS pr Msg enc A.toShrincsAdversary}[
            Fxmss.Rom.WinNotC1 (o.map Prod.fst)] :=
          (prEvent_map (gameHybS pr Msg enc A.toShrincsAdversary)
            (Option.map fun p => (p.1.1, p.2))
            (fun o => Fxmss.Rom.WinNotC1 (o.map Prod.fst))).symm
      _ = _ := by rw [gameHybS_map]; rfl
  exact telescope (hF.trans (Fxmss.Rom.gameHyb_winNotC1_le (slKeygenS pr) vp.valid hinj hgc 0 _))
    (Claim415.prEvent_hyb_le_of_exp_eq pr Msg enc A 0 Fxmss.Rom.Honest.E3 _ _
      (Claim415.B2S_exp_eq pr Msg enc A) fun uSl =>
        Fxmss.Rom.claim_4_3 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl))
    (Claim415.claim_4_4_S pr Msg enc A)
    (Claim415.prEvent_hyb_le_of_exp_eq pr Msg enc A 0 Fxmss.Rom.Honest.E5 _ _
      (Claim415.B4S_exp_eq pr Msg enc A) fun uSl =>
        Fxmss.Rom.claim_4_5 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl))
    (Claim415.prEvent_hyb_le_of_exp_eq pr Msg enc A (vp.params.w - 2) Fxmss.Rom.Honest.E6 _ _
      (Claim415.B5S_exp_eq pr Msg enc A) fun uSl =>
        Fxmss.Rom.claim_4_6 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl))
    (Claim415.prEvent_hyb_le_of_exp_eq pr Msg enc A 0 Fxmss.Rom.Honest.E7 _ _
      (Claim415.B6S_exp_eq pr Msg enc A) fun uSl =>
        Fxmss.Rom.claim_4_7 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl))
    (Claim415.prEvent_hyb_le_of_exp_eq pr Msg enc A 0 Fxmss.Rom.Honest.E8 _ _
      (Claim415.B7S_exp_eq pr Msg enc A) fun uSl =>
        Fxmss.Rom.claim_4_8 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl))
    (Claim415.prEvent_hyb_le_of_exp_eq pr Msg enc A 0 Fxmss.Rom.Honest.E9 _ _
      (Claim415.B8S_exp_eq pr Msg enc A) fun uSl =>
        Fxmss.Rom.claim_4_9 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc (AFEager pr Msg enc A uSl))

end ShrincsSecurity.Shrincs

end
