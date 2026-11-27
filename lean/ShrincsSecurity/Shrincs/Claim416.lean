module

public import ShrincsSecurity.Slhdsa.PostPrf
public import ShrincsSecurity.Shrincs.AFBounds

/-!
# Claim 4.16: Stateless-branch security of SHRINCS (`GAME.5` → [HK22] post-PRF bound)

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.16** (discharging `StatelessBound` in
`Shrincs/Theorem41.lean`): in `GAME.5` (equivalently `GAME.4`, `gameHybS`, since the aborts of
`GAME.3` and `GAME.5` concern only the stateful branch), the probability `Pr_{gameHybS}[W_sl]`
that a SHRINCS forger `A` outputs a fresh forgery verifying on the stateless branch is bounded by
the **ten post-PRF summands** of `Slhdsa.postPrf_bound` (see `DEVIATIONS.md` §4.6 for the minor
`4 · SM-TCR(F) + 2 · SM-TCR(H)` vs. paper `5 · SM-TCR(F) + 1 · SM-TCR(H)` difference and the
aggregate `q_s` vs. `q_s^{sl}` ITSR budget):

1. `Succ^{ITSR}_{H_msg^sl, q_s}(B_itsr)`
2. `+ ∑_{γ < w - 2} Adv^{SM-UD}_{F ∈ Th_λ, q₂}(B_ud γ)`
3. `+ Adv^{SM-PRE}_{F ∈ Th_λ, q₂}(B_pre)`
4. `+ Adv^{SM-TCR}_{F ∈ Th_λ, q₃}(B_tcrF_wots)`
5. `+ Adv^{SM-TCR}_{H ∈ Th_λ, q₄}(B_tcrH_xmss)`
6. `+ Adv^{SM-TCR}_{Th_k ∈ Th_λ, q₅}(B_tcrThK)`
7. `+ Adv^{SM-TCR}_{Th_lsl ∈ Th_λ, q₆}(B_tcrThLsl)`
8. `+ Adv^{SM-TCR}_{H ∈ Th_λ, q₇}(B_tcrH_fors)`
9. `+ 3 · Adv^{SM-TCR}_{F ∈ Th_λ, q₈}(B_tcrF_fors)`
10. `+ Adv^{SM-DSPR}_{F ∈ Th_λ, q₈}(B_dsprF_fors)`.

## Proof structure

1. **Stage-1 stateful precomputation hook (`sfStageShrincs`)**: instantiates `Slhdsa.SfStage1`
   with `setupHybS` and `Slhdsa.sfPrecompM` (`Slhdsa/Bridge.lean`), precomputing `PK.sf` and all
   stateful FXMSS signatures in Stage 1 via `O_coll` at `Scheme.IsStateful` tweaks (leaving every
   stateless tweak untouched, and leaving Stage 2 with zero stateful `Th_λ` evaluations).
2. **Post-PRF stateless adversary (`shrincsSlAdv`)**: receives `(d, sf, pk, pkSl)`, simulates
   `A.forge` by answering `H_msg^sf` lazily from `d.cache`, answering stateful signing queries from
   the precomputed `sf.sig` and programming `H_msg^sf` with `digOf pr d.ys` (matching `implHyb`),
   and forwarding stateless signing queries on `slMsg pr Msg enc sf.pkSf m` to the SLH-DSA post-PRF
   signing oracle (`≤ q_s` queries).
3. **Game bridge (`pr_gameHybS_Wsl_le_postPrf`)**:
   - drops the post-forgery `H_msg^sf` query and `completion` in `progS` (inert for `W_sl`);
   - switches lazy `SecCache` to eager `u ←$ (SlSecAdrs vp → pr.Y)` on `forgeExt` (keeping `Ext`);
   - couples `implHyb + implAFDet` with `slSignImpl + slSimImpl` in lockstep, transporting freshness
     `m* ∉ log` to `slMsg sf.pkSf m* ∉ slLog` via `Slhdsa.slMsg_injective henc` and verification
     `slVerify` to `SLHDSA.GeneralScheme.verifyInternal` via `Slhdsa.slVerify_eq_verifyInternal`.
4. **Master discharge (`claim_4_16`)**: applies `Slhdsa.postPrf_bound` directly to
   `(sfStageShrincs, shrincsSlAdv)`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme Slhdsa SLHDSA.Security
open SLHDSA (Adrs AddrType Byte wotsSkAdrs wotsChainAdrs wotsPkAdrs wotsLeafAdrs
  xmssNodeAdrs forsSkAdrs forsNodeAdrs forsPkAdrs
  wotsPkGenWithSecret wotsPkGenTopsWithSecret wotsSignWithSecret
  xmssNodeWithSecret xmssLeafWithSecret xmssNodeHashWith xmssSignWithSecret
  forsSignWithSecretM forsSignWithSecret forsLeafWithSecret LayerPosition)
open Fxmss.Rom (roIn verifyWith pkSfOf skOf SkIdx Keys roSpec RoIn St Transcript completion
  otherMsg anchorList implHyb Setup hon digOf betaOf fullSpec Honest)
open ShrincsSecurity.Scheme.Structure (leafIds)

section Helpers

private theorem evalDistEq_apply_true {mx my : ProbComp Bool} (h : mx =ᵈ my) :
    𝒟[mx] {true} = 𝒟[my] {true} := by
  have htop : (⊤ : MeasurableSpace Bool) = (inferInstance : MeasurableSpace Bool) :=
    MeasurableSpace.ext fun s => ⟨fun _ => MeasurableSet.of_discrete, fun _ => trivial⟩
  have h1 := congrArg (fun μ => μ {true}) h.evalDist_eq
  simpa only [htop] using h1

private theorem prEvent_eq_evalDist_bind {α : Type} (mx : ProbComp α) (P : α → Prop) :
    Pr{let x ← mx}[P x] = 𝒟[mx >>= fun x => pure (decide (P x))] {true} := by
  rw [prEvent_def, map_eq_bind_pure_comp]
  let : MeasurableSpace Prop := ⊤
  let : MeasurableSpace Bool := ⊤
  have h1 := lintegral_evalDist_bind_mono_of_support mx (fun x => pure (P x))
    (fun x => pure (decide (P x))) (v := Set.indicator {True} 1) (w := Set.indicator {true} 1)
    (measurable_of_countable _) (measurable_of_countable _)
    (fun x _ => by by_cases hx : P x <;> simp [hx])
  have h2 := lintegral_evalDist_bind_mono_of_support mx (fun x => pure (decide (P x)))
    (fun x => pure (P x)) (v := Set.indicator {true} 1) (w := Set.indicator {True} 1)
    (measurable_of_countable _) (measurable_of_countable _)
    (fun x _ => by by_cases hx : P x <;> simp [hx])
  rw [MeasureTheory.lintegral_indicator_one (by trivial),
      MeasureTheory.lintegral_indicator_one (by trivial)] at h1 h2
  exact le_antisymm h1 h2

end Helpers

section Claim416

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

/-! ## 1. Stage-1 stateful precomputation hook (`sfStageShrincs`) -/

/-- Stage-1 stateful `O_coll` precomputation hook for SHRINCS Claim 4.16: draws `setupHybS`
before `PK.seed` is revealed, and precomputes `PK.sf` and all anchor FXMSS signatures via `O_coll`
exclusively at `Scheme.IsStateful` tweaks. -/
noncomputable def sfStageShrincs {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Slhdsa.SfStage1 pr (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) (Slhdsa.SfPrecomp pr) where
  g₁ := setupHybS pr Msg enc A
  sfDet d pk := Slhdsa.sfPrecompDet pr pk d.S d.ys d.u
  sfRun collCall d := Slhdsa.sfPrecompM pr collCall d.S d.ys d.u
  sfRun_spec impl collCall pk Inv step hcall hinv d _ s hs :=
    Slhdsa.simulateQ_sfPrecompM_run pr impl collCall pk Inv step hcall hinv d.S d.ys d.u s hs

/-! ## 2. Post-PRF stateless adversary (`shrincsSlAdv`) -/

/-- Internal simulator state while running `A.forge` inside `shrincsSlAdv`. -/
structure SlSimSt where
  roCache : (roSpec pr (BMsg pr Msg)).QueryCache
  used : List LeafId
  ctr : ℕ
  log : List Msg

/-- Handler simulating `A`'s oracles (`advSpec`) inside `SlAdvSpec`:
* coins are forwarded to `SlAdvSpec.inl`;
* `H_msg^sf` is answered lazily from `s.roCache` using coins;
* stateful signing queries use the precomputed `sf.sig` and program `s.roCache` with `digOf d.ys`;
* stateless signing queries forward `slMsg sf.pkSf m` to `SlAdvSpec.inr`. -/
noncomputable def slSimImpl {State : Type} (d : Setup pr (BMsg pr Msg) State)
    (sf : Slhdsa.SfPrecomp pr) (pk : pr.PkSeed) (pkSl : pr.Y) :
    QueryImpl (advSpec pr Msg) (StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr))) :=
  ((fun n => liftM ((Slhdsa.SlAdvSpec pr).query (.inl n)) :
      QueryImpl unifSpec (StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr)))) +
    (fun x => StateT.mk fun s =>
      match s.roCache x with
      | some dig => pure (dig, s)
      | none => (fun dig => (dig, { s with roCache := s.roCache.cacheQuery x dig })) <$>
          (liftM ($ᵗ pr.Digest : ProbComp pr.Digest) : OracleComp (Slhdsa.SlAdvSpec pr) pr.Digest) :
      QueryImpl (roSpec pr (BMsg pr Msg))
        (StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr))))) +
  (fun q => (do
      let s ← get
      if q.2 then
        let σ ← (liftM ((Slhdsa.SlAdvSpec pr).query (.inr (slMsg pr Msg enc sf.pkSf q.1))) :
          StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr)) (Stateless.Sig pr))
        set { s with log := s.log ++ [q.1] }
        return some (.stateless σ)
      else
        match d.S.leafSelect s.ctr with
        | none =>
          set { s with log := s.log ++ [q.1] }
          return none
        | some v =>
          let id := v.toLeafId vp.params.hsf
          if id ∈ leafIds vp.params.hsf d.S ∧ id ∉ s.used then
            let R ← (liftM (liftM ($ᵗ pr.Y : ProbComp pr.Y) :
              OracleComp (Slhdsa.SlAdvSpec pr) pr.Y) :
              StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr)) pr.Y)
            let md := digOf pr d.ys id
            let x := roIn pr (BMsg pr Msg) R pk sf.pkSf id (pkSl, q.1)
            set { s with
              roCache := s.roCache.cacheQuery x md
              used := s.used ++ [id]
              ctr := s.ctr + 1
              log := s.log ++ [q.1] }
            return (sf.sig id).map (Scheme.Shrincs.Signature.stateful id.height id.index R)
          else
            set { s with ctr := s.ctr + 1, log := s.log ++ [q.1] }
            return none) :
    QueryImpl (Notions.ShrincsScheme.signSpec Msg (Sig pr))
      (StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr))))

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest] in
private theorem isQueryBoundP_liftProb_slAdv {α : Type} (p : ProbComp α) :
    (liftM p : OracleComp (Slhdsa.SlAdvSpec pr) α).IsQueryBoundP Slhdsa.IsSlSignQuery 0 := by
  refine AFBounds.isQueryBoundP_liftComp (p' := fun _ : ℕ => False) ?_ (isQueryBoundP_false p 0)
  intro n h
  exact h

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] [Nontrivial Msg] in
private theorem slSimImpl_step {State : Type} (d : Setup pr (BMsg pr Msg) State)
    (sf : Slhdsa.SfPrecomp pr) (pk : pr.PkSeed) (pkSl : pr.Y)
    (t : (advSpec pr Msg).Domain) (s : SlSimSt pr Msg) :
    ((slSimImpl pr Msg enc d sf pk pkSl t).run s).IsQueryBoundP Slhdsa.IsSlSignQuery
      (if Notions.IsSignQuery t then 1 else 0) := by
  rcases t with (n | x) | ⟨m, b⟩
  · change ((liftM ((Slhdsa.SlAdvSpec pr).query (.inl n)) :
      StateT (SlSimSt pr Msg) (OracleComp (Slhdsa.SlAdvSpec pr)) _).run s).IsQueryBoundP _ 0
    simp [StateT.run_monadLift, Slhdsa.IsSlSignQuery]
  · change (match s.roCache x with
      | some dig => pure (dig, s)
      | none => (fun dig => (dig, { s with roCache := s.roCache.cacheQuery x dig })) <$>
          (liftM ($ᵗ pr.Digest : ProbComp pr.Digest) :
            OracleComp (Slhdsa.SlAdvSpec pr) pr.Digest)).IsQueryBoundP Slhdsa.IsSlSignQuery 0
    cases s.roCache x with
    | some dig => simp
    | none =>
      rw [isQueryBoundP_map_iff]
      exact isQueryBoundP_liftProb_slAdv pr ($ᵗ pr.Digest)
  · unfold slSimImpl
    simp only [QueryImpl.add_apply_inr, Notions.IsSignQuery, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases d.S.leafSelect s.ctr with
      | none => simp
      | some v =>
        dsimp only
        split_ifs
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, pure_bind, bind_assoc]
          refine (isQueryBoundP_bind (n := 0) (m := 0)
            (isQueryBoundP_liftProb_slAdv pr ($ᵗ pr.Y)) fun _ _ => by simp).mono (by omega)
        · simp
    · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc]
      simp [Slhdsa.IsSlSignQuery]

/-- The `q_s`-query post-PRF stateless adversary extracted from a SHRINCS adversary `A` (Claim 4.16). -/
noncomputable def shrincsSlAdv {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Slhdsa.PostPrfAdv pr (Fxmss.Rom.Setup pr (BMsg pr Msg) A.State) (Slhdsa.SfPrecomp pr) qs where
  run d sf pk pkSl :=
    if ¬ d.S.TreeValid vp.params.hsf then pure none else do
      let o ← (simulateQ (slSimImpl pr Msg enc d sf pk pkSl)
        (A.forge d.st d.S (pk, pkSl, sf.pkSf))).run ⟨d.cache, [], 0, []⟩
      return if d.S.Valid vp.params.hsf ∧ o.1.1 ∉ o.2.log then
        match o.1.2 with
        | .stateless σ => some (slMsg pr Msg enc sf.pkSf o.1.1, σ)
        | .stateful _ _ _ _ => none
      else none
  signBound d sf pk pkSl := by
    split_ifs
    · rw [bind_pure_comp, isQueryBoundP_map_iff]
      exact IsQueryBoundP.simulateQ_run_StateT_of_step (A.signBound d.st d.S _)
        (slSimImpl_step pr Msg enc d sf pk pkSl) _
    · exact isQueryBoundP_pure (p := Slhdsa.IsSlSignQuery) none qs

/-! ## 3. Eager-vs-lazy stateless secret equivalence on `forgeExt` (keeping `Ext`) -/

/-- `forgeExt` lifted to `SecFSpec` (keeping `Ext`). -/
noncomputable def forgeExtSecF {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (K : Keys pr) :
    OracleComp (SecFSpec pr Msg) ((BMsg pr Msg × LeafId × Fxmss.Rom.Sig pr) × Ext) := do
  let pkSl ← slRootSecF pr Msg K.pk
  let K' : Keys pr := ⟨K.S, K.pk, pkSl, K.pkSf⟩
  let o ← (simulateQ (implAFSecF pr Msg enc K') (A.forge st K.S K'.toPK)).run ⟨0, [], ∅⟩
  let fresh := !decide (o.1.1 ∈ o.2.log)
  return (outOf pr Msg K' o.1.1 o.1.2, extOf pr Msg enc K' o.1.1 fresh o.1.2)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem slRootSecF_interpEager' (u : SlSecAdrs vp → pr.Y) (pk : pr.PkSeed) :
    simulateQ (interpEager pr Msg u) (slRootSecF pr Msg pk) = pure (slRootDet pr pk u) := by
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (OracleComp (FSpec pr Msg))
  let _ := pubQ pr Id
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (OracleComp (FSpec pr Msg)) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpEager pr Msg u) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpEager pr Msg u) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core F
    (secQueryF pr Msg) (fun a => pure (slSecOf pr u a))
    (fun a _ => by
      change simulateQ (interpEager pr Msg u) (secQueryF pr Msg a) = pure (slSecOf pr u a)
      unfold secQueryF slSecOf
      split_ifs <;> simp [interpEager])
    pk
  have h2 : SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl) pr.toSLHDSA.core
      (m := OracleComp (FSpec pr Msg)) (fun a => pure (slSecOf pr u a)) pk =
      pure (slRootDet pr pk u) := by
    let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
        Id (OracleComp (FSpec pr Msg)) :=
      { toMonadHom :=
          { toFun := fun {_} x => pure (Id.run x)
            toFun_pure' := fun _ => rfl
            toFun_bind' := fun _ _ => by rw [pure_bind]; rfl }
        map_query' := fun _ => rfl }
    exact (SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl)
      pr.toSLHDSA.core G (fun a => pure (slSecOf pr u a)) (fun a => pure (slSecOf pr u a))
      (fun _ _ => rfl) pk).symm
  exact h1.trans h2

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem slSignSecF_interpEager' (u : SlSecAdrs vp → pr.Y)
    (msg : List Byte) (pk : pr.PkSeed) (pkSl R : pr.Y) :
    simulateQ (interpEager pr Msg u) (slSignSecF pr Msg msg pk pkSl R) =
      pure (slSignDet pr pk pkSl u msg R) := by
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (OracleComp (FSpec pr Msg))
  let _ := pubQ pr Id
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (OracleComp (FSpec pr Msg)) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpEager pr Msg u) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpEager pr Msg u) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core F (secQueryF pr Msg) (fun a => pure (slSecOf pr u a))
    (fun a _ => by
      change simulateQ (interpEager pr Msg u) (secQueryF pr Msg a) = pure (slSecOf pr u a)
      unfold secQueryF slSecOf
      split_ifs <;> simp [interpEager])
    msg pk pkSl R
  have h2 : SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
      (m := OracleComp (FSpec pr Msg)) (fun a => pure (slSecOf pr u a)) msg pk pkSl R =
      pure (slSignDet pr pk pkSl u msg R) := by
    let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
        Id (OracleComp (FSpec pr Msg)) :=
      { toMonadHom :=
          { toFun := fun {_} x => pure (Id.run x)
            toFun_pure' := fun _ => rfl
            toFun_bind' := fun _ _ => by rw [pure_bind]; rfl }
        map_query' := fun _ => rfl }
    exact (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
      pr.toSLHDSA.core G (fun a => pure (slSecOf pr u a)) (fun a => pure (slSecOf pr u a))
      (fun _ _ => rfl) msg pk pkSl R).symm
  exact h1.trans h2

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem sec_congr_of_ledger' {m : Type → Type} [Monad m] [LawfulMonad m]
    (sec₁ sec₂ : Adrs → m pr.Y)
    (hsec : ∀ a b, b ∈ SLHDSA.Security.constructionAddresses vp.sl →
      .inl a ∈ SLHDSA.Security.childAdrs vp.sl b → sec₁ a = sec₂ a) :
    (∀ pk, (letI := pubQ pr m; SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl)
        pr.toSLHDSA.core sec₁ pk) =
      (letI := pubQ pr m; SLHDSA.GeneralScheme.keygenInternalWithSecretM (vp := vp.sl)
        pr.toSLHDSA.core sec₂ pk)) ∧
    (∀ msg pk pkRoot R, (letI := pubQ pr m; SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM
        (vp := vp.sl) pr.toSLHDSA.core sec₁ msg pk pkRoot R) =
      (letI := pubQ pr m; SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM
        (vp := vp.sl) pr.toSLHDSA.core sec₂ msg pk pkRoot R)) := by
  have hchain : ∀ (pos : LayerPosition vp.sl) (c : Fin vp.sl.params.len),
      sec₁ (wotsSkAdrs (SLHDSA.Security.wotsInstanceAdrs pos) c.val) =
      sec₂ (wotsSkAdrs (SLHDSA.Security.wotsInstanceAdrs pos) c.val) := fun pos c => by
    have hw : 1 < vp.params.w := Params.one_lt_w vp.valid
    exact hsec _ _
      (SLHDSA.Security.wotsChainAdrs_setHashAddress_mem_constructionAddresses pos c (t := 0) (by
        change 0 < vp.params.w - 1; omega))
      (by rw [SLHDSA.Security.childAdrs_wotsChainAdrs_setHashAddress_zero]; exact List.mem_singleton_self _)
  have hwotsPk : ∀ pos : LayerPosition vp.sl, ∀ pk,
      (letI := pubQ pr m; wotsPkGenWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₁ (SLHDSA.Security.wotsInstanceAdrs pos)) =
      (letI := pubQ pr m; wotsPkGenWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₂ (SLHDSA.Security.wotsInstanceAdrs pos)) := fun pos pk => by
    unfold wotsPkGenWithSecret wotsPkGenTopsWithSecret
    congr 1; apply congrArg Vector.ofFnM; funext i; rw [hchain pos i]
  have hwotsSign : ∀ msg (pos : LayerPosition vp.sl) pk,
      (letI := pubQ pr m; wotsSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        sec₁ msg (SLHDSA.Security.wotsInstanceAdrs pos)) =
      (letI := pubQ pr m; wotsSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        sec₂ msg (SLHDSA.Security.wotsInstanceAdrs pos)) := fun msg pos pk => by
    unfold wotsSignWithSecret
    apply congrArg Vector.ofFnM; funext i; rw [hchain pos i]
  have hmerkle : ∀ {Y : Type} (l₁ l₂ : ℕ → m Y) (nh : ℕ → ℕ → Y → Y → m Y) (z t : ℕ),
      (∀ i, i / 2 ^ z = t → l₁ i = l₂ i) →
      PerfectMerkleTree.merkleRootM l₁ nh z t = PerfectMerkleTree.merkleRootM l₂ nh z t := by
    intro Y l₁ l₂ nh z
    induction z with
    | zero => intro t h; exact h t (by simp)
    | succ z ih =>
      intro t h
      simp only [PerfectMerkleTree.merkleRootM]
      rw [ih (2 * t) (fun i hi => h i (by rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega)),
        ih (2 * t + 1) (fun i hi => h i (by rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega))]
  have hauth : ∀ {Y : Type} (l₁ l₂ : ℕ → m Y) (nh : ℕ → ℕ → Y → Y → m Y) (idx z : ℕ),
      (∀ i, i / 2 ^ z = idx / 2 ^ z → l₁ i = l₂ i) →
      PerfectMerkleTree.intrinsicAuthPathM l₁ nh idx z =
        PerfectMerkleTree.intrinsicAuthPathM l₂ nh idx z := by
    intro Y l₁ l₂ nh idx z
    induction z with
    | zero => intro _; rfl
    | succ z ih =>
      intro h
      simp only [PerfectMerkleTree.intrinsicAuthPathM]
      rw [ih (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hi])),
        hmerkle l₁ l₂ nh z _ (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hi,
            PerfectMerkleTree.sibling_div_two]))]
  have hxmssNode : ∀ (coord : LayerTreeCoord vp.sl) (pk : pr.PkSeed) (z t : ℕ),
      z ≤ vp.sl.params.hp → t < 2 ^ (vp.sl.params.hp - z) →
      (letI := pubQ pr m; xmssNodeWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₁ coord.toAdrs z t) =
      (letI := pubQ pr m; xmssNodeWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₂ coord.toAdrs z t) :=
    fun coord pk z t hz ht =>
      hmerkle _ _ _ z t fun i hi =>
        hwotsPk ⟨coord.layer, coord.tree, ⟨i, SLHDSA.Security.lt_pow_of_div_pow_lt hz hi ht⟩⟩ pk
  have hxmssSign : ∀ msg (pos : LayerPosition vp.sl) pk,
      (letI := pubQ pr m; xmssSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
        sec₁ msg pos.toAdrs pos.leaf.val) =
      (letI := pubQ pr m; xmssSignWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) (SLHDSA.PublicHash.h pr.toSLHDSA.core pk)
        sec₂ msg pos.toAdrs pos.leaf.val) := fun msg pos pk => by
    unfold xmssSignWithSecret
    have h1 := hauth
      (letI := pubQ pr m; xmssLeafWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₁ pos.toAdrs)
      (letI := pubQ pr m; xmssLeafWithSecret pr.toSLHDSA.core (SLHDSA.PublicHash.f pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk) sec₂ pos.toAdrs)
      (letI := pubQ pr m; xmssNodeHashWith (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) pos.toAdrs)
      pos.leaf.val vp.sl.params.hp (fun i hi =>
        hwotsPk ⟨pos.layer, pos.tree, ⟨i, SLHDSA.Security.lt_pow_of_div_pow_lt le_rfl
          (hi.trans (Nat.div_eq_of_lt pos.leaf.isLt)) (by positivity)⟩⟩ pk)
    rw [h1]
    refine bind_congr fun path => ?_
    change (letI := pubQ pr m; wotsSignWithSecret pr.toSLHDSA.core
      (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) sec₁ msg (SLHDSA.Security.wotsInstanceAdrs pos)) >>= _ = _
    rw [hwotsSign msg pos pk]
    rfl
  have hht : ∀ (layers : ℕ) (rf : Bool) (pos : LayerPosition vp.sl)
      (h : pos.layer.val + layers = vp.sl.params.d) (msg : pr.Y) (pk : pr.PkSeed),
      (letI := pubQ pr m; SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
        (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₁ rf pos layers h msg) =
      (letI := pubQ pr m; SLHDSA.GeneralHypertree.signFromPositionWithSecret pr.toSLHDSA.core
        (SLHDSA.PublicHash.f pr.toSLHDSA.core pk) (SLHDSA.PublicHash.tl pr.toSLHDSA.core pk)
        (SLHDSA.PublicHash.h pr.toSLHDSA.core pk) sec₂ rf pos layers h msg) := by
    intro layers
    induction layers with
    | zero => intro _ _ _ _ _; rfl
    | succ layers ih =>
      cases layers with
      | zero =>
        intro rf pos h msg pk
        simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret, hxmssSign msg pos pk]
      | succ layers =>
        intro rf pos h msg pk
        simp only [SLHDSA.GeneralHypertree.signFromPositionWithSecret, hxmssSign msg pos pk]
        refine bind_congr fun sig => bind_congr fun root => ?_
        rw [ih false _ _ root pk]
  have hforsSk : ∀ (pos : BottomPosition vp.sl) (tree : Fin vp.sl.params.k) {i : ℕ},
      i / 2 ^ vp.sl.params.a = tree.val →
      sec₁ (forsSkAdrs pos.forsAdrs i) = sec₂ (forsSkAdrs pos.forsAdrs i) := fun pos tree {i} hi =>
    hsec _ _ (SLHDSA.Security.forsLeafAdrs_mem_constructionAddresses pos tree hi)
      (by rw [SLHDSA.Security.childAdrs_forsNodeAdrs_zero]; exact List.mem_singleton_self _)
  have hforsSign : ∀ md (pos : BottomPosition vp.sl) pk,
      (letI := pubQ pr m; forsSignWithSecretM pr.toSLHDSA.core sec₁ md pk pos.forsAdrs) =
      (letI := pubQ pr m; forsSignWithSecretM pr.toSLHDSA.core sec₂ md pk pos.forsAdrs) :=
    fun md pos pk => by
      unfold forsSignWithSecretM forsSignWithSecret
      apply congrArg Vector.ofFnM; funext tree
      dsimp only
      have hdiv := forsLeafIndex_div vp.sl.params md tree.val
      change sec₁ (forsSkAdrs pos.forsAdrs (forsLeafIndex vp.sl.params md tree.val)) >>= _ = _
      rw [hforsSk pos tree hdiv]
      refine bind_congr fun _ => ?_
      rw [hauth _ _ _ _ _ fun i hi => by
        unfold forsLeafWithSecret; rw [hforsSk pos tree (hi.trans hdiv)]]
      rfl
  constructor
  · intro pk
    have h := hxmssNode (LayerTreeCoord.top vp.sl) pk vp.sl.params.hp 0 le_rfl (by simp)
    rw [LayerTreeCoord.top_toAdrs_layerAdrs] at h
    exact h
  · intro msg pk pkRoot R
    unfold SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM
    refine bind_congr fun digest => ?_
    dsimp only
    have hpos := BottomPosition.forsAdrs_ofDigestParts vp.sl (SLHDSA.splitDigest vp.sl.params digest)
    rw [← hpos, hforsSign _ _ pk, hpos]
    refine bind_congr fun _ => bind_congr fun forsPk => ?_
    unfold SLHDSA.GeneralHypertree.signWithSecretM SLHDSA.GeneralHypertree.signWithSecret
    rw [hht vp.sl.params.d _ _ _ forsPk pk]

omit [Fintype pr.Y] [DecidableEq pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg]
  [Nontrivial Msg] in
private theorem slRootSecF_interpLazy' (pk : pr.PkSeed) (sc : SecCache pr) :
    (simulateQ (interpLazy pr Msg pk) (slRootSecF pr Msg pk)).run sc =
      (liftM (slRootP pr pk sc) : OracleComp (FSpec pr Msg) _) := by
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
  let _ := pubQ pr (StateT (SecCache pr) ProbComp)
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpLazy pr Msg pk) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpLazy pr Msg pk) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core F
    (secQueryF pr Msg)
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (fun a _ => by
      change simulateQ (interpLazy pr Msg pk) (secQueryF pr Msg a) = _
      unfold secQueryF
      split_ifs <;> simp [interpLazy, SlSecAdrs.toSecAdrs])
    pk
  have h2 := (sec_congr_of_ledger' pr
    (m := StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (guardSec pr (fun x => StateT.mk fun sc => liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a b hb hab => by
      have hm : a ∈ (slSecretList vp.sl).toFinset := List.mem_toFinset.2 (mem_slSecretList hb hab)
      have hsk : a.IsSecretKey := isSecretKey_of_mem_slSecretList (List.mem_toFinset.1 hm)
      simp [hm, guardSec, hsk])).1 pk
  let G : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (StateT (SecCache pr) ProbComp) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} m => StateT.mk fun sc => liftM (m.run sc)
          toFun_pure' := fun x => by ext sc; simp
          toFun_bind' := fun ma mb => by ext sc; simp [StateT.run_bind] }
      map_query' := fun q => by ext sc; simp }
  have h3 := SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) pr.toSLHDSA.core G
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
    (guardSec pr (fun x => StateT.mk fun sc => liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a h => by ext sc; simp [G, guardSec, h]) pk
  exact congrArg (fun f => f.run sc) ((h1.trans h2).trans h3.symm)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
private theorem slStepSecF_interpLazy' (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg)
    (sc : SecCache pr) (rc : RndCache pr) :
    (simulateQ (interpLazy pr Msg pk) (slStepSecF pr Msg enc pk pkSl pkSf msg rc)).run sc =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        (liftM (slStepP pr Msg enc pk pkSl pkSf msg sc rc) : OracleComp (FSpec pr Msg) _) := by
  have hlift : ∀ {α : Type} (p : ProbComp α) (s : SecCache pr),
      (simulateQ (interpLazy pr Msg pk) (liftM p : OracleComp (SecFSpec pr Msg) α)).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p
    induction p using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      have hq : (simulateQ (interpLazy pr Msg pk)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (SecFSpec pr Msg) _)).run s =
          (fun u => (u, s)) <$>
            (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := rfl
      rw [liftM_bind, liftM_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left, map_bind]
      exact bind_congr fun u => ih u s
  have hliftM2 : ∀ {α : Type} (p : ProbComp α) (s : SecCache pr) (r : RndCache pr),
      ((liftM p : M2 pr α).run s).run r = (fun a => ((a, s), r)) <$> p := fun p s r => by
    simp [MonadLiftT.monadLift, MonadLift.monadLift, map_eq_bind_pure_comp]
  have hliftRc : ∀ {α : Type} (m : StateT (RndCache pr) ProbComp α) (s : SecCache pr)
      (r : RndCache pr),
      ((liftM m : M2 pr α).run s).run r = (fun z => ((z.1, s), z.2)) <$> m.run r := fun m s r => by
    simp [MonadLiftT.monadLift, map_eq_bind_pure_comp]
  unfold slStepSecF slStepP slSignM
  simp only [simulateQ_bind, StateT.run_bind, hlift, hliftM2, hliftRc, bind_map_left,
    liftM_bind, map_bind]
  refine bind_congr fun optRand => bind_congr fun r => ?_
  let _ := pubQ pr (OracleComp (SecFSpec pr Msg))
  let _ := pubQ pr (StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
  let _ := pubQ pr (StateT (SecCache pr) ProbComp)
  let _ := pubQ pr (M2 pr)
  let F : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (OracleComp (SecFSpec pr Msg)) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} oa => simulateQ (interpLazy pr Msg pk) oa
          toFun_pure' := fun x => by simp
          toFun_bind' := fun oa ob => by simp }
      map_query' := fun q => by
        change simulateQ (interpLazy pr Msg pk) (pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)) =
          pure (SLHDSA.PublicHash.impl pr.toSLHDSA q)
        simp }
  have h1 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core F (secQueryF pr Msg)
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (fun a _ => by
      change simulateQ (interpLazy pr Msg pk) (secQueryF pr Msg a) = _
      unfold secQueryF
      split_ifs <;> simp [interpLazy, SlSecAdrs.toSecAdrs])
    (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  have h2 := (sec_congr_of_ledger' pr
    (m := StateT (SecCache pr) (OracleComp (FSpec pr Msg)))
    (fun a => if h : a ∈ (slSecretList vp.sl).toFinset then
        StateT.mk fun sc => liftM ((lazyRO (pk, ⟨a, isSecretKey_of_mem_slSecretList
          (List.mem_toFinset.1 h)⟩) : StateT (SecCache pr) ProbComp pr.Y).run sc)
      else pure default)
    (guardSec pr (fun x => StateT.mk fun sc => liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a b hb hab => by
      have hm : a ∈ (slSecretList vp.sl).toFinset := List.mem_toFinset.2 (mem_slSecretList hb hab)
      have hsk : a.IsSecretKey := isSecretKey_of_mem_slSecretList (List.mem_toFinset.1 hm)
      simp [hm, guardSec, hsk])).2 (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  let G_lift : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (StateT (SecCache pr) ProbComp) (M2 pr) :=
    { toMonadHom :=
        { toFun := fun {_} m => StateT.mk fun sc => StateT.mk fun rc =>
            (fun z => (z, rc)) <$> m.run sc
          toFun_pure' := fun x => by ext sc rc; simp
          toFun_bind' := fun ma mb => by ext sc rc; simp [StateT.run_bind, map_bind, bind_map_left] }
      map_query' := fun q => by ext sc rc; simp }
  let G_spec : HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
      (StateT (SecCache pr) ProbComp) (StateT (SecCache pr) (OracleComp (FSpec pr Msg))) :=
    { toMonadHom :=
        { toFun := fun {_} m => StateT.mk fun sc => liftM (m.run sc)
          toFun_pure' := fun x => by ext sc; simp
          toFun_bind' := fun ma mb => by ext sc; simp [StateT.run_bind] }
      map_query' := fun q => by ext sc; simp }
  have h3 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core G_spec
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
    (guardSec pr (fun x => StateT.mk fun sc =>
      liftM ((lazyRO x : StateT (SecCache pr) ProbComp pr.Y).run sc)) pk)
    (fun a h => by ext sc; simp [G_spec, guardSec, h]) (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  have h4 := SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl)
    pr.toSLHDSA.core G_lift
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
    (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → M2 pr pr.Y) pk)
    (fun a h => by
      ext sc rc
      simp only [G_lift, guardSec, h, ↓reduceDIte, lazyRO, StateT.run_mk]
      cases sc (pk, ⟨a, h⟩) with
      | none => simp [map_eq_bind_pure_comp, bind_assoc]
      | some v => simp)
    (slMsg pr Msg enc pkSf msg) pk pkSl r.1
  have hcomb : (simulateQ (interpLazy pr Msg pk)
      (slSignSecF pr Msg (slMsg pr Msg enc pkSf msg) pk pkSl r.1)).run sc =
      (liftM ((letI := pubQ pr (StateT (SecCache pr) ProbComp);
        SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
          (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
          (slMsg pr Msg enc pkSf msg) pk pkSl r.1).run sc) : OracleComp (FSpec pr Msg) _) :=
    congrArg (fun f => f.run sc) ((h1.trans h2).trans h3.symm)
  have hrun4 : ((letI := pubQ pr (M2 pr);
      SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
        (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → M2 pr pr.Y) pk)
        (slMsg pr Msg enc pkSf msg) pk pkSl r.1).run sc).run r.2 =
      (fun z => (z, r.2)) <$> ((letI := pubQ pr (StateT (SecCache pr) ProbComp);
        SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
          (guardSec pr (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y) pk)
          (slMsg pr Msg enc pkSf msg) pk pkSl r.1).run sc) :=
    (congrArg (fun f => (f.run sc).run r.2) h4).symm
  rw [hcomb, hrun4]
  simp [bind_pure_comp, map_eq_bind_pure_comp]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem interpEager_forgeExtSecF {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (u : SlSecAdrs vp → pr.Y) (st : A.State) (K : Keys pr) :
    simulateQ (interpEager pr Msg u) (forgeExtSecF pr Msg enc A st K) =
      forgeExtDet pr Msg enc (fun p => slRootDet pr p u)
        (fun p pkSl m R => slSignDet pr p pkSl u m R) A st K.S K.toPK := by
  have hliftE : ∀ {α : Type} (p : ProbComp α),
      simulateQ (interpEager pr Msg u) (liftM p : OracleComp (SecFSpec pr Msg) α) =
        (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      have hq : simulateQ (interpEager pr Msg u)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (SecFSpec pr Msg) _) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := rfl
      rw [liftM_bind, liftM_bind, simulateQ_bind, hq]
      exact bind_congr fun x => ih x
  have hliftDet : ∀ {α : Type} (p : ProbComp α) (s : AFStEager pr Msg),
      (liftM p : StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)) α).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p s
    change liftComp (liftComp (p >>= fun a => pure (a, s))
        (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
          Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
        (FSpec pr Msg) = _
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [bind_assoc, OracleComp.liftComp_bind, OracleComp.liftComp_bind, liftM_bind, map_bind]
      have hq : liftComp (liftComp (liftM (unifSpec.query t) : ProbComp _)
          (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
            Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
          (FSpec pr Msg) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := by
        simp; rfl
      rw [hq]
      exact bind_congr fun u => ih u
  have hstep : ∀ (K' : Keys pr) (t) (s : AFStEager pr Msg),
      simulateQ (interpEager pr Msg u) ((implAFSecF pr Msg enc K' t).run s) =
        (implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K' t).run s := by
    intro K' t s
    rcases t with (n | x) | ⟨m, b⟩
    · simp [implAFSecF, implAFDet, interpEager, StateT.run_monadLift]
    · simp [implAFSecF, implAFDet, interpEager, StateT.run_monadLift]
    · unfold implAFSecF implAFDet
      simp only [QueryImpl.add_apply_inr, signAFSecF, signAFDet, StateT.run_bind, StateT.run_get,
        pure_bind]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases K'.S.leafSelect s.ctr with
        | none => simp
        | some v => simp [interpEager, StateT.run_monadLift]
      · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self, hliftDet,
          StateT.run_set, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_map_left]
        unfold slStepSecF slStepDet
        simp only [simulateQ_bind, hliftE, liftM_bind, bind_assoc, simulateQ_pure, pure_bind]
        refine bind_congr fun optRand => bind_congr fun r => ?_
        rw [slSignSecF_interpEager']
        simp
  have hsim : ∀ {α : Type} (K' : Keys pr) (oa : OracleComp (advSpec pr Msg) α)
      (s : AFStEager pr Msg),
      simulateQ (interpEager pr Msg u) ((simulateQ (implAFSecF pr Msg enc K') oa).run s) =
        (simulateQ (implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K') oa).run
          s := by
    intro α K' oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep]
      exact bind_congr fun z => ih z.1 z.2
  unfold forgeExtSecF forgeExtDet
  simp only [simulateQ_bind, slRootSecF_interpEager', pure_bind, hsim, simulateQ_pure]
  rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem interpLazy_forgeExtSecF {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) (st : A.State) (K : Keys pr) :
    Prod.fst <$> (simulateQ (interpLazy pr Msg K.pk)
        (forgeExtSecF pr Msg enc A st K)).run ∅ =
      forgeExt pr Msg enc A st K.S K.toPK := by
  have hliftAF : ∀ {α : Type} (p : ProbComp α) (s : AFSt pr Msg),
      (liftM p : StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)) α).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) α) := by
    intro α p s
    change liftComp (liftComp (p >>= fun a => pure (a, s))
        (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
          Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
        (FSpec pr Msg) = _
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [bind_assoc, OracleComp.liftComp_bind, OracleComp.liftComp_bind, liftM_bind, map_bind]
      have hq : liftComp (liftComp (liftM (unifSpec.query t) : ProbComp _)
          (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
            Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
          (FSpec pr Msg) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := by
        simp; rfl
      rw [hq]
      exact bind_congr fun u => ih u
  have hstep : ∀ (K' : Keys pr) (hpk : K'.pk = K.pk) (t) (s : AFStEager pr Msg) (sc : SecCache pr),
      (simulateQ (interpLazy pr Msg K.pk) ((implAFSecF pr Msg enc K' t).run s)).run sc =
        (fun z => ((z.1, ⟨z.2.ctr, z.2.log, z.2.rnd⟩), z.2.sec)) <$>
          (implAF pr Msg enc K' t).run ⟨s.ctr, s.log, sc, s.rnd⟩ := by
    intro K' hpk t s sc
    rcases t with (n | x) | ⟨m, b⟩
    · simp [implAFSecF, implAF, interpLazy, StateT.run_monadLift, map_eq_bind_pure_comp]
    · simp [implAFSecF, implAF, interpLazy, StateT.run_monadLift, map_eq_bind_pure_comp]
    · unfold implAFSecF implAF
      simp only [QueryImpl.add_apply_inr, signAFSecF, signAF, StateT.run_bind, StateT.run_get,
        pure_bind]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases K'.S.leafSelect s.ctr with
        | none => simp
        | some v =>
          simp [interpLazy, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc]
      · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self, hliftAF,
          StateT.run_set, StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_map_left,
          map_bind]
        rw [← hpk, slStepSecF_interpLazy']
        simp
  have hsim : ∀ {α : Type} (K' : Keys pr) (hpk : K'.pk = K.pk)
      (oa : OracleComp (advSpec pr Msg) α) (s : AFStEager pr Msg) (sc : SecCache pr),
      (simulateQ (interpLazy pr Msg K.pk) ((simulateQ (implAFSecF pr Msg enc K') oa).run s)).run
          sc =
        (fun z => ((z.1, ⟨z.2.ctr, z.2.log, z.2.rnd⟩), z.2.sec)) <$>
          (simulateQ (implAF pr Msg enc K') oa).run ⟨s.ctr, s.log, sc, s.rnd⟩ := by
    intro α K' hpk oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s sc; simp
    | query_bind t k ih =>
      intro s sc
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep K' hpk,
        bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 ⟨z.2.ctr, z.2.log, z.2.rnd⟩ z.2.sec
  unfold forgeExtSecF forgeExt
  simp only [simulateQ_bind, StateT.run_bind, slRootSecF_interpLazy', map_bind]
  refine bind_congr fun r => ?_
  rw [hsim ⟨K.S, K.pk, r.1, K.pkSf⟩ rfl]
  simp only [bind_map_left]
  rfl

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem simulateQ_implSecEager' {α : Type} (K : Keys pr) (H : Honest pr)
    (u : SlSecAdrs vp → pr.Y) (oa : OracleComp (SecFSpec pr Msg) α) (s : St pr (BMsg pr Msg)) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (implSecEager pr Msg K H) oa).run (s, u) =
      (simulateQ (implHyb pr (BMsg pr Msg) K H) (simulateQ (interpEager pr Msg u) oa)).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with f | a
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecEager, interpEager,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 z.2
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecEager, interpEager,
        StateT.run_bind, StateT.run_mk, pure_bind]
      exact ih (u a) s

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem simulateQ_implSecLazy' {α : Type} (K : Keys pr) (H : Honest pr)
    (oa : OracleComp (SecFSpec pr Msg) α) (s : St pr (BMsg pr Msg)) (sc : SecCache pr) :
    (fun z => ((z.1, z.2.2), z.2.1)) <$> (simulateQ (implSecLazy pr Msg K H) oa).run (s, sc) =
      (simulateQ (implHyb pr (BMsg pr Msg) K H)
        ((simulateQ (interpLazy pr Msg K.pk) oa).run sc)).run s := by
  have hlift : ∀ {β : Type} (p : ProbComp β) (s : St pr (BMsg pr Msg)),
      (simulateQ (implHyb pr (BMsg pr Msg) K H) (liftM p : OracleComp (FSpec pr Msg) β)).run s =
        (fun x => (x, s)) <$> p := by
    intro β p
    induction p using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      have hq : (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _)).run s =
          (fun x => (x, s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
        change (implHyb pr (BMsg pr Msg) K H (.inl (.inl t))).run s = _
        simp [Fxmss.Rom.implHyb, Fxmss.Rom.impl, map_eq_bind_pure_comp]
      rw [liftM_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left, map_bind]
      exact bind_congr fun x => ih x s
  induction oa using OracleComp.inductionOn generalizing s sc with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with f | a
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecLazy, interpLazy,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      exact bind_congr fun z => ih z.1 z.2 sc
    · simp only [simulateQ_bind, simulateQ_spec_query, implSecLazy, interpLazy,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind, hlift]
      exact bind_congr fun z => ih z.1 s z.2

omit [Fintype pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
private theorem implSecEager_evalDistEq_implSecLazy' {α : Type} (K : Keys pr) (H : Honest pr)
    (oa : OracleComp (SecFSpec pr Msg) α) (s : St pr (BMsg pr Msg)) :
    (do let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        (fun z : α × (St pr (BMsg pr Msg) × (SlSecAdrs vp → pr.Y)) => (z.1, z.2.1)) <$>
          (simulateQ (implSecEager pr Msg K H) oa).run (s, u)) =ᵈ
      (fun z : α × (St pr (BMsg pr Msg) × SecCache pr) => (z.1, z.2.1)) <$>
        (simulateQ (implSecLazy pr Msg K H) oa).run (s, ∅) := by
  let κ : St pr (BMsg pr Msg) × SecCache pr → ProbComp (St pr (BMsg pr Msg) × (SlSecAdrs vp → pr.Y)) :=
    fun st => (fun u => (st.1, fun a => (st.2 (K.pk, a.toSecAdrs)).getD (u a))) <$>
      ($ᵗ (SlSecAdrs vp → pr.Y))
  have hstep : ∀ (t : (SecFSpec pr Msg).Domain) (stL : St pr (BMsg pr Msg) × SecCache pr),
      (κ stL >>= fun stE => (implSecEager pr Msg K H t).run stE) =ᵈ
        ((implSecLazy pr Msg K H t).run stL >>= fun z => (z.1, ·) <$> κ z.2) := by
    intro t ⟨sL, sc⟩
    rcases t with f | a
    · simp only [κ, implSecEager, implSecLazy, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      exact EvalDistEq.bind_bind_swap _ _ _
    · simp only [κ, implSecEager, implSecLazy, StateT.run_mk, lazyRO, map_eq_bind_pure_comp,
        bind_assoc, Function.comp_apply, pure_bind]
      cases hsc : sc (K.pk, a.toSecAdrs) with
      | some v =>
        simp only [Option.getD_some, pure_bind]
        exact EvalDistEq.refl _
      | none =>
        simp only [Option.getD_none, bind_assoc, Function.comp_apply, pure_bind]
        change (($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
            pure (u a, (sL, fun b => (sc (K.pk, b.toSecAdrs)).getD (u b)))) =ᵈ
          (($ᵗ pr.Y) >>= fun v => ($ᵗ (SlSecAdrs vp → pr.Y)) >>= fun u =>
            pure (v, (sL, fun b =>
              ((sc.cacheQuery (K.pk, a.toSecAdrs) v) (K.pk, b.toSecAdrs)).getD (u b))))
        refine EvalDistEq.trans (EvalDistEq.symm (Repro.resample a _)) ?_
        refine EvalDistEq.bind_right _ fun v => EvalDistEq.bind_right _ fun u => ?_
        have hupd : (fun b : SlSecAdrs vp =>
              (sc (K.pk, b.toSecAdrs)).getD (Function.update u a v b)) =
            (fun b : SlSecAdrs vp =>
              ((sc.cacheQuery (K.pk, a.toSecAdrs) v) (K.pk, b.toSecAdrs)).getD (u b)) := by
          funext b
          by_cases hba : b = a
          · subst hba; simp [hsc]
          · have hne : (K.pk, b.toSecAdrs) ≠ (K.pk, a.toSecAdrs) := by
              intro h; apply hba
              exact Subtype.ext (congrArg (fun p : pr.PkSeed × SecAdrs => p.2.1) h)
            simp [Function.update_of_ne hba, hne]
        simp only [Function.update_self, hupd]
        exact EvalDistEq.refl _
  have hgen : ∀ (oa : OracleComp (SecFSpec pr Msg) α) (stL : St pr (BMsg pr Msg) × SecCache pr),
      (κ stL >>= fun stE => (fun z => (z.1, z.2.1)) <$>
        (simulateQ (implSecEager pr Msg K H) oa).run stE) =ᵈ
      (fun z => (z.1, z.2.1)) <$> (simulateQ (implSecLazy pr Msg K H) oa).run stL := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro stL
      simp only [simulateQ_pure, StateT.run_pure, κ, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      exact EvalDistEq.bind_const ($ᵗ (SlSecAdrs vp → pr.Y)) (pure (a, stL.1))
    | query_bind t k ih =>
      intro stL
      have h1 : (κ stL >>= fun stE => (fun z => (z.1, z.2.1)) <$>
            (simulateQ (implSecEager pr Msg K H) (liftM ((SecFSpec pr Msg).query t) >>= k)).run stE) =
          (κ stL >>= fun stE => (implSecEager pr Msg K H t).run stE) >>= fun z =>
            (fun w => (w.1, w.2.1)) <$> (simulateQ (implSecEager pr Msg K H) (k z.1)).run z.2 := by
        simp [bind_assoc, map_bind]
      have h2 : (fun z => (z.1, z.2.1)) <$>
            (simulateQ (implSecLazy pr Msg K H) (liftM ((SecFSpec pr Msg).query t) >>= k)).run stL =
          (implSecLazy pr Msg K H t).run stL >>= fun z =>
            (fun w => (w.1, w.2.1)) <$> (simulateQ (implSecLazy pr Msg K H) (k z.1)).run z.2 := by
        simp [map_bind]
      rw [h1, h2]
      refine EvalDistEq.trans (EvalDistEq.bind_left (hstep t stL) _) ?_
      simp only [bind_assoc, bind_map_left]
      exact EvalDistEq.bind_right _ fun z => ih z.1 z.2
  simpa [κ] using hgen oa (s, ∅)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
/-- Eager-vs-lazy equivalence on `forgeExt` (keeping `Ext`). -/
theorem forgeExtDet_evalDistEq_forgeExt {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (K : Keys pr) (H : Honest pr) (s : St pr (BMsg pr Msg)) :
    (do let u ← $ᵗ (SlSecAdrs vp → pr.Y)
        (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (forgeExtDet pr Msg enc (fun p => slRootDet pr p u)
            (fun p pkSl m R => slSignDet pr p pkSl u m R) A st K.S K.toPK)).run s) =ᵈ
      (simulateQ (implHyb pr (BMsg pr Msg) K H)
        (forgeExt pr Msg enc A st K.S K.toPK)).run s := by
  have hE : ∀ u, (simulateQ (implHyb pr (BMsg pr Msg) K H)
        (forgeExtDet pr Msg enc (fun p => slRootDet pr p u)
          (fun p pkSl m R => slSignDet pr p pkSl u m R) A st K.S K.toPK)).run s =
      (fun z => (z.1, z.2.1)) <$>
        (simulateQ (implSecEager pr Msg K H) (forgeExtSecF pr Msg enc A st K)).run (s, u) := fun u => by
    rw [simulateQ_implSecEager', interpEager_forgeExtSecF]
  have hL : (simulateQ (implHyb pr (BMsg pr Msg) K H)
        (forgeExt pr Msg enc A st K.S K.toPK)).run s =
      (fun z => (z.1, z.2.1)) <$>
        (simulateQ (implSecLazy pr Msg K H) (forgeExtSecF pr Msg enc A st K)).run (s, ∅) := by
    rw [← interpLazy_forgeExtSecF, simulateQ_map, StateT.run_map, ← simulateQ_implSecLazy',
      Functor.map_map]
  simp_rw [hE]
  rw [hL]
  exact implSecEager_evalDistEq_implSecLazy' pr Msg K H _ s

/-! ## 4. Lockstep coupling `forgeExtDet` → `shrincsSlAdv` and `claim_4_16` -/

/-- State coupling invariant between `(AFStEager, Fxmss.Rom.St)` (in `gameHybS` with eager `u`)
and `(SlSimSt, SlSignSt)` (in `postPrfExp` with `shrincsSlAdv`). -/
structure SimRel (pkSf : pr.Y)
    (afSt : AFStEager pr Msg) (fSt : St pr (BMsg pr Msg))
    (simSt : SlSimSt pr Msg) (slSt : Slhdsa.SlSignSt pr) : Prop where
  roCache_eq : simSt.roCache = fSt.cache
  used_eq : simSt.used = fSt.used
  ctr_eq : simSt.ctr = afSt.ctr
  log_eq : simSt.log = afSt.log
  rnd_eq : ∀ optRand m', afSt.rnd (.sl optRand m') = slSt.rnd (optRand, m')
  slLog_sub : ∀ m' ∈ slSt.log, ∃ m ∈ afSt.log, m' = slMsg pr Msg enc pkSf m

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg]
  [Nontrivial Msg] in
private theorem lockstep_mono {State : Type} (d : Setup pr (BMsg pr Msg) State)
    (hS : d.S.TreeValid vp.params.hsf) (pk : pr.PkSeed) (u : SlSecAdrs vp → pr.Y) :
    let H := hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)
    let K : Keys pr := ⟨d.S, pk, default, H.pkSf⟩
    let sf := Slhdsa.sfPrecompDet pr pk d.S d.ys d.u
    let pkSl := slRootDet pr pk u
    let K' : Keys pr := ⟨d.S, pk, pkSl, H.pkSf⟩
    ∀ {α : Type} (oa : OracleComp (advSpec pr Msg) α)
      (afSt : AFStEager pr Msg) (fSt : St pr (BMsg pr Msg))
      (simSt : SlSimSt pr Msg) (slSt : Slhdsa.SlSignSt pr)
      (k₁ : α → AFStEager pr Msg → St pr (BMsg pr Msg) → ProbComp Bool)
      (k₂ : α → SlSimSt pr Msg → Slhdsa.SlSignSt pr → ProbComp Bool),
      SimRel pr Msg enc sf.pkSf afSt fSt simSt slSt →
      (∀ a af' f' sim' sl', SimRel pr Msg enc sf.pkSf af' f' sim' sl' →
        𝒟[k₁ a af' f'] {true} ≤ 𝒟[k₂ a sim' sl'] {true}) →
      𝒟[(simulateQ (implHyb pr (BMsg pr Msg) K H)
          ((simulateQ (implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K') oa).run afSt)).run fSt >>=
          fun z => k₁ z.1.1 z.1.2 z.2] {true} ≤
      𝒟[(simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((simulateQ (slSimImpl pr Msg enc d sf pk pkSl) oa).run simSt)).run slSt >>=
          fun z => k₂ z.1.1 z.1.2 z.2] {true} := by
  intro H K sf pkSl K'
  have hsfHon := Slhdsa.sfPrecompDet_eq_hon pr hS pk d.ys d.u
  have hpkSf : sf.pkSf = H.pkSf := hsfHon.1
  have hsigEq : ∀ id ∈ leafIds vp.params.hsf d.S, sf.sig id = H.sig id := hsfHon.2
  -- Lifting `ProbComp` through `implHyb` and `slSignImpl`
  have hliftHyb : ∀ {β : Type} (p : ProbComp β) (fSt : St pr (BMsg pr Msg)),
      (simulateQ (implHyb pr (BMsg pr Msg) K H) (liftM p : OracleComp (FSpec pr Msg) β)).run fSt =
        (fun x => (x, fSt)) <$> p := by
    intro β p
    induction p using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      have hq : (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _)).run s =
          (fun x => (x, s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
        change (implHyb pr (BMsg pr Msg) K H (.inl (.inl t))).run s = _
        simp [Fxmss.Rom.implHyb, Fxmss.Rom.impl, map_eq_bind_pure_comp]
      rw [liftM_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left, map_bind]
      exact bind_congr fun x => ih x s
  have hliftSl : ∀ {β : Type} (p : ProbComp β) (slSt : Slhdsa.SlSignSt pr),
      (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
        (liftM p : OracleComp (Slhdsa.SlAdvSpec pr) β)).run slSt =
        (fun x => (x, slSt)) <$> p := by
    intro β p
    induction p using OracleComp.inductionOn with
    | pure a => intro s; simp
    | query_bind t k ih =>
      intro s
      have hq : (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (Slhdsa.SlAdvSpec pr) _)).run s =
          (fun x => (x, s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
        change (StateT.lift (liftM (unifSpec.query t) : ProbComp (unifSpec.Range t))).run s = _
        rw [StateT.run_lift]
        rfl
      rw [liftM_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left, map_bind]
      exact bind_congr fun x => ih x s
  have hliftStateF : ∀ {β : Type} (p : ProbComp β) (s : AFStEager pr Msg),
      (liftM p : StateT (AFStEager pr Msg) (OracleComp (FSpec pr Msg)) β).run s =
        (fun a => (a, s)) <$> (liftM p : OracleComp (FSpec pr Msg) β) := by
    intro β p s
    change liftComp (liftComp (p >>= fun a => pure (a, s))
        (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
          Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
        (FSpec pr Msg) = _
    induction p using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [bind_assoc, OracleComp.liftComp_bind, OracleComp.liftComp_bind, liftM_bind, map_bind]
      have hq : liftComp (liftComp (liftM (unifSpec.query t) : ProbComp _)
          (unifSpec + (Fxmss.Rom.roSpec pr (BMsg pr Msg) +
            Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))))
          (FSpec pr Msg) =
          (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (FSpec pr Msg) _) := by
        simp; rfl
      rw [hq]
      exact bind_congr fun x => ih x
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro afSt fSt simSt slSt k₁ k₂ hrel hk
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a afSt fSt simSt slSt hrel
  | query_bind t k ih =>
    intro afSt fSt simSt slSt k₁ k₂ hrel hk
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases t with (n | x) | ⟨m, b⟩
    · -- Private coins (`unifSpec`)
      have hL : (simulateQ (implHyb pr (BMsg pr Msg) K H)
          ((implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K' (.inl (.inl n))).run afSt)).run fSt =
          (fun r => ((r, afSt), fSt)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        change (simulateQ (implHyb pr (BMsg pr Msg) K H)
          ((fun r => (r, afSt)) <$> ((FSpec pr Msg).query (.inl (.inl n))))).run fSt = _
        simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query]
        change (fun z => ((z.1, afSt), z.2)) <$>
          (implHyb pr (BMsg pr Msg) K H (.inl (.inl n))).run fSt = _
        simp [Fxmss.Rom.implHyb, Fxmss.Rom.impl, map_eq_bind_pure_comp]
      have hR : (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((slSimImpl pr Msg enc d sf pk pkSl (.inl (.inl n))).run simSt)).run slSt =
          (fun r => ((r, simSt), slSt)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
        change (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((fun r => (r, simSt)) <$> ((Slhdsa.SlAdvSpec pr).query (.inl n)))).run slSt = _
        simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query]
        change (fun z => ((z.1, simSt), z.2)) <$>
          (StateT.lift (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))).run slSt = _
        rw [StateT.run_lift]
        simp [Functor.map_map]
      rw [hL, hR, bind_map_left, bind_map_left]
      exact evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true) fun r _ =>
        ih r afSt fSt simSt slSt k₁ k₂ hrel hk
    · -- Random oracle `H_msg^sf` (`roSpec`)
      have hL : (simulateQ (implHyb pr (BMsg pr Msg) K H)
          ((implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K' (.inl (.inr x))).run afSt)).run fSt =
          match fSt.cache x with
          | some dig => pure ((dig, afSt), fSt)
          | none => (fun dig => ((dig, afSt), { fSt with cache := fSt.cache.cacheQuery x dig })) <$> ($ᵗ pr.Digest) := by
        change (simulateQ (implHyb pr (BMsg pr Msg) K H)
          ((fun r => (r, afSt)) <$> ((FSpec pr Msg).query (.inl (.inr x))))).run fSt = _
        simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query]
        change (fun z => ((z.1, afSt), z.2)) <$>
          (Fxmss.Rom.roStep pr (BMsg pr Msg) x).run fSt = _
        unfold Fxmss.Rom.roStep
        cases hf : fSt.cache x with
        | some dig => simp [hf]
        | none => simp [hf, Functor.map_map]
      have hR : (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((slSimImpl pr Msg enc d sf pk pkSl (.inl (.inr x))).run simSt)).run slSt =
          match simSt.roCache x with
          | some dig => pure ((dig, simSt), slSt)
          | none => (fun dig => ((dig, { simSt with roCache := simSt.roCache.cacheQuery x dig }), slSt)) <$> ($ᵗ pr.Digest) := by
        change (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          (match simSt.roCache x with
           | some dig => pure (dig, simSt)
           | none => (fun dig => (dig, { simSt with roCache := simSt.roCache.cacheQuery x dig })) <$>
               (liftM ($ᵗ pr.Digest : ProbComp pr.Digest) :
                 OracleComp (Slhdsa.SlAdvSpec pr) pr.Digest))).run slSt = _
        cases simSt.roCache x with
        | some dig => simp
        | none =>
          simp only [simulateQ_map, StateT.run_map, hliftSl, Functor.map_map]
          rfl
      rw [hL, hR, hrel.roCache_eq]
      cases fSt.cache x with
      | some dig =>
        simp only [pure_bind]
        exact ih dig afSt fSt simSt slSt k₁ k₂ hrel hk
      | none =>
        simp only [bind_map_left]
        refine evalDist_bind_apply_mono_of_support ($ᵗ pr.Digest) _ _ (measurableSet_singleton true) fun dig _ => ?_
        exact ih dig afSt _ _ slSt k₁ k₂
          ⟨rfl, hrel.used_eq, hrel.ctr_eq, hrel.log_eq, hrel.rnd_eq, hrel.slLog_sub⟩ hk
    · -- Signing query `(m, b)`
      cases b
      · -- Stateful signing (`b = false`)
        have hL : (simulateQ (implHyb pr (BMsg pr Msg) K H)
            ((implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K' (.inr (m, false))).run afSt)).run fSt =
            match d.S.leafSelect afSt.ctr with
            | none => pure ((none, { afSt with log := afSt.log ++ [m] }), fSt)
            | some v =>
              let id := v.toLeafId vp.params.hsf
              if id ∈ leafIds vp.params.hsf d.S ∧ id ∉ fSt.used then
                (fun R =>
                  (((H.sig id).map (Scheme.Shrincs.Signature.stateful id.height id.index R),
                    { afSt with ctr := afSt.ctr + 1, log := afSt.log ++ [m] }),
                   { fSt with
                     cache := fSt.cache.cacheQuery (roIn pr (BMsg pr Msg) R pk H.pkSf id (pkSl, m)) (digOf pr d.ys id)
                     used := fSt.used ++ [id]
                     log := fSt.log ++ [(pkSl, m)]
                     recs := Function.update fSt.recs id (some ⟨(pkSl, m), R, digOf pr d.ys id, H.sig id⟩) })) <$>
                  ($ᵗ pr.Y)
              else
                pure ((none, { afSt with ctr := afSt.ctr + 1, log := afSt.log ++ [m] }),
                  { fSt with log := fSt.log ++ [(pkSl, m)] }) := by
          unfold implAFDet signAFDet
          simp only [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.false_eq_true, ↓reduceIte]
          cases d.S.leafSelect afSt.ctr with
          | none => simp
          | some v =>
            set id := v.toLeafId vp.params.hsf
            dsimp only [K']
            simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
              pure_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_assoc]
            change (Fxmss.Rom.signStep pr (BMsg pr Msg) K
                (fun id x => Fxmss.Rom.progStep pr (BMsg pr Msg) x (H.dig id))
                (fun id _ => H.sig id) ((pkSl, m), id)).run fSt >>= (fun z =>
              pure ((z.1.bind fun a => a.2.map (Scheme.Shrincs.Signature.stateful id.height id.index a.1),
                { afSt with ctr := afSt.ctr + 1, log := afSt.log ++ [m] }), z.2)) = _
            unfold Fxmss.Rom.signStep Fxmss.Rom.progStep
            simp only [StateT.run_bind, StateT.run_get, pure_bind]
            split_ifs
            · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_mk,
                StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_eq_bind_pure_comp]
              rfl
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              rfl
        have hR : (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
            ((slSimImpl pr Msg enc d sf pk pkSl (.inr (m, false))).run simSt)).run slSt =
            match d.S.leafSelect simSt.ctr with
            | none => pure ((none, { simSt with log := simSt.log ++ [m] }), slSt)
            | some v =>
              let id := v.toLeafId vp.params.hsf
              if id ∈ leafIds vp.params.hsf d.S ∧ id ∉ simSt.used then
                (fun R =>
                  (((sf.sig id).map (Scheme.Shrincs.Signature.stateful id.height id.index R),
                    { simSt with
                      roCache := simSt.roCache.cacheQuery (roIn pr (BMsg pr Msg) R pk sf.pkSf id (pkSl, m)) (digOf pr d.ys id)
                      used := simSt.used ++ [id]
                      ctr := simSt.ctr + 1
                      log := simSt.log ++ [m] }), slSt)) <$> ($ᵗ pr.Y)
              else
                pure ((none, { simSt with ctr := simSt.ctr + 1, log := simSt.log ++ [m] }), slSt) := by
          unfold slSimImpl
          simp only [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.false_eq_true, ↓reduceIte]
          cases d.S.leafSelect simSt.ctr with
          | none => simp
          | some v =>
            dsimp only
            set id := v.toLeafId vp.params.hsf
            split_ifs
            · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure]
              rw [hliftSl]
              simp [map_eq_bind_pure_comp]
            · simp
        rw [hL, hR, hrel.ctr_eq, hrel.used_eq]
        cases d.S.leafSelect afSt.ctr with
        | none =>
          simp only [pure_bind]
          exact ih none _ fSt _ slSt k₁ k₂
            ⟨hrel.roCache_eq, rfl, rfl, by simp [hrel.log_eq], hrel.rnd_eq,
              fun m' hm' => by
                obtain ⟨m0, hm0, heq⟩ := hrel.slLog_sub m' hm'
                exact ⟨m0, List.mem_append_left _ hm0, heq⟩⟩ hk
        | some v =>
          dsimp only
          set id := v.toLeafId vp.params.hsf
          split_ifs with hid
          · simp only [bind_map_left]
            refine evalDist_bind_apply_mono_of_support ($ᵗ pr.Y) _ _ (measurableSet_singleton true) fun R _ => ?_
            rw [hsigEq id hid.1, hpkSf]
            exact ih ((H.sig id).map (Scheme.Shrincs.Signature.stateful id.height id.index R)) _ _ _ slSt k₁ k₂
              ⟨by simp [hrel.roCache_eq], rfl, rfl,
                by simp [hrel.log_eq], hrel.rnd_eq,
                fun m' hm' => by
                  obtain ⟨m0, hm0, heq⟩ := hrel.slLog_sub m' hm'
                  exact ⟨m0, List.mem_append_left _ hm0, heq⟩⟩ hk
          · simp only [pure_bind]
            exact ih none _ _ _ slSt k₁ k₂
              ⟨hrel.roCache_eq, rfl, rfl, by simp [hrel.log_eq], hrel.rnd_eq,
                fun m' hm' => by
                  obtain ⟨m0, hm0, heq⟩ := hrel.slLog_sub m' hm'
                  exact ⟨m0, List.mem_append_left _ hm0, heq⟩⟩ hk
      · -- Stateless signing (`b = true`)
        have hL : (simulateQ (implHyb pr (BMsg pr Msg) K H)
            ((implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K' (.inr (m, true))).run afSt)).run fSt =
            (do
              let optRand ← $ᵗ pr.Y
              match afSt.rnd (.sl optRand (slMsg pr Msg enc H.pkSf m)) with
              | some R =>
                  pure ((some (.stateless (slSignDet pr pk pkSl u (slMsg pr Msg enc H.pkSf m) R)),
                    { afSt with log := afSt.log ++ [m] }), fSt)
              | none =>
                  let R ← $ᵗ pr.Y
                  pure ((some (.stateless (slSignDet pr pk pkSl u (slMsg pr Msg enc H.pkSf m) R)),
                    { afSt with
                      rnd := afSt.rnd.cacheQuery (.sl optRand (slMsg pr Msg enc H.pkSf m)) R
                      log := afSt.log ++ [m] }), fSt)) := by
          unfold implAFDet signAFDet
          simp only [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
            ↓reduceIte, hliftStateF, StateT.run_set, StateT.run_pure, bind_map_left,
            simulateQ_bind, simulateQ_pure, hliftHyb]
          unfold slStepDet lazyRO
          simp only [StateT.run_mk, bind_assoc, pure_bind]
          refine bind_congr fun optRand => ?_
          cases afSt.rnd (.sl optRand (slMsg pr Msg enc H.pkSf m)) with
          | some R => simp [K']
          | none => simp [K', map_eq_bind_pure_comp, bind_assoc]
        have hsl_inr : (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u)
            (.inr (slMsg pr Msg enc sf.pkSf m))).run slSt =
            (do
              let optRand ← $ᵗ pr.Y
              match slSt.rnd (optRand, slMsg pr Msg enc sf.pkSf m) with
              | some R => pure (slSignDet pr pk pkSl u (slMsg pr Msg enc sf.pkSf m) R,
                  { slSt with log := slSt.log ++ [slMsg pr Msg enc sf.pkSf m] })
              | none =>
                  let R ← $ᵗ pr.Y
                  pure (slSignDet pr pk pkSl u (slMsg pr Msg enc sf.pkSf m) R,
                    { log := slSt.log ++ [slMsg pr Msg enc sf.pkSf m]
                      rnd := slSt.rnd.cacheQuery (optRand, slMsg pr Msg enc sf.pkSf m) R
                      itLog := slSt.itLog ++ [(R, (pk, pkSl, slMsg pr Msg enc sf.pkSf m))] })) := by
          dsimp only [Slhdsa.slSignImpl, HAdd.hAdd, QueryImpl.add]
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            StateT.run_get, bind_assoc, pure_bind]
          refine bind_congr fun optRand => ?_
          cases slSt.rnd (optRand, slMsg pr Msg enc sf.pkSf m) with
          | some R => simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          | none =>
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
              StateT.run_pure, bind_assoc, pure_bind]
        have hR : (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
            ((slSimImpl pr Msg enc d sf pk pkSl (.inr (m, true))).run simSt)).run slSt =
            (do
              let optRand ← $ᵗ pr.Y
              match slSt.rnd (optRand, slMsg pr Msg enc sf.pkSf m) with
              | some R =>
                  pure ((some (.stateless (slSignDet pr pk pkSl u (slMsg pr Msg enc sf.pkSf m) R)),
                    { simSt with log := simSt.log ++ [m] }),
                    { slSt with log := slSt.log ++ [slMsg pr Msg enc sf.pkSf m] })
              | none =>
                  let R ← $ᵗ pr.Y
                  pure ((some (.stateless (slSignDet pr pk pkSl u (slMsg pr Msg enc sf.pkSf m) R)),
                    { simSt with log := simSt.log ++ [m] }),
                    { log := slSt.log ++ [slMsg pr Msg enc sf.pkSf m]
                      rnd := slSt.rnd.cacheQuery (optRand, slMsg pr Msg enc sf.pkSf m) R
                      itLog := slSt.itLog ++ [(R, (pk, pkSl, slMsg pr Msg enc sf.pkSf m))] })) := by
          unfold slSimImpl
          simp only [QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind,
            ↓reduceIte, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_assoc]
          rw [hsl_inr, bind_assoc]
          refine bind_congr fun optRand => ?_
          cases slSt.rnd (optRand, slMsg pr Msg enc sf.pkSf m) with
          | some R => simp
          | none => simp
        rw [hL, hR]
        simp only [bind_assoc]
        refine evalDist_bind_apply_mono_of_support ($ᵗ pr.Y) _ _ (measurableSet_singleton true) fun optRand _ => ?_
        rw [← hpkSf, hrel.rnd_eq optRand (slMsg pr Msg enc sf.pkSf m)]
        cases slSt.rnd (optRand, slMsg pr Msg enc sf.pkSf m) with
        | some R =>
          simp only [pure_bind]
          exact ih (some (.stateless (slSignDet pr pk pkSl u (slMsg pr Msg enc sf.pkSf m) R))) _ fSt _ _ k₁ k₂
            ⟨hrel.roCache_eq, hrel.used_eq, hrel.ctr_eq, by simp [hrel.log_eq], hrel.rnd_eq,
              fun m' hm' => by
                rcases List.mem_append.1 hm' with h1 | h2
                · obtain ⟨m0, hm0, heq⟩ := hrel.slLog_sub m' h1
                  exact ⟨m0, List.mem_append_left _ hm0, heq⟩
                · simp only [List.mem_singleton] at h2; subst h2
                  exact ⟨m, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩⟩ hk
        | none =>
          simp only [bind_assoc, pure_bind]
          refine evalDist_bind_apply_mono_of_support ($ᵗ pr.Y) _ _ (measurableSet_singleton true) fun R _ => ?_
          exact ih (some (.stateless (slSignDet pr pk pkSl u (slMsg pr Msg enc sf.pkSf m) R))) _ fSt _ _ k₁ k₂
            ⟨hrel.roCache_eq, hrel.used_eq, hrel.ctr_eq, by simp [hrel.log_eq],
              fun optRand' m'' => by
                by_cases hkey : (optRand', m'') = (optRand, slMsg pr Msg enc sf.pkSf m)
                · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
                  simp
                · have hne : (PrfMsgInput.sl optRand' m'' : PrfMsgInput pr.PkSeed pr.Y) ≠
                      .sl optRand (slMsg pr Msg enc sf.pkSf m) := fun h => by
                    cases h; exact hkey rfl
                  simp [hne, hkey, hrel.rnd_eq],
              fun m' hm' => by
                rcases List.mem_append.1 hm' with h1 | h2
                · obtain ⟨m0, hm0, heq⟩ := hrel.slLog_sub m' h1
                  exact ⟨m0, List.mem_append_left _ hm0, heq⟩
                · simp only [List.mem_singleton] at h2; subst h2
                  exact ⟨m, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩⟩ hk

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Game bridge (`gameHybS` → `postPrfExp`)**: under `enc.Injective`, the stateless-branch
forgery probability `Pr_{gameHybS}[W_sl]` is at most the post-PRF winning probability of
`shrincsSlAdv` against `sfStageShrincs`. -/
theorem pr_gameHybS_Wsl_le_postPrf (henc : enc.Injective)
    {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let o ← gameHybS pr Msg enc A}[HEv Wsl o] ≤
      Pr{let z ← Slhdsa.postPrfExp pr (sfStageShrincs pr Msg enc A) (shrincsSlAdv pr Msg enc A)}[
        Slhdsa.PostPrfWin pr z.1 (slRootDet pr z.1 z.2.1) z.2.2.2.log z.2.2.1] := by
  rw [prEvent_eq_evalDist_bind, prEvent_eq_evalDist_bind]
  unfold gameHybS stageHybS Slhdsa.postPrfExp sfStageShrincs Slhdsa.runPostPrf shrincsSlAdv
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_apply_mono_of_support ($ᵗ pr.PkSeed) _ _ (measurableSet_singleton true) fun pk _ => ?_
  refine evalDist_bind_apply_mono_of_support (setupHybS pr Msg enc A) _ _ (measurableSet_singleton true) fun d _ => ?_
  by_cases hS : d.S.TreeValid vp.params.hsf
  · simp only [hS, not_true_eq_false, ↓reduceIte, slKeygenS, bind_assoc, pure_bind]
    set H := hon pr d.S pk (digOf pr d.ys) (betaOf pr 0 pk d.u)
    set K : Keys pr := ⟨d.S, pk, default, H.pkSf⟩
    set sf := Slhdsa.sfPrecompDet pr pk d.S d.ys d.u
    have hpkSf : sf.pkSf = H.pkSf := (Slhdsa.sfPrecompDet_eq_hon pr hS pk d.ys d.u).1
    -- Step A: drop post-forgery `yf` query and `completion` in `progS` (`Wsl` depends only on `d.S` and `Ext`)
    have hdrop :
        ((simulateQ (implHyb pr (BMsg pr Msg) K H) (progS pr Msg enc A d.st K)).run
            (St.init pr (BMsg pr Msg) d.cache) >>= fun r =>
          pure (decide (HEv Wsl (some ((Transcript.ofRun pr (BMsg pr Msg) K (r.1.1, r.2), r.1.2), H))))) =ᵈ
        ((simulateQ (implHyb pr (BMsg pr Msg) K H) (forgeExt pr Msg enc A d.st d.S K.toPK)).run
            (St.init pr (BMsg pr Msg) d.cache) >>= fun r =>
          pure (decide (d.S.Valid vp.params.hsf ∧ r.1.2.sl = true ∧ r.1.2.fresh = true ∧ r.1.2.slOk = true))) := by
      unfold progS
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
      refine EvalDistEq.bind_right _ fun r => ?_
      have hdec : ∀ x x₁,
          decide (HEv Wsl (some ((Transcript.ofRun pr (BMsg pr Msg) K ((r.1.1.1, r.1.1.2.1, r.1.1.2.2, x), x₁), r.1.2), H))) =
          decide (d.S.Valid vp.params.hsf ∧ r.1.2.sl = true ∧ r.1.2.fresh = true ∧ r.1.2.slOk = true) :=
        fun _ _ => decide_eq_decide.2 Iff.rfl
      simp_rw [hdec]
      exact EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_const _ _)
        (EvalDistEq.bind_const _ _)
    -- Step B: switch lazy `SecCache` to eager `u ← $ᵗ (SlSecAdrs vp → pr.Y)`
    have heager := evalDistEq_apply_true (EvalDistEq.trans
      (EvalDistEq.bind_left (forgeExtDet_evalDistEq_forgeExt pr Msg enc A d.st K H
        (St.init pr (BMsg pr Msg) d.cache))
        (fun r => pure (decide (d.S.Valid vp.params.hsf ∧ r.1.2.sl = true ∧ r.1.2.fresh = true ∧ r.1.2.slOk = true))))
      hdrop.symm)
    rw [← heager]
    simp only [bind_assoc]
    refine evalDist_bind_apply_mono_of_support ($ᵗ (SlSecAdrs vp → pr.Y)) _ _
      (measurableSet_singleton true) fun u _ => ?_
    -- Step C: lockstep coupling `forgeExtDet` → `shrincsSlAdv`
    let pkSl := slRootDet pr pk u
    let K' : Keys pr := ⟨d.S, pk, pkSl, H.pkSf⟩
    have hforgeL :
        (simulateQ (implHyb pr (BMsg pr Msg) K H)
          (forgeExtDet pr Msg enc (fun p => slRootDet pr p u)
            (fun p pkSl m R => slSignDet pr p pkSl u m R) A d.st d.S K.toPK)).run
          (St.init pr (BMsg pr Msg) d.cache) >>=
        (fun r => pure (decide (d.S.Valid vp.params.hsf ∧ r.1.2.sl = true ∧ r.1.2.fresh = true ∧ r.1.2.slOk = true))) =
        (simulateQ (implHyb pr (BMsg pr Msg) K H)
          ((simulateQ (implAFDet pr Msg enc (fun p pkSl m R => slSignDet pr p pkSl u m R) K')
            (A.forge d.st d.S K'.toPK)).run ⟨0, [], ∅⟩)).run (St.init pr (BMsg pr Msg) d.cache) >>=
        (fun z => pure (decide (d.S.Valid vp.params.hsf ∧
          (extOf pr Msg enc K' z.1.1.1 (!decide (z.1.1.1 ∈ z.1.2.log)) z.1.1.2).sl = true ∧
          (extOf pr Msg enc K' z.1.1.1 (!decide (z.1.1.1 ∈ z.1.2.log)) z.1.1.2).fresh = true ∧
          (extOf pr Msg enc K' z.1.1.1 (!decide (z.1.1.1 ∈ z.1.2.log)) z.1.1.2).slOk = true))) := by
      unfold forgeExtDet
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
      rfl
    have hforgeR :
        (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          (do
            let o ← (simulateQ (slSimImpl pr Msg enc d sf pk pkSl)
              (A.forge d.st d.S (pk, pkSl, sf.pkSf))).run ⟨d.cache, [], 0, []⟩
            return if d.S.Valid vp.params.hsf ∧ o.1.1 ∉ o.2.log then
              match o.1.2 with
              | .stateless σ => some (slMsg pr Msg enc sf.pkSf o.1.1, σ)
              | .stateful _ _ _ _ => none
            else none)).run (Slhdsa.SlSignSt.init pr) >>=
        (fun res => pure (decide (Slhdsa.PostPrfWin pr pk pkSl res.2.log res.1))) =
        (simulateQ (Slhdsa.slSignImpl pr pk pkSl (slSignDet pr pk pkSl u))
          ((simulateQ (slSimImpl pr Msg enc d sf pk pkSl)
            (A.forge d.st d.S (pk, pkSl, sf.pkSf))).run ⟨d.cache, [], 0, []⟩)).run (Slhdsa.SlSignSt.init pr) >>=
        (fun z => pure (decide (Slhdsa.PostPrfWin pr pk pkSl z.2.log
          (if d.S.Valid vp.params.hsf ∧ z.1.1.1 ∉ z.1.2.log then
            match z.1.1.2 with
            | .stateless σ => some (slMsg pr Msg enc sf.pkSf z.1.1.1, σ)
            | .stateful _ _ _ _ => none
          else none)))) := by
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    rw [hforgeL, hforgeR]
    have hpkEq : (pk, pkSl, sf.pkSf) = K'.toPK := by simp [K', Fxmss.Rom.Keys.toPK, hpkSf]
    rw [hpkEq]
    refine lockstep_mono pr Msg enc d hS pk u (A.forge d.st d.S K'.toPK)
      ⟨0, [], ∅⟩ (St.init pr (BMsg pr Msg) d.cache) ⟨d.cache, [], 0, []⟩ (Slhdsa.SlSignSt.init pr)
      (fun a af' _ => pure (decide (d.S.Valid vp.params.hsf ∧
        (extOf pr Msg enc K' a.1 (!decide (a.1 ∈ af'.log)) a.2).sl = true ∧
        (extOf pr Msg enc K' a.1 (!decide (a.1 ∈ af'.log)) a.2).fresh = true ∧
        (extOf pr Msg enc K' a.1 (!decide (a.1 ∈ af'.log)) a.2).slOk = true)))
      (fun a sim' sl' => pure (decide (Slhdsa.PostPrfWin pr pk pkSl sl'.log
        (if d.S.Valid vp.params.hsf ∧ a.1 ∉ sim'.log then
          match a.2 with
          | .stateless σ => some (slMsg pr Msg enc sf.pkSf a.1, σ)
          | .stateful _ _ _ _ => none
        else none))))
      ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => by simp [Slhdsa.SlSignSt.init] at h⟩
      fun ⟨mf, σf⟩ af' f' sim' sl' hrel => ?_
    by_cases hL : d.S.Valid vp.params.hsf ∧
        (extOf pr Msg enc K' mf (!decide (mf ∈ af'.log)) σf).sl = true ∧
        (extOf pr Msg enc K' mf (!decide (mf ∈ af'.log)) σf).fresh = true ∧
        (extOf pr Msg enc K' mf (!decide (mf ∈ af'.log)) σf).slOk = true
    · obtain ⟨hval, hsl, hfr, hok⟩ := hL
      cases σf with
      | stateful _ _ _ _ => simp [extOf] at hsl
      | stateless σ =>
        simp only [extOf, Bool.not_eq_true', decide_eq_false_iff_not] at hfr hok
        have hnotSim : mf ∉ sim'.log := hrel.log_eq ▸ hfr
        have hnotSl : slMsg pr Msg enc sf.pkSf mf ∉ sl'.log := by
          intro hmem
          obtain ⟨m0, hm0, heq⟩ := hrel.slLog_sub _ hmem
          have hm_eq : mf = m0 := Slhdsa.slMsg_injective pr Msg enc henc sf.pkSf heq
          exact hfr (hm_eq ▸ hm0)
        have hver : SLHDSA.GeneralScheme.verifyInternal vp.sl pr.toSLHDSA
            (slMsg pr Msg enc sf.pkSf mf) σ ⟨pk, pkSl⟩ = true := by
          rw [← Slhdsa.slVerify_eq_verifyInternal pr Msg enc pk pkSl sf.pkSf mf σ, hpkSf]
          exact hok
        have hR : Slhdsa.PostPrfWin pr pk pkSl sl'.log
            (if d.S.Valid vp.params.hsf ∧ mf ∉ sim'.log then
              some (slMsg pr Msg enc sf.pkSf mf, σ)
            else none) := by
          rw [ite_eq_left_iff.2 (fun h => (h ⟨hval, hnotSim⟩).elim)]
          exact ⟨hnotSl, hver⟩
        rw [decide_eq_true hR]
        cases decide (d.S.Valid vp.params.hsf ∧
          (extOf pr Msg enc K' mf (!decide (mf ∈ af'.log)) (.stateless σ)).sl = true ∧
          (extOf pr Msg enc K' mf (!decide (mf ∈ af'.log)) (.stateless σ)).fresh = true ∧
          (extOf pr Msg enc K' mf (!decide (mf ∈ af'.log)) (.stateless σ)).slOk = true) <;> simp
    · simp [hL]
  · simp only [hS, not_false_eq_true, ↓reduceIte, pure_bind]
    rw [decide_eq_false (by simp [HEv])]
    simp

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] in
/-- **Main Paper Claim 4.16 (unconditional discharge of `StatelessBound`)**:
under `hinj : Function.Injective pr.yToBytes` and `henc : enc.Injective`, the stateless-branch
forgery probability `Pr_{gameHybS}[W_sl]` in `GAME.5` is bounded by the ten post-PRF summands of
`Slhdsa.postPrf_bound` for the Stage-1-precomputing reductions built from
`(sfStageShrincs, shrincsSlAdv)`. -/
theorem claim_4_16 (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let o ← gameHybS pr Msg enc A}[HEv Wsl o] ≤
      Notions.itsrSucc (Slhdsa.slHmsg pr) (Slhdsa.slMap vp)
        (Slhdsa.B_itsr pr (sfStageShrincs pr Msg enc A) (shrincsSlAdv pr Msg enc A)) +
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (Slhdsa.B_ud pr (sfStageShrincs pr Msg enc A)
          (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A)) γ) +
      SM_DT_PRE_Advantage (Slhdsa.B_pre pr (sfStageShrincs pr Msg enc A)
        (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A))) +
      SM_DT_TCR_Advantage (Slhdsa.B_tcrF_wots pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (Slhdsa.B_tcrH_xmss pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (Slhdsa.B_tcrThK pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (Slhdsa.B_tcrThLsl pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) +
      SM_DT_TCR_Advantage (Slhdsa.B_tcrH_fors pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) +
      3 * SM_DT_TCR_Advantage (Slhdsa.B_tcrF_fors pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) +
      SM_DT_DSPR_Advantage (Slhdsa.B_dsprF_fors pr (sfStageShrincs pr Msg enc A)
        (shrincsSlAdv pr Msg enc A)) :=
  (pr_gameHybS_Wsl_le_postPrf pr Msg enc henc A).trans
    (Slhdsa.postPrf_bound pr hinj (sfStageShrincs pr Msg enc A) (shrincsSlAdv pr Msg enc A))

end Claim416

end ShrincsSecurity.Shrincs

end
