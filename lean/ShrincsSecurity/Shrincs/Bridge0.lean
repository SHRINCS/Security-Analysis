module

public import ShrincsSecurity.Shrincs.Natural

/-!
# The EU-CMA experiment of Definition 4.15 is `GAME.0`

`SHRINCS-Security-Analysis.pdf`, Section 4.8 (txt lines 3930–3945): "By definition
`Succ₀(A) = Succ^{SHRINCS-EU-CMA}_{SHRINCS,q_s}(A)`". `succ_eq_game0` proves that the success
probability of the interface experiment `Notions.ShrincsScheme.experiment` for `scheme`
(`Model.lean`) under the random-oracle runtime is the winning probability of the explicit game
`game0` (`Games.lean`).

The two programs differ in inessential ways, each handled by one lemma (as for Theorem 4.2,
`Fxmss/Bridge.lean`):

* **Handler shape** (`Bridge0.implC_step`, `Bridge0.forge_run`). The experiment runs `A₂` against
  the scheme oracles (a `StateT (ctr, log)` handler over `unifSpec + H_msg^sf`), simulated by
  `romImpl` (state: the cache). Flattening the two `StateT` layers gives one handler on
  `(ctr, log) × cache`, the projection of `GAME.0`'s handler `implC` with the honest sources
  `PRF(·, SK.seed, ·)` and `PRF_msg(SK.prf, ·)`. The stateless signer agrees by `slSignM_prf`,
  and `PRF_msg^sf(SK.prf, PK.seed, idx, M̃)` is `PRF_msg(SK.prf, (sf, PK.seed, idx, M̃))` by
  definition.
* **Verification** (`Bridge0.verifyC_run`): the same random-oracle query on the stateful branch.
* **Stateful secrets** (`Bridge0.pkSfOf_prf`, `Bridge0.sign_prf`). The scheme derives
  `SK.wots = prfSecret`, `GAME.0` the table `skOf (prfTable)`; they agree on anchors × chains
  `< lsf`, the only entries the FXMSS root and signer read (`Bridge0.root_congr`,
  `Bridge0.sign_congr`).
* **Order of the samples**: the experiment draws `SK.seed, SK.prf, PK.seed` in key generation
  after `A₁`; `GAME.0` draws `SK.seed` before `A₁` and `PK.seed` before `SK.prf`. Independent
  samples commute (`EvalDistEq.bind_bind_swap`); the stateless root is `slRootM_prf`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme

namespace Bridge0

open Fxmss.Rom (roIn verifyWith pkSfOf skOf SkIdx Keys roSpec RoIn)
open ShrincsSecurity.Scheme.Structure (leafIds)

/-! ## The FXMSS root and signer read the secrets at anchors × chains only -/

section Congr

variable {P : Params} {pr : Primitives P}

/-- `WOTS+C.kg` reads the chain starts `ch < lsf` only. -/
theorem pkGen_congr {pk : pr.PkSeed} {id : LeafId} {f g : ℕ → pr.Y}
    (h : ∀ ch < P.lsf, f ch = g ch) : WotsC.pkGen pr pk id f = WotsC.pkGen pr pk id g := by
  simp only [WotsC.pkGen, WotsC.pkTops]
  congr 2
  funext ch
  rw [h ch.val ch.isLt]

/-- `WOTS+C.sign` reads the chain starts `ch < lsf` only. -/
theorem wotsSign_congr {pk : pr.PkSeed} {id : LeafId} {f g : ℕ → pr.Y} {md : pr.Digest}
    (h : ∀ ch < P.lsf, f ch = g ch) : WotsC.sign pr pk id f md = WotsC.sign pr pk id g md := by
  simp only [WotsC.sign, WotsC.signWith, WotsC.signChains]
  congr 1
  funext dc
  congr 2
  funext ch
  rw [h ch.val ch.isLt]

variable {S : Structure} {pk : pr.PkSeed} {sk₁ sk₂ : LeafId → ℕ → pr.Y}

/-- Secret tables that agree on anchors × chains give the same anchor values. -/
theorem leaf_congr (h : ∀ id ∈ leafIds P.hsf S, ∀ ch < P.lsf, sk₁ id ch = sk₂ id ch) :
    ∀ id ∈ leafIds P.hsf S, Fxmss.leaf pr pk sk₁ id = Fxmss.leaf pr pk sk₂ id :=
  fun id hid => pkGen_congr (h id hid)

/-- Secret tables that agree on anchors × chains give the same FXMSS root. -/
theorem root_congr (h : ∀ id ∈ leafIds P.hsf S, ∀ ch < P.lsf, sk₁ id ch = sk₂ id ch) :
    Fxmss.root pr S pk sk₁ = Fxmss.root pr S pk sk₂ :=
  Fxmss.Rom.Hyb.treeNode_congr _ (leaf_congr h) _ _

/-- Secret tables that agree on anchors × chains give the same FXMSS signatures (signing off an
anchor is `⊥` for both). -/
theorem sign_congr (h : ∀ id ∈ leafIds P.hsf S, ∀ ch < P.lsf, sk₁ id ch = sk₂ id ch)
    (md : pr.Digest) (id : LeafId) :
    Fxmss.sign pr S pk sk₁ md id = Fxmss.sign pr S pk sk₂ md id := by
  unfold Fxmss.sign
  split_ifs with hid
  · rw [wotsSign_congr (h id (Fxmss.mem_leafIds_of hid.1 hid.2)),
      Fxmss.Rom.Hyb.authPath_congr _ (leaf_congr h)]
  · rfl

end Congr

section Prf

variable {vp : ValidatedParams} (pr : Primitives vp.params) [Inhabited pr.Y]

/-- The PRF table of `GAME.0` is the scheme's `SK.wots` on anchors × chains. -/
theorem prf_agree (S : Structure) (pk : pr.PkSeed) (skSeed : pr.SkSeed) :
    ∀ id ∈ leafIds vp.params.hsf S, ∀ ch < vp.params.lsf,
      skOf pr S (prfTable pr S pk skSeed) id ch = Fxmss.prfSecret pr pk skSeed S id ch := by
  intro id hid ch hch
  simp [skOf, hid, hch, prfTable, sfPrfAdrs, Fxmss.prfSecret, WotsC.prfSecret]

/-- `PK.sf` of `GAME.0` is `PK.sf` of the scheme. -/
theorem pkSfOf_prf (S : Structure) (pk : pr.PkSeed) (skSeed : pr.SkSeed) :
    pkSfOf pr S pk (skOf pr S (prfTable pr S pk skSeed)) =
      pkSfOf pr S pk (Fxmss.prfSecret pr pk skSeed S) := by
  rw [pkSfOf, pkSfOf, root_congr (prf_agree pr S pk skSeed)]

/-- The FXMSS signatures of `GAME.0` are those of the scheme. -/
theorem sign_prf (S : Structure) (pk : pr.PkSeed) (skSeed : pr.SkSeed) (md : pr.Digest)
    (id : LeafId) :
    Fxmss.sign pr S pk (skOf pr S (prfTable pr S pk skSeed)) md id =
      Fxmss.sign pr S pk (Fxmss.prfSecret pr pk skSeed S) md id :=
  sign_congr (prf_agree pr S pk skSeed) md id

end Prf

/-! ## Flattening and projection of the signing phase -/

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

/-- The scheme oracle's state `(ctr, log)` and the random-oracle cache read off a signing-phase
state of `GAME.0`. -/
def projC (s : CSt pr Msg) : (ℕ × List Msg) × (roSpec pr (BMsg pr Msg)).QueryCache :=
  ((s.ctr, s.log), s.cache)

/-- The nested handler of the EU-CMA experiment (scheme oracles over `romImpl`), flattened. -/
noncomputable def flatImpl (k : SK pr) : QueryImpl (advSpec pr Msg)
    (StateT ((ℕ × List Msg) × (roSpec pr (BMsg pr Msg)).QueryCache) ProbComp) :=
  ((roSpec pr (BMsg pr Msg)).romImpl.mapStateTBase ((scheme pr Msg enc).oracles k)).flattenStateT

/-- The signing-phase handler of `GAME.0` with the honest PRF sources of the key `k`. -/
noncomputable abbrev implH (k : SK pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (advSpec pr Msg) (StateT (CSt pr Msg) ProbComp) :=
  implC pr Msg enc (fun x => pure (pr.PRF x.1 k.skSeed x.2.1))
    (fun x => pure (pr.PRFmsg k.skPrf x)) ⟨k.S, k.pk, k.pkSl, k.pkSf⟩ sk

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- One step of `GAME.0`'s handler, projected to `(ctr, log) × cache`, is one step of the
flattened handler of the experiment, for a secret table `sk` that signs like `SK.wots`. -/
theorem implC_step (k : SK pr) (sk : LeafId → ℕ → pr.Y)
    (hsk : ∀ md id, Fxmss.sign pr k.S k.pk sk md id = Fxmss.sign pr k.S k.pk k.wots md id)
    (t : (advSpec pr Msg).Domain) (s : CSt pr Msg) :
    Prod.map id (projC pr Msg) <$> (implH pr Msg enc k sk t).run s =
      (flatImpl pr Msg enc k t).run (projC pr Msg s) := by
  rcases t with (n | x) | ⟨msg, b⟩
  · simp [implC, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      Notions.ShrincsScheme.oracles, projC, unifFwdImpl]
  · cases h : s.cache x <;>
      simp [implC, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Notions.ShrincsScheme.oracles, projC, roStepC, h]
  · cases b
    · cases hl : k.S.leafSelect s.ctr
      · simp [implC, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          Notions.ShrincsScheme.oracles, projC, signStepC, Notions.ShrincsScheme.signOracle,
          scheme, signSF, hl]
      · simp [implC, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          Notions.ShrincsScheme.oracles, projC, signStepC, Notions.ShrincsScheme.signOracle,
          scheme, signSF, hl, roStepC, Primitives.PRFmsgSf, hsk]
        split <;> simp_all
    · simp [implC, flatImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Notions.ShrincsScheme.oracles, projC, signStepC, Notions.ShrincsScheme.signOracle,
        scheme, signSL, slSignM_prf, OracleSpec.simulateQ_romImpl_liftM_run]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **Flattening and projection**: the scheme oracles of Definition 4.15 run under `romImpl` are
the signing-phase handler of `GAME.0` with its state projected to `(ctr, log)` and the cache. -/
theorem forge_run {α : Type} (k : SK pr) (sk : LeafId → ℕ → pr.Y)
    (hsk : ∀ md id, Fxmss.sign pr k.S k.pk sk md id = Fxmss.sign pr k.S k.pk k.wots md id)
    (oa : OracleComp (advSpec pr Msg) α) (c : (roSpec pr (BMsg pr Msg)).QueryCache) :
    (simulateQ (roSpec pr (BMsg pr Msg)).romImpl
      ((simulateQ ((scheme pr Msg enc).oracles k) oa).run (0, []))).run c =
      (fun z => ((z.1, (z.2.ctr, z.2.log)), z.2.cache)) <$>
        (simulateQ (implH pr Msg enc k sk) oa).run (CSt.init pr Msg c) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change _ <$> (simulateQ (flatImpl pr Msg enc k) oa).run
    (projC pr Msg (CSt.init pr Msg c)) = _
  rw [← map_run_simulateQ_eq_of_query_map_eq _ _ _ (implC_step pr Msg enc k sk hsk),
    Functor.map_map]
  rfl

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
/-- Verification on the state of `GAME.0` is verification (Algorithm 3) under `romImpl` on its
cache; the counter and the log are untouched. -/
theorem verifyC_run (K : Keys pr) (m : Msg) (σ : Sig pr) (s : CSt pr Msg) :
    (verifyC pr Msg enc (m := ProbComp) K m σ).run s =
      (fun p => (p.1, { s with cache := p.2 })) <$>
        (simulateQ (roSpec pr (BMsg pr Msg)).romImpl (verify pr Msg enc K.toPK m σ)).run s.cache := by
  rcases σ with σ' | ⟨z, i, R, σt⟩
  · simp [verifyC, verify, Fxmss.Rom.Keys.toPK]
  · cases h : s.cache.toFn (roIn pr (BMsg pr Msg) R K.pk K.pkSf ⟨z, i⟩ (K.pkSl, m)) <;>
      simp [verifyC, verify, roStepC, h, Fxmss.Rom.Keys.toPK]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The signing phase of the experiment (forgery, verification, freshness) under `romImpl` is
the signing phase `phase2C` of `GAME.0` with the honest sources. -/
theorem signPhase {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) (st : A.State)
    (k : SK pr) (sk : LeafId → ℕ → pr.Y)
    (hsk : ∀ md id, Fxmss.sign pr k.S k.pk sk md id = Fxmss.sign pr k.S k.pk k.wots md id)
    (c : (roSpec pr (BMsg pr Msg)).QueryCache) :
    ((simulateQ (roSpec pr (BMsg pr Msg)).romImpl
      ((simulateQ ((scheme pr Msg enc).oracles k)
        (A.forge st k.S (k.pk, k.pkSl, k.pkSf))).run (0, []))).run c >>= fun a =>
      (simulateQ (roSpec pr (BMsg pr Msg)).romImpl
        (verify pr Msg enc (k.pk, k.pkSl, k.pkSf) a.1.1.1 a.1.1.2)).run a.2 >>= fun a₁ =>
      (fun x => x.1) <$> (pure (a₁.1 && !decide (a.1.1.1 ∈ a.1.2.2), a₁.2) :
        ProbComp (Bool × (roSpec pr (BMsg pr Msg)).QueryCache))) =
      (phase2C pr Msg enc A st ⟨k.S, k.pk, k.pkSl, k.pkSf⟩
        (fun x => pure (pr.PRF x.1 k.skSeed x.2.1)) (fun x => pure (pr.PRFmsg k.skPrf x)) sk).run'
        (CSt.init pr Msg c) := by
  simp only [phase2C, StateT.run'_eq, StateT.run_bind, Fxmss.Rom.Keys.toPK]
  rw [forge_run pr Msg enc k sk hsk, bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  rw [verifyC_run, bind_map_left, map_bind]
  simp [Fxmss.Rom.Keys.toPK]

end Bridge0

open Bridge0
open Fxmss.Rom (pkSfOf skOf roSpec)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **`Succ₀(A) = Succ^{SHRINCS-EU-CMA}(A)`**: the EU-CMA experiment of Definition 4.15 in the
random-oracle model has the success probability of `GAME.0`. -/
theorem succ_eq_game0 {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    succ pr Msg enc A = Pr{let b ← game0 pr Msg enc A}[b = true] := by
  have H : (simulateQ (roSpec pr (BMsg pr Msg)).romImpl
      (Notions.ShrincsScheme.experiment (scheme pr Msg enc) A)).run' ∅ =ᵈ
      (game0 pr Msg enc A >>= fun b => pure (decide (b = true))) := by
    simp only [game0, bind_assoc]
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _)
    rw [Notions.ShrincsScheme.experiment, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine EvalDistEq.bind_right _ fun z => ?_
    rcases z with ⟨⟨S, st⟩, c⟩
    dsimp only
    by_cases hv : S.Valid vp.params.hsf
    · simp only [scheme, hv, not_true_eq_false, ↓reduceIte, keygen, simulateQ_bind,
        StateT.run_bind, OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left, simulateQ_pure,
        StateT.run_pure, pure_bind, map_bind, bind_assoc, slRootM_prf]
      refine EvalDistEq.bind_right _ fun skSeed => ?_
      refine EvalDistEq.trans (EvalDistEq.bind_bind_swap _ _ _) ?_
      refine EvalDistEq.bind_right _ fun pk => EvalDistEq.bind_right _ fun skPrf => ?_
      rw [pkSfOf_prf]
      have h := signPhase pr Msg enc A st ⟨S, skSeed, skPrf, pk, Stateless.root pr skSeed pk,
        pkSfOf pr S pk (Fxmss.prfSecret pr pk skSeed S)⟩ (skOf pr S (prfTable pr S pk skSeed))
        (sign_prf pr S pk skSeed) c
      dsimp only at h
      simp only [Bool.decide_eq_true, bind_pure]
      rw [← h]
      exact EvalDistEq.rfl
    · simp only [scheme, hv, not_false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure,
        map_pure, pure_bind]
      exact (EvalDistEq.bind_const ($ᵗ pr.SkSeed : ProbComp pr.SkSeed) _).symm
  rw [succ, Notions.ShrincsScheme.succ, runtime, ProbCompRuntime.rom_evalDist, H.evalDist_eq,
    prEvent_eq_evalDist_decide]

end ShrincsSecurity.Shrincs

end
