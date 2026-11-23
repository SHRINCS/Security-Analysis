module

public import ShrincsSecurity.Shrincs.Wrapper

/-!
# `GAME.2` in the form of Section 4.7: the forger `A_F`

`SHRINCS-Security-Analysis.pdf`, Section 4.8 (txt lines 4085–4095): "Restricted to the stateful
signing oracle and the stateful verification branch, `GAME.4` is the game `F.2` for the structure
`Π` … With the stateless path added, `GAME.4` is `F.2⁺` played by the forger `A_F`". This file
proves the corresponding identification at `GAME.2`: the game `game2` (`Games.lean`, one flat
handler for both paths) has the success probability of the augmented game `gameS implG`
(`Wrapper.lean`), in which the stateful path is the signing oracle of Section 4.7 (`implG`) and
the stateless path is simulated by `A_F`, with success event `W_sf ∨ W_sl`.

The two games differ in:

* the position of `PK.seed` (before `A₁` in `gameS`), which commutes with `A₁`;
* the stateful randomizers: lazily sampled at the inputs `(sf, PK.seed, idx, M̃)` in `GAME.2`,
  fresh uniform in `implG`; every stateful signing query names a fresh anchor (`leafSelect` is
  injective on a valid structure), so its input is fresh;
* the handlers: one flat handler in `GAME.2`, `A_F`'s handler over `implG` in `gameS`; the
  stateless randomizers, cached by `A_F` at the `PRF_msg^sl` inputs, are the `sl`-part of the
  randomizer cache of `GAME.2`, the stateful ones are read off the records of `implG`;
* the verification query and the completion of Remark 4.6 run after `A₂` in `gameS`, which do
  not change the winning check; the freshness of `A_F`'s FXMSS forgery follows from freshness for
  both paths (every FXMSS query of `A_F` carries a message `A` queried).

## Proof

After `PK.seed`, `A₁`, the validity check and the stateful secrets, both games compute `PK.sl`
from the same lazily sampled secrets (`slRoot_run`, by VCVio's naturality of the secret-provider
programs under the lift `liftR` of the secret-cache monad into `M2`). The forging phases are
compared on flattened handlers: `FG` (the handler of `GAME.2` on `(CSt × SecCache) × RndCache`)
and `FS` (`A_F`'s handler over `implG` on `AFSt × St`). The projection `proj` reads `GAME.2`'s
state off `gameS`'s: the stateless randomizers from `A_F`'s cache and the stateful ones from the
records of `implG` (`sfC`); under the invariant `Inv` (every used anchor was selected at an
earlier counter, every record is at a used anchor, every FXMSS message carries a message of
`A`) each query step commutes with `proj` (`proj_step`): a stateful query names a fresh anchor
(`fresh_of_inv`), so its randomizer input is uncached in `GAME.2` and the lazy draw is the
uniform `R ←$` of `implG`. The tails then agree (`tail_eq`): the verification queries read the
same cache, and the completion of Remark 4.6 neither changes the event nor fails.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option linter.unusedSectionVars false

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte)
open Fxmss.Rom (Keys implG)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]

namespace Bridge2

open Fxmss.Rom (roIn verifyWith pkSfOf skOf SkIdx Keys roSpec RoIn St Transcript completion
  otherMsg anchorList implG Rec)

/-- Lift of the secret-cache monad into `M2`. -/
def liftR : StateT (SecCache pr) ProbComp →ᵐ M2 pr where
  toFun _ x := StateT.mk fun sc => StateT.mk fun rc => (fun p => (p, rc)) <$> x.run sc
  toFun_pure' x := by
    ext sc rc; simp
  toFun_bind' x y := by
    ext sc rc; simp [StateT.run_bind, map_bind]

@[simp] theorem liftR_run {α : Type} (x : StateT (SecCache pr) ProbComp α) (sc : SecCache pr)
    (rc : RndCache pr) : ((liftR pr x).run sc).run rc = (fun p => (p, rc)) <$> x.run sc := rfl

theorem liftR_lazyRO (x : pr.PkSeed × SecAdrs) :
    liftR pr (lazyRO x : StateT (SecCache pr) ProbComp pr.Y) = (lazyRO x : M2 pr pr.Y) := by
  ext sc rc
  simp only [liftR_run]
  cases h : sc.toFn x <;> simp [lazyRO, h]

/-- `liftR` as a query-preserving morphism for the public hashes. -/
def liftQ : letI := pubQ pr (StateT (SecCache pr) ProbComp); letI := pubQ pr (M2 pr)
    HasQuery.QueryHom (SLHDSA.publicHashSpec pr.toSLHDSA.core)
    (StateT (SecCache pr) ProbComp) (M2 pr) :=
  letI := pubQ pr (StateT (SecCache pr) ProbComp); letI := pubQ pr (M2 pr)
  { liftR pr with map_query' := fun _ => (liftR pr).toFun_pure' _ }

theorem guard_liftR (pk : pr.PkSeed) (a : Adrs) (ha : a.IsSecretKey) :
    letI := pubQ pr (StateT (SecCache pr) ProbComp); letI := pubQ pr (M2 pr)
    (liftQ pr).toMonadHom (guardSec pr (lazyRO : _ → StateT (SecCache pr) ProbComp pr.Y) pk a) =
      guardSec pr (lazyRO : _ → M2 pr pr.Y) pk a := by
  simp only [guardSec, ha, dite_true]
  exact liftR_lazyRO pr (pk, ⟨a, ha⟩)

theorem slRootM_M2 (pk : pr.PkSeed) :
    slRootM pr (lazyRO : _ → M2 pr pr.Y) pk =
      liftR pr (slRootM pr (lazyRO : _ → StateT (SecCache pr) ProbComp pr.Y) pk) := by
  unfold slRootM
  let := pubQ pr (StateT (SecCache pr) ProbComp); let := pubQ pr (M2 pr)
  exact (SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural pr.toSLHDSA.core (vp := vp.sl)
    (liftQ pr) _ _ (guard_liftR pr pk) pk).symm

theorem slRoot_run (pk : pr.PkSeed) (sc : SecCache pr) (rc : RndCache pr) :
    ((slRootM pr (lazyRO : _ → M2 pr pr.Y) pk).run sc).run rc =
      (fun p => (p, rc)) <$> slRootP pr pk sc := by
  rw [slRootM_M2]; rfl

/-- The stateless signer at a supplied randomizer, on the secret cache. -/
noncomputable def signP (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (R : pr.Y) :
    StateT (SecCache pr) ProbComp (Stateless.Sig pr) :=
  letI := pubQ pr (StateT (SecCache pr) ProbComp)
  SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
    (guardSec pr lazyRO pk) (slMsg pr Msg enc pkSf msg) pk pkSl R

theorem slStepP_eq (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (sc : SecCache pr)
    (rc : RndCache pr) :
    slStepP pr Msg enc pk pkSl pkSf msg sc rc =
      ($ᵗ pr.Y : ProbComp pr.Y) >>= fun o =>
      (lazyRO (.sl o (slMsg pr Msg enc pkSf msg)) :
        StateT (RndCache pr) ProbComp pr.Y).run rc >>= fun r =>
      (signP pr Msg enc pk pkSl pkSf msg r.1).run sc >>= fun p => pure (p, r.2) := by
  have h : ∀ R, (letI := pubQ pr (M2 pr)
    SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM (vp := vp.sl) pr.toSLHDSA.core
      (guardSec pr (lazyRO : _ → M2 pr pr.Y) pk) (slMsg pr Msg enc pkSf msg) pk pkSl R) =
      liftR pr (signP pr Msg enc pk pkSl pkSf msg R) := fun R =>
    letI := pubQ pr (StateT (SecCache pr) ProbComp); letI := pubQ pr (M2 pr)
    (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural pr.toSLHDSA.core (vp := vp.sl)
      (liftQ pr) _ _ (guard_liftR pr pk) _ pk pkSl R).symm
  simp only [slStepP, slSignM, h]
  simp [StateT.run_bind]

/-- Game2's handler, flattened. -/
noncomputable abbrev implC2 (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :=
  implC pr Msg enc (lazyRO : _ → M2 pr pr.Y)
    (fun x => liftM (lazyRO x : StateT (RndCache pr) ProbComp pr.Y)) K sk

/-- The lazily sampled random oracle on a cache. -/
noncomputable def roC (x : RoIn pr (BMsg pr Msg)) (c : (roSpec pr (BMsg pr Msg)).QueryCache) :
    ProbComp (pr.Digest × (roSpec pr (BMsg pr Msg)).QueryCache) :=
  match c x with
  | some d => pure (d, c)
  | none => (fun d => (d, c.cacheQuery x d)) <$> ($ᵗ pr.Digest)

theorem roStep_run (x : RoIn pr (BMsg pr Msg)) (s : St pr (BMsg pr Msg)) :
    (Fxmss.Rom.roStep pr (BMsg pr Msg) x).run s =
      (fun p => (p.1, { s with cache := p.2 })) <$> roC pr Msg x s.cache := by
  cases h : s.cache.toFn x <;> simp [Fxmss.Rom.roStep, roC, h]

theorem roStepC_run (x : RoIn pr (BMsg pr Msg)) (cs : CSt pr Msg) (sc : SecCache pr)
    (rc : RndCache pr) :
    (((roStepC pr Msg x : StateT (CSt pr Msg) (M2 pr) pr.Digest).run cs).run sc).run rc =
      (fun p => (((p.1, { cs with cache := p.2 }), sc), rc)) <$> roC pr Msg x cs.cache := by
  cases h : cs.cache.toFn x <;> simp [roStepC, roC, h]

theorem implC2_coin (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (n : ℕ) (cs : CSt pr Msg)
    (sc : SecCache pr) (rc : RndCache pr) :
    (((implC2 pr Msg enc K sk (.inl (.inl n))).run cs).run sc).run rc =
      (fun u => (((u, cs), sc), rc)) <$> (unifSpec.query n : ProbComp _) := by
  simp [implC]

theorem implC2_ro (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (x : RoIn pr (BMsg pr Msg))
    (cs : CSt pr Msg) (sc : SecCache pr) (rc : RndCache pr) :
    (((implC2 pr Msg enc K sk (.inl (.inr x))).run cs).run sc).run rc =
      (fun p => (((p.1, { cs with cache := p.2 }), sc), rc)) <$> roC pr Msg x cs.cache := by
  simp only [implC, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  exact roStepC_run pr Msg x cs sc rc

theorem implAF_coin (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) (K : Keys pr) (n : ℕ)
    (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk) ((implAF pr Msg enc K (.inl (.inl n))).run a)).run s =
      (fun u => ((u, a), s)) <$> (unifSpec.query n : ProbComp _) := by
  simp [implAF, implG, Fxmss.Rom.impl]

theorem implAF_ro (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) (K : Keys pr) (x : RoIn pr (BMsg pr Msg))
    (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk) ((implAF pr Msg enc K (.inl (.inr x))).run a)).run s =
      (fun p => ((p.1, a), { s with cache := p.2 })) <$> roC pr Msg x s.cache := by
  simp [implAF, implG, Fxmss.Rom.impl, roStep_run]

theorem implC2_sl (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (m : Msg)
    (cs : CSt pr Msg) (sc : SecCache pr) (rc : RndCache pr) :
    (((implC2 pr Msg enc K sk (.inr (m, true))).run cs).run sc).run rc =
      (fun r => (((some (.stateless r.1.1), { cs with log := cs.log ++ [m] }), r.1.2), r.2)) <$>
        slStepP pr Msg enc K.pk K.pkSl K.pkSf m sc rc := by
  simp [implC, signStepC, slStepP, StateT.run_bind]

/-- `A_F`'s oracles, re-associated as coins + (`H_msg^sf` + signing). -/
abbrev FSpec' := unifSpec + (roSpec pr (BMsg pr Msg) +
  Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))

/-- A `ProbComp` lifted to `A_F`'s oracles along the canonical sum embedding. -/
noncomputable abbrev liftF {α : Type} (p : ProbComp α) : OracleComp (FSpec pr Msg) α :=
  liftComp p ((unifSpec + roSpec pr (BMsg pr Msg)) +
    Notions.FxmssScheme.signSpec (BMsg pr Msg) LeafId (Fxmss.Rom.Sig pr))

theorem liftM_eq_liftF {α : Type} (p : ProbComp α) :
    (liftM p : OracleComp (FSpec pr Msg) α) = liftF pr Msg p := by
  change liftComp (liftComp p (FSpec' pr Msg)) _ = _
  apply liftComp_liftComp
  intro t; rfl

theorem liftM_AF_run {α : Type} (p : ProbComp α) (a : AFSt pr Msg) :
    (liftM p : StateT (AFSt pr Msg) (OracleComp (FSpec pr Msg)) α).run a =
      liftF pr Msg (p >>= fun x => pure (x, a)) := by
  change liftComp (liftComp (p >>= fun x => pure (x, a)) (FSpec' pr Msg)) (FSpec pr Msg) = _
  apply liftComp_liftComp
  intro t; rfl

theorem implG_liftF (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type} (p : ProbComp α)
    (s : St pr (BMsg pr Msg)) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk) (liftF pr Msg p)).run s =
      (fun x => (x, s)) <$> p := by
  simp only [implG, Fxmss.Rom.impl, liftF]
  rw [simulateQ_add_add_liftComp_left]
  exact Fxmss.simulateQ_unifFwd_run p s

theorem implAF_sl (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) (K : Keys pr) (m : Msg)
    (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk) ((implAF pr Msg enc K (.inr (m, true))).run a)).run s =
      (fun r => ((some (.stateless r.1.1), { a with sec := r.1.2, rnd := r.2, log := a.log ++ [m] }),
        s)) <$> slStepP pr Msg enc K.pk K.pkSl K.pkSf m a.sec a.rnd := by
  simp [implAF, signAF, StateT.run_bind, liftM_AF_run, implG_liftF]

theorem implC2_sf_none (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (m : Msg)
    (cs : CSt pr Msg) (sc : SecCache pr) (rc : RndCache pr) (h : K.S.leafSelect cs.ctr = none) :
    (((implC2 pr Msg enc K sk (.inr (m, false))).run cs).run sc).run rc =
      pure (((none, { cs with log := cs.log ++ [m] }), sc), rc) := by
  simp [implC, signStepC, StateT.run_bind, h]

theorem implAF_sf_none (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) (K : Keys pr) (m : Msg)
    (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) (h : K.S.leafSelect a.ctr = none) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk) ((implAF pr Msg enc K (.inr (m, false))).run a)).run s =
      pure ((none, { a with log := a.log ++ [m] }), s) := by
  simp [implAF, signAF, StateT.run_bind, h]

theorem implC2_sf_some (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (m : Msg)
    (cs : CSt pr Msg) (sc : SecCache pr) (rc : RndCache pr) (v : Node)
    (h : K.S.leafSelect cs.ctr = some v)
    (hrc : rc.toFn (.sf K.pk (v.toLeafId vp.params.hsf) (bmBytes pr Msg enc K.pkSl m)) = none) :
    (((implC2 pr Msg enc K sk (.inr (m, false))).run cs).run sc).run rc =
      ($ᵗ pr.Y : ProbComp pr.Y) >>= fun R =>
      roC pr Msg (roIn pr (BMsg pr Msg) R K.pk K.pkSf (v.toLeafId vp.params.hsf) (K.pkSl, m))
        cs.cache >>= fun p =>
      pure ((((Scheme.Fxmss.sign pr K.S K.pk sk p.1 (v.toLeafId vp.params.hsf)).map
        (Scheme.Shrincs.Signature.stateful (v.toLeafId vp.params.hsf).height
          (v.toLeafId vp.params.hsf).index R),
        { cs with cache := p.2, ctr := cs.ctr + 1, log := cs.log ++ [m] }), sc),
        rc.cacheQuery (.sf K.pk (v.toLeafId vp.params.hsf) (bmBytes pr Msg enc K.pkSl m)) R) := by
  simp [implC, signStepC, StateT.run_bind, h, lazyRO, hrc, roStepC_run, Functor.map_map]

theorem implAF_sf_some (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) (K : Keys pr) (m : Msg)
    (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) (v : Node)
    (h : K.S.leafSelect a.ctr = some v)
    (hfr : v.toLeafId vp.params.hsf ∈ Structure.leafIds vp.params.hsf K0.S ∧
      v.toLeafId vp.params.hsf ∉ s.used) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk) ((implAF pr Msg enc K (.inr (m, false))).run a)).run s =
      ($ᵗ pr.Y : ProbComp pr.Y) >>= fun R =>
      roC pr Msg (roIn pr (BMsg pr Msg) R K0.pk K0.pkSf (v.toLeafId vp.params.hsf) (K.pkSl, m))
        s.cache >>= fun p =>
      pure (((Scheme.Fxmss.sign pr K0.S K0.pk sk p.1 (v.toLeafId vp.params.hsf)).map
        (Scheme.Shrincs.Signature.stateful (v.toLeafId vp.params.hsf).height
          (v.toLeafId vp.params.hsf).index R),
        { a with ctr := a.ctr + 1, log := a.log ++ [m] }),
        { s with
          cache := p.2
          used := s.used ++ [v.toLeafId vp.params.hsf]
          log := s.log ++ [(K.pkSl, m)]
          recs := Function.update s.recs (v.toLeafId vp.params.hsf)
            (some ⟨(K.pkSl, m), R, p.1,
              Scheme.Fxmss.sign pr K0.S K0.pk sk p.1 (v.toLeafId vp.params.hsf)⟩) }) := by
  simp [implAF, signAF, StateT.run_bind, h, implG, Fxmss.Rom.impl, Fxmss.Rom.signStep, hfr,
    roStep_run]

/-! ## The projection -/

/-- Keep the stateless entries of `rc` and the stateful entries of `g`. -/
def mergeR (rc g : RndCache pr) : RndCache pr :=
  QueryCache.ofFn fun x => match x with
    | .sl o mb => rc.toFn (.sl o mb)
    | .sf p id mb => g.toFn (.sf p id mb)

/-- The stateful randomizers of `GAME.2`, read off the records of `implG`. -/
def sfC (K : Keys pr) (s : St pr (BMsg pr Msg)) : RndCache pr :=
  QueryCache.ofFn fun x => match x with
    | .sl _ _ => none
    | .sf p id mb => (s.recs id).bind fun r =>
        if p = K.pk ∧ mb = bmBytes pr Msg enc K.pkSl r.msg.2 then some r.rand else none

theorem mergeR_cacheQuery_sl (rc g : RndCache pr) (o : pr.Y) (mb : List Byte) (v : pr.Y) :
    mergeR pr (rc.cacheQuery (.sl o mb) v) g = (mergeR pr rc g).cacheQuery (.sl o mb) v := by
  ext x
  rcases x with ⟨o', mb'⟩ | ⟨p, id, mb'⟩
  · by_cases h : o' = o ∧ mb' = mb
    · obtain ⟨rfl, rfl⟩ := h; simp [mergeR, QueryCache.cacheQuery]
    · simp [mergeR, QueryCache.cacheQuery, Function.update, h]
  · simp [mergeR, QueryCache.cacheQuery, Function.update]

theorem slStepP_merge (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (sc : SecCache pr)
    (rc g : RndCache pr) :
    (fun r => (r.1, mergeR pr r.2 g)) <$> slStepP pr Msg enc pk pkSl pkSf msg sc rc =
      slStepP pr Msg enc pk pkSl pkSf msg sc (mergeR pr rc g) := by
  rw [slStepP_eq, slStepP_eq]
  simp only [map_bind]
  refine bind_congr fun o => ?_
  have hm : (mergeR pr rc g).toFn (.sl o (slMsg pr Msg enc pkSf msg)) =
      rc.toFn (.sl o (slMsg pr Msg enc pkSf msg)) := rfl
  cases h : rc.toFn (.sl o (slMsg pr Msg enc pkSf msg)) <;>
    simp [lazyRO, h, hm, mergeR_cacheQuery_sl]

theorem sfC_update (K : Keys pr) (s : St pr (BMsg pr Msg)) (rc : RndCache pr) (id : LeafId)
    (m : Msg) (R : pr.Y) (md : pr.Digest) (sig : Option (Scheme.Fxmss.Sig pr))
    (c : (roSpec pr (BMsg pr Msg)).QueryCache) (u : List LeafId) (l : List (BMsg pr Msg))
    (hr : s.recs id = none) :
    mergeR pr rc (sfC pr Msg enc K { s with
      cache := c
      used := u
      log := l
      recs := Function.update s.recs id (some ⟨(K.pkSl, m), R, md, sig⟩) }) =
      (mergeR pr rc (sfC pr Msg enc K s)).cacheQuery (.sf K.pk id (bmBytes pr Msg enc K.pkSl m)) R := by
  ext x
  rcases x with ⟨o', mb'⟩ | ⟨p, id', mb'⟩
  · simp [mergeR, sfC, QueryCache.cacheQuery]
  · by_cases hid : id' = id
    · subst hid
      by_cases h : p = K.pk ∧ mb' = bmBytes pr Msg enc K.pkSl m
      · obtain ⟨rfl, rfl⟩ := h; simp [mergeR, sfC, QueryCache.cacheQuery]
      · simp [mergeR, sfC, QueryCache.cacheQuery, Function.update, hr, h]
    · simp [mergeR, sfC, QueryCache.cacheQuery, Function.update, hid]

/-- The keys of `implG` in `gameS` (`PK.sl` of the FXMSS game is a constant). -/
abbrev K0of (K : Keys pr) : Keys pr := ⟨K.S, K.pk, default, K.pkSf⟩

/-- `gameS`'s nested handler (`A_F` over `implG`), flattened. -/
noncomputable abbrev FS (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (advSpec pr Msg) (StateT (AFSt pr Msg × St pr (BMsg pr Msg)) ProbComp) :=
  ((implG pr (BMsg pr Msg) (K0of pr K) sk).mapStateTBase (implAF pr Msg enc K)).flattenStateT

/-- `game2`'s handler in `M2`, flattened. -/
noncomputable abbrev FG (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (advSpec pr Msg)
      (StateT ((CSt pr Msg × SecCache pr) × RndCache pr) ProbComp) :=
  (implC2 pr Msg enc K sk).flattenStateT.flattenStateT

/-- The projection of `gameS`'s state to `game2`'s. -/
def proj (K : Keys pr) (p : AFSt pr Msg × St pr (BMsg pr Msg)) :
    (CSt pr Msg × SecCache pr) × RndCache pr :=
  ((⟨p.2.cache, p.1.ctr, p.1.log⟩, p.1.sec), mergeR pr p.1.rnd (sfC pr Msg enc K p.2))

/-- The invariant of the forging phase of `gameS`. -/
def Inv (K : Keys pr) (p : AFSt pr Msg × St pr (BMsg pr Msg)) : Prop :=
  (∀ id ∈ p.2.used, ∃ j < p.1.ctr, ∃ v, K.S.leafSelect j = some v ∧ v.toLeafId vp.params.hsf = id) ∧
  (∀ id r, p.2.recs id = some r → id ∈ p.2.used) ∧
  (∀ x ∈ p.2.log, x.2 ∈ p.1.log)

theorem FS_run (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (t : (advSpec pr Msg).Domain)
    (p : AFSt pr Msg × St pr (BMsg pr Msg)) :
    (FS pr Msg enc K sk t).run p = (fun y => (y.1.1, (y.1.2, y.2))) <$>
      (simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk) ((implAF pr Msg enc K t).run p.1)).run p.2 :=
  rfl

theorem FG_run (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (t : (advSpec pr Msg).Domain)
    (q : (CSt pr Msg × SecCache pr) × RndCache pr) :
    (FG pr Msg enc K sk t).run q = (fun y => (y.1.1.1, ((y.1.1.2, y.1.2), y.2))) <$>
      (((implC2 pr Msg enc K sk t).run q.1.1).run q.1.2).run q.2 := by
  simp [QueryImpl.flattenStateT, Functor.map_map]

/-- The next anchor is fresh. -/
theorem fresh_of_inv (K : Keys pr) (hS : K.S.Valid vp.params.hsf)
    (p : AFSt pr Msg × St pr (BMsg pr Msg)) (hp : Inv pr Msg K p) (v : Node)
    (h : K.S.leafSelect p.1.ctr = some v) :
    v.toLeafId vp.params.hsf ∈ Structure.leafIds vp.params.hsf K.S ∧
      v.toLeafId vp.params.hsf ∉ p.2.used := by
  refine ⟨Finset.mem_image_of_mem _ (hS.leafSelect_mem _ _ h), fun hu => ?_⟩
  obtain ⟨j, hj, w, hw, hwv⟩ := hp.1 _ hu
  have hwv' : w = v := hS.toTreeValid.toLeafId_injOn
    (Structure.anchors_subset_nodes (hS.leafSelect_mem _ _ hw))
    (Structure.anchors_subset_nodes (hS.leafSelect_mem _ _ h)) hwv
  subst hwv'
  exact absurd (hS.leafSelect_injective _ _ _ hw h) (Nat.ne_of_lt hj)

theorem proj_step (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (hS : K.S.Valid vp.params.hsf)
    (t : (advSpec pr Msg).Domain) (p : AFSt pr Msg × St pr (BMsg pr Msg))
    (hp : Inv pr Msg K p) :
    Prod.map id (proj pr Msg enc K) <$> (FS pr Msg enc K sk t).run p =
      (FG pr Msg enc K sk t).run (proj pr Msg enc K p) := by
  rw [FS_run, FG_run, Functor.map_map]
  obtain ⟨a, s⟩ := p
  dsimp only [proj]
  rcases t with (n | x) | ⟨m, _ | _⟩
  · rw [implAF_coin, implC2_coin]
    simp [Functor.map_map, proj]
  · rw [implAF_ro, implC2_ro]
    simp [Functor.map_map, proj, sfC]
  · cases hsel : K.S.leafSelect a.ctr with
    | none =>
      rw [implAF_sf_none (h := hsel), implC2_sf_none (h := hsel)]
      simp [proj]
    | some v =>
      have hfr := fresh_of_inv pr Msg K hS (a, s) hp v hsel
      have hr : s.recs (v.toLeafId vp.params.hsf) = none := by
        cases h : s.recs (v.toLeafId vp.params.hsf) with
        | none => rfl
        | some r => exact absurd (hp.2.1 _ r h) hfr.2
      have hrc : (mergeR pr a.rnd (sfC pr Msg enc K s)).toFn
          (.sf K.pk (v.toLeafId vp.params.hsf) (bmBytes pr Msg enc K.pkSl m)) = none := by
        simp [mergeR, sfC, hr]
      rw [implAF_sf_some (K0 := K0of pr K) (h := hsel) (hfr := hfr), implC2_sf_some (h := hsel) (hrc := hrc)]
      simp only [map_bind, map_pure]
      refine bind_congr fun R => bind_congr fun q => ?_
      simp [proj, sfC_update (hr := hr)]
  · rw [implAF_sl, implC2_sl]
    simp only [Functor.map_map]
    rw [← slStepP_merge, Functor.map_map]
    rfl

theorem inv_step (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (hS : K.S.Valid vp.params.hsf)
    (t : (advSpec pr Msg).Domain) (p : AFSt pr Msg × St pr (BMsg pr Msg))
    (hp : Inv pr Msg K p) :
    ∀ y ∈ support ((FS pr Msg enc K sk t).run p), Inv pr Msg K y.2 := by
  intro y hy
  rw [FS_run] at hy
  obtain ⟨a, s⟩ := p
  obtain ⟨h1, h2, h3⟩ := hp
  rcases t with (n | x) | ⟨m, _ | _⟩
  · rw [implAF_coin] at hy
    simp at hy
    obtain ⟨u, rfl⟩ := hy
    exact ⟨h1, h2, h3⟩
  · rw [implAF_ro] at hy
    simp at hy
    obtain ⟨d, c, -, rfl⟩ := hy
    exact ⟨h1, h2, h3⟩
  · cases hsel : K.S.leafSelect a.ctr with
    | none =>
      rw [implAF_sf_none (h := hsel)] at hy
      simp at hy
      subst hy
      exact ⟨h1, h2, fun x hx => List.mem_append_left _ (h3 x hx)⟩
    | some v =>
      have hfr := fresh_of_inv pr Msg K hS (a, s) ⟨h1, h2, h3⟩ v hsel
      rw [implAF_sf_some (K0 := K0of pr K) (h := hsel) (hfr := hfr)] at hy
      simp at hy
      obtain ⟨R, d, c, -, rfl⟩ := hy
      refine ⟨fun id hid => ?_, fun id r hr => ?_, fun x hx => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hid
        rcases hid with hid | rfl
        · obtain ⟨j, hj, w, hw, hwv⟩ := h1 id hid
          exact ⟨j, Nat.lt_succ_of_lt hj, w, hw, hwv⟩
        · exact ⟨a.ctr, by simp, v, hsel, rfl⟩
      · by_cases hid : id = v.toLeafId vp.params.hsf
        · simp [hid]
        · simp [Function.update, hid] at hr
          exact List.mem_append_left _ (h2 id r hr)
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_append_left _ (h3 x hx)
        · simp
  · rw [implAF_sl] at hy
    simp at hy
    obtain ⟨σ, sc, rc, -, rfl⟩ := hy
    exact ⟨h1, h2, fun x hx => List.mem_append_left _ (h3 x hx)⟩

theorem forge_proj (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (hS : K.S.Valid vp.params.hsf)
    {α : Type} (oa : OracleComp (advSpec pr Msg) α) (p : AFSt pr Msg × St pr (BMsg pr Msg))
    (hp : Inv pr Msg K p) :
    Prod.map id (proj pr Msg enc K) <$> (simulateQ (FS pr Msg enc K sk) oa).run p =
      (simulateQ (FG pr Msg enc K sk) oa).run (proj pr Msg enc K p) :=
  map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (Inv pr Msg K) (proj pr Msg enc K)
    (inv_step pr Msg enc K sk hS) (proj_step pr Msg enc K sk hS) oa p hp

theorem pure_evalDistEq {x y : Bool} (h : x = y) :
    (pure x : ProbComp Bool) =ᵈ (pure y : ProbComp Bool) := by
  rw [h]

theorem implG_ro (K0 : Keys pr) (sk : LeafId → ℕ → pr.Y) (x : RoIn pr (BMsg pr Msg))
    (s : St pr (BMsg pr Msg)) :
    (simulateQ (implG pr (BMsg pr Msg) K0 sk)
      ((FSpec pr Msg).query (.inl (.inr x)) : OracleComp (FSpec pr Msg) pr.Digest)).run s =
      (fun p => (p.1, { s with cache := p.2 })) <$> roC pr Msg x s.cache := by
  simp [implG, Fxmss.Rom.impl, roStep_run]

/-- **The tails agree**: `game2`'s verification and freshness check is `gameS`'s verification
query, completion and event `W_sf ∨ W_sl`. -/
theorem tail_eq (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (hS : K.S.Valid vp.params.hsf)
    (out : Msg × Sig pr) (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) (rc : RndCache pr)
    (hp : Inv pr Msg K (a, s)) :
    ((((verifyC pr Msg enc K out.1 out.2 : StateT (CSt pr Msg) (M2 pr) Bool).run
        ⟨s.cache, a.ctr, a.log⟩).run a.sec).run rc >>= fun w =>
        pure (w.1.1.1 && !decide (out.1 ∈ w.1.1.2.log))) =ᵈ
    ((simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk)
        ((FSpec pr Msg).query (.inl (.inr (roIn pr (BMsg pr Msg) (outOf pr Msg K out.1 out.2).2.2.1
          K.pk K.pkSf (outOf pr Msg K out.1 out.2).2.1 (outOf pr Msg K out.1 out.2).1))) :
          OracleComp (FSpec pr Msg) pr.Digest)).run s >>= fun x_1 =>
      (simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk)
        (completion pr (BMsg pr Msg) (otherMsg (BMsg pr Msg) (outOf pr Msg K out.1 out.2).1)
          (anchorList vp.params K.S))).run x_1.2 >>= fun x_2 =>
      pure (decide (OEv WinS (some (Transcript.ofRun pr (BMsg pr Msg) (K0of pr K)
        (((outOf pr Msg K out.1 out.2).1, (outOf pr Msg K out.1 out.2).2.1,
          (outOf pr Msg K out.1 out.2).2.2, x_1.1), x_2.2),
        extOf pr Msg enc K out.1 (!decide (out.1 ∈ a.log)) out.2))))) := by
  obtain ⟨M, σ⟩ := out
  have hlog : ∀ y : pr.Y, (K.pkSl, M) ∈ s.log → M ∈ a.log := fun _ h => hp.2.2 _ h
  rw [implG_ro, bind_map_left]
  cases σ with
  | stateless σ' =>
    simp only [verifyC, outOf, extOf, StateT.run_pure, pure_bind]
    refine EvalDistEq.symm (EvalDistEq.trans (EvalDistEq.bind_right _ fun d =>
      EvalDistEq.trans (EvalDistEq.bind_right _ fun x2 => pure_evalDistEq ?_)
        (EvalDistEq.bind_const _ _)) (EvalDistEq.bind_const _ _))
    apply Bool.eq_iff_iff.2
    by_cases hM : M ∈ a.log <;> simp [OEv, WinS, Wsf, Wsl, Transcript.ofRun, hS, hM]
  | stateful z i R σt =>
    simp only [verifyC, outOf, extOf, StateT.run_bind, roStepC_run, bind_map_left, StateT.run_pure,
      pure_bind, bind_assoc]
    refine EvalDistEq.bind_right _ fun d => ?_
    refine EvalDistEq.symm (EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ fun x2 hx2 =>
      pure_evalDistEq ?_) (EvalDistEq.bind_const _ _))
    have hc := Fxmss.Rom.completion_log pr (BMsg pr Msg) (K0of pr K) sk _ (K.pkSl, M)
      (Fxmss.Rom.otherMsg_ne (BMsg pr Msg) (K.pkSl, M)) _ _ x2 hx2
    simp only at hc
    apply Bool.eq_iff_iff.2
    by_cases hM : M ∈ a.log
    · simp [OEv, WinS, Wsf, Wsl, Transcript.ofRun, hS, hM]
    · have hM' : (K.pkSl, M) ∉ s.log := fun h => hM (hlog default h)
      simp [OEv, WinS, Wsf, Wsl, Transcript.ofRun, Transcript.Win, hS, hM, hc, hM']

theorem implC2_flat (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (advSpec pr Msg) α) (cs : CSt pr Msg) (sc : SecCache pr) (rc : RndCache pr) :
    (((simulateQ (implC2 pr Msg enc K sk) oa).run cs).run sc).run rc =
      (fun y => (((y.1, y.2.1.1), y.2.1.2), y.2.2)) <$>
        (simulateQ (FG pr Msg enc K sk) oa).run ((cs, sc), rc) := by
  simp [FG, simulateQ_flattenStateT_run]

theorem FS_flat (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (advSpec pr Msg) α) (a : AFSt pr Msg) (s : St pr (BMsg pr Msg)) :
    (simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk)
      ((simulateQ (implAF pr Msg enc K) oa).run a)).run s =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (FS pr Msg enc K sk) oa).run (a, s) :=
  simulateQ_mapStateTBase_run_eq_map_flattenStateT _ _ oa a s

theorem proj_init (K : Keys pr) (sc : SecCache pr) (c : (roSpec pr (BMsg pr Msg)).QueryCache) :
    proj pr Msg enc K (⟨0, [], sc, ∅⟩, St.init pr (BMsg pr Msg) c) = ((CSt.init pr Msg c, sc), ∅) := by
  have h : mergeR pr ∅ (sfC pr Msg enc K (St.init pr (BMsg pr Msg) c)) = ∅ := by
    ext x
    rcases x with ⟨o, mb⟩ | ⟨p, id, mb⟩ <;> simp [mergeR, sfC, St.init]
  simp only [proj, h]
  rfl

theorem inv_init (K : Keys pr) (sc : SecCache pr) (c : (roSpec pr (BMsg pr Msg)).QueryCache) :
    Inv pr Msg K (⟨0, [], sc, ∅⟩, St.init pr (BMsg pr Msg) c) := by
  refine ⟨fun id h => ?_, fun id r h => ?_, fun x h => ?_⟩ <;> simp [St.init] at h

/-- **The signing phases agree** (after `PK.sl`): `game2`'s phase run in `M2` and `gameS`'s
augmented signing phase with its success event. -/
theorem inner_eq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) (st : A.State)
    (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (sc : SecCache pr)
    (c : (roSpec pr (BMsg pr Msg)).QueryCache) (hS : K.S.Valid vp.params.hsf) :
    (fun a => a.1.1.1) <$> (StateT.run ((phase2C pr Msg enc A st K
      (lazyRO : _ → M2 pr pr.Y)
      (fun x => (liftM (lazyRO x : StateT (RndCache pr) ProbComp pr.Y) : M2 pr pr.Y)) sk).run
        (CSt.init pr Msg c)) sc).run ∅ =ᵈ
    ((simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk)
        ((simulateQ (implAF pr Msg enc K) (A.forge st K.S K.toPK)).run ⟨0, [], sc, ∅⟩)).run
          (St.init pr (BMsg pr Msg) c) >>= fun x =>
      (simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk)
        ((FSpec pr Msg).query (.inl (.inr (roIn pr (BMsg pr Msg) (outOf pr Msg K x.1.1.1 x.1.1.2).2.2.1
          K.pk K.pkSf (outOf pr Msg K x.1.1.1 x.1.1.2).2.1 (outOf pr Msg K x.1.1.1 x.1.1.2).1))) :
          OracleComp (FSpec pr Msg) pr.Digest)).run x.2 >>= fun x_1 =>
      (simulateQ (implG pr (BMsg pr Msg) (K0of pr K) sk)
        (completion pr (BMsg pr Msg) (otherMsg (BMsg pr Msg) (outOf pr Msg K x.1.1.1 x.1.1.2).1)
          (anchorList vp.params K.S))).run x_1.2 >>= fun x_2 =>
      pure (decide (OEv WinS (some (Transcript.ofRun pr (BMsg pr Msg) (K0of pr K)
        (((outOf pr Msg K x.1.1.1 x.1.1.2).1, (outOf pr Msg K x.1.1.1 x.1.1.2).2.1,
          (outOf pr Msg K x.1.1.1 x.1.1.2).2.2, x_1.1), x_2.2),
        extOf pr Msg enc K x.1.1.1 (!decide (x.1.1.1 ∈ x.1.2.log)) x.1.1.2))))) := by
  simp only [phase2C, StateT.run_bind, implC2_flat, map_bind, bind_map_left]
  rw [FS_flat, bind_map_left, ← proj_init pr Msg enc K sc c,
    ← forge_proj pr Msg enc K sk hS _ _ (inv_init pr Msg K sc c), bind_map_left]
  refine EvalDistEq.bind_congr_of_support _ fun y hy => ?_
  have hinv := simulateQ_run_preserves_inv_of_query _ (Inv pr Msg K) (inv_step pr Msg enc K sk hS)
    _ _ (inv_init pr Msg K sc c) y hy
  obtain ⟨out, a, s⟩ := y
  simp only [Prod.map_fst, Prod.map_snd, id_eq, proj, StateT.run_get, StateT.run_pure, pure_bind,
    map_pure]
  exact tail_eq pr Msg enc K sk hS out a s _ hinv

end Bridge2

open Bridge2 Fxmss.Rom in
theorem game2_eq_gameS {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let b ← game2 pr Msg enc A}[b = true] =
      Pr{let o ← gameS pr Msg enc A (implG pr (BMsg pr Msg))}[OEv WinS o] := by
  have H : game2 pr Msg enc A =ᵈ (fun o => decide (OEv WinS o)) <$>
      gameS pr Msg enc A (implG pr (BMsg pr Msg)) := by
    simp only [gameS, map_bind]
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
    unfold game2
    refine EvalDistEq.bind_right _ fun z => ?_
    by_cases hv : z.1.1.Valid vp.params.hsf
    · simp only [hv, not_true_eq_false, ite_false]
      refine EvalDistEq.bind_right _ fun pk => ?_
      unfold stageGS
      rw [ite_eq_right (not_not.2 hv.toTreeValid)]
      simp only [map_bind]
      refine EvalDistEq.bind_right _ fun f => ?_
      simp only [StateT.run'_eq, StateT.run_map, StateT.run_bind, slRoot_run, progS, forgeExt,
        simulateQ_bind, liftM_eq_liftF, implG_liftF, slKeygenS, pure_bind, map_bind, bind_map_left,
        Functor.map_map, bind_assoc, Keys.toPK, StateT.run_pure, simulateQ_pure, map_pure]
      refine EvalDistEq.bind_right _ fun r => ?_
      exact inner_eq pr Msg enc A z.1.2 ⟨z.1.1, pk, r.1, pkSfOf pr z.1.1 pk (skOf pr z.1.1 f)⟩
        (skOf pr z.1.1 f) r.2 z.2 hv
    · rw [ite_eq_left hv]
      have h0 : ∀ pk, (fun o => decide (OEv WinS o)) <$>
          stageGS pr Msg enc A (implG pr (BMsg pr Msg)) pk z =
          (fun _ => false) <$> stageGS pr Msg enc A (implG pr (BMsg pr Msg)) pk z := by
        intro pk
        unfold stageGS
        split_ifs
        · simp only [map_bind]
          refine bind_congr fun _ => bind_congr fun _ => ?_
          congr 1
          funext x
          refine congrArg (pure : Bool → ProbComp Bool) (decide_eq_false ?_)
          simp [OEv, WinS, Wsf, Wsl, Transcript.ofRun, hv]
        · simp only [map_pure]
          exact congrArg (pure : Bool → ProbComp Bool) (decide_eq_false id)
      simp only [h0]
      exact (EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.map_const _ _)
        (EvalDistEq.bind_const _ _)).symm
  rw [H.prEvent_eq, prEvent_map]
  simp

end ShrincsSecurity.Shrincs

end
