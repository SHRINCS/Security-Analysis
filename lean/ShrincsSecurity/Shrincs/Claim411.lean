module

public import ShrincsSecurity.Shrincs.Natural

/-!
# Claim 4.11: `GAME.0 → GAME.1`, uniform secret elements on both paths

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.11** (txt lines 3950–3962): "A standard
reduction `B₁` samples `PK.seed` and `SK.prf` honestly and, wherever key generation would call
`PRF(SK.seed, ADRS)`, queries its oracle at `ADRS` instead … If the oracle implements `PRF(S, ·)`
for a uniform key `S`, the simulation is `GAME.0`; if it is a uniformly random function, it is
`GAME.1`." One term covers the secret elements of both paths.

The reduction is `Bprf` (`Games.lean`).

* `prfReal_Bprf`: the real world of the PRF game run by `Bprf` is `GAME.0`.
* `prfIdeal_Bprf`: the ideal world is `GAME.1`: the `|SkIdx|` queries of the stateful table hit
  pairwise distinct fresh points (the `SF_WOTS_C_PRF` addresses are pairwise distinct,
  `SfAdrs.prfAdrs_inj`), so their answers form a uniform table; the stateless queries are at
  secret-key addresses, never at a stateful address, so they see a fresh lazily sampled
  function.
* `claim_4_11`: `Succ₀ ≤ Succ₁ + Adv^{prf}(B_prf)`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs)
open Fxmss.Rom (pkSfOf skOf SkIdx Keys roSpec)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

namespace Claim411

/-- The common part of `GAME.0`, `GAME.1` and `B_prf` after the draw of the stateful table `f`:
the stateless root over the secret source `sec`, then the signing phase with the `PRF_msg`
randomizers. -/
def tail {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (z : (Structure × A.State) × (roSpec pr (BMsg pr Msg)).QueryCache) (pk : pr.PkSeed)
    (skPrf : pr.SkPrf) (f : SkIdx vp.params z.1.1 → pr.Y)
    (sec : pr.PkSeed × SecAdrs → m pr.Y) : m Bool := do
  let pkSl ← slRootM pr sec pk
  let K : Keys pr := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 f)⟩
  (phase2C pr Msg enc A z.1.2 K sec (fun x => pure (pr.PRFmsg skPrf x)) (skOf pr z.1.1 f)).run'
    (CSt.init pr Msg z.2)

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- `B_prf` in terms of `tail`. -/
theorem Bprf_eq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Bprf pr Msg enc A = (do
      let z ← (liftM (stage1S pr Msg enc A) : OracleComp (PrfSpec pr) _)
      if ¬ z.1.1.Valid vp.params.hsf then return false else do
      let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (PrfSpec pr) _)
      let skPrf ← (liftM ($ᵗ pr.SkPrf : ProbComp pr.SkPrf) : OracleComp (PrfSpec pr) _)
      let f ← tableM (fun i : SkIdx vp.params z.1.1 =>
        (PRFScheme.functionQuery (pk, sfPrfAdrs i) : OracleComp (PrfSpec pr) pr.Y))
      tail pr Msg enc A z pk skPrf f (fun x => PRFScheme.functionQuery (x.1, x.2.1))) := rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- `GAME.0` in terms of `tail`. -/
theorem game0_eq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    game0 pr Msg enc A = (do
      let skSeed ← $ᵗ pr.SkSeed
      let z ← stage1S pr Msg enc A
      if ¬ z.1.1.Valid vp.params.hsf then return false else do
      let pk ← $ᵗ pr.PkSeed
      let skPrf ← $ᵗ pr.SkPrf
      tail pr Msg enc A z pk skPrf (prfTable pr z.1.1 pk skSeed)
        (fun x => pure (pr.PRF x.1 skSeed x.2.1))) := rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- `GAME.1` in terms of `tail`. -/
theorem game1_eq {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    game1 pr Msg enc A = (do
      let z ← stage1S pr Msg enc A
      if ¬ z.1.1.Valid vp.params.hsf then return false else do
      let pk ← $ᵗ pr.PkSeed
      let skPrf ← $ᵗ pr.SkPrf
      let f ← $ᵗ (SkIdx vp.params z.1.1 → pr.Y)
      (tail pr Msg enc A z pk skPrf f
        (lazyRO : pr.PkSeed × SecAdrs → StateT (SecCache pr) ProbComp pr.Y)).run' ∅) := rfl

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- `tail` is natural in the monad (`slRootM_natural`, `phase2C_natural`). -/
theorem tail_natural {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT ProbComp m] [MonadLiftT ProbComp n] (Φ : m →ᵐ n) (hΦ : LiftPres Φ) {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (z : (Structure × A.State) × (roSpec pr (BMsg pr Msg)).QueryCache) (pk : pr.PkSeed)
    (skPrf : pr.SkPrf) (f : SkIdx vp.params z.1.1 → pr.Y)
    (sec : pr.PkSeed × SecAdrs → m pr.Y) :
    Φ (tail pr Msg enc A z pk skPrf f sec) =
      tail pr Msg enc A z pk skPrf f (fun x => Φ (sec x)) := by
  unfold tail
  rw [MonadHom.mmap_bind, slRootM_natural]
  refine bind_congr fun pkSl => ?_
  rw [StateT.run'_eq, StateT.run'_eq, MonadHom.mmap_map, phase2C_natural pr Msg enc Φ hΦ]
  simp only [MonadHom.mmap_pure]

section Table

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  {T R : Type} [DecidableEq T] [Inhabited R]

omit [LawfulMonad m] [LawfulMonad n] in
/-- Tables are natural in the monad. -/
theorem tableList_natural (Φ : m →ᵐ n) (q : T → m R) (l : List T) :
    Φ (tableList q l) = tableList (fun t => Φ (q t)) l := by
  induction l with
  | nil => exact MonadHom.mmap_pure Φ _
  | cons t ts ih =>
    rw [tableList, tableList, MonadHom.mmap_bind]
    refine bind_congr fun v => ?_
    rw [MonadHom.mmap_bind, ih]
    exact bind_congr fun g => MonadHom.mmap_pure Φ _

/-- The table of a deterministic source. -/
theorem tableList_pure (g : T → R) (l : List T) :
    tableList (fun t => (pure (g t) : m R)) l = pure fun t => if t ∈ l then g t else default := by
  induction l with
  | nil => simp [tableList]
  | cons t ts ih =>
    simp only [tableList, ih, pure_bind]
    congr 1
    funext s
    by_cases h : s = t
    · subst h; simp
    · simp [h]

/-- The full table of a deterministic source is the source. -/
theorem tableM_pure [Fintype T] (g : T → R) :
    tableM (fun t => (pure (g t) : m R)) = pure g := by
  simp [tableM, tableList_pure]

end Table

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The real PRF oracle as a monad morphism preserves the `ProbComp` lifts. -/
theorem liftPres_real (k : pr.SkSeed) :
    LiftPres (simulateQ' ((Notions.KeyedHash.toPRF (prfF pr)).prfRealQueryImpl k)) := by
  intro α p
  exact PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ k p

/-! ## Uniform tables -/

section Uniform

variable {T Y : Type} [Fintype T] [DecidableEq T] [SampleableType Y] [Inhabited Y]
  [SampleableType (T → Y)]

/-- A table of independent uniform values on a list is a uniform function masked off the list. -/
theorem tableList_uniform (l : List T) :
    tableList (fun _ => ($ᵗ Y : ProbComp Y)) l =ᵈ
      (fun f t => if t ∈ l then f t else default) <$> ($ᵗ (T → Y) : ProbComp (T → Y)) := by
  induction l with
  | nil =>
    simp only [tableList, List.not_mem_nil, ite_false]
    exact (EvalDistEq.map_const _ _).symm
  | cons t ts ih =>
    let : MeasurableSpace Y := ⊤
    have hmask : ∀ (f : T → Y) (v : Y),
        Function.update (fun s => if s ∈ ts then f s else default) t v =
          (fun s => if s ∈ t :: ts then Function.update f t v s else default) := by
      intro f v
      funext s
      by_cases h : s = t
      · subst h; simp
      · simp [h]
    calc tableList (fun _ => ($ᵗ Y : ProbComp Y)) (t :: ts)
        = ($ᵗ Y >>= fun v => tableList (fun _ => ($ᵗ Y : ProbComp Y)) ts >>= fun g =>
            pure (Function.update g t v)) := rfl
      _ =ᵈ ($ᵗ Y >>= fun v => ((fun f s => if s ∈ ts then f s else default) <$>
            ($ᵗ (T → Y) : ProbComp (T → Y))) >>= fun g => pure (Function.update g t v)) :=
          EvalDistEq.bind_right _ fun v => EvalDistEq.bind_left ih _
      _ = ($ᵗ Y >>= fun v => ($ᵗ (T → Y) : ProbComp (T → Y)) >>= fun f =>
            pure ((fun s => if s ∈ t :: ts then Function.update f t v s else default))) := by
          simp only [bind_map_left, hmask]
      _ =ᵈ (($ᵗ (T → Y) : ProbComp (T → Y)) >>= fun f =>
            pure (fun s => if s ∈ t :: ts then f s else default)) := by
          exact EvalDistEq.of_evalDist_eq <| evalDist_bind_bind_update_map _ _
            SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t
            (fun f s => if s ∈ t :: ts then f s else default)
      _ = _ := by rw [bind_pure_comp]

/-- On the whole finite type, the table of independent uniform values is a uniform function. -/
theorem tableM_uniform :
    tableM (fun _ : T => ($ᵗ Y : ProbComp Y)) =ᵈ ($ᵗ (T → Y) : ProbComp (T → Y)) := by
  refine (tableList_uniform _).trans ?_
  simp

end Uniform

/-! ## The ideal world -/

/-- The inputs of the stateless secrets. -/
abbrev SecIn : Type := pr.PkSeed × SecAdrs

/-- The oracles of a distinguisher whose queries are at secret-key addresses only. -/
abbrev SecSpec := PRFScheme.PRFOracleSpec (SecIn pr) pr.Y

/-- The cache of the ideal PRF oracle. -/
abbrev PrfCache : Type := (pr.PkSeed × Adrs →ₒ pr.Y).QueryCache

/-- The restriction of the ideal PRF cache to secret-key addresses. -/
def projC (c : PrfCache pr) : SecCache pr := QueryCache.ofFn fun x => c (x.1, x.2.1)

/-- The ideal PRF oracle, queried at secret-key addresses only. -/
def implR : QueryImpl (SecSpec pr) (StateT (PrfCache pr) ProbComp) :=
  unifFwdImpl (pr.PkSeed × Adrs →ₒ pr.Y) +
    (fun x => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1) :
      QueryImpl (SecIn pr →ₒ pr.Y) (StateT (PrfCache pr) ProbComp))

/-- The lazily sampled stateless secrets of `GAME.1`. -/
def implL : QueryImpl (SecSpec pr) (StateT (SecCache pr) ProbComp) :=
  unifFwdImpl (SecIn pr →ₒ pr.Y) +
    (fun x => lazyRO x : QueryImpl (SecIn pr →ₒ pr.Y) (StateT (SecCache pr) ProbComp))

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- A handler forwarding the uniform queries preserves the `ProbComp` lifts. -/
theorem liftPres_unifFwd {ι ι' : Type} {hs : OracleSpec ι} {spec' : OracleSpec ι'}
    (ro : QueryImpl spec' (StateT hs.QueryCache ProbComp)) :
    LiftPres (simulateQ' (unifFwdImpl hs + ro)) := by
  intro α p
  change simulateQ (unifFwdImpl hs + ro) (liftM p) = liftM p
  rw [QueryImpl.simulateQ_add_liftM_left]
  refine StateT.ext fun s => ?_
  rw [unifFwdImpl.simulateQ_run]
  simp

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- Caching at a secret-key address commutes with the restriction. -/
theorem projC_cacheQuery (c : PrfCache pr) (x : SecIn pr) (u : pr.Y) :
    projC pr (c.cacheQuery (x.1, x.2.1) u) = (projC pr c).cacheQuery x u := by
  refine QueryCache.ext fun y => ?_
  by_cases h : y = x
  · subst h
    simp [projC]
  · rw [QueryCache.cacheQuery_of_ne _ _ h]
    have h' : (y.1, y.2.1) ≠ (x.1, x.2.1) := fun e => by
      simp only [Prod.mk.injEq] at e
      exact h (Prod.ext e.1 (Subtype.ext e.2))
    simp [projC, QueryCache.cacheQuery_of_ne _ _ h']

omit [Fintype pr.Y] [DecidableEq pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] in
/-- Each step of the ideal PRF oracle at secret-key addresses is a step of the lazily sampled
secrets, through the restriction of the cache. -/
theorem implR_proj (t : (SecSpec pr).Domain) (s : PrfCache pr) :
    Prod.map id (projC pr) <$> (implR pr t).run s = (implL pr t).run (projC pr s) := by
  rcases t with n | x
  · simp [implR, implL, unifFwdImpl]
  · change Prod.map id (projC pr) <$>
        ((pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1)).run s = (lazyRO x).run (projC pr s)
    rw [randomOracle.run_eq]
    have hx : (projC pr s) x = s (x.1, x.2.1) := rfl
    cases h : s (x.1, x.2.1) with
    | some u => simp [lazyRO, hx, h]
    | none => simp [lazyRO, hx, h, projC_cacheQuery]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The tail of the ideal world reads the PRF cache at secret-key addresses only. -/
theorem tail_proj {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (z : (Structure × A.State) × (roSpec pr (BMsg pr Msg)).QueryCache) (pk : pr.PkSeed)
    (skPrf : pr.SkPrf) (f : SkIdx vp.params z.1.1 → pr.Y) (c : PrfCache pr) :
    (tail pr Msg enc A z pk skPrf f
        (fun x => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1))).run' c =
      (tail pr Msg enc A z pk skPrf f
        (lazyRO : SecIn pr → StateT (SecCache pr) ProbComp pr.Y)).run' (projC pr c) := by
  have h₁ := tail_natural pr Msg enc (simulateQ' (implR pr)) (liftPres_unifFwd _) A z pk skPrf f
    (fun x => PRFScheme.functionQuery x)
  have h₂ := tail_natural pr Msg enc (simulateQ' (implL pr)) (liftPres_unifFwd _) A z pk skPrf f
    (fun x => PRFScheme.functionQuery x)
  have e₁ : (fun x : SecIn pr => simulateQ' (implR pr) (PRFScheme.functionQuery x)) =
      fun x => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1) :=
    funext fun x => simulateQ_spec_query (implR pr) (Sum.inr x)
  have e₂ : (fun x : SecIn pr => simulateQ' (implL pr) (PRFScheme.functionQuery x)) =
      fun x => lazyRO x :=
    funext fun x => simulateQ_spec_query (implL pr) (Sum.inr x)
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [← h₁, ← h₂]
  exact run'_simulateQ_eq_of_query_map_eq _ _ _ (implR_proj pr) _ c

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- A secret-key address is an address of the stateless path. -/
theorem isStateless_of_isSecretKey {a : Adrs} (h : a.IsSecretKey) : IsStateless a :=
  h.elim (fun h => ⟨.wotsPrf, h⟩) (fun h => ⟨.forsPrf, h⟩)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- The `SF_WOTS_C_PRF` addresses of a structure are pairwise distinct. -/
theorem sfPrfAdrs_injective {S : Structure} :
    Function.Injective (sfPrfAdrs (vp := vp) (S := S)) := by
  intro i j h
  obtain ⟨-, h1, h2⟩ := SfAdrs.prfAdrs_inj.1 h
  exact Prod.ext (Subtype.ext h1) (Fin.ext h2)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- Caching a stateful secret leaves the cache at secret-key addresses unchanged. -/
theorem projC_cacheQuery_sf (c : PrfCache pr) (pk : pr.PkSeed) {S : Structure}
    (i : SkIdx vp.params S) (u : pr.Y) :
    projC pr (c.cacheQuery (pk, sfPrfAdrs i) u) = projC pr c := by
  refine QueryCache.ext fun x => ?_
  change (c.cacheQuery (pk, sfPrfAdrs i) u) (x.1, x.2.1) = c (x.1, x.2.1)
  refine QueryCache.cacheQuery_of_ne _ _ fun e => ?_
  exact SfAdrs.toAdrs_ne_of_isStateless _ (isStateless_of_isSecretKey x.2.2)
    (congrArg Prod.snd e).symm

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The stateful table drawn from the ideal PRF oracle at pairwise distinct fresh points is a
table of independent uniform values, and leaves the cache at secret-key addresses unchanged. -/
theorem table_run (pk : pr.PkSeed) {S : Structure} (l : List (SkIdx vp.params S))
    (hl : l.Nodup) (c : PrfCache pr) (hc : ∀ t ∈ l, c (pk, sfPrfAdrs t) = none) :
    (fun p => (p.1, projC pr p.2)) <$>
        (tableList (fun t => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, sfPrfAdrs t)) l).run c =
      (fun g => (g, projC pr c)) <$> tableList (fun _ => ($ᵗ pr.Y : ProbComp pr.Y)) l := by
  induction l generalizing c with
  | nil => simp [tableList]
  | cons t ts ih =>
    rw [List.nodup_cons] at hl
    simp only [tableList, StateT.run_bind, randomOracle.run_eq, hc t List.mem_cons_self, map_bind,
      bind_assoc, pure_bind]
    refine bind_congr fun u => ?_
    have hc' : ∀ t' ∈ ts, (c.cacheQuery (pk, sfPrfAdrs t) u) (pk, sfPrfAdrs t') = none := by
      intro t' ht'
      have hne : t' ≠ t := fun e => hl.1 (e ▸ ht')
      rw [QueryCache.cacheQuery_of_ne _ _ fun e => hne (sfPrfAdrs_injective (congrArg Prod.snd e))]
      exact hc t' (List.mem_cons_of_mem _ ht')
    have := ih hl.2 _ hc'
    rw [projC_cacheQuery_sf] at this
    have h2 := congrArg (fun x => (fun p => (Function.update p.1 t u, p.2)) <$> x) this
    simp only [Functor.map_map] at h2
    simpa [map_eq_bind_pure_comp] using h2

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- A lifted `ProbComp` draw at the head of a stateful run. -/
theorem run'_liftM_bind {σ α β : Type} (p : ProbComp α) (g : α → StateT σ ProbComp β) (s : σ) :
    (liftM p >>= g).run' s = p >>= fun a => (g a).run' s := by
  simp [StateT.run'_eq, map_bind]

end Claim411

open Claim411

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **The real world of `B_prf` is `GAME.0`**: interpreting the oracle by `PRF(PK.seed, SK.seed, ·)`
is a monad morphism, so the stateless secrets are the PRF values, and the table of the stateful
queries is `prfTable`. -/
theorem prfReal_Bprf {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    (Notions.KeyedHash.toPRF (prfF pr)).prfRealExperiment (Bprf pr Msg enc A) =
      game0 pr Msg enc A := by
  rw [game0_eq, PRFScheme.prfRealExperiment]
  refine bind_congr fun k => ?_
  set Φ := simulateQ' ((Notions.KeyedHash.toPRF (prfF pr)).prfRealQueryImpl k)
  have hL : LiftPres Φ := liftPres_real pr k
  change Φ (Bprf pr Msg enc A) = _
  rw [Bprf_eq, MonadHom.mmap_bind, hL]
  refine bind_congr fun z => ?_
  by_cases hv : z.1.1.Valid vp.params.hsf
  swap
  · rw [ite_eq_left hv, ite_eq_left hv]
    exact MonadHom.mmap_pure Φ false
  rw [ite_eq_right (not_not.2 hv), ite_eq_right (not_not.2 hv), MonadHom.mmap_bind, hL]
  refine bind_congr fun pk => ?_
  rw [MonadHom.mmap_bind, hL]
  refine bind_congr fun skPrf => ?_
  rw [MonadHom.mmap_bind, tableM, tableList_natural]
  have hq : (fun t : SkIdx vp.params z.1.1 => Φ (PRFScheme.functionQuery (pk, sfPrfAdrs t))) =
      fun t => pure (prfTable pr z.1.1 pk k t) :=
    funext fun t => PRFScheme.simulateQ_prfRealQueryImpl_functionQuery _ _ _
  rw [hq, ← tableM, tableM_pure, pure_bind, tail_natural pr Msg enc Φ hL]
  congr 1

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **The ideal world of `B_prf` is `GAME.1`**: the stateful queries hit pairwise distinct fresh
points (`sfPrfAdrs_injective`), so they draw a uniform table (`table_run`, `tableM_uniform`), and
leave the cache at secret-key addresses empty (`projC_cacheQuery_sf`); the stateless queries,
at secret-key addresses, then see a fresh lazily sampled function (`tail_proj`). -/
theorem prfIdeal_Bprf {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    PRFScheme.prfIdealExperiment (Bprf pr Msg enc A) =ᵈ game1 pr Msg enc A := by
  rw [game1_eq, PRFScheme.prfIdealExperiment]
  set Ψ := simulateQ' (PRFScheme.prfIdealQueryImpl (D := pr.PkSeed × Adrs) (R := pr.Y))
  have hL : LiftPres Ψ := liftPres_unifFwd _
  change (Ψ (Bprf pr Msg enc A)).run' ∅ =ᵈ _
  rw [Bprf_eq, MonadHom.mmap_bind, hL, run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun z => ?_
  by_cases hv : z.1.1.Valid vp.params.hsf
  swap
  · rw [ite_eq_left hv, ite_eq_left hv, MonadHom.mmap_pure]
    simp
  rw [ite_eq_right (not_not.2 hv), ite_eq_right (not_not.2 hv), MonadHom.mmap_bind, hL,
    run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun pk => ?_
  rw [MonadHom.mmap_bind, hL, run'_liftM_bind]
  refine EvalDistEq.bind_right _ fun skPrf => ?_
  rw [MonadHom.mmap_bind, tableM, tableList_natural]
  have hq : (fun t : SkIdx vp.params z.1.1 => Ψ (PRFScheme.functionQuery (pk, sfPrfAdrs t))) =
      fun t => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, sfPrfAdrs t) :=
    funext fun t => PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery _
  have ht : ∀ f, Ψ (tail pr Msg enc A z pk skPrf f
      (fun x => PRFScheme.functionQuery (x.1, x.2.1))) =
      tail pr Msg enc A z pk skPrf f
        (fun x => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (x.1, x.2.1)) := fun f => by
    rw [tail_natural pr Msg enc Ψ hL]
    congr 1
    funext x
    exact PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery _
  simp only [hq, ht]
  rw [StateT.run'_eq, StateT.run_bind, map_bind]
  calc _ = ((tableList (fun t => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, sfPrfAdrs t))
          Finset.univ.toList).run ∅ >>= fun p =>
            (tail pr Msg enc A z pk skPrf p.1
              (lazyRO : SecIn pr → StateT (SecCache pr) ProbComp pr.Y)).run' (projC pr p.2)) :=
        bind_congr fun p => by rw [← tail_proj, StateT.run'_eq]
    _ = (((fun p => (p.1, projC pr p.2)) <$>
          (tableList (fun t => (pr.PkSeed × Adrs →ₒ pr.Y).randomOracle (pk, sfPrfAdrs t))
            Finset.univ.toList).run ∅) >>= fun p =>
            (tail pr Msg enc A z pk skPrf p.1
              (lazyRO : SecIn pr → StateT (SecCache pr) ProbComp pr.Y)).run' p.2) := by
        rw [bind_map_left]
    _ = (tableM (fun _ : SkIdx vp.params z.1.1 => ($ᵗ pr.Y : ProbComp pr.Y)) >>= fun f =>
            (tail pr Msg enc A z pk skPrf f
              (lazyRO : SecIn pr → StateT (SecCache pr) ProbComp pr.Y)).run' ∅) := by
        rw [table_run pr pk _ (Finset.nodup_toList _) ∅ fun _ _ => rfl, bind_map_left]
        rfl
    _ =ᵈ _ := EvalDistEq.bind_left tableM_uniform _

-- The statement keeps every section instance, as fixed by the skeleton.
set_option linter.unusedSectionVars false in
/-- **Claim 4.11** (`GAME.0 → GAME.1`): `Succ₀(A) ≤ Succ₁(A) + Adv^{prf}_{PRF}(B_prf)`. -/
theorem claim_4_11 {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let b ← game0 pr Msg enc A}[b = true] ≤
      Pr{let b ← game1 pr Msg enc A}[b = true] +
        (Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A) := by
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, ← prfReal_Bprf,
    ← (prfIdeal_Bprf pr Msg enc A).evalDist_eq, PRFScheme.prfAdvantage]
  exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _

end ShrincsSecurity.Shrincs

end
