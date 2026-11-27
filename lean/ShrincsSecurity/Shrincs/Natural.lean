module

public import ShrincsSecurity.Shrincs.Games

/-!
# Naturality of the games' handler, and the honest stateless path

The games and the PRF reductions of `Games.lean` run the same programs (`slRootM`, `slSignM`,
`phase2C`) in different monads with different sources of secrets and randomizers. A reduction's
real or ideal world is a game because interpreting its oracle is a monad morphism `Φ` that
commutes with these programs:

* `slRootM_natural`, `slSignM_natural`, `phase2C_natural`: a monad morphism that preserves the
  lift of `ProbComp` maps each program with sources `sec`, `rnd` to the same program with sources
  `Φ ∘ sec`, `Φ ∘ rnd` (the stateful parts through `MonadHom.stateT`).
* `slRootM_prf`, `slSignM_prf`: with the honest PRF sources, the provider programs are the
  stateless key generation and signer of the scheme (`Stateless.root`, `slSign`, VCVio's FIPS 205
  algorithms). They rest on VCVio's specialisation and naturality theorems for the secret
  providers (`HashSig.SLHDSA.SecretProvider`): the guard `guardSec` agrees with the honest
  provider at secret-key addresses, the only addresses at which the programs read a secret.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte)
open Fxmss.Rom (Keys)

/-! ## Monad morphisms through a state -/

section StateHom

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]

/-- A monad morphism lifted through `StateT σ`. -/
def MonadHom.stateT (σ : Type) (Φ : m →ᵐ n) : StateT σ m →ᵐ StateT σ n where
  toFun _ x := StateT.mk fun s => Φ (x.run s)
  toFun_pure' x := by
    ext s
    simp [StateT.run_pure]
  toFun_bind' x y := by
    ext s
    simp [StateT.run_bind]

omit [LawfulMonad m] [LawfulMonad n] in
@[simp] theorem MonadHom.stateT_run (σ : Type) (Φ : m →ᵐ n) {α : Type} (x : StateT σ m α)
    (s : σ) : (MonadHom.stateT σ Φ x).run s = Φ (x.run s) := rfl

/-- A monad morphism preserves the lift of `ProbComp`. -/
def LiftPres [MonadLiftT ProbComp m] [MonadLiftT ProbComp n] (Φ : m →ᵐ n) : Prop :=
  ∀ {α : Type} (p : ProbComp α), Φ (liftM p) = liftM p

/-- A lifted monad morphism maps the lift of `x` to the lift of `Φ x`. -/
theorem MonadHom.stateT_liftM {σ α : Type} (Φ : m →ᵐ n) (x : m α) :
    MonadHom.stateT σ Φ (liftM x : StateT σ m α) = liftM (Φ x) := by
  ext s
  simp [liftM, StateT.run_monadLift]

/-- A lifted monad morphism preserves the lift of `ProbComp`. -/
theorem MonadHom.stateT_liftPres [MonadLiftT ProbComp m] [MonadLiftT ProbComp n] {σ : Type}
    (Φ : m →ᵐ n) (hΦ : LiftPres Φ) : LiftPres (MonadHom.stateT σ Φ) := fun p => by
  change MonadHom.stateT σ Φ (liftM (liftM p : m _)) = liftM (liftM p : n _)
  rw [MonadHom.stateT_liftM, hΦ]

omit [LawfulMonad m] [LawfulMonad n] in
/-- A lifted monad morphism preserves `get`. -/
theorem MonadHom.stateT_get {σ : Type} (Φ : m →ᵐ n) :
    MonadHom.stateT σ Φ (get : StateT σ m σ) = get := by
  ext s
  simp

omit [LawfulMonad m] [LawfulMonad n] in
/-- A lifted monad morphism preserves `modify`. -/
theorem MonadHom.stateT_modify {σ : Type} (Φ : m →ᵐ n) (f : σ → σ) :
    MonadHom.stateT σ Φ (modify f : StateT σ m PUnit) = modify f := by
  ext s
  simp

/-- A monad morphism commutes with simulation when it commutes with the handler. -/
theorem MonadHom.mmap_simulateQ {ι : Type} {spec : OracleSpec ι} (Φ : m →ᵐ n)
    (impl : QueryImpl spec m) (impl' : QueryImpl spec n) (h : ∀ t, Φ (impl t) = impl' t)
    {α : Type} (oa : OracleComp spec α) : Φ (simulateQ impl oa) = simulateQ impl' oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih => simp [h, ih]

end StateHom

section PubHash

variable {vp : ValidatedParams} (pr : Primitives vp.params)
variable {m n : Type → Type} [Monad m] [Monad n]

/-- A monad morphism preserves the public hashes `pubQ`, which are `pure`. -/
def pubHom (Φ : m →ᵐ n) :
    @HasQuery.QueryHom _ (SLHDSA.publicHashSpec pr.toSLHDSA.core) m _ (pubQ pr m) n _
      (pubQ pr n) :=
  @HasQuery.QueryHom.mk _ _ m _ (pubQ pr m) n _ (pubQ pr n) Φ fun _ => Φ.mmap_pure _

/-- The guarded provider commutes with a monad morphism. -/
theorem guardSec_natural [Inhabited pr.Y] (Φ : m →ᵐ n) (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (pk : pr.PkSeed)
    (a : Adrs) : Φ (guardSec pr sec pk a) = guardSec pr (fun x => Φ (sec x)) pk a := by
  unfold guardSec
  split_ifs <;> simp

/-- Under `pubQ`, interpreting a public-hash program through the ambient queries returns the pure
value of its deterministic interpretation by `pr`. -/
theorem ofSimulateQ_pubQ [LawfulMonad m] {α : Type}
    (oa : OracleComp (SLHDSA.publicHashSpec pr.toSLHDSA.core) α) :
    letI := pubQ pr m
    (HasQuery.QueryHom.ofSimulateQ (m := m)).toMonadHom oa =
      pure (simulateQ (SLHDSA.PublicHash.impl pr.toSLHDSA) oa) :=
  (MonadHom.mmap_simulateQ (MonadHom.pure m) (SLHDSA.PublicHash.impl pr.toSLHDSA) _
    (fun _ => rfl) oa).symm

/-- The guard of the PRF secrets is the honest provider at secret-key addresses. -/
theorem guardSec_prf [Inhabited pr.Y] (skSeed : pr.SkSeed) (pk : pr.PkSeed) (a : Adrs)
    (h : a.IsSecretKey) :
    letI := pubQ pr m
    (HasQuery.QueryHom.id (SLHDSA.publicHashSpec pr.toSLHDSA.core) m).toMonadHom
        (guardSec pr (fun x => pure (pr.PRF x.1 skSeed x.2.1)) pk a) =
      pure (pr.toSLHDSA.core.PRF pk skSeed a) := by
  simp [guardSec, h]

end PubHash

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

section Natural

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] [MonadLiftT ProbComp m]
  [MonadLiftT ProbComp n] in
/-- The stateless key generation is natural in the monad. -/
theorem slRootM_natural (Φ : m →ᵐ n) (sec : pr.PkSeed × SecAdrs → m pr.Y) (pk : pr.PkSeed) :
    Φ (slRootM pr sec pk) = slRootM pr (fun x => Φ (sec x)) pk :=
  letI := pubQ pr m
  letI := pubQ pr n
  SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) _ (pubHom pr Φ) _ _
    (fun a _ => guardSec_natural pr Φ sec pk a) pk

omit [Fintype pr.Y] [DecidableEq pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The stateless signer is natural in the monad. -/
theorem slSignM_natural (Φ : m →ᵐ n) (hΦ : LiftPres Φ) (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y) (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) :
    Φ (slSignM pr Msg enc sec rnd pk pkSl pkSf msg) =
      slSignM pr Msg enc (fun x => Φ (sec x)) (fun x => Φ (rnd x)) pk pkSl pkSf msg := by
  unfold slSignM
  rw [Φ.mmap_bind, hΦ]
  refine bind_congr fun optRand => ?_
  rw [Φ.mmap_bind]
  refine bind_congr fun R => ?_
  let _ := pubQ pr m
  let _ := pubQ pr n
  exact SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl) _
    (pubHom pr Φ) _ _ (fun a _ => guardSec_natural pr Φ sec pk a) _ _ _ _

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
/-- The lazily sampled random oracle is natural in the monad. -/
theorem roStepC_natural (Φ : m →ᵐ n) (hΦ : LiftPres Φ) (x : Fxmss.Rom.RoIn pr (BMsg pr Msg)) :
    MonadHom.stateT (CSt pr Msg) Φ (roStepC pr Msg x) = roStepC pr Msg x := by
  ext s
  simp only [MonadHom.stateT_run, roStepC, StateT.run_mk]
  split
  · exact Φ.mmap_pure _
  · exact (MonadHom.mmap_map Φ _ _).trans (congrArg _ (hΦ _))

omit [Fintype pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
/-- The signing oracle is natural in the monad. -/
theorem signStepC_natural (Φ : m →ᵐ n) (hΦ : LiftPres Φ) (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y) (K : Keys pr) (sk : LeafId → ℕ → pr.Y)
    (q : Msg × Bool) :
    MonadHom.stateT (CSt pr Msg) Φ (signStepC pr Msg enc sec rnd K sk q) =
      signStepC pr Msg enc (fun x => Φ (sec x)) (fun x => Φ (rnd x)) K sk q := by
  unfold signStepC
  split_ifs
  · rw [MonadHom.mmap_bind, MonadHom.stateT_liftM, slSignM_natural pr Msg enc Φ hΦ]
    refine bind_congr fun σ => ?_
    rw [MonadHom.mmap_bind, MonadHom.stateT_modify]
    exact bind_congr fun _ => MonadHom.mmap_pure _ _
  · rw [MonadHom.mmap_bind, MonadHom.stateT_get]
    refine bind_congr fun s => ?_
    split
    · rw [MonadHom.mmap_bind, MonadHom.stateT_modify]
      exact bind_congr fun _ => MonadHom.mmap_pure _ _
    · rw [MonadHom.mmap_bind, MonadHom.stateT_liftM]
      refine bind_congr fun R => ?_
      rw [MonadHom.mmap_bind, roStepC_natural pr Msg Φ hΦ]
      refine bind_congr fun md => ?_
      rw [MonadHom.mmap_bind, MonadHom.stateT_modify]
      exact bind_congr fun _ => MonadHom.mmap_pure _ _

omit [Fintype pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
/-- The handler of the signing phase is natural in the monad. -/
theorem implC_natural (Φ : m →ᵐ n) (hΦ : LiftPres Φ) (sec : pr.PkSeed × SecAdrs → m pr.Y)
    (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y) (K : Keys pr) (sk : LeafId → ℕ → pr.Y)
    (t : (advSpec pr Msg).Domain) :
    MonadHom.stateT (CSt pr Msg) Φ (implC pr Msg enc sec rnd K sk t) =
      implC pr Msg enc (fun x => Φ (sec x)) (fun x => Φ (rnd x)) K sk t := by
  rcases t with (t | x) | q
  · exact MonadHom.stateT_liftPres Φ hΦ _
  · exact roStepC_natural pr Msg Φ hΦ x
  · exact signStepC_natural pr Msg enc Φ hΦ sec rnd K sk q

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
/-- Verification of the forgery is natural in the monad. -/
theorem verifyC_natural (Φ : m →ᵐ n) (hΦ : LiftPres Φ) (K : Keys pr) (msg : Msg)
    (σ : Sig pr) :
    MonadHom.stateT (CSt pr Msg) Φ (verifyC pr Msg enc K msg σ) = verifyC pr Msg enc K msg σ := by
  cases σ with
  | stateless σ' => exact MonadHom.mmap_pure _ _
  | stateful z i R σt =>
    rw [verifyC, MonadHom.mmap_bind, roStepC_natural pr Msg Φ hΦ]
    exact bind_congr fun _ => MonadHom.mmap_pure _ _

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The signing phase is natural in the monad. -/
theorem phase2C_natural (Φ : m →ᵐ n) (hΦ : LiftPres Φ) {qs : ℕ}
    (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) (st : A.State) (K : Keys pr)
    (sec : pr.PkSeed × SecAdrs → m pr.Y) (rnd : PrfMsgInput pr.PkSeed pr.Y → m pr.Y)
    (sk : LeafId → ℕ → pr.Y) (s : CSt pr Msg) :
    Φ ((phase2C pr Msg enc A st K sec rnd sk).run s) =
      (phase2C pr Msg enc A st K (fun x => Φ (sec x)) (fun x => Φ (rnd x)) sk).run s := by
  rw [← MonadHom.stateT_run (CSt pr Msg) Φ]
  congr 1
  unfold phase2C
  rw [MonadHom.mmap_bind,
    MonadHom.mmap_simulateQ _ _ _ (implC_natural pr Msg enc Φ hΦ sec rnd K sk)]
  refine bind_congr fun out => ?_
  rw [MonadHom.mmap_bind, verifyC_natural pr Msg enc Φ hΦ]
  refine bind_congr fun ok => ?_
  rw [MonadHom.mmap_bind, MonadHom.stateT_get]
  exact bind_congr fun _ => MonadHom.mmap_pure _ _

end Natural

section Honest

variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- With the PRF secrets, the provider key generation is `Stateless.root` (Algorithm 1). -/
theorem slRootM_prf (skSeed : pr.SkSeed) (pk : pr.PkSeed) :
    slRootM pr (m := m) (fun x => pure (pr.PRF x.1 skSeed x.2.1)) pk =
      pure (Stateless.root pr skSeed pk) := by
  let _ := pubQ pr m
  refine (SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural (vp := vp.sl) _
    (HasQuery.QueryHom.id _ m) _ _ (guardSec_prf pr skSeed pk) pk).trans ?_
  rw [SLHDSA.GeneralScheme.keygenInternalWithSecretM,
    SLHDSA.GeneralHypertree.rootWithSecretM_eq_rootM,
    ← SLHDSA.GeneralHypertree.rootM_natural vp.sl _ HasQuery.QueryHom.ofSimulateQ,
    ofSimulateQ_pubQ]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Y] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
/-- With the PRF secrets and the `PRF_msg` randomizers, the provider signer is the stateless
signer of the scheme (Algorithm 2, stateless branch). -/
theorem slSignM_prf [MonadLiftT ProbComp m] (k : SK pr) (msg : Msg) :
    slSignM pr Msg enc (m := m) (fun x => pure (pr.PRF x.1 k.skSeed x.2.1))
        (fun x => pure (pr.PRFmsg k.skPrf x)) k.pk k.pkSl k.pkSf msg =
      (fun o => slSign pr Msg enc k o msg) <$> (liftM ($ᵗ pr.Y : ProbComp pr.Y) : m pr.Y) := by
  let _ := pubQ pr m
  unfold slSignM
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun optRand => ?_
  rw [pure_bind]
  refine (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp.sl) _
    (HasQuery.QueryHom.id _ m) _ _ (guardSec_prf pr k.skSeed k.pk) _ _ _ _).trans ?_
  rw [SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM]
  change (SLHDSA.GeneralScheme.signInternalM vp.sl pr.toSLHDSA.core (slMsg pr Msg enc k.pkSf msg)
    (Stateless.secretKey pr k.skSeed k.skPrf k.pk k.pkSl) optRand : m _) = _
  rw [← SLHDSA.GeneralScheme.signInternalM_natural vp.sl _ HasQuery.QueryHom.ofSimulateQ,
    ofSimulateQ_pubQ]
  rfl

end Honest

end ShrincsSecurity.Shrincs

end
