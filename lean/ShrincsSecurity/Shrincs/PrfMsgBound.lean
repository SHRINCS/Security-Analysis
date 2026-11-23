module

public import ShrincsSecurity.Shrincs.Natural

/-!
# The query budget of `B_prfmsg` (Claim 4.12)

`SHRINCS-Security-Analysis.pdf`, Claim 4.12 and Remark 4.9 (txt lines 3980–3992): the reduction
`B₂` against `PRF_msg` "query[ies] the PRF oracle classically, … once per signing query (`q_s`)".

`Bprfmsg_bound`: the reduction `Bprfmsg` (`Games.lean`) makes at most `q_s` queries to its
`PRF_msg` oracle, one per signing query of the forger on either path (a stateful query answered
`⊥` because the keys are exhausted makes none), and none for key generation or verification.
`BprfmsgAdv` packages it as an adversary of Definition 4.3 with budget `p = q_s`, so that the
`PRF_msg` term of Theorem 4.1 is `Adv^{prf}_{PRF_msg, q_s}(B_prfmsg)`.

The stateless signer of `B_prfmsg` draws its secrets lazily with its own coins: its program is the
image of the `ProbComp` program under the lift `Φ` (VCVio's naturality of
`signInternalWithSecretRandomizerM`), hence makes no oracle query; only the randomizer is a query.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte)
open Fxmss.Rom (Keys roSpec RoIn)

namespace PrfMsgBound

section Lift

variable {vp : ValidatedParams} (pr : Primitives vp.params)

/-- The monad of `B_prfmsg`'s signing phase. -/
abbrev MB : Type → Type := StateT (SecCache pr) (OracleComp (PrfMsgSpec pr))

/-- The lift of the lazily sampled secrets from `ProbComp` into `B_prfmsg`'s monad. -/
noncomputable def Φ : StateT (SecCache pr) ProbComp →ᵐ MB pr :=
  MonadHom.stateT (SecCache pr) (MonadHom.ofLift ProbComp (OracleComp (PrfMsgSpec pr)))

/-- A lifted `ProbComp` makes no `PRF_msg` query. -/
theorem liftM_bound {α : Type} (p : ProbComp α) :
    (liftM p : OracleComp (PrfMsgSpec pr) α).IsQueryBoundP Notions.IsPRFQuery 0 :=
  (isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
    rcases t with n | x
    · exact absurd ht (by simp [Notions.IsPRFQuery])
    · rfl

theorem Φ_bound {α : Type} (x : StateT (SecCache pr) ProbComp α) (c : SecCache pr) :
    ((Φ pr x).run c).IsQueryBoundP Notions.IsPRFQuery 0 := by
  rw [Φ, MonadHom.stateT_run, MonadHom.ofLift_apply]
  exact liftM_bound pr _

theorem run_liftP {α : Type} (p : ProbComp α) (c : SecCache pr) :
    (liftM p : MB pr α).run c =
      (fun a => (a, c)) <$> (liftM p : OracleComp (PrfMsgSpec pr) α) := by
  rw [show (liftM p : MB pr α) = liftM (liftM p : StateT (SecCache pr) ProbComp α) from rfl,
    liftM_StateT_eq]
  simp [StateT.run_monadLift]

theorem liftP_run_bound {α : Type} (p : ProbComp α) (c : SecCache pr) :
    ((liftM p : MB pr α).run c).IsQueryBoundP Notions.IsPRFQuery 0 := by
  rw [run_liftP, isQueryBoundP_map_iff]
  exact liftM_bound pr p

variable [SampleableType pr.Y] [DecidableEq pr.PkSeed]

theorem Φ_lazyRO (x : pr.PkSeed × SecAdrs) :
    Φ pr (lazyRO x : StateT (SecCache pr) ProbComp pr.Y) = (lazyRO x : MB pr pr.Y) := by
  apply StateT.ext
  intro c
  simp only [Φ, MonadHom.stateT_run, lazyRO, StateT.run_mk]
  cases c x <;> simp [MonadHom.ofLift_apply]

/-- `Φ` as a query morphism of the public hashes (answered by `pr` on both sides). -/
noncomputable def ΦQ : @HasQuery.QueryHom _ (SLHDSA.publicHashSpec pr.toSLHDSA.core)
    (StateT (SecCache pr) ProbComp) _ (pubQ pr _) (MB pr) _ (pubQ pr _) :=
  @HasQuery.QueryHom.mk _ (SLHDSA.publicHashSpec pr.toSLHDSA.core)
    (StateT (SecCache pr) ProbComp) _ (pubQ pr _) (MB pr) _ (pubQ pr _) (Φ pr)
    (fun _ => (Φ pr).mmap_pure _)

variable [Inhabited pr.Y]

/-- The FIPS 205 signer of `B_prfmsg`, with lazily sampled secrets, is the lift of the
`ProbComp` signer. -/
theorem tail_eq (pk : pr.PkSeed) (pkSl R : pr.Y) (M : List Byte) :
    @SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM vp.sl pr.toSLHDSA.core (MB pr) _
      (pubQ pr _) (guardSec pr (lazyRO : _ → MB pr pr.Y) pk) M pk pkSl R =
      Φ pr (@SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM vp.sl pr.toSLHDSA.core
        (StateT (SecCache pr) ProbComp) _ (pubQ pr _)
          (guardSec pr (lazyRO : _ → StateT (SecCache pr) ProbComp pr.Y) pk) M pk pkSl R) := by
  refine (@SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural vp.sl pr.toSLHDSA.core
    _ _ _ _ _ _ (pubQ pr _) (pubQ pr _) (ΦQ pr) _ _ (fun a ha => ?_) M pk pkSl R).symm
  change Φ pr (guardSec pr _ pk a) = guardSec pr _ pk a
  unfold guardSec
  rw [dite_eq_left ha, dite_eq_left ha]
  exact Φ_lazyRO pr _

end Lift

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The stateless key generation of `B_prfmsg` makes no query. -/
theorem slRootM_bound (pk : pr.PkSeed) (c : SecCache pr) :
    ((slRootM pr (lazyRO : _ → MB pr pr.Y) pk).run c).IsQueryBoundP Notions.IsPRFQuery 0 := by
  have h := slRootM_natural pr (Φ pr) (lazyRO : _ → StateT (SecCache pr) ProbComp pr.Y) pk
  simp only [Φ_lazyRO] at h
  rw [← h]
  exact Φ_bound pr _ c

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The stateless signer of `B_prfmsg` makes one query, for the randomizer. -/
theorem slSignM_bound (pk : pr.PkSeed) (pkSl pkSf : pr.Y) (msg : Msg) (c : SecCache pr) :
    ((slSignM pr Msg enc (lazyRO : _ → MB pr pr.Y)
      (fun x => liftM (PRFScheme.functionQuery x : OracleComp (PrfMsgSpec pr) pr.Y))
        pk pkSl pkSf msg).run c).IsQueryBoundP Notions.IsPRFQuery 1 := by
  unfold slSignM
  simp only [tail_eq, StateT.run_bind]
  refine (isQueryBoundP_bind (n := 0) (m := 1) (liftP_run_bound pr _ c) fun p _ =>
    (isQueryBoundP_bind (n := 1) (m := 0) ?_ fun p' _ => Φ_bound pr _ _)).mono (by omega)
  simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_lift]
  exact (isQueryBoundP_query_bind_iff _ _ _ 1).2 ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-- The secret source of `B_prfmsg`. -/
abbrev secB : pr.PkSeed × SecAdrs → MB pr pr.Y := lazyRO

/-- The randomizer source of `B_prfmsg`: one oracle query. -/
abbrev rndB : PrfMsgInput pr.PkSeed pr.Y → MB pr pr.Y :=
  fun x => liftM (PRFScheme.functionQuery x : OracleComp (PrfMsgSpec pr) pr.Y)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
theorem run_liftP2 {α : Type} (p : ProbComp α) (s : CSt pr Msg) (c : SecCache pr) :
    ((liftM p : StateT (CSt pr Msg) (MB pr) α).run s).run c =
      (fun a => ((a, s), c)) <$> (liftM p : OracleComp (PrfMsgSpec pr) α) := by
  rw [show (liftM p : StateT (CSt pr Msg) (MB pr) α) = StateT.lift (liftM p : MB pr α) from rfl]
  simp [StateT.run_lift, run_liftP]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
theorem roStepC_bound [DecidableEq pr.Y] [DecidableEq pr.PkSeed] [DecidableEq Msg]
    (x : RoIn pr (BMsg pr Msg)) (s : CSt pr Msg) (c : SecCache pr) :
    (((roStepC pr Msg x : StateT (CSt pr Msg) (MB pr) pr.Digest).run s).run c).IsQueryBoundP
      Notions.IsPRFQuery 0 := by
  unfold roStepC
  simp only [StateT.run_mk]
  split
  · exact trivial
  · rw [StateT.run_map, run_liftP, Functor.map_map, isQueryBoundP_map_iff]
    exact liftM_bound pr _

variable [DecidableEq Msg]

omit [Fintype pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.SkPrf] in
/-- One step of `B_prfmsg`'s signing phase makes at most one query, for a signing query. -/
theorem step_bound (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (t : (advSpec pr Msg).Domain)
    (s : CSt pr Msg) (c : SecCache pr) :
    ((((implC pr Msg enc (secB pr) (rndB pr) K sk) t).run s).run c).IsQueryBoundP
      Notions.IsPRFQuery (if Notions.IsSignQuery t then 1 else 0) := by
  rcases t with (n | x) | q
  · simp only [implC, QueryImpl.add_apply_inl, Notions.IsSignQuery, ite_false]
    rw [QueryImpl.liftTarget_apply, run_liftP2, isQueryBoundP_map_iff]
    exact liftM_bound pr _
  · simp only [implC, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, Notions.IsSignQuery,
      ite_false]
    exact roStepC_bound pr Msg x s c
  · simp only [implC, QueryImpl.add_apply_inr, Notions.IsSignQuery, ite_true]
    unfold signStepC
    split
    · simp only [StateT.run_bind]
      rw [show ∀ {α : Type} (X : MB pr α), (liftM X : StateT (CSt pr Msg) (MB pr) α).run s =
        (fun a => (a, s)) <$> X from fun X => by simp [StateT.run_monadLift]]
      simp only [StateT.run_map, bind_map_left]
      exact isQueryBoundP_bind (n := 1) (m := 0) (slSignM_bound pr Msg enc _ _ _ _ c)
        fun a _ => by simp [StateT.run_modify]
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp [StateT.run_modify]
      · simp only [StateT.run_bind]
        rw [show ∀ {α : Type} (X : MB pr α), (liftM X : StateT (CSt pr Msg) (MB pr) α).run s =
          (fun a => (a, s)) <$> X from fun X => by simp [StateT.run_monadLift]]
        simp only [StateT.run_map, bind_map_left, rndB, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        refine (isQueryBoundP_query_bind_iff _ _ _ 1).2 ⟨Or.inr Nat.one_pos, fun u => ?_⟩
        simp only [Notions.IsPRFQuery, ite_true, Nat.sub_self]
        exact isQueryBoundP_bind (n := 0) (m := 0) (roStepC_bound pr Msg _ s c)
          fun a _ => by simp [StateT.run_modify]

omit [Fintype pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.Y] [DecidableEq pr.Digest]
  [SampleableType pr.SkPrf] in
/-- The verification of the forgery makes no query. -/
theorem verifyC_bound (K : Keys pr) (msg : Msg) (σ : Sig pr) (s : CSt pr Msg) (c : SecCache pr) :
    (((verifyC pr Msg enc K msg σ : StateT (CSt pr Msg) (MB pr) Bool).run s).run c).IsQueryBoundP
      Notions.IsPRFQuery 0 := by
  cases σ with
  | stateless σ' => exact trivial
  | stateful z i R σt =>
    simp only [verifyC, StateT.run_bind]
    exact isQueryBoundP_bind (n := 0) (m := 0) (roStepC_bound pr Msg _ s c) fun a _ => trivial

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The signing phase of `B_prfmsg` makes at most `q_s` queries. -/
theorem phase2C_bound {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (s : CSt pr Msg) (c : SecCache pr) :
    (((phase2C pr Msg enc A st K (secB pr) (rndB pr) sk).run s).run c).IsQueryBoundP
      Notions.IsPRFQuery qs := by
  unfold phase2C
  simp only [StateT.run_bind]
  have hsim := OracleComp.simulateQ_flattenStateT_run
    (implC pr Msg enc (secB pr) (rndB pr) K sk) (A.forge st K.S K.toPK) s c
  have hsim' : ((simulateQ (implC pr Msg enc (secB pr) (rndB pr) K sk)
      (A.forge st K.S K.toPK)).run s).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (implC pr Msg enc (secB pr) (rndB pr) K sk).flattenStateT
          (A.forge st K.S K.toPK)).run (s, c) := by
    rw [hsim]; simp
  rw [hsim', bind_map_left]
  refine (isQueryBoundP_bind (n := qs) (m := 0) ?_ fun z _ => ?_).mono (by omega)
  · refine IsQueryBoundP.simulateQ_run_StateT_of_step (A.signBound st K.S K.toPK)
      (fun t s' => ?_) (s, c)
    simp only [QueryImpl.flattenStateT, StateT.run_mk, isQueryBoundP_map_iff]
    exact step_bound pr Msg enc K sk t s'.1 s'.2
  · exact isQueryBoundP_bind (n := 0) (m := 0) (verifyC_bound pr Msg enc K _ _ _ _)
      fun a _ => by simp

end PrfMsgBound

open PrfMsgBound in
/-- **`B_prfmsg` makes at most `q_s` queries to its `PRF_msg` oracle**: one per signing query of
the forger (on either path), none for key generation or verification. -/
theorem Bprfmsg_bound {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type)
    (enc : MsgEnc Msg) [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
    [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
    [DecidableEq Msg] {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    (Bprfmsg pr Msg enc A).IsQueryBoundP Notions.IsPRFQuery qs := by
  unfold Bprfmsg
  refine (isQueryBoundP_bind (n := 0) (m := qs) (liftM_bound pr _) fun z _ => ?_).mono
    (by omega)
  split
  · exact trivial
  refine (isQueryBoundP_bind (n := 0) (m := qs) (liftM_bound pr _) fun pk _ => ?_).mono
    (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := qs) (liftM_bound pr _) fun f _ => ?_).mono
    (by omega)
  simp only [StateT.run'_eq, StateT.run_bind, isQueryBoundP_map_iff]
  refine (isQueryBoundP_bind (n := 0) (m := qs) (slRootM_bound pr _ _) fun r _ => ?_).mono
    (by omega)
  simp only [StateT.run_map, isQueryBoundP_map_iff]
  exact phase2C_bound pr Msg enc A _ _ _ _ _

/-- **`B_prfmsg` as an adversary of Definition 4.3** with budget `p = q_s`. -/
noncomputable def BprfmsgAdv {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type)
    (enc : MsgEnc Msg) [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
    [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
    [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
    [DecidableEq Msg] {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Notions.PRFAdversary (PrfMsgInput pr.PkSeed pr.Y) pr.Y qs where
  run := Bprfmsg pr Msg enc A
  queryBound := Bprfmsg_bound pr Msg enc A

end ShrincsSecurity.Shrincs

end
