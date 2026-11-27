module

public import ShrincsSecurity.Shrincs.Games
public import ShrincsSecurity.Shrincs.CachedPRF
public import HashSig.SLHDSA.Security.SecretTraces
import HashSig.SLHDSA.Security.AddressKeys

/-!
# The query budget `q₁` of `B_prf` (Claim 4.11)

`SHRINCS-Security-Analysis.pdf`, Claim 4.11 (txt lines 3950–3962): the reduction against `PRF`
"queries its oracle at `ADRS`" wherever key generation derives a secret element, "the queries are
classical and pairwise distinct", and the term is `InSec^prf(PRF; ξ, q₁)` with `q₁` "the total
number of secret-key elements across both paths of the SHRINCS key".

The reduction `Bprf` of `Games.lean` derives a secret element whenever a program reads one, so it
queries an address again when a later signature reads the same secret (the hypertree's WOTS+
keys are shared by many signatures). Its cached form `BprfC = cacheAdv Bprf` (`CachedPRF.lean`)
queries every input at most once and has the same advantage. Its inputs are the points
`(PK.seed, ADRS)` with `ADRS`

* the `SF_WOTS_C_PRF` address of an anchor and chain of the committed structure: `|A| · lsf`
  addresses, at most `L · lsf`; or
* a secret-key address of the SLH-DSA hypertree: a `WOTS_PRF` address of a chain of a reachable
  WOTS+ instance or a `FORS_PRF` address of a reachable FORS leaf (`slSecretList`, VCVio's ledger
  of the secret children of the construction's addresses). There are
  `slSecretCount = wotsInstanceCount · len + 2^h · k · 2^a` of them, with
  `wotsInstanceCount = Σ_{i<d} 2^{h'(d−i)}` the number of WOTS+ instances of the hypertree.

The stateless programs read secrets at these addresses only: VCVio's ledger theorems
(`keygenInternalWithSecretM_pred_of_ledger`, `signInternalWithSecretRandomizerM_pred_of_ledger`)
show that every secret read of FIPS 205 key generation and signing is at a secret child of an
address of the union ledger `constructionAddresses`, and such a child is in `slSecretList`
(`mem_slSecretList`, the proof of VCVio's `mem_secretChildren_of_inl_mem_childAdrs`).

`BprfAdv A`: `BprfC` as an adversary of Definition 4.3 with budget
`q₁ = L · lsf + slSecretCount`, and its advantage is that of `Bprf` (`prfAdv_BprfAdv`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open SLHDSA (Adrs Byte wotsSkAdrs forsSkAdrs)
open SLHDSA.Security
open Fxmss.Rom (Keys roSpec RoIn SkIdx skOf pkSfOf)
open ShrincsSecurity.Scheme.Structure (leafIds)
open CachedPRF (cacheAdv InSet)

/-! ## The secret-key addresses of the hypertree -/

section SlSecrets

variable (vp : SLHDSA.ValidatedParams)

/-- The secret-key addresses of the SLH-DSA hypertree: the `WOTS_PRF` address of every chain of
every reachable WOTS+ instance, and the `FORS_PRF` address of every reachable FORS leaf. -/
def slSecretList : List Adrs :=
  (allWotsChains vp).map (fun c => wotsSkAdrs (wotsInstanceAdrs c.1) c.2.val) ++
    (forsLeafAddresses vp).map fun b => forsSkAdrs b b.word3

/-- The number of secret elements of the hypertree, `wotsInstanceCount · len + 2^h · k · 2^a`. -/
def slSecretCount : ℕ :=
  wotsInstanceCount vp.params * vp.params.len + targetCount vp.params .forsF

theorem length_slSecretList : (slSecretList vp).length = slSecretCount vp := by
  simp [slSecretList, slSecretCount]

variable {vp}

/-- Every secret read at a secret child of a ledger address is in `slSecretList` (VCVio's
`mem_secretChildren_of_inl_mem_childAdrs`, `HashSig.SLHDSA.Security.WeakKeyBound`). -/
theorem mem_slSecretList {a b : Adrs} (hb : b ∈ constructionAddresses vp)
    (h : .inl a ∈ childAdrs vp b) : a ∈ slSecretList vp := by
  rcases (mem_constructionAddresses_iff b).1 hb with hm | hm | hm | hm | hm | hm
  · obtain ⟨⟨⟨pos, tree⟩, j⟩, -, rfl⟩ := List.mem_map.1 hm
    rw [childAdrs_forsNodeAdrs_zero, List.mem_singleton, Sum.inl.injEq] at h
    subst h
    refine List.mem_append_right _ (List.mem_map.2 ⟨_, hm, ?_⟩)
    rw [forsNodeAdrs_eq, forsSkAdrs_eq, forsSkAdrs_eq]
  · obtain ⟨⟨_, z, j⟩, hmem, rfl⟩ := List.mem_map.1 hm
    rw [childAdrs_forsNodeAdrs vp (mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2).1]
      at h
    simp at h
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hm
    simp [childAdrs_forsPkAdrs] at h
  · obtain ⟨⟨c, ⟨t, ht⟩⟩, hmem, rfl⟩ := List.mem_map.1 hm
    simp only [wotsStepAdrs] at h
    rcases t with _ | t
    · rw [childAdrs_wotsChainAdrs_setHashAddress_zero, List.mem_singleton, Sum.inl.injEq] at h
      subst h
      exact List.mem_append_left _
        (List.mem_map.2 ⟨c, (List.mem_product.1 hmem).1, rfl⟩)
    · simp [childAdrs_wotsChainAdrs_setHashAddress_succ] at h
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hm
    simp [childAdrs_wotsPkAdrs] at h
  · obtain ⟨⟨_, z, j⟩, hmem, rfl⟩ := List.mem_map.1 hm
    have hz := (mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2).1
    rcases (by omega : z = 1 ∨ 1 < z) with rfl | hz1
    · simp [childAdrs_xmssNodeAdrs_one] at h
    · simp [childAdrs_xmssNodeAdrs vp hz1] at h

end SlSecrets


/-! ## Queries of `B_prf` -/

section Queries

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ : Type}

theorem aqs_map {α β : Type} {oa : OracleComp spec' α} {P : ι' → Prop} (f : α → β)
    (h : oa.AllQueriesSatisfy P) : (f <$> oa).AllQueriesSatisfy P := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind h fun _ => allQueriesSatisfy_pure _ _

/-- Every query of a stateful simulation satisfies `P` when every step's queries do. -/
theorem aqs_simulateQ_run (impl : QueryImpl spec (StateT σ (OracleComp spec'))) {P : ι' → Prop}
    (h : ∀ t s, ((impl t).run s).AllQueriesSatisfy P) {α : Type} :
    ∀ (oa : OracleComp spec α) (s : σ), ((simulateQ impl oa).run s).AllQueriesSatisfy P := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (h t s) fun p => ih p.1 p.2

end Queries

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

/-- **The inputs of `B_prf`** at `PK.seed = pk` for the structure `S`: the `SF_WOTS_C_PRF`
addresses of the anchors and chains, and the secret-key addresses of the hypertree. -/
noncomputable def prfInputs (S : Structure) (pk : pr.PkSeed) : Finset (pr.PkSeed × Adrs) :=
  (Finset.univ : Finset (SkIdx vp.params S)).image (fun i => (pk, sfPrfAdrs i)) ∪
    (slSecretList vp.sl).toFinset.image fun a => (pk, a)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
theorem card_prfInputs {S : Structure} (hS : S.TreeValid vp.params.hsf) (pk : pr.PkSeed) :
    (prfInputs pr S pk).card ≤ S.anchors.card * vp.params.lsf + slSecretCount vp.sl := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
      Structure.TreeValid.card_leafIds hS]
  · refine Finset.card_image_le.trans ?_
    rw [← length_slSecretList]
    exact List.toFinset_card_le _

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
theorem aqs_liftP {α : Type} (p : ProbComp α) (Ds : Finset (pr.PkSeed × Adrs)) :
    (liftM p : OracleComp (PrfSpec pr) α).AllQueriesSatisfy (InSet Ds) :=
  (isQueryBoundP_zero_iff _ _).1 ((isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
    rcases t with n | x
    · exact absurd trivial ht
    · rfl)

/-- The secret source of `B_prf`: one oracle query at `(PK.seed, ADRS)`. -/
abbrev secQ : pr.PkSeed × SecAdrs → OracleComp (PrfSpec pr) pr.Y :=
  fun x => PRFScheme.functionQuery (x.1, x.2.1)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] in
theorem aqs_guardSec (S : Structure) (pk : pr.PkSeed) (a b : Adrs)
    (hb : b ∈ constructionAddresses vp.sl) (hab : .inl a ∈ childAdrs vp.sl b) :
    (guardSec pr (secQ pr) pk a).AllQueriesSatisfy (InSet (prfInputs pr S pk)) := by
  unfold guardSec
  split
  · rw [secQ, PRFScheme.functionQuery, allQueriesSatisfy_query_iff]
    exact Finset.mem_union_right _ (Finset.mem_image.2
      ⟨a, List.mem_toFinset.2 (mem_slSecretList hb hab), rfl⟩)
  · exact allQueriesSatisfy_pure _ _

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] in
/-- The stateless key generation of `B_prf` queries only secret-key addresses of the
hypertree. -/
theorem aqs_slRootM (S : Structure) (pk : pr.PkSeed) :
    (slRootM pr (secQ pr) pk).AllQueriesSatisfy (InSet (prfInputs pr S pk)) := by
  exact @keygenInternalWithSecretM_pred_of_ledger _ _ _
    (fun {_} (oa : OracleComp (PrfSpec pr) _) => oa.AllQueriesSatisfy (InSet (prfInputs pr S pk)))
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
    _ pr.toSLHDSA.core _ (fun a b hb hab => aqs_guardSec pr S pk a b hb hab) (pubQ pr _) pk
    (fun _ _ _ => allQueriesSatisfy_pure _ _)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
/-- The stateless signer of `B_prf` queries only secret-key addresses of the hypertree. -/
theorem aqs_slSignM (S : Structure) (pk : pr.PkSeed) (skPrf : pr.SkPrf) (pkSl pkSf : pr.Y)
    (msg : Msg) :
    (slSignM pr Msg enc (secQ pr) (fun x => pure (pr.PRFmsg skPrf x)) pk pkSl pkSf
      msg).AllQueriesSatisfy (InSet (prfInputs pr S pk)) := by
  unfold slSignM
  refine allQueriesSatisfy_bind (aqs_liftP pr _ _) fun o => ?_
  rw [pure_bind]
  exact @signInternalWithSecretRandomizerM_pred_of_ledger _ _ _
    (fun {_} (oa : OracleComp (PrfSpec pr) _) => oa.AllQueriesSatisfy (InSet (prfInputs pr S pk)))
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
    _ pr.toSLHDSA.core _ (fun a b hb hab => aqs_guardSec pr S pk a b hb hab) (pubQ pr _) _ pk
    pkSl _ (fun _ _ _ => allQueriesSatisfy_pure _ _) (allQueriesSatisfy_pure _ _)

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
theorem aqs_roStepC (Ds : Finset (pr.PkSeed × Adrs)) (x : RoIn pr (BMsg pr Msg))
    (s : CSt pr Msg) :
    ((roStepC pr Msg x : StateT (CSt pr Msg) (OracleComp (PrfSpec pr)) pr.Digest).run
      s).AllQueriesSatisfy (InSet Ds) := by
  unfold roStepC
  simp only [StateT.run_mk]
  split
  · exact allQueriesSatisfy_pure _ _
  · exact aqs_map _ (aqs_liftP pr _ _)

omit [Fintype pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] in
/-- Every step of `B_prf`'s signing phase queries only inputs of `prfInputs`. -/
theorem aqs_implC (skPrf : pr.SkPrf) (K : Keys pr) (sk : LeafId → ℕ → pr.Y)
    (t : (advSpec pr Msg).Domain) (s : CSt pr Msg) :
    (((implC pr Msg enc (secQ pr) (fun x => pure (pr.PRFmsg skPrf x)) K sk) t).run
      s).AllQueriesSatisfy (InSet (prfInputs pr K.S K.pk)) := by
  have hlift : ∀ {α : Type} (X : OracleComp (PrfSpec pr) α),
      (liftM X : StateT (CSt pr Msg) (OracleComp (PrfSpec pr)) α).run s =
        (fun a => (a, s)) <$> X := fun X => by simp [StateT.run_monadLift]
  rcases t with (n | x) | q
  · simp only [implC, QueryImpl.add_apply_inl]
    rw [QueryImpl.liftTarget_apply]
    change ((StateT.lift (liftM _ : OracleComp (PrfSpec pr) _) :
      StateT (CSt pr Msg) (OracleComp (PrfSpec pr)) _).run s).AllQueriesSatisfy _
    rw [StateT.run_lift]
    exact allQueriesSatisfy_bind (aqs_liftP pr _ _) fun _ => allQueriesSatisfy_pure _ _
  · simp only [implC, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact aqs_roStepC pr Msg _ x s
  · simp only [implC, QueryImpl.add_apply_inr]
    unfold signStepC
    split
    · simp only [StateT.run_bind]
      rw [hlift]
      simp only [bind_map_left]
      exact allQueriesSatisfy_bind (aqs_slSignM pr Msg enc _ _ _ _ _ _)
        fun a => by simp [StateT.run_modify]
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp [StateT.run_modify]
      · simp only [StateT.run_bind]
        rw [hlift]
        simp only [map_pure, pure_bind]
        exact allQueriesSatisfy_bind (aqs_roStepC pr Msg _ _ s)
          fun a => by simp [StateT.run_modify]

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The signing phase of `B_prf` queries only inputs of `prfInputs`. -/
theorem aqs_phase2C {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (skPrf : pr.SkPrf) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (s : CSt pr Msg) :
    ((phase2C pr Msg enc A st K (secQ pr) (fun x => pure (pr.PRFmsg skPrf x)) sk).run
      s).AllQueriesSatisfy (InSet (prfInputs pr K.S K.pk)) := by
  unfold phase2C
  simp only [StateT.run_bind]
  refine allQueriesSatisfy_bind (aqs_simulateQ_run _ (aqs_implC pr Msg enc skPrf K sk) _ s)
    fun z => allQueriesSatisfy_bind ?_ fun _ => by simp
  rcases z with ⟨⟨m, σ⟩, s'⟩
  cases σ with
  | stateless σ' => exact allQueriesSatisfy_pure _ _
  | stateful z i R σt =>
    simp only [verifyC, StateT.run_bind]
    exact allQueriesSatisfy_bind (aqs_roStepC pr Msg _ _ _) fun _ => allQueriesSatisfy_pure _ _

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
theorem aqs_tableList {T R : Type} [DecidableEq T] [Inhabited R]
    (q : T → OracleComp (PrfSpec pr) R) {P : ℕ ⊕ (pr.PkSeed × Adrs) → Prop}
    (h : ∀ t, (q t).AllQueriesSatisfy P) : ∀ l : List T, (tableList q l).AllQueriesSatisfy P
  | [] => allQueriesSatisfy_pure _ _
  | t :: ts => allQueriesSatisfy_bind (h t) fun _ =>
      allQueriesSatisfy_bind (aqs_tableList q h ts) fun _ => allQueriesSatisfy_pure _ _

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **`B_prf` makes at most `q₁ = L · lsf + slSecretCount` distinct queries**: the cached
reduction `cacheAdv (Bprf A)` queries only the inputs of `prfInputs`, each at most once. -/
theorem cacheAdv_Bprf_bound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    (cacheAdv (Bprf pr Msg enc A.toShrincsAdversary)).IsQueryBoundP Notions.IsPRFQuery
      (L * vp.params.lsf + slSecretCount vp.sl) := by
  have hlift : ∀ {α : Type} (p : ProbComp α) (k : α → OracleComp (PrfSpec pr) Bool),
      (simulateQ CachedPRF.cacheImpl ((liftM p : OracleComp (PrfSpec pr) α) >>= k)).run ∅ =
        (liftM p : OracleComp (PrfSpec pr) α) >>= fun x =>
          (simulateQ CachedPRF.cacheImpl (k x)).run ∅ := fun p k => by
    rw [simulateQ_bind, StateT.run_bind, CachedPRF.cacheImpl_liftM_run, bind_map_left]
  have hzero : ∀ {α : Type} (p : ProbComp α),
      (liftM p : OracleComp (PrfSpec pr) α).IsQueryBoundP Notions.IsPRFQuery 0 := fun p =>
    (isQueryBoundP_liftM_isRight p).of_imp fun t ht => by
      rcases t with n | x
      · exact absurd ht (by simp [Notions.IsPRFQuery])
      · rfl
  rw [cacheAdv, StateT.run'_eq, isQueryBoundP_map_iff, Bprf, hlift]
  refine (isQueryBoundP_bind (n := 0) (m := L * vp.params.lsf + slSecretCount vp.sl) (hzero _)
    fun z hz => ?_).mono (by omega)
  have hz1 : z ∈ support (stage1S pr Msg enc A.toShrincsAdversary) :=
    mem_support_of_mem_support_liftComp (spec := unifSpec) _ _ _ hz
  have hz' : z.1 ∈ support A.chooseShape :=
    mem_support_of_mem_support_simulateQ_run _ _ _ hz1
  split
  · exact trivial
  rename_i hv
  have hS : z.1.1.TreeValid vp.params.hsf := (not_not.1 hv).toTreeValid
  rw [hlift]
  refine (isQueryBoundP_bind (n := 0) (m := L * vp.params.lsf + slSecretCount vp.sl) (hzero _)
    fun pk _ => ?_).mono (by omega)
  rw [hlift]
  refine (isQueryBoundP_bind (n := 0) (m := L * vp.params.lsf + slSecretCount vp.sl) (hzero _)
    fun skPrf _ => ?_).mono (by omega)
  refine (CachedPRF.cache_run_bound (prfInputs pr z.1.1 pk) _ ∅ ?_).mono ?_
  · refine allQueriesSatisfy_bind (aqs_tableList pr _ (fun i => ?_) _) fun f =>
      allQueriesSatisfy_bind (aqs_slRootM pr z.1.1 pk) fun pkSl =>
        aqs_map _ (aqs_phase2C pr Msg enc A.toShrincsAdversary _ skPrf _ _ _)
    rw [PRFScheme.functionQuery, allQueriesSatisfy_query_iff]
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  · have h1 : CachedPRF.fresh (prfInputs pr z.1.1 pk)
        (∅ : CachedPRF.Cache (pr.PkSeed × Adrs) pr.Y) =
        prfInputs pr z.1.1 pk := by
      ext; simp [CachedPRF.fresh]
    rw [h1]
    refine (card_prfInputs pr hS pk).trans (Nat.add_le_add_right ?_ _)
    exact Nat.mul_le_mul_right _ (A.anchors_le z.1 hz' hS)

/-- **`B_prf` as an adversary of Definition 4.3** with the budget
`q₁ = L · lsf + slSecretCount`: the cached reduction. -/
noncomputable def BprfAdv {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.PRFAdversary (pr.PkSeed × Adrs) pr.Y (L * vp.params.lsf + slSecretCount vp.sl) where
  run := cacheAdv (Bprf pr Msg enc A.toShrincsAdversary)
  queryBound := cacheAdv_Bprf_bound pr Msg enc A

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- The budgeted `B_prf` has the advantage of `Bprf`. -/
theorem prfAdv_BprfAdv {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) =
      (Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A.toShrincsAdversary) :=
  CachedPRF.prfAdvantage_cacheAdv _ _

end ShrincsSecurity.Shrincs

end
