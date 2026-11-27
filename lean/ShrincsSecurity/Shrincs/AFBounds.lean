module

public import ShrincsSecurity.Shrincs.Wrapper

/-!
# The FXMSS forger `A_F` of a SHRINCS forger, as a forger of Theorem 4.2

`SHRINCS-Security-Analysis.pdf`, Section 4.8 (txt lines 4085–4095): "With the stateless path
added, `GAME.4` is `F.2⁺` played by the forger `A_F` that runs `A` …". `AF` packages `forgeExt`
(`Wrapper.lean`) as an FXMSS EU-CMA adversary (Definition 4.16) and as a forger of Theorem 4.2
(`Fxmss.Rom.Forger`), so that the reductions `B₀ … B₈` of Section 4.7 apply to it: they are the
**augmented reductions** of Section 4.8, which simulate the stateless path with uniform secrets
inside `A_F`.

* `A_F` makes at most `q_s` FXMSS signing queries (one per stateful signing query of `A`, none for
  a stateless one): `forgeExt_signBound`.
* `A_F` makes exactly `A`'s queries to `H_msg^sf` (the stateless path evaluates none):
  `forgeExt_roBound`.
* `A_F` commits to `A`'s structure.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys IsRoQuery')

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)

namespace AFBounds

/-! ## Query bounds of lifted computations -/

/-- A query bound transported along an oracle-spec inclusion: a `p`-query of the lifted program
is the image of a `p'`-query of the original one. -/
theorem isQueryBoundP_liftComp {ι τ α : Type} {spec : OracleSpec ι} {sup : OracleSpec τ}
    [h : spec ⊂ₒ sup] {p' : ι → Prop} {p : τ → Prop} [DecidablePred p] [DecidablePred p']
    (hp : ∀ t, p (h.onQuery t) → p' t) {oa : OracleComp spec α} {n : ℕ}
    (hoa : oa.IsQueryBoundP p' n) : (liftComp oa sup).IsQueryBoundP p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rw [liftM_eq_liftM_liftM]
    rw [show (liftM (spec.query t) : OracleQuery sup (spec.Range t)) =
        ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _, liftM_eq_map_query]
    change IsQueryBoundP (h.onResponse t <$>
      (liftM (OracleSpec.query (h.onQuery t)) : OracleComp sup _) >>= _) p n
    rw [bind_map_left, isQueryBoundP_query_bind_iff]
    refine ⟨hoa.1.imp (fun h1 h2 => h1 (hp t h2)) id, fun u => ?_⟩
    refine (ih _ (hoa.2 _)).mono ?_
    by_cases h1 : p (h.onQuery t) <;> by_cases h2 : p' t <;> simp [h1, h2]
    · exact absurd (hp t h1) h2

/-- The query indices of `A_F`'s oracles. -/
abbrev FIdx : Type := (ℕ ⊕ Fxmss.Rom.RoIn pr (BMsg pr Msg)) ⊕ (BMsg pr Msg × LeafId)

/-- A `ProbComp` lifted to `A_F`'s oracles makes no query other than coins. -/
theorem liftM_bound {α : Type} (oa : ProbComp α) (p : FIdx pr Msg → Prop) [DecidablePred p]
    (hp : ∀ n, ¬ p (.inl (.inl n))) :
    (liftM oa : OracleComp (FSpec pr Msg) α).IsQueryBoundP p 0 := by
  refine isQueryBoundP_liftComp (p' := fun t => t.isRight) ?_
    (isQueryBoundP_liftComp (p' := fun _ : ℕ => False) ?_ (isQueryBoundP_false _ 0))
  · rintro (n | x)
    · exact fun h => absurd h (hp n)
    · simp
  · intro t h
    change Sum.isRight (Sum.inl t : ℕ ⊕ _) = true at h
    simp at h

/-- A `ProbComp` lifted to a state over `A_F`'s oracles makes no query other than coins. -/
theorem liftM_stateT_bound {α σ : Type} (oa : ProbComp α) (p : FIdx pr Msg → Prop)
    [DecidablePred p] (hp : ∀ n, ¬ p (.inl (.inl n))) (s : σ) :
    ((liftM oa : StateT σ (OracleComp (FSpec pr Msg)) α).run s).IsQueryBoundP p 0 := by
  refine isQueryBoundP_liftComp (p' := fun t => t.isRight) ?_
    (isQueryBoundP_liftComp (p' := fun _ : ℕ => False) ?_ (isQueryBoundP_false _ 0))
  · rintro (n | x)
    · exact fun h => absurd h (hp n)
    · simp
  · intro t h
    change Sum.isRight (Sum.inl t : ℕ ⊕ _) = true at h
    simp at h

/-- A forwarded query makes exactly that query. -/
theorem fwd_bound {σ : Type} (t : FIdx pr Msg) (s : σ) (p : FIdx pr Msg → Prop)
    [DecidablePred p] (n : ℕ) (hn : p t → 0 < n) :
    ((liftM ((FSpec pr Msg).query t) : StateT σ (OracleComp (FSpec pr Msg)) _).run
      s).IsQueryBoundP p n := by
  simpa using hn

end AFBounds

open AFBounds

variable [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed]
  [SampleableType pr.SkPrf] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg]

namespace AFBounds

omit [Fintype pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- `A_F`'s answer to a signing query makes at most one query, an FXMSS signing query (a stateful
query), besides coins (the stateless signer is a lifted `ProbComp`). -/
theorem signAF_bound (K : Keys pr) (q : Msg × Bool) (s : AFSt pr Msg)
    (p : FIdx pr Msg → Prop) [DecidablePred p] (hp : ∀ n, ¬ p (.inl (.inl n))) (n : ℕ)
    (hn : ∀ x, p (.inr x) → 0 < n) :
    ((signAF pr Msg enc K q).run s).IsQueryBoundP p n := by
  unfold signAF
  rcases q with ⟨m, _ | _⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.false_eq_true, ↓reduceIte]
    cases K.S.leafSelect s.ctr with
    | none => simp
    | some v => simpa using hn _
  · simp
    exact (liftM_stateT_bound pr Msg _ p hp s).mono (Nat.zero_le _)

omit [Fintype pr.Y] [SampleableType pr.PkSeed] [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- One step of `implAF`: coins are free, a random-oracle query is forwarded as one, a signing
query costs at most one FXMSS signing query. -/
theorem implAF_step (K : Keys pr)
    (P : (ℕ ⊕ Fxmss.Rom.RoIn pr (BMsg pr Msg)) ⊕ (Msg × Bool) → Prop) [DecidablePred P]
    (p : FIdx pr Msg → Prop) [DecidablePred p] (hp : ∀ n, ¬ p (.inl (.inl n)))
    (hro : ∀ x, p (.inl (.inr x)) → P (.inl (.inr x)))
    (hsign : ∀ q x, p (.inr x) → P (.inr q)) (t) (s : AFSt pr Msg) :
    ((implAF pr Msg enc K t).run s).IsQueryBoundP p (if P t then 1 else 0) := by
  rcases t with (n | x) | q
  · exact fwd_bound pr Msg _ s p _ (fun h => absurd h (hp n))
  · exact fwd_bound pr Msg _ s p _ (fun h => by simp [hro x h])
  · exact signAF_bound pr Msg enc K q s p hp _ (fun x h => by simp [hsign q x h])

end AFBounds

omit [Fintype pr.Y] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- `A_F` makes at most `q_s` FXMSS signing queries: one per stateful signing query of `A`. -/
theorem forgeExt_signBound {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : A.State) (S : Structure) (pk : Fxmss.Rom.PK pr) :
    (forgeExt pr Msg enc A st S pk).IsQueryBoundP Notions.IsSignQuery qs := by
  unfold forgeExt
  refine (isQueryBoundP_bind (n := 0) (m := qs) (liftM_bound pr Msg _ _ (fun _ h => h))
    fun r _ => ?_).mono (by omega)
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (A.signBound st S _)
    (implAF_step pr Msg enc _ Notions.IsSignQuery Notions.IsSignQuery (fun _ h => h)
      (fun _ h => h) (fun _ _ _ => trivial)) _

omit [Fintype pr.Y] [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- `A_F` makes exactly `A`'s signing-phase queries to `H_msg^sf`. -/
theorem forgeExt_roBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    (st : A.State) (S : Structure) (pk : Fxmss.Rom.PK pr) :
    (forgeExt pr Msg enc A.toShrincsAdversary st S pk).IsQueryBoundP
      (IsRoQuery' pr (BMsg pr Msg)) qh₂ := by
  unfold forgeExt
  refine (isQueryBoundP_bind (n := 0) (m := qh₂) (liftM_bound pr Msg _ _ (fun _ h => h))
    fun r _ => ?_).mono (by omega)
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (A.roBound₂ st S _)
    (implAF_step pr Msg enc _ (IsRoQueryS pr Msg) (IsRoQuery' pr (BMsg pr Msg)) (fun _ h => h)
      (fun _ _ => trivial) (fun _ _ h => h)) _

/-- **`A_F` as an FXMSS EU-CMA adversary** (Definition 4.16) with `q_s` signing queries. -/
noncomputable def AFAdv {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Notions.FxmssAdversary (Fxmss.Rom.scheme pr (BMsg pr Msg) (slKeygenS pr)) qs where
  State := A.State
  chooseShape := A.chooseShape
  forge st S pk := Prod.fst <$> forgeExt pr Msg enc A st S pk
  signBound st S pk := by
    rw [isQueryBoundP_map_iff]
    exact forgeExt_signBound pr Msg enc A st S pk

/-- **`A_F` as a forger of Theorem 4.2**: `q_s` signing queries, `A`'s random-oracle queries, and
`A`'s structures (at most `L` anchors). -/
noncomputable def AF {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Fxmss.Rom.Forger pr (BMsg pr Msg) (slKeygenS pr) qs qh₁ qh₂ L where
  toFxmssAdversary := AFAdv pr Msg enc A.toShrincsAdversary
  roBound₁ := A.roBound₁
  roBound₂ st S pk := by
    change (Prod.fst <$> forgeExt pr Msg enc A.toShrincsAdversary st S pk).IsQueryBoundP _ _
    rw [isQueryBoundP_map_iff]
    exact forgeExt_roBound pr Msg enc A st S pk
  anchors_le := A.anchors_le

end ShrincsSecurity.Shrincs

end
