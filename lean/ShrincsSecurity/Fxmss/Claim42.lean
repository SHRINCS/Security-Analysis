module

public import ShrincsSecurity.Fxmss.Events
public import ShrincsSecurity.Fxmss.Lift
public import ShrincsSecurity.Repro.Lazy

/-!
# Claim 4.2: `F.1 → F.2`, adaptive reprogramming of `H_msg^sf`

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.2** and **Algorithm 5** (txt lines
3270–3365).

The distinguisher `B1` plays `DI-Repro_b` (Definition C.2) with `X₁ = Y` (the randomizers `R`),
`X₂ = (PK.seed, PK.sf, idx, M)` and `Y = {0,1}^{2n}`: the random oracle `H_msg^sf` of the games is
literally the oracle `O_b` (`roSpec = Repro.HashSpec`), so the forger's queries are forwarded
unchanged. A signing query at an unused anchor calls `R ← Reprogram(x₂)`, queries
`y ← O_b(R, x₂)` and signs `y`; `B1` outputs `1` exactly when the forger wins `F.1` (wins and the
abort event `C₁` of `F.1` does not occur).

**Proof.** Both worlds are run lazily (`Repro.diExperiment_evalDistEq_lazy`). Projecting the lazy
state onto its table (the random-oracle cache of the games) and `B1`'s state onto the signing
records, world `0` is `gameG` (`F.0`, whose `Win ∧ ¬C₁` is the success of `F.1`) and world `1` is
`gameG2` (`F.2`, lazily): `Reprogram` samples a pair `(R, y)`; world `0` discards `y` and the hash
query reads (or samples) the honest value, world `1` discards the recorded cell, so that the hash
query samples a fresh digest and programs it (`freshProgStep`). The guard of Definition C.2 never
fires: signing queries name pairwise distinct anchors, and distinct anchors of a valid structure
have distinct `idx` (`toIdx_inj`). The projection is an equality of distributions on the output
bit (`map_run_nested_evalDistEq`), gated by this invariant.

**Query counts.** `B1` makes at most `q_{h,1} + q_{h,2} + L + 1` hash queries (the forwarded
queries, one per answered signing query, one verification) and at most `L` reprogramming calls
(one per answered signing query, each consuming an anchor, `|A| ≤ L`). The paper counts
`q_s + q_h + 1` hash queries and `q_s` calls; with the completion of Remark 4.6 inside the games
`q_s` is replaced by the number `L` of anchors.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

namespace Claim42

/-! ## Generic: a nested simulation projected onto a flat one -/

section Generic

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α BS LS GS : Type}

/-- **Nested simulation through a state projection, in distribution.** A handler `implB` of
`spec` in terms of `spec'` (with state `BS`), run under a handler `implL` of `spec'` (state `LS`),
projects onto a flat handler `implG` (state `GS`) through `proj : LS → BS → GS`, if every step
does so in distribution while the invariant `inv` holds, and `inv` is preserved. -/
theorem map_run_nested_evalDistEq
    (implB : QueryImpl spec (StateT BS (OracleComp spec')))
    (implL : QueryImpl spec' (StateT LS ProbComp))
    (implG : QueryImpl spec (StateT GS ProbComp))
    (proj : LS → BS → GS) (inv : LS → BS → Prop)
    (hinv : ∀ t ls bs, inv ls bs → ∀ z ∈ support ((simulateQ implL ((implB t).run bs)).run ls),
      inv z.2 z.1.2)
    (hstep : ∀ t ls bs, inv ls bs →
      (fun z : (spec.Range t × BS) × LS => (z.1.1, proj z.2 z.1.2)) <$>
          (simulateQ implL ((implB t).run bs)).run ls =ᵈ (implG t).run (proj ls bs))
    (oa : OracleComp spec α) (ls : LS) (bs : BS) (h : inv ls bs) :
    (fun z : (α × BS) × LS => (z.1.1, proj z.2 z.1.2)) <$>
        (simulateQ implL ((simulateQ implB oa).run bs)).run ls =ᵈ
      (simulateQ implG oa).run (proj ls bs) := by
  induction oa using OracleComp.inductionOn generalizing ls bs with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    calc ((simulateQ implL ((implB t).run bs)).run ls >>= fun z =>
          (fun w : (α × BS) × LS => (w.1.1, proj w.2 w.1.2)) <$>
            (simulateQ implL ((simulateQ implB (k z.1.1)).run z.1.2)).run z.2)
        =ᵈ ((simulateQ implL ((implB t).run bs)).run ls >>= fun z =>
            (simulateQ implG (k z.1.1)).run (proj z.2 z.1.2)) :=
          EvalDistEq.bind_congr_of_support _ fun z hz =>
            ih z.1.1 z.2 z.1.2 (hinv t ls bs h z hz)
      _ = (((fun z : (spec.Range t × BS) × LS => (z.1.1, proj z.2 z.1.2)) <$>
            (simulateQ implL ((implB t).run bs)).run ls) >>= fun z =>
            (simulateQ implG (k z.1)).run z.2) := by rw [bind_map_left]
      _ =ᵈ ((implG t).run (proj ls bs) >>= fun z => (simulateQ implG (k z.1)).run z.2) :=
          EvalDistEq.bind_left (hstep t ls bs h) _

/-- Equal computations are equal in distribution. -/
theorem evalDistEq_of_eq {α : Type} {mx my : ProbComp α} (h : mx = my) : mx =ᵈ my :=
  h ▸ EvalDistEq.rfl

/-- **Query bound through a stateful simulation with a potential.** If each simulated step of a
`p`-query costs at most one `q`-query plus the decrease of the potential `φ` (and a step of any
other query costs at most the decrease of `φ`), the simulation of a program with at most `n`
`p`-queries makes at most `n + φ s` `q`-queries. -/
theorem isQueryBoundP_run_potential {p : ι → Prop} [DecidablePred p] {q : ι' → Prop}
    [DecidablePred q] {σ : Type} (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (φ : σ → ℕ)
    (hstep : ∀ (t : ι) (s : σ) {β : Type} (m : ℕ) (k : spec.Range t × σ → OracleComp spec' β),
      (∀ z ∈ support ((impl t).run s), IsQueryBoundP (k z) q (m + φ z.2)) →
      IsQueryBoundP ((impl t).run s >>= k) q ((if p t then 1 else 0) + m + φ s))
    {oa : OracleComp spec α} {n : ℕ} (h : IsQueryBoundP oa p n) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q (n + φ s) := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, StateT.run_bind]
    have := hstep t s (if p t then n - 1 else n) _ fun z _ => ih z.1 (h.2 z.1) z.2
    refine this.mono ?_
    by_cases hp : p t
    · have := h.1.resolve_left (not_not.2 hp)
      simp only [hp, ↓reduceIte]; omega
    · simp [hp]

end Generic

end Claim42

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

namespace Claim42

/-! ## The distinguisher `B₁` (Algorithm 5) -/

/-- The oracles of a `DI-Repro` distinguisher for `H_msg^sf`. -/
abbrev DSpec : OracleSpec (ℕ ⊕ ((RoIn pr Msg) ⊕ X2 pr Msg)) :=
  Repro.DIAdvSpec pr.Y (X2 pr Msg) pr.Digest

/-- `B₁` forwards the forger's private coins and its queries to `H_msg^sf` (to `O_b`). -/
def fwd : QueryImpl (spec pr Msg) (OracleComp (DSpec pr Msg))
  | .inl n => liftM ((DSpec pr Msg).query (.inl n))
  | .inr x => liftM ((DSpec pr Msg).query (.inr (.inl x)))

/-- `B₁`'s signing oracle (Algorithm 5, lines 6–11): at an unused anchor, `R ← Reprogram(x₂)`,
`y ← O_b(R, x₂)`, and the FXMSS signature of `y`; the records are kept as in the games. A refused
call (never happens) is answered with `R = default`. -/
noncomputable def signB (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId) :
    StateT (St pr Msg) (OracleComp (DSpec pr Msg)) (Option (Sig pr)) := do
  let s ← get
  if q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used then
    let x₂ : X2 pr Msg := (K.pk, K.pkSf, toIdx q.2, q.1)
    let oR ← (liftM ((DSpec pr Msg).query (.inr (.inr x₂))) :
      StateT (St pr Msg) (OracleComp (DSpec pr Msg)) (Option pr.Y))
    let R := oR.getD default
    let md ← (liftM ((DSpec pr Msg).query (.inr (.inl (R, x₂)))) :
      StateT (St pr Msg) (OracleComp (DSpec pr Msg)) pr.Digest)
    modify fun s => { s with
      used := s.used ++ [q.2]
      log := s.log ++ [q.1]
      recs := Function.update s.recs q.2
        (some ⟨q.1, R, md, Scheme.Fxmss.sign pr K.S K.pk sk md q.2⟩) }
    return some (R, Scheme.Fxmss.sign pr K.S K.pk sk md q.2)
  else
    modify fun s => { s with log := s.log ++ [q.1] }
    return none

/-- `B₁`'s handler of the signing phase (its state keeps the records; its `cache` is unused). -/
noncomputable def implB (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) (OracleComp (DSpec pr Msg)))
  | .inl t => liftM (fwd pr Msg t)
  | .inr q => signB pr Msg K sk q

/-- `B₁` after the structure phase (Algorithm 5, lines 3–17): key generation, the signing phase
with signing queries answered through `Reprogram`, and the output bit `Win ∧ ¬C₁`. -/
noncomputable def B1cont {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (pk : pr.PkSeed) (z : Structure × A.State) : OracleComp (DSpec pr Msg) Bool :=
  if ¬ z.1.TreeValid P.hsf then return false else do
  let f ← (liftM ($ᵗ (SkIdx P z.1 → pr.Y) : ProbComp _) : OracleComp (DSpec pr Msg) _)
  let pkSl ← (liftM (slKeygen pk) : OracleComp (DSpec pr Msg) pr.Y)
  let sk := skOf pr z.1 f
  let K : Keys pr := ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk sk⟩
  let r ← (simulateQ (implB pr Msg K sk) (stage2Prog pr Msg slKeygen A z.2 K)).run
    (St.init pr Msg ∅)
  return decide (WinNotC1 (some (Transcript.ofRun pr Msg K r)))

/-- The run of `B₁` (Algorithm 5): `PK.seed ←$`, the structure phase `A₁` with its queries
forwarded, then `B1cont`. -/
noncomputable def B1run {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    OracleComp (DSpec pr Msg) Bool := do
  let pk ← (liftM ($ᵗ pr.PkSeed : ProbComp pr.PkSeed) : OracleComp (DSpec pr Msg) pr.PkSeed)
  let z ← simulateQ (fwd pr Msg) A.chooseShape
  B1cont pr Msg slKeygen A pk z

/-! ## Unfolding `B₁`'s steps -/

section Steps

variable {pr Msg}

/-- The second input `x₂ = (PK.seed, PK.sf, idx, M)` of a signing query. -/
def x2Of (K : Keys pr) (q : Msg × LeafId) : X2 pr Msg := (K.pk, K.pkSf, toIdx q.2, q.1)

/-- The state after an answered signing query. -/
def stSign (s : St pr Msg) (q : Msg × LeafId) (R : pr.Y) (md : pr.Digest)
    (σ : Option (Scheme.Fxmss.Sig pr)) : St pr Msg :=
  { s with
    used := s.used ++ [q.2]
    log := s.log ++ [q.1]
    recs := Function.update s.recs q.2 (some ⟨q.1, R, md, σ⟩) }

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
theorem signB_run_fresh (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (s : St pr Msg) (h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used) :
    (signB pr Msg K sk q).run s =
      (liftM ((DSpec pr Msg).query (.inr (.inr (x2Of K q)))) : OracleComp _ (Option pr.Y)) >>=
        fun oR => (liftM ((DSpec pr Msg).query (.inr (.inl (oR.getD default, x2Of K q)))) :
          OracleComp _ pr.Digest) >>= fun md =>
        pure (some (oR.getD default, Scheme.Fxmss.sign pr K.S K.pk sk md q.2),
          stSign s q (oR.getD default) md (Scheme.Fxmss.sign pr K.S K.pk sk md q.2)) := by
  simp [signB, h, x2Of, stSign]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
theorem signB_run_else (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (s : St pr Msg) (h : ¬ (q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used)) :
    (signB pr Msg K sk q).run s = pure (none, { s with log := s.log ++ [q.1] }) := by
  simp only [signB, StateT.run_bind, StateT.run_get, pure_bind]
  rw [ite_eq_right h]
  simp

end Steps

/-! ## Query counts of `B₁` -/

section Bounds

variable {pr Msg}

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
/-- A lifted `ProbComp` makes no hash query and no reprogramming call. -/
theorem liftM_bound {α : Type} (oa : ProbComp α) (p : ℕ ⊕ ((RoIn pr Msg) ⊕ X2 pr Msg) → Prop)
    [DecidablePred p] (hp : ∀ n, ¬ p (.inl n)) :
    (liftM oa : OracleComp (DSpec pr Msg) α).IsQueryBoundP p 0 :=
  (isQueryBoundP_liftM_isRight oa).of_imp fun t ht => by
    rcases t with n | _
    · exact absurd ht (hp n)
    · rfl

/-- A query-free prefix does not change the bound. -/
theorem isQueryBoundP_zero_bind {ι : Type} {spec : OracleSpec ι} {α β : Type} {p : ι → Prop}
    [DecidablePred p] {oa : OracleComp spec α} {ob : α → OracleComp spec β} {m : ℕ}
    (h : oa.IsQueryBoundP p 0) (h' : ∀ x ∈ support oa, (ob x).IsQueryBoundP p m) :
    (oa >>= ob).IsQueryBoundP p m := by
  simpa using isQueryBoundP_bind h h'

/-- The number of unused anchors, the potential of the signing phase. -/
noncomputable def unusedCount (K : Keys pr) (s : St pr Msg) : ℕ :=
  ((leafIds P.hsf K.S).filter (· ∉ s.used)).card

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
theorem unusedCount_sign (K : Keys pr) (s : St pr Msg) (q : Msg × LeafId) (R : pr.Y)
    (md : pr.Digest) (σ : Option (Scheme.Fxmss.Sig pr))
    (h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used) :
    unusedCount K (stSign s q R md σ) + 1 = unusedCount K s := by
  unfold unusedCount stSign
  have : (leafIds P.hsf K.S).filter (· ∉ s.used ++ [q.2]) =
      ((leafIds P.hsf K.S).filter (· ∉ s.used)).erase q.2 := by
    ext x
    simp only [Finset.mem_filter, List.mem_append, List.mem_singleton, Finset.mem_erase]
    tauto
  simp only [this]
  exact Finset.card_erase_add_one (Finset.mem_filter.2 h)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
theorem unusedCount_log (K : Keys pr) (s : St pr Msg) (M : Msg) :
    unusedCount K { s with log := s.log ++ [M] } = unusedCount K s := rfl

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
/-- Hash queries of `B₁`'s signing phase: one per forwarded query to `H_msg^sf`, one per
answered signing query (charged to the potential). -/
theorem implB_hash_step (K : Keys pr) (sk : LeafId → ℕ → pr.Y)
    (t : (fullSpec pr Msg).Domain) (s : St pr Msg) {β : Type} (m : ℕ)
    (k : (fullSpec pr Msg).Range t × St pr Msg → OracleComp (DSpec pr Msg) β)
    (hk : ∀ z ∈ support ((implB pr Msg K sk t).run s),
      IsQueryBoundP (k z) (Repro.IsHashQuery pr.Y (X2 pr Msg)) (m + unusedCount K z.2)) :
    IsQueryBoundP ((implB pr Msg K sk t).run s >>= k) (Repro.IsHashQuery pr.Y (X2 pr Msg))
      ((if IsRoQuery' pr Msg t then 1 else 0) + m + unusedCount K s) := by
  rcases t with (n | x) | q
  · simp only [implB, fwd, StateT.run_monadLift, bind_assoc, pure_bind] at hk ⊢
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [Repro.IsHashQuery], fun u => ?_⟩
    refine (hk (u, s) (by simp)).mono ?_
    simp [IsRoQuery', Repro.IsHashQuery]
  · simp only [implB, fwd, StateT.run_monadLift, bind_assoc, pure_bind] at hk ⊢
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2
      ⟨by simp [IsRoQuery', Repro.IsHashQuery], fun u => ?_⟩
    refine (hk (u, s) (by simp)).mono ?_
    simp [IsRoQuery', Repro.IsHashQuery]; omega
  · by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
    · simp only [implB, signB_run_fresh K sk q s h, bind_assoc, pure_bind] at hk ⊢
      have hc := unusedCount_sign K s q
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [Repro.IsHashQuery], fun oR => ?_⟩
      have h0 := hc default default none h
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2
        ⟨by simp [IsRoQuery', Repro.IsHashQuery]; omega, fun md => ?_⟩
      have h1 := hc (oR.getD default) md (Scheme.Fxmss.sign pr K.S K.pk sk md q.2) h
      have hz := hk (some (oR.getD default, Scheme.Fxmss.sign pr K.S K.pk sk md q.2),
          stSign s q (oR.getD default) md (Scheme.Fxmss.sign pr K.S K.pk sk md q.2))
        ((mem_support_bind_iff _ _ _).2 ⟨oR, by simp,
          (mem_support_bind_iff _ _ _).2 ⟨md, by simp, by simp⟩⟩)
      refine hz.mono ?_
      simp [IsRoQuery', Repro.IsHashQuery]; omega
    · simp only [implB, signB_run_else K sk q s h] at hk ⊢
      rw [pure_bind]
      refine (hk _ (by simp)).mono ?_
      simp [IsRoQuery', unusedCount_log]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
/-- Reprogramming calls of `B₁`'s signing phase: one per answered signing query (charged to the
potential). -/
theorem implB_repro_step (K : Keys pr) (sk : LeafId → ℕ → pr.Y)
    (t : (fullSpec pr Msg).Domain) (s : St pr Msg) {β : Type} (m : ℕ)
    (k : (fullSpec pr Msg).Range t × St pr Msg → OracleComp (DSpec pr Msg) β)
    (hk : ∀ z ∈ support ((implB pr Msg K sk t).run s),
      IsQueryBoundP (k z) (Repro.IsReproQuery pr.Y (X2 pr Msg)) (m + unusedCount K z.2)) :
    IsQueryBoundP ((implB pr Msg K sk t).run s >>= k) (Repro.IsReproQuery pr.Y (X2 pr Msg))
      ((if (fun _ => False) t then 1 else 0) + m + unusedCount K s) := by
  rcases t with (n | x) | q
  · simp only [implB, fwd, StateT.run_monadLift, bind_assoc, pure_bind] at hk ⊢
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [Repro.IsReproQuery], fun u => ?_⟩
    refine (hk (u, s) (by simp)).mono ?_
    simp [Repro.IsReproQuery]
  · simp only [implB, fwd, StateT.run_monadLift, bind_assoc, pure_bind] at hk ⊢
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [Repro.IsReproQuery], fun u => ?_⟩
    refine (hk (u, s) (by simp)).mono ?_
    simp [Repro.IsReproQuery]
  · by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
    · simp only [implB, signB_run_fresh K sk q s h, bind_assoc, pure_bind] at hk ⊢
      have hc := unusedCount_sign K s q
      have h0 := hc default default none h
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2
        ⟨by simp [Repro.IsReproQuery]; omega, fun oR => ?_⟩
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [Repro.IsReproQuery], fun md => ?_⟩
      have h1 := hc (oR.getD default) md (Scheme.Fxmss.sign pr K.S K.pk sk md q.2) h
      have hz := hk (some (oR.getD default, Scheme.Fxmss.sign pr K.S K.pk sk md q.2),
          stSign s q (oR.getD default) md (Scheme.Fxmss.sign pr K.S K.pk sk md q.2))
        ((mem_support_bind_iff _ _ _).2 ⟨oR, by simp,
          (mem_support_bind_iff _ _ _).2 ⟨md, by simp, by simp⟩⟩)
      refine hz.mono ?_
      simp [Repro.IsReproQuery]; omega
    · simp only [implB, signB_run_else K sk q s h] at hk ⊢
      rw [pure_bind]
      refine (hk _ (by simp)).mono ?_
      simp [unusedCount_log]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
/-- The completion of Remark 4.6 makes no query to `H_msg^sf`. -/
theorem completion_roBound (M : Msg) (ids : List LeafId) :
    (completion pr Msg M ids).IsQueryBoundP (IsRoQuery' pr Msg) 0 := by
  induction ids with
  | nil => simp [completion]
  | cons id ids ih =>
    simp only [completion]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [IsRoQuery']),
      fun _ => by simpa [IsRoQuery'] using ih⟩

omit [Fintype pr.Y] [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg]
  [DecidableEq Msg] in
/-- The signing phase makes at most `q_{h,2} + 1` queries to `H_msg^sf`. -/
theorem stage2Prog_roBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (st : A.State) (K : Keys pr) :
    (stage2Prog pr Msg slKeygen A.toFxmssAdversary st K).IsQueryBoundP (IsRoQuery' pr Msg)
      (qh₂ + 1) := by
  unfold stage2Prog
  refine isQueryBoundP_bind (A.roBound₂ st K.S K.toPK) fun out _ => ?_
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr (by omega), fun _ => ?_⟩
  simp only [IsRoQuery', ↓reduceIte, Nat.sub_self]
  simpa using completion_roBound (otherMsg Msg out.1) (anchorList P K.S)

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  in
/-- The unused anchors at the start of the signing phase are the anchors. -/
theorem unusedCount_init (K : Keys pr) (c : (roSpec pr Msg).QueryCache) :
    unusedCount K (St.init pr Msg c) ≤ K.S.anchors.card := by
  unfold unusedCount
  simp only [St.init, List.not_mem_nil, not_false_eq_true, Finset.filter_true]
  exact Finset.card_image_le

omit [Fintype pr.Y] [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Fintype Msg] [DecidableEq Msg] in
/-- `B₁` makes at most `q_{h,1} + q_{h,2} + L + 1` queries to `O_b`. -/
theorem B1run_hashBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    (B1run pr Msg slKeygen A.toFxmssAdversary).IsQueryBoundP
      (Repro.IsHashQuery pr.Y (X2 pr Msg)) (qh₁ + qh₂ + L + 1) := by
  have hnot : ∀ n, ¬ Repro.IsHashQuery pr.Y (X2 pr Msg) (.inl n) := fun _ h => h
  have h1 : (simulateQ (fwd pr Msg) A.chooseShape).IsQueryBoundP
      (Repro.IsHashQuery pr.Y (X2 pr Msg)) qh₁ := by
    refine A.roBound₁.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
    · rcases t with n | x
      · exact ht.elim
      · simp [fwd, Repro.IsHashQuery]
    · rcases t with n | x
      · simpa [fwd] using hnot n
      · exact (ht trivial).elim
  unfold B1run
  refine (isQueryBoundP_bind (n := 0) (m := qh₁ + (qh₂ + 1 + L)) (liftM_bound _ _ hnot)
    fun pk _ => isQueryBoundP_bind (n := qh₁) (m := qh₂ + 1 + L) h1 fun z hz => ?_).mono
      (by omega)
  have hz' : z ∈ support A.chooseShape := support_simulateQ_subset _ _ hz
  unfold B1cont
  by_cases hv : z.1.TreeValid P.hsf
  swap
  · rw [ite_eq_left hv]; simp
  rw [ite_eq_right (not_not.2 hv)]
  refine isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun f _ =>
    isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun pkSl _ => ?_
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  refine (isQueryBoundP_run_potential (implB pr Msg _ _) (unusedCount _)
    (fun t s _ m k hk => implB_hash_step _ _ t s m k hk)
    (stage2Prog_roBound slKeygen A z.2 _) _).mono ?_
  have := (unusedCount_init (Msg := Msg) ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ ∅).trans
    (A.anchors_le z hz' hv)
  omega

omit [Fintype pr.Y] [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] [Fintype Msg] [DecidableEq Msg] in
/-- `B₁` makes at most `L` reprogramming calls. -/
theorem B1run_reproBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    (B1run pr Msg slKeygen A.toFxmssAdversary).IsQueryBoundP
      (Repro.IsReproQuery pr.Y (X2 pr Msg)) L := by
  have hnot : ∀ n, ¬ Repro.IsReproQuery pr.Y (X2 pr Msg) (.inl n) := fun _ h => h
  have h1 : (simulateQ (fwd pr Msg) A.chooseShape).IsQueryBoundP
      (Repro.IsReproQuery pr.Y (X2 pr Msg)) 0 :=
    isQueryBoundP_simulateQ_zero _ fun t => by
      rcases t with n | x <;> simp [fwd, Repro.IsReproQuery]
  unfold B1run
  refine (isQueryBoundP_bind (n := 0) (m := 0 + L) (liftM_bound _ _ hnot)
    fun pk _ => isQueryBoundP_bind (n := 0) (m := L) h1 fun z hz => ?_).mono (by omega)
  have hz' : z ∈ support A.chooseShape := support_simulateQ_subset _ _ hz
  unfold B1cont
  by_cases hv : z.1.TreeValid P.hsf
  swap
  · rw [ite_eq_left hv]; simp
  rw [ite_eq_right (not_not.2 hv)]
  refine isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun f _ =>
    isQueryBoundP_zero_bind (liftM_bound _ _ hnot) fun pkSl _ => ?_
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  refine (isQueryBoundP_run_potential (p := fun _ => False) (implB pr Msg _ _) (unusedCount _)
    (fun t s _ m k hk => implB_repro_step _ _ t s m k hk)
    (isQueryBoundP_false _ 0) _).mono ?_
  have := (unusedCount_init (Msg := Msg) ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ ∅).trans
    (A.anchors_le z hz' hv)
  omega

end Bounds

end Claim42

open Claim42 in
/-- **The distinguisher `B₁`** of Algorithm 5 against `DI-Repro` (Definition C.2) for
`H_msg^sf`, with `X₁ = Y`, `X₂ = (PK.seed, PK.sf, idx, M)`: at most `q_{h,1} + q_{h,2} + L + 1`
hash queries and at most `L` reprogramming calls. -/
noncomputable def B1 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Repro.DIAdversary pr.Y (X2 pr Msg) pr.Digest (qh₁ + qh₂ + L + 1) L where
  run := B1run pr Msg slKeygen A.toFxmssAdversary
  hashBound := B1run_hashBound slKeygen A
  reproBound := B1run_reproBound slKeygen A

namespace Claim42

/-! ## The lazy worlds are the games -/

section Simulation

variable {pr Msg}

/-- The lazy state of `DI-Repro` for `H_msg^sf`. -/
abbrev LS (pr : Primitives P) (Msg : Type) : Type := Repro.LazyState pr.Y (X2 pr Msg) pr.Digest

/-- The signing-phase state of the games read off the lazy state (its table is the random-oracle
cache) and `B₁`'s state (the records). -/
def projSt (ls : LS pr Msg) (bs : St pr Msg) : St pr Msg := { bs with cache := ⟨ls.table⟩ }

/-- The signing mode of the game simulated in world `b`: `F.0` for `b = 0`, `F.2` for `b = 1`. -/
noncomputable def modeOf (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg) ProbComp) :=
  if b then implG2 pr Msg K sk else implG pr Msg K sk

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
theorem step_unif (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (n : ℕ) (ls : LS pr Msg)
    (bs : St pr Msg) :
    (fun z : ((fullSpec pr Msg).Range (.inl (.inl n)) × St pr Msg) × LS pr Msg =>
        (z.1.1, projSt z.2 z.1.2)) <$>
        (simulateQ (Repro.lazyDIImpl b) ((implB pr Msg K sk (.inl (.inl n))).run bs)).run ls =
      (modeOf b K sk (.inl (.inl n))).run (projSt ls bs) := by
  cases b <;> simp [implB, fwd, modeOf, implG, implG2, impl, Repro.lazyDIImpl, projSt]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [DecidableEq pr.Digest] in
theorem lazyHash_run_some {x : RoIn pr Msg} {ls : LS pr Msg} {d : pr.Digest}
    (h : ls.table x = some d) :
    (Repro.lazyHash x).run ls = pure (d, { ls with log := x :: ls.log }) := by
  simp only [StateT.run, Repro.lazyHash, h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [DecidableEq pr.Digest] in
theorem lazyHash_run_none {x : RoIn pr Msg} {ls : LS pr Msg} (h : ls.table x = none) :
    (Repro.lazyHash x).run ls = (fun d => (d, { ls with
      table := Function.update ls.table x (some d)
      log := x :: ls.log })) <$> ($ᵗ pr.Digest) := by
  simp only [StateT.run, Repro.lazyHash, h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [DecidableEq pr.Digest] in
theorem roStep_run_some {x : RoIn pr Msg} {s : St pr Msg} {d : pr.Digest}
    (h : s.cache x = some d) : (roStep pr Msg x).run s = pure (d, s) := by
  simp only [roStep, StateT.run_mk, h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [DecidableEq pr.Digest] in
theorem roStep_run_none {x : RoIn pr Msg} {s : St pr Msg} (h : s.cache x = none) :
    (roStep pr Msg x).run s =
      (fun d => (d, { s with cache := s.cache.cacheQuery x d })) <$> ($ᵗ pr.Digest) := by
  simp only [roStep, StateT.run_mk, h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] [DecidableEq pr.Digest] in
theorem step_ro (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (x : RoIn pr Msg)
    (ls : LS pr Msg) (bs : St pr Msg) :
    (fun z : ((fullSpec pr Msg).Range (.inl (.inr x)) × St pr Msg) × LS pr Msg =>
        (z.1.1, projSt z.2 z.1.2)) <$>
        (simulateQ (Repro.lazyDIImpl b) ((implB pr Msg K sk (.inl (.inr x))).run bs)).run ls =
      (modeOf b K sk (.inl (.inr x))).run (projSt ls bs) := by
  have hc : (projSt ls bs).cache x = ls.table x := rfl
  have hm : (modeOf b K sk (.inl (.inr x))).run (projSt ls bs) =
      (roStep pr Msg x).run (projSt ls bs) := by cases b <;> rfl
  rw [hm]
  rcases h : ls.table x with _ | d
  · rw [roStep_run_none (hc.trans h)]
    simp [implB, fwd, Repro.lazyDIImpl, lazyHash_run_none h, projSt, QueryCache.cacheQuery,
      Functor.map_map]
    rfl
  · rw [roStep_run_some (hc.trans h)]
    simp [implB, fwd, Repro.lazyDIImpl, lazyHash_run_some h, projSt]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [DecidableEq pr.Y]
  [DecidableEq pr.PkSeed] [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
theorem signStep_run_fresh (K : Keys pr)
    (dig : LeafId → RoIn pr Msg → StateT (St pr Msg) ProbComp pr.Digest)
    (sigOf : LeafId → pr.Digest → Option (Scheme.Fxmss.Sig pr)) (q : Msg × LeafId)
    (s : St pr Msg) (h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used) :
    (signStep pr Msg K dig sigOf q).run s =
      ($ᵗ pr.Y) >>= fun R => (dig q.2 (roIn pr Msg R K.pk K.pkSf q.2 q.1)).run s >>= fun p =>
        pure (some (R, sigOf q.2 p.1), stSign p.2 q R p.1 (sigOf q.2 p.1)) := by
  simp [signStep, h, stSign]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [DecidableEq pr.Y]
  [DecidableEq pr.PkSeed] [DecidableEq pr.Digest] [SampleableType pr.Digest] [DecidableEq Msg] in
theorem signStep_run_else (K : Keys pr)
    (dig : LeafId → RoIn pr Msg → StateT (St pr Msg) ProbComp pr.Digest)
    (sigOf : LeafId → pr.Digest → Option (Scheme.Fxmss.Sig pr)) (q : Msg × LeafId)
    (s : St pr Msg) (h : ¬ (q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used)) :
    (signStep pr Msg K dig sigOf q).run s = pure (none, { s with log := s.log ++ [q.1] }) := by
  simp only [signStep, StateT.run_bind, StateT.run_get, pure_bind]
  rw [ite_eq_right h]
  simp

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [DecidableEq pr.Digest] in
theorem freshProgStep_run (x : RoIn pr Msg) (s : St pr Msg) :
    (freshProgStep pr Msg x).run s =
      (fun d => (d, { s with cache := s.cache.cacheQuery x d })) <$> ($ᵗ pr.Digest) := rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
theorem step_sign_else (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (ls : LS pr Msg) (bs : St pr Msg) (h : ¬ (q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ bs.used)) :
    (fun z : ((fullSpec pr Msg).Range (.inr q) × St pr Msg) × LS pr Msg =>
        (z.1.1, projSt z.2 z.1.2)) <$>
        (simulateQ (Repro.lazyDIImpl b) ((implB pr Msg K sk (.inr q)).run bs)).run ls =
      (modeOf b K sk (.inr q)).run (projSt ls bs) := by
  have hm : (modeOf b K sk (.inr q)).run (projSt ls bs) = (signStep pr Msg K
      (if b then fun _ x => freshProgStep pr Msg x else fun _ x => roStep pr Msg x)
      (fun id md => Scheme.Fxmss.sign pr K.S K.pk sk md id) q).run (projSt ls bs) := by
    cases b <;> rfl
  rw [hm, signStep_run_else K _ _ q (projSt ls bs) h]
  simp [implB, signB_run_else K sk q bs h, projSt]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
theorem step_sign_fresh (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (ls : LS pr Msg) (bs : St pr Msg) (h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ bs.used)
    (hx : x2Of K q ∉ ls.submitted) :
    (fun z : ((fullSpec pr Msg).Range (.inr q) × St pr Msg) × LS pr Msg =>
        (z.1.1, projSt z.2 z.1.2)) <$>
        (simulateQ (Repro.lazyDIImpl b) ((implB pr Msg K sk (.inr q)).run bs)).run ls =ᵈ
      (modeOf b K sk (.inr q)).run (projSt ls bs) := by
  have hm : (modeOf b K sk (.inr q)).run (projSt ls bs) = (signStep pr Msg K
      (if b then fun _ x => freshProgStep pr Msg x else fun _ x => roStep pr Msg x)
      (fun id md => Scheme.Fxmss.sign pr K.S K.pk sk md id) q).run (projSt ls bs) := by
    cases b <;> rfl
  rw [hm, signStep_run_fresh K _ _ q (projSt ls bs) h]
  simp only [implB, signB_run_fresh K sk q bs h, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  simp only [Repro.lazyDIImpl, QueryImpl.add_apply_inr, Repro.lazyDIRepro_run, hx, ite_false,
    Repro.uniformSample_prod_eq, map_bind, bind_assoc, pure_bind, map_pure, Option.getD_some,
    QueryImpl.add_apply_inl]
  refine EvalDistEq.bind_right _ fun R => ?_
  refine (EvalDistEq.bind_const _ _).trans (evalDistEq_of_eq ?_)
  have hc : (projSt ls bs).cache (roIn pr Msg R K.pk K.pkSf q.2 q.1) = ls.table (R, x2Of K q) :=
    rfl
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases h' : ls.table (R, x2Of K q) with _ | d
    · rw [roStep_run_none (hc.trans h')]
      simp [StateT.run, Repro.lazyHash, h', projSt, stSign, QueryCache.cacheQuery]
      rfl
    · rw [roStep_run_some (hc.trans h')]
      simp [StateT.run, Repro.lazyHash, h', projSt, stSign]
  · simp only [↓reduceIte]
    rw [freshProgStep_run]
    simp [StateT.run, Repro.lazyHash, projSt, stSign, QueryCache.cacheQuery]
    rfl

/-- The invariant of `B₁`'s simulation: used leaves are anchors, and every submitted second input
names the `idx` of a used leaf. -/
def InvB (K : Keys pr) (ls : LS pr Msg) (bs : St pr Msg) : Prop :=
  (∀ id ∈ bs.used, id ∈ leafIds P.hsf K.S) ∧ ∀ x ∈ ls.submitted, ∃ id ∈ bs.used, x.2.2.1 = toIdx id

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg]
  [Nontrivial Msg] in
/-- The leaf identifiers of a valid structure fit `idx` (one height byte, eight index bytes). -/
theorem leafId_lt (hP : P.Valid) {S : Structure} (hS : S.TreeValid P.hsf) {id : LeafId}
    (h : id ∈ leafIds P.hsf S) : id.height < 256 ∧ id.index < 2 ^ 64 := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  have := hP.hsf_le
  exact ⟨by simp only [Node.toLeafId]; omega, hS.anchor_idx_lt v hv⟩

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y] [SampleableType pr.Digest]
  [DecidableEq pr.Y] [DecidableEq pr.PkSeed] [DecidableEq pr.Digest] [Inhabited pr.Y]
  [DecidableEq Msg] in
/-- **The guard of Definition C.2 never fires**: a signing query at an unused anchor submits a
fresh second input. -/
theorem x2Of_not_mem (hP : P.Valid) {K : Keys pr} (hS : K.S.TreeValid P.hsf) {ls : LS pr Msg}
    {bs : St pr Msg} (hi : InvB K ls bs) {q : Msg × LeafId}
    (h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ bs.used) : x2Of K q ∉ ls.submitted := by
  intro hx
  obtain ⟨id, hid, he⟩ := hi.2 _ hx
  have h1 := leafId_lt hP hS h.1
  have h2 := leafId_lt hP hS (hi.1 id hid)
  exact h.2 (toIdx_inj h1.1 h1.2 h2.1 h2.2 he ▸ hid)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [SampleableType pr.Y]
  [DecidableEq pr.Digest] in
theorem lazyHash_submitted (x : RoIn pr Msg) (ls : LS pr Msg) (w)
    (hw : w ∈ support ((Repro.lazyHash x).run ls)) : w.2.submitted = ls.submitted := by
  rcases h : ls.table x with _ | d
  · rw [lazyHash_run_none h, support_map] at hw
    obtain ⟨d, -, rfl⟩ := hw
    rfl
  · rw [lazyHash_run_some h] at hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] [DecidableEq pr.Digest] in
theorem invB_step (hP : P.Valid) (b : Bool) {K : Keys pr} (hS : K.S.TreeValid P.hsf)
    (sk : LeafId → ℕ → pr.Y) (t : (fullSpec pr Msg).Domain) (ls : LS pr Msg) (bs : St pr Msg)
    (hi : InvB K ls bs)
    (z) (hz : z ∈ support
      ((simulateQ (Repro.lazyDIImpl b) ((implB pr Msg K sk t).run bs)).run ls)) :
    InvB K z.2 z.1.2 := by
  rcases t with (n | x) | q
  · simp [implB, fwd, Repro.lazyDIImpl] at hz
    obtain ⟨y, rfl⟩ := hz
    exact hi
  · simp only [implB, fwd, Repro.lazyDIImpl, StateT.run_monadLift, monadLift_self,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨hi.1, by rw [lazyHash_submitted _ _ _ hw]; exact hi.2⟩
  · by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ bs.used
    · simp only [implB, signB_run_fresh K sk q bs h, Repro.lazyDIImpl, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, Repro.lazyDIRepro_run,
        x2Of_not_mem hP hS hi h, ite_false, mem_support_bind_iff, support_map, Set.mem_image,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨_, ⟨r, -, rfl⟩, w, hw, rfl⟩ := hz
      have hsub := lazyHash_submitted _ _ _ hw
      refine ⟨fun id hid => ?_, fun x hx => ?_⟩
      · simp only [stSign, List.mem_append, List.mem_singleton] at hid
        rcases hid with hid | rfl
        · exact hi.1 id hid
        · exact h.1
      · rw [hsub] at hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact ⟨q.2, by simp [stSign], rfl⟩
        · obtain ⟨id, hid, he⟩ := hi.2 x hx
          exact ⟨id, by simp [stSign, hid], he⟩
    · simp [implB, signB_run_else K sk q bs h] at hz
      subst hz
      exact hi

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
/-- Every step of `B₁`'s signing phase in the lazy world `b` projects onto the game's step. -/
theorem stepB (hP : P.Valid) (b : Bool) {K : Keys pr} (hS : K.S.TreeValid P.hsf)
    (sk : LeafId → ℕ → pr.Y) (t : (fullSpec pr Msg).Domain) (ls : LS pr Msg) (bs : St pr Msg)
    (hi : InvB K ls bs) :
    (fun z : ((fullSpec pr Msg).Range t × St pr Msg) × LS pr Msg =>
        (z.1.1, projSt z.2 z.1.2)) <$>
        (simulateQ (Repro.lazyDIImpl b) ((implB pr Msg K sk t).run bs)).run ls =ᵈ
      (modeOf b K sk t).run (projSt ls bs) := by
  rcases t with (n | x) | q
  · exact evalDistEq_of_eq (step_unif b K sk n ls bs)
  · exact evalDistEq_of_eq (step_ro b K sk x ls bs)
  · by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ bs.used
    · exact step_sign_fresh b K sk q ls bs h (x2Of_not_mem hP hS hi h)
    · exact evalDistEq_of_eq (step_sign_else b K sk q ls bs h)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest]
  [DecidableEq pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Nontrivial Msg] in
/-- **The signing phase of `B₁` in the lazy world `b` is the signing phase of the game**
(`F.0` for `b = 0`, `F.2` for `b = 1`), on the projected state. -/
theorem stage2_lazy (hP : P.Valid) (b : Bool) {K : Keys pr} (hS : K.S.TreeValid P.hsf)
    (sk : LeafId → ℕ → pr.Y) {α : Type} (oa : OracleComp (fullSpec pr Msg) α) (ls : LS pr Msg)
    (bs : St pr Msg) (hi : InvB K ls bs) :
    (fun z : (α × St pr Msg) × LS pr Msg => (z.1.1, projSt z.2 z.1.2)) <$>
        (simulateQ (Repro.lazyDIImpl b) ((simulateQ (implB pr Msg K sk) oa).run bs)).run ls =ᵈ
      (simulateQ (modeOf b K sk) oa).run (projSt ls bs) :=
  map_run_nested_evalDistEq _ _ _ projSt (InvB K)
    (fun t ls bs hi z hz => invB_step hP b hS sk t ls bs hi z hz)
    (fun t ls bs hi => stepB hP b hS sk t ls bs hi) oa ls bs hi

/-- The random-oracle cache of a lazy state. -/
def LS.cache (ls : LS pr Msg) : (roSpec pr Msg).QueryCache := ⟨ls.table⟩

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
/-- **The structure phase of `B₁` in a lazy world is `A₁` against the lazy random oracle.** -/
theorem stage1_lazy (b : Bool) {α : Type} (oa : OracleComp (spec pr Msg) α) (ls : LS pr Msg) :
    Prod.map id LS.cache <$> (simulateQ (Repro.lazyDIImpl b) (simulateQ (fwd pr Msg) oa)).run ls =
      (simulateQ (roSpec pr Msg).romImpl oa).run ls.cache := by
  rw [← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ LS.cache (fun t s => ?_) oa ls
  rcases t with n | x
  · simp [fwd, Repro.lazyDIImpl, LS.cache, unifFwdImpl]
  · rw [QueryImpl.apply_compose]
    rcases h : s.table x with _ | d
    · simp [fwd, Repro.lazyDIImpl, lazyHash_run_none h, LS.cache, h,
        QueryCache.cacheQuery]
      rfl
    · simp [fwd, Repro.lazyDIImpl, lazyHash_run_some h, LS.cache, h]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [Inhabited pr.Digest] [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
/-- The structure phase submits nothing. -/
theorem stage1_submitted (b : Bool) {α : Type} (oa : OracleComp (spec pr Msg) α)
    (ls : LS pr Msg) :
    ∀ z ∈ support ((simulateQ (Repro.lazyDIImpl b) (simulateQ (fwd pr Msg) oa)).run ls),
      z.2.submitted = ls.submitted := by
  rw [← QueryImpl.simulateQ_compose]
  refine simulateQ_run_preserves_inv_of_query _ (fun s => s.submitted = ls.submitted)
    (fun t s hs z hz => ?_) oa ls rfl
  rcases t with n | x
  · simp [fwd, Repro.lazyDIImpl] at hz
    obtain ⟨y, rfl⟩ := hz
    exact hs
  · simp only [QueryImpl.apply_compose, fwd, simulateQ_spec_query, Repro.lazyDIImpl,
      QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
    exact (lazyHash_submitted _ _ _ hz).trans hs

end Simulation

/-- The game simulated by `B₁` in world `b`: `F.0` (`gameG`) for `b = 0`, `F.2` (`gameG2`) for
`b = 1`. -/
noncomputable def gameOf (b : Bool) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    ProbComp (Option (Transcript pr Msg)) := do
  let pk ← $ᵗ pr.PkSeed
  let z ← stage1 pr Msg slKeygen A
  stageG pr Msg slKeygen A (fun K sk => modeOf b K sk) pk z

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] in
/-- `B₁` after the structure phase, in the lazy world `b`, is the game after the structure
phase. -/
theorem lazy_B1cont (hP : P.Valid) (b : Bool) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) (pk : pr.PkSeed)
    (z : Structure × A.State) (ls : LS pr Msg) (hls : ls.submitted = ∅) :
    Prod.fst <$> (simulateQ (Repro.lazyDIImpl b) (B1cont pr Msg slKeygen A pk z)).run ls =ᵈ
      (fun o => decide (WinNotC1 o)) <$>
        stageG pr Msg slKeygen A (fun K sk => modeOf b K sk) pk (z, ls.cache) := by
  have hl : ∀ {β : Type} (oa : ProbComp β) (s : LS pr Msg),
      (simulateQ (Repro.lazyDIImpl b) (liftM oa : OracleComp (DSpec pr Msg) β)).run s =
        (fun x => (x, s)) <$> oa := fun oa s => simulateQ_add_liftM_run _ oa s
  unfold B1cont stageG
  by_cases hv : z.1.TreeValid P.hsf
  swap
  · rw [ite_eq_left hv, ite_eq_left hv]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact evalDistEq_of_eq (by rw [decide_eq_false (by simp [WinNotC1])])
  rw [ite_eq_right (not_not.2 hv), ite_eq_right (not_not.2 hv)]
  simp only [simulateQ_bind, StateT.run_bind, hl, bind_map_left, map_bind]
  refine EvalDistEq.bind_right _ fun f => EvalDistEq.bind_right _ fun pkSl => ?_
  have hi : InvB (Msg := Msg) ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ ls
      (St.init pr Msg ∅) :=
    ⟨fun _ h => by simp [St.init] at h, fun _ h => by simp [hls] at h⟩
  have h2 := (stage2_lazy hP b hv (skOf pr z.1 f)
    (stage2Prog pr Msg slKeygen A z.2 ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩) ls
    (St.init pr Msg ∅) hi).map (fun r => decide (WinNotC1 (some (Transcript.ofRun pr Msg
      ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩ r))))
  simp only [Functor.map_map] at h2
  simp only [simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]
  exact h2

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] in
/-- **World `b` of `DI-Repro` run by `B₁` is the game `F.0` / `F.2`** on the output bit. -/
theorem lazy_B1run (hP : P.Valid) (b : Bool) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    (simulateQ (Repro.lazyDIImpl b) (B1run pr Msg slKeygen A)).run' Repro.LazyState.init =ᵈ
      (fun o => decide (WinNotC1 o)) <$> gameOf pr Msg slKeygen b A := by
  have hl : ∀ {β : Type} (oa : ProbComp β) (s : LS pr Msg),
      (simulateQ (Repro.lazyDIImpl b) (liftM oa : OracleComp (DSpec pr Msg) β)).run s =
        (fun x => (x, s)) <$> oa := fun oa s => simulateQ_add_liftM_run _ oa s
  unfold B1run gameOf
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, StateT.run_bind, hl, bind_map_left, map_bind]
  refine EvalDistEq.bind_right _ fun pk => ?_
  have hst : stage1 pr Msg slKeygen A = Prod.map id LS.cache <$>
      (simulateQ (Repro.lazyDIImpl b) (simulateQ (fwd pr Msg) A.chooseShape)).run
        Repro.LazyState.init := by
    rw [stage1_lazy]; rfl
  rw [hst, bind_map_left]
  refine EvalDistEq.bind_congr_of_support _ fun p hp => ?_
  have hsub := stage1_submitted b A.chooseShape _ p hp
  exact lazy_B1cont pr Msg slKeygen hP b A pk p.1 p.2 hsub

omit [Fintype pr.Digest] [DecidableEq pr.Digest] [Inhabited pr.Digest] in
/-- `Pr[F.0 or F.2 ⇒ Win ∧ ¬C₁] = Pr[DI-Repro_b(B₁) ⇒ 1]`. -/
theorem prEvent_gameOf (hP : P.Valid) (b : Bool) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Pr{let o ← gameOf pr Msg slKeygen b A}[WinNotC1 o] =
      Pr{let x ← Repro.diExperiment b (B1run pr Msg slKeygen A)}[x = true] := by
  have h := ((Repro.diExperiment_evalDistEq_lazy b _).trans
    (lazy_B1run pr Msg slKeygen hP b A)).prEvent_eq (· = true)
  rw [h, Functor.map_map]
  congr 2
  funext o
  simp

/-- `a ≤ b + |a − b|` for finite `a`, `b`. -/
theorem le_add_ofReal_abs {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a ≤ b + ENNReal.ofReal |a.toReal - b.toReal| := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + |a.toReal - b.toReal|) :=
        ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a.toReal - b.toReal)])
    _ = b + ENNReal.ofReal |a.toReal - b.toReal| := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _), ENNReal.ofReal_toReal hb]

end Claim42

open Claim42 in
omit [Fintype pr.Digest] [DecidableEq pr.Digest] in
/-- **Claim 4.2** (`F.1 → F.2`): `Succ^{F.1}(A) ≤ Succ^{F.2}(A) + Adv^{DI-Repro}(B₁)`, where
`Succ^{F.1}` is the probability of `Win ∧ ¬C₁` in `F.0` and `F.2` is run lazily (`gameG2`); `B₁`
makes at most `q_{h,1} + q_{h,2} + L + 1` hash queries and at most `L` reprogramming calls. -/
theorem claim_4_2 (hP : P.Valid) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameG pr Msg slKeygen A.toFxmssAdversary}[WinNotC1 o] ≤
      Pr{let o ← gameG2 pr Msg slKeygen A.toFxmssAdversary}[WinNotC1 o] +
        ENNReal.ofReal (Repro.diAdvantage (B1 pr Msg slKeygen A)) := by
  have h0 := prEvent_gameOf pr Msg slKeygen hP false A.toFxmssAdversary
  have h1 := prEvent_gameOf pr Msg slKeygen hP true A.toFxmssAdversary
  have e0 : gameOf pr Msg slKeygen false A.toFxmssAdversary =
      gameG pr Msg slKeygen A.toFxmssAdversary := rfl
  have e1 : gameOf pr Msg slKeygen true A.toFxmssAdversary =
      gameG2 pr Msg slKeygen A.toFxmssAdversary := rfl
  rw [e0] at h0
  rw [e1] at h1
  rw [h0, h1, Repro.diAdvantage]
  exact le_add_ofReal_abs (prEvent_ne_top _) (prEvent_ne_top _)

end ShrincsSecurity.Fxmss.Rom

end
