module

public import ShrincsSecurity.Notions.PRF
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Caching a PRF distinguisher

`SHRINCS-Security-Analysis.pdf`, Claim 4.11 (txt lines 3950–3962): the reduction against `PRF`
issues "classical and pairwise distinct" queries. A distinguisher that may repeat a query is
turned into one that does not by caching the oracle's answers: `cacheAdv B` runs `B` and answers a
repeated query from its cache.

* `prfAdvantage_cacheAdv`: caching does not change the advantage. In the real world the oracle is
  a function of its input; in the ideal world it is a lazily sampled function whose own cache
  contains `cacheAdv`'s cache, so a cached answer is the answer the oracle would give.
* `cacheAdv_bound`: if every query of `B` (after a prefix of private coins) lies in a finite set
  `Ds`, then `cacheAdv B` makes at most `|Ds|` queries, each at a distinct point.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Shrincs.CachedPRF

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- The oracles of a PRF distinguisher. -/
abbrev PSpec (D R : Type) := PRFScheme.PRFOracleSpec D R

/-- The cache of the answers of the function oracle. -/
abbrev Cache (D R : Type) := (D →ₒ R).QueryCache

/-- The caching handler: private coins forwarded; a function query answered from the cache, or
forwarded and cached. -/
def cacheImpl : QueryImpl (PSpec D R) (StateT (Cache D R) (OracleComp (PSpec D R))) :=
  (fun n => liftM ((PSpec D R).query (.inl n)) :
      QueryImpl unifSpec (StateT (Cache D R) (OracleComp (PSpec D R)))) +
  (fun d => StateT.mk fun c => match c d with
    | some v => pure (v, c)
    | none => (fun v => (v, c.cacheQuery d v)) <$> (PSpec D R).query (.inr d) :
      QueryImpl (D →ₒ R) (StateT (Cache D R) (OracleComp (PSpec D R))))

/-- **The cached distinguisher**: `B` with its function queries answered from a cache. -/
def cacheAdv (B : OracleComp (PSpec D R) Bool) : OracleComp (PSpec D R) Bool :=
  (simulateQ cacheImpl B).run' ∅

/-- The points of `Ds` not yet cached. -/
def fresh (Ds : Finset D) (c : Cache D R) : Finset D := Ds.filter fun d => c d = none

/-- Every query is a coin or a function query at a point of `Ds`. -/
def InSet (Ds : Finset D) : ℕ ⊕ D → Prop
  | .inl _ => True
  | .inr d => d ∈ Ds


/-! ## Steps of the caching handler -/

omit [SampleableType R] in
theorem cacheImpl_inl (n : ℕ) (c : Cache D R) :
    (cacheImpl (.inl n)).run c =
      (fun u => (u, c)) <$> (liftM ((PSpec D R).query (.inl n)) : OracleComp (PSpec D R) _) := by
  simp [cacheImpl, StateT.run_monadLift]

omit [SampleableType R] in
theorem cacheImpl_some {d : D} {c : Cache D R} {v : R} (h : c d = some v) :
    (cacheImpl (.inr d)).run c = pure (v, c) := by
  simp [cacheImpl, h]

omit [SampleableType R] in
theorem cacheImpl_none {d : D} {c : Cache D R} (h : c d = none) :
    (cacheImpl (.inr d)).run c =
      (fun v => (v, c.cacheQuery d v)) <$>
        (liftM ((PSpec D R).query (.inr d)) : OracleComp (PSpec D R) R) := by
  simp [cacheImpl, h]

omit [SampleableType R] in
theorem cacheQuery_sub {c c' : Cache D R} (h : ∀ d v, c d = some v → c' d = some v) (d : D)
    (v : R) (h' : c' d = some v) : ∀ d' v', c.cacheQuery d v d' = some v' → c' d' = some v' := by
  intro d' v' hv
  by_cases hd : d' = d
  · subst hd; simp at hv; rw [← hv]; exact h'
  · rw [QueryCache.cacheQuery_of_ne _ _ hd] at hv; exact h _ _ hv

/-! ## The advantage is unchanged -/

section Advantage

variable {K : Type}

/-- The real oracle `F(k, ·)`. -/
abbrev realImpl (F : K → D → R) (k : K) : QueryImpl (PSpec D R) ProbComp :=
  unifSpec.passthrough + fun d => (pure (F k d) : ProbComp R)

omit [DecidableEq D] [SampleableType R] in
theorem realImpl_inr (F : K → D → R) (k : K) (d : D) :
    realImpl F k (.inr d) = (pure (F k d) : ProbComp R) := rfl

omit [SampleableType R] in
/-- In the real world, with every cached answer the function's value, the cached run is the
run. -/
theorem real_run (F : K → D → R) (k : K) :
    ∀ (oa : OracleComp (PSpec D R) Bool) (c : Cache D R), (∀ d v, c d = some v → v = F k d) →
      Prod.fst <$> simulateQ (realImpl F k) ((simulateQ cacheImpl oa).run c) =
        simulateQ (realImpl F k) oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro c _; simp
  | query_bind t k' ih =>
    intro c hc
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | d
    · rw [cacheImpl_inl]
      simp only [simulateQ_map, bind_map_left]
      exact bind_congr fun u => ih u c hc
    · rcases h : c d with _ | v
      · rw [cacheImpl_none h]
        simp only [simulateQ_map, bind_map_left, simulateQ_spec_query, realImpl_inr, pure_bind]
        refine ih _ _ fun d' v' hv => ?_
        by_cases hd : d' = d
        · subst hd; simp at hv; exact hv.symm
        · rw [QueryCache.cacheQuery_of_ne _ _ hd] at hv; exact hc _ _ hv
      · rw [cacheImpl_some h]
        simp only [simulateQ_pure, pure_bind, realImpl_inr]
        rw [← hc d v h]
        exact ih v c hc

/-- The ideal oracle: a lazily sampled function. -/
abbrev idealImpl : QueryImpl (PSpec D R) (StateT (Cache D R) ProbComp) := (D →ₒ R).romImpl


theorem idealImpl_inl (n : ℕ) (ro : Cache D R) :
    (idealImpl (D := D) (R := R) (.inl n)).run ro =
      (fun u => (u, ro)) <$> (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
  simp [idealImpl, OracleSpec.romImpl, unifFwdImpl]

theorem idealImpl_inr_support {d : D} {ro : Cache D R} {p : R × Cache D R}
    (hp : p ∈ support ((idealImpl (.inr d)).run ro)) :
    p.2 d = some p.1 ∧ ∀ d' v, ro d' = some v → p.2 d' = some v := by
  rw [idealImpl, OracleSpec.romImpl_apply_inr, randomOracle.run_eq] at hp
  rcases h : ro d with _ | u
  · rw [h] at hp
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨u, -, rfl⟩ := hp
    refine ⟨by simp, fun d' v hv => ?_⟩
    by_cases hd : d' = d
    · subst hd; rw [h] at hv; cases hv
    · rw [QueryCache.cacheQuery_of_ne _ _ hd]; exact hv
  · rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨h, fun _ _ hv => hv⟩

/-- In the ideal world, with the cache contained in the oracle's table, the cached run is the
run. -/
theorem ideal_run :
    ∀ (oa : OracleComp (PSpec D R) Bool) (c ro : Cache D R),
      (∀ d v, c d = some v → ro d = some v) →
      (fun p => (p.1.1, p.2)) <$> (simulateQ idealImpl ((simulateQ cacheImpl oa).run c)).run ro =
        (simulateQ idealImpl oa).run ro := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro c ro _; simp
  | query_bind t k' ih =>
    intro c ro hc
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | d
    · rw [cacheImpl_inl, simulateQ_map, StateT.run_map, simulateQ_spec_query, idealImpl_inl]
      simp only [Functor.map_map, bind_map_left]
      exact bind_congr fun u => ih u c ro hc
    · rcases h : c d with _ | v
      · rw [cacheImpl_none h, simulateQ_map, StateT.run_map, simulateQ_spec_query, bind_map_left]
        refine bind_congr_of_forall_mem_support _ fun p hp => ?_
        obtain ⟨h1, h2⟩ := idealImpl_inr_support hp
        exact ih p.1 _ p.2 fun d' v' hv => by
          by_cases hd : d' = d
          · subst hd; simp at hv; rw [← hv]; exact h1
          · rw [QueryCache.cacheQuery_of_ne _ _ hd] at hv; exact h2 _ _ (hc _ _ hv)
      · rw [cacheImpl_some h, simulateQ_pure, StateT.run_pure, pure_bind, idealImpl,
          OracleSpec.romImpl_apply_inr, randomOracle.run_eq, hc d v h, pure_bind]
        exact ih v c ro hc

/-- **Caching does not change the advantage** (Definition 4.3). -/
theorem prfAdvantage_cacheAdv {K : Type} (prf : PRFScheme K D R)
    (B : OracleComp (PSpec D R) Bool) :
    prf.prfAdvantage (cacheAdv B) = prf.prfAdvantage B := by
  have hreal : prf.prfRealExperiment (cacheAdv B) = prf.prfRealExperiment B := by
    unfold PRFScheme.prfRealExperiment
    refine bind_congr fun k => ?_
    have h := real_run prf.eval k B ∅ (fun d v h => by simp at h)
    rw [cacheAdv, StateT.run'_eq, simulateQ_map]
    exact h
  have hideal : PRFScheme.prfIdealExperiment (cacheAdv B) =
      PRFScheme.prfIdealExperiment (D := D) (R := R) B := by
    unfold PRFScheme.prfIdealExperiment
    have h := congrArg (fun x => Prod.fst <$> x) (ideal_run B ∅ ∅ (fun d v h => h))
    simp only [Functor.map_map] at h
    simp only [cacheAdv, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
    exact h
  rw [PRFScheme.prfAdvantage, PRFScheme.prfAdvantage, hreal, hideal]

end Advantage

/-! ## The budget -/

omit [SampleableType R] in
/-- A lifted `ProbComp` is passed through, with the cache unchanged. -/
theorem cacheImpl_liftM_run {α : Type} (p : ProbComp α) (c : Cache D R) :
    (simulateQ cacheImpl (liftM p : OracleComp (PSpec D R) α)).run c =
      (fun a => (a, c)) <$> (liftM p : OracleComp (PSpec D R) α) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    have hq : (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (PSpec D R) _) =
        liftM ((PSpec D R).query (.inl n)) := rfl
    simp only [liftM_bind, simulateQ_bind, StateT.run_bind, map_bind, hq, simulateQ_spec_query]
    rw [cacheImpl_inl, bind_map_left]
    exact bind_congr fun u => ih u

omit [SampleableType R] in
/-- **The budget of the cached distinguisher**: if every query of `oa` is a coin or a point of
`Ds`, the cached run from `c` makes at most as many function queries as there are points of `Ds`
not in `c`. -/
theorem cache_run_bound (Ds : Finset D) {α : Type} :
    ∀ (oa : OracleComp (PSpec D R) α) (c : Cache D R), oa.AllQueriesSatisfy (InSet Ds) →
      ((simulateQ cacheImpl oa).run c).IsQueryBoundP Notions.IsPRFQuery (fresh Ds c).card := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro c _; exact trivial
  | query_bind t k' ih =>
    intro c h
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | d
    · rw [cacheImpl_inl, bind_map_left]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [Notions.IsPRFQuery]),
        fun u => ?_⟩
      simpa [Notions.IsPRFQuery] using ih u c (h.2 u)
    · have hd : d ∈ Ds := h.1
      rcases hc : c d with _ | v
      · rw [cacheImpl_none hc, bind_map_left]
        have hmem : d ∈ fresh Ds c := Finset.mem_filter.2 ⟨hd, hc⟩
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr (Finset.card_pos.2 ⟨d, hmem⟩),
          fun u => ?_⟩
        have hf : fresh Ds (c.cacheQuery d u) = (fresh Ds c).erase d := by
          ext d'
          by_cases hd' : d' = d
          · subst hd'; simp [fresh]
          · simp [fresh, hd']
        have := ih u (c.cacheQuery d u) (h.2 u)
        rw [hf, Finset.card_erase_of_mem hmem] at this
        simpa [Notions.IsPRFQuery] using this
      · rw [cacheImpl_some hc, pure_bind]
        exact ih v c (h.2 v)

end ShrincsSecurity.Shrincs.CachedPRF

end
