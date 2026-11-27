module

public import ShrincsSecurity.Fxmss.Reduction
public import ShrincsSecurity.Fxmss.Members

/-!
# Common pieces of the TCR-type reductions of Section 4.7

`SHRINCS-Security-Analysis.pdf`, Section 4.7, Claims 4.3–4.9 (txt lines 3376–3760) and
Algorithms 6–11: the reductions `B₂`–`B₈` share the shape of `Reduction.lean` (`mkTcrAdv`,
`mkSTcrAdv`, `mkExclAdv`), and this file provides the pieces they have in common.

**Generic part** (any problem):
* `tcrFind` / `stcrFind`: the bounded witness search of a reduction's second stage over a list of
  candidates read off the forgery, and `tcrWin_tcrFind` / `stcrIsCollision_stcrFind`: a candidate
  colliding with a recorded target makes the search win.
* Query programs and their exact runs (the hypothesis `hq` of the `mk…` lemmas): chained challenge
  queries (`iterChal`, `iterChal_run`), chained collection queries (`iterColl`, `iterColl_run`),
  `List.mapM` of collection-only work (`tcr_mapM_run`), sequential composition of SM-TCR jobs
  (`tcr_forM_run`), and a list of S-TCR(Prop) challenge queries (`stcrQueries`,
  `stcrQueries_run`).

**The block game** (`Rom`):
* anchors (`anchorList`) and their bounds (`leafId_bounds`), Conjecture 3.1 at the anchors
  (`grind_eq_some`), the honest data `hon` of `F.3_γ` under a successful counter search
  (`hon_wots`, `hon_encoded`, `hon_block`) and in `F.3_0` (`hon0_chainValue`, `hon0_tops`), chain
  tweaks (`chainTw`) and chained `F`-evaluations (`iterVal_chain`);
* supports: a reachable setup has at most `L` anchors (`setupHyb_length_anchorList_le`), a
  reachable signing-phase output carries the honest data (`mem_support_stageHyb`);
* `prEvent_gameHyb_le`: an event of `F.3_γ` is bounded by the winning probability of a second
  stage that runs the signing phase itself and extracts from its output, as soon as the event
  implies the win on every reachable output. With the `mk…` lemmas this reduces each claim to a
  pointwise implication.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Fxmss

open Notions

variable {ι P T M N : Type}

/-! ## The witness search -/

section Search

variable [DecidableEq T] [DecidableEq M] [DecidableEq N] [Inhabited M]

/-- **SM-TCR witness search**: the first candidate `(t, m*)` (read off the forgery) for which some
recorded target `(t, mⱼ)` at the same tweak has `m* ≠ mⱼ` and the same image; output its index
`j` and `m*` (a dummy output if there is none). -/
def tcrFind (f : T → M → N) (Q : List (T × M)) (cands : List (T × M)) : ℕ × M :=
  ((cands.findSome? fun c =>
    (Q.findIdx? fun e => decide (e.1 = c.1 ∧ c.2 ≠ e.2 ∧ f e.1 c.2 = f e.1 e.2)).map
      fun j => (j, c.2)).getD (0, default))

theorem tcrWin_tcrFind (prob : SM_DT_TCR_Problem ι P T M N) (pk : P) (Q cands : List (T × M))
    (h : ∃ c ∈ cands, ∃ e ∈ Q, e.1 = c.1 ∧ c.2 ≠ e.2 ∧
      prob.th.eval pk e.1 c.2 = prob.th.eval pk e.1 e.2) :
    tcrWin prob pk Q (tcrFind (prob.th.eval pk) Q cands) = true := by
  obtain ⟨c, hc, e, he, h1, h2, h3⟩ := h
  have hsome : (cands.findSome? fun c =>
      (Q.findIdx? fun e => decide (e.1 = c.1 ∧ c.2 ≠ e.2 ∧
        prob.th.eval pk e.1 c.2 = prob.th.eval pk e.1 e.2)).map fun j => (j, c.2)).isSome := by
    rw [List.findSome?_isSome_iff]
    refine ⟨c, hc, ?_⟩
    rw [Option.isSome_map, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨e, he, by simp only [decide_eq_true_eq]; exact ⟨h1, h2, h3⟩⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨c', -, hc'⟩ := List.exists_of_findSome?_eq_some hr
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hc'
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [tcrFind, hr, Option.getD_some, tcrWin, List.getElem?_eq_getElem hlt]
  simp only [decide_eq_true_eq] at hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  simp [hp2, hp3]

/-- **S-TCR(Prop) witness search**: the first candidate `(t, m*, ctr*)` for which some recorded
entry `((t, mⱼ), (·, iⱼ))` has the same image and `m* ≠ mⱼ`. -/
def stcrFind (f : T → M × ℕ → N) (Q : List ((T × M) × (N × ℕ))) (cands : List (T × M × ℕ)) :
    ℕ × M × ℕ :=
  ((cands.findSome? fun c =>
    (Q.findIdx? fun e => decide (e.1.1 = c.1 ∧ f e.1.1 (e.1.2, e.2.2) = f e.1.1 c.2 ∧
      c.2.1 ≠ e.1.2)).map fun j => (j, c.2)).getD (0, default))

theorem stcrIsCollision_stcrFind (prob : STCRProblem ι P T M N) (pk : P)
    (Q : List ((T × M) × (N × ℕ))) (cands : List (T × M × ℕ))
    (h : ∃ c ∈ cands, ∃ e ∈ Q, e.1.1 = c.1 ∧
      prob.th.eval pk e.1.1 (e.1.2, e.2.2) = prob.th.eval pk e.1.1 c.2 ∧ c.2.1 ≠ e.1.2) :
    STCR_IsCollision prob pk Q (stcrFind (prob.th.eval pk) Q cands) = true := by
  obtain ⟨c, hc, e, he, h1, h2, h3⟩ := h
  have hsome : (cands.findSome? fun c =>
      (Q.findIdx? fun e => decide (e.1.1 = c.1 ∧
        prob.th.eval pk e.1.1 (e.1.2, e.2.2) = prob.th.eval pk e.1.1 c.2 ∧
        c.2.1 ≠ e.1.2)).map fun j => (j, c.2)).isSome := by
    rw [List.findSome?_isSome_iff]
    refine ⟨c, hc, ?_⟩
    rw [Option.isSome_map, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨e, he, by simp only [decide_eq_true_eq]; exact ⟨h1, h2, h3⟩⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨c', -, hc'⟩ := List.exists_of_findSome?_eq_some hr
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hc'
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [stcrFind, hr, Option.getD_some, STCR_IsCollision, List.getElem?_eq_getElem hlt]
  simp only [decide_eq_true_eq] at hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  simp [hp2, hp3]

end Search

/-! ## SM-TCR query programs -/

section TCRQueries

variable [DecidableEq T] (prob : SM_DT_TCR_Problem ι P T M N)

/-- The first-stage oracles of an SM-TCR problem. -/
abbrev TcrSpec := unifSpec + (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl)

/-- A challenge query `O(t, m)`. -/
def tcrChal (tm : T × M) : OracleComp (TcrSpec prob) (Option N) :=
  (TcrSpec prob).query (.inr (.inl tm))

/-- A collection query `Th_λ(i, t, m)`. -/
def tcrColl (q : (i : ι) × T × prob.thColl.Msg i) : OracleComp (TcrSpec prob) (Option N) :=
  (TcrSpec prob).query (.inr (.inr q))

theorem tcrChal_run (pk : P) (tm : T × M) (s : SM_DT_TCR_State T M) :
    (simulateQ (SM_DT_TCR_oracles prob pk) (tcrChal prob tm)).run s =
      (SM_DT_TCR_challengeOracle prob pk tm).run s := by
  simp [tcrChal, SM_DT_TCR_oracles]

theorem tcrColl_run (pk : P) (q : (i : ι) × T × prob.thColl.Msg i) (s : SM_DT_TCR_State T M) :
    (simulateQ (SM_DT_TCR_oracles prob pk) (tcrColl prob q)).run s =
      (collectionOracle (Q := T × M) Prod.fst prob.thColl pk q).run s := by
  simp [tcrColl, SM_DT_TCR_oracles]

/-- The value after `k` chained evaluations `x ↦ f (tw j) x`, `x ↦ f (tw (j+1)) x`, …. -/
def iterVal {N : Type} (f : T → N → N) (tw : ℕ → T) : ℕ → N → ℕ → N
  | _, x, 0 => x
  | j, x, k + 1 => iterVal f tw (j + 1) (f (tw j) x) k

/-- The targets `(tw (j+i), x_i)` of `k` chained challenge queries. -/
def iterTargets (f : T → M → M) (tw : ℕ → T) : ℕ → M → ℕ → List (T × M)
  | _, _, 0 => []
  | j, x, k + 1 => (tw j, x) :: iterTargets f tw (j + 1) (f (tw j) x) k

omit [DecidableEq T] in
theorem iterTargets_eq (f : T → M → M) (tw : ℕ → T) :
    ∀ (j : ℕ) (x : M) (k : ℕ),
      iterTargets f tw j x k = (List.range k).map fun i => (tw (j + i), iterVal f tw j x i)
  | j, x, 0 => rfl
  | j, x, k + 1 => by
    rw [iterTargets, iterTargets_eq f tw (j + 1) (f (tw j) x) k, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, iterVal]
    rw [show j + (i + 1) = j + 1 + i by omega]

omit [DecidableEq T] in
theorem iterTargets_map_fst (f : T → M → M) (tw : ℕ → T) (j : ℕ) (x : M) (k : ℕ) :
    (iterTargets f tw j x k).map Prod.fst = (List.range k).map fun i => tw (j + i) := by
  rw [iterTargets_eq, List.map_map]
  rfl

omit [DecidableEq T] in
theorem iterTargets_length (f : T → M → M) (tw : ℕ → T) (j : ℕ) (x : M) (k : ℕ) :
    (iterTargets f tw j x k).length = k := by
  rw [iterTargets_eq, List.length_map, List.length_range]

/-- **Sequential SM-TCR jobs.** If each job, from any state whose challenge history together with
its targets has pairwise distinct tweaks disjoint from the collection tweaks, records exactly its
targets `tg a` and collection tweaks `cw a`, then the jobs in sequence record the concatenations. -/
theorem tcr_forM_run {α : Type} (pk : P) (jobs : List α) (g : α → OracleComp (TcrSpec prob) PUnit)
    (tg : α → List (T × M)) (cw : α → List T)
    (hg : ∀ a ∈ jobs, ∀ qs tws, qs.length + (tg a).length ≤ prob.numTargets →
      ((qs ++ tg a).map Prod.fst).Nodup → (∀ t ∈ (qs ++ tg a).map Prod.fst, t ∉ tws ++ cw a) →
      (simulateQ (SM_DT_TCR_oracles prob pk) (g a)).run (qs, tws) =
        pure (PUnit.unit, (qs ++ tg a, tws ++ cw a)))
    (qs : List (T × M)) (tws : List T)
    (hcap : qs.length + (jobs.flatMap tg).length ≤ prob.numTargets)
    (hnd : ((qs ++ jobs.flatMap tg).map Prod.fst).Nodup)
    (hdis : ∀ t ∈ (qs ++ jobs.flatMap tg).map Prod.fst, t ∉ tws ++ jobs.flatMap cw) :
    (simulateQ (SM_DT_TCR_oracles prob pk) (jobs.forM g)).run (qs, tws) =
      pure (PUnit.unit, (qs ++ jobs.flatMap tg, tws ++ jobs.flatMap cw)) := by
  induction jobs generalizing qs tws with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_append] at hcap hnd
    rw [show (a :: as).forM g = (g a >>= fun _ => as.forM g) from rfl, simulateQ_bind,
      StateT.run_bind, hg a (by simp) qs tws (by omega)
        (hnd.sublist (by rw [List.map_append, ← List.append_assoc]
                         exact List.sublist_append_left _ _))
        (fun t ht => by
          have h := hdis t (by
            simp only [List.flatMap_cons, List.map_append, List.mem_append] at ht ⊢; tauto)
          simp only [List.flatMap_cons, List.mem_append, not_or] at h ⊢
          tauto), pure_bind]
    rw [ih (fun b hb => hg b (by simp [hb])) (qs ++ tg a) (tws ++ cw a)
      (by simp only [List.length_append]; omega) (by simpa [List.map_append, List.append_assoc]
        using hnd)
      (fun t ht => by
        have h := hdis t (by
          simp only [List.flatMap_cons, List.map_append, List.mem_append] at ht ⊢; tauto)
        simp only [List.flatMap_cons, List.mem_append, not_or] at h ⊢
        tauto)]
    simp [List.append_assoc]

section Chained

variable [Inhabited M] (prob : SM_DT_TCR_Problem ι P T M M)

/-- `k` **chained challenge queries** at the tweaks `tw j, …, tw (j + k − 1)`, starting from `x`,
each answer being the next message (the chains of Algorithm 8). -/
def iterChal (tw : ℕ → T) : ℕ → M → ℕ → OracleComp (TcrSpec prob) PUnit
  | _, _, 0 => pure PUnit.unit
  | j, x, k + 1 => do
    let r ← tcrChal prob (tw j, x)
    iterChal tw (j + 1) (r.getD default) k

/-- Chained challenge queries at fresh, pairwise distinct tweaks below the cap record the chain. -/
theorem iterChal_run (pk : P) (tw : ℕ → T) :
    ∀ (j : ℕ) (x : M) (k : ℕ) (qs : List (T × M)) (tws : List T),
      qs.length + k ≤ prob.numTargets →
      ((qs ++ iterTargets (prob.th.eval pk) tw j x k).map Prod.fst).Nodup →
      (∀ t ∈ (iterTargets (prob.th.eval pk) tw j x k).map Prod.fst, t ∉ tws) →
      (simulateQ (SM_DT_TCR_oracles prob pk) (iterChal prob tw j x k)).run (qs, tws) =
        pure (PUnit.unit, (qs ++ iterTargets (prob.th.eval pk) tw j x k, tws))
  | j, x, 0, qs, tws, _, _, _ => by simp [iterChal, iterTargets]
  | j, x, k + 1, qs, tws, hcap, hnd, htws => by
    simp only [iterTargets, List.map_append, List.map_cons, List.mem_cons] at hnd htws
    have hfresh : TweakFresh Prod.fst qs tws (tw j) := by
      refine ⟨(not_tweakReserved_iff _ _ _).2 fun e he h => ?_, htws _ (Or.inl rfl)⟩
      exact (List.nodup_cons.1 (List.nodup_middle.1 hnd)).1
        (List.mem_append_left _ (List.mem_map.2 ⟨e, he, h⟩))
    simp only [iterChal]
    rw [simulateQ_bind, StateT.run_bind, tcrChal_run,
      SM_DT_TCR_challengeOracle_run_of_fresh (by omega) hfresh, pure_bind, Option.getD_some,
      iterChal_run pk tw (j + 1) _ k (qs ++ [(tw j, x)]) tws (by simp; omega)
        (by simpa [List.append_assoc] using hnd) (fun t ht => htws t (Or.inr ht))]
    simp [iterTargets, List.append_assoc]

end Chained

section CollChain

variable [Inhabited N]

/-- `k` **chained collection queries** to the member `i` at the tweaks `tw j, …`, starting from
`x` (embedded into the member's message type by `emb`), each answer being the next message; the
final answer is returned. -/
def iterColl (i : ι) (emb : N → prob.thColl.Msg i) (tw : ℕ → T) :
    ℕ → N → ℕ → OracleComp (TcrSpec prob) N
  | _, x, 0 => pure x
  | j, x, k + 1 => do
    let r ← tcrColl prob ⟨i, tw j, emb x⟩
    iterColl i emb tw (j + 1) (r.getD default) k

/-- Chained collection queries at tweaks not reserved by the challenge history are answered:
they return the iterated value and append their tweaks. -/
theorem iterColl_run (pk : P) (i : ι) (emb : N → prob.thColl.Msg i) (tw : ℕ → T) :
    ∀ (j : ℕ) (x : N) (k : ℕ) (qs : List (T × M)) (tws : List T),
      (∀ e ∈ qs, ∀ n < k, e.1 ≠ tw (j + n)) →
      (simulateQ (SM_DT_TCR_oracles prob pk) (iterColl prob i emb tw j x k)).run (qs, tws) =
        pure (iterVal (fun t y => prob.thColl.eval i pk t (emb y)) tw j x k,
          (qs, tws ++ (List.range k).map fun n => tw (j + n)))
  | j, x, 0, qs, tws, _ => by simp [iterColl, iterVal]
  | j, x, k + 1, qs, tws, hres => by
    have hnew : ¬ TweakReserved Prod.fst qs (tw j) :=
      (not_tweakReserved_iff _ _ _).2 fun e he => by simpa using hres e he 0 (by omega)
    simp only [iterColl]
    rw [simulateQ_bind, StateT.run_bind, tcrColl_run,
      collectionOracle_run_of_fresh (Q := T × M) Prod.fst ⟨i, tw j, emb x⟩ hnew, pure_bind,
      Option.getD_some,
      iterColl_run pk i emb tw (j + 1) _ k qs _ fun e he n hn => by
        simpa [show j + 1 + n = j + (n + 1) by omega] using hres e he (n + 1) (by omega)]
    simp only [iterVal, List.append_assoc, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_zero, List.singleton_append]
    congr 5
    refine List.map_congr_left fun n _ => ?_
    simp only [Function.comp_apply]
    rw [show j + 1 + n = j + (n + 1) by omega]

end CollChain

/-- `List.mapM` of collection-only computations, each returning `v a` and appending `c a` to the
collection tweaks without touching the challenge history. -/
theorem tcr_mapM_run {α β : Type} (pk : P) (f : α → OracleComp (TcrSpec prob) β) (v : α → β)
    (c : α → List T) (qs : List (T × M)) :
    ∀ (as : List α), (∀ a ∈ as, ∀ tws, (simulateQ (SM_DT_TCR_oracles prob pk) (f a)).run (qs, tws) =
      pure (v a, (qs, tws ++ c a))) → ∀ tws,
      (simulateQ (SM_DT_TCR_oracles prob pk) (as.mapM f)).run (qs, tws) =
        pure (as.map v, (qs, tws ++ as.flatMap c))
  | [], _, tws => by simp
  | a :: as, h, tws => by
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, h a (by simp) tws, pure_bind,
      simulateQ_bind, StateT.run_bind,
      tcr_mapM_run pk f v c qs as (fun b hb => h b (by simp [hb])) (tws ++ c a), pure_bind]
    simp [List.append_assoc]

end TCRQueries

/-! ## S-TCR(Prop) query programs -/

section STCRQueries

variable [DecidableEq T] (prob : STCRProblem ι P T M N)

/-- The first-stage oracles of an S-TCR(Prop) problem. -/
abbrev StcrSpec := unifSpec + (STCR_challengeSpec T M N + collectionSpec prob.thColl)

/-- A challenge query `O_Prop(t, m)`. -/
def stcrChal (tm : T × M) : OracleComp (StcrSpec prob) (Option (N × ℕ)) :=
  (StcrSpec prob).query (.inr (.inl tm))

theorem stcrChal_run (pk : P) (tm : T × M) (s : STCRState T M N) :
    (simulateQ (STCR_oracles prob pk) (stcrChal prob tm)).run s =
      (STCR_challengeOracle prob pk tm).run s := by
  simp [stcrChal, STCR_oracles]

/-- The entry `((t, m), (y, i))` that `O_Prop` records on a fresh query below the cap (none if no
counter exists). -/
noncomputable def stcrRecord (pk : P) (tm : T × M) : Option ((T × M) × (N × ℕ)) :=
  (leastCounter prob.th prob.prop pk tm.1 tm.2).map fun i =>
    (tm, (prob.th.eval pk tm.1 (tm.2, i), i))

/-- The challenge queries `O_Prop(t, m)` for a list of pairs, answers discarded. -/
def stcrQueries (l : List (T × M)) : OracleComp (StcrSpec prob) PUnit :=
  l.forM fun tm => do
    let _ ← stcrChal prob tm
    pure PUnit.unit

theorem STCR_challengeOracle_run_of_fresh (pk : P) (tm : T × M) (qs : List ((T × M) × (N × ℕ)))
    (tws : List T) (hlen : qs.length < prob.numTargets)
    (hfresh : TweakFresh (fun e : (T × M) × (N × ℕ) => e.1.1) qs tws tm.1) :
    (STCR_challengeOracle prob pk tm).run (qs, tws) =
      pure ((stcrRecord prob pk tm).map Prod.snd, (qs ++ (stcrRecord prob pk tm).toList, tws)) := by
  unfold STCR_challengeOracle stcrRecord
  simp only [StateT.run_bind, StateT.run_get, pure_bind, Nat.not_le.mpr hlen, hfresh,
    not_true_eq_false, or_self, ↓reduceIte]
  cases leastCounter prob.th prob.prop pk tm.1 tm.2 <;> simp

/-- **The challenge queries of a list** with pairwise distinct tweaks, fresh for the state and
within the cap, record `stcrRecord` of each pair. -/
theorem stcrQueries_run (pk : P) :
    ∀ (l : List (T × M)) (qs : List ((T × M) × (N × ℕ))) (tws : List T),
      qs.length + l.length ≤ prob.numTargets →
      (qs.map (fun e => e.1.1) ++ l.map Prod.fst).Nodup → (∀ t ∈ l.map Prod.fst, t ∉ tws) →
      (simulateQ (STCR_oracles prob pk) (stcrQueries prob l)).run (qs, tws) =
        pure (PUnit.unit, (qs ++ l.filterMap (stcrRecord prob pk), tws))
  | [], qs, tws, _, _, _ => by simp [stcrQueries]
  | tm :: l, qs, tws, hcap, hnd, htws => by
    simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hnd htws
    have hfresh : TweakFresh (fun e : (T × M) × (N × ℕ) => e.1.1) qs tws tm.1 := by
      refine ⟨(not_tweakReserved_iff _ _ _).2 fun e he h => ?_, htws.1⟩
      exact (List.nodup_cons.1 (List.nodup_middle.1 hnd)).1
        (List.mem_append_left _ (List.mem_map.2 ⟨e, he, h⟩))
    have hrest := stcrQueries_run pk l (qs ++ (stcrRecord prob pk tm).toList) tws
      (by cases stcrRecord prob pk tm <;> simp at hcap ⊢ <;> omega)
      (by
        have h' := List.nodup_middle.1 hnd
        cases hr : stcrRecord prob pk tm with
        | none => simpa using (List.nodup_cons.1 h').2
        | some r =>
          have hr1 : r.1 = tm := by
            unfold stcrRecord at hr
            obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hr
            rfl
          simpa [hr1, List.append_assoc] using List.nodup_middle.2 h')
      htws.2
    rw [show stcrQueries prob (tm :: l) =
        (stcrChal prob tm >>= fun _ => pure PUnit.unit) >>= fun _ => stcrQueries prob l from rfl,
      simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, stcrChal_run,
      STCR_challengeOracle_run_of_fresh prob pk tm qs tws (by simp at hcap; omega) hfresh]
    simp only [pure_bind, simulateQ_pure, StateT.run_pure]
    rw [hrest]
    rcases hr : stcrRecord prob pk tm with _ | r <;> simp [hr]

end STCRQueries

end ShrincsSecurity.Fxmss

/-! ## The block game `F.3_γ` seen by a two-stage reduction -/

namespace ShrincsSecurity.Fxmss.Rom

open OracleComp OracleSpec ENNReal
open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {P : Params}

/-! ### Anchors -/

theorem mem_anchorList {S : Structure} {id : LeafId} :
    id ∈ anchorList P S ↔ id ∈ leafIds P.hsf S :=
  Finset.mem_toList

theorem nodup_anchorList (S : Structure) : (anchorList P S).Nodup :=
  Finset.nodup_toList _

theorem length_anchorList (S : Structure) : (anchorList P S).length = (leafIds P.hsf S).card :=
  Finset.length_toList _

/-- The leaf identifier of an anchor of a valid structure is addressable: `z < 256`, `i < 2^64`. -/
theorem leafId_bounds (hP : P.Valid) {S : Structure} (hS : S.TreeValid P.hsf) {id : LeafId}
    (h : id ∈ leafIds P.hsf S) : id.height < 256 ∧ id.index < 2 ^ 64 := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  have := hP.hsf_le
  exact ⟨by simp only [Node.toLeafId]; omega, hS.anchor_idx_lt v hv⟩

/-! ### Grinding and the honest data of `F.3_γ` -/

section Honest

variable (pr : Primitives P)

/-- **Conjecture 3.1 at the anchors**: the counter search of every anchor of a valid structure
succeeds. -/
theorem grind_eq_some (hP : P.Valid) (hgc : GrindComplete pr) {S : Structure}
    (hS : S.TreeValid P.hsf) {id : LeafId} (h : id ∈ leafIds P.hsf S) (pk : pr.PkSeed)
    (md : pr.Digest) : ∃ c, WotsC.grind pr pk id md = some (WotsC.encode pr pk id md c, c) := by
  obtain ⟨h1, h2⟩ := leafId_bounds hP hS h
  have hex : ∃ ctr, WotsC.TargetSum pr (WotsC.encode pr pk id md ctr) :=
    hgc pk (⟨id.height, h1⟩, ⟨id.index, h2⟩) md
  exact ⟨_, by unfold WotsC.grind; rw [dite_eq_left_of_eq_true (eq_true hex)]⟩

variable {S : Structure} {pk : pr.PkSeed} {dig : LeafId → pr.Digest}
  {β : LeafId → ℕ → ℕ → pr.Y} {id : LeafId} {d : pr.Y} {c : Fin (2 ^ P.c)}

theorem hon_pk : (hon pr S pk dig β).pk = pk := rfl

theorem hon_wots (hg : WotsC.grind pr pk id (dig id) = some (d, c)) :
    (hon pr S pk dig β).wots id = blockSig pr β id d c := by
  simp [hon, hg]

theorem hon_encoded (hg : WotsC.grind pr pk id (dig id) = some (d, c)) :
    (hon pr S pk dig β).encoded id = d := by
  have h := ((WotsC.grind_eq_some_iff pr).1 hg).1
  rw [Honest.encoded, hon_wots pr hg]
  exact h.symm

theorem hon_block (hg : WotsC.grind pr pk id (dig id) = some (d, c)) (ch : Fin P.lsf) :
    (hon pr S pk dig β).block id ch = β id ch.val (WotsC.digit pr d ch.val) := by
  simp [Honest.block, hon_wots pr hg, blockSig]

variable [Inhabited pr.Y]

theorem betaOf_zero {u : SkIdx P S → pr.Y} (id : LeafId) (ch a : ℕ) :
    betaOf pr 0 pk u id ch a = WotsC.chain pr pk id ch (skOf pr S u id ch) 0 a := by
  simp [betaOf, blockVal]

/-- In `F.3_0` (secret key `u`) the honest chain value at `p ≥ a` is `c_{0,p}(u)`. -/
theorem hon0_chainValue {u : SkIdx P S → pr.Y} (hg : WotsC.grind pr pk id (dig id) = some (d, c))
    (ch : Fin P.lsf) {p : ℕ} (hp : WotsC.digit pr d ch.val ≤ p) :
    (hon pr S pk dig (betaOf pr 0 pk u)).chainValue id ch p =
      WotsC.chain pr pk id ch.val (skOf pr S u id ch.val) 0 p := by
  rw [Honest.chainValue, hon_block pr hg, hon_encoded pr hg, betaOf_zero, hon_pk]
  have h := WotsC.chain_compose pr pk id ch.val (skOf pr S u id ch.val) 0
    (WotsC.digit pr d ch.val) (p - WotsC.digit pr d ch.val)
  rw [Nat.zero_add] at h
  rw [h, Nat.add_sub_cancel' hp]

/-- In `F.3_0` the honest uncompressed public key is `c_{0,w−1}(u)`. -/
theorem hon0_tops {u : SkIdx P S → pr.Y} (hg : WotsC.grind pr pk id (dig id) = some (d, c)) :
    (hon pr S pk dig (betaOf pr 0 pk u)).tops id = WotsC.pkTops pr pk id (skOf pr S u id) := by
  apply Vector.ext
  intro i hi
  have hb := hon_block pr (β := betaOf pr 0 pk u) (S := S) hg ⟨i, hi⟩
  simp only at hb
  simp only [Honest.tops, WotsC.topsFromSig, Vector.getElem_ofFn, WotsC.pkTops, hon_encoded pr hg,
    hon_pk]
  rw [show (hon pr S pk dig (betaOf pr 0 pk u)).wots id |>.chains[i] =
    (hon pr S pk dig (betaOf pr 0 pk u)).block id ⟨i, hi⟩ from rfl, hb, betaOf_zero]
  have h := WotsC.chain_compose pr pk id i (skOf pr S u id i) 0 (WotsC.digit pr d i)
    (P.w - 1 - WotsC.digit pr d i)
  rw [Nat.zero_add] at h
  rw [h, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (WotsC.digit_lt pr d i))]

/-- The `SF_WOTS_C_HASH` tweak of chain `ch` at hash address `p` of the instance `id`. -/
def chainTw (id : LeafId) (ch p : ℕ) : SLHDSA.Adrs := (SfAdrs.chainAdrs id ch p).toAdrs

theorem chainTw_inj {id id' : LeafId} {ch ch' p p' : ℕ} :
    chainTw id ch p = chainTw id' ch' p' ↔ id = id' ∧ ch = ch' ∧ p = p' :=
  SfAdrs.chainAdrs_inj

/-- The chain tweaks `chainTw id ch p`, `p < k`, of a list of pairwise distinct `(id, ch)` are
pairwise distinct. -/
theorem nodup_flatMap_chainTw {l : List (LeafId × ℕ)} (hl : l.Nodup) (k : ℕ) :
    (l.flatMap fun a => (List.range k).map fun i => chainTw a.1 a.2 (0 + i)).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => List.nodup_range.map fun i j h => ?_, hl.imp ?_⟩
  · simpa using (chainTw_inj.1 h).2.2
  · intro a b hab x hxa hxb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hxa
    obtain ⟨j, -, hj⟩ := List.mem_map.1 hxb
    obtain ⟨h1, h2, -⟩ := chainTw_inj.1 hj
    exact hab (Prod.ext h1.symm h2.symm)

omit [Inhabited pr.Y] in
/-- Chained evaluations of `F` at the hash addresses `j, j + 1, …` of chain `ch` are the WOTS+C
chain `c_{j,k}`. -/
theorem iterVal_chain (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (f : SLHDSA.Adrs → pr.Y → pr.Y)
    (hf : ∀ t y, f t y = pr.F pk t y) :
    ∀ (j : ℕ) (x : pr.Y) (k : ℕ), iterVal f (chainTw id ch) j x k = WotsC.chain pr pk id ch x j k
  | j, x, 0 => rfl
  | j, x, k + 1 => by
    rw [iterVal, iterVal_chain pk id ch f hf (j + 1) _ k, hf]
    have h := WotsC.chain_compose pr pk id ch x j 1 k
    rw [WotsC.chain_succ, WotsC.chain_zero, Nat.add_zero] at h
    rw [chainTw, h, Nat.add_comm]

end Honest

/-! ### Candidates read off the forgery -/

section Cands

variable (pr : Primitives P) (Msg : Type)

/-- The witness candidates `f(H, (z*, i*), y*, σ*_tree)` of a block-game output (none for `⊥`
or a `⊥` forgery signature). -/
def forgeryCands {α : Type} (f : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → List α) :
    Option (Transcript pr Msg × Honest pr) → List α
  | some (tr, H) => match tr.σf.2 with
    | some w => f H tr.idf tr.yf w
    | none => []
  | none => []

theorem forgeryCands_some {α : Type}
    (f : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → List α) {tr : Transcript pr Msg}
    {H : Honest pr} {w : Scheme.Fxmss.Sig pr} (hw : tr.σf.2 = some w) :
    forgeryCands pr Msg f (some (tr, H)) = f H tr.idf tr.yf w := by
  simp [forgeryCands, hw]

end Cands

/-! ### Support of the setup and of the signing phase -/

section Support

variable (pr : Primitives P) (Msg : Type)
  [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.Digest] [Inhabited pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

omit [Inhabited pr.Digest] [Nontrivial Msg] in
/-- A reachable setup with a valid structure has at most `L` anchors (`Forger.anchors_le`). -/
theorem setupHyb_length_anchorList_le {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    {d : Setup pr Msg A.State} (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary))
    (hS : d.S.TreeValid P.hsf) : (anchorList P d.S).length ≤ L := by
  unfold setupHyb at hd
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hd
  obtain ⟨z, hz, ys, -, u, -, rfl⟩ := hd
  rw [length_anchorList, hS.card_leafIds]
  exact A.anchors_le z.1 (OracleComp.mem_support_of_mem_support_simulateQ_run _ _ _ hz) hS

/-- A reachable output of the signing phase of `F.3_γ` is `⊥` or carries the honest data
`hon(S, PK.seed, y, β)` of a valid structure. -/
theorem mem_support_stageHyb {qs : ℕ} {A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs}
    {β : LeafId → ℕ → ℕ → pr.Y} {d : Setup pr Msg A.State} {pk : pr.PkSeed}
    {o : Option (Transcript pr Msg × Honest pr)}
    (ho : o ∈ support (stageHyb pr Msg slKeygen A β d pk)) :
    o = none ∨ (d.S.TreeValid P.hsf ∧ ∃ tr, o = some (tr, hon pr d.S pk (digOf pr d.ys) β)) := by
  unfold stageHyb at ho
  by_cases hS : d.S.TreeValid P.hsf
  · right
    refine ⟨hS, ?_⟩
    simp only [hS, not_true_eq_false, ↓reduceIte, mem_support_bind_iff] at ho
    obtain ⟨_, -, ho⟩ := ho
    obtain ⟨_, -, ho⟩ := ho
    rw [support_pure, Set.mem_singleton_iff] at ho
    exact ⟨_, ho⟩
  · left
    simp only [hS, not_false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at ho
    exact ho

/-- **From `F.3_γ` to a two-stage reduction.** Write the reduction's second stage as the signing
phase of `F.3_γ` followed by an extraction `ext`. If, on every reachable setup with a valid
structure, the event `E` of a forgery against the honest data implies the reduction's winning
condition on the extraction, the event's probability in `F.3_γ` is at most the probability of the
winning condition in `PK.seed ←$; d ← setup; out ← ext <$> stage`. -/
theorem prEvent_gameHyb_le {qs : ℕ} (γ : ℕ) (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (E : Honest pr → LeafId → pr.Digest → Scheme.Fxmss.Sig pr → Prop) {Out : Type}
    (ext : Setup pr Msg A.State → pr.PkSeed → Option (Transcript pr Msg × Honest pr) → Out)
    (win : Setup pr Msg A.State → pr.PkSeed → Out → Prop)
    (h : ∀ pk, ∀ d ∈ support (setupHyb pr Msg slKeygen A), d.S.TreeValid P.hsf →
      ∀ (tr : Transcript pr Msg) (w : Scheme.Fxmss.Sig pr), tr.σf.2 = some w →
      E (hon pr d.S pk (digOf pr d.ys) (betaOf pr γ pk d.u)) tr.idf tr.yf w →
      win d pk (ext d pk (some (tr, hon pr d.S pk (digOf pr d.ys) (betaOf pr γ pk d.u))))) :
    Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent E o] ≤
      Pr{let pk ← $ᵗ pr.PkSeed
         let d ← setupHyb pr Msg slKeygen A
         let o ← ext d pk <$> stageHyb pr Msg slKeygen A (betaOf pr γ pk d.u) d pk}[win d pk o] := by
  have key : ∀ {α : Type} (mx : ProbComp α) (F G : α → ProbComp Prop),
      (∀ x ∈ support mx, prEvent (F x) ≤ prEvent (G x)) → prEvent (mx >>= F) ≤ prEvent (mx >>= G) :=
    fun mx F G hFG => by
      simpa using prEvent_bind_mono_of_forall_le_of_support mx F G id id
        (fun x hx => by simpa using hFG x hx)
  unfold gameHyb
  simp only [map_bind]
  refine key _ _ _ fun pk _ => key _ _ _ fun d hd => ?_
  rw [Functor.map_map]
  refine prEvent_mono_of_support _ _ (fun o => win d pk (ext d pk o)) fun o ho hE => ?_
  rcases mem_support_stageHyb pr Msg slKeygen ho with rfl | ⟨hS, tr, rfl⟩
  · exact hE.elim
  · obtain ⟨w, hw, hE⟩ := hE
    exact h pk d hd hS tr w hw hE

end Support

end ShrincsSecurity.Fxmss.Rom

end
