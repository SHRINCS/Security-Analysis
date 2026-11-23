module

public import ShrincsSecurity.Fxmss.Reduction
public import ShrincsSecurity.Fxmss.Members

/-!
# Query programs over the tree of a structure (helpers for Claims 4.8 and 4.9)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, Algorithms 11 and 12 (the first stages of `B₇` and
`B₈`): with `PK.seed` hidden, the reduction recomputes the honest FXMSS tree of `F.3` (secret key
`u`) through its oracles: every chain step through the collection oracle (`F`), every anchor
compression `Th_lsf` through the collection (`B₇`) or the challenge oracle (`B₈`), and every
internal node `H` through the challenge oracle, bottom-up.

* **Permissive semantics.** `simulateQ_run_eq_pure_of_perm`: if a deterministic "permissive"
  handler (answer every query, append it to a log) reaches a final log satisfying a
  prefix-closed condition `Good`, and on every query whose resulting log is `Good` the game's
  handler answers as the permissive one, then the game's handler runs the program
  deterministically to the same result. `tcrPerm`/`tcr_run_eq` and `exclPerm`/`excl_run_eq`
  instantiate this for the SM-TCR and sm-tcr-excl oracles: a final log whose challenge tweaks are
  pairwise fresh (distinct, resp. outside each other's `Ω`), within the cap, and disjoint from the
  collection tweaks, is never refused.
* **Logs.** `IsLog x v q c`: the state program `x` returns `v` and appends `q` and `c` to the two
  logs, from every state.
* **The tree program.** `treeNodeM` is `Tree.treeNode` with monadic leaf and node operations
  (`chainM`, `topsM`, `leafM` compute an anchor value `WOTS+C.pkGen` through `F` and `Th_lsf`
  operations); `treeOrder` lists the anchors (`inl`) and internal nodes (`inr`) in the order the
  program visits them (post-order). `treeNodeM_isLog`: with logging operations, the program
  returns the honest tree value and its logs are the concatenated per-position entries.
  `nodup_treeOrder` and `visit_mem_treeOrder` (valid structures): every anchor and internal node
  is visited exactly once; `nodup_map_flatMap`: logs with one entry per position, keyed by the
  node identifier (`nodeKey`), have distinct keys.
* **The witness search.** `exclFind`/`exclIsCollision_exclFind`: the sm-tcr-excl analogue of
  `tcrFind` (a bounded search over candidates read off the forgery).
* **The honest data of `F.3`.** `hon_zero_leafVal`, `hon_zero_value`, `hon_zero_tops`: in
  `gameHyb 0` the anchor values are `WOTS+C.pkGen(u)`, the tree is the FXMSS tree of `u`, and
  (under Conjecture 3.1) the uncompressed public keys are `c_{0,w−1}(u)`. `stageHyb_support`: every
  output of the signing phase carries the honest data of its setup, on a valid structure.
  `anchors_le_of_mem_support_setupHyb`: the forger's structure has at most `L` anchors on every
  reachable setup. `prEvent_bind_mono'`: event comparison under a common draw.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Fxmss

open Notions

/-! ## Deterministic runs from a permissive semantics -/

section Perm

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- A permissive run only extends the state (for a reflexive, transitive extension relation
respected by every query). -/
theorem simulateQ_perm_ext (perm : QueryImpl spec (StateM σ)) (Ext : σ → σ → Prop)
    (hrefl : ∀ s, Ext s s) (htrans : ∀ a b c, Ext a b → Ext b c → Ext a c)
    (hext : ∀ t s, Ext s ((perm t).run s).2) (oa : OracleComp spec α) (s : σ) :
    Ext s ((simulateQ perm oa).run s).2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => exact hrefl s
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact htrans _ _ _ (hext t s) (ih _ _)

/-- **Deterministic runs.** If the final state of the permissive run is `Good` (a condition
closed under restriction to earlier states), and the game's handler answers as the permissive
one whenever the resulting state is `Good`, then the game's handler runs the program to the
permissive result. -/
theorem simulateQ_run_eq_pure_of_perm (real : QueryImpl spec (StateT σ ProbComp))
    (perm : QueryImpl spec (StateM σ)) (Good : σ → Prop) (Ext : σ → σ → Prop)
    (hrefl : ∀ s, Ext s s) (htrans : ∀ a b c, Ext a b → Ext b c → Ext a c)
    (hmono : ∀ s s', Ext s s' → Good s' → Good s)
    (hext : ∀ t s, Ext s ((perm t).run s).2)
    (hstep : ∀ t s, Good ((perm t).run s).2 → (real t).run s = pure ((perm t).run s))
    (oa : OracleComp spec α) (s : σ) (hgood : Good ((simulateQ perm oa).run s).2) :
    (simulateQ real oa).run s = pure ((simulateQ perm oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hgood ⊢
    have h1 : Good ((perm t).run s).2 :=
      hmono _ _ (simulateQ_perm_ext perm Ext hrefl htrans hext _ _) hgood
    rw [hstep t s h1, pure_bind, ih _ _ hgood]
    rfl

end Perm

/-- A comparison of events on every reachable continuation survives a common draw (stated on
`Prop`-valued computations, the normal form of `Pr{let a ← mx; …}[…]`). -/
theorem prEvent_bind_mono' {α : Type} (mx : ProbComp α) (F G : α → ProbComp Prop)
    (h : ∀ a ∈ support mx, prEvent (F a) ≤ prEvent (G a)) :
    prEvent (mx >>= F) ≤ prEvent (mx >>= G) := by
  have := prEvent_bind_mono_of_forall_le_of_support mx F G (fun y => y) (fun y => y)
    (by simpa using h)
  simpa using this

/-! ## The permissive semantics of the SM-TCR and sm-tcr-excl oracles -/

section Games

variable {ι P T M N α : Type}

/-- `pure` in `Id` is the value itself. -/
theorem id_pure_eq {β : Type} (b : β) : (pure b : Id β) = b := rfl

/-- The state of the first stage: the challenge history and the collection tweaks. -/
abbrev LogSt (T M : Type) : Type := List (T × M) × List T

/-- Extension of a state by appending to both logs. -/
def LogExt (s s' : LogSt T M) : Prop := s.1 <+: s'.1 ∧ s.2 <+: s'.2

theorem LogExt.refl (s : LogSt T M) : LogExt s s := ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem LogExt.trans {a b c : LogSt T M} (h₁ : LogExt a b) (h₂ : LogExt b c) : LogExt a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- The permissive SM-TCR handler: every query is answered and logged. -/
def tcrPerm (prob : SM_DT_TCR_Problem ι P T M N) (pk : P) :
    QueryImpl (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl) (StateM (LogSt T M)) :=
  (fun tm => (StateT.mk fun s => pure (some (prob.th.eval pk tm.1 tm.2), (s.1 ++ [tm], s.2)) :
    StateM (LogSt T M) (Option N)) : QueryImpl (SM_DT_TCR_challengeSpec T M N) _) +
  (fun q => (StateT.mk fun s =>
    pure (some (prob.thColl.eval q.1 pk q.2.1 q.2.2), (s.1, s.2 ++ [q.2.1])) :
    StateM (LogSt T M) (Option N)) : QueryImpl (collectionSpec prob.thColl) _)

/-- A final SM-TCR log that no oracle refuses: distinct challenge tweaks, within the cap, and
disjoint from the collection tweaks. -/
def TcrGood (cap : ℕ) (s : LogSt T M) : Prop :=
  (s.1.map Prod.fst).Nodup ∧ s.1.length ≤ cap ∧ ∀ t ∈ s.2, t ∉ s.1.map Prod.fst

theorem TcrGood.mono {cap : ℕ} {s s' : LogSt T M} (h : LogExt s s') (hg : TcrGood cap s') :
    TcrGood cap s := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hn, hl, hc⟩ := hg
  refine ⟨hn.sublist (h1.sublist.map _), (h1.sublist.length_le).trans hl, fun t ht hq => ?_⟩
  exact hc t (h2.sublist.subset ht) ((h1.sublist.map _).subset hq)

/-- **The SM-TCR oracles run a program deterministically** when its permissive log is `TcrGood`. -/
theorem tcr_run_eq [DecidableEq T] (prob : SM_DT_TCR_Problem ι P T M N) (pk : P)
    (oa : OracleComp (SM_DT_TCR_challengeSpec T M N + collectionSpec prob.thColl) α)
    (hgood : TcrGood prob.numTargets ((simulateQ (tcrPerm prob pk) oa).run ([], [])).2) :
    (simulateQ (SM_DT_TCR_oracles prob pk)
      (OracleComp.liftComp oa (unifSpec + (SM_DT_TCR_challengeSpec T M N +
        collectionSpec prob.thColl)))).run ([], []) =
      pure ((simulateQ (tcrPerm prob pk) oa).run ([], [])) := by
  rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_right]
  refine simulateQ_run_eq_pure_of_perm _ (tcrPerm prob pk) (TcrGood prob.numTargets) LogExt
    LogExt.refl (fun _ _ _ => LogExt.trans) (fun _ _ h hg => hg.mono h) ?_ ?_ oa _ hgood
  · rintro (tm | q) s
    · exact ⟨List.prefix_append _ _, List.prefix_refl _⟩
    · exact ⟨List.prefix_refl _, List.prefix_append _ _⟩
  · rintro (⟨t, m⟩ | q) ⟨Q, C⟩ hg
    · obtain ⟨hn, hl, hc⟩ := hg
      simp only [tcrPerm, QueryImpl.add_apply_inl, StateT.run_mk, id_pure_eq, List.map_append,
        List.map_cons, List.map_nil, List.length_append, List.length_singleton] at hn hl hc ⊢
      have hnot : t ∉ Q.map Prod.fst := fun h => (List.nodup_append.1 hn).2.2 _ h _ (by simp) rfl
      rw [SM_DT_TCR_challengeOracle_run_of_fresh (by omega)
        ⟨by
          rw [not_tweakReserved_iff]
          exact fun e he het => hnot (List.mem_map.2 ⟨e, he, het⟩),
          fun htC => hc t htC (by simp)⟩]
    · obtain ⟨-, -, hc⟩ := hg
      simp only [tcrPerm, QueryImpl.add_apply_inr, StateT.run_mk, id_pure_eq] at hc ⊢
      rw [collectionOracle_run_of_fresh _ _ (by
        rw [not_tweakReserved_iff]
        intro e he heq
        exact hc q.2.1 (by simp) (List.mem_map.2 ⟨e, he, heq⟩))]

/-- The permissive sm-tcr-excl handler. -/
def exclPerm (prob : SMTCRExclProblem ι P T M N) (pk : P) :
    QueryImpl (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl)
      (StateM (LogSt T M)) :=
  (fun tm => (StateT.mk fun s => pure (some (prob.th.eval pk tm.1 tm.2), (s.1 ++ [tm], s.2)) :
    StateM (LogSt T M) (Option N)) : QueryImpl (SMTCRExcl_challengeSpec T M N) _) +
  (fun q => (StateT.mk fun s =>
    pure (some (prob.thColl.eval q.1 pk q.2.1 q.2.2), (s.1, s.2 ++ [q.2.1])) :
    StateM (LogSt T M) (Option N)) : QueryImpl (collectionSpec prob.thColl) _)

/-- A final sm-tcr-excl log that no oracle refuses: every challenge tweak outside `Ω` of the
earlier ones, within the cap, and every collection tweak outside `Ω` of every challenge tweak. -/
def ExclGood (X : ExclusiveTweaks T) (cap : ℕ) (s : LogSt T M) : Prop :=
  s.1.Pairwise (fun e e' => e'.1 ∉ X.Omega e.1) ∧ s.1.length ≤ cap ∧
    ∀ t ∈ s.2, ∀ e ∈ s.1, t ∉ X.Omega e.1

theorem ExclGood.mono {X : ExclusiveTweaks T} {cap : ℕ} {s s' : LogSt T M} (h : LogExt s s')
    (hg : ExclGood X cap s') : ExclGood X cap s := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hp, hl, hc⟩ := hg
  exact ⟨hp.sublist h1.sublist, (h1.sublist.length_le).trans hl,
    fun t ht e he => hc t (h2.sublist.subset ht) e (h1.sublist.subset he)⟩

/-- **The sm-tcr-excl oracles run a program deterministically** when its permissive log is
`ExclGood`. -/
theorem excl_run_eq [DecidableEq T] (prob : SMTCRExclProblem ι P T M N) (pk : P)
    (oa : OracleComp (SMTCRExcl_challengeSpec T M N + collectionSpec prob.thColl) α)
    (hgood : ExclGood prob.X prob.numTargets ((simulateQ (exclPerm prob pk) oa).run ([], [])).2) :
    (simulateQ (SMTCRExcl_oracles prob pk)
      (OracleComp.liftComp oa (unifSpec + (SMTCRExcl_challengeSpec T M N +
        collectionSpec prob.thColl)))).run ([], []) =
      pure ((simulateQ (exclPerm prob pk) oa).run ([], [])) := by
  rw [SMTCRExcl_oracles, QueryImpl.simulateQ_add_liftComp_right]
  refine simulateQ_run_eq_pure_of_perm _ (exclPerm prob pk) (ExclGood prob.X prob.numTargets)
    LogExt LogExt.refl (fun _ _ _ => LogExt.trans) (fun _ _ h hg => hg.mono h) ?_ ?_ oa _ hgood
  · rintro (tm | q) s
    · exact ⟨List.prefix_append _ _, List.prefix_refl _⟩
    · exact ⟨List.prefix_refl _, List.prefix_append _ _⟩
  · rintro (⟨t, m⟩ | q) ⟨Q, C⟩ hg
    · obtain ⟨hp, hl, hc⟩ := hg
      simp only [exclPerm, QueryImpl.add_apply_inl, StateT.run_mk, id_pure_eq, List.length_append,
        List.length_singleton] at hp hl hc ⊢
      rw [SMTCRExcl_challengeOracle_run_of_fresh (by omega)
        (fun ⟨e, he, hte⟩ => (List.pairwise_append.1 hp).2.2 e he (t, m) (by simp) hte)
        (fun ⟨c, hcC, hct⟩ => hc c hcC (t, m) (by simp) hct)]
    · obtain ⟨-, -, hc⟩ := hg
      simp only [exclPerm, QueryImpl.add_apply_inr, StateT.run_mk, id_pure_eq] at hc ⊢
      have hres : ¬ ExclReserved prob.X Q q.2.1 := fun ⟨e, he, hte⟩ =>
        hc q.2.1 (by simp) e he hte
      simp [SMTCRExcl_collectionOracle, hres]

end Games

/-! ## The sm-tcr-excl witness search -/

section ExclSearch

variable {ι P T M N : Type} [DecidableEq T] [DecidableEq M] [DecidableEq N]

/-- **sm-tcr-excl witness search**: the first candidate `(t, T*, m*)` (read off the forgery) for
which some recorded target `(t, mⱼ)` has `T* ∈ Ω(t)`, `m* ≠ mⱼ` and `Th(t, mⱼ) = Th(T*, m*)`;
output its index `j`, `T*` and `m*` (the output `dflt` if there is none). -/
def exclFind (f : T → M → N) (X : ExclusiveTweaks T) (Q : List (T × M))
    (cands : List (T × T × M)) (dflt : ℕ × T × M) : ℕ × T × M :=
  ((cands.findSome? fun c =>
    (Q.findIdx? fun e => decide (e.1 = c.1 ∧ (c.2.1 = e.1 ∨ c.2.1 = X.partner e.1) ∧
      c.2.2 ≠ e.2 ∧ f e.1 e.2 = f c.2.1 c.2.2)).map fun j => (j, c.2.1, c.2.2)).getD dflt)

theorem exclIsCollision_exclFind (prob : SMTCRExclProblem ι P T M N) (pk : P)
    (Q : List (T × M)) (cands : List (T × T × M)) (dflt : ℕ × T × M)
    (h : ∃ c ∈ cands, ∃ e ∈ Q, e.1 = c.1 ∧ c.2.1 ∈ prob.X.Omega e.1 ∧ c.2.2 ≠ e.2 ∧
      prob.th.eval pk e.1 e.2 = prob.th.eval pk c.2.1 c.2.2) :
    SMTCRExcl_IsCollision prob pk Q (exclFind (prob.th.eval pk) prob.X Q cands dflt) = true := by
  obtain ⟨c, hc, e, he, h1, h2, h3, h4⟩ := h
  have hsome : (cands.findSome? fun c =>
      (Q.findIdx? fun e => decide (e.1 = c.1 ∧ (c.2.1 = e.1 ∨ c.2.1 = prob.X.partner e.1) ∧
        c.2.2 ≠ e.2 ∧ prob.th.eval pk e.1 e.2 = prob.th.eval pk c.2.1 c.2.2)).map
        fun j => (j, c.2.1, c.2.2)).isSome := by
    rw [List.findSome?_isSome_iff]
    refine ⟨c, hc, ?_⟩
    rw [Option.isSome_map, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨e, he, by simp only [decide_eq_true_eq]; exact ⟨h1, h2, h3, h4⟩⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨c', -, hc'⟩ := List.exists_of_findSome?_eq_some hr
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 hc'
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  simp only [exclFind, hr, Option.getD_some, SMTCRExcl_IsCollision, List.getElem?_eq_getElem hlt]
  simp only [decide_eq_true_eq] at hp
  obtain ⟨-, hp2, hp3, hp4⟩ := hp
  simp only [decide_eq_true_eq]
  exact ⟨hp2, hp3, hp4⟩

end ExclSearch

/-! ## Logging state programs -/

section Log

variable {α β γ δ : Type}

theorem id_bind_eq {ε : Type} (b : β) (g : β → Id ε) : (b >>= g : Id ε) = g b := rfl

theorem id_map_eq {ε : Type} (b : β) (g : β → ε) : (g <$> b : Id ε) = g b := rfl

/-- `x` returns `v` and appends `q` and `c` to the two logs, from every state. -/
def IsLog (x : StateM (List α × List β) γ) (v : γ) (q : List α) (c : List β) : Prop :=
  ∀ s, x.run s = (v, (s.1 ++ q, s.2 ++ c))

theorem IsLog.of_eq {x : StateM (List α × List β) γ} {v v' : γ} {q q' : List α}
    {c c' : List β} (h : IsLog x v q c) (hv : v = v') (hq : q = q') (hc : c = c') :
    IsLog x v' q' c' := hv ▸ hq ▸ hc ▸ h

theorem IsLog.pure (v : γ) : IsLog (pure v : StateM (List α × List β) γ) v [] [] := by
  intro s
  simp [StateT.run_pure, id_pure_eq]

theorem IsLog.bind {x : StateM (List α × List β) γ} {f : γ → StateM (List α × List β) δ}
    {v : γ} {w : δ} {q q' : List α} {c c' : List β} (hx : IsLog x v q c)
    (hf : IsLog (f v) w q' c') : IsLog (x >>= f) w (q ++ q') (c ++ c') := by
  intro s
  rw [StateT.run_bind, hx s, id_bind_eq, hf]
  simp

theorem IsLog.map {x : StateM (List α × List β) γ} {v : γ} {q : List α} {c : List β}
    (hx : IsLog x v q c) (g : γ → δ) : IsLog (g <$> x) (g v) q c := by
  intro s
  rw [StateT.run_map, hx s, id_map_eq]

theorem IsLog.mapM {ε : Type} {l : List ε} {f : ε → StateM (List α × List β) γ} {val : ε → γ}
    {q : ε → List α} {c : ε → List β} (h : ∀ a ∈ l, IsLog (f a) (val a) (q a) (c a)) :
    IsLog (l.mapM f) (l.map val) (l.flatMap q) (l.flatMap c) := by
  induction l with
  | nil => simpa using IsLog.pure (α := α) (β := β) ([] : List γ)
  | cons a l ih =>
    intro s
    have ih' := ih fun b hb => h b (by simp [hb])
    rw [List.mapM_cons, StateT.run_bind, h a (by simp) s, id_bind_eq, StateT.run_bind, ih',
      id_bind_eq, StateT.run_pure]
    simp only [List.append_assoc, List.map_cons, List.flatMap_cons]
    rfl

end Log

/-! ## The tree program -/

section Programs

open Scheme

variable {P : Params} (pr : Primitives P) {m : Type → Type} [Monad m]

/-- The chain `c_{0,k}(x)` of chain `ch` at `id`, one `F` operation per step (at the
`SF_WOTS_C_HASH` address of the step). -/
def chainM (fOp : SLHDSA.Adrs → pr.Y → m pr.Y) (id : LeafId) (ch : ℕ) (x : pr.Y) : ℕ → m pr.Y
  | 0 => pure x
  | k + 1 => do
    let y ← chainM fOp id ch x k
    fOp (SfAdrs.chainAdrs id ch k).toAdrs y

variable [Inhabited pr.Y]

/-- The uncompressed WOTS+C public key `c_{0,w−1}(x_ch)`, `ch < lsf`, of the instance at `id`. -/
def topsM (fOp : SLHDSA.Adrs → pr.Y → m pr.Y) (id : LeafId) (x : ℕ → pr.Y) :
    m (Vector pr.Y P.lsf) := do
  let l ← (List.finRange P.lsf).mapM fun ch => chainM pr fOp id ch.val (x ch.val) (P.w - 1)
  return Vector.ofFn fun ch => l.getD ch.val default

/-- The anchor value `WOTS+C.pkGen(x)`: the chains, then the compression operation at
`ADRS^pk`. -/
def leafM (fOp : SLHDSA.Adrs → pr.Y → m pr.Y) (cOp : SLHDSA.Adrs → Vector pr.Y P.lsf → m pr.Y)
    (x : LeafId → ℕ → pr.Y) (id : LeafId) : m pr.Y := do
  let v ← topsM pr fOp id (x id)
  cOp (SfAdrs.pkAdrs id).toAdrs v

/-- Combine two optional children values with a node operation. -/
def combineM {Y : Type} (f : Y → Y → m Y) : Option Y → Option Y → m (Option Y)
  | some a, some b => some <$> f a b
  | _, _ => pure none

/-- **`treeNode_structure` with monadic operations**: `Tree.treeNode` where the anchor values and
the node hashes are computed by `leafOp` and `nodeOp` (left subtree, right subtree, node). -/
def treeNodeM {Y : Type} (hsf : ℕ) (S : Structure) (leafOp : LeafId → m Y)
    (nodeOp : LeafId → Y → Y → m Y) : ℕ → ℕ → m (Option Y)
  | 0, i => if (⟨hsf, i⟩ : Node) ∈ S.anchors then some <$> leafOp ⟨0, i⟩ else pure none
  | z + 1, i =>
    if z + 1 ≤ hsf ∧ (⟨hsf - (z + 1), i⟩ : Node) ∈ S.anchors then some <$> leafOp ⟨z + 1, i⟩
    else if z + 1 ≤ hsf ∧ (⟨hsf - (z + 1), i⟩ : Node) ∈ S.internal then do
      let l ← treeNodeM hsf S leafOp nodeOp z (2 * i)
      let r ← treeNodeM hsf S leafOp nodeOp z (2 * i + 1)
      combineM (nodeOp ⟨z + 1, i⟩) l r
    else pure none

/-- **The query program of `B₇`/`B₈`**: the FXMSS tree of `S` from the chain starts `x`, with the
operations `fOp` (chain steps), `cOp` (anchor compressions) and `hOp` (internal nodes). -/
def treeProgM (S : Structure) (fOp : SLHDSA.Adrs → pr.Y → m pr.Y)
    (cOp : SLHDSA.Adrs → Vector pr.Y P.lsf → m pr.Y) (hOp : SLHDSA.Adrs → pr.Y → pr.Y → m pr.Y)
    (x : LeafId → ℕ → pr.Y) : m Unit := do
  let _ ← treeNodeM P.hsf S (leafM pr fOp cOp x) (fun id => hOp (SfAdrs.treeAdrs id).toAdrs)
    P.hsf 0
  pure ()

/-! ### Simulation commutes with the program -/

variable {ι : Type} {spec : OracleSpec ι} {n : Type → Type} [Monad n] [LawfulMonad n]
  (impl : QueryImpl spec n)

omit [Inhabited pr.Y] in
theorem simulateQ_chainM (fOp : SLHDSA.Adrs → pr.Y → OracleComp spec pr.Y) (id : LeafId)
    (ch : ℕ) (x : pr.Y) (k : ℕ) :
    simulateQ impl (chainM pr fOp id ch x k) =
      chainM pr (fun t y => simulateQ impl (fOp t y)) id ch x k := by
  induction k with
  | zero => simp [chainM]
  | succ k ih => simp [chainM, ih]

theorem simulateQ_list_mapM {ε γ : Type} (l : List ε) (f : ε → OracleComp spec γ) :
    simulateQ impl (l.mapM f) = l.mapM fun a => simulateQ impl (f a) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.mapM_cons, ih]

theorem simulateQ_leafM (fOp : SLHDSA.Adrs → pr.Y → OracleComp spec pr.Y)
    (cOp : SLHDSA.Adrs → Vector pr.Y P.lsf → OracleComp spec pr.Y) (x : LeafId → ℕ → pr.Y)
    (id : LeafId) :
    simulateQ impl (leafM pr fOp cOp x id) =
      leafM pr (fun t y => simulateQ impl (fOp t y)) (fun t v => simulateQ impl (cOp t v)) x id := by
  simp [leafM, topsM, simulateQ_chainM]

theorem simulateQ_combineM {Y : Type} (f : Y → Y → OracleComp spec Y) (l r : Option Y) :
    simulateQ impl (combineM f l r) = combineM (fun a b => simulateQ impl (f a b)) l r := by
  rcases l with _ | a <;> rcases r with _ | b <;> simp [combineM]

theorem simulateQ_treeNodeM {Y : Type} (hsf : ℕ) (S : Structure)
    (leafOp : LeafId → OracleComp spec Y) (nodeOp : LeafId → Y → Y → OracleComp spec Y) :
    ∀ z i, simulateQ impl (treeNodeM hsf S leafOp nodeOp z i) =
      treeNodeM hsf S (fun id => simulateQ impl (leafOp id))
        (fun id a b => simulateQ impl (nodeOp id a b)) z i
  | 0, i => by unfold treeNodeM; split_ifs <;> simp
  | z + 1, i => by
    unfold treeNodeM
    split_ifs <;> simp [simulateQ_treeNodeM hsf S leafOp nodeOp z, simulateQ_combineM]

theorem simulateQ_treeProgM (S : Structure) (fOp : SLHDSA.Adrs → pr.Y → OracleComp spec pr.Y)
    (cOp : SLHDSA.Adrs → Vector pr.Y P.lsf → OracleComp spec pr.Y)
    (hOp : SLHDSA.Adrs → pr.Y → pr.Y → OracleComp spec pr.Y) (x : LeafId → ℕ → pr.Y) :
    simulateQ impl (treeProgM pr S fOp cOp hOp x) =
      treeProgM pr S (fun t y => simulateQ impl (fOp t y)) (fun t v => simulateQ impl (cOp t v))
        (fun t a b => simulateQ impl (hOp t a b)) x := by
  simp [treeProgM, simulateQ_treeNodeM, simulateQ_leafM]

end Programs

/-! ## The logs of the tree program -/

section TreeLog

open Scheme

/-- The position of a visited anchor (`inl`) or internal node (`inr`). -/
def posOf : LeafId ⊕ LeafId → LeafId
  | .inl a => a
  | .inr a => a

/-- **The visiting order of `treeNodeM`**: the anchors (`inl`) and internal nodes (`inr`) below
the position `(z, i)`, post-order. -/
def treeOrder (hsf : ℕ) (S : Structure) : ℕ → ℕ → List (LeafId ⊕ LeafId)
  | 0, i => if (⟨hsf, i⟩ : Node) ∈ S.anchors then [.inl ⟨0, i⟩] else []
  | z + 1, i =>
    if z + 1 ≤ hsf ∧ (⟨hsf - (z + 1), i⟩ : Node) ∈ S.anchors then [.inl ⟨z + 1, i⟩]
    else if z + 1 ≤ hsf ∧ (⟨hsf - (z + 1), i⟩ : Node) ∈ S.internal then
      treeOrder hsf S z (2 * i) ++ treeOrder hsf S z (2 * i + 1) ++ [.inr ⟨z + 1, i⟩]
    else []

variable {α β Y : Type}

/-- The log of a node operation on optional children values. -/
def combineLog (f : Y → Y → List α) : Option Y → Option Y → List α
  | some a, some b => f a b
  | _, _ => []

/-- The challenge-log entry of a visited position: the anchor's log `lq`, or the node's log `nq`
on the honest children values. -/
def entryQ (hsf : ℕ) (S : Structure) (leaf : LeafId → Y) (node : LeafId → Y → Y → Y)
    (lq : LeafId → List α) (nq : LeafId → Y → Y → List α) : LeafId ⊕ LeafId → List α
  | .inl id => lq id
  | .inr id => combineLog (nq id) (Tree.treeNode hsf S leaf node (id.height - 1) (2 * id.index))
      (Tree.treeNode hsf S leaf node (id.height - 1) (2 * id.index + 1))

/-- The collection-log entry of a visited position (anchors only). -/
def entryC (lc : LeafId → List β) : LeafId ⊕ LeafId → List β
  | .inl id => lc id
  | .inr _ => []

theorem combineM_isLog {f : Y → Y → StateM (List α × List β) Y} {g : Y → Y → Y}
    {fq : Y → Y → List α} (h : ∀ a b, IsLog (f a b) (g a b) (fq a b) []) (l r : Option Y) :
    IsLog (combineM f l r) (Option.map₂ g l r) (combineLog fq l r) [] := by
  rcases l with _ | a <;> rcases r with _ | b
  · exact IsLog.pure _
  · exact IsLog.pure _
  · exact IsLog.pure _
  · exact (h a b).map some

/-- **The logs of `treeNodeM`**: with logging operations, the program returns `Tree.treeNode` and
logs the entries of the visited positions in order. -/
theorem treeNodeM_isLog (hsf : ℕ) (S : Structure) {leafOp : LeafId → StateM (List α × List β) Y}
    {nodeOp : LeafId → Y → Y → StateM (List α × List β) Y} {leaf : LeafId → Y}
    {node : LeafId → Y → Y → Y} {lq : LeafId → List α} {lc : LeafId → List β}
    {nq : LeafId → Y → Y → List α} (hl : ∀ id, IsLog (leafOp id) (leaf id) (lq id) (lc id))
    (hn : ∀ id a b, IsLog (nodeOp id a b) (node id a b) (nq id a b) []) :
    ∀ z i, IsLog (treeNodeM hsf S leafOp nodeOp z i) (Tree.treeNode hsf S leaf node z i)
      ((treeOrder hsf S z i).flatMap (entryQ hsf S leaf node lq nq))
      ((treeOrder hsf S z i).flatMap (entryC lc))
  | 0, i => by
    rw [treeNodeM, Tree.treeNode, treeOrder]
    split_ifs
    · exact ((hl _).map some).of_eq rfl (by simp [entryQ]) (by simp [entryC])
    · exact (IsLog.pure _).of_eq rfl (by simp) (by simp)
  | z + 1, i => by
    rw [treeNodeM, Tree.treeNode, treeOrder]
    split_ifs
    · exact ((hl _).map some).of_eq rfl (by simp [entryQ]) (by simp [entryC])
    · exact ((treeNodeM_isLog hsf S hl hn z (2 * i)).bind
        ((treeNodeM_isLog hsf S hl hn z (2 * i + 1)).bind
          (combineM_isLog (hn ⟨z + 1, i⟩) _ _))).of_eq rfl (by simp [entryQ]) (by simp [entryC])
    · exact (IsLog.pure _).of_eq rfl (by simp) (by simp)

variable {P : Params} (pr : Primitives P)

/-- The chain tweaks `SF_WOTS_C_HASH` of the instance at `id`, in program order. -/
def chainLog (P : Params) (id : LeafId) : List SLHDSA.Adrs :=
  (List.finRange P.lsf).flatMap fun ch =>
    (List.range (P.w - 1)).map fun j => (SfAdrs.chainAdrs id ch.val j).toAdrs

theorem chainM_isLog (pk : pr.PkSeed) {fOp : SLHDSA.Adrs → pr.Y → StateM (List α × List SLHDSA.Adrs) pr.Y}
    (hF : ∀ t y, IsLog (fOp t y) (pr.F pk t y) [] [t]) (id : LeafId) (ch : ℕ) (x : pr.Y) :
    ∀ k, IsLog (chainM pr fOp id ch x k) (WotsC.chain pr pk id ch x 0 k) []
      ((List.range k).map fun j => (SfAdrs.chainAdrs id ch j).toAdrs)
  | 0 => (IsLog.pure x).of_eq rfl rfl rfl
  | k + 1 => ((chainM_isLog pk hF id ch x k).bind (hF _ _)).of_eq
      (by rw [WotsC.chain_succ, Nat.zero_add]) rfl (by simp [List.range_succ])

variable [Inhabited pr.Y]

theorem topsM_isLog (pk : pr.PkSeed)
    {fOp : SLHDSA.Adrs → pr.Y → StateM (List α × List SLHDSA.Adrs) pr.Y}
    (hF : ∀ t y, IsLog (fOp t y) (pr.F pk t y) [] [t]) (id : LeafId) (x : ℕ → pr.Y) :
    IsLog (topsM pr fOp id x) (WotsC.pkTops pr pk id x) [] (chainLog P id) := by
  unfold topsM
  have h := (IsLog.mapM (l := List.finRange P.lsf) fun (ch : Fin P.lsf) _ =>
    chainM_isLog pr pk hF id ch.val (x ch.val) (P.w - 1)).bind
    (f := fun l => pure (Vector.ofFn fun (ch : Fin P.lsf) => l.getD ch.val default))
    (IsLog.pure _)
  refine h.of_eq ?_ (by simp) (by simp [chainLog])
  apply Vector.ext
  intro j hj
  simp [WotsC.pkTops, List.getD_eq_getElem?_getD]

theorem leafM_isLog (pk : pr.PkSeed)
    {fOp : SLHDSA.Adrs → pr.Y → StateM (List α × List SLHDSA.Adrs) pr.Y}
    {cOp : SLHDSA.Adrs → Vector pr.Y P.lsf → StateM (List α × List SLHDSA.Adrs) pr.Y}
    {cq : SLHDSA.Adrs → Vector pr.Y P.lsf → List α} {cc : SLHDSA.Adrs → List SLHDSA.Adrs}
    (hF : ∀ t y, IsLog (fOp t y) (pr.F pk t y) [] [t])
    (hC : ∀ t v, IsLog (cOp t v) (pr.ThLsf pk t v) (cq t v) (cc t)) (x : LeafId → ℕ → pr.Y)
    (id : LeafId) :
    IsLog (leafM pr fOp cOp x id) (Fxmss.leaf pr pk x id)
      (cq (SfAdrs.pkAdrs id).toAdrs (WotsC.pkTops pr pk id (x id)))
      (chainLog P id ++ cc (SfAdrs.pkAdrs id).toAdrs) :=
  ((topsM_isLog pr pk hF id (x id)).bind (hC _ _)).of_eq rfl (by simp) rfl

/-- **The logs of the query program**: it computes the honest FXMSS tree of the chain starts `x`
(`Fxmss.treeNode`), logging per anchor its chain tweaks and compression, and per internal node
its node operation on the honest children values. -/
theorem treeProgM_isLog (pk : pr.PkSeed) (S : Structure)
    {fOp : SLHDSA.Adrs → pr.Y → StateM (List α × List SLHDSA.Adrs) pr.Y}
    {cOp : SLHDSA.Adrs → Vector pr.Y P.lsf → StateM (List α × List SLHDSA.Adrs) pr.Y}
    {hOp : SLHDSA.Adrs → pr.Y → pr.Y → StateM (List α × List SLHDSA.Adrs) pr.Y}
    {cq : SLHDSA.Adrs → Vector pr.Y P.lsf → List α} {cc : SLHDSA.Adrs → List SLHDSA.Adrs}
    {hq : SLHDSA.Adrs → pr.Y → pr.Y → List α}
    (hF : ∀ t y, IsLog (fOp t y) (pr.F pk t y) [] [t])
    (hC : ∀ t v, IsLog (cOp t v) (pr.ThLsf pk t v) (cq t v) (cc t))
    (hH : ∀ t a b, IsLog (hOp t a b) (pr.H pk t a b) (hq t a b) []) (x : LeafId → ℕ → pr.Y) :
    IsLog (treeProgM pr S fOp cOp hOp x) ()
      ((treeOrder P.hsf S P.hsf 0).flatMap (entryQ P.hsf S (Fxmss.leaf pr pk x) (Fxmss.node pr pk)
        (fun id => cq (SfAdrs.pkAdrs id).toAdrs (WotsC.pkTops pr pk id (x id)))
        (fun id a b => hq (SfAdrs.treeAdrs id).toAdrs a b)))
      ((treeOrder P.hsf S P.hsf 0).flatMap
        (entryC fun id => chainLog P id ++ cc (SfAdrs.pkAdrs id).toAdrs)) :=
  ((treeNodeM_isLog P.hsf S (leafM_isLog pr pk hF hC x) (fun id a b => hH _ a b) P.hsf 0).bind
    (IsLog.pure ())).of_eq rfl (by rw [List.append_nil]; rfl) (by simp)

end TreeLog

/-! ## The visiting order on a valid structure -/

section Order

open Scheme

variable {hsf : ℕ} {S : Structure}

/-- A visited position is an anchor (`inl`) or an internal node (`inr`) of the structure. -/
def Visit (hsf : ℕ) (S : Structure) : LeafId ⊕ LeafId → Prop
  | .inl id => id.height ≤ hsf ∧ Node.ofLeafId hsf id ∈ S.anchors
  | .inr id => 1 ≤ id.height ∧ id.height ≤ hsf ∧ Node.ofLeafId hsf id ∈ S.internal

private theorem div_pow_succ_sub {a h z : ℕ} (hh : h ≤ z) :
    a / 2 ^ (z + 1 - h) = a / 2 ^ (z - h) / 2 := by
  rw [show z + 1 - h = (z - h) + 1 by omega, Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- Every visited position below `(z, i)` is an anchor or internal node in the subtree of
`(z, i)`. -/
theorem mem_treeOrder : ∀ (z i : ℕ) (e : LeafId ⊕ LeafId), e ∈ treeOrder hsf S z i →
    Visit hsf S e ∧ (posOf e).height ≤ z ∧ (posOf e).index / 2 ^ (z - (posOf e).height) = i
  | 0, i, e, h => by
    rw [treeOrder] at h
    split_ifs at h with ha
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨⟨Nat.zero_le _, by simpa [Node.ofLeafId] using ha⟩, le_rfl, by simp [posOf]⟩
    · simp at h
  | z + 1, i, e, h => by
    rw [treeOrder] at h
    split_ifs at h with ha hi
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨⟨ha.1, ha.2⟩, le_rfl, by simp [posOf]⟩
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with (h | h) | rfl
      · obtain ⟨hv, hz, hi'⟩ := mem_treeOrder z _ e h
        exact ⟨hv, by omega, by rw [div_pow_succ_sub hz, hi']; omega⟩
      · obtain ⟨hv, hz, hi'⟩ := mem_treeOrder z _ e h
        exact ⟨hv, by omega, by rw [div_pow_succ_sub hz, hi']; omega⟩
      · exact ⟨⟨Nat.succ_le_succ (Nat.zero_le z), hi.1, hi.2⟩, le_rfl, by simp [posOf]⟩
    · simp at h

/-- **Every position is visited at most once.** -/
theorem nodup_treeOrder : ∀ (z i : ℕ), ((treeOrder hsf S z i).map posOf).Nodup
  | 0, i => by rw [treeOrder]; split_ifs <;> simp
  | z + 1, i => by
    rw [treeOrder]
    split_ifs with ha hi
    · simp
    · rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
      refine ⟨⟨nodup_treeOrder z _, nodup_treeOrder z _, ?_⟩, by simp, ?_⟩
      · intro a ha' b hb' hab
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha'
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb'
        have h1 := (mem_treeOrder z _ e he).2.2
        have h2 := (mem_treeOrder z _ e' he').2.2
        rw [hab] at h1
        omega
      · intro a ha' b hb' hab
        simp only [List.map_cons, List.map_nil, List.mem_singleton, posOf] at hb'
        subst hb'
        rw [← List.map_append] at ha'
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha'
        rw [List.mem_append] at he
        have h1 : (posOf e).height ≤ z := by
          rcases he with he | he
          · exact (mem_treeOrder z _ e he).2.1
          · exact (mem_treeOrder z _ e he).2.1
        rw [hab] at h1
        simp at h1
    · simp

/-- **Every anchor and internal node below a node of a valid structure is visited.** -/
theorem mem_treeOrder_of_visit (hS : S.TreeValid hsf) :
    ∀ (z i : ℕ), z ≤ hsf → (⟨hsf - z, i⟩ : Node) ∈ S.nodes →
      ∀ e, Visit hsf S e → (posOf e).height ≤ z →
        (posOf e).index / 2 ^ (z - (posOf e).height) = i → e ∈ treeOrder hsf S z i
  | 0, i, _, hw, e, hv, hz, hi => by
    have hA : (⟨hsf, i⟩ : Node) ∈ S.anchors := by
      rcases Structure.mem_nodes.1 hw with h | h
      · simpa using h
      · have := hS.internal_depth_lt h; simp at this
    rw [treeOrder, ite_eq_left hA]
    rcases e with id | id
    · simp only [posOf, Nat.le_zero] at hz hi
      simp only [hz, Nat.sub_zero, pow_zero, Nat.div_one] at hi
      simp only [List.mem_singleton, Sum.inl.injEq]
      exact LeafId.ext hz hi
    · simp only [Visit, posOf] at hv hz
      omega
  | z + 1, i, hzh, hw, e, hv, hz, hi => by
    have hnode : ∀ p : LeafId, p.height ≤ z + 1 → p.index / 2 ^ (z + 1 - p.height) = i →
        Node.ofLeafId hsf p ∈ S.nodes → p.height < z + 1 →
          (⟨hsf - (z + 1), i⟩ : Node) ∈ S.internal := by
      intro p hp1 hp2 hpn hlt
      have hdle := hS.depth_le hpn
      have := hS.ancestor_mem_internal hpn (k := z + 1 - p.height) (by omega)
        (by simp only [Node.ofLeafId]; omega)
      simp only [Node.ancestor, Node.ofLeafId] at this
      convert this using 2
      · omega
      · exact hp2.symm
    have hvn : Node.ofLeafId hsf (posOf e) ∈ S.nodes := by
      rcases e with id | id
      · exact Structure.anchors_subset_nodes hv.2
      · exact Structure.internal_subset_nodes hv.2.2
    rw [treeOrder]
    by_cases hA : (⟨hsf - (z + 1), i⟩ : Node) ∈ S.anchors
    · rw [ite_eq_left ⟨hzh, hA⟩, List.mem_singleton]
      rcases Nat.lt_or_ge (posOf e).height (z + 1) with hlt | hge
      · exact absurd hA (hS.not_mem_anchors_of_mem_internal (hnode _ hz hi hvn hlt))
      · have hh : (posOf e).height = z + 1 := by omega
        rw [hh, Nat.sub_self, pow_zero, Nat.div_one] at hi
        rcases e with id | id
        · exact congrArg Sum.inl (LeafId.ext hh hi)
        · simp only [Visit, posOf] at hv hh hi
          have : Node.ofLeafId hsf id = ⟨hsf - (z + 1), i⟩ := by
            simp [Node.ofLeafId, hh, hi]
          exact absurd hA (hS.not_mem_anchors_of_mem_internal (this ▸ hv.2.2))
    · have hI : (⟨hsf - (z + 1), i⟩ : Node) ∈ S.internal :=
        (Structure.mem_nodes.1 hw).resolve_left hA
      rw [ite_eq_right (fun h => hA h.2), ite_eq_left ⟨hzh, hI⟩]
      simp only [List.mem_append, List.mem_singleton]
      rcases Nat.lt_or_ge (posOf e).height (z + 1) with hlt | hge
      · have hz' : (posOf e).height ≤ z := by omega
        rw [div_pow_succ_sub hz'] at hi
        have hc : ∀ b : Bool, (⟨hsf - z, 2 * i + b.toNat⟩ : Node) ∈ S.nodes := by
          intro b
          have := hS.child_mem _ hI b
          simp only [Node.child] at this
          convert this using 2
          omega
        rcases Nat.mod_two_eq_zero_or_one ((posOf e).index / 2 ^ (z - (posOf e).height)) with
          h2 | h2
        · refine Or.inl (Or.inl (mem_treeOrder_of_visit hS z (2 * i) (by omega)
            (by simpa using hc false) e hv hz' (by omega)))
        · refine Or.inl (Or.inr (mem_treeOrder_of_visit hS z (2 * i + 1) (by omega)
            (by simpa using hc true) e hv hz' (by omega)))
      · have hh : (posOf e).height = z + 1 := by omega
        rw [hh, Nat.sub_self, pow_zero, Nat.div_one] at hi
        rcases e with id | id
        · simp only [Visit, posOf] at hv hh hi
          have : Node.ofLeafId hsf id = ⟨hsf - (z + 1), i⟩ := by
            simp [Node.ofLeafId, hh, hi]
          exact absurd (this ▸ hv.2) hA
        · exact Or.inr (congrArg Sum.inr (LeafId.ext hh hi))

theorem visit_mem_treeOrder (hS : S.TreeValid hsf) {e : LeafId ⊕ LeafId}
    (hv : Visit hsf S e) : e ∈ treeOrder hsf S hsf 0 := by
  have hvn : Node.ofLeafId hsf (posOf e) ∈ S.nodes := by
    rcases e with id | id
    · exact Structure.anchors_subset_nodes hv.2
    · exact Structure.internal_subset_nodes hv.2.2
  have hle : (posOf e).height ≤ hsf := by rcases e with id | id <;> simp [Visit, posOf] at hv ⊢ <;> omega
  have hlt := hS.idx_lt_two_pow hvn
  refine mem_treeOrder_of_visit hS hsf 0 le_rfl ?_ e hv hle ?_
  · have := Structure.internal_subset_nodes hS.root_mem
    simpa [Node.root] using this
  · simp only [Node.ofLeafId] at hlt
    exact Nat.div_eq_of_lt hlt

/-- A visited internal node is a tree-node tweak of the structure. -/
theorem visit_inr_of_mem_treeTweaks (hS : S.TreeValid hsf) {id : LeafId}
    (h : (SfAdrs.treeAdrs id).toAdrs ∈ Structure.treeTweaks hsf S) : Visit hsf S (.inr id) := by
  obtain ⟨v, hv, hvid⟩ := Finset.mem_image.1 h
  obtain rfl := SfAdrs.treeAdrs_inj.1 hvid
  have := hS.internal_depth_lt hv
  exact ⟨by simp [Node.toLeafId]; omega, by simp [Node.toLeafId],
    by rwa [Node.ofLeafId_toLeafId this.le]⟩

/-- An anchor of the structure, as a compression tweak, is visited. -/
theorem visit_inl_of_mem_pkTweaks (hS : S.TreeValid hsf) {id : LeafId}
    (h : (SfAdrs.pkAdrs id).toAdrs ∈ Structure.pkTweaks hsf S) : Visit hsf S (.inl id) := by
  obtain ⟨v, hv, hvid⟩ := Finset.mem_image.1 h
  obtain rfl := SfAdrs.pkAdrs_inj.1 hvid
  have := hS.anchor_depth_le v hv
  exact ⟨by simp [Node.toLeafId], by rwa [Node.ofLeafId_toLeafId this]⟩

/-- The node identifier `(z, i)` of an address (its layer and tree fields). -/
def nodeKey (a : SLHDSA.Adrs) : LeafId := ⟨a.layer, a.tree⟩

@[simp] theorem nodeKey_toAdrs (a : SfAdrs) : nodeKey a.toAdrs = ⟨a.height, a.index⟩ := rfl

theorem map_flatMap_sublist {γ δ ε : Type} (l : List γ) (f : γ → List δ) (key : δ → ε)
    (pos : γ → ε) (hf : ∀ c ∈ l, ((f c).map key).Sublist [pos c]) :
    ((l.flatMap f).map key).Sublist (l.map pos) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.map_cons, ← List.singleton_append]
    exact (hf a (by simp)).append (ih fun c hc => hf c (by simp [hc]))

/-- **Distinct keys of the logged entries**: if every position logs at most one entry, keyed by
the position, the keys of the log are distinct. -/
theorem nodup_map_flatMap {γ δ ε : Type} (l : List γ) (f : γ → List δ) (key : δ → ε)
    (pos : γ → ε) (hf : ∀ c ∈ l, ((f c).map key).Sublist [pos c]) (hl : (l.map pos).Nodup) :
    ((l.flatMap f).map key).Nodup :=
  hl.sublist (map_flatMap_sublist l f key pos hf)

end Order

end ShrincsSecurity.Fxmss

/-! ## The honest data of `F.3` -/

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Scheme.Grinding
open ShrincsSecurity.Scheme.Structure (leafIds)

variable {P : Params} (pr : Primitives P) [Inhabited pr.Y]

/-- In `F.3` the revealed blocks complete to the uncompressed public key `c_{0,w−1}(u)`. -/
theorem topsFromSig_blockSig_zero (S : Structure) (pk : pr.PkSeed) (u : SkIdx P S → pr.Y)
    (id : LeafId) (d : pr.Y) (c : Fin (2 ^ P.c)) :
    WotsC.topsFromSig pr pk id d (blockSig pr (betaOf pr 0 pk u) id d c) =
      WotsC.pkTops pr pk id (skOf pr S u id) := by
  apply Vector.ext
  intro ch hch
  simp only [WotsC.topsFromSig, blockSig, betaOf, blockVal, WotsC.pkTops, Vector.getElem_ofFn,
    Nat.zero_min, Nat.sub_zero]
  have hc := WotsC.chain_compose pr pk id ch (skOf pr S u id ch) 0 (WotsC.digit pr d ch)
    (P.w - 1 - WotsC.digit pr d ch)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (WotsC.digit_lt pr d ch))]

/-- **The anchor values of `F.3`** are the WOTS+C public keys of the secret key `u`. -/
theorem hon_zero_leafVal (S : Structure) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (u : SkIdx P S → pr.Y) (id : LeafId) :
    (hon pr S pk dig (betaOf pr 0 pk u)).leafVal id = Fxmss.leaf pr pk (skOf pr S u) id := by
  simp only [hon, Fxmss.leaf, WotsC.pkGen]
  split
  · rw [topsFromSig_blockSig_zero]
  · congr 1

/-- The honest tree of `F.3` is the FXMSS tree of the secret key `u`. -/
theorem hon_zero_value (S : Structure) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (u : SkIdx P S → pr.Y) (z i : ℕ) :
    (hon pr S pk dig (betaOf pr 0 pk u)).value z i = Fxmss.treeNode pr S pk (skOf pr S u) z i := by
  have h : (hon pr S pk dig (betaOf pr 0 pk u)).leafVal = Fxmss.leaf pr pk (skOf pr S u) :=
    funext (hon_zero_leafVal pr S pk dig u)
  simp only [Honest.value, Fxmss.treeNode, h]
  rfl

/-- **The uncompressed public keys of `F.3`** at the anchors of a valid structure are
`c_{0,w−1}(u)`, under Conjecture 3.1 (the counter search succeeds, so the revealed blocks are
those of the honest encoded digest). -/
theorem hon_zero_tops (hP : P.Valid) (hgc : GrindComplete pr) {S : Structure}
    (hS : S.TreeValid P.hsf) (pk : pr.PkSeed) (dig : LeafId → pr.Digest) (u : SkIdx P S → pr.Y)
    {id : LeafId} (hid : id ∈ leafIds P.hsf S) :
    (hon pr S pk dig (betaOf pr 0 pk u)).tops id = WotsC.pkTops pr pk id (skOf pr S u id) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
  have hz : P.hsf - v.depth < 256 := by have := hP.hsf_le; omega
  have hi : v.idx < 2 ^ 64 := hS.anchor_idx_lt v hv
  have hg := (grindComplete_iff pr).1 hgc pk (⟨P.hsf - v.depth, hz⟩, ⟨v.idx, hi⟩)
    (dig (v.toLeafId P.hsf))
  simp only [GrindTweak.leafId] at hg
  obtain ⟨⟨d, c⟩, hdc⟩ := Option.ne_none_iff_exists'.1 hg
  have hdc' : WotsC.grind pr pk (v.toLeafId P.hsf) (dig (v.toLeafId P.hsf)) = some (d, c) := hdc
  obtain ⟨hd, -, -⟩ := (WotsC.grind_eq_some_iff pr).1 hdc'
  simp only [Honest.tops, Honest.encoded, hon, hdc']
  have hctr : (blockSig pr (betaOf pr 0 pk u) (v.toLeafId P.hsf) d c).ctr = c := rfl
  rw [hctr, ← hd, topsFromSig_blockSig_zero]

variable (Msg : Type) [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.Digest] [DecidableEq Msg] [SampleableType pr.PkSeed]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- On every reachable setup, a valid committed structure has at most `L` anchors. -/
theorem anchors_le_of_mem_support_setupHyb {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) {d : Setup pr Msg A.State}
    (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary)) (hS : d.S.TreeValid P.hsf) :
    d.S.anchors.card ≤ L := by
  unfold setupHyb at hd
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hd
  obtain ⟨z, hz, ys, -, u, -, rfl⟩ := hd
  exact A.anchors_le z.1 (OracleComp.mem_support_of_mem_support_simulateQ_run _ _ _ hz) hS

end ShrincsSecurity.Fxmss.Rom

namespace ShrincsSecurity.Fxmss.Rom

open Scheme

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.Digest] [DecidableEq Msg]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg]
  [Inhabited pr.Digest]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- Every output of the signing phase of a block game is a transcript with the honest data of the
setup, on a valid structure. -/
theorem stageHyb_support {qs : ℕ} {A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs}
    {β : LeafId → ℕ → ℕ → pr.Y} {d : Setup pr Msg A.State} {pk : pr.PkSeed}
    {o : Option (Transcript pr Msg × Honest pr)}
    (ho : o ∈ support (stageHyb pr Msg slKeygen A β d pk)) {tr : Transcript pr Msg}
    {H : Honest pr} (hoe : o = some (tr, H)) :
    d.S.TreeValid P.hsf ∧ H = hon pr d.S pk (digOf pr d.ys) β := by
  subst hoe
  unfold stageHyb at ho
  split_ifs at ho with hS
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at ho
    exact ⟨hS, by aesop⟩
  · simp at ho

end ShrincsSecurity.Fxmss.Rom

end
