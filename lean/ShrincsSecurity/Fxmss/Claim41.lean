module

public import ShrincsSecurity.Fxmss.Events
public import ShrincsSecurity.Fxmss.Lift
public import ShrincsSecurity.Notions.Generic.RandomSamplingTCR

/-!
# Claim 4.1: `F.0 → F.1`, SM-rTCR of `H_msg^sf`

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.1** and **Algorithm 4** (txt lines
3200–3260).

The reduction `B0` plays the classical ROM SM-rTCR game of Definition 4.9
(`Notions.Generic.RandomSamplingTCR`) with public parameter `P = PK.seed`, tweak
`T = (PK.sf, idx)`, message `m = M`, randomness `ρ = R`, `Prop ≡ 1`, sampling budget `K = 1` and
target cap `p = L`: the random oracle `Th(P, T, (m, ρ))` of the game is `H_msg^sf(R, PK.seed,
PK.sf, idx, M)` with its inputs rearranged (`roToTh`, a bijection). `B0` runs the structure
phase `A₁` forwarding its random-oracle queries, samples the WOTS+C secrets and `PK.sl` itself,
and runs the signing phase of the games (`stage2Prog`: `A₂`, the verification query of the
forgery, the completion of Remark 4.6) answering a signing query at an unused anchor `id` by the
challenge query `O((PK.sf, idx(id)), M)`, which returns `(y, R)` with `y = Th(P, (PK.sf, idx),
(M, R))` for a fresh uniform `R` — exactly the honest signing of `F.0`. It outputs
`(j, M*, R*)`, `j` the position of the forgery's leaf among the used ones.

**Proof.** The experiment run with `B0`, projected onto the random-oracle cache (the game's table
through `roToTh`) and `B0`'s signing records, is `gameG` (`F.0`), step by step
(`flat_run_proj`): the challenge oracle never refuses (signing queries name pairwise distinct
anchors, which have distinct `idx` by `toIdx_inj`, and at most `|leafIds| ≤ L` of them are
signed), and with `K = 1`, `Prop ≡ 1` it is `R ←$; y ← Th(…)`. On `Win ∧ C₁` the forgery's leaf
`j` was signed with `y_j = y*`; its message was queried, so `(M*, R*) ≠ (M_j, R_j)`, and both
points are cached with `y*` (the forgery's point by the verification query), so the final check
of the experiment succeeds with probability one (`isCollision_true`).

**Query counts.** `B0` makes at most `q_{h,1} + q_{h,2} + 1` queries to `Th` (the forwarded
queries and the verification of the forgery; the challenge oracle's internal evaluations are not
`B0`'s queries) and at most `L` challenge queries (each consumes an anchor, `|A| ≤ L`). The paper
bounds the challenges by `q_s`; with the completion of Remark 4.6 inside the games every anchor
is signed, so the cap is the number `L` of anchors.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions.Generic
open ShrincsSecurity.Scheme.Structure (leafIds)

/-! ## Generic: a query bound through a stateful simulation with a potential -/

namespace Claim41

section Generic

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α : Type}

/-- **Query bound through a stateful simulation with a potential.** If, from every state
satisfying the invariant `inv` (preserved by every step), a step followed by any continuation
whose budget is the potential `pot` of the reached state costs at most `pot s` `q`-queries, then
the whole simulation costs at most `pot s` `q`-queries. -/
theorem isQueryBoundP_run_of_pot {q : ι' → Prop} [DecidablePred q] {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (inv : σ → Prop) (pot : σ → ℕ)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hstep : ∀ (t : ι) (s : σ), inv s → ∀ {β : Type} (k : spec.Range t × σ → OracleComp spec' β),
      (∀ z ∈ support ((impl t).run s), IsQueryBoundP (k z) q (pot z.2)) →
      IsQueryBoundP ((impl t).run s >>= k) q (pot s))
    (oa : OracleComp spec α) (s : σ) (hs : inv s) :
    IsQueryBoundP ((simulateQ impl oa).run s) q (pot s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, StateT.run_bind]
    exact hstep t s hs _ fun z hz => ih z.1 z.2 (hinv t s hs z hz)

end Generic

/-! ## Types of the reduction -/

variable {P : Params} (pr : Primitives P) (Msg : Type)

/-- The inputs `(P, T, (m, ρ)) = (PK.seed, (PK.sf, idx), (M, R))` of `Th = H_msg^sf` in the
SM-rTCR game. -/
abbrev ThIn : Type := pr.PkSeed × (pr.Y × Idx) × (Msg × pr.Y)

/-- The oracles of an SM-rTCR adversary against `H_msg^sf`. -/
abbrev B0Spec : OracleSpec (ℕ ⊕ (ThIn pr Msg ⊕ ((pr.Y × Idx) × Msg))) :=
  RandomSamplingTCR.AdvSpec pr.PkSeed (pr.Y × Idx) Msg pr.Y pr.Digest

/-- The state of the SM-rTCR experiment against `H_msg^sf`. -/
abbrev GSt : Type := RandomSamplingTCR.GameState pr.PkSeed (pr.Y × Idx) Msg pr.Y pr.Digest

/-- `(R, (PK.seed, PK.sf, idx, M)) ↦ (PK.seed, (PK.sf, idx), (M, R))`. -/
def roToTh (x : RoIn pr Msg) : ThIn pr Msg := (x.2.1, (x.2.2.1, x.2.2.2.1), (x.2.2.2.2, x.1))

/-- The inverse of `roToTh`. -/
def thToRo (y : ThIn pr Msg) : RoIn pr Msg := (y.2.2.2, (y.1, y.2.1.1, y.2.1.2, y.2.2.1))

theorem roToTh_injective : Function.Injective (roToTh pr Msg) :=
  fun _ _ h => congrArg (thToRo pr Msg) h

/-- `B0`'s state in the signing phase: the used leaves, the queried messages, and the records of
the answered signing queries (as in the games). -/
structure BSt where
  /-- The used leaves, in order. -/
  used : List LeafId
  /-- The queried messages. -/
  log : List Msg
  /-- The record of the answered signing query at each used leaf. -/
  recs : LeafId → Option (Rec pr Msg)

/-- The initial state of `B0`'s signing phase. -/
def BSt.init : BSt pr Msg := ⟨[], [], fun _ => none⟩

/-- The random-oracle cache seen through the game's table. -/
def cacheOf (g : GSt pr Msg) : (roSpec pr Msg).QueryCache :=
  QueryCache.ofFn fun x => g.table (roToTh pr Msg x)

/-- The game state of `F.0` simulated by `B0`: the cache from the game's table, the records from
`B0`'s state. -/
def proj (z : BSt pr Msg × GSt pr Msg) : St pr Msg :=
  ⟨cacheOf pr Msg z.2, z.1.used, z.1.log, z.1.recs⟩

variable [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- `B0` forwards the forger's private coins and its queries to `H_msg^sf` (to `Th`, through
`roToTh`). -/
def fwd : QueryImpl (spec pr Msg) (OracleComp (B0Spec pr Msg))
  | .inl n => liftM ((B0Spec pr Msg).query (.inl n))
  | .inr x => liftM ((B0Spec pr Msg).query (.inr (.inl (roToTh pr Msg x))))

/-- The WOTS+C/tree signature of a digest at a leaf. -/
noncomputable def sigOf (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (id : LeafId) (md : pr.Digest) :
    Option (Scheme.Fxmss.Sig pr) :=
  Scheme.Fxmss.sign pr K.S K.pk sk md id

/-- `B0`'s bookkeeping after a challenge query at an unused leaf: an answer `(y, R)` is signed
and recorded; a refusal (never happens) is answered `⊥`, the leaf still marked used. -/
noncomputable def record (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (s : BSt pr Msg) : Option (pr.Digest × pr.Y) → Option (Sig pr) × BSt pr Msg
  | some (md, R) => (some (R, sigOf pr K sk q.2 md),
      ⟨s.used ++ [q.2], s.log ++ [q.1],
        Function.update s.recs q.2 (some ⟨q.1, R, md, sigOf pr K sk q.2 md⟩)⟩)
  | none => (none, ⟨s.used ++ [q.2], s.log ++ [q.1], s.recs⟩)

/-- `B0`'s signing oracle (Algorithm 4, lines 5–9): at an unused anchor `id`, the challenge query
`O((PK.sf, idx(id)), M)` returns `(y, R)`, and the reply is `(R, FXMSS.sign(y))`; any other query
is answered `⊥`. -/
noncomputable def signB (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId) :
    StateT (BSt pr Msg) (OracleComp (B0Spec pr Msg)) (Option (Sig pr)) := StateT.mk fun s =>
  if q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used then
    record pr Msg K sk q s <$>
      (liftM ((B0Spec pr Msg).query (.inr (.inr ((K.pkSf, toIdx q.2), q.1)))) :
        OracleComp (B0Spec pr Msg) (Option (pr.Digest × pr.Y)))
  else pure (none, ⟨s.used, s.log ++ [q.1], s.recs⟩)

/-- `B0`'s handler of the signing phase. -/
noncomputable def implB (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (BSt pr Msg) (OracleComp (B0Spec pr Msg)))
  | .inl t => liftM (fwd pr Msg t)
  | .inr q => signB pr Msg K sk q

/-- `B0`'s output `(j, M*, R*)`: `j` the position of the forgery's leaf among the used leaves
(past the end, so losing, when it is not used). -/
def out (r : (Msg × LeafId × Sig pr × pr.Digest) × BSt pr Msg) : ℕ × Msg × pr.Y :=
  (r.2.used.idxOf r.1.2.1, r.1.1, r.1.2.2.1.1)

/-- `B0` after the structure phase (Algorithm 4, lines 3–15). -/
noncomputable def stage2B {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (pk : pr.PkSeed) (z : Structure × A.State) : OracleComp (B0Spec pr Msg) (ℕ × Msg × pr.Y) :=
  if ¬ z.1.TreeValid P.hsf then pure (0, Classical.arbitrary Msg, default) else do
    let f ← (liftM ($ᵗ (SkIdx P z.1 → pr.Y) : ProbComp _) : OracleComp (B0Spec pr Msg) _)
    let pkSl ← (liftM (slKeygen pk) : OracleComp (B0Spec pr Msg) pr.Y)
    let sk := skOf pr z.1 f
    let K : Keys pr := ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk sk⟩
    let r ← (simulateQ (implB pr Msg K sk) (stage2Prog pr Msg slKeygen A z.2 K)).run
      (BSt.init pr Msg)
    return out pr Msg r

/-- **The reduction `B0`** (Algorithm 4), run on the public parameter `P = PK.seed`. -/
noncomputable def mainB {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (pk : pr.PkSeed) : OracleComp (B0Spec pr Msg) (ℕ × Msg × pr.Y) := do
  let z ← simulateQ (fwd pr Msg) A.chooseShape
  stage2B pr Msg slKeygen A pk z

/-! ## Query counts -/

/-- A query to `Th`. -/
abbrev IsThQuery := RandomSamplingTCR.IsRoQuery pr.PkSeed (pr.Y × Idx) Msg pr.Y

/-- A challenge query. -/
abbrev IsChal := RandomSamplingTCR.IsChalQuery pr.PkSeed (pr.Y × Idx) Msg pr.Y

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
theorem fwd_roBound {α : Type} {oa : OracleComp (spec pr Msg) α} {n : ℕ}
    (h : oa.IsQueryBoundP (IsRoQuery pr Msg) n) :
    (simulateQ (fwd pr Msg) oa).IsQueryBoundP (IsThQuery pr Msg) n :=
  h.simulateQ_of_step
    (fun t ht => by
      rcases t with _ | x
      · exact ht.elim
      · simp [fwd, RandomSamplingTCR.IsRoQuery])
    (fun t ht => by
      rcases t with _ | x
      · simp [fwd, RandomSamplingTCR.IsRoQuery]
      · exact (ht trivial).elim)

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
theorem fwd_chalBound {α : Type} (oa : OracleComp (spec pr Msg) α) :
    (simulateQ (fwd pr Msg) oa).IsQueryBoundP (IsChal pr Msg) 0 :=
  isQueryBoundP_simulateQ_zero oa fun t => by
    rcases t with _ | x <;> simp [fwd, RandomSamplingTCR.IsChalQuery]

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- A lifted `ProbComp` makes no query to `Th` and no challenge query. -/
theorem liftM_bound {α : Type} (oa : ProbComp α)
    (p : ℕ ⊕ (ThIn pr Msg ⊕ ((pr.Y × Idx) × Msg)) → Prop) [DecidablePred p]
    (hp : ∀ n, ¬ p (.inl n)) :
    (liftM oa : OracleComp (B0Spec pr Msg) α).IsQueryBoundP p 0 :=
  (isQueryBoundP_liftM_isRight oa).of_imp fun t ht => by
    rcases t with n | _
    · exact (hp n ht).elim
    · rfl

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
theorem completion_roBound (M : Msg) :
    ∀ ids, (completion pr Msg M ids).IsQueryBoundP (IsRoQuery' pr Msg) 0
  | [] => trivial
  | id :: ids => by
    simp only [completion]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [IsRoQuery']), fun _ => by
      simpa [IsRoQuery'] using completion_roBound M ids⟩

omit [Fintype pr.Y] [DecidableEq pr.PkSeed] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
theorem stage2Prog_roBound {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (st : A.State) (K : Keys pr) :
    (stage2Prog pr Msg slKeygen A.toFxmssAdversary st K).IsQueryBoundP (IsRoQuery' pr Msg)
      (qh₂ + 1) := by
  unfold stage2Prog
  refine isQueryBoundP_bind (A.roBound₂ st K.S K.toPK) fun o _ => ?_
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr one_pos, fun _ => ?_⟩
  exact (isQueryBoundP_bind_zero _ _ (completion_roBound pr Msg _ _)
    fun _ => isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

omit [Nontrivial Msg] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem implB_inl_run (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (t : ℕ ⊕ RoIn pr Msg)
    (s : BSt pr Msg) :
    ((implB pr Msg K sk) (.inl t)).run s = (fun u => (u, s)) <$> fwd pr Msg t := by
  simp [implB]

omit [Nontrivial Msg] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem implB_roBound (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type}
    {oa : OracleComp (fullSpec pr Msg) α} {n : ℕ} (h : oa.IsQueryBoundP (IsRoQuery' pr Msg) n)
    (s : BSt pr Msg) :
    ((simulateQ (implB pr Msg K sk) oa).run s).IsQueryBoundP (IsThQuery pr Msg) n := by
  refine h.simulateQ_run_of_step (fun t ht s => ?_) (fun t ht s => ?_) s
  · rcases t with (_ | x) | q
    · exact ht.elim
    · rw [implB_inl_run]; simp [fwd]
    · exact ht.elim
  · rcases t with (_ | x) | q
    · rw [implB_inl_run]; simp [fwd, RandomSamplingTCR.IsRoQuery]
    · exact (ht trivial).elim
    · simp only [implB, signB, StateT.run_mk]
      split_ifs
      · simp [RandomSamplingTCR.IsRoQuery]
      · trivial

theorem length_lt_card {used : List LeafId} {F : Finset LeafId} {id : LeafId}
    (hnd : used.Nodup) (hsub : ∀ x ∈ used, x ∈ F) (hid : id ∈ F) (hn : id ∉ used) :
    used.length < F.card := by
  rw [← List.toFinset_card_of_nodup hnd]
  have hs : used.toFinset ⊆ F := fun x hx => hsub x (List.mem_toFinset.1 hx)
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hs).2
    ⟨id, hid, fun h => hn (List.mem_toFinset.1 h)⟩)

/-- `B0`'s invariant for the challenge count: the used leaves are distinct anchors. -/
def UsedInv (K : Keys pr) (s : BSt pr Msg) : Prop :=
  s.used.Nodup ∧ ∀ id ∈ s.used, id ∈ leafIds P.hsf K.S

omit [Nontrivial Msg] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem record_used (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId) (s : BSt pr Msg)
    (r : Option (pr.Digest × pr.Y)) : (record pr Msg K sk q s r).2.used = s.used ++ [q.2] := by
  rcases r with _ | ⟨_, _⟩ <;> rfl

omit [Nontrivial Msg] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem implB_chalBound (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : BSt pr Msg) (hs : UsedInv pr Msg K s) :
    ((simulateQ (implB pr Msg K sk) oa).run s).IsQueryBoundP (IsChal pr Msg)
      ((leafIds P.hsf K.S).card - s.used.length) := by
  refine isQueryBoundP_run_of_pot (implB pr Msg K sk) (UsedInv pr Msg K)
    (fun s => (leafIds P.hsf K.S).card - s.used.length) (fun t s hs z hz => ?_)
    (fun t s hs β k hk => ?_) oa s hs
  · rcases t with t | q
    · simp only [implB_inl_run, support_map, Set.mem_image] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact hs
    · simp only [implB, signB, StateT.run_mk] at hz
      split_ifs at hz with hc
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨r, _, rfl⟩ := hz
        rw [UsedInv, record_used]
        refine ⟨List.nodup_append.2 ⟨hs.1, List.nodup_singleton _, ?_⟩, fun id hid => ?_⟩
        · intro a ha b hb hab
          rw [List.mem_singleton] at hb
          subst hb hab
          exact hc.2 ha
        · rcases List.mem_append.1 hid with h | h
          · exact hs.2 id h
          · rw [List.mem_singleton.1 h]; exact hc.1
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hs
  · rcases t with t | q
    · simp only [implB_inl_run, bind_map_left] at hk ⊢
      rcases t with n | x
      · simp only [fwd]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [RandomSamplingTCR.IsChalQuery]), fun u => by
          simpa [RandomSamplingTCR.IsChalQuery] using hk (u, s) (by simp [fwd])⟩
      · simp only [fwd]
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [RandomSamplingTCR.IsChalQuery]), fun u => by
          simpa [RandomSamplingTCR.IsChalQuery] using hk (u, s) (by simp [fwd])⟩
    · simp only [implB, signB, StateT.run_mk] at hk ⊢
      split_ifs at hk ⊢ with hc
      · rw [bind_map_left, isQueryBoundP_query_bind_iff]
        have hlt := length_lt_card hs.1 hs.2 hc.1 hc.2
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        have := hk (record pr Msg K sk q s u) (by simp)
        rw [record_used, List.length_append, List.length_singleton] at this
        simpa [RandomSamplingTCR.IsChalQuery, Nat.sub_add_eq] using this
      · rw [pure_bind]
        exact hk _ (by simp)


omit [Fintype pr.Y] [DecidableEq pr.PkSeed] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [DecidableEq Msg] in
/-- The bound of a valid branch of `stage2B` from a bound on its signing phase. -/
theorem stage2B_bound {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (pk : pr.PkSeed) (z : Structure × A.State)
    (p : ℕ ⊕ (ThIn pr Msg ⊕ ((pr.Y × Idx) × Msg)) → Prop) [DecidablePred p]
    (hp : ∀ n, ¬ p (.inl n)) (m : ℕ)
    (h : z.1.TreeValid P.hsf → ∀ (f : SkIdx P z.1 → pr.Y) (pkSl : pr.Y),
      ((simulateQ (implB pr Msg ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩
        (skOf pr z.1 f)) (stage2Prog pr Msg slKeygen A z.2
          ⟨z.1, pk, pkSl, pkSfOf pr z.1 pk (skOf pr z.1 f)⟩)).run
        (BSt.init pr Msg)).IsQueryBoundP p m) :
    (stage2B pr Msg slKeygen A pk z).IsQueryBoundP p m := by
  unfold stage2B
  by_cases hv : z.1.TreeValid P.hsf
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_not.2 hv))]
    exact (isQueryBoundP_bind (liftM_bound pr Msg _ p hp) fun f _ =>
      isQueryBoundP_bind (liftM_bound pr Msg _ p hp) fun pkSl _ =>
        isQueryBoundP_bind (h hv f pkSl) fun _ _ => isQueryBoundP_pure _ _ 0).mono
      (by omega)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    exact isQueryBoundP_pure _ _ _

/-- **The reduction `B₀` of Claim 4.1** (Algorithm 4) against SM-rTCR of `H_msg^sf` with
`P = PK.seed`, `T = (PK.sf, idx)`, `m = M`, `ρ = R`: at most `q_{h,1} + q_{h,2} + 1` queries to
`Th` (the forwarded queries and the verification of the forgery) and at most `L` challenge
queries (one per anchor). -/
noncomputable def _root_.ShrincsSecurity.Fxmss.Rom.B0 {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    RandomSamplingTCR.Adversary pr.PkSeed (pr.Y × Idx) Msg pr.Y pr.Digest (qh₁ + qh₂ + 1) L where
  main := mainB pr Msg slKeygen A.toFxmssAdversary
  roBound pk :=
    (isQueryBoundP_bind (n := qh₁) (m := qh₂ + 1) (fwd_roBound pr Msg A.roBound₁) fun z _ =>
      stage2B_bound pr Msg slKeygen _ pk z (IsThQuery pr Msg) (fun _ h => h) _ fun _ _ _ =>
        implB_roBound pr Msg _ _ (stage2Prog_roBound pr Msg slKeygen A _ _) _).mono
      (by omega)
  chalBound pk := by
    refine (isQueryBoundP_bind (n := 0) (m := L) (fwd_chalBound pr Msg A.chooseShape)
      fun z hz => ?_).mono (by omega)
    have hz' : z ∈ support A.chooseShape := support_simulateQ_subset _ _ hz
    refine stage2B_bound pr Msg slKeygen _ pk z (IsChal pr Msg) (fun _ h => h) _ fun hv f pkSl => ?_
    have hcard : (leafIds P.hsf z.1).card ≤ L :=
      Finset.card_image_le.trans (A.anchors_le z hz' hv)
    exact (implB_chalBound pr Msg _ _ _ _
      ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩).mono
      (by simpa [BSt.init] using hcard)

/-! ## The simulation: the game's oracles under `B0` -/

/-- The game's oracles of the SM-rTCR experiment with `Prop ≡ 1`, `K = 1`, cap `L`. -/
noncomputable abbrev gImpl (L : ℕ) (pk : pr.PkSeed) :
    QueryImpl (B0Spec pr Msg) (StateT (GSt pr Msg) ProbComp) :=
  RandomSamplingTCR.gameImpl (fun _ => true) 1 L pk

/-- `B0`'s signing phase run under the game's oracles, flattened into one handler over
`B0`'s state and the game state. -/
noncomputable abbrev flatImpl (L : ℕ) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (BSt pr Msg × GSt pr Msg) ProbComp) :=
  ((gImpl pr Msg L K.pk).mapStateTBase (implB pr Msg K sk)).flattenStateT

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg]
  [SampleableType pr.Y] [DecidableEq pr.Digest] in
/-- The lazy `Th` at a translated point, projected onto the random-oracle cache, is the lazy
`H_msg^sf` of the games. -/
theorem roImpl_proj (x : RoIn pr Msg) (b : BSt pr Msg) (g : GSt pr Msg) :
    (fun y : pr.Digest × GSt pr Msg => (y.1, proj pr Msg (b, y.2))) <$>
        (RandomSamplingTCR.roImpl (roToTh pr Msg x)).run g =
      (roStep pr Msg x).run (proj pr Msg (b, g)) := by
  rw [RandomSamplingTCR.roImpl_run]
  simp only [roStep, StateT.run_mk]
  rw [show (proj pr Msg (b, g)).cache x = g.table (roToTh pr Msg x) from rfl]
  cases h : g.table (roToTh pr Msg x) with
  | some d => simp
  | none =>
    simp only [Functor.map_map]
    congr 1
    funext d
    simp only [proj, Prod.mk.injEq, true_and]
    congr 1
    refine QueryCache.ext fun x' => ?_
    by_cases hx : x' = x
    · subst hx
      simp [cacheOf]
    · simp [cacheOf, hx, Function.update_of_ne ((roToTh_injective pr Msg).ne hx)]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg]
  [SampleableType pr.Y] [DecidableEq pr.Digest] in
/-- The same projection onto the random oracle of the structure phase. -/
theorem roImpl_proj_rom (x : RoIn pr Msg) (g : GSt pr Msg) :
    Prod.map id (cacheOf pr Msg) <$> (RandomSamplingTCR.roImpl (roToTh pr Msg x)).run g =
      ((roSpec pr Msg).randomOracle x).run (cacheOf pr Msg g) := by
  rw [RandomSamplingTCR.roImpl_run, randomOracle.run_eq]
  rw [show (cacheOf pr Msg g) x = g.table (roToTh pr Msg x) from rfl]
  cases h : g.table (roToTh pr Msg x) with
  | some d => simp
  | none =>
    dsimp only
    rw [Functor.map_map, map_eq_bind_pure_comp]
    refine bind_congr fun d => ?_
    simp only [Function.comp_apply, Prod.map, id]
    congr 2
    refine QueryCache.ext fun x' => ?_
    by_cases hx : x' = x
    · subst hx
      simp [cacheOf]
    · simp [cacheOf, hx, Function.update_of_ne ((roToTh_injective pr Msg).ne hx)]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem gfwd_run_unif (L : ℕ) (pk : pr.PkSeed) (n : ℕ) (g : GSt pr Msg) :
    (simulateQ (gImpl pr Msg L pk) (fwd pr Msg (.inl n))).run g =
      (fun u => (u, g)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp only [fwd, simulateQ_spec_query]
  exact RandomSamplingTCR.gameImpl_unif_run _ _ _ _ _ _

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem gfwd_run_ro (L : ℕ) (pk : pr.PkSeed) (x : RoIn pr Msg) (g : GSt pr Msg) :
    (simulateQ (gImpl pr Msg L pk) (fwd pr Msg (.inr x))).run g =
      (RandomSamplingTCR.roImpl (roToTh pr Msg x)).run g := by
  simp only [fwd, simulateQ_spec_query]
  rfl

omit [Nontrivial Msg] [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed]
  [DecidableEq pr.Digest] in
theorem flat_run_inl (L : ℕ) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (t : ℕ ⊕ RoIn pr Msg)
    (b : BSt pr Msg) (g : GSt pr Msg) :
    ((flatImpl pr Msg L K sk) (.inl t)).run (b, g) =
      (fun y => (y.1, (b, y.2))) <$> (simulateQ (gImpl pr Msg L K.pk) (fwd pr Msg t)).run g := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run, implB_inl_run]
  simp [Functor.map_map]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem flat_run_other (L : ℕ) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (b : BSt pr Msg) (g : GSt pr Msg) (hc : ¬ (q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ b.used)) :
    ((flatImpl pr Msg L K sk) (.inr q)).run (b, g) =
      pure (none, (⟨b.used, b.log ++ [q.1], b.recs⟩, g)) := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp [implB, signB, hc]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem flat_run_fresh (L : ℕ) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId)
    (b : BSt pr Msg) (g : GSt pr Msg) (hc : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ b.used)
    (hnr : ¬ (L ≤ g.chal.length ∨ TweakReserved Prod.fst g.chal (K.pkSf, toIdx q.2))) :
    ((flatImpl pr Msg L K sk) (.inr q)).run (b, g) =
      ($ᵗ pr.Y) >>= fun ρ =>
        (RandomSamplingTCR.roImpl (K.pk, (K.pkSf, toIdx q.2), (q.1, ρ))).run g >>= fun z =>
          pure (some (ρ, sigOf pr K sk q.2 z.1),
            (⟨b.used ++ [q.2], b.log ++ [q.1],
              Function.update b.recs q.2 (some ⟨q.1, ρ, z.1, sigOf pr K sk q.2 z.1⟩)⟩,
              { z.2 with chal := z.2.chal ++ [((K.pkSf, toIdx q.2), q.1, some ρ)] })) := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [gImpl, implB, signB, StateT.run_mk, ite_eq_left_of_eq_true _ _ (eq_true hc),
    simulateQ_map, simulateQ_spec_query, StateT.run_map]
  erw [RandomSamplingTCR.gameImpl_chal_run, RandomSamplingTCR.chalImpl_run,
    ite_eq_right_of_eq_false _ _ (eq_false hnr)]
  simp [RandomSamplingTCR.resample_succ_run, record, Functor.map_map]

/-- The challenge list `Q` the game records for `B0`'s used leaves. -/
noncomputable def chalOf (K : Keys pr) (s : BSt pr Msg) :
    List ((pr.Y × Idx) × Msg × Option pr.Y) :=
  s.used.map fun id => ((K.pkSf, toIdx id),
    ((s.recs id).map Rec.msg).getD (Classical.arbitrary Msg), (s.recs id).map Rec.rand)

/-- The invariant of the simulation: the used leaves are distinct anchors, and the game's
challenge list is `B0`'s record of them. -/
def Inv (K : Keys pr) (z : BSt pr Msg × GSt pr Msg) : Prop :=
  UsedInv pr Msg K z.1 ∧ z.2.chal = chalOf pr Msg K z.1

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] [Nontrivial Msg] in
/-- The anchors of a valid structure have identifiers fitting `idx` (`hsf ≤ 255`). -/
theorem leaf_bounds (hP : P.Valid) {S : Structure} (hS : S.TreeValid P.hsf) {id : LeafId}
    (h : id ∈ leafIds P.hsf S) : id.height < 256 ∧ id.index < 2 ^ 64 := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  have := hP.hsf_le
  exact ⟨by simp only [Node.toLeafId]; omega, hS.anchor_idx_lt v hv⟩

omit [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
/-- **The challenge oracle never refuses `B0`**: fewer than `|leafIds| ≤ L` leaves are used, and
the tweaks `(PK.sf, idx)` of distinct anchors are distinct. -/
theorem not_refused (hP : P.Valid) (L : ℕ) (K : Keys pr) (hS : K.S.TreeValid P.hsf)
    (hcard : (leafIds P.hsf K.S).card ≤ L) {b : BSt pr Msg} {g : GSt pr Msg}
    (hI : Inv pr Msg K (b, g)) {id : LeafId} (hc : id ∈ leafIds P.hsf K.S ∧ id ∉ b.used) :
    ¬ (L ≤ g.chal.length ∨ TweakReserved Prod.fst g.chal (K.pkSf, toIdx id)) := by
  rw [hI.2]
  rintro (h | ⟨e, he, het⟩)
  · have : b.used.length < _ := length_lt_card hI.1.1 hI.1.2 hc.1 hc.2
    simp only [chalOf, List.length_map] at h
    omega
  · simp only [chalOf, List.mem_map] at he
    obtain ⟨id', hid', rfl⟩ := he
    simp only [Prod.mk.injEq] at het
    have h1 := leaf_bounds hP hS (hI.1.2 id' hid')
    have h2 := leaf_bounds hP hS hc.1
    rw [toIdx_inj h1.1 h1.2 h2.1 h2.2 het.2] at hid'
    exact hc.2 hid'

omit [Nontrivial Msg] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem usedInv_snoc (K : Keys pr) {s : BSt pr Msg} (hs : UsedInv pr Msg K s) {id : LeafId}
    (hc : id ∈ leafIds P.hsf K.S ∧ id ∉ s.used) {s' : BSt pr Msg} (h : s'.used = s.used ++ [id]) :
    UsedInv pr Msg K s' := by
  rw [UsedInv, h]
  refine ⟨List.nodup_append.2 ⟨hs.1, List.nodup_singleton _, ?_⟩, fun x hx => ?_⟩
  · intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb hab
    exact hc.2 ha
  · rcases List.mem_append.1 hx with h | h
    · exact hs.2 x h
    · rw [List.mem_singleton.1 h]; exact hc.1

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
/-- The handler of `F.0` with the secret table `sk` (`implG` with `sigOf`). -/
theorem implG_run_fresh (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId) (s : St pr Msg)
    (hc : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used) :
    ((implG pr Msg K sk) (.inr q)).run s =
      ($ᵗ pr.Y) >>= fun R => (roStep pr Msg (roIn pr Msg R K.pk K.pkSf q.2 q.1)).run s >>= fun z =>
        pure (some (R, sigOf pr K sk q.2 z.1), { z.2 with
          used := z.2.used ++ [q.2], log := z.2.log ++ [q.1],
          recs := Function.update z.2.recs q.2 (some ⟨q.1, R, z.1, sigOf pr K sk q.2 z.1⟩) }) := by
  simp [implG, impl, signStep, hc, sigOf]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem implG_run_other (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (q : Msg × LeafId) (s : St pr Msg)
    (hc : ¬ (q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used)) :
    ((implG pr Msg K sk) (.inr q)).run s = pure (none, { s with log := s.log ++ [q.1] }) := by
  simp [implG, impl, signStep, hc]

omit [Nontrivial Msg] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
theorem chal_roImpl {y : ThIn pr Msg} {g : GSt pr Msg} {z : pr.Digest × GSt pr Msg}
    (hz : z ∈ support ((RandomSamplingTCR.roImpl y).run g)) : z.2.chal = g.chal := by
  rcases RandomSamplingTCR.mem_support_roImpl_run hz with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
/-- **The simulation preserves the invariant.** -/
theorem flat_inv (hP : P.Valid) (L : ℕ) (K : Keys pr) (hS : K.S.TreeValid P.hsf)
    (hcard : (leafIds P.hsf K.S).card ≤ L) (sk : LeafId → ℕ → pr.Y) (t : (fullSpec pr Msg).Domain)
    (s : BSt pr Msg × GSt pr Msg) (hs : Inv pr Msg K s) :
    ∀ z ∈ support ((flatImpl pr Msg L K sk t).run s), Inv pr Msg K z.2 := by
  obtain ⟨b, g⟩ := s
  intro z hz
  rcases t with t | q
  · rw [flat_run_inl, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have : y.2.chal = g.chal := by
      rcases t with n | x
      · rw [gfwd_run_unif, support_map] at hy
        obtain ⟨_, _, rfl⟩ := hy
        rfl
      · rw [gfwd_run_ro] at hy
        exact chal_roImpl pr Msg hy
    exact ⟨hs.1, this.trans hs.2⟩
  · by_cases hc : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ b.used
    · rw [flat_run_fresh pr Msg L K sk q b g hc (not_refused pr Msg hP L K hS hcard hs hc)] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨ρ, -, y, hy, rfl⟩ := hz
      refine ⟨usedInv_snoc pr Msg K hs.1 hc rfl, ?_⟩
      have h2 : g.chal = chalOf pr Msg K b := hs.2
      simp only [chal_roImpl pr Msg hy, h2, chalOf, List.map_append, List.map_cons,
        List.map_nil]
      congr 1
      · refine List.map_congr_left fun x hx => ?_
        have : x ≠ q.2 := fun h => hc.2 (h ▸ hx)
        simp [Function.update_of_ne this]
      · simp
    · rw [flat_run_other pr Msg L K sk q b g hc, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
/-- **One step of the simulation projects onto one step of `F.0`.** -/
theorem flat_proj (hP : P.Valid) (L : ℕ) (K : Keys pr) (hS : K.S.TreeValid P.hsf)
    (hcard : (leafIds P.hsf K.S).card ≤ L) (sk : LeafId → ℕ → pr.Y) (t : (fullSpec pr Msg).Domain)
    (s : BSt pr Msg × GSt pr Msg) (hs : Inv pr Msg K s) :
    Prod.map id (proj pr Msg) <$> (flatImpl pr Msg L K sk t).run s =
      (implG pr Msg K sk t).run (proj pr Msg s) := by
  obtain ⟨b, g⟩ := s
  rcases t with (n | x) | q
  · rw [flat_run_inl, gfwd_run_unif]
    simp [implG, impl, Functor.map_map]
  · rw [flat_run_inl, gfwd_run_ro, Functor.map_map]
    exact roImpl_proj pr Msg x b g
  · by_cases hc : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ b.used
    · rw [flat_run_fresh pr Msg L K sk q b g hc (not_refused pr Msg hP L K hS hcard hs hc),
        implG_run_fresh pr Msg K sk q _ hc]
      simp only [map_bind, map_pure]
      refine bind_congr fun ρ => ?_
      rw [← roImpl_proj, bind_map_left]
      rfl
    · rw [flat_run_other pr Msg L K sk q b g hc, implG_run_other pr Msg K sk q _ hc]
      rfl

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
/-- **The simulation projects onto `F.0`**, from any state satisfying the invariant. -/
theorem flat_run_proj (hP : P.Valid) (L : ℕ) (K : Keys pr) (hS : K.S.TreeValid P.hsf)
    (hcard : (leafIds P.hsf K.S).card ≤ L) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : BSt pr Msg × GSt pr Msg) (hs : Inv pr Msg K s) :
    Prod.map id (proj pr Msg) <$> (simulateQ (flatImpl pr Msg L K sk) oa).run s =
      (simulateQ (implG pr Msg K sk) oa).run (proj pr Msg s) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (Inv pr Msg K) (proj pr Msg)
    (flat_inv pr Msg hP L K hS hcard sk) (flat_proj pr Msg hP L K hS hcard sk) oa s hs

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
theorem flat_run_inv (hP : P.Valid) (L : ℕ) (K : Keys pr) (hS : K.S.TreeValid P.hsf)
    (hcard : (leafIds P.hsf K.S).card ≤ L) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : BSt pr Msg × GSt pr Msg) (hs : Inv pr Msg K s) :
    ∀ z ∈ support ((simulateQ (flatImpl pr Msg L K sk) oa).run s), Inv pr Msg K z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (Inv pr Msg K)
    (flat_inv pr Msg hP L K hS hcard sk) oa s hs

/-! ## Facts of `F.0` read off its final state -/

/-- Every record of `F.0` is at a used leaf, its message was queried, and its point is cached with
its digest. -/
def GInv (K : Keys pr) (s : St pr Msg) : Prop :=
  ∀ id rr, s.recs id = some rr →
    id ∈ s.used ∧ rr.msg ∈ s.log ∧
      s.cache (roIn pr Msg rr.rand K.pk K.pkSf id rr.msg) = some rr.digest

/-- The cache only grows. -/
def GMono (c : (roSpec pr Msg).QueryCache) (s : St pr Msg) : Prop :=
  ∀ x v, c x = some v → s.cache x = some v

omit [Nontrivial Msg] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
theorem roStep_support {x : RoIn pr Msg} {s : St pr Msg} {z : pr.Digest × St pr Msg}
    (hz : z ∈ support ((roStep pr Msg x).run s)) :
    z.2.cache x = some z.1 ∧ GMono pr Msg s.cache z.2 ∧ z.2.used = s.used ∧ z.2.log = s.log ∧
      z.2.recs = s.recs := by
  simp only [roStep, StateT.run_mk] at hz
  cases h : s.cache x with
  | some d =>
    rw [h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨h, fun _ _ h => h, rfl, rfl, rfl⟩
  | none =>
    rw [h] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨d, -, rfl⟩ := hz
    refine ⟨by simp, fun x' v hx' => ?_, rfl, rfl, rfl⟩
    have : x' ≠ x := fun h' => by rw [h', h] at hx'; simp at hx'
    simpa [QueryCache.cacheQuery_of_ne _ _ this] using hx'

omit [Nontrivial Msg] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [DecidableEq Msg] in
theorem gMono_trans {c : (roSpec pr Msg).QueryCache} {s s' : St pr Msg}
    (h : GMono pr Msg c s) (h' : GMono pr Msg s.cache s') : GMono pr Msg c s' :=
  fun x v hx => h' x v (h x v hx)

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem implG_run_unif (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (n : ℕ) (s : St pr Msg) :
    ((implG pr Msg K sk) (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [implG, impl]

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
/-- One step of `F.0` grows the cache and preserves `GInv`. -/
theorem implG_step (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (t : (fullSpec pr Msg).Domain)
    (s : St pr Msg) :
    ∀ z ∈ support ((implG pr Msg K sk t).run s),
      GMono pr Msg s.cache z.2 ∧ (GInv pr Msg K s → GInv pr Msg K z.2) := by
  intro z hz
  rcases t with (n | x) | q
  · rw [implG_run_unif, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact ⟨fun _ _ h => h, id⟩
  · have hz' : z ∈ support ((roStep pr Msg x).run s) := hz
    obtain ⟨-, hm, hu, hl, hr⟩ := roStep_support pr Msg hz'
    refine ⟨hm, fun hI id rr hrr => ?_⟩
    rw [hr] at hrr
    obtain ⟨h1, h2, h3⟩ := hI id rr hrr
    exact ⟨hu ▸ h1, hl ▸ h2, hm _ _ h3⟩
  · by_cases hc : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
    · rw [implG_run_fresh pr Msg K sk q s hc] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨R, -, y, hy, rfl⟩ := hz
      obtain ⟨hc', hm, hu, hl, hr⟩ := roStep_support pr Msg hy
      refine ⟨hm, fun hI id rr hrr => ?_⟩
      by_cases hid : id = q.2
      · subst hid
        simp only [Function.update_self, Option.some.injEq] at hrr
        subst hrr
        exact ⟨by simp, by simp, hc'⟩
      · simp only [Function.update_of_ne hid, hr] at hrr
        obtain ⟨h1, h2, h3⟩ := hI id rr hrr
        exact ⟨by simp [hu, h1], by simp [hl, h2], hm _ _ h3⟩
    · rw [implG_run_other pr Msg K sk q s hc, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨fun _ _ h => h, fun hI id rr hrr => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hI id rr hrr
      exact ⟨h1, by simp [h2], h3⟩

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
theorem implG_run (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : St pr Msg) (hs : GInv pr Msg K s) :
    ∀ z ∈ support ((simulateQ (implG pr Msg K sk) oa).run s),
      GMono pr Msg s.cache z.2 ∧ GInv pr Msg K z.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (fun s' => GMono pr Msg s.cache s' ∧ GInv pr Msg K s')
    (fun t s' hs' z hz => ⟨gMono_trans pr Msg hs'.1 (implG_step pr Msg K sk t s' z hz).1,
      (implG_step pr Msg K sk t s' z hz).2 hs'.2⟩) oa s ⟨fun _ _ h => h, hs⟩

omit [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **The final state of `F.0`'s signing phase**: the verification query cached the forgery's
point with `y*`, and every record satisfies `GInv`. -/
theorem stage2_facts {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (s : St pr Msg) (hs : GInv pr Msg K s)
    (r : (Msg × LeafId × Sig pr × pr.Digest) × St pr Msg)
    (hr : r ∈ support ((simulateQ (implG pr Msg K sk) (stage2Prog pr Msg slKeygen A st K)).run s)) :
    r.2.cache (roIn pr Msg r.1.2.2.1.1 K.pk K.pkSf r.1.2.1 r.1.1) = some r.1.2.2.2 ∧
      GInv pr Msg K r.2 := by
  simp only [stage2Prog, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨⟨o, s1⟩, h1, ⟨yf, s2⟩, h2, ⟨u, s3⟩, h3, rfl⟩ := hr
  have hI1 := (implG_run pr Msg K sk _ s hs _ h1).2
  have h2' : (yf, s2) ∈ support ((roStep pr Msg
      (roIn pr Msg o.2.2.1 K.pk K.pkSf o.2.1 o.1)).run s1) := h2
  obtain ⟨hc2, -⟩ := roStep_support pr Msg h2'
  have hI2 := (implG_step pr Msg K sk _ s1 _ h2).2 hI1
  obtain ⟨hm3, hI3⟩ := implG_run pr Msg K sk _ s2 hI2 _ h3
  exact ⟨hm3 _ _ hc2, hI3⟩

/-! ## The final check and the structure phase -/

omit [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] in
/-- **The final check of the experiment succeeds on `Win ∧ C₁`**: the forgery's leaf is the
`j`-th target, `(M*, R*) ≠ (M_j, R_j)`, and both points are cached with `y*`. -/
theorem isCollision_true (K : Keys pr) (b : BSt pr Msg) (g : GSt pr Msg)
    (hI : Inv pr Msg K (b, g)) (r : Msg × LeafId × Sig pr × pr.Digest) (rr : Rec pr Msg)
    (hrec : b.recs r.2.1 = some rr) (hused : r.2.1 ∈ b.used) (hne : rr.msg ≠ r.1)
    (h1 : g.table (K.pk, (K.pkSf, toIdx r.2.1), (r.1, r.2.2.1.1)) = some r.2.2.2)
    (h2 : g.table (K.pk, (K.pkSf, toIdx r.2.1), (rr.msg, rr.rand)) = some r.2.2.2) :
    (RandomSamplingTCR.isCollision K.pk g.chal (out pr Msg (r, b))).run g = pure (true, g) := by
  have hQ : g.chal[b.used.idxOf r.2.1]? = some ((K.pkSf, toIdx r.2.1), rr.msg, some rr.rand) := by
    rw [hI.2]
    simp [chalOf, List.getElem?_idxOf hused, hrec]
  have hne' : (r.1, r.2.2.1.1) ≠ (rr.msg, rr.rand) := fun h => hne (congrArg Prod.fst h).symm
  unfold RandomSamplingTCR.isCollision
  simp only [out, hQ]
  simp [RandomSamplingTCR.roImpl_run, h1, h2, hne']

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
/-- The structure phase under `B0` projects onto the structure phase of the games. -/
theorem stage1_proj (L : ℕ) (pk : pr.PkSeed) {α : Type} (oa : OracleComp (spec pr Msg) α)
    (g : GSt pr Msg) :
    Prod.map id (cacheOf pr Msg) <$>
        (simulateQ (gImpl pr Msg L pk) (simulateQ (fwd pr Msg) oa)).run g =
      (simulateQ (roSpec pr Msg).romImpl oa).run (cacheOf pr Msg g) := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := fun t => simulateQ (gImpl pr Msg L pk) (fwd pr Msg t)) (fun t => rfl)]
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t g => ?_) oa g
  rcases t with n | x
  · rw [gfwd_run_unif]
    simp [Functor.map_map, unifFwdImpl]
  · rw [gfwd_run_ro, roImpl_proj_rom]
    rfl

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
/-- The structure phase makes no challenge query. -/
theorem stage1_chal (L : ℕ) (pk : pr.PkSeed) {α : Type} (oa : OracleComp (spec pr Msg) α)
    (g : GSt pr Msg) :
    ∀ p ∈ support ((simulateQ (gImpl pr Msg L pk) (simulateQ (fwd pr Msg) oa)).run g),
      p.2.chal = g.chal := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := fun t => simulateQ (gImpl pr Msg L pk) (fwd pr Msg t)) (fun t => rfl)]
  refine OracleComp.simulateQ_run_preserves_inv_of_query _ (fun g' => g'.chal = g.chal)
    (fun t g' hg' z hz => ?_) oa g rfl
  rcases t with n | x
  · rw [gfwd_run_unif, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hg'
  · rw [gfwd_run_ro] at hz
    exact (chal_roImpl pr Msg hz).trans hg'

/-! ## Claim 4.1 -/

omit [Inhabited pr.Y] [Fintype pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Digest]
  [Nontrivial Msg] in
/-- Sampling a lifted `ProbComp` under the game's oracles. -/
theorem gImpl_liftM_bind_run (L : ℕ) (pk : pr.PkSeed) {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp (B0Spec pr Msg) β) (g : GSt pr Msg) :
    (simulateQ (gImpl pr Msg L pk) ((liftM oa : OracleComp (B0Spec pr Msg) α) >>= k)).run g =
      oa >>= fun x => (simulateQ (gImpl pr Msg L pk) (k x)).run g :=
  simulateQ_add_liftM_bind_run _ oa k g

omit [Fintype pr.Y] in
/-- **The signing phase**: on `Win ∧ C₁` of `F.0`, the experiment with `B0` outputs `1`. -/
theorem stage2_le (hP : P.Valid) (L : ℕ) (K : Keys pr) (hS : K.S.TreeValid P.hsf)
    (hcard : (leafIds P.hsf K.S).card ≤ L) (sk : LeafId → ℕ → pr.Y) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) (st : A.State) (g1 : GSt pr Msg)
    (hg1 : g1.chal = []) :
    Pr{let o ← (simulateQ (implG pr Msg K sk) (stage2Prog pr Msg slKeygen A st K)).run
        (St.init pr Msg (cacheOf pr Msg g1)) >>= fun r =>
          pure (some (Transcript.ofRun pr Msg K r))}[WinC1 o] ≤
      Pr{let b ← (simulateQ (gImpl pr Msg L K.pk)
          ((simulateQ (implB pr Msg K sk) (stage2Prog pr Msg slKeygen A st K)).run
            (BSt.init pr Msg) >>= fun r => pure (out pr Msg r))).run g1 >>= fun z =>
          (RandomSamplingTCR.isCollision K.pk z.2.chal z.1).run z.2 >>= fun w =>
            pure w.1}[b = true] := by
  have hI0 : Inv pr Msg K (BSt.init pr Msg, g1) :=
    ⟨⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim⟩, by simp [hg1, chalOf, BSt.init]⟩
  rw [show St.init pr Msg (cacheOf pr Msg g1) = proj pr Msg (BSt.init pr Msg, g1) from rfl,
    ← flat_run_proj pr Msg hP L K hS hcard sk _ _ hI0, bind_map_left]
  rw [simulateQ_bind, StateT.run_bind,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, bind_map_left, bind_assoc]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun w hw => ?_
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  by_cases hW : WinC1 (some (Transcript.ofRun pr Msg K (Prod.map id (proj pr Msg) w)))
  · obtain ⟨⟨-, hlog⟩, rr, hrr, hd⟩ := hW
    have hwI := flat_run_inv pr Msg hP L K hS hcard sk _ _ hI0 w hw
    have hr : Prod.map id (proj pr Msg) w ∈ support ((simulateQ (implG pr Msg K sk)
        (stage2Prog pr Msg slKeygen A st K)).run (proj pr Msg (BSt.init pr Msg, g1))) := by
      rw [← flat_run_proj pr Msg hP L K hS hcard sk _ _ hI0, support_map]
      exact Set.mem_image_of_mem _ hw
    obtain ⟨hc, hG⟩ := stage2_facts pr Msg slKeygen A st K sk _
      (fun _ _ h => by simp [proj, BSt.init] at h) _ hr
    obtain ⟨hu, hm, hcache⟩ := hG _ _ hrr
    have hm' : rr.msg ∈ w.2.1.log := hm
    have hlog' : w.1.1 ∉ w.2.1.log := hlog
    have hd' : rr.digest = w.1.2.2.2 := hd
    rw [isCollision_true pr Msg K w.2.1 w.2.2 hwI w.1 rr hrr hu (fun h => hlog' (h ▸ hm')) hc
      (by rw [← hd']; exact hcache)]
    simp only [pure_bind, prEvent_pure]
    split_ifs <;> simp
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun o ho => by
      rw [support_pure, Set.mem_singleton_iff] at ho
      exact ho ▸ hW]
    exact zero_le

omit [Fintype pr.Y] in
/-- **Claim 4.1** (`F.0 → F.1`): the probability that the forger wins `F.0` and the abort event
`C₁` occurs (the forgery's leaf was signed with the forgery's digest `y_j = y*`) is at most the
success of `B₀` against SM-rTCR of `H_msg^sf` with `Prop ≡ 1`, `K = 1`:
`Succ_{F.0}(A) − Succ_{F.1}(A) ≤ Succ^{SM-rTCR,1}(B₀)`. -/
theorem _root_.ShrincsSecurity.Fxmss.Rom.claim_4_1 (hP : P.Valid) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameG pr Msg slKeygen A.toFxmssAdversary}[WinC1 o] ≤
      RandomSamplingTCR.advantage (fun _ => true) 1 (B0 pr Msg slKeygen A) := by
  unfold RandomSamplingTCR.advantage RandomSamplingTCR.experiment gameG
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pk => ?_
  have hs1 : stage1 pr Msg slKeygen A.toFxmssAdversary =
      Prod.map id (cacheOf pr Msg) <$> (simulateQ (gImpl pr Msg L pk)
        (simulateQ (fwd pr Msg) A.chooseShape)).run
          (RandomSamplingTCR.GameState.init pr.PkSeed (pr.Y × Idx) Msg pr.Y pr.Digest) := by
    rw [stage1_proj]
    rfl
  rw [hs1, bind_map_left]
  rw [show (B0 pr Msg slKeygen A).main pk = mainB pr Msg slKeygen A.toFxmssAdversary pk from rfl,
    mainB, simulateQ_bind, StateT.run_bind, bind_assoc]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => ?_
  have hchal : p.2.chal = [] := stage1_chal pr Msg L pk _ _ p hp
  have hcs : p.1 ∈ support A.chooseShape :=
    support_simulateQ_subset _ _ (mem_support_of_mem_support_simulateQ_run _ _ _ hp)
  obtain ⟨z, g1⟩ := p
  simp only [Prod.map, id, stageG, stage2B]
  by_cases hv : z.1.TreeValid P.hsf
  · simp only [hv, not_true_eq_false, ↓reduceIte, gImpl_liftM_bind_run, bind_assoc]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun f => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSl => ?_
    exact stage2_le pr Msg slKeygen hP L _ hv
      (Finset.card_image_le.trans (A.anchors_le z hcs hv)) _ _ _ g1 hchal
  · simp only [hv, not_false_eq_true, ↓reduceIte]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun o ho => by
      rw [support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact id]
    exact zero_le

end Claim41

end ShrincsSecurity.Fxmss.Rom

end
