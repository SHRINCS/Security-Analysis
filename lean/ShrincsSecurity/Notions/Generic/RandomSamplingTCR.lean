module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTRTCR
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# SM-rTCR in the classical random-oracle model: Corollary G.1

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), **Definition 4.9** (SM-rTCR, lines
2305–2337), the conventions of Appendix G (lines 7681–7687) and **Corollary G.1** (lines
7846–7873, with the classical paragraph 7833–7845 and the games of the proof of Theorem G.1,
lines 7727–7830).

## The game

`experiment` is Definition 4.9 with `Th : P × T × (M × R) → N` a lazily sampled random oracle
(one table in the state, shared by the adversary's queries, the challenge oracle's attempts and
the final check). It is VCVio's standard-model `TweakableHash.SM_DT_RTCR_Experiment`
(`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`) with every
`th.eval pk t x` replaced by a query to the table at `(pk, t, x)`, and with the oracle semantics
kept verbatim:

* `P ←$ P` is sampled and handed to the adversary; there is no collection oracle;
* the challenge list has VCVio's type `SM_DT_RTCR_State T M R = List (T × M × Option R)`;
* `chalImpl` mirrors `SM_DT_RTCR_challengeOracle`: a query at the target cap `p` or at a tweak
  already in `Q` (`TweakReserved Prod.fst`) is refused with `none`, recording and drawing
  nothing; otherwise `resample` (VCVio's `FirstSuccess.runWith` kernel, as in
  `SM_DT_RTCR_resample`) makes up to `K` attempts `ρ ←$ R`, `y := Th(P, T, (m, ρ))`, stops at
  the first `y` with `Prop(y) = 1`, and `(T, m, res.map Prod.snd)` is appended either way;
* `isCollision` has the arms of `SM_DT_RTCR_IsCollision`: an index outside `Q` and an
  exhausted entry `(Tⱼ, mⱼ, ⊥)` lose (the paper's reading, line 7685), otherwise the win is
  `(m*, ρ*) ≠ (mⱼ, ρⱼ) ∧ Th(P, Tⱼ, (m*, ρ*)) = Th(P, Tⱼ, (mⱼ, ρⱼ))`, both evaluated through the
  table (first `(m*, ρ*)`, then `(mⱼ, ρⱼ)`).

The adversary (`Adversary`) gets private coins, `Th` and the challenge oracle, and is bounded by
`IsQueryBoundP` to `q` queries to `Th` and `p` challenge queries; `p` is also the oracle's target
cap, as in the paper. The proof only uses the cap (at most `p` accepted challenges), so the
field `Adversary.chalBound` is carried for fidelity but not used. The paper's convention "the
latest reprogramming counts" concerns its Game 1 and has no counterpart here: the game is
Game 0, in which the table is never overwritten. No assumption `|N| ≥ 2` is needed.

## The bound

`advantage_le` is Corollary G.1,
`Succ^{SM-rTCR,K}_{Th,p,Prop}(A) ≤ (q + 1)/|N| + (K·q + p·K(K-1)/2)/|R|`, and
`advantage_le_of_one` its `K = 1` case `(q + 1)/|N| + q/|R|`.

The proof is direct, without the paper's detour through Lemma C.4 and Avg-Search; it charges the
same quantities. The bad event `Bad` says that some accepted entry `(T, m, ρ)` of `Q` shares its
digest with another cached point at `(P, T)`; a win makes it true (the final evaluation at
`(m*, ρ*)` is charged `1/|N|`, the `+ 1` of `q + 1`). Its probability is bounded by a potential
argument over the run (`prEvent_simulateQ_run_bind_le_of_potential`, proved here: VCVio's
`prEvent_simulateQ_run_le_sum_of_isQueryBoundP` needs a hazard that is a function of a counter,
and VCVio's `IsPotentialStep` needs a single-sample step, while the hazard of a challenge here
depends on the table and the step makes up to `2K` draws). The potential `pot` with `n` direct
queries left is

  `(n + 1)/|N| + K·n/|R| + (p - |Q|)·(K(K-1)/2)/|R| + K·d/|R| + e/|{y | Prop(y)}|`,

where `d` counts the cached points at `P` and a tweak not yet in `Q`, and `e` those of them
holding a digest with `Prop = 1`:

* a fresh direct query at a tweak with an accepted entry hits its digest with probability `1/|N|`
  (`ro_step`); at a tweak not in `Q` it adds `K/|R|` to `K·d/|R|` and, with probability
  `|{Prop}|/|N|`, `1/|{Prop}|` to `e/|{Prop}|`, i.e. `1/|N|` on average;
* an accepted challenge at `(T, m)` (`chal_step`) is bad only if an attempt hits a cached seed —
  the `i`-th with probability at most `(c + i)/|R|`, `c ≤ d_T` the cached seeds at `(P, T, m)`,
  for `K·d_T + K(K-1)/2` over `|R|` — or the accepted fresh digest equals one of the `e_T` digests
  with `Prop = 1` already cached at `(P, T)`, with probability at most `e_T/|{Prop}|`
  (`resample_loopBad_le`); the tweak then leaves the free set, releasing exactly that credit.

Summing the per-tweak credit is the paper's `Σ_c a_c ≤ q` (tweak distinctness), and the
`K(K-1)/2` per challenge is its `Σ_k (k - 1)`. The credit `e/|{Prop}|` is how the
target-after-query case is charged at creation time: a direct query made before the challenge at
its tweak pays `1/|N|` in expectation, not pathwise.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

/-! ## A potential bound for stateful handlers -/

section Potential

variable {ι : Type} {spec : OracleSpec ι} {σ α β : Type}

/-- **The potential bound.** Let `impl` be a stateful handler with an invariant `inv`, a bad event
`bad` and a potential `B n` indexed by the number `n` of charged queries left, monotone in `n`. If
from every good state satisfying the invariant a step's probability of going bad plus its
expected potential afterwards is at most the potential before (with one charged query fewer
after a charged step), and the terminal continuation `g` fires `E` from a good final state with
probability at most `B 0`, then a run with at most `q` charged queries from a good state `s`
followed by `g` fires `E` with probability at most `B q s`. With a constant per-step hazard this
is the usual union bound; here the hazard may depend on the state, paid for by credit stored in
the potential (a supermartingale argument). -/
theorem prEvent_simulateQ_run_bind_le_of_potential
    (impl : QueryImpl spec (StateT σ ProbComp)) (charged : ι → Prop) [DecidablePred charged]
    (inv bad : σ → Prop) (B : ℕ → σ → ℝ≥0∞)
    (hinv : QueryImpl.PreservesInv impl inv)
    (hmono : ∀ n s, B n s ≤ B (n + 1) s)
    (hfree : ∀ t, ¬ charged t → ∀ n s, inv s → ¬ bad s →
      Pr{let z ← (impl t).run s}[bad z.2] +
        ∑' z, Pr{let y ← (impl t).run s}[y = z] * B n z.2 ≤ B n s)
    (hcharged : ∀ t, charged t → ∀ n s, inv s → ¬ bad s →
      Pr{let z ← (impl t).run s}[bad z.2] +
        ∑' z, Pr{let y ← (impl t).run s}[y = z] * B n z.2 ≤ B (n + 1) s)
    (g : α × σ → ProbComp β) (E : β → Prop)
    (hg : ∀ z, inv z.2 → ¬ bad z.2 → Pr{let y ← g z}[E y] ≤ B 0 z.2)
    (oa : OracleComp spec α) {q : ℕ} (hq : oa.IsQueryBoundP charged q) (s : σ)
    (hs : inv s) (hb : ¬ bad s) :
    Pr{let y ← (simulateQ impl oa).run s >>= g}[E y] ≤ B q s := by
  classical
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure x =>
    rw [simulateQ_pure, StateT.run_pure, pure_bind]
    exact (hg (x, s) hs hb).trans (monotone_nat_of_le_succ (fun n => hmono n s) (Nat.zero_le q))
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    obtain ⟨hvalid, hcont⟩ := hq
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      prEvent_bind_eq_tsum]
    have key : ∀ n, (∀ u, (k u).IsQueryBoundP charged n) →
        ∑' z, Pr{let y ← (impl t).run s}[y = z] *
          Pr{let y ← (simulateQ impl (k z.1)).run z.2 >>= g}[E y] ≤
        Pr{let z ← (impl t).run s}[bad z.2] +
          ∑' z, Pr{let y ← (impl t).run s}[y = z] * B n z.2 := by
      intro n hk
      rw [prEvent_eq_tsum_ite, ← tsum_add]
      refine tsum_le_tsum fun z => ?_
      by_cases hz : z ∈ support ((impl t).run s)
      · by_cases hbz : bad z.2
        · simp only [hbz, ite_true]
          exact (mul_le_of_le_one_right' (prEvent_le_one _)).trans le_self_add
        · simp only [hbz, ite_false, zero_add]
          gcongr
          exact ih z.1 (hk z.1) z.2 (hinv t s hs z hz) hbz
      · rw [prEvent_eq_zero_of_not_mem_support _ hz]
        simp
    by_cases ht : charged t
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 :=
        Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.1 (hvalid.resolve_left (· ht)))
      simp only [ht, ↓reduceIte, Nat.add_sub_cancel] at hcont
      exact (key q' hcont).trans (hcharged t ht q' s hs hb)
    · simp only [ht, ↓reduceIte] at hcont
      exact (key q hcont).trans (hfree t ht q s hs hb)

end Potential

/-! ## The game -/

namespace RandomSamplingTCR

variable (P T M R N : Type)

/-- Queries to the random oracle `Th : P × T × (M × R) → N`. -/
abbrev RoSpec : OracleSpec (P × T × (M × R)) := (P × T × (M × R)) →ₒ N

/-- The challenge oracle `O(T, m)`, answered by a digest and its randomness, or `⊥ = none`;
the same signature as VCVio's `TweakableHash.SM_DT_RTCR_challengeSpec`. -/
abbrev ChalSpec : OracleSpec (T × M) := SM_DT_RTCR_challengeSpec T M R N

/-- The adversary's oracles: private coins, the random oracle `Th`, the challenge oracle. -/
abbrev AdvSpec : OracleSpec (ℕ ⊕ ((P × T × (M × R)) ⊕ (T × M))) :=
  unifSpec + (RoSpec P T M R N + ChalSpec T M R N)

/-- A query to `Th`. -/
def IsRoQuery : ℕ ⊕ ((P × T × (M × R)) ⊕ (T × M)) → Prop
  | .inr (.inl _) => True
  | _ => False

/-- A challenge query. -/
def IsChalQuery : ℕ ⊕ ((P × T × (M × R)) ⊕ (T × M)) → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (IsRoQuery P T M R) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsRoQuery] <;> infer_instance

instance : DecidablePred (IsChalQuery P T M R) := fun x => by
  rcases x with _ | _ | _ <;> simp only [IsChalQuery] <;> infer_instance

/-- The experiment's state: the lazily sampled table of `Th`, and the challenge list `Q` in the
format of VCVio's `TweakableHash.SM_DT_RTCR_State` (entries `(T, m, some ρ)` or `(T, m, none)`,
in issue order). -/
structure GameState where
  /-- The lazily sampled table of `Th`. -/
  table : P × T × (M × R) → Option N
  /-- The challenge list `Q`. -/
  chal : SM_DT_RTCR_State T M R

/-- The initial state: empty table, `Q = []`. -/
def GameState.init : GameState P T M R N := ⟨fun _ => none, []⟩

variable {P T M R N}
variable [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R]
  [DecidableEq N] [SampleableType R] [SampleableType N]

/-- The lazily sampled random oracle `Th`, shared by the adversary, the challenge oracle and the
final check. -/
def roImpl (x : P × T × (M × R)) : StateT (GameState P T M R N) ProbComp N := do
  let s ← get
  match s.table x with
  | some d => return d
  | none => do
    let d ← (monadLift ($ᵗ N) : StateT (GameState P T M R N) ProbComp N)
    set { s with table := Function.update s.table x (some d) }
    return d

/-- The sampling loop of Definition 4.9, step 3: up to `K` attempts `ρ ←$ R`,
`y := Th(P, T, (m ‖ ρ))` through the table, stopping at the first `y` with `Prop(y) = 1`. This is
VCVio's `TweakableHash.SM_DT_RTCR_resample` (the same `FirstSuccess.runWith` kernel) with
`th.eval` replaced by the random oracle. -/
def resample (prop : N → Bool) (pk : P) (t : T) (m : M) :
    ℕ → StateT (GameState P T M R N) ProbComp (Option (N × R)) :=
  VCVio.Algorithms.FirstSuccess.runWith
    (do
      let ρ ← (monadLift ($ᵗ R) : StateT (GameState P T M R N) ProbComp R)
      let y ← roImpl (pk, t, (m, ρ))
      return (y, ρ))
    (fun yρ => if prop yρ.1 then some yρ else none)

/-- The challenge oracle `O(T, m)` of Definition 4.9 with target cap `p` and sampling budget `K`.
A query is refused with `none`, recording and drawing nothing, when `|Q| ≥ p` or `T` already
occurs in `Q`; otherwise the sampling loop runs and `(T, m, ρ)` (or `(T, m, ⊥)` on exhaustion) is
appended to `Q`. This mirrors `TweakableHash.SM_DT_RTCR_challengeOracle`. -/
def chalImpl (prop : N → Bool) (K p : ℕ) (pk : P) (tm : T × M) :
    StateT (GameState P T M R N) ProbComp (Option (N × R)) := do
  let s ← get
  if p ≤ s.chal.length ∨ TweakReserved Prod.fst s.chal tm.1 then
    return none
  else
    let res ← resample prop pk tm.1 tm.2 K
    modify fun s => { s with chal := s.chal ++ [(tm.1, tm.2, res.map Prod.snd)] }
    return res

/-- The experiment's handler for the adversary's three oracles. -/
def gameImpl (prop : N → Bool) (K p : ℕ) (pk : P) :
    QueryImpl (AdvSpec P T M R N) (StateT (GameState P T M R N) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState P T M R N) ProbComp) +
    ((fun x => roImpl x : QueryImpl (RoSpec P T M R N) (StateT (GameState P T M R N) ProbComp)) +
      (fun tm => chalImpl prop K p pk tm :
        QueryImpl (ChalSpec T M R N) (StateT (GameState P T M R N) ProbComp)))

/-- The winning check of Definition 4.9, step 5, evaluated through the random oracle: the arms
of VCVio's `TweakableHash.SM_DT_RTCR_IsCollision`, with `th.eval pk t` replaced by queries to
`Th` at `(pk, t, ·)` (first at `(m*, ρ*)`, then at `(mⱼ, ρⱼ)`). An index outside `Q` and an
exhausted entry `(Tⱼ, mⱼ, ⊥)` lose. -/
def isCollision (pk : P) (Q : SM_DT_RTCR_State T M R) (out : ℕ × M × R) :
    StateT (GameState P T M R N) ProbComp Bool :=
  match Q[out.1]? with
  | none => return false
  | some (_, _, none) => return false
  | some (t, mj, some ρj) => do
    let y ← roImpl (pk, t, out.2)
    let yj ← roImpl (pk, t, (mj, ρj))
    return decide (out.2 ≠ (mj, ρj) ∧ y = yj)

variable (P T M R N) in
/-- A classical SM-rTCR adversary in the random-oracle model, making at most `q` queries to `Th`
and at most `p` challenge queries on every execution path. It receives the public parameter `P`
and outputs `(j, m*, ρ*)`. -/
structure Adversary (q p : ℕ) where
  /-- The adversary, run on the public parameter. -/
  main : P → OracleComp (AdvSpec P T M R N) (ℕ × M × R)
  /-- At most `q` queries to `Th`. -/
  roBound : ∀ pk, (main pk).IsQueryBoundP (IsRoQuery P T M R) q
  /-- At most `p` challenge queries. -/
  chalBound : ∀ pk, (main pk).IsQueryBoundP (IsChalQuery P T M R) p

/-- **The experiment `SM-rTCR^K_{Th,p,Prop}(A)`** (Definition 4.9) with `Th` a lazily sampled
random oracle: `P ←$ P`, the adversary runs on `P` against `Th` and the challenge oracle with
target cap `p` and budget `K`, and the output is checked through the same table. -/
def experiment [SampleableType P] (prop : N → Bool) (K : ℕ) {q p : ℕ}
    (A : Adversary P T M R N q p) : ProbComp Bool := do
  let pk ← $ᵗ P
  let z ← (simulateQ (gameImpl prop K p pk) (A.main pk)).run (GameState.init P T M R N)
  let w ← (isCollision pk z.2.chal z.1).run z.2
  return w.1

/-- **`Succ^{SM-rTCR,K}_{Th,p,Prop}(A)`**, the probability that the experiment outputs `1`. -/
noncomputable def advantage [SampleableType P] (prop : N → Bool) (K : ℕ) {q p : ℕ}
    (A : Adversary P T M R N q p) : ℝ≥0∞ :=
  Pr{let b ← experiment prop K A}[b = true]

/-! ## Unfolding the oracles -/

section Run

omit [DecidableEq N] [SampleableType R] in
theorem roImpl_run (x : P × T × (M × R)) (s : GameState P T M R N) :
    (roImpl x).run s = match s.table x with
      | some d => pure (d, s)
      | none => (fun d => (d, { s with table := Function.update s.table x (some d) })) <$>
          ($ᵗ N) := by
  unfold roImpl
  cases h : s.table x <;> simp [h]

omit [DecidableEq N] [SampleableType R] in
theorem mem_support_roImpl_run {x : P × T × (M × R)} {s : GameState P T M R N}
    {z : N × GameState P T M R N} (hz : z ∈ support ((roImpl x).run s)) :
    (s.table x = some z.1 ∧ z.2 = s) ∨
      (s.table x = none ∧ z.2 = { s with table := Function.update s.table x (some z.1) }) := by
  rw [roImpl_run] at hz
  cases h : s.table x with
  | some d =>
    rw [h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    rw [h] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨d, -, rfl⟩ := hz
    exact Or.inr ⟨rfl, rfl⟩

omit [DecidableEq N] in
theorem resample_zero_run (prop : N → Bool) (pk : P) (t : T) (m : M)
    (s : GameState P T M R N) :
    (resample prop pk t m 0).run s = pure (none, s) := rfl

omit [DecidableEq N] in
theorem resample_succ_run (prop : N → Bool) (pk : P) (t : T) (m : M) (k : ℕ)
    (s : GameState P T M R N) :
    (resample prop pk t m (k + 1)).run s = ($ᵗ R) >>= fun ρ =>
      (roImpl (pk, t, (m, ρ))).run s >>= fun z =>
        if prop z.1 then pure (some (z.1, ρ), z.2) else (resample prop pk t m k).run z.2 := by
  rw [resample, VCVio.Algorithms.FirstSuccess.runWith_succ]
  simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind]
  refine bind_congr fun ρ => bind_congr fun z => ?_
  by_cases h : prop z.1 <;> simp [h]

omit [DecidableEq N] in
theorem chalImpl_run (prop : N → Bool) (K p : ℕ) (pk : P) (tm : T × M)
    (s : GameState P T M R N) :
    (chalImpl prop K p pk tm).run s =
      if p ≤ s.chal.length ∨ TweakReserved Prod.fst s.chal tm.1 then pure (none, s)
      else (resample prop pk tm.1 tm.2 K).run s >>= fun z =>
        pure (z.1, { z.2 with chal := z.2.chal ++ [(tm.1, tm.2, z.1.map Prod.snd)] }) := by
  unfold chalImpl
  split_ifs with h <;> simp [h]

omit [DecidableEq N] in
theorem gameImpl_unif_run (prop : N → Bool) (K p : ℕ) (pk : P) (n : ℕ)
    (s : GameState P T M R N) :
    (gameImpl prop K p pk (Sum.inl n : ℕ ⊕ ((P × T × (M × R)) ⊕ (T × M)))).run s =
      (fun u => (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  simp [gameImpl]

omit [DecidableEq N] in
theorem gameImpl_ro_run (prop : N → Bool) (K p : ℕ) (pk : P) (x : P × T × (M × R))
    (s : GameState P T M R N) :
    (gameImpl prop K p pk (Sum.inr (Sum.inl x) : ℕ ⊕ ((P × T × (M × R)) ⊕ (T × M)))).run s =
      (roImpl x).run s := rfl

omit [DecidableEq N] in
theorem gameImpl_chal_run (prop : N → Bool) (K p : ℕ) (pk : P) (tm : T × M)
    (s : GameState P T M R N) :
    (gameImpl prop K p pk (Sum.inr (Sum.inr tm) : ℕ ⊕ ((P × T × (M × R)) ⊕ (T × M)))).run s =
      (chalImpl prop K p pk tm).run s := rfl

omit [DecidableEq N] in
/-- The sampling loop leaves `Q` alone, never overwrites a cached point, only touches points at
its own tweak, and caches the point of an accepted attempt with the returned digest. -/
theorem mem_support_resample_run (prop : N → Bool) (pk : P) (t : T) (m : M) :
    ∀ (k : ℕ) (s : GameState P T M R N), ∀ z ∈ support ((resample prop pk t m k).run s),
      z.2.chal = s.chal ∧ (∀ x, s.table x ≠ none → z.2.table x = s.table x) ∧
      (∀ x, x.2.1 ≠ t → z.2.table x = s.table x) ∧
      (∀ y ρ, z.1 = some (y, ρ) → z.2.table (pk, t, (m, ρ)) = some y) := by
  intro k
  induction k with
  | zero =>
    intro s z hz
    rw [resample_zero_run, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | succ k ih =>
    intro s z hz
    rw [resample_succ_run] at hz
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨ρ, -, w, hw, hz⟩ := hz
    have hw' : w.2.chal = s.chal ∧ (∀ x, s.table x ≠ none → w.2.table x = s.table x) ∧
        (∀ x, x.2.1 ≠ t → w.2.table x = s.table x) ∧
        w.2.table (pk, t, (m, ρ)) = some w.1 := by
      rcases mem_support_roImpl_run hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, h1⟩
      · rw [h2]
        refine ⟨rfl, fun x hx => ?_, fun x hx => ?_, by simp⟩
        · have : x ≠ (pk, t, (m, ρ)) := fun h => hx (h ▸ h1)
          simp [Function.update_of_ne this]
        · have : x ≠ (pk, t, (m, ρ)) := fun h => hx (h ▸ rfl)
          simp [Function.update_of_ne this]
    split_ifs at hz with hp
    · rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨hw'.1, hw'.2.1, hw'.2.2.1, ?_⟩
      intro y ρ' h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hw'.2.2.2
    · obtain ⟨h1, h2, h3, h4⟩ := ih w.2 z hz
      refine ⟨h1.trans hw'.1, fun x hx => ?_, fun x hx => (h3 x hx).trans (hw'.2.2.1 x hx), h4⟩
      rw [h2 x (by rw [hw'.2.1 x hx]; exact hx), hw'.2.1 x hx]

end Run

/-! ## The bad event and the potential -/

section Analysis

variable (prop : N → Bool) (pk : P)

/-- `t` does not occur in `Q`: a challenge at `t` may still be accepted. -/
def Free (s : GameState P T M R N) (t : T) : Prop := ¬ TweakReserved Prod.fst s.chal t

/-- Cached points at the real parameter `pk` and a free tweak. Each may be hit by up to `K`
attempts of the (unique) future challenge at its tweak. -/
def cachedFree (s : GameState P T M R N) : Set (P × T × (M × R)) :=
  {x | x.1 = pk ∧ Free s x.2.1 ∧ s.table x ≠ none}

/-- Cached points at `pk` and a free tweak holding a digest `y` with `Prop(y) = 1`. Each may
coincide with the accepted digest of the future challenge at its tweak. -/
def propFree (s : GameState P T M R N) : Set (P × T × (M × R)) :=
  {x | x.1 = pk ∧ Free s x.2.1 ∧ ∃ y, s.table x = some y ∧ prop y = true}

/-- The bad event: some accepted entry `(T, m, ρ)` of `Q` has a second cached point
`(pk, T, x') ≠ (pk, T, (m, ρ))` holding the same digest. A win makes it true. -/
def Bad (s : GameState P T M R N) : Prop :=
  ∃ t m ρ, (t, m, some ρ) ∈ s.chal ∧ ∃ x', x' ≠ (m, ρ) ∧ s.table (pk, t, x') ≠ none ∧
    s.table (pk, t, x') = s.table (pk, t, (m, ρ))

/-- The invariant: accepted entries are cached, and the tweaks of `Q` are distinct. -/
def Inv (s : GameState P T M R N) : Prop :=
  (∀ t m ρ, (t, m, some ρ) ∈ s.chal → s.table (pk, t, (m, ρ)) ≠ none) ∧
    ∀ e₁ ∈ s.chal, ∀ e₂ ∈ s.chal, e₁.1 = e₂.1 → e₁ = e₂

variable [Fintype N] [Fintype R]

/-- `|{y | Prop(y) = 1}|`. -/
def cardProp : ℕ := (Finset.univ.filter fun y : N => prop y = true).card

/-- The potential: with `n` direct queries left, the budget still to be spent, plus the credit
of the cached points at free tweaks. -/
noncomputable def pot (K p n : ℕ) (s : GameState P T M R N) : ℝ≥0∞ :=
  ((n : ℝ≥0∞) + 1) * (Fintype.card N : ℝ≥0∞)⁻¹ + (K : ℝ≥0∞) * n * (Fintype.card R : ℝ≥0∞)⁻¹ +
    ((p - s.chal.length : ℕ) : ℝ≥0∞) * ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞) *
      (Fintype.card R : ℝ≥0∞)⁻¹ +
    (K : ℝ≥0∞) * ((cachedFree pk s).encard : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ +
    ((propFree prop pk s).encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype R] in
theorem cardProp_mul_inv_le_one : (cardProp prop : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos (cardProp prop) with h | h
  · simp [h]
  · rw [ENNReal.mul_inv_cancel (by exact_mod_cast h.ne') (ENNReal.natCast_ne_top _)]

omit [Fintype N] [Fintype R] [DecidableEq N] [SampleableType R] [SampleableType N] in
/-- A fresh point makes the state bad only by hitting the digest of the accepted entry at its
tweak. -/
theorem bad_update {s : GameState P T M R N} (hinv : Inv pk s) (hb : ¬ Bad pk s)
    {x : P × T × (M × R)} (hx : s.table x = none) {d : N}
    (h : Bad pk { s with table := Function.update s.table x (some d) }) :
    x.1 = pk ∧ ∃ mj ρj, (x.2.1, mj, some ρj) ∈ s.chal ∧ s.table (pk, x.2.1, (mj, ρj)) = some d := by
  obtain ⟨t, m, ρ, hmem, x', hne, hc, heq⟩ := h
  have hjx : (pk, t, (m, ρ)) ≠ x := fun h' => hinv.1 t m ρ hmem (h' ▸ hx)
  simp only [Function.update_of_ne hjx] at heq hc ⊢
  by_cases hx' : (pk, t, x') = x
  · subst hx'
    simp only [Function.update_self] at heq
    exact ⟨rfl, m, ρ, hmem, heq.symm⟩
  · simp only [Function.update_of_ne hx'] at heq hc
    exact absurd ⟨t, m, ρ, hmem, x', hne, hc, heq⟩ hb

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype N] [Fintype R] in
/-- A step whose final state is always the initial one. -/
theorem step_le_of_state_eq {α : Type} {mx : ProbComp (α × GameState P T M R N)}
    {s : GameState P T M R N} (h : ∀ z ∈ support mx, z.2 = s) (hb : ¬ Bad pk s)
    (f : GameState P T M R N → ℝ≥0∞) :
    Pr{let z ← mx}[Bad pk z.2] + ∑' z, Pr{let y ← mx}[y = z] * f z.2 ≤ f s := by
  rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => (h z hz) ▸ hb, zero_add,
    tsum_prEvent_mul_of_const_on_support mx fun z hz => by rw [h z hz]]

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype N] [Fintype R] in
/-- A step whose bad event costs at most `X`, after which the potential has dropped by `X`. -/
theorem step_le_of_forall {α : Type} {mx : ProbComp (α × GameState P T M R N)}
    {X c : ℝ≥0∞} (f : GameState P T M R N → ℝ≥0∞) (hX : Pr{let z ← mx}[Bad pk z.2] ≤ X)
    (h : ∀ z ∈ support mx, f z.2 + X ≤ c) :
    Pr{let z ← mx}[Bad pk z.2] + ∑' z, Pr{let y ← mx}[y = z] * f z.2 ≤ c := by
  calc _ ≤ ∑' z, Pr{let y ← mx}[y = z] * X + ∑' z, Pr{let y ← mx}[y = z] * f z.2 := by
        rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]
        gcongr
    _ = ∑' z, Pr{let y ← mx}[y = z] * (f z.2 + X) := by
        rw [← tsum_add]
        exact tsum_congr fun z => by ring
    _ ≤ ∑' z, Pr{let y ← mx}[y = z] * c := by
        refine tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support mx
        · gcongr
          exact h z hz
        · rw [prEvent_eq_zero_of_not_mem_support _ hz]
          simp
    _ = c := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype N] [Fintype R] in
theorem encard_cast_le_of_subset_insert {α : Type} {u v : Set α} {a : α}
    (h : u ⊆ insert a v) : (u.encard : ℝ≥0∞) ≤ v.encard + 1 := by
  have := (Set.encard_le_encard h).trans (Set.encard_insert_le v a)
  rw [← ENat.toENNReal_one, ← ENat.toENNReal_add]
  exact ENat.toENNReal_le.mpr this

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype N] [Fintype R] in
theorem encard_cast_le_of_subset {α : Type} {u v : Set α} (h : u ⊆ v) :
    (u.encard : ℝ≥0∞) ≤ v.encard :=
  ENat.toENNReal_le.mpr (Set.encard_le_encard h)

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] in
theorem pot_le_succ (K p n : ℕ) (s : GameState P T M R N) :
    pot prop pk K p n s + (Fintype.card N : ℝ≥0∞)⁻¹ + (K : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ =
      pot prop pk K p (n + 1) s := by
  unfold pot
  push_cast
  ring

omit [DecidableEq N] in
theorem sum_uniform_mul {α : Type} [SampleableType α] [Fintype α] (f : α → ℝ≥0∞) :
    ∑' a, Pr{let y ← ($ᵗ α : ProbComp α)}[y = a] * f a =
      ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * f a := by
  rw [tsum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton]

omit [DecidableEq N] in
theorem sum_inv_card_mul_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ≥0∞) :
    ∑ _a : α, (Fintype.card α : ℝ≥0∞)⁻¹ * c = c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

omit [DecidableEq N] [SampleableType R] in
/-- **A direct query to `Th`.** A fresh point at a tweak holding an accepted entry makes the
state bad with probability at most `1/|N|`; a fresh point at a free tweak adds `K/|R|` and, when
its digest satisfies `Prop`, `1/|{y | Prop(y)}|` to the credit, which is `1/|N|` on average. -/
theorem ro_step (K p n : ℕ) (x : P × T × (M × R)) (s : GameState P T M R N)
    (hinv : Inv pk s) (hb : ¬ Bad pk s) :
    Pr{let z ← (roImpl x).run s}[Bad pk z.2] +
      ∑' z, Pr{let y ← (roImpl x).run s}[y = z] * pot prop pk K p n z.2 ≤
      pot prop pk K p (n + 1) s := by
  rw [← pot_le_succ]
  cases h : s.table x with
  | some d =>
    rw [roImpl_run, h]
    refine (step_le_of_state_eq pk (fun z hz => ?_) hb _).trans ?_
    · rw [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    · rw [add_assoc]
      exact le_self_add
  | none =>
    rw [roImpl_run, h, tsum_prEvent_map_mul, sum_uniform_mul, prEvent_map]
    dsimp only
    set s' : N → GameState P T M R N :=
      fun d => { s with table := Function.update s.table x (some d) } with hs'
    by_cases hc : x.1 = pk ∧ Free s x.2.1
    · have hbad : Pr{let d ← ($ᵗ N : ProbComp N)}[Bad pk (s' d)] = 0 := by
        refine prEvent_eq_zero_of_forall_mem_support _ _ fun d _ hd => ?_
        obtain ⟨-, mj, ρj, hmem, -⟩ := bad_update pk hinv hb h hd
        exact hc.2 ⟨_, hmem, rfl⟩
      have hpt : ∀ d, pot prop pk K p n (s' d) ≤ pot prop pk K p n s +
          (K : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ +
          (if prop d = true then (cardProp prop : ℝ≥0∞)⁻¹ else 0) := by
        intro d
        have h1 : (cachedFree pk (s' d)).encard ≤ ((cachedFree pk s).encard : ℝ≥0∞) + 1 := by
          refine encard_cast_le_of_subset_insert (a := x) fun y hy => ?_
          by_cases hyx : y = x
          · exact Or.inl hyx
          · refine Or.inr ⟨hy.1, hy.2.1, ?_⟩
            simpa [hs', Function.update_of_ne hyx] using hy.2.2
        unfold pot
        by_cases hp : prop d = true
        · have h2 : (propFree prop pk (s' d)).encard ≤
              ((propFree prop pk s).encard : ℝ≥0∞) + 1 := by
            refine encard_cast_le_of_subset_insert (a := x) fun y hy => ?_
            by_cases hyx : y = x
            · exact Or.inl hyx
            · refine Or.inr ⟨hy.1, hy.2.1, ?_⟩
              simpa [hs', Function.update_of_ne hyx] using hy.2.2
          simp only [hp, ite_true]
          calc _ ≤ ((n : ℝ≥0∞) + 1) * (Fintype.card N : ℝ≥0∞)⁻¹ +
                (K : ℝ≥0∞) * n * (Fintype.card R : ℝ≥0∞)⁻¹ +
                ((p - s.chal.length : ℕ) : ℝ≥0∞) * ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞) *
                  (Fintype.card R : ℝ≥0∞)⁻¹ +
                (K : ℝ≥0∞) * (((cachedFree pk s).encard : ℝ≥0∞) + 1) *
                  (Fintype.card R : ℝ≥0∞)⁻¹ +
                (((propFree prop pk s).encard : ℝ≥0∞) + 1) * (cardProp prop : ℝ≥0∞)⁻¹ := by
                gcongr
            _ = _ := by ring
        · have h2 : (propFree prop pk (s' d)).encard ≤
              ((propFree prop pk s).encard : ℝ≥0∞) := by
            refine encard_cast_le_of_subset fun y hy => ?_
            by_cases hyx : y = x
            · subst hyx
              obtain ⟨y', hy', hpy'⟩ := hy.2.2
              simp only [hs', Function.update_self, Option.some.injEq] at hy'
              exact absurd (hy' ▸ hpy') hp
            · refine ⟨hy.1, hy.2.1, ?_⟩
              simpa [hs', Function.update_of_ne hyx] using hy.2.2
          simp only [hp, Bool.false_eq_true, ite_false, add_zero]
          calc _ ≤ ((n : ℝ≥0∞) + 1) * (Fintype.card N : ℝ≥0∞)⁻¹ +
                (K : ℝ≥0∞) * n * (Fintype.card R : ℝ≥0∞)⁻¹ +
                ((p - s.chal.length : ℕ) : ℝ≥0∞) * ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞) *
                  (Fintype.card R : ℝ≥0∞)⁻¹ +
                (K : ℝ≥0∞) * (((cachedFree pk s).encard : ℝ≥0∞) + 1) *
                  (Fintype.card R : ℝ≥0∞)⁻¹ +
                ((propFree prop pk s).encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹ := by
                gcongr
            _ = _ := by ring
      rw [hbad, zero_add]
      calc _ ≤ ∑ d, (Fintype.card N : ℝ≥0∞)⁻¹ * (pot prop pk K p n s +
            (K : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ +
            (if prop d = true then (cardProp prop : ℝ≥0∞)⁻¹ else 0)) :=
            Finset.sum_le_sum fun d _ => by gcongr; exact hpt d
        _ = pot prop pk K p n s + (K : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ +
            (Fintype.card N : ℝ≥0∞)⁻¹ * ((cardProp prop : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹) := by
            rw [show ∀ c : ℝ≥0∞, ∀ f : N → ℝ≥0∞, ∑ d, (Fintype.card N : ℝ≥0∞)⁻¹ * (c + f d) =
                ∑ _d : N, (Fintype.card N : ℝ≥0∞)⁻¹ * c + (Fintype.card N : ℝ≥0∞)⁻¹ * ∑ d, f d
                from fun c f => by rw [Finset.mul_sum, ← Finset.sum_add_distrib]; simp [mul_add],
              sum_inv_card_mul_const, Finset.sum_ite, Finset.sum_const_zero, add_zero,
              Finset.sum_const, nsmul_eq_mul]
            rfl
        _ ≤ _ := by
            have := cardProp_mul_inv_le_one prop
            calc _ ≤ pot prop pk K p n s + (K : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ +
                  (Fintype.card N : ℝ≥0∞)⁻¹ * 1 := by gcongr
              _ = _ := by ring
    · have hbad : Pr{let d ← ($ᵗ N : ProbComp N)}[Bad pk (s' d)] ≤
          (Fintype.card N : ℝ≥0∞)⁻¹ := by
        by_cases hex : ∃ mj ρj, (x.2.1, mj, some ρj) ∈ s.chal
        · obtain ⟨mj, ρj, hmem⟩ := hex
          obtain ⟨d0, hd0⟩ := Option.ne_none_iff_exists'.mp (hinv.1 _ _ _ hmem)
          refine (prEvent_mono _ _ (fun d => d = d0) fun d hd => ?_).trans
            (SampleableType.prEvent_uniformSample_eq_singleton d0).le
          obtain ⟨-, mj', ρj', hmem', hd⟩ := bad_update pk hinv hb h hd
          have := hinv.2 _ hmem _ hmem' rfl
          simp only [Prod.mk.injEq, Option.some.injEq] at this
          obtain ⟨-, rfl, rfl⟩ := this
          rw [hd0] at hd
          exact (Option.some.inj hd).symm
        · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun d _ hd => by
            obtain ⟨-, mj, ρj, hmem, -⟩ := bad_update pk hinv hb h hd
            exact hex ⟨mj, ρj, hmem⟩]
          exact zero_le
      have hpt : ∀ d, pot prop pk K p n (s' d) ≤ pot prop pk K p n s := by
        intro d
        have h1 : (cachedFree pk (s' d)).encard ≤ ((cachedFree pk s).encard : ℝ≥0∞) := by
          refine encard_cast_le_of_subset fun y hy => ?_
          by_cases hyx : y = x
          · subst hyx
            exact absurd ⟨hy.1, hy.2.1⟩ hc
          · refine ⟨hy.1, hy.2.1, ?_⟩
            simpa [hs', Function.update_of_ne hyx] using hy.2.2
        have h2 : (propFree prop pk (s' d)).encard ≤ ((propFree prop pk s).encard : ℝ≥0∞) := by
          refine encard_cast_le_of_subset fun y hy => ?_
          by_cases hyx : y = x
          · subst hyx
            exact absurd ⟨hy.1, hy.2.1⟩ hc
          · refine ⟨hy.1, hy.2.1, ?_⟩
            simpa [hs', Function.update_of_ne hyx] using hy.2.2
        unfold pot
        gcongr
      calc _ ≤ (Fintype.card N : ℝ≥0∞)⁻¹ +
            ∑ _d : N, (Fintype.card N : ℝ≥0∞)⁻¹ * pot prop pk K p n s := by
            gcongr with d
            exact hpt d
        _ = (Fintype.card N : ℝ≥0∞)⁻¹ + pot prop pk K p n s := by rw [sum_inv_card_mul_const]
        _ ≤ _ := by rw [add_comm _ (pot prop pk K p n s)]; exact le_self_add

/-! ### The sampling loop -/

/-- The loop's bad event: it returns an accepted `(y, ρ)` whose point `(pk, t, (m, ρ))` shares
its digest with another cached point at `(pk, t)`. -/
def LoopBad (t : T) (m : M) (z : Option (N × R) × GameState P T M R N) : Prop :=
  ∃ y ρ, z.1 = some (y, ρ) ∧ ∃ x', x' ≠ (m, ρ) ∧ z.2.table (pk, t, x') ≠ none ∧
    z.2.table (pk, t, x') = z.2.table (pk, t, (m, ρ))

/-- The number of seeds `ρ` with `(pk, t, (m, ρ))` already cached. -/
def cntCached (t : T) (m : M) (s : GameState P T M R N) : ℕ :=
  (Finset.univ.filter fun ρ : R => (s.table (pk, t, (m, ρ))).isSome = true).card

/-- The cached points at `(pk, t)` holding a digest with `Prop = 1`. -/
def propAt (t : T) (s : GameState P T M R N) : Set (M × R) :=
  {x' | ∃ y, s.table (pk, t, x') = some y ∧ prop y = true}

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype R] in
open Classical in
/-- The digests with `Prop = 1` held at `(pk, t)` are at most as many as the points holding
them. -/
theorem card_prop_digests_le (t : T) (s : GameState P T M R N) :
    ((Finset.univ.filter fun d : N =>
        prop d = true ∧ ∃ x', s.table (pk, t, x') = some d).card : ℝ≥0∞) ≤
      ((propAt prop pk t s).encard : ℝ≥0∞) := by
  rw [← ENat.toENNReal_coe, ← Set.encard_coe_eq_coe_finsetCard]
  refine ENat.toENNReal_le.mpr ?_
  rw [← (Option.some_injective N).injOn.encard_image]
  refine (Set.encard_le_encard ?_).trans
    (Set.encard_image_le (fun x' => s.table (pk, t, x')) (propAt prop pk t s))
  rintro _ ⟨d, hd, rfl⟩
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hd
  obtain ⟨hp, x', hx'⟩ := hd
  exact ⟨x', ⟨d, hx', hp⟩, hx'⟩

omit [DecidableEq N] in
/-- **The hazard of the sampling loop.** From any state, `k` attempts at `(pk, t, m)` end in
`LoopBad` with probability at most `Σ_{i<k} (c + i)/|R| + b/|{y | Prop(y)}|`, where `c` counts
the seeds already cached at `(pk, t, m)` and `b` the cached points at `(pk, t)` holding a digest
with `Prop = 1`. The `i`-th attempt hits a cached seed with probability at most `(c + i)/|R|`
(every earlier attempt caches at most one more seed). A fresh attempt is accepted with a fixed
digest `v` (with `Prop(v) = 1`) with probability `1/|N|` and rejected with probability
`1 - |{y | Prop(y)}|/|N|`, so the accepted digest is `v` with probability at most
`1/|{y | Prop(y)}|`; rejected digests hold `Prop = 0` and do not add to `b`. -/
theorem resample_loopBad_le (t : T) (m : M) :
    ∀ (k : ℕ) (s : GameState P T M R N),
      Pr{let z ← (resample prop pk t m k).run s}[LoopBad pk t m z] ≤
        (∑ i ∈ Finset.range k, ((cntCached pk t m s : ℝ≥0∞) + i)) *
            (Fintype.card R : ℝ≥0∞)⁻¹ +
          ((propAt prop pk t s).encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹ := by
  classical
  intro k
  induction k with
  | zero =>
    intro s
    rw [resample_zero_run, prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hb => by
      rw [support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨y, ρ, h, -⟩ := hb
      simp [hz] at h]
    exact zero_le
  | succ k ih =>
    intro s
    set c : ℝ≥0∞ := (cntCached pk t m s : ℝ≥0∞) with hc
    set Y : ℝ≥0∞ := (∑ i ∈ Finset.range k, (c + 1 + i)) * (Fintype.card R : ℝ≥0∞)⁻¹ +
      ((propAt prop pk t s).encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹ with hY
    rw [resample_succ_run, prEvent_bind_eq_tsum, sum_uniform_mul]
    have hρ : ∀ ρ, Pr{let z ← ((roImpl (pk, t, (m, ρ))).run s >>= fun w =>
        if prop w.1 = true then pure (some (w.1, ρ), w.2)
        else (resample prop pk t m k).run w.2)}[LoopBad pk t m z] ≤
        (if (s.table (pk, t, (m, ρ))).isSome = true then 1 else 0) + Y := by
      intro ρ
      cases hρ : s.table (pk, t, (m, ρ)) with
      | some y0 => exact (prEvent_le_one _).trans (by simp)
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ite_false, zero_add]
        rw [roImpl_run, hρ, bind_map_left, prEvent_bind_eq_tsum, sum_uniform_mul]
        set s' : N → GameState P T M R N :=
          fun d => { s with table := Function.update s.table (pk, t, (m, ρ)) (some d) } with hs'
        have hne : ∀ x' : M × R, x' ≠ (m, ρ) → (pk, t, x') ≠ (pk, t, (m, ρ)) :=
          fun x' h h' => h (by simpa using h')
        set Vb : N → Prop := fun d => ∃ x', s.table (pk, t, x') = some d with hVb
        have hu : ∀ d, Pr{let z ← (if prop d = true then pure (some (d, ρ), s' d)
            else (resample prop pk t m k).run (s' d))}[LoopBad pk t m z] ≤
            if prop d = true then (if Vb d then 1 else 0) else Y := by
          intro d
          by_cases hp : prop d = true
          · simp only [hp, ite_true]
            rw [prEvent_pure]
            split_ifs with hL hV
            · exact le_rfl
            · exfalso
              obtain ⟨y, ρ', h1, x', hx'ne, hx'c, hx'eq⟩ := hL
              simp only [Option.some.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              simp only [hs', Function.update_self,
                Function.update_of_ne (hne x' hx'ne)] at hx'eq
              exact hV ⟨x', hx'eq⟩
            · exact zero_le
            · exact le_rfl
          · simp only [hp, Bool.false_eq_true, ite_false]
            refine (ih (s' d)).trans ?_
            have hcnt : (cntCached pk t m (s' d) : ℝ≥0∞) ≤ c + 1 := by
              rw [hc]
              exact_mod_cast (Finset.card_le_card (s := Finset.univ.filter fun ρ' : R =>
                  ((s' d).table (pk, t, (m, ρ'))).isSome = true)
                (t := insert ρ (Finset.univ.filter fun ρ' : R =>
                  (s.table (pk, t, (m, ρ'))).isSome = true)) (fun ρ' hρ' => by
                  by_cases hρρ : ρ' = ρ
                  · exact Finset.mem_insert.mpr (Or.inl hρρ)
                  · refine Finset.mem_insert_of_mem ?_
                    have h' : (pk, t, (m, ρ')) ≠ (pk, t, (m, ρ)) := by simpa using hρρ
                    simpa [hs', Function.update_of_ne h'] using hρ')).trans
                (Finset.card_insert_le _ _)
            have hprop : ((propAt prop pk t (s' d)).encard : ℝ≥0∞) ≤
                (propAt prop pk t s).encard := by
              refine encard_cast_le_of_subset fun x' hx' => ?_
              obtain ⟨y, hy, hpy⟩ := hx'
              by_cases hxe : x' = (m, ρ)
              · subst hxe
                simp only [hs', Function.update_self, Option.some.injEq] at hy
                exact absurd (hy ▸ hpy) hp
              · simp only [hs', Function.update_of_ne (hne x' hxe)] at hy
                exact ⟨y, hy, hpy⟩
            rw [hY]
            gcongr with i hi
        calc _ ≤ ∑ d, (Fintype.card N : ℝ≥0∞)⁻¹ *
              (if prop d = true then (if Vb d then 1 else 0) else Y) :=
              Finset.sum_le_sum fun d _ => by gcongr; exact hu d
          _ ≤ ∑ _d : N, (Fintype.card N : ℝ≥0∞)⁻¹ * Y := by
              rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d => prop d = true),
                ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d => prop d = true)
                  (fun _ => (Fintype.card N : ℝ≥0∞)⁻¹ * Y)]
              refine add_le_add ?_ (le_of_eq (Finset.sum_congr rfl fun d hd => ?_))
              · rw [← Finset.mul_sum, ← Finset.mul_sum]
                gcongr (Fintype.card N : ℝ≥0∞)⁻¹ * ?_
                rw [Finset.sum_ite_of_true (fun d hd => (Finset.mem_filter.mp hd).2),
                  Finset.sum_boole, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
                have hcard := card_prop_digests_le prop pk t s
                have hA : (Finset.univ.filter fun d : N => prop d = true).card = cardProp prop :=
                  rfl
                rw [hA]
                rcases Nat.eq_zero_or_pos (cardProp prop) with h0 | h0
                · have : (Finset.univ.filter fun d : N => prop d = true ∧ Vb d) = ∅ := by
                    rw [Finset.filter_eq_empty_iff]
                    intro d _ hd
                    have hmem : d ∈ Finset.univ.filter fun d : N => prop d = true := by
                      simp [hd.1]
                    rw [cardProp] at h0
                    rw [Finset.card_eq_zero.mp h0] at hmem
                    simp at hmem
                  rw [this]
                  simp
                · calc _ ≤ ((propAt prop pk t s).encard : ℝ≥0∞) := hcard
                    _ = (cardProp prop : ℝ≥0∞) * (((propAt prop pk t s).encard : ℝ≥0∞) *
                          (cardProp prop : ℝ≥0∞)⁻¹) := by
                        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel
                          (by exact_mod_cast h0.ne') (ENNReal.natCast_ne_top _), mul_one]
                    _ ≤ _ := by
                        gcongr
                        rw [hY]
                        exact le_add_self
              · simp [(Finset.mem_filter.mp hd).2]
          _ = Y := sum_inv_card_mul_const Y
    calc _ ≤ ∑ ρ, (Fintype.card R : ℝ≥0∞)⁻¹ *
          ((if (s.table (pk, t, (m, ρ))).isSome = true then 1 else 0) + Y) :=
          Finset.sum_le_sum fun ρ _ => by gcongr; exact hρ ρ
      _ = (Fintype.card R : ℝ≥0∞)⁻¹ * c + Y := by
          simp only [mul_add, Finset.sum_add_distrib, sum_inv_card_mul_const]
          rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul, mul_one]
          rfl
      _ = _ := by
          rw [hY, Finset.sum_range_succ']
          push_cast
          ring_nf

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype N] [Fintype R] in
theorem sum_range_add_eq (c : ℝ≥0∞) (K : ℕ) :
    ∑ i ∈ Finset.range K, (c + i) = K * c + ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_range_id, Nat.cast_sum]

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] [SampleableType N] [Fintype N] [Fintype R] in
theorem encard_cast_add_le {α : Type} {u v w : Set α} (hd : Disjoint u v) (h : u ∪ v ⊆ w) :
    (u.encard : ℝ≥0∞) + v.encard ≤ w.encard := by
  rw [← ENat.toENNReal_add, ← Set.encard_union_eq hd]
  exact encard_cast_le_of_subset h

omit [DecidableEq N] in
/-- **An accepted challenge query.** The new entry makes the state bad only through the loop's
bad event, charged by `resample_loopBad_le`; its tweak leaves the free set, releasing the credit
of the cached points there, and one challenge slot of `K(K-1)/2 / |R|` is used. -/
theorem chal_step (K p n : ℕ) (tm : T × M) (s : GameState P T M R N) (hb : ¬ Bad pk s) :
    Pr{let z ← (chalImpl prop K p pk tm).run s}[Bad pk z.2] +
      ∑' z, Pr{let y ← (chalImpl prop K p pk tm).run s}[y = z] * pot prop pk K p n z.2 ≤
      pot prop pk K p n s := by
  obtain ⟨t, m⟩ := tm
  rw [chalImpl_run]
  split_ifs with hcap
  · exact step_le_of_state_eq pk (fun z hz => by
      rw [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]) hb _
  · simp only [not_or] at hcap
    obtain ⟨hlen, hres⟩ := hcap
    have hlen : s.chal.length < p := Nat.lt_of_not_le hlen
    set post : Option (N × R) × GameState P T M R N → GameState P T M R N :=
      fun z => { z.2 with chal := z.2.chal ++ [(t, m, z.1.map Prod.snd)] } with hpost
    rw [show ((resample prop pk t m K).run s >>= fun z =>
        pure (z.1, { z.2 with chal := z.2.chal ++ [(t, m, z.1.map Prod.snd)] })) =
        (fun z => (z.1, post z)) <$> (resample prop pk t m K).run s by
      rw [map_eq_bind_pure_comp]; rfl]
    have hsupp := mem_support_resample_run prop pk t m K s
    refine step_le_of_forall pk (pot prop pk K p n : GameState P T M R N → ℝ≥0∞)
      (X := (∑ i ∈ Finset.range K, ((cntCached pk t m s : ℝ≥0∞) + i)) *
          (Fintype.card R : ℝ≥0∞)⁻¹ +
        ((propAt prop pk t s).encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹) ?_ ?_
    · rw [prEvent_map]
      refine (prEvent_mono_of_support _ _ (LoopBad pk t m) fun w hw hbad => ?_).trans
        (resample_loopBad_le prop pk t m K s)
      obtain ⟨hchal, -, hother, -⟩ := hsupp w hw
      obtain ⟨t', m', ρ', hmem, x', hne, hc, heq⟩ := hbad
      simp only [hpost, hchal, List.mem_append, List.mem_singleton] at hmem heq hc
      rcases hmem with hmem | hmem
      · have ht' : t' ≠ t := fun h => hres ⟨_, hmem, h⟩
        rw [hother _ ht', hother _ ht'] at heq
        rw [hother _ ht'] at hc
        exact absurd ⟨t', m', ρ', hmem, x', hne, hc, heq⟩ hb
      · simp only [Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, hρ⟩ := hmem
        obtain ⟨⟨y, ρ''⟩, hw1, hρ''⟩ := Option.map_eq_some_iff.mp hρ.symm
        simp only at hρ''
        subst hρ''
        exact ⟨y, ρ'', hw1, x', hne, hc, heq⟩
    · intro z hz
      rw [support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨hchal, -, hother, -⟩ := hsupp w hw
      have hfree : ∀ t', Free (post w) t' → Free s t' ∧ t' ≠ t := by
        intro t' ht'
        refine ⟨fun ⟨e, he, het⟩ => ht' ⟨e, ?_, het⟩, fun h => ht' ⟨(t, m, w.1.map Prod.snd),
          by simp [hpost], h.symm⟩⟩
        simp [hpost, hchal, he]
      -- the cached points at `t`
      set D : Set (P × T × (M × R)) := {x | x.1 = pk ∧ x.2.1 = t ∧ s.table x ≠ none} with hD
      set E : Set (P × T × (M × R)) :=
        {x | x.1 = pk ∧ x.2.1 = t ∧ ∃ y, s.table x = some y ∧ prop y = true} with hE
      have hcd : (cachedFree pk (post w)).encard + (D.encard : ℝ≥0∞) ≤
          (cachedFree pk s).encard := by
        refine encard_cast_add_le ?_ ?_
        · refine Set.disjoint_left.mpr fun x hx hxD => (hfree _ hx.2.1).2 hxD.2.1
        · rintro x (hx | hx)
          · obtain ⟨hf, hne⟩ := hfree _ hx.2.1
            refine ⟨hx.1, hf, ?_⟩
            have := hx.2.2
            simp only [hpost] at this
            rwa [hother _ hne] at this
          · exact ⟨hx.1, hx.2.1 ▸ hres, hx.2.2⟩
      have hpe : (propFree prop pk (post w)).encard + (E.encard : ℝ≥0∞) ≤
          (propFree prop pk s).encard := by
        refine encard_cast_add_le ?_ ?_
        · refine Set.disjoint_left.mpr fun x hx hxE => (hfree _ hx.2.1).2 hxE.2.1
        · rintro x (hx | hx)
          · obtain ⟨hf, hne⟩ := hfree _ hx.2.1
            refine ⟨hx.1, hf, ?_⟩
            have := hx.2.2
            simp only [hpost] at this
            rwa [hother _ hne] at this
          · exact ⟨hx.1, hx.2.1 ▸ hres, hx.2.2⟩
      have hcnt : (cntCached pk t m s : ℝ≥0∞) ≤ D.encard := by
        rw [cntCached, ← ENat.toENNReal_coe, ← Set.encard_coe_eq_coe_finsetCard]
        refine ENat.toENNReal_le.mpr ?_
        rw [← (show Set.InjOn (fun ρ : R => (pk, t, (m, ρ))) _ from
          fun a _ b _ h => by simpa using h).encard_image]
        refine Set.encard_le_encard ?_
        rintro _ ⟨ρ, hρ, rfl⟩
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
          Option.isSome_iff_ne_none] at hρ
        exact ⟨rfl, rfl, hρ⟩
      have hprop : ((propAt prop pk t s).encard : ℝ≥0∞) ≤ E.encard := by
        refine ENat.toENNReal_le.mpr ?_
        rw [← (show Set.InjOn (fun x' : M × R => (pk, t, x')) _ from
          fun a _ b _ h => by simpa using h).encard_image]
        refine Set.encard_le_encard ?_
        rintro _ ⟨x', hx', rfl⟩
        exact ⟨rfl, rfl, hx'⟩
      have hslot : ((p - (post w).chal.length : ℕ) : ℝ≥0∞) + 1 = ((p - s.chal.length : ℕ) : ℝ≥0∞) := by
        simp only [hpost, hchal, List.length_append, List.length_singleton]
        exact_mod_cast (by omega : p - (s.chal.length + 1) + 1 = p - s.chal.length)
      rw [sum_range_add_eq]
      unfold pot
      rw [← hslot]
      calc _ ≤ ((n : ℝ≥0∞) + 1) * (Fintype.card N : ℝ≥0∞)⁻¹ +
            (K : ℝ≥0∞) * n * (Fintype.card R : ℝ≥0∞)⁻¹ +
            (((p - (post w).chal.length : ℕ) : ℝ≥0∞) + 1) * ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞) *
              (Fintype.card R : ℝ≥0∞)⁻¹ +
            (K : ℝ≥0∞) * (((cachedFree pk (post w)).encard : ℝ≥0∞) + D.encard) *
              (Fintype.card R : ℝ≥0∞)⁻¹ +
            (((propFree prop pk (post w)).encard : ℝ≥0∞) + E.encard) *
              (cardProp prop : ℝ≥0∞)⁻¹ := by
            calc _ ≤ ((n : ℝ≥0∞) + 1) * (Fintype.card N : ℝ≥0∞)⁻¹ +
                  (K : ℝ≥0∞) * n * (Fintype.card R : ℝ≥0∞)⁻¹ +
                  ((p - (post w).chal.length : ℕ) : ℝ≥0∞) * ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞) *
                    (Fintype.card R : ℝ≥0∞)⁻¹ +
                  (K : ℝ≥0∞) * ((cachedFree pk (post w)).encard : ℝ≥0∞) *
                    (Fintype.card R : ℝ≥0∞)⁻¹ +
                  ((propFree prop pk (post w)).encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹ +
                  (((K : ℝ≥0∞) * D.encard + ((K * (K - 1) / 2 : ℕ) : ℝ≥0∞)) *
                    (Fintype.card R : ℝ≥0∞)⁻¹ + (E.encard : ℝ≥0∞) * (cardProp prop : ℝ≥0∞)⁻¹) := by
                  gcongr
              _ = _ := by ring
        _ ≤ _ := by gcongr

/-! ### The invariant -/

omit [Fintype N] [Fintype R] [DecidableEq N] [SampleableType R] in
theorem inv_roImpl (x : P × T × (M × R)) (s : GameState P T M R N) (h : Inv pk s) :
    ∀ z ∈ support ((roImpl x).run s), Inv pk z.2 := by
  intro z hz
  rcases mem_support_roImpl_run hz with ⟨-, h2⟩ | ⟨h1, h2⟩
  · rwa [h2]
  · rw [h2]
    refine ⟨fun t m ρ hmem => ?_, h.2⟩
    by_cases hx : (pk, t, (m, ρ)) = x
    · simp [hx]
    · simpa [Function.update_of_ne hx] using h.1 t m ρ hmem

omit [Fintype N] [Fintype R] [DecidableEq N] in
theorem inv_chalImpl (K p : ℕ) (tm : T × M) (s : GameState P T M R N) (h : Inv pk s) :
    ∀ z ∈ support ((chalImpl prop K p pk tm).run s), Inv pk z.2 := by
  intro z hz
  rw [chalImpl_run] at hz
  split_ifs at hz with hcap
  · rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact h
  · simp only [not_or] at hcap
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hchal, hcached, -, hnew⟩ := mem_support_resample_run prop pk tm.1 tm.2 K s w hw
    refine ⟨fun t m ρ hmem => ?_, fun e₁ he₁ e₂ he₂ he => ?_⟩
    · simp only [hchal, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · rw [hcached _ (h.1 t m ρ hmem)]
        exact h.1 t m ρ hmem
      · simp only [Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, hρ⟩ := hmem
        obtain ⟨⟨y, ρ'⟩, hw1, hρ'⟩ := Option.map_eq_some_iff.mp hρ.symm
        simp only at hρ'
        subst hρ'
        simp [hnew y ρ' hw1]
    · simp only [hchal, List.mem_append, List.mem_singleton] at he₁ he₂
      rcases he₁ with he₁ | rfl <;> rcases he₂ with he₂ | rfl
      · exact h.2 e₁ he₁ e₂ he₂ he
      · exact absurd ⟨e₁, he₁, he⟩ hcap.2
      · exact absurd ⟨e₂, he₂, he.symm⟩ hcap.2
      · rfl

omit [Fintype N] [Fintype R] [DecidableEq N] in
theorem gameImpl_preservesInv (K p : ℕ) :
    QueryImpl.PreservesInv (gameImpl prop K p pk) (Inv pk : GameState P T M R N → Prop) := by
  intro t s hs z hz
  rcases t with n | x | tm
  · rw [gameImpl_unif_run, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · exact inv_roImpl pk x s hs z hz
  · exact inv_chalImpl prop pk K p tm s hs z hz

/-! ### The final check -/

omit [Fintype R] [SampleableType R] in
/-- **The final check.** From a good state the win needs the fresh evaluation at `(m*, ρ*)` to
hit the accepted digest `yⱼ`: probability at most `1/|N|`. -/
theorem isCollision_le (s : GameState P T M R N) (out : ℕ × M × R) (hinv : Inv pk s)
    (hb : ¬ Bad pk s) :
    Pr{let w ← (isCollision pk s.chal out).run s}[w.1 = true] ≤ (Fintype.card N : ℝ≥0∞)⁻¹ := by
  unfold isCollision
  rcases hj : s.chal[out.1]? with _ | ⟨t, mj, _ | ρj⟩
  · rw [StateT.run_pure, prEvent_pure]; simp
  · rw [StateT.run_pure, prEvent_pure]; simp
  · have hmem : (t, mj, some ρj) ∈ s.chal := List.mem_of_getElem? hj
    obtain ⟨yj, hyj⟩ := Option.ne_none_iff_exists'.mp (hinv.1 t mj ρj hmem)
    simp only [StateT.run_bind, roImpl_run]
    cases hx : s.table (pk, t, out.2) with
    | some y =>
      simp only [pure_bind, hyj, StateT.run_pure]
      rw [prEvent_pure]
      split_ifs with hw
      · exfalso
        simp only [decide_eq_true_eq] at hw
        exact hb ⟨t, mj, ρj, hmem, out.2, hw.1, by simp [hx], by rw [hx, hyj, hw.2]⟩
      · exact zero_le
    | none =>
      have hne : (pk, t, (mj, ρj)) ≠ (pk, t, out.2) := fun h => by
        rw [h, hx] at hyj
        simp at hyj
      simp only [bind_map_left, Function.update_of_ne hne, hyj, pure_bind, StateT.run_pure]
      rw [prEvent_bind_eq_tsum, sum_uniform_mul]
      calc _ ≤ ∑ y, (Fintype.card N : ℝ≥0∞)⁻¹ * (if y = yj then 1 else 0) := by
            refine Finset.sum_le_sum fun y _ => ?_
            gcongr
            rw [prEvent_pure]
            split_ifs with h1 h2 <;> simp_all
        _ = _ := by simp

omit [DecidableEq P] [DecidableEq T] [DecidableEq M] [DecidableEq R] [DecidableEq N]
  [SampleableType R] in
/-- The potential at the start: the whole budget, no credit. -/
theorem pot_init (K p q : ℕ) :
    pot prop pk K p q (GameState.init P T M R N) =
      ((q : ℝ≥0∞) + 1) * (Fintype.card N : ℝ≥0∞)⁻¹ +
        ((K * q + p * (K * (K - 1) / 2) : ℕ) : ℝ≥0∞) * (Fintype.card R : ℝ≥0∞)⁻¹ := by
  have h1 : cachedFree pk (GameState.init P T M R N) = ∅ := by
    ext x; simp [cachedFree, GameState.init]
  have h2 : propFree prop pk (GameState.init P T M R N) = ∅ := by
    ext x; simp [propFree, GameState.init]
  rw [pot, h1, h2]
  simp only [GameState.init, List.length_nil, Nat.sub_zero, Set.encard_empty]
  push_cast
  ring

end Analysis

/-! ## Corollary G.1 -/

/-- **Corollary G.1** (generic classical security of SM-rTCR). For a classical adversary making at
most `q` queries to the random oracle `Th` and at most `p` challenge queries,
`Succ^{SM-rTCR,K}_{Th,p,Prop}(A) ≤ (q + 1)/|N| + (K·q + p·K(K-1)/2)/|R|`. -/
theorem advantage_le [SampleableType P] [Fintype N] [Fintype R] (prop : N → Bool) (K : ℕ)
    {q p : ℕ} (A : Adversary P T M R N q p) :
    advantage prop K A ≤ ((q : ℝ≥0∞) + 1) / Fintype.card N +
      ((K * q + p * (K * (K - 1) / 2) : ℕ) : ℝ≥0∞) / Fintype.card R := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  unfold advantage experiment
  refine prEvent_bind_le_of_forall_le _ _ _ fun pk => ?_
  rw [← pot_init (T := T) (M := M) (R := R) prop pk K p q]
  refine prEvent_simulateQ_run_bind_le_of_potential (gameImpl prop K p pk) (IsRoQuery P T M R)
    (Inv pk) (Bad pk) (pot prop pk K p) (gameImpl_preservesInv prop pk K p)
    (fun n s => by rw [← pot_le_succ, add_assoc]; exact le_self_add) ?_ ?_
    (fun z => (isCollision pk z.2.chal z.1).run z.2 >>= fun w => pure w.1) (· = true) ?_
    (A.main pk) (A.roBound pk) _ ⟨by simp [GameState.init], by simp [GameState.init]⟩
    (by simp [Bad, GameState.init])
  · intro t ht n s hs hb
    rcases t with u | x | tm
    · rw [gameImpl_unif_run]
      exact step_le_of_state_eq pk (fun z hz => by
        rw [support_map] at hz
        obtain ⟨v, -, rfl⟩ := hz
        rfl) hb _
    · exact absurd trivial ht
    · exact chal_step prop pk K p n tm s hb
  · intro t ht n s hs hb
    rcases t with u | x | tm
    · exact absurd ht id
    · exact ro_step prop pk K p n x s hs hb
    · exact absurd ht id
  · intro z hz hb
    rw [bind_pure_comp, prEvent_map]
    refine (isCollision_le pk z.2 z.1 hz hb).trans ?_
    unfold pot
    simp only [Nat.cast_zero, zero_add, one_mul, mul_zero, zero_mul, add_zero]
    exact le_add_right (le_add_right (le_add_right le_rfl))

/-- **Corollary G.1, `K = 1`**: `Succ^{SM-rTCR,1}_{Th,p,Prop}(A) ≤ (q + 1)/|N| + q/|R|`. -/
theorem advantage_le_of_one [SampleableType P] [Fintype N] [Fintype R] (prop : N → Bool)
    {q p : ℕ} (A : Adversary P T M R N q p) :
    advantage prop 1 A ≤ ((q : ℝ≥0∞) + 1) / Fintype.card N + (q : ℝ≥0∞) / Fintype.card R := by
  simpa using advantage_le prop 1 A

end RandomSamplingTCR

end ShrincsSecurity.Notions.Generic

end
