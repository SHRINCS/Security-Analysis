module

public import ShrincsSecurity.Notions.Generic.HiddenSlice
public import ShrincsSecurity.Notions.TweakPartition

/-!
# SM-TCR-EXCL in the classical random-oracle model

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`): **Definition 4.7** (SM-TCR-EXCL,
lines 2226–2262, repeated in Appendix E at line 7235) with `Th` a random oracle, and
**Theorem E.1**, classical case (lines 7283–7373).

`Th : P × T × M → N` is a lazily sampled random oracle (we write its domain `P × (T × M)`). The
challenge oracle `O` of Definition 4.7 is the classical interface `Σ` of Lemma C.9
(`HiddenSlice.Interface`) on the hidden slice `Th(P, ·, ·)`, and the winning condition is its
predicate `Φ`; so the experiment is Game 0 of Lemma C.9 for this interface
(`SmTcrExcl.experiment`). Unfolded, it reads as Definition 4.7:

1. `P ←$ P`, `Q = []`;
2. `A₁` evaluates `Th` and queries `O(T, m)`, which returns `⊥` (`none`) and leaves `Q` unchanged
   if `|Q| ≥ p` or some `(T', m') ∈ Q` has `T' ∈ Ω(T)`, and otherwise appends `(T, m)` to `Q` and
   returns `Th(P, T, m)` (`some`), evaluated on the table that `A₁` also queries;
3. `(j, T*, m*) ← A₂(P)`, with access to `Th`;
4. output `1` iff `Q[j] = (T_j, m_j)` exists, `T* ∈ Ω(T_j)`, `m* ≠ m_j` and
   `Th(P, T_j, m_j) = Th(P, T*, m*)`.

Here `Ω(T) = {T, partner T}` (`ExclusiveTweaks.Omega`). The paper's three refusal guards are
`(T', m') ∈ Q` with `T' = T`, with `T' = ω(T)` for `T ∈ T₂`, and with `T' = ω⁻¹(T)` for `T ∈ T₃`;
since `partner` is the identity on `T₁`, `ω` on `T₂` and `ω⁻¹` on `T₃`, these together say
exactly `T' ∈ Ω(T)`. Steps 6–8 of Definition 4.7 likewise say `T* ∈ Ω(T_j)`
(`ExclusiveTweaks.mem_Omega_iff_cases`). The list `Q` stores each admitted challenge with its
answer `Th(P, T_j, m_j)`, which the winning check reads instead of evaluating `Th(P, T_j, m_j)`
again; the two agree because the challenge was answered from the same table. Indices `j` are
`0`-based. The bound holds for every target cap `p`, so the paper's range conditions `p ≤ |T|`
(Theorem E.1) and `p ≤ |T₁ ∪ T₂|` (Definition 4.7) play no role.

## Main statements

* `SmTcrExcl.succ_game1_le`: in Game 1 of Lemma C.9 the adversary wins with probability at most
  `(q₂ + 1)/|N|`, where `q₂` bounds the second stage's evaluations of `Th`.
* `SmTcrExcl.succ_le_add_advantage`: **Theorem E.1**, with the ZeroDist term
  `Adv^{ZeroDist}(C)` of the reduction `C` kept.
* `SmTcrExcl.succ_le`: **Theorem E.1** (classical), sharp form,
  `Succ^{sm-tcr-excl}_{Th,p}(A) ≤ (q₂ + 1)/|N| + q₁/|P|`, where `q₁` bounds the first stage's
  evaluations of `Th`.
* `SmTcrExcl.succ_le_of_le`: the paper's form `(q + 1)/|N| + q/|P|` for `q₁ + q₂ ≤ q`.

## Proof

Game 0 → Game 1 is Lemma C.9 (`HiddenSlice.prEvent_game_le`), at cost `q₁/|P|`; the ZeroDist
adversary `C` of the paper is `HiddenSlice.reduction` (`succ_le_add_advantage`). In Game 1 the
challenges are answered by an independent lazily sampled `g : T × M → N`, which is programmed into
`Th` at `P` for the second stage. Instead of the reduction to `Avg-Search_{1/|N|}` (Algorithm 13)
we bound Game 1 directly by the per-query hazard argument that proves Lemma C.6: a state is *bad*
when `g` takes the answer `y_j` of an admitted challenge `(T_j, m_j)` at another point `(T, m)`
with `T ∈ Ω(T_j)`. The guards make the sets `Ω(T_j)` of distinct admitted challenges disjoint
(`ExclusiveTweaks.mem_Omega_of_mem_of_mem`), so a fresh value of `g` can make the state bad only by
hitting one fixed `y_j`, with probability `1/|N|`. The first stage never makes the state bad, the
`q₂` evaluations of the second stage do so with probability at most `q₂/|N|`, and the final
evaluation of the winning check wins from a good state with probability at most `1/|N|`. These are
the `q₂ + 1` hidden bits `f(k, i, m)` that Algorithm 13 reads.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

namespace SmTcrExcl

open HiddenSlice

variable (P T M N : Type)

/-- Evaluations of `Th : P × T × M → N`. -/
abbrev ROSpec : OracleSpec (P × (T × M)) := HiddenSlice.ROSpec P (T × M) N

/-- The challenge oracle `O(T, m)`: `none` is `⊥`. -/
abbrev ChalSpec : OracleSpec (T × M) := (T × M) →ₒ Option N

/-- The list `Q` of admitted challenges, each with its answer `Th(P, T, m)`, in issue order. -/
abbrev ChalList : Type := List ((T × M) × N)

/-- A direct evaluation of `Th` by the second stage. -/
def IsRO₂Query : ℕ ⊕ (P × (T × M)) → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred (IsRO₂Query P T M) := fun x => by
  rcases x with _ | _ <;> simp only [IsRO₂Query] <;> infer_instance

/-- An SM-TCR-EXCL adversary `A = (A₁, A₂)` with shared state `σ`. The first stage evaluates `Th`
at most `q₁` times and queries `O` freely; the second stage receives `P` and evaluates `Th` at most
`q₂` times. -/
structure Adversary (σ : Type) (q₁ q₂ : ℕ) where
  /-- The first stage, with access to `Th` and `O`. -/
  A1 : OracleComp (unifSpec + (ROSpec P T M N + ChalSpec T M N)) σ
  /-- The second stage: it outputs `(j, T*, m*)`. -/
  A2 : σ → P → OracleComp (unifSpec + ROSpec P T M N) (ℕ × T × M)
  /-- The first stage evaluates `Th` at most `q₁` times. -/
  bound₁ : A1.IsQueryBoundP (IsROQuery P (T × M)) q₁
  /-- The second stage evaluates `Th` at most `q₂` times. -/
  bound₂ : ∀ st P', (A2 st P').IsQueryBoundP (IsRO₂Query P T M) q₂

variable {P T M N} [DecidableEq T] [DecidableEq M] [DecidableEq N] [SampleableType N]

/-- The guards of `O`: the target cap is reached, or `Q` holds a challenge at a tweak of `Ω(T)`. -/
def Refused (X : ExclusiveTweaks T) (p : ℕ) (Q : ChalList T M N) (t : T) : Prop :=
  p ≤ Q.length ∨ ∃ e ∈ Q, e.1.1 ∈ X.Omega t

instance (X : ExclusiveTweaks T) (p : ℕ) (Q : ChalList T M N) (t : T) :
    Decidable (Refused X p Q t) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- **The challenge oracle `O`** of Definition 4.7, on the hidden slice `Th(P, ·, ·)`. -/
def chalImpl (X : ExclusiveTweaks T) (p : ℕ) : QueryImpl (ChalSpec T M N)
    (StateT (ChalList T M N) (OracleComp (unifSpec + SliceSpec (T × M) N))) :=
  fun tm => StateT.mk fun Q =>
    if Refused X p Q tm.1 then pure (none, Q)
    else (fun y => (some y, Q ++ [(tm, y)])) <$>
      (liftM ((unifSpec + SliceSpec (T × M) N).query (.inr tm)) :
        OracleComp (unifSpec + SliceSpec (T × M) N) N)

/-- **The winning condition** of Definition 4.7, steps 5–9. -/
def win (X : ExclusiveTweaks T) (Q : ChalList T M N) (out : ℕ × T × M) :
    OracleComp (unifSpec + SliceSpec (T × M) N) Bool :=
  match Q[out.1]? with
  | none => pure false
  | some (tmj, yj) =>
    if out.2.1 ∈ X.Omega tmj.1 ∧ out.2.2 ≠ tmj.2 then
      (fun y => decide (y = yj)) <$>
        (liftM ((unifSpec + SliceSpec (T × M) N).query (.inr out.2)) :
          OracleComp (unifSpec + SliceSpec (T × M) N) N)
    else pure false

/-- The challenge oracle and the winning condition as the interface `(Σ, Φ)` of Lemma C.9. -/
def interface (X : ExclusiveTweaks T) (p : ℕ) :
    Interface (T × M) N (ChalSpec T M N) (ChalList T M N) (ℕ × T × M) where
  init := []
  impl := chalImpl X p
  pred := win X

/-- The adversary as a two-stage adversary of Lemma C.9. -/
def Adversary.toHiddenSlice {σ : Type} {q₁ q₂ : ℕ} (A : Adversary P T M N σ q₁ q₂) :
    HiddenSlice.Adversary P (T × M) N (ChalSpec T M N) σ (ℕ × T × M) q₁ :=
  ⟨A.A1, A.A2, A.bound₁⟩

variable [DecidableEq P] [SampleableType P]

/-- **The experiment `SM-TCR-EXCL_{Th,p}(A)`** of Definition 4.7, with `Th` a random oracle:
Game 0 of Lemma C.9 for the challenge oracle and the winning condition. -/
def experiment (X : ExclusiveTweaks T) (p : ℕ) {σ : Type} {q₁ q₂ : ℕ}
    (A : Adversary P T M N σ q₁ q₂) : ProbComp Bool :=
  game0 (interface X p) A.toHiddenSlice

/-- **`Succ^{sm-tcr-excl}_{Th,p}(A)`** (Definition 4.7). -/
noncomputable def succ (X : ExclusiveTweaks T) (p : ℕ) {σ : Type} {q₁ q₂ : ℕ}
    (A : Adversary P T M N σ q₁ q₂) : ℝ≥0∞ :=
  Pr{let b ← experiment X p A}[b = true]

/-! ## Game 1 -/

section Game1

variable (X : ExclusiveTweaks T)

/-- The answers of the admitted challenges are stored in `g`, and distinct admitted challenges
have disjoint sets `Ω(T_j)`. -/
def GoodSlice (Q : ChalList T M N) (g : Slice (T × M) N) : Prop :=
  (∀ e ∈ Q, g e.1 = some e.2) ∧ (∀ a ∈ Q, ∀ b ∈ Q, a.1.1 ∈ X.Omega b.1.1 → a = b)

/-- The bad event: `g` takes the answer `y_j` of an admitted challenge `(T_j, m_j)` at another
point `(T, m)` with `T ∈ Ω(T_j)`. -/
def Bad (Q : ChalList T M N) (g : Slice (T × M) N) : Prop :=
  ∃ e ∈ Q, ∃ x : T × M, x.1 ∈ X.Omega e.1.1 ∧ x ≠ e.1 ∧ g x = some e.2

/-- The invariant of Game 1's first stage: a good slice, filled only at admitted challenges. -/
def Phase1Inv (st : (Table P (T × M) N × Slice (T × M) N) × ChalList T M N) : Prop :=
  GoodSlice X st.2 st.1.2 ∧ ∀ x, st.1.2 x ≠ none → ∃ e ∈ st.2, e.1 = x

omit [DecidableEq T] [DecidableEq M] [DecidableEq N] [SampleableType N] [DecidableEq P]
  [SampleableType P] in
theorem not_bad_of_phase1Inv {st : (Table P (T × M) N × Slice (T × M) N) × ChalList T M N}
    (h : Phase1Inv X st) : ¬ Bad X st.2 st.1.2 := by
  rintro ⟨e, he, x, hxΩ, hne, hgx⟩
  obtain ⟨e', he', rfl⟩ := h.2 x (by rw [hgx]; exact Option.some_ne_none _)
  exact hne (congrArg Prod.fst (h.1.2 e' he' e he hxΩ))

omit [DecidableEq T] [DecidableEq M] [DecidableEq N] [SampleableType N] [DecidableEq P]
  [SampleableType P] in
theorem refused_of_mem {p : ℕ} {Q : ChalList T M N} {t : T} {e : (T × M) × N} (he : e ∈ Q)
    (h : e.1.1 ∈ X.Omega t) : Refused X p Q t :=
  .inr ⟨e, he, h⟩

omit [DecidableEq P] [SampleableType P] in
/-- An admitted challenge query answered from `g`. -/
theorem mem_support_sigmaStep_chal (p : ℕ) (tm : T × M)
    (st : (Table P (T × M) N × Slice (T × M) N) × ChalList T M N)
    {z : Option N × ((Table P (T × M) N × Slice (T × M) N) × ChalList T M N)}
    (hz : z ∈ support ((sigmaStep (interface X p) sliceImpl₁ tm).run st)) :
    (Refused X p st.2 tm.1 ∧ z.2 = st) ∨
      (¬ Refused X p st.2 tm.1 ∧ ∃ y, z.2 = ((st.1.1, Function.update st.1.2 tm (some y)),
        st.2 ++ [(tm, y)]) ∧ ∀ v, st.1.2 tm = some v → y = v) := by
  rw [sigmaStep_run, support_map] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  by_cases hR : Refused X p st.2 tm.1
  · left
    refine ⟨hR, ?_⟩
    have h : (interface X p).impl tm = StateT.mk fun Q => if Refused X p Q tm.1 then pure (none, Q)
        else (fun y => (some y, Q ++ [(tm, y)])) <$>
          (liftM ((unifSpec + SliceSpec (T × M) N).query (.inr tm)) :
            OracleComp (unifSpec + SliceSpec (T × M) N) N) := rfl
    simp only [h, StateT.run_mk, hR, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hu
    subst hu
    rfl
  · right
    refine ⟨hR, ?_⟩
    have h : ((interface X p).impl tm).run st.2 =
        (fun y => (some y, st.2 ++ [(tm, y)])) <$>
          (liftM ((unifSpec + SliceSpec (T × M) N).query (.inr tm)) :
            OracleComp (unifSpec + SliceSpec (T × M) N) N) := by
      change (if Refused X p st.2 tm.1 then _ else _) = _
      simp only [hR, ↓reduceIte]
    rw [h, run_simulateQ_sliceImpl₁_query, support_map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨h1, h2⟩ := mem_support_lazyStep hw
    exact ⟨w.1, by dsimp only; rw [h1], h2⟩

omit [SampleableType P] in
/-- Game 1's first stage keeps the invariant: a guard-admitted challenge is a fresh point of `g`
whose set `Ω(T)` meets no earlier one. -/
theorem preservesInv_phase1Inv (p : ℕ) :
    QueryImpl.PreservesInv (phase1₁ (interface (M := M) (N := N) X p) (P := P))
      (Phase1Inv X) := by
  rintro (n | x | tm) st hst z hz
  · rw [mem_support_coinImpl_run hz]; exact hst
  · rw [mem_support_roStep₁ x st hz]; exact hst
  · rcases mem_support_sigmaStep_chal X p tm st hz with ⟨-, h⟩ | ⟨hR, y, h, hy⟩
    · rw [h]; exact hst
    rw [h]
    obtain ⟨⟨hans, hdisj⟩, hfill⟩ := hst
    have hfresh : ∀ e ∈ st.2, e.1 ≠ tm := fun e he het =>
      hR (refused_of_mem X he (het ▸ X.self_mem_Omega _))
    refine ⟨⟨fun e he => ?_, fun a ha b hb hab => ?_⟩, fun x hx => ?_⟩ <;> dsimp only at *
    · simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · rw [Function.update_of_ne (hfresh e he)]; exact hans e he
      · exact Function.update_self ..
    · simp only [List.mem_append, List.mem_singleton] at ha hb
      rcases ha with ha | rfl <;> rcases hb with hb | rfl
      · exact hdisj a ha b hb hab
      · exact absurd (refused_of_mem X ha hab) hR
      · exact absurd (refused_of_mem X hb ((X.mem_Omega_comm _ _).1 hab)) hR
      · rfl
    · by_cases hxt : x = tm
      · exact ⟨(tm, y), by simp, hxt.symm⟩
      · rw [Function.update_of_ne hxt] at hx
        obtain ⟨e, he, rfl⟩ := hfill x hx
        exact ⟨e, List.mem_append_left _ he, rfl⟩

omit [DecidableEq N] [SampleableType P] in
theorem mem_support_thPrimeImpl_inr (P' : P) (x : P × (T × M))
    (st : Table P (T × M) N × Slice (T × M) N) {z : N × (Table P (T × M) N × Slice (T × M) N)}
    (hz : z ∈ support ((thPrimeImpl P' (.inr x)).run st)) :
    (x.1 = P' ∧ z.2.2 = Function.update st.2 x.2 (some z.1) ∧
        ∀ v, st.2 x.2 = some v → z.1 = v) ∨ (x.1 ≠ P' ∧ z.2.2 = st.2) := by
  rw [thPrimeImpl_inr_run] at hz
  split_ifs at hz with hx
  · rw [support_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact .inl ⟨hx, (mem_support_lazyStep hu).1, (mem_support_lazyStep hu).2⟩
  · rw [support_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact .inr ⟨hx, rfl⟩

omit [DecidableEq N] [SampleableType P] in
theorem preservesInv_thPrimeImpl (P' : P) (Q : ChalList T M N) :
    QueryImpl.PreservesInv (thPrimeImpl (D := T × M) (N := N) P')
      (fun st => GoodSlice X Q st.2) := by
  rintro (n | x) st hst z hz
  · rw [mem_support_coinImpl_run hz]; exact hst
  · rcases mem_support_thPrimeImpl_inr P' x st hz with ⟨-, h, hv⟩ | ⟨-, h⟩
    · rw [h]
      refine ⟨fun e he => ?_, hst.2⟩
      by_cases hex : e.1 = x.2
      · rw [hex, Function.update_self, hv _ (hex ▸ hst.1 e he)]
      · rw [Function.update_of_ne hex]; exact hst.1 e he
    · rw [h]; exact hst

omit [DecidableEq N] [SampleableType P] in
/-- **The hazard of one fresh value of `g`.** From a good slice that is not bad, one evaluation
of `Th'` makes it bad with probability at most `1/|N|`. -/
theorem prEvent_bad_thPrimeImpl_le [Fintype N] (P' : P) (Q : ChalList T M N) (x : P × (T × M))
    (st : Table P (T × M) N × Slice (T × M) N) (hst : GoodSlice X Q st.2)
    (hb : ¬ Bad X Q st.2) :
    Pr{let z ← (thPrimeImpl P' (.inr x)).run st}[Bad X Q z.2.2] ≤ (Fintype.card N : ℝ≥0∞)⁻¹ := by
  rw [thPrimeImpl_inr_run]
  split_ifs with hx
  · unfold lazyStep
    cases hg : st.2 x.2 with
    | some v =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
        simp only [map_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hb]
      exact zero_le
    | none =>
      simp only [Functor.map_map]
      by_cases hex : ∃ e ∈ Q, x.2.1 ∈ X.Omega e.1.1
      · obtain ⟨e₀, he₀, hΩ₀⟩ := hex
        refine le_trans (prEvent_mono _ _ _ fun y hy => ?_)
          (SampleableType.prEvent_uniformSample_eq_singleton e₀.2).le
        obtain ⟨e, he, x', hx'Ω, hne, hgx'⟩ := hy
        by_cases hx' : x' = x.2
        · subst hx'
          rw [Function.update_self, Option.some_inj] at hgx'
          rw [hgx', hst.2 e₀ he₀ e he (X.mem_Omega_of_mem_of_mem hx'Ω hΩ₀)]
        · rw [Function.update_of_ne hx'] at hgx'
          exact absurd ⟨e, he, x', hx'Ω, hne, hgx'⟩ hb
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun y _ hy => ?_]
        · exact zero_le
        obtain ⟨e, he, x', hx'Ω, hne, hgx'⟩ := hy
        by_cases hx' : x' = x.2
        · subst hx'
          exact hex ⟨e, he, hx'Ω⟩
        · rw [Function.update_of_ne hx'] at hgx'
          exact hb ⟨e, he, x', hx'Ω, hne, hgx'⟩
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => ?_]
    · exact zero_le
    rw [support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hb

omit [DecidableEq P] [SampleableType P] in
/-- **The final evaluation.** From a slice that is not bad, the winning check succeeds with
probability at most `1/|N|`. -/
theorem prEvent_win_le [Fintype N] (Q : ChalList T M N) (out : ℕ × T × M)
    (st : Table P (T × M) N × Slice (T × M) N) (hb : ¬ Bad X Q st.2) :
    Pr{let v ← (simulateQ sliceImpl₁ (win X Q out)).run st}[v.1 = true] ≤
      (Fintype.card N : ℝ≥0∞)⁻¹ := by
  obtain ⟨j, t, m⟩ := out
  unfold win
  dsimp only
  cases hQ : Q[j]? with
  | none =>
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun v hv => ?_]
    · exact zero_le
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hv
    simp [hv]
  | some e =>
    obtain ⟨⟨tj, mj⟩, yj⟩ := e
    dsimp only
    split_ifs with hc
    · rw [run_simulateQ_sliceImpl₁_query, prEvent_map]
      unfold lazyStep
      cases hg : st.2 (t, m) with
      | some v =>
        rw [prEvent_eq_zero_of_forall_mem_support _ _ fun v' hv' => ?_]
        · exact zero_le
        simp only [support_pure, Set.mem_singleton_iff] at hv'
        subst hv'
        simp only [decide_eq_true_eq]
        rintro rfl
        refine hb ⟨((tj, mj), v), List.mem_of_getElem? hQ, (t, m), hc.1, fun h => hc.2 ?_, hg⟩
        exact congrArg Prod.snd h
      | none =>
        simp only [Functor.map_map, decide_eq_true_eq]
        exact (SampleableType.prEvent_uniformSample_eq_singleton yj).le
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun v hv => ?_]
      · exact zero_le
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hv
      simp [hv]

omit [DecidableEq T] [DecidableEq M] [DecidableEq N] [SampleableType N] [DecidableEq P]
  [SampleableType P] in
theorem phase1Inv_init : Phase1Inv (P := P) (M := M) (N := N) X
    ((fun _ => none, fun _ => none), []) :=
  ⟨⟨by simp, by simp⟩, fun _ h => absurd rfl h⟩

/-- **Game 1 of Theorem E.1.** With the challenges answered by an independent `g` that is
programmed into `Th` at `P` for the second stage, the adversary wins with probability at most
`(q₂ + 1)/|N|`. -/
theorem succ_game1_le [Fintype N] (p : ℕ) {σ : Type} {q₁ q₂ : ℕ}
    (A : Adversary P T M N σ q₁ q₂) :
    Pr{let b ← game1 (interface X p) A.toHiddenSlice}[b = true] ≤
      (q₂ + 1) / Fintype.card N := by
  unfold game1
  refine prEvent_bind_le_of_forall_le _ _ _ fun P' => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  have hinv : Phase1Inv X z.2 :=
    simulateQ_run_preservesInv _ _ (preservesInv_phase1Inv X p) A.A1 _ (phase1Inv_init X) z hz
  obtain ⟨st, ⟨H, g⟩, Q⟩ := z
  unfold tail₁
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun w => Bad X Q w.2.2) _
    (ε := (Fintype.card N : ℝ≥0∞)⁻¹) fun w _ hb => ?_).trans ?_
  · rw [bind_pure_comp, prEvent_map]
    exact prEvent_win_le X Q w.1 w.2 hb
  · have hhaz := prEvent_simulateQ_run_le_sum_of_isQueryBoundP (thPrimeImpl P')
      (IsRO₂Query P T M) (fun _ => 0) (fun st => GoodSlice X Q st.2) (fun st => Bad X Q st.2)
      (fun _ => (Fintype.card N : ℝ≥0∞)⁻¹) (fun _ _ _ => le_rfl)
      (preservesInv_thPrimeImpl X P' Q)
      (by
        rintro (n | x) s hn - hs w hw
        · rw [mem_support_coinImpl_run hw]; exact ⟨rfl, hs⟩
        · exact absurd trivial hn)
      (fun _ _ _ _ _ _ _ => Nat.le_succ _)
      (by
        rintro (n | x) s hc hinv' hs
        · exact absurd hc id
        · exact prEvent_bad_thPrimeImpl_le X P' Q x s hinv' hs)
      (A.A2 st P') (A.bound₂ st P') (H, g) hinv.1 (not_bad_of_phase1Inv X hinv)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hhaz
    calc _ ≤ (q₂ : ℝ≥0∞) * (Fintype.card N : ℝ≥0∞)⁻¹ + (Fintype.card N : ℝ≥0∞)⁻¹ :=
          add_le_add hhaz le_rfl
      _ = (q₂ + 1) / Fintype.card N := by
          rw [ENNReal.div_eq_inv_mul, mul_comm, mul_add, mul_one]

end Game1

/-- **Theorem E.1**, reduction form for the first step: with `C = HiddenSlice.reduction`, a
ZeroDist adversary making at most `q₁` queries,
`Succ^{sm-tcr-excl}_{Th,p}(A) ≤ (q₂ + 1)/|N| + Adv^{ZeroDist}(C)`. The paper's first summand
`Succ^{Avg-Search_{1/|N|}}(B)` is replaced by its value `(q₂ + 1)/|N|` from Lemma C.6
(`succ_game1_le`). -/
theorem succ_le_add_advantage [Fintype N] (X : ExclusiveTweaks T) (p : ℕ) {σ : Type}
    {q₁ q₂ : ℕ} (A : Adversary P T M N σ q₁ q₂) :
    succ X p A ≤ (q₂ + 1) / Fintype.card N +
      ENNReal.ofReal (ZeroDist.advantage (reduction (interface X p) A.toHiddenSlice)) := by
  have h := le_add_ofReal_abs_toReal_sub
    (a := Pr{let b ← game0 (interface X p) A.toHiddenSlice}[b = true])
    (b := Pr{let b ← game1 (interface X p) A.toHiddenSlice}[b = true])
    (prEvent_ne_top _) (prEvent_ne_top _)
  rw [abs_game_sub_eq_advantage] at h
  exact h.trans (add_le_add (succ_game1_le X p A) le_rfl)

/-- **Theorem E.1** (classical case), sharp form. An SM-TCR-EXCL adversary whose first stage
evaluates `Th` at most `q₁` times and whose second stage evaluates it at most `q₂` times succeeds
with probability at most `(q₂ + 1)/|N| + q₁/|P|`, for every target cap `p`. -/
theorem succ_le [Fintype N] [Fintype P] (X : ExclusiveTweaks T) (p : ℕ) {σ : Type}
    {q₁ q₂ : ℕ} (A : Adversary P T M N σ q₁ q₂) :
    succ X p A ≤ (q₂ + 1) / Fintype.card N + q₁ / Fintype.card P :=
  (prEvent_game_le (interface X p) A.toHiddenSlice).1.trans
    (add_le_add (succ_game1_le X p A) le_rfl)

/-- **Theorem E.1** (classical case), in the paper's form: an adversary making at most `q`
evaluations of `Th` in total succeeds with probability at most `(q + 1)/|N| + q/|P|`. -/
theorem succ_le_of_le [Fintype N] [Fintype P] (X : ExclusiveTweaks T) (p : ℕ) {σ : Type}
    {q₁ q₂ q : ℕ} (A : Adversary P T M N σ q₁ q₂) (hq : q₁ + q₂ ≤ q) :
    succ X p A ≤ (q + 1) / Fintype.card N + q / Fintype.card P := by
  refine (succ_le X p A).trans (add_le_add ?_ ?_) <;>
    refine ENNReal.div_le_div_right ?_ _ <;> norm_cast <;> omega

end SmTcrExcl

end ShrincsSecurity.Notions.Generic

end
