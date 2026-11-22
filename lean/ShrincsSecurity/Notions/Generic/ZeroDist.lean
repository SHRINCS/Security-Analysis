module

public import ShrincsSecurity.Notions.Generic.AvgSearch
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Distinguishing from constant zero

Main paper (`notes/txt/SHRINCS-Security-Analysis.txt`), Appendix C, *Public parameter
reprogramming*: **Definition C.4** (the experiment `ZeroDist`, lines 6360–6381) and **Lemma C.7**
(classical case, `[Kud25, Lemma 6.1.8]`, lines 6383–6388).

The first stage `A₁` of a two-stage adversary has private coins and oracle access to a boolean
function on the parameter space `P`: either `f_{P'}`, the indicator of a hidden uniform `P'`, or
the constant `f₀ = 0`. The second stage `A₂` receives `P'` and the state of `A₁`, without the
oracle, and outputs a bit. The advantage is the difference of the probabilities of output `1` in
the two worlds.

## Main statements

* `ZeroDist.advantage_le`: **Lemma C.7**, `Adv^{ZeroDist}(A) ≤ q / |P|`, and its one-sided
  forms in `ℝ≥0∞`, `ZeroDist.prEvent_experiment_le`.

## Proof

The first stage is run with a log of its queried points. The two worlds answer alike until `P'`
is queried (identical until bad, `QueryImpl.AgreeUntilBad`), and in the world `f₀` the run does
not depend on `P'` and logs at most `q` points, so `P'` is among them with probability at most
`q / |P|`. The two generic steps:

* `prEvent_uniform_bind_le_add_of_agree`: two runs that agree off a hit event `hit P' z` put the
  same mass on every continuation up to the hit mass; when the second run does not depend on the
  uniform `P'` and hits at most `q` parameters, the hit mass is at most `q / |P|`.
* `cnt_le_of_mem_support_simulateQ_run`: a counter raised by at most one per charged query is
  raised by at most `q` along a run with at most `q` charged queries.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.Notions.Generic

/-! ## Generic tools -/

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- A counter that free queries do not raise and each charged query raises by at most one is
raised by at most `q` along every run with at most `q` charged queries. -/
theorem cnt_le_of_mem_support_simulateQ_run (impl : QueryImpl spec (StateT σ ProbComp))
    (charged : ι → Prop) [DecidablePred charged] (cnt : σ → ℕ)
    (h_free : ∀ t s, ¬ charged t → ∀ z ∈ support ((impl t).run s), cnt z.2 ≤ cnt s)
    (h_charged : ∀ t s, charged t → ∀ z ∈ support ((impl t).run s), cnt z.2 ≤ cnt s + 1)
    {α : Type} (oa : OracleComp spec α) {q : ℕ} (hq : oa.IsQueryBoundP charged q) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), cnt z.2 ≤ cnt s + q := by
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    obtain ⟨hvalid, hcont⟩ := hq
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      at hz
    obtain ⟨y, hy, hz⟩ := hz
    by_cases ht : charged t
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 :=
        Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.1 (hvalid.resolve_left (· ht)))
      simp only [ht, ↓reduceIte, Nat.add_sub_cancel] at hcont
      have h1 := ih y.1 (hcont y.1) y.2 z hz
      have h2 := h_charged t s ht y hy
      omega
    · simp only [ht, ↓reduceIte] at hcont
      have h1 := ih y.1 (hcont y.1) y.2 z hz
      have h2 := h_free t s ht y hy
      omega

/-- Two computations that put the same mass on every event off `hit` put, after a common
continuation, the same mass on every event up to the mass of `hit` under the first. -/
theorem prEvent_bind_le_add_of_agree {β γ : Type} (mx my : ProbComp β) (hit : β → Prop)
    (hagree : ∀ E : β → Prop, Pr{let z ← mx}[E z ∧ ¬hit z] = Pr{let z ← my}[E z ∧ ¬hit z])
    (k : β → ProbComp γ) (E : γ → Prop) :
    Pr{let b ← mx >>= k}[E b] ≤ Pr{let b ← my >>= k}[E b] + Pr{let z ← mx}[hit z] := by
  classical
  have hhit : Pr{let z ← mx}[hit z] = ∑' z, Pr{let w ← mx}[w = z] * (if hit z then 1 else 0) := by
    have := prEvent_bind_eq_tsum mx (fun z => (pure z : ProbComp β)) hit
    simp only [bind_pure] at this
    rw [this]
    refine tsum_congr fun z => ?_
    rw [prEvent_pure]
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum, hhit, ← tsum_add]
  refine tsum_le_tsum fun z => ?_
  by_cases hz : hit z
  · simp only [hz, ↓reduceIte, mul_one]
    exact le_add_left (mul_le_of_le_one_right' (prEvent_le_one _))
  · simp only [hz, ↓reduceIte, mul_zero, add_zero]
    have h := hagree (· = z)
    rw [prEvent_congr _ _ _ fun w => ⟨fun h => h.1, fun h => ⟨h, h ▸ hz⟩⟩,
      prEvent_congr my _ _ fun w => ⟨fun h => h.1, fun h => ⟨h, h ▸ hz⟩⟩] at h
    rw [h]

/-- Agreement off `hit` gives `hit` the same mass. -/
theorem prEvent_hit_eq_of_agree {β : Type} (mx my : ProbComp β) (hit : β → Prop)
    (hagree : ∀ E : β → Prop, Pr{let z ← mx}[E z ∧ ¬hit z] = Pr{let z ← my}[E z ∧ ¬hit z]) :
    Pr{let z ← mx}[hit z] = Pr{let z ← my}[hit z] := by
  have hgood := hagree fun _ => True
  simp only [true_and] at hgood
  have e₁ := prEvent_add_prEvent_not_eq_prEvent_true mx hit
  have e₂ := prEvent_add_prEvent_not_eq_prEvent_true my hit
  rw [prEvent_true_eq_one, hgood] at e₁
  rw [prEvent_true_eq_one] at e₂
  exact (ENNReal.add_left_inj (prEvent_ne_top _)).1 (e₁.trans e₂.symm)

/-- A bound on an event after every possible draw bounds it after the draw. -/
theorem prEvent_bind_le_of_support' {β : Type} {mx : ProbComp β} {f : β → ProbComp Prop}
    {ε : ℝ≥0∞} (h : ∀ a ∈ support mx, prEvent (f a) ≤ ε) : prEvent (mx >>= f) ≤ ε := by
  simpa using prEvent_bind_le_of_forall_le_of_support mx f (fun p => p) (by simpa using h)

/-- Two-sided additive bounds in `ℝ≥0∞` give an absolute bound on the real difference. -/
theorem abs_toReal_sub_le {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (h₁ : a ≤ b + c) (h₂ : b ≤ a + c) : |a.toReal - b.toReal| ≤ c.toReal := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  constructor
  · simpa only [ENNReal.toReal_add hb hc, add_comm] using
      ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, hc⟩) h₁
  · simpa only [ENNReal.toReal_add ha hc, add_comm] using
      ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, hc⟩) h₂

/-- A finite value exceeds another by at most their real distance. -/
theorem le_add_ofReal_abs_toReal_sub {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a ≤ b + ENNReal.ofReal |a.toReal - b.toReal| := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + |a.toReal - b.toReal|) :=
        ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a.toReal - b.toReal)])
    _ = b + ENNReal.ofReal |a.toReal - b.toReal| := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _), ENNReal.ofReal_toReal hb]

/-- The real form of `q / |P|`. -/
theorem toReal_natCast_div_card (P : Type) [Fintype P] (q : ℕ) :
    ((q : ℝ≥0∞) / Fintype.card P).toReal = (q : ℝ) / Fintype.card P := by
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

theorem natCast_div_card_ne_top (P : Type) [Fintype P] [Nonempty P] (q : ℕ) :
    (q : ℝ≥0∞) / Fintype.card P ≠ ⊤ :=
  ENNReal.div_ne_top (ENNReal.natCast_ne_top q) (by simp [Fintype.card_ne_zero])

variable {P : Type} [Fintype P] [SampleableType P]

/-- **Hidden-parameter hit bound.** Let `run₀ P'` agree with `run₁`, a run that does not depend
on `P'`, off a hit event `hit P' z`, and let every possible output of `run₁` hit at most `q`
parameters. Then for `P'` uniform, every continuation `k P'` reaches an event with probability at
most `q / |P|` more after `run₀ P'` than after `run₁`, and conversely. -/
theorem prEvent_uniform_bind_le_add_of_agree {β γ : Type} (run₀ : P → ProbComp β)
    (run₁ : ProbComp β) (hit : P → β → Prop)
    (hagree : ∀ p (E : β → Prop),
      Pr{let z ← run₀ p}[E z ∧ ¬hit p z] = Pr{let z ← run₁}[E z ∧ ¬hit p z])
    {q : ℕ} (hcard : ∀ z ∈ support run₁, ∀ (_ : DecidablePred (hit · z)),
      (Finset.univ.filter (hit · z)).card ≤ q)
    (k : P → β → ProbComp γ) (E : γ → Prop) :
    Pr{let p ← $ᵗ P; let z ← run₀ p; let b ← k p z}[E b] ≤
        Pr{let p ← $ᵗ P; let z ← run₁; let b ← k p z}[E b] + q / Fintype.card P ∧
      Pr{let p ← $ᵗ P; let z ← run₁; let b ← k p z}[E b] ≤
        Pr{let p ← $ᵗ P; let z ← run₀ p; let b ← k p z}[E b] + q / Fintype.card P := by
  classical
  have hmass : Pr{let p ← $ᵗ P; let z ← run₁}[hit p z] ≤ q / Fintype.card P := by
    rw [prEvent_bind_bind_swap_of_countable_left ($ᵗ P) run₁ hit]
    refine prEvent_bind_le_of_support' fun z hz => ?_
    rw [SampleableType.prEvent_uniformSample]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcard z hz _) _
  have hmass₀ : Pr{let p ← $ᵗ P; let z ← run₀ p}[hit p z] ≤ q / Fintype.card P := by
    refine le_trans (le_of_eq ?_) hmass
    exact prEvent_bind_congr_of_forall _ _ _ _ _ fun p =>
      prEvent_hit_eq_of_agree _ _ _ (hagree p)
  constructor
  · have h := prEvent_bind_le_add_of_forall_le ($ᵗ P) (fun p => run₀ p >>= k p)
      (fun p => run₁ >>= k p) (fun p => (fun z => hit p z) <$> run₀ p) E E id fun p => by
        simpa only [prEvent_map, Function.comp_def, id] using
          prEvent_bind_le_add_of_agree (run₀ p) run₁ (hit p) (hagree p) (k p) E
    simp only [prEvent_norm, id] at h
    refine h.trans (add_le_add le_rfl ?_)
    simpa only [prEvent_norm] using hmass₀
  · have h := prEvent_bind_le_add_of_forall_le ($ᵗ P) (fun p => run₁ >>= k p)
      (fun p => run₀ p >>= k p) (fun p => (fun z => hit p z) <$> run₁) E E id fun p => by
        simpa only [prEvent_map, Function.comp_def, id] using
          prEvent_bind_le_add_of_agree run₁ (run₀ p) (hit p) (fun E => (hagree p E).symm) (k p) E
    simp only [prEvent_norm, id] at h
    refine h.trans (add_le_add le_rfl ?_)
    simpa only [prEvent_norm] using hmass

end Generic

/-! ## The experiment -/

namespace ZeroDist

variable (P : Type)

/-- Oracle access to a boolean function on the parameter space. -/
abbrev FSpec : OracleSpec P := P →ₒ Bool

/-- The first stage's oracles: private coins and the boolean function. -/
abbrev AdvSpec : OracleSpec (ℕ ⊕ P) := unifSpec + FSpec P

/-- A query to the boolean function. -/
def IsFQuery : ℕ ⊕ P → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred (IsFQuery P) := fun x => by
  rcases x with _ | _ <;> simp only [IsFQuery] <;> infer_instance

/-- A ZeroDist adversary `A = (A₁, A₂)` with state `σ`, whose first stage makes at most `q`
oracle queries. -/
structure Adversary (σ : Type) (q : ℕ) where
  /-- The first stage, with oracle access to `f_{P'}` or `f₀`. -/
  A1 : OracleComp (AdvSpec P) σ
  /-- The second stage: it receives `P'`, without the oracle. -/
  A2 : σ → P → ProbComp Bool
  /-- The first stage makes at most `q` oracle queries. -/
  queryBound : A1.IsQueryBoundP (IsFQuery P) q

variable {P}

/-- The first stage's oracles with the boolean function `ans`. -/
def oracle (ans : P → Bool) : QueryImpl (AdvSpec P) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + fun x => (pure (ans x) : ProbComp Bool)

@[simp] theorem oracle_inl (ans : P → Bool) (n : ℕ) :
    oracle ans (.inl n) = (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := rfl

@[simp] theorem oracle_inr (ans : P → Bool) (x : P) :
    oracle ans (.inr x) = (pure (ans x) : ProbComp Bool) := rfl

variable [DecidableEq P]

/-- `f_{P'}`: `1` exactly at `P'`. -/
def fHidden (P' : P) : P → Bool := fun x => decide (x = P')

/-- `f₀`: constantly `0`. -/
def fZero : P → Bool := fun _ => false

variable [SampleableType P]

/-- **The experiment `ZeroDist(A)`** of Definition C.4 for a fixed coin: `b = 1` gives the first
stage `f_{P'}`, `b = 0` gives it `f₀`. -/
def experiment {σ : Type} {q : ℕ} (b : Bool) (A : Adversary P σ q) : ProbComp Bool := do
  let P' ← $ᵗ P
  let st ← simulateQ (oracle (if b then fHidden P' else fZero)) A.A1
  A.A2 st P'

/-- **`Adv^{ZeroDist}(A)`** (Definition C.4): the difference of the probabilities of output `1`
given `b = 1` and given `b = 0`. -/
noncomputable def advantage {σ : Type} {q : ℕ} (A : Adversary P σ q) : ℝ :=
  |(Pr{let b ← experiment true A}[b = true]).toReal -
    (Pr{let b ← experiment false A}[b = true]).toReal|

/-! ## Proof of Lemma C.7 -/

/-- The first stage's oracles with the boolean function `ans`, recording the queried points. -/
def loggedOracle (ans : P → Bool) : QueryImpl (AdvSpec P) (StateT (Finset P) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Finset P) ProbComp) +
    fun x => (StateT.mk fun s => pure (ans x, insert x s) : StateT (Finset P) ProbComp Bool)

omit [SampleableType P] in
@[simp] theorem loggedOracle_inl_run (ans : P → Bool) (n : ℕ) (s : Finset P) :
    (loggedOracle ans (.inl n)).run s =
      (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) >>= fun u => pure (u, s) := rfl

omit [SampleableType P] in
@[simp] theorem loggedOracle_inr_run (ans : P → Bool) (x : P) (s : Finset P) :
    (loggedOracle ans (.inr x)).run s = (pure (ans x, insert x s) : ProbComp _) := rfl

omit [SampleableType P] in
theorem map_run_simulateQ_loggedOracle (ans : P → Bool) {α : Type}
    (oa : OracleComp (AdvSpec P) α) (s : Finset P) :
    Prod.fst <$> (simulateQ (loggedOracle ans) oa).run s = simulateQ (oracle ans) oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | x
    · rw [loggedOracle_inl_run, oracle_inl, bind_assoc]
      simp only [pure_bind]
      exact bind_congr fun u => ih u s
    · rw [loggedOracle_inr_run, oracle_inr, pure_bind, pure_bind]
      exact ih _ _

omit [SampleableType P] in
theorem mem_support_loggedOracle_inl {ans : P → Bool} {n : ℕ} {s : Finset P}
    {z : (AdvSpec P).Range (.inl n) × Finset P}
    (hz : z ∈ support ((loggedOracle ans (.inl n)).run s)) : z.2 = s := by
  rw [loggedOracle_inl_run, mem_support_bind_iff] at hz
  obtain ⟨_, -, hz⟩ := hz
  rw [mem_support_pure_iff] at hz
  rw [hz]

/-- **Lemma C.7** (`[Kud25, Lemma 6.1.8]`), one-sided forms: output `1` given `b = 1` is at most
`q / |P|` more likely than given `b = 0`, and conversely. -/
theorem prEvent_experiment_le [Fintype P] {σ : Type} {q : ℕ} (A : Adversary P σ q) :
    Pr{let b ← experiment true A}[b = true] ≤
        Pr{let b ← experiment false A}[b = true] + q / Fintype.card P ∧
      Pr{let b ← experiment false A}[b = true] ≤
        Pr{let b ← experiment true A}[b = true] + q / Fintype.card P := by
  classical
  have hexp : ∀ b, experiment b A = ($ᵗ P >>= fun P' =>
      (simulateQ (loggedOracle (if b then fHidden P' else fZero)) A.A1).run ∅ >>= fun z =>
        A.A2 z.1 P') := by
    intro b
    simp only [experiment, ← map_run_simulateQ_loggedOracle _ A.A1 ∅, bind_map_left]
  have hpres : ∀ ans : P → Bool, ∀ P' : P,
      QueryImpl.PreservesInv (loggedOracle ans) (fun s => P' ∈ s) := by
    rintro ans P' (n | x) s hs z hz
    · rw [mem_support_loggedOracle_inl hz]; exact hs
    · simp only [loggedOracle_inr_run, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Finset.mem_insert_of_mem hs
  have hagree : ∀ P' : P, QueryImpl.AgreeUntilBad (loggedOracle (fHidden P'))
      (loggedOracle fZero) (fun s => P' ∈ s) := by
    intro P'
    refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun t s hs => ?_
    rcases t with n | x
    · left; rfl
    · by_cases hx : x = P'
      · subst hx
        right
        constructor <;>
        · intro z hz
          simp only [loggedOracle_inr_run, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact Finset.mem_insert_self _ _
      · left
        simp only [loggedOracle_inr_run, fHidden, fZero, hx, decide_false]
  have key := prEvent_uniform_bind_le_add_of_agree
    (fun P' => (simulateQ (loggedOracle (fHidden P')) A.A1).run ∅)
    ((simulateQ (loggedOracle fZero) A.A1).run ∅) (fun P' z => P' ∈ z.2)
    (fun P' E => (hagree P').prEvent_simulateQ_run_and_not_bad_eq (hpres _ P') (hpres _ P')
      A.A1 ∅ E)
    (q := q)
    (fun z hz _ => by
      have := cnt_le_of_mem_support_simulateQ_run (loggedOracle fZero) (IsFQuery P)
        Finset.card
        (by
          rintro (n | x) s hn z hz
          · rw [mem_support_loggedOracle_inl hz]
          · exact absurd trivial hn)
        (by
          rintro (n | x) s - z hz
          · rw [mem_support_loggedOracle_inl hz]; exact Nat.le_succ _
          · simp only [loggedOracle_inr_run, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact Finset.card_insert_le _ _)
        A.A1 A.queryBound ∅ z hz
      simp only [Finset.card_empty, zero_add] at this
      convert this
      ext p
      simp)
    (fun P' z => A.A2 z.1 P') (· = true)
  rw [hexp true, hexp false]
  simpa only [prEvent_norm, ↓reduceIte, Bool.false_eq_true] using key

/-- **Lemma C.7** (`[Kud25, Lemma 6.1.8]`). A ZeroDist adversary whose first stage makes at most
`q` classical queries has advantage at most `q / |P|`. -/
theorem advantage_le [Fintype P] {σ : Type} {q : ℕ} (A : Adversary P σ q) :
    advantage A ≤ q / Fintype.card P := by
  obtain ⟨h₁, h₀⟩ := prEvent_experiment_le A
  rw [advantage, ← toReal_natCast_div_card]
  exact abs_toReal_sub_le (prEvent_ne_top _) (prEvent_ne_top _) (natCast_div_card_ne_top P q)
    h₁ h₀

end ZeroDist

end ShrincsSecurity.Notions.Generic

end
