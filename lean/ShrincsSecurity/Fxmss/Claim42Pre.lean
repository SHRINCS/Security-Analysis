module

public import ShrincsSecurity.Fxmss.Claim42
public import ShrincsSecurity.Repro.PerCall

/-!
# Claim 4.2 with the paper's figure: only the forger's queries count

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.2** and Appendix C, **Corollary C.3**
(txt lines 3354–3365): the advantage of the distinguisher `B₁` (Algorithm 5) against `DI-Repro` is
bounded through the query pattern of Algorithm 5, by `(q_{h,1} + q_{h,2}) / |Y|`.

By Corollary C.2 in expectation form (`Repro.diAdvantage_le_expectedPre`),
`Adv^DI-Repro(B₁) ≤ E[q_pre] / |X₁|`, where `q_pre` counts, at each reprogramming call that is not
refused, the earlier hash queries at its second input. Along every execution of the lazy game,
`q_pre ≤ q_{h,1} + q_{h,2}` (`B1_count_le`):

* the potential `count + #(logged queries whose second input is not yet submitted)` grows by at
  most one at each forwarded query of the forger (`q_{h,1} + q_{h,2}` of them) and is unchanged by
  a reprogramming call that is not refused (its share of `q_pre` moves from the pending queries to
  the counter) and by the read-back `O_b(R, x₂)` of a signing query (`x₂` is submitted by then,
  whether the call was refused or not);
* the verification query of the forgery, at the second input `x₂* = (PK.seed, PK.sf, idx*, M*)`,
  is not charged: from then on the potential ignores the queries at `x₂*`, which no later call
  submits (the completion of Remark 4.6 signs messages `≠ M*`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

namespace Claim42

/-! ## Generic: a potential along a nested simulation -/

section Generic

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α BS LS : Type}

/-- **A potential along a nested simulation.** If every simulated step of a `p`-query raises the
potential `Φ` of the outer state by at most one, and every other step does not raise it, the
simulation of a program with at most `n` `p`-queries raises it by at most `n`. -/
theorem nested_pot_le (implB : QueryImpl spec (StateT BS (OracleComp spec')))
    (implL : QueryImpl spec' (StateT LS ProbComp)) (Φ : LS → ℕ) {p : ι → Prop}
    [DecidablePred p]
    (hstep : ∀ t ls bs, ∀ z ∈ support ((simulateQ implL ((implB t).run bs)).run ls),
      Φ z.2 ≤ Φ ls + if p t then 1 else 0)
    (oa : OracleComp spec α) {n : ℕ} (h : oa.IsQueryBoundP p n) (ls : LS) (bs : BS) :
    ∀ z ∈ support ((simulateQ implL ((simulateQ implB oa).run bs)).run ls), Φ z.2 ≤ Φ ls + n := by
  induction oa using OracleComp.inductionOn generalizing n ls bs with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    intro z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have h1 := hstep t ls bs w hw
    have h2 := ih w.1.1 (h.2 w.1.1) w.2 w.1.2 z hz
    by_cases hp : p t
    · have := h.1.resolve_left (not_not.2 hp)
      simp only [hp, ↓reduceIte] at h1 h2
      omega
    · simp only [hp, ↓reduceIte] at h1 h2
      omega

/-- The support of a nested simulation of a bind. -/
theorem mem_support_nested_bind (implB : QueryImpl spec (StateT BS (OracleComp spec')))
    (implL : QueryImpl spec' (StateT LS ProbComp)) {β : Type} (oa : OracleComp spec α)
    (f : α → OracleComp spec β) (ls : LS) (bs : BS) {z : (β × BS) × LS}
    (hz : z ∈ support ((simulateQ implL ((simulateQ implB (oa >>= f)).run bs)).run ls)) :
    ∃ w ∈ support ((simulateQ implL ((simulateQ implB oa).run bs)).run ls),
      z ∈ support ((simulateQ implL ((simulateQ implB (f w.1.1)).run w.1.2)).run w.2) := by
  simpa only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] using hz

end Generic

variable {P : Params} {pr : Primitives P} {Msg : Type}
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [DecidableEq pr.PkSeed] [SampleableType pr.Digest] [DecidableEq Msg]

/-! ## The potential -/

/-- The logged queries whose second input is not submitted yet and satisfies `Q`. -/
noncomputable def pend (Q : X2 pr Msg → Prop) (s : LS pr Msg) : ℕ :=
  s.log.countP fun p => decide (p.2 ∉ s.submitted ∧ Q p.2)

/-- The potential: the counter `q_pre` plus the pending queries satisfying `Q`. -/
noncomputable def pot (Q : X2 pr Msg → Prop) (s : LS pr Msg) : ℕ := s.count + pend Q s

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.Digest] in
theorem pot_mono {Q Q' : X2 pr Msg → Prop} (h : ∀ x, Q x → Q' x) (s : LS pr Msg) :
    pot Q s ≤ pot Q' s := by
  unfold pot pend
  refine Nat.add_le_add_left (List.countP_mono_left fun p _ hp => ?_) _
  simp only [decide_eq_true_eq] at hp ⊢
  exact ⟨hp.1, h _ hp.2⟩

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.Digest] in
theorem pot_true (s : LS pr Msg) : pot (fun _ => True) s = s.count + Repro.pendQ s := by
  simp [pot, pend, Repro.pendQ]

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [SampleableType pr.Digest] in
/-- Submitting a fresh `x₂` satisfying `Q` moves exactly the queries at `x₂` (its share of
`q_pre`) out of the pending ones. -/
theorem pend_insert (Q : X2 pr Msg → Prop) (s s' : LS pr Msg) {x₂ : X2 pr Msg}
    (hl : s'.log = s.log) (hs : s'.submitted = insert x₂ s.submitted)
    (hx : x₂ ∉ s.submitted) (hQ : Q x₂) :
    pend Q s' + Repro.preCount s.log x₂ = pend Q s := by
  unfold pend Repro.preCount
  rw [hl, hs]
  generalize s.log = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    by_cases h : a.2 = x₂
    · have h1 : decide (a.2 ∉ insert x₂ s.submitted ∧ Q a.2) = false := by simp [h]
      have h2 : decide (a.2 ∉ s.submitted ∧ Q a.2) = true := by simp [h, hx, hQ]
      have h3 : decide (a.2 = x₂) = true := by simp [h]
      rw [h1, h2, h3]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have h3 : decide (a.2 = x₂) = false := by simp [h]
      have h4 : decide (a.2 ∉ insert x₂ s.submitted ∧ Q a.2) =
          decide (a.2 ∉ s.submitted ∧ Q a.2) := by simp [h]
      rw [h3, h4]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega

omit [Fintype pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] in
/-- A lazy hash query raises the potential by one if its second input is pending and satisfies
`Q`, and leaves it unchanged otherwise. -/
theorem pot_hash (Q : X2 pr Msg → Prop) (x : RoIn pr Msg) (s : LS pr Msg)
    (w) (hw : w ∈ support ((Repro.lazyHash x).run s)) :
    pot Q w.2 = pot Q s + if x.2 ∉ s.submitted ∧ Q x.2 then 1 else 0 := by
  obtain ⟨-, hL, hl, hc, -⟩ := Repro.lazyHash_support x s w hw
  simp only [pot, pend, hL, hl, hc, List.countP_cons]
  split_ifs <;> simp_all
  omega

omit [Fintype pr.Y] [Inhabited pr.Y] in
/-- A reprogramming call submits its second input and, if that input satisfies `Q`, keeps the
potential. -/
theorem pot_repro (b : Bool) (Q : X2 pr Msg → Prop) (x₂ : X2 pr Msg) (s : LS pr Msg)
    (hQ : Q x₂) (r) (hr : r ∈ support ((Repro.lazyDIRepro b x₂).run s)) :
    pot Q r.2 = pot Q s ∧ x₂ ∈ r.2.submitted := by
  rw [Repro.lazyDIRepro_run] at hr
  by_cases hx : x₂ ∈ s.submitted
  · simp only [hx, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨rfl, hx⟩
  · simp only [hx, ↓reduceIte, support_map, Set.mem_image] at hr
    obtain ⟨w, -, rfl⟩ := hr
    refine ⟨?_, Finset.mem_insert_self _ _⟩
    have := pend_insert Q s ((some w.1, { s with
      table := if b then Function.update s.table (w.1, x₂) none else s.table
      submitted := insert x₂ s.submitted
      bad := s.bad || (s.table (w.1, x₂)).isSome
      count := s.count + Repro.preCount s.log x₂ }) : Option pr.Y × LS pr Msg).2 rfl rfl hx hQ
    simp only [pot] at this ⊢
    omega

/-! ## The steps of `B₁`'s signing phase -/

omit [Fintype pr.Y] in
theorem lazy_implB_unif (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (n : ℕ)
    (ls : LS pr Msg) (bs : St pr Msg) (z)
    (hz : z ∈ support ((simulateQ (Repro.lazyDIImpl b)
      ((implB pr Msg K sk (.inl (.inl n))).run bs)).run ls)) : z.2 = ls := by
  simp [implB, fwd, Repro.lazyDIImpl] at hz
  obtain ⟨y, rfl⟩ := hz
  rfl

omit [Fintype pr.Y] in
theorem lazy_implB_ro (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (x : RoIn pr Msg)
    (ls : LS pr Msg) (bs : St pr Msg) (z)
    (hz : z ∈ support ((simulateQ (Repro.lazyDIImpl b)
      ((implB pr Msg K sk (.inl (.inr x))).run bs)).run ls)) :
    ∃ w ∈ support ((Repro.lazyHash x).run ls), z.2 = w.2 := by
  simp only [implB, fwd, Repro.lazyDIImpl, StateT.run_monadLift, monadLift_self,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

omit [Fintype pr.Y] in
/-- A signing query whose second input satisfies `Q` does not raise the potential: a call that is
not refused moves its share of `q_pre` from the pending queries to the counter, and the read-back
is at a submitted second input. -/
theorem lazy_implB_sign (b : Bool) (Q : X2 pr Msg → Prop) (K : Keys pr) (sk : LeafId → ℕ → pr.Y)
    (q : Msg × LeafId) (hQ : Q (x2Of K q)) (ls : LS pr Msg) (bs : St pr Msg) (z)
    (hz : z ∈ support ((simulateQ (Repro.lazyDIImpl b)
      ((implB pr Msg K sk (.inr q)).run bs)).run ls)) : pot Q z.2 ≤ pot Q ls := by
  by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ bs.used
  · simp only [implB, signB_run_fresh K sk q bs h, Repro.lazyDIImpl, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, hr, w, hw, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := pot_repro b Q _ ls hQ r hr
    have h3 := pot_hash Q _ r.2 w hw
    simp only [h2, not_true_eq_false, false_and, ↓reduceIte, add_zero] at h3
    show pot Q w.2 ≤ pot Q ls
    omega
  · simp [implB, signB_run_else K sk q bs h] at hz
    subst hz
    exact le_rfl

omit [Fintype pr.Y] in
/-- The forger's signing phase raises the potential `count + pendQ` by at most `q_{h,2}`. -/
theorem forge_pot_le (b : Bool) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) {β : Type}
    (oa : OracleComp (fullSpec pr Msg) β) {n : ℕ} (h : oa.IsQueryBoundP (IsRoQuery' pr Msg) n)
    (ls : LS pr Msg) (bs : St pr Msg) :
    ∀ z ∈ support ((simulateQ (Repro.lazyDIImpl b)
      ((simulateQ (implB pr Msg K sk) oa).run bs)).run ls),
      pot (fun _ => True) z.2 ≤ pot (fun _ => True) ls + n := by
  refine nested_pot_le _ _ _ (fun t ls bs z hz => ?_) oa h ls bs
  rcases t with (n | x) | q
  · rw [lazy_implB_unif b K sk n ls bs z hz]
    omega
  · obtain ⟨w, hw, he⟩ := lazy_implB_ro b K sk x ls bs z hz
    rw [he, pot_hash _ x ls w hw]
    simp only [IsRoQuery', ↓reduceIte]
    split_ifs <;> omega
  · have := lazy_implB_sign b (fun _ => True) K sk q trivial ls bs z hz
    omega

omit [Fintype pr.Y] in
/-- The completion of Remark 4.6 does not raise a potential that counts every second input it
submits. -/
theorem completion_pot_le (b : Bool) (Q : X2 pr Msg → Prop) (K : Keys pr)
    (sk : LeafId → ℕ → pr.Y) (M : Msg) (hQ : ∀ id, Q (x2Of K (M, id))) (ids : List LeafId)
    (ls : LS pr Msg) (bs : St pr Msg) :
    ∀ z ∈ support ((simulateQ (Repro.lazyDIImpl b)
      ((simulateQ (implB pr Msg K sk) (completion pr Msg M ids)).run bs)).run ls),
      pot Q z.2 ≤ pot Q ls := by
  induction ids generalizing ls bs with
  | nil =>
    intro z hz
    simp only [completion, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact le_rfl
  | cons id ids ih =>
    intro z hz
    simp only [completion] at hz
    obtain ⟨w, hw, hz⟩ := mem_support_nested_bind _ _ _ _ ls bs hz
    simp only [simulateQ_spec_query] at hw
    exact (ih w.2 w.1.2 z hz).trans (lazy_implB_sign b Q K sk (M, id) (hQ id) ls bs w hw)

end Claim42

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

namespace Claim42

/-! ## `q_pre ≤ q_{h,1} + q_{h,2}` along every execution -/

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [Fintype pr.Y] in
/-- **The signing phase charges only the forger's queries**: along every execution of `B₁`'s
signing phase in the lazy `DI-Repro_b`, the final `q_pre` is at most the initial potential plus
`q_{h,2}`. -/
theorem stage2_count_le (b : Bool) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (st : A.State) (K : Keys pr) (sk : LeafId → ℕ → pr.Y) (ls : LS pr Msg) (bs : St pr Msg) :
    ∀ z ∈ support ((simulateQ (Repro.lazyDIImpl b) ((simulateQ (implB pr Msg K sk)
      (stage2Prog pr Msg slKeygen A.toFxmssAdversary st K)).run bs)).run ls),
      z.2.count ≤ pot (fun _ => True) ls + qh₂ := by
  intro z hz
  unfold stage2Prog at hz
  obtain ⟨w₁, hw₁, hz⟩ := mem_support_nested_bind _ _ _ _ ls bs hz
  obtain ⟨w₂, hw₂, hz⟩ := mem_support_nested_bind _ _ _ _ _ _ hz
  obtain ⟨w₃, hw₃, hz⟩ := mem_support_nested_bind _ _ _ _ _ _ hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have h₁ := forge_pot_le b K sk _ (A.roBound₂ st K.S K.toPK) ls bs w₁ hw₁
  simp only [simulateQ_spec_query] at hw₂
  obtain ⟨v, hv, he⟩ := lazy_implB_ro b K sk _ w₁.2 w₁.1.2 w₂ hw₂
  have h₂ : pot (fun x => x ≠ (K.pk, K.pkSf, toIdx w₁.1.1.2.1, w₁.1.1.1)) v.2 =
      pot (fun x => x ≠ (K.pk, K.pkSf, toIdx w₁.1.1.2.1, w₁.1.1.1)) w₁.2 := by
    rw [pot_hash _ _ w₁.2 v hv]
    simp [roIn]
  have h₃ := completion_pot_le b (fun x => x ≠ (K.pk, K.pkSf, toIdx w₁.1.1.2.1, w₁.1.1.1)) K sk
    (otherMsg Msg w₁.1.1.1)
    (fun id h => otherMsg_ne Msg w₁.1.1.1 (congrArg (fun x : X2 pr Msg => x.2.2.2) h))
    (anchorList P K.S) w₂.2 w₂.1.2 w₃ hw₃
  have h₄ := pot_mono (fun x (_ : x ≠ (K.pk, K.pkSf, toIdx w₁.1.1.2.1, w₁.1.1.1)) => trivial) w₁.2
  rw [he] at h₃
  have h₅ : w₃.2.count ≤ pot (fun x => x ≠ (K.pk, K.pkSf, toIdx w₁.1.1.2.1, w₁.1.1.1)) w₃.2 :=
    Nat.le_add_right _ _
  show w₃.2.count ≤ _
  omega

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg] [Fintype pr.Y] in
/-- **`q_pre ≤ q_{h,1} + q_{h,2}`** on every execution of `B₁` in the lazy `DI-Repro_b`. -/
theorem B1_count_le (b : Bool) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    ∀ z ∈ support ((simulateQ (Repro.lazyDIImpl b) (B1 pr Msg slKeygen A).run).run
      Repro.LazyState.init), z.2.count ≤ qh₁ + qh₂ := by
  have hl : ∀ {β : Type} (oa : ProbComp β) (s : LS pr Msg),
      (simulateQ (Repro.lazyDIImpl b) (liftM oa : OracleComp (DSpec pr Msg) β)).run s =
        (fun x => (x, s)) <$> oa := fun oa s => simulateQ_add_liftM_run _ oa s
  intro z hz
  change z ∈ support ((simulateQ (Repro.lazyDIImpl b)
    (B1run pr Msg slKeygen A.toFxmssAdversary)).run Repro.LazyState.init) at hz
  unfold B1run at hz
  simp only [simulateQ_bind, StateT.run_bind, hl, bind_map_left, mem_support_bind_iff] at hz
  obtain ⟨pk, -, p₁, hp₁, hz⟩ := hz
  have h₁ := Repro.count_add_pend_le b _ qh₁ (fwd_hashBound slKeygen A) _ p₁ hp₁
  have h₀ : Repro.pendQ (Repro.LazyState.init : LS pr Msg) = 0 := by
    simp [Repro.pendQ, Repro.LazyState.init]
  rw [h₀] at h₁
  simp only [Repro.LazyState.init, zero_add] at h₁
  unfold B1cont at hz
  by_cases hv : p₁.1.1.TreeValid P.hsf
  swap
  · rw [ite_eq_left hv] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    show p₁.2.count ≤ _
    omega
  rw [ite_eq_right (not_not.2 hv)] at hz
  simp only [simulateQ_bind, StateT.run_bind, hl, bind_map_left, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨f, -, pkSl, -, w, hw, rfl⟩ := hz
  have h₂ := stage2_count_le pr Msg slKeygen b A _ _ _ _ _ w hw
  rw [pot_true] at h₂
  show w.2.count ≤ _
  omega

end Claim42

omit [Fintype pr.Digest] [DecidableEq pr.Digest] in
/-- **Claim 4.2 with Corollary C.3** (the paper's figure): the distinguisher `B₁` has advantage at
most `(q_{h,1} + q_{h,2}) / |Y|` against `DI-Repro`; only the forger's own queries to `H_msg^sf`
count, not the hash queries of `B₁`'s signing simulation and of the verification. -/
theorem B1_diAdvantage_le {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    ENNReal.ofReal (Repro.diAdvantage (B1 pr Msg slKeygen A)) ≤
      ((qh₁ + qh₂ : ℕ) : ℝ≥0∞) / Fintype.card pr.Y := by
  refine (Repro.diAdvantage_le_expectedPre _ false).trans (ENNReal.div_le_div_right ?_ _)
  rw [Repro.expectedPre_eq_lazy]
  refine Repro.expect_le_of_forall _ _ fun n hn => ?_
  simp only [support_map, Set.mem_image] at hn
  obtain ⟨z, hz, rfl⟩ := hn
  exact Claim42.B1_count_le pr Msg slKeygen false A z hz

end ShrincsSecurity.Fxmss.Rom

end
