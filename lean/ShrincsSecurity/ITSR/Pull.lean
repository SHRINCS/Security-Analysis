module

public import ShrincsSecurity.ITSR.Classification

/-!
# The pull probability

`ITSR-Classical.pdf`, Lemma 6 (pull probability of a fixed index set) and the bad-event bound of
Lemma 10.

Both bounds hold for *fixed* tapes: they are statements about the pre-sampled game run from an
arbitrary state, and the only randomness they use is that of the challenge keys (the adversary's
coins stay oracle randomness and are averaged out step by step, so the bounds are uniform in the
coins as well). The key fact is the one of Remark 1: the challenge message is fixed before the
challenge key is drawn uniformly, so given the past, the key that would pull a given direct point
is determined.

**Lemma 6** (`prob_pulled_le`) is proved by an induction over the adversary that conditions on
the earlier keys, as in the paper's Eq. (13); it charges the injective maps `σ : B → [r]` of
Eq. (11) through the falling-factorial recursion `(c)_m = (c - 1)_m + m (c - 1)_{m - 1}` instead
of a union over them. At a challenge, at most `m` keys pull an index of the `m` indices of `B` not
yet pulled (distinct indices name distinct points, Definition 7, and a key names at most one point
with the challenge message), and such a key leaves `m - 1` of them; every other key leaves `m`.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

variable {K M D : Type} [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D]

/-- The pull factor `(c)_m / |K|^m` of Lemma 6, for a key space of size `nK`. -/
noncomputable def pullFactor (nK c m : ℕ) : ℝ≥0∞ :=
  (c.descFactorial m : ℝ≥0∞) * ((nK : ℝ≥0∞)⁻¹) ^ m

/-- No index to pull costs nothing. -/
@[simp] theorem pullFactor_zero (nK c : ℕ) : pullFactor nK c 0 = 1 := by
  simp [pullFactor]

/-- The recursion of the pull factor over one challenge. -/
theorem pullFactor_succ (nK c m : ℕ) :
    (m + 1 : ℝ≥0∞) * (nK : ℝ≥0∞)⁻¹ * pullFactor nK c m + pullFactor nK c (m + 1) =
      pullFactor nK (c + 1) (m + 1) := by
  have hnat : (c + 1).descFactorial (m + 1) =
      (m + 1) * c.descFactorial m + c.descFactorial (m + 1) := by
    rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
    rcases le_or_gt m c with hmc | hmc
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmc
      rw [show m + d - m = d by omega]
      ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hmc]
      simp
  have hdesc : ((c + 1).descFactorial (m + 1) : ℝ≥0∞) =
      (m + 1) * (c.descFactorial m : ℝ≥0∞) + (c.descFactorial (m + 1) : ℝ≥0∞) := by
    rw [hnat]
    push_cast
    ring
  simp only [pullFactor, hdesc, pow_succ]
  ring

/-! ## The challenge step -/

/-- The pulled set after a challenge with key `key` on message `msg`. -/
def pulledAfter (s : TapeState K M D) (key : K) (msg : M) : Finset ℕ :=
  match s.table (key, msg) with
  | some e => e.2.pull s.pulled
  | none => s.pulled

omit [SampleableType K] in
/-- A challenge at a drawn key keeps Definition 7 and the direct counter, and pulls according
to `pulledAfter`. -/
theorem mem_support_tapeChalAt {key : K} {msg : M} {s : TapeState K M D} (hs : OriginInv s)
    {p : (K × D) × TapeState K M D} (hp : p ∈ support (tapeChalAt key msg s)) :
    OriginInv p.2 ∧ p.2.pulled = pulledAfter s key msg ∧ p.2.nU = s.nU := by
  simp only [tapeChalAt] at hp
  cases h : s.table (key, msg) with
  | some e =>
    rw [h] at hp
    obtain rfl : p = ((key, e.1), s.chalHit (key, msg) e) := by simpa using hp
    exact ⟨hs.chalHit _ e, by simp [TapeState.chalHit, pulledAfter, h], rfl⟩
  | none =>
    rw [h] at hp
    simp only [support_map, Set.mem_image] at hp
    obtain ⟨z, -, rfl⟩ := hp
    exact ⟨hs.chalFresh _ z, by simp [TapeState.chalFresh, pulledAfter, h], rfl⟩

/-- The pre-sampled challenge oracle draws its key first. -/
theorem tapeChal_run_eq (msg : M) (s : TapeState K M D) :
    (tapeChal msg).run s = ($ᵗ K : ProbComp K) >>= fun key => tapeChalAt key msg s := rfl

/-- The keys at which a challenge on `msg` pulls an index of `B` not yet pulled. -/
noncomputable def badKeys [Fintype K] (s : TapeState K M D) (msg : M) (B : Finset ℕ) : Finset K :=
  by classical exact Finset.univ.filter fun key =>
    ∃ d b, s.table (key, msg) = some (d, .direct b) ∧ b ∈ B \ s.pulled

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- At most `|B \ pulled|` keys pull an index of `B` (Definition 7). -/
theorem card_badKeys_le [Fintype K] {s : TapeState K M D} (hs : OriginInv s) (msg : M)
    (B : Finset ℕ) : (badKeys s msg B).card ≤ (B \ s.pulled).card := by
  classical
  let f : K → ℕ := fun key => match s.table (key, msg) with
    | some (_, .direct b) => b
    | _ => 0
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro key hkey
    simp only [badKeys, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hkey
    obtain ⟨d, b, hk, hb⟩ := hkey
    simp only [f, hk]
    exact hb
  · intro key₁ h₁ key₂ h₂ hf
    simp only [badKeys, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
    obtain ⟨d₁, b₁, hk₁, -⟩ := h₁
    obtain ⟨d₂, b₂, hk₂, -⟩ := h₂
    simp only [f, hk₁, hk₂] at hf
    subst hf
    have := hs.inj _ _ d₁ d₂ b₁ hk₁ hk₂
    simpa using this

omit [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- A key outside the bad keys leaves the indices of `B` not yet pulled unchanged; a bad key
pulls exactly one of them. -/
theorem card_sdiff_pulledAfter [Fintype K] (s : TapeState K M D) (msg : M) (B : Finset ℕ)
    (key : K) :
    (B \ pulledAfter s key msg).card + (if key ∈ badKeys s msg B then 1 else 0) =
      (B \ s.pulled).card := by
  classical
  have hmem : key ∈ badKeys s msg B ↔
      ∃ d b, s.table (key, msg) = some (d, .direct b) ∧ b ∈ B \ s.pulled := by
    simp [badKeys]
  unfold pulledAfter
  rcases h : s.table (key, msg) with _ | ⟨d, b | j⟩
  · rw [ite_eq_right (by simp [hmem, h])]
    simp
  · simp only [Origin.pull]
    have hsd : B \ insert b s.pulled = (B \ s.pulled).erase b := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    rw [hsd]
    by_cases hb : b ∈ B \ s.pulled
    · rw [ite_eq_left (hmem.mpr ⟨d, b, h, hb⟩), Finset.card_erase_add_one hb]
    · rw [ite_eq_right (by rw [hmem, h]; rintro ⟨_, _, he, h'⟩; cases he; exact hb h'),
        Finset.erase_eq_of_notMem hb, add_zero]
  · rw [ite_eq_right (by simp [hmem, h])]
    simp [Origin.pull]

/-! ## Lemma 6 -/

/-- **Lemma 6** (pull probability of a fixed index set), Eq. (9). For every state satisfying
Definition 7 and an adversary making at most `c` challenge queries, the probability over the
challenge keys and the adversary's coins that every index of `B` is pulled at the end is at most
`(c)_m / |K|^m`, where `m` is the number of indices of `B` not yet pulled. The tapes are fixed
(they are part of the state). -/
theorem prob_pulled_le [Fintype K] {α : Type} (oa : OracleComp (AdvSpec K M D) α) (c : ℕ)
    (hc : oa.IsQueryBoundP (IsChalQuery K M) c) (B : Finset ℕ) (s : TapeState K M D)
    (hs : OriginInv s) :
    Pr{let z ← (simulateQ tapeImpl oa).run s}[B ⊆ z.2.pulled] ≤
      pullFactor (Fintype.card K) c (B \ s.pulled).card := by
  classical
  induction oa using OracleComp.inductionOn generalizing c s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, prEvent_pure_prop]
    split_ifs with hB
    · rw [Finset.sdiff_eq_empty_iff_subset.mpr hB]; simp
    · exact zero_le
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hc
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rcases t with n | x | msg
    · refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp => ?_
      have hp2 := mem_support_tapeImpl_unif hp
      have hc' := hc.2 p.1
      simp only [IsChalQuery, ite_false] at hc'
      rw [← hp2]
      exact ih p.1 c hc' p.2 (hp2 ▸ hs)
    · refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp => ?_
      have hc' := hc.2 p.1
      simp only [IsChalQuery, ite_false] at hc'
      rcases mem_support_tapeHash hp with ⟨e, -, rfl⟩ | ⟨hx, w, -, rfl⟩
      · exact ih _ c hc' s hs
      · exact ih _ c hc' _ (hs.hashFresh hx w)
    · have hc0 : 0 < c := by simpa [IsChalQuery] using hc.1
      have hc' := hc.2
      simp only [IsChalQuery, ite_true] at hc'
      obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hc'
      rcases hm : (B \ s.pulled).card with _ | m
      · simp
      rw [tapeImpl_chal_run, tapeChal_run_eq, bind_assoc, prEvent_bind_eq_sum_fintype]
      have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
      have hstep : ∀ key, Pr{let z ← tapeChalAt key msg s >>= fun p =>
            (simulateQ tapeImpl (k p.1)).run p.2}[B ⊆ z.2.pulled] ≤
          (if key ∈ badKeys s msg B then pullFactor (Fintype.card K) c m else 0) +
            pullFactor (Fintype.card K) c (m + 1) := by
        intro key
        refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp => ?_
        obtain ⟨hinv, hpull, -⟩ := mem_support_tapeChalAt hs hp
        refine (ih p.1 c (hc' p.1) p.2 hinv).trans ?_
        have hcard := card_sdiff_pulledAfter s msg B key
        rw [hpull]
        split_ifs at hcard ⊢ with hbad
        · rw [show (B \ pulledAfter s key msg).card = m by omega]
          exact le_self_add
        · rw [show (B \ pulledAfter s key msg).card = m + 1 by omega]
          simp
      calc ∑ key, Pr{let x ← ($ᵗ K : ProbComp K)}[x = key] *
            Pr{let z ← tapeChalAt key msg s >>= fun p =>
              (simulateQ tapeImpl (k p.1)).run p.2}[B ⊆ z.2.pulled]
          ≤ ∑ key, (Fintype.card K : ℝ≥0∞)⁻¹ *
              ((if key ∈ badKeys s msg B then pullFactor (Fintype.card K) c m else 0) +
                pullFactor (Fintype.card K) c (m + 1)) := by
            refine Finset.sum_le_sum fun key _ => ?_
            rw [SampleableType.prEvent_uniformSample_eq_singleton]
            exact mul_le_mul_right (hstep key) _
        _ = (Fintype.card K : ℝ≥0∞)⁻¹ * ((badKeys s msg B).card *
              pullFactor (Fintype.card K) c m) + pullFactor (Fintype.card K) c (m + 1) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
              Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul,
              mul_add, ← mul_assoc ((Fintype.card K : ℝ≥0∞)⁻¹) (Fintype.card K : ℝ≥0∞),
              ENNReal.inv_mul_cancel hK (by simp), one_mul]
        _ ≤ (Fintype.card K : ℝ≥0∞)⁻¹ * ((m + 1 : ℕ) * pullFactor (Fintype.card K) c m) +
              pullFactor (Fintype.card K) c (m + 1) := by
            gcongr
            exact hm ▸ card_badKeys_le hs msg B
        _ = pullFactor (Fintype.card K) (c + 1) (m + 1) := by
            rw [← pullFactor_succ]
            push_cast
            ring

/-! ## The bad event of Lemma 10 -/

/-- The keys at which a challenge on `msg` pulls some direct point. -/
noncomputable def pullKeys [Fintype K] (s : TapeState K M D) (msg : M) : Finset K :=
  by classical exact Finset.univ.filter fun key => ∃ d b, s.table (key, msg) = some (d, .direct b)

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- At most `min(nU, |K|)` keys pull a direct point: the direct points with message `msg` have
distinct keys and distinct creation indices below `nU` (Definition 7). -/
theorem card_pullKeys_le [Fintype K] {s : TapeState K M D} (hs : OriginInv s) (msg : M) :
    (pullKeys s msg).card ≤ min s.nU (Fintype.card K) := by
  classical
  refine le_min ?_ (Finset.card_le_univ _)
  let f : K → ℕ := fun key => match s.table (key, msg) with
    | some (_, .direct b) => b
    | _ => 0
  have h := Finset.card_le_card_of_injOn (s := pullKeys s msg) (t := Finset.range s.nU) f ?_ ?_
  · simpa using h
  · intro key hkey
    simp only [pullKeys, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hkey
    obtain ⟨d, b, hk⟩ := hkey
    simp only [f, hk, Finset.coe_range, Set.mem_Iio]
    exact hs.lt _ d b hk
  · intro key₁ h₁ key₂ h₂ hf
    simp only [pullKeys, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
    obtain ⟨d₁, b₁, hk₁⟩ := h₁
    obtain ⟨d₂, b₂, hk₂⟩ := h₂
    simp only [f, hk₁, hk₂] at hf
    subst hf
    simpa using hs.inj _ _ d₁ d₂ b₁ hk₁ hk₂

omit [DecidableEq K] [DecidableEq M] [SampleableType K] [SampleableType D] in
/-- A key that pulls no direct point leaves the pulled set unchanged. -/
theorem pulledAfter_of_notMem_pullKeys [Fintype K] {s : TapeState K M D} {msg : M} {key : K}
    (hkey : key ∉ pullKeys s msg) : pulledAfter s key msg = s.pulled := by
  classical
  unfold pulledAfter
  rcases h : s.table (key, msg) with _ | ⟨d, b | j⟩
  · rfl
  · exact absurd (by simp [pullKeys, h]) hkey
  · rfl

/-- **The bad event of Lemma 10.** From a state satisfying Definition 7 with nothing pulled, an
adversary making at most `h` direct and `c` challenge queries, with at most `Q` direct points
in total, pulls some direct point with probability at most `c · min(Q, |K|) / |K|`: each
challenge pulls with probability at most `min(Q, |K|) / |K|`, since the direct points with its
message have distinct keys. -/
theorem prob_pulled_nonempty_le [Fintype K] {α : Type} (oa : OracleComp (AdvSpec K M D) α)
    (h c Q : ℕ) (hh : oa.IsQueryBoundP (IsHashQuery K M) h)
    (hc : oa.IsQueryBoundP (IsChalQuery K M) c) (s : TapeState K M D) (hs : OriginInv s)
    (hp : s.pulled = ∅) (hQ : s.nU + h ≤ Q) :
    Pr{let z ← (simulateQ tapeImpl oa).run s}[z.2.pulled.Nonempty] ≤
      c * ((min Q (Fintype.card K) : ℕ) * (Fintype.card K : ℝ≥0∞)⁻¹) := by
  classical
  set ε : ℝ≥0∞ := (min Q (Fintype.card K) : ℕ) * (Fintype.card K : ℝ≥0∞)⁻¹
  induction oa using OracleComp.inductionOn generalizing h c s with
  | pure a =>
    simp [hp]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hh hc
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rcases t with n | x | msg
    · refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp' => ?_
      have hp2 := mem_support_tapeImpl_unif hp'
      have hh' := hh.2 p.1
      have hc' := hc.2 p.1
      simp only [IsHashQuery, IsChalQuery, ite_false] at hh' hc'
      rw [← hp2] at hs hp hQ
      exact ih p.1 h c hh' hc' p.2 hs hp hQ
    · have hh0 : 0 < h := by simpa [IsHashQuery] using hh.1
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp' => ?_
      have hh' := hh.2 p.1
      have hc' := hc.2 p.1
      simp only [IsHashQuery, IsChalQuery, ite_true, ite_false] at hh' hc'
      rcases mem_support_tapeHash hp' with ⟨e, -, rfl⟩ | ⟨hx, w, -, rfl⟩
      · exact ih _ (h - 1) c hh' hc' s hs hp (by omega)
      · exact ih _ (h - 1) c hh' hc' _ (hs.hashFresh hx w) hp
          (by simp only [TapeState.hashFresh]; omega)
    · have hc0 : 0 < c := by simpa [IsChalQuery] using hc.1
      have hh' := hh.2
      have hc' := hc.2
      simp only [IsHashQuery, IsChalQuery, ite_true, ite_false] at hh' hc'
      obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hc'
      rw [tapeImpl_chal_run, tapeChal_run_eq, bind_assoc, prEvent_bind_eq_sum_fintype]
      have hK : (Fintype.card K : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
      have hstep : ∀ key, Pr{let z ← tapeChalAt key msg s >>= fun p =>
            (simulateQ tapeImpl (k p.1)).run p.2}[z.2.pulled.Nonempty] ≤
          (if key ∈ pullKeys s msg then 1 else 0) + c * ε := by
        intro key
        split_ifs with hkey
        · exact (prEvent_le_one _).trans le_self_add
        · rw [zero_add]
          refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp' => ?_
          obtain ⟨hinv, hpull, hnU⟩ := mem_support_tapeChalAt hs hp'
          rw [pulledAfter_of_notMem_pullKeys hkey, hp] at hpull
          exact ih p.1 h c (hh' p.1) (hc' p.1) p.2 hinv hpull (by omega)
      calc ∑ key, Pr{let x ← ($ᵗ K : ProbComp K)}[x = key] *
            Pr{let z ← tapeChalAt key msg s >>= fun p =>
              (simulateQ tapeImpl (k p.1)).run p.2}[z.2.pulled.Nonempty]
          ≤ ∑ key, (Fintype.card K : ℝ≥0∞)⁻¹ *
              ((if key ∈ pullKeys s msg then 1 else 0) + c * ε) := by
            refine Finset.sum_le_sum fun key _ => ?_
            rw [SampleableType.prEvent_uniformSample_eq_singleton]
            exact mul_le_mul_right (hstep key) _
        _ = (Fintype.card K : ℝ≥0∞)⁻¹ * (pullKeys s msg).card + c * ε := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul, mul_add, ← mul_assoc ((Fintype.card K : ℝ≥0∞)⁻¹)
              (Fintype.card K : ℝ≥0∞), ENNReal.inv_mul_cancel hK (by simp), one_mul,
              Finset.filter_mem_eq_inter, Finset.univ_inter]
        _ ≤ ε + c * ε := by
            gcongr
            rw [mul_comm]
            show _ ≤ ((min Q (Fintype.card K) : ℕ) : ℝ≥0∞) * _
            gcongr
            exact (card_pullKeys_le hs msg).trans (min_le_min_right _ (by omega))
        _ = (c + 1 : ℕ) * ε := by
            push_cast
            ring

/-! ## The verification query pulls nothing -/

/-- The verification query is a direct query, so it pulls nothing: an event of the final pulled
set is at most as likely as the same event after the adversary's run. -/
theorem prob_withVerify_pulled_le (oa : OracleComp (AdvSpec K M D) (K × M))
    (s : TapeState K M D) (P : Finset ℕ → Prop) :
    Pr{let z ← (simulateQ tapeImpl (withVerify oa)).run s}[P z.2.pulled] ≤
      Pr{let z ← (simulateQ tapeImpl oa).run s}[P z.2.pulled] := by
  have hrun : (simulateQ tapeImpl (withVerify oa)).run s =
      ((simulateQ tapeImpl oa).run s >>= fun y =>
        (tapeHash y.1).run y.2 >>= fun p => pure ((y.1, p.1), p.2)) := by
    simp only [withVerify, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rfl
  rw [hrun]
  refine prEvent_bind_le_prEvent_of_forall_eq_zero _ _ _ _ fun y hy => ?_
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hPz => hy ?_
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  rcases mem_support_tapeHash hp with ⟨e, -, rfl⟩ | ⟨-, w, -, rfl⟩
  · exact hPz
  · exact hPz

end ShrincsSecurity.ITSR

end
