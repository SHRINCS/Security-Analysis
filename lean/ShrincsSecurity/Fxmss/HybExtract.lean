module

public import ShrincsSecurity.Fxmss.Claim410
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Claim 4.10 in the block games

`SHRINCS-Security-Analysis.pdf`, Section 4.7: the extraction of **Claim 4.10** (txt lines
~3833–3880) applied to every execution of the block games `gameHyb γ` (`F.2`–`F.4`), giving the
union bound

`Pr[Win ∧ ¬C₁] ≤ Pr[E3] + Pr[E5] + Pr[E6] + Pr[E7] + Pr[E8] + Pr[E9]`

in every hybrid `γ` (`gameHyb_winNotC1_le`). The ingredients:

* **Consistency of the honest data** (`hon_consistent`): for a valid structure, the tree has a
  root (`Tree.root_isSome`), and under Conjecture 3.1 (`GrindComplete`) the counter search at every
  anchor succeeds (its grinding tweak `(z, i)` has `z ≤ hsf ≤ 255` and `i < 2^64`), so the block
  signature recovers the anchor value by construction (for every block source `β`).
* **The signing-phase invariant** (`RecInv`): every record carries the honest digest `y_j`, and
  every used leaf has a record. After the completion of Remark 4.6 every anchor has a record
  (`stage2_recs`), so `¬ C₁` excludes a forgery at an anchor with the honest digest.
* **The forgery verifies** under the honest `PK.sf` (`Transcript.Win`), and Claim 4.10
  (`Honest.claim_4_10`) gives one of the six events pointwise on the support.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)
open ShrincsSecurity.Scheme.Grinding (GrindComplete grindComplete_iff)

variable {P : Params} (pr : Primitives P)

section Consistent

/-- **The honest data of a block game is consistent** for a valid structure, under
Conjecture 3.1: the tree has a root, and at every anchor the counter search succeeds, so the
block signature (from any block source `β`) recovers the anchor value. -/
theorem hon_consistent (hP : P.Valid) (hgc : GrindComplete pr) {S : Structure}
    (hS : S.TreeValid P.hsf) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (β : LeafId → ℕ → ℕ → pr.Y) : (hon pr S pk dig β).Consistent where
  root := Tree.root_isSome hS
  sig id hid := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
    have h1 : P.hsf - v.depth < 256 := by have := hP.hsf_le; omega
    have h2 : v.idx < 2 ^ 64 := hS.anchor_idx_lt v hv
    have hg := (grindComplete_iff pr).1 hgc pk (⟨_, h1⟩, ⟨_, h2⟩) (dig (v.toLeafId P.hsf))
    obtain ⟨⟨d, c⟩, hdc⟩ := Option.ne_none_iff_exists'.1 hg
    have hdc' : WotsC.grind pr pk (v.toLeafId P.hsf) (dig (v.toLeafId P.hsf)) = some (d, c) :=
      hdc
    obtain ⟨hd, hT, -⟩ := (WotsC.grind_eq_some_iff pr).1 hdc'
    simp only [hon, hdc']
    rw [WotsC.pkFromSig_eq_some_iff]
    exact ⟨hd ▸ hT, by rw [hd]; rfl⟩

end Consistent

section Run

variable (Msg : Type)

/-- **The signing-phase invariant** of a block game with honest data `H`: every record carries
the honest digest `y_j`, and every used leaf has a record. -/
structure RecInv (H : Honest pr) (s : St pr Msg) : Prop where
  dig : ∀ id r, s.recs id = some r → r.digest = H.dig id
  used : ∀ id ∈ s.used, s.recs id ≠ none

theorem recInv_init (H : Honest pr) (c : (roSpec pr Msg).QueryCache) :
    RecInv pr Msg H (St.init pr Msg c) :=
  ⟨fun _ _ h => by simp [St.init] at h, fun _ h => by simp [St.init] at h⟩

variable [DecidableEq pr.Y] [SampleableType pr.Y] [DecidableEq pr.PkSeed]
  [SampleableType pr.Digest] [DecidableEq Msg]

variable {pr Msg}

/-- A query to the coins or the random oracle changes neither the used leaves nor the records. -/
theorem implHyb_run_inl {K : Keys pr} {H : Honest pr} {t : ℕ ⊕ RoIn pr Msg} {s : St pr Msg}
    {y : _} (hy : y ∈ support ((implHyb pr Msg K H (.inl t)).run s)) :
    y.2.used = s.used ∧ y.2.recs = s.recs := by
  rcases t with n | x
  · simp only [implHyb, impl, QueryImpl.add_apply_inl] at hy
    simp at hy
    obtain ⟨_, rfl⟩ := hy
    exact ⟨rfl, rfl⟩
  · simp only [implHyb, impl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hy
    simp only [roStep, StateT.run_mk] at hy
    split at hy
    · simp at hy
      subst hy
      exact ⟨rfl, rfl⟩
    · simp at hy
      obtain ⟨_, rfl⟩ := hy
      exact ⟨rfl, rfl⟩

/-- A signing query at `id`: either a fresh anchor, signed and recorded with the honest digest,
or answered `⊥` without changing the used leaves or the records. -/
theorem implHyb_run_sign {K : Keys pr} {H : Honest pr} {M : Msg} {id : LeafId} {s : St pr Msg}
    {y : _} (hy : y ∈ support ((implHyb pr Msg K H (.inr (M, id))).run s)) :
    (id ∈ leafIds P.hsf K.S ∧ id ∉ s.used ∧ ∃ R, y.2.used = s.used ++ [id] ∧
      y.2.recs = Function.update s.recs id (some ⟨M, R, H.dig id, H.sig id⟩)) ∨
    (¬ (id ∈ leafIds P.hsf K.S ∧ id ∉ s.used) ∧ y.2.used = s.used ∧ y.2.recs = s.recs) := by
  simp only [implHyb, impl, QueryImpl.add_apply_inr] at hy
  by_cases hc : id ∈ leafIds P.hsf K.S ∧ id ∉ s.used
  · simp [signStep, hc, progStep, StateT.run_bind] at hy
    obtain ⟨R, rfl⟩ := hy
    exact Or.inl ⟨hc.1, hc.2, R, rfl, rfl⟩
  · simp [signStep, hc, StateT.run_bind] at hy
    subst hy
    exact Or.inr ⟨hc, rfl, rfl⟩

/-- Every query preserves `RecInv`. -/
theorem implHyb_inv (K : Keys pr) (H : Honest pr) :
    ∀ t s, RecInv pr Msg H s →
      ∀ y ∈ support ((implHyb pr Msg K H t).run s), RecInv pr Msg H y.2 := by
  intro t s hs y hy
  rcases t with t | ⟨M, id⟩
  · obtain ⟨hu, hr⟩ := implHyb_run_inl hy
    exact ⟨by rw [hr]; exact hs.dig, by rw [hu, hr]; exact hs.used⟩
  · rcases implHyb_run_sign hy with ⟨-, -, R, hu, hr⟩ | ⟨-, hu, hr⟩
    · refine ⟨fun id' r h => ?_, fun id' h => ?_⟩
      · rw [hr] at h
        by_cases he : id' = id
        · subst he
          simp only [Function.update_self, Option.some.injEq] at h
          rw [← h]
        · rw [Function.update_of_ne he] at h
          exact hs.dig id' r h
      · rw [hr]
        by_cases he : id' = id
        · subst he
          simp
        · rw [Function.update_of_ne he]
          rw [hu, List.mem_append, List.mem_singleton] at h
          exact hs.used id' (h.resolve_right he)
    · exact ⟨by rw [hr]; exact hs.dig, by rw [hu, hr]; exact hs.used⟩

/-- Every query keeps an existing record. -/
theorem implHyb_recs (K : Keys pr) (H : Honest pr) (id : LeafId) :
    ∀ t s, (fun s : St pr Msg => s.recs id ≠ none) s →
      ∀ y ∈ support ((implHyb pr Msg K H t).run s), (fun s : St pr Msg => s.recs id ≠ none) y.2 := by
  intro t s hs y hy
  rcases t with t | ⟨M, id'⟩
  · obtain ⟨-, hr⟩ := implHyb_run_inl hy
    simpa [hr] using hs
  · rcases implHyb_run_sign hy with ⟨-, -, R, -, hr⟩ | ⟨-, -, hr⟩
    · simp only [hr]
      by_cases he : id = id'
      · subst he
        simp
      · rw [Function.update_of_ne he]
        exact hs
    · simpa [hr] using hs

/-- After the completion of Remark 4.6 over `ids`, every listed anchor has a record. -/
theorem completion_recs (K : Keys pr) (H : Honest pr) (M : Msg) :
    ∀ (ids : List LeafId) (s : St pr Msg), RecInv pr Msg H s →
      ∀ y ∈ support ((simulateQ (implHyb pr Msg K H) (completion pr Msg M ids)).run s),
        ∀ id ∈ ids, id ∈ leafIds P.hsf K.S → y.2.recs id ≠ none
  | [], _, _, _, _, id, hid, _ => by simp at hid
  | id :: ids, s, hs, y, hy, id', hid', hmem => by
    simp only [completion, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [simulateQ_spec_query] at hp
    have hinv := implHyb_inv K H _ s hs p hp
    rcases List.mem_cons.1 hid' with rfl | hid'
    · have hrec : p.2.recs id' ≠ none := by
        rcases implHyb_run_sign hp with ⟨-, -, R, -, hr⟩ | ⟨hc, hu, hr⟩
        · simp [hr]
        · rw [hr]
          exact hs.used id' (by by_contra h; exact hc ⟨hmem, h⟩)
      exact simulateQ_run_preserves_inv_of_query _ _ (implHyb_recs K H id') _ p.2 hrec y hy
    · exact completion_recs K H M ids p.2 hinv y hy id' hid' hmem

variable [Inhabited pr.Y] [SampleableType pr.PkSeed] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- **The signing phase records every anchor with its honest digest**: after `A₂`, the
verification query and the completion of Remark 4.6, every anchor of the structure has a record,
and every record carries the honest digest. -/
theorem stage2_recs {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (st : A.State) (K : Keys pr) (H : Honest pr) (s : St pr Msg) (hs : RecInv pr Msg H s) :
    ∀ r ∈ support ((simulateQ (implHyb pr Msg K H) (stage2Prog pr Msg slKeygen A st K)).run s),
      RecInv pr Msg H r.2 ∧ ∀ id ∈ leafIds P.hsf K.S, r.2.recs id ≠ none := by
  intro r hr
  refine ⟨simulateQ_run_preserves_inv_of_query _ _ (implHyb_inv K H) _ s hs r hr, ?_⟩
  simp only [stage2Prog, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨p1, hp1, p2, hp2, p3, hp3, rfl⟩ := hr
  have h1 := simulateQ_run_preserves_inv_of_query _ _ (implHyb_inv K H) _ s hs p1 hp1
  have h2 := simulateQ_run_preserves_inv_of_query _ _ (implHyb_inv K H) _ _ h1 p2 hp2
  intro id hid
  exact completion_recs K H _ _ p2.2 h2 p3 hp3 id (Finset.mem_toList.2 hid) hid

variable [Inhabited pr.Digest]

/-- **Claim 4.10 on the signing phase of a block game** (any block source `β`): every execution
in which the forger wins without the abort event of F.1 exhibits one of the events
`E3, E5, E6, E7, E8, E9`. -/
theorem stageHyb_events (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hgc : GrindComplete pr) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (β : LeafId → ℕ → ℕ → pr.Y) (d : Setup pr Msg A.State) (pk : pr.PkSeed) :
    ∀ o ∈ support (stageHyb pr Msg slKeygen A β d pk), WinNotC1 (o.map Prod.fst) →
      ((((HybEvent Honest.E3 o ∨ HybEvent Honest.E5 o) ∨ HybEvent Honest.E6 o) ∨
        HybEvent Honest.E7 o) ∨ HybEvent Honest.E8 o) ∨ HybEvent Honest.E9 o := by
  intro o ho hwin
  unfold stageHyb at ho
  split_ifs at ho with hS
  swap
  · simp only [support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact hwin.elim
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ho
  obtain ⟨pkSl, -, r, hr, rfl⟩ := ho
  have hH := hon_consistent pr hP hgc hS pk (digOf pr d.ys) β
  obtain ⟨hinv, hrec⟩ := stage2_recs slKeygen A d.st _ _ _ (recInv_init pr Msg _ d.cache) r hr
  obtain ⟨⟨Mf, idf, ⟨Rf, σo⟩, yf⟩, st⟩ := r
  simp only [Option.map_some, WinNotC1, Transcript.Win, Transcript.C1, Transcript.ofRun]
    at hwin
  obtain ⟨⟨hver, -⟩, hc1⟩ := hwin
  cases σo with
  | none => simp [verifyWith] at hver
  | some w =>
    simp only [verifyWith, decide_eq_true_eq] at hver
    have hc1' : ¬ (idf ∈ leafIds P.hsf (hon pr d.S pk (digOf pr d.ys) β).S ∧
        yf = (hon pr d.S pk (digOf pr d.ys) β).dig idf) := by
      rintro ⟨hmem, hy⟩
      obtain ⟨rec, hrec'⟩ := Option.ne_none_iff_exists'.1 (hrec _ hmem)
      exact hc1 ⟨rec, hrec', (hinv.dig _ _ hrec').trans hy.symm⟩
    have hE := Honest.claim_4_10 hP hinj hH hver hc1'
    simp only [HybEvent, Transcript.ofRun]
    rcases hE with h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨w, rfl, h⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨w, rfl, h⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨w, rfl, h⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨w, rfl, h⟩))
    · exact Or.inl (Or.inr ⟨w, rfl, h⟩)
    · exact Or.inr ⟨w, rfl, h⟩

/-- **Claim 4.10 and the union bound in every block game** (`SHRINCS-Security-Analysis.pdf`,
Section 4.7, Claim 4.10): in the hybrid `F.3_γ`, the probability that the forger wins without the
abort event of F.1 is at most the sum of the probabilities of the abort events of F.3, F.5, F.6,
F.7, F.8 and F.9 (under Conjecture 3.1). -/
theorem gameHyb_winNotC1_le (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hgc : GrindComplete pr) (γ : ℕ) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Pr{let o ← gameHyb pr Msg slKeygen γ A}[WinNotC1 (o.map Prod.fst)] ≤
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E3 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E5 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E6 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E7 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E8 o] +
      Pr{let o ← gameHyb pr Msg slKeygen γ A}[HybEvent Honest.E9 o] := by
  have hpt : ∀ o ∈ support (gameHyb pr Msg slKeygen γ A), WinNotC1 (o.map Prod.fst) →
      ((((HybEvent Honest.E3 o ∨ HybEvent Honest.E5 o) ∨ HybEvent Honest.E6 o) ∨
        HybEvent Honest.E7 o) ∨ HybEvent Honest.E8 o) ∨ HybEvent Honest.E9 o := by
    intro o ho
    simp only [gameHyb, mem_support_bind_iff] at ho
    obtain ⟨pk, -, d, -, ho⟩ := ho
    exact stageHyb_events slKeygen hP hinj hgc A _ d pk o ho
  refine (prEvent_mono_of_support _ _ _ hpt).trans ?_
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl)
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl)
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl)
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl)
  exact prEvent_or_le _ _ _

end Run

end ShrincsSecurity.Fxmss.Rom

end
