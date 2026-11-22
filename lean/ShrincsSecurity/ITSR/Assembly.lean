module

public import ShrincsSecurity.ITSR.Pull

/-!
# The probability space of the proof

`ITSR-Classical.pdf`, Section 5.5, step 1 and Eq. (10).

`presampled A` is the probability space of the proof of Lemma 9: the tapes `(U, V)` are drawn
first (`drawTapes`), then the pre-sampled game runs, with the challenge keys and the adversary's
coins as its randomness. By Lemma 2 the success probability is the winning probability of this
space (`advantage_eq_presampled_win`).

`prob_presampled_and_le` is the decoupling of Eq. (10): an event `P` of the tapes jointly with an
event `Q` of the run whose conditional probability is at most `ε` for every value of the tapes
satisfying `P` has probability at most `Pr[P] · ε`. The paper also conditions on the coins `ρ`;
the bounds of Lemma 6 and Lemma 10 used here are uniform in the tapes and already averaged over
the coins, which suffices.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace ShrincsSecurity.ITSR

variable {K M : Type} [DecidableEq K] [DecidableEq M] [SampleableType K]
variable {ι : Type} [DecidableEq ι] {k t : ℕ}

/-- The pre-sampled tapes `U = (U_1, …, U_{q+1})` and `V = (V_1, …, V_r)` of Lemma 2. -/
abbrev Tapes (ι : Type) (k t q r : ℕ) := (Fin (q + 1) → Digest ι k t) × (Fin r → Digest ι k t)

/-- The outcome of a pre-sampled run with its verification query: the output pair, its digest,
and the final state. -/
abbrev Outcome (K M ι : Type) (k t : ℕ) :=
  ((K × M) × Digest ι k t) × TapeState K M (Digest ι k t)

variable [SampleableType (Digest ι k t)]

/-- Draw the tapes `U` and `V` independently and uniformly (Lemma 2). -/
def drawTapes (q r : ℕ) : ProbComp (Tapes ι k t q r) := do
  let U ← $ᵗ (Fin (q + 1) → Digest ι k t)
  let V ← $ᵗ (Fin r → Digest ι k t)
  return (U, V)

/-- The pre-sampled run of the adversary with its verification query on tapes `uv`. -/
def tapedRun {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) (uv : Tapes ι k t q r) :
    ProbComp (Outcome K M ι k t) :=
  (simulateQ tapeImpl (withVerify A.run)).run
    (TapeState.init (K := K) (M := M) (List.ofFn uv.1) (List.ofFn uv.2))

/-- The probability space of the proof of Lemma 9: tapes, then the pre-sampled run. -/
def presampled {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    ProbComp (Tapes ι k t q r × Outcome K M ι k t) :=
  drawTapes q r >>= fun uv => (fun z => (uv, z)) <$> tapedRun A uv

/-- **Lemma 2**, on the probability space of the proof. -/
theorem advantage_eq_presampled_win {q r : ℕ} (A : Adversary K M (Digest ι k t) q r) :
    advantage A = Pr{let w ← presampled A}[Wins w.2.2.toGame w.2.1.1 w.2.1.2] := by
  rw [advantage_eq_presampled]
  simp only [presampled, drawTapes, tapedRun, bind_assoc, pure_bind, map_bind,
    Functor.map_map]

omit [DecidableEq ι] in
/-- A possible outcome of the probability space is a possible run on its tapes. -/
theorem mem_support_presampled {q r : ℕ} {A : Adversary K M (Digest ι k t) q r}
    {w : Tapes ι k t q r × Outcome K M ι k t} (hw : w ∈ support (presampled A)) :
    w.2 ∈ support (tapedRun A w.1) := by
  simp only [presampled, mem_support_bind_iff, support_map, Set.mem_image] at hw
  obtain ⟨uv, -, z, hz, rfl⟩ := hw
  exact hz

omit [DecidableEq ι] in
/-- An event of the tapes on the probability space of the proof has its probability under the
tape draw. -/
theorem prob_drawTapes {q r : ℕ}
    (P : (Fin (q + 1) → Digest ι k t) → (Fin r → Digest ι k t) → Prop) :
    Pr{let w ← drawTapes (ι := ι) (k := k) (t := t) q r}[P w.1 w.2] =
      Pr{let U ← $ᵗ (Fin (q + 1) → Digest ι k t); let V ← $ᵗ (Fin r → Digest ι k t)}[P U V] := by
  simp only [drawTapes, map_bind, bind_pure_comp, Functor.map_map]

omit [DecidableEq ι] in
/-- **The decoupling of Eq. (10).** If the run event `Q` has probability at most `ε` for every
value of the tapes satisfying `P`, then `P ∧ Q` has probability at most `Pr[P] · ε`. -/
theorem prob_presampled_and_le {q r : ℕ} (A : Adversary K M (Digest ι k t) q r)
    (P : Tapes ι k t q r → Prop) (Q : Outcome K M ι k t → Prop) {ε : ℝ≥0∞}
    (h : ∀ uv, P uv → Pr{let z ← tapedRun A uv}[Q z] ≤ ε) :
    Pr{let w ← presampled A}[P w.1 ∧ Q w.2] ≤
      Pr{let uv ← drawTapes (ι := ι) (k := k) (t := t) q r}[P uv] * ε := by
  refine prEvent_bind_le_prEvent_mul_of_forall_le _ _ P _ (fun uv huv => ?_) fun uv huv => ?_
  · simp only [Functor.map_map]
    exact (prEvent_mono _ _ _ fun _ hz => hz.2).trans (h uv huv)
  · simp only [Functor.map_map]
    exact prEvent_eq_zero_of_forall_not _ _ fun _ hz => huv hz.1

end ShrincsSecurity.ITSR

end
