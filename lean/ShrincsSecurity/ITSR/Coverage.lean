module

public import ShrincsSecurity.ITSR.Coverage.Cover
public import ShrincsSecurity.ITSR.Coverage.Witness
public import ShrincsSecurity.ITSR.Coverage.Pull
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.ProbabilityNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Coverage probabilities and structure counts

`ITSR-Classical.pdf`, Lemma 1 (reading of `Γ_j`), Lemma 5 (search term), Lemma 7 (digest
structure) and Lemma 8 (counting). The identity `θ Γ⁺(r) = E[Δ*] / N'` of the proof of
Corollary 1 is in `ShrincsSecurity.ITSR.OnePull`.

The digest events are stated over *tapes*: `U : Fin n → Digest ι k t` (the pre-sampled answers of
the direct queries) and `V : Fin r → Digest ι k t` (the pre-sampled answers of fresh challenges),
independent and uniform, as in Lemma 2. A pull structure `(B, (W_b))` of Lemma 4 is encoded as a
witness map `β : Fin k → Option (Fin n)`: `β i = none` puts position `i` in `F` (covered by fresh
challenge digests), `β i = some b` puts `i` in `W_b`. Then `B` is the image of `β`, `m = |B|`, and
`ω = |W|` is the number of positions with `β i ≠ none` (`witnessSet`, `pulledPositions` and the
counting of Lemma 8 live in `ShrincsSecurity.ITSR.Coverage.Witness`).

All probabilities are reduced to finite averages (`prEvent_uniform_pair`) and evaluated by the
counting identities of `ShrincsSecurity.ITSR.Coverage.Cover`; Lemma 1 there shows that the
conditional coverage count of a digest does not depend on the digest.
-/

@[expose] public section

open OracleComp
open scoped ENNReal

namespace ShrincsSecurity.ITSR

variable {ι : Type} [Fintype ι] [DecidableEq ι] [SampleableType ι] {k t : ℕ} [NeZero t]

/-- The digest event `(ii) ∧ (iii) ∧ (iv)` of Lemma 4 for output entry `a` and witness map `β`:
every pulled witness `U b` lies in the instance of `U a` and agrees with it at the positions it
certifies, and every other position of `U a` is covered by the fresh digests `V`. -/
def DigestEvent {n r : ℕ} (a : Fin n) (β : Fin k → Option (Fin n))
    (U : Fin n → Digest ι k t) (V : Fin r → Digest ι k t) : Prop :=
  (∀ i b, β i = some b → (U b).1 = (U a).1 ∧ (U b).2 i = (U a).2 i) ∧
    ∀ i, β i = none → (U a).2 i ∈ posSet (Finset.univ.image V) (U a).1 i

omit [DecidableEq ι] [SampleableType ι] [NeZero t] in
/-- The number of digests, `N' = |ι| t^k`. -/
theorem card_digest : (Fintype.card (Digest ι k t) : ℝ) = Fintype.card ι * (t : ℝ) ^ k := by
  simp [Digest, Fintype.card_prod]

omit [DecidableEq ι] in
theorem card_digest_ne_zero : (Fintype.card ι : ℝ) * (t : ℝ) ^ k ≠ 0 := by
  have h1 : 0 < Fintype.card ι := Fintype.card_pos
  have h2 : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  positivity

/-- Two independent uniform samples satisfy an event with the probability given by the finite
average of its indicator. -/
theorem prEvent_uniform_pair {A B : Type} [SampleableType A] [SampleableType B] [Fintype A]
    [Fintype B] (p : A → B → Prop) [∀ a b, Decidable (p a b)] :
    Pr{let a ← $ᵗ A; let b ← $ᵗ B}[p a b] =
      ENNReal.ofReal ((∑ a, ∑ b, if p a b then (1 : ℝ) else 0) /
        ((Fintype.card A : ℝ) * Fintype.card B)) := by
  have h : Pr{let a ← $ᵗ A; let b ← $ᵗ B}[p a b] = Pr{let x ← $ᵗ (A × B)}[p x.1 x.2] := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp
  rw [h, SampleableType.prEvent_uniformSample_eq_ofReal, Finset.card_filter, Fintype.card_prod]
  push_cast
  rw [Fintype.sum_prod_type]

/-- **Lemma 1** (reading of `Γ_j`): for a uniform digest `u` and `r` independent uniform digests
`V`, the probability that the positions `F` of `u` are covered is `Γ_{|F|}(r)`. -/
theorem prob_covered_positions (r : ℕ) (F : Finset (Fin k)) :
    Pr{let u ← $ᵗ (Digest ι k t); let V ← $ᵗ (Fin r → Digest ι k t)}[
      ∀ i ∈ F, u.2 i ∈ posSet (Finset.univ.image V) u.1 i] =
      ENNReal.ofReal (gamma (theta ι) t r F.card) := by
  rw [prEvent_uniform_pair]
  simp_rw [sum_cover]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, card_digest]
  congr 1
  have := card_digest_ne_zero (ι := ι) (k := k) (t := t)
  have ht : (t : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne t)
  field_simp

/-- **Lemma 5** (search term): a fixed tape entry is covered by the fresh digests with probability
exactly `Γ_k(r)`. -/
theorem prob_covered_tape {n r : ℕ} (a : Fin n) :
    Pr{let U ← $ᵗ (Fin n → Digest ι k t); let V ← $ᵗ (Fin r → Digest ι k t)}[
      Covered (Finset.univ.image V) (U a)] =
      ENNReal.ofReal (gamma (theta ι) t r k) := by
  rw [prEvent_uniform_pair]
  have hc : ∀ U : Fin n → Digest ι k t, ∑ V : Fin r → Digest ι k t,
      (if Covered (Finset.univ.image V) (U a) then (1 : ℝ) else 0) =
        ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r * gamma (theta ι) t r k := by
    intro U
    have := sum_cover r (U a) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← this]
    refine Finset.sum_congr rfl fun V _ => ?_
    split_ifs <;> simp_all [Covered]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, card_digest]
  congr 1
  have := card_digest_ne_zero (ι := ι) (k := k) (t := t)
  field_simp

/-- **Lemma 7** (digest structure): for `a ∉ B`, the digest event has probability
`θ^m t^{-ω} Γ_{k-ω}(r)`. -/
theorem prob_digestEvent {n r : ℕ} (a : Fin n) (β : Fin k → Option (Fin n))
    (ha : a ∉ witnessSet β) :
    Pr{let U ← $ᵗ (Fin n → Digest ι k t); let V ← $ᵗ (Fin r → Digest ι k t)}[
      DigestEvent a β U V] =
      ENNReal.ofReal (theta ι ^ (witnessSet β).card * ((t : ℝ)⁻¹) ^ (pulledPositions β).card *
        gamma (theta ι) t r (k - (pulledPositions β).card)) := by
  classical
  rw [prEvent_uniform_pair]
  set F : Finset (Fin k) := Finset.univ.filter fun i => β i = none with hF_def
  have hF : F.card = k - (pulledPositions β).card := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin k => (β i).isSome)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have hneg : (Finset.univ.filter fun i : Fin k => ¬ (β i).isSome) = F := by
      ext i
      simp [hF_def]
    rw [hneg] at h
    simp only [pulledPositions]
    omega
  set P : (Fin n → Digest ι k t) → Prop :=
    fun U => ∀ i b, β i = some b → (U b).1 = (U a).1 ∧ (U b).2 i = (U a).2 i with hP_def
  have hV : ∀ U : Fin n → Digest ι k t,
      ∑ V : Fin r → Digest ι k t, (if DigestEvent a β U V then (1 : ℝ) else 0) =
        (if P U then (1 : ℝ) else 0) *
          (((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ r *
            gamma (theta ι) t r (k - (pulledPositions β).card)) := by
    intro U
    rw [← hF, ← sum_cover r (U a) F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    have hiff : DigestEvent a β U V ↔
        P U ∧ ∀ i ∈ F, (U a).2 i ∈ posSet (Finset.univ.image V) (U a).1 i := by
      simp [DigestEvent, hP_def, hF_def]
    by_cases h : DigestEvent a β U V
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h).1, ite_eq_left (hiff.mp h).2, one_mul]
    · rw [ite_eq_right h]
      by_cases hP : P U
      · rw [ite_eq_left hP, ite_eq_right (fun hQ => h (hiff.mpr ⟨hP, hQ⟩)), mul_zero]
      · rw [ite_eq_right hP, zero_mul]
  rw [Finset.sum_congr rfl fun U _ => hV U, ← Finset.sum_mul]
  have hPU : ∑ U : Fin n → Digest ι k t, (if P U then (1 : ℝ) else 0) =
      ((Fintype.card ι : ℝ) * (t : ℝ) ^ k) ^ n * theta ι ^ (witnessSet β).card *
        ((t : ℝ)⁻¹) ^ (pulledPositions β).card := by
    rw [← sum_pulled a β ha]
  rw [hPU, Fintype.card_fun, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_pow, card_digest]
  congr 1
  have := card_digest_ne_zero (ι := ι) (k := k) (t := t)
  field_simp

/-- **Lemma 8** (counting): the witness maps into `Fin n` with `|B| = m` and `|W| = ω` number
`C(k, ω) · C(n, m) · m! · St(ω, m)`; summed against any weight depending on `(m, ω)` only. -/
theorem sum_witnessMaps (n : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ β : Fin k → Option (Fin n), f (witnessSet β).card (pulledPositions β).card =
      ∑ m ∈ Finset.range (k + 1), ∑ ω ∈ Finset.range (k + 1),
        (k.choose ω : ℝ) * (n.choose m : ℝ) * (m.factorial : ℝ) * (Nat.stirlingSecond ω m : ℝ) *
          f m ω :=
  sum_witnessMaps_eq n f

end ShrincsSecurity.ITSR

end
