module

public import ShrincsSecurity.Undetectability.Marginal.Basic
public import VCVio.Quantum.Oracle.Comb
public import QuantumFoundations.Oracle.Unitary

/-!
# Lemma 1 for quantum combs: output probabilities are linear in the `2q`-point marginals

Undetectability paper (`notes/txt/Undetectability.txt`), **Lemma 1** (lines 187–230, after
Zhandry and Beals et al.): for a `q`-query algorithm with oracle access to `H : X → Y` and an
outcome `z`, `Pr[A^{|H⟩} outputs z] = ∑_{x,r} c_{x,r} 1[H(x_i) = r_i ∀ i ∈ [2q]]` with real
coefficients that depend only on the algorithm and `z`.

## Program model

The algorithm is a VCVio `Quantum.QuantumComb` on the register `(X × Y) × E`: an initial substate,
`q + 1` steps and a final instrument, with the standard oracle `|x, y⟩ ↦ |x, y + H x⟩`
(`Quantum.oracleUnitary`, which needs `[AddCommGroup Y]`) applied to the designated query register
`X × Y` and the identity on the workspace `E` in each of the `q` query slots (`queryStep`). This is
the fixed-query circuit form of Section 2.2 of the paper, with two generalisations: the steps are
arbitrary trace-nonincreasing completely positive instruments (unitaries, intermediate
measurements, discarding), and the initial state may be mixed (classical coins). Adaptive
`Quantum.QuantumComp` programs whose number of calls depends on intermediate outcomes are not
covered; the paper reduces them to this form by deferred measurement and padding (line 158), which
VCVio does not provide (`Quantum.QuantumComb.toComp` embeds combs into programs, not conversely).

## Proof

The paper expands amplitudes of a pure state. With mixed states and instruments we expand the
density matrix instead, which gives the same count: after a query, the entry of the state at
`((x, y), e), ((x', y'), e')` is the entry of the previous state at
`((x, y - H x), e), ((x', y' - H x'), e')`, that is
`∑_{r, r'} 1[H x = r] 1[H x' = r'] ρ((x, y - r), e)((x', y' - r'), e')`: two more indicator
factors (`isMarginalPoly_query`). Steps are fixed linear maps and do not change the count
(`IsMarginalPoly.map`), and the outcome probability is the real trace of a fixed linear map of the
last state. After `q` queries the probability uses exactly `2q` points, so no padding is needed
(`IsMarginalPoly.mono` pads for algorithms with fewer queries).

## Main results

* `isMarginalPoly_post_interleave`: the state after `s 0, Q_H, s 1, …, Q_H, s q` uses `t + 2q`
  points if the input state uses `t`.
* `QuantumComb.isMarginalLinear_outcome`: **Lemma 1** for combs.
* `TwoStageAdversary`: two-stage comb adversaries (Section 2.3: both stages query the oracle,
  sharing their register), and `TwoStageAdversary.isMarginalLinear_outProb`, Lemma 1 for them with
  `q = q₁ + q₂`.
-/

@[expose] public section

namespace ShrincsSecurity.Undetectability

open Finset Quantum MeasureTheory

/-! ### Matrices -/

section matrix

variable {X Y : Type*} {n : Type*} [Fintype n] {t : ℕ}

/-- The entry `(i, j)` of a matrix, as a real-linear map. -/
def entryLm (i j : n) : Matrix n n ℂ →ₗ[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The matrix with one nonzero entry at `(i, j)`, as a real-linear map. -/
noncomputable def singleLm [DecidableEq n] (i j : n) : ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun z := Matrix.single i j z
  map_add' a b := Matrix.single_add i j a b
  map_smul' r a := (Matrix.smul_single r i j a).symm

/-- A matrix-valued function uses `t` points if each of its entries does. -/
theorem IsMarginalPoly.of_entries [DecidableEq n] {F : (X → Y) → Matrix n n ℂ}
    (h : ∀ i j, IsMarginalPoly (fun H => F H i j) t) : IsMarginalPoly F t :=
  (IsMarginalPoly.sum univ fun i _ => IsMarginalPoly.sum univ fun j _ =>
    (h i j).map (singleLm i j)).congr fun H => (Matrix.matrix_eq_sum_single (F H)).symm

/-- The real part of the trace, as a real-linear map. -/
noncomputable def reTraceLm : Matrix n n ℂ →ₗ[ℝ] ℝ :=
  Complex.reLm ∘ₗ (Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ

@[simp] lemma reTraceLm_apply (A : Matrix n n ℂ) : reTraceLm A = A.trace.re := rfl

end matrix

variable {X Y E : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E]

/-! ### One query -/

/-- One query to `H` in a comb on `(X × Y) × E`: the standard oracle `|x, y⟩ ↦ |x, y + H x⟩` on
the query register `X × Y`, the identity on the workspace `E`. -/
noncomputable abbrev queryStep (E : Type*) [Fintype E] (H : X → Y) :
    SubInstrument ((X × Y) × E) ((X × Y) × E) Unit :=
  (oracleQuery H).frame E

lemma queryStep_branch (H : X → Y) :
    (queryStep E H).branch () = (MatrixMap.conj (oracleUnitary H)).amplify E := by
  rw [DSubInstrument.branch_frame_apply, branch_oracleQuery_apply]

/-- The entry of the state after a query: the entry of the state before it at the response
registers shifted by `-H`. -/
lemma queryStep_branch_apply (H : X → Y) (ρ : Matrix ((X × Y) × E) ((X × Y) × E) ℂ)
    (m m' : (X × Y) × E) :
    (queryStep E H).branch () ρ m m' =
      ρ ((m.1.1, m.1.2 - H m.1.1), m.2) ((m'.1.1, m'.1.2 - H m'.1.1), m'.2) := by
  rw [queryStep_branch, MatrixMap.amplify_apply, conj_oracleUnitary_apply]
  rfl

/-- **One query adds two points** (proof of Lemma 1, lines 205–222, in density-matrix form). -/
theorem isMarginalPoly_query {t : ℕ} {ρ : (X → Y) → Matrix ((X × Y) × E) ((X × Y) × E) ℂ}
    (hρ : IsMarginalPoly ρ t) :
    IsMarginalPoly (fun H => (queryStep E H).branch () (ρ H)) (t + 2) := by
  classical
  refine IsMarginalPoly.of_entries fun m m' => ?_
  have hterm : ∀ r r' : Y, IsMarginalPoly (fun H =>
      (if H m.1.1 = r then (1 : ℝ) else 0) • (if H m'.1.1 = r' then (1 : ℝ) else 0) •
        ρ H ((m.1.1, m.1.2 - r), m.2) ((m'.1.1, m'.1.2 - r'), m'.2)) (t + 2) := fun r r' =>
    ((IsMarginalPoly.indicator m.1.1 r).smul ((IsMarginalPoly.indicator m'.1.1 r').smul
      (hρ.map (entryLm ((m.1.1, m.1.2 - r), m.2) ((m'.1.1, m'.1.2 - r'), m'.2))))).cast
      (by omega)
  refine (IsMarginalPoly.sum univ fun r _ => IsMarginalPoly.sum univ fun r' _ => hterm r r').congr
    fun H => ?_
  rw [queryStep_branch_apply, Fintype.sum_eq_single (H m.1.1) fun r hr => by
      simp [Ne.symm hr],
    Fintype.sum_eq_single (H m'.1.1) fun r' hr' => by simp [Ne.symm hr']]
  simp

/-! ### Interleaving steps with queries -/

/-- The state after `s 0, Q_H, s 1, …, Q_H, s q` uses `t + 2q` points if the input state uses
`t`. -/
theorem isMarginalPoly_post_interleave {t : ℕ} :
    ∀ (q : ℕ) (s : Fin (q + 1) → SubInstrument ((X × Y) × E) ((X × Y) × E) Unit)
      {ρ : (X → Y) → SubState ((X × Y) × E)}, IsMarginalPoly (fun H => (ρ H).matrix) t →
      IsMarginalPoly (fun H => ((interleave (queryStep E H) q s).post (ρ H) ()).matrix)
        (t + 2 * q)
  | 0, s, ρ, hρ => by
    simpa using hρ.map (((s 0).branch ()).restrictScalars ℝ)
  | q + 1, s, ρ, hρ => by
    have ih := isMarginalPoly_post_interleave q (Fin.init s) hρ
    refine ((isMarginalPoly_query ih).map
      (((s (Fin.last _)).branch ()).restrictScalars ℝ)).cast (by ring) |>.congr fun H => ?_
    rw [interleave_succ, DSubInstrument.post_bind_unit, DSubInstrument.post_bind_unit]
    rfl

omit [DecidableEq X] [DecidableEq Y] [AddCommGroup Y] in
/-- The probability of outcome `z` of an instrument `p` on a state that uses `t` points uses `t`
points. -/
theorem isMarginalPoly_outcome {t : ℕ} {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : SubInstrument ((X × Y) × E) ((X × Y) × E) α) (z : α)
    {ρ : (X → Y) → SubState ((X × Y) × E)} (hρ : IsMarginalPoly (fun H => (ρ H).matrix) t) :
    IsMarginalPoly (fun H => (p.outcomeMeasure (ρ H) {z}).toReal) t := by
  refine (hρ.map (reTraceLm ∘ₗ (p.branch z).restrictScalars ℝ)).congr fun H => ?_
  rw [DSubInstrument.outcomeMeasure_apply_singleton,
    ENNReal.toReal_ofReal (p.trace_re_branch_apply_nonneg z (ρ H).posSemidef)]
  rfl

/-! ### Lemma 1 for combs -/

/-- **Lemma 1** (Undetectability, lines 187–195) for a `q`-query comb on the register
`(X × Y) × E` with the standard oracle of `H : X → Y`: the probability that the comb outputs `z`
is a fixed real combination of the `2q`-point marginal indicators of `H`. -/
theorem QuantumComb.isMarginalLinear_outcome {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {q : ℕ} (c : QuantumComb ((X × Y) × E) α q) (z : α) :
    IsMarginalLinear (fun H : X → Y => ((c.run (queryStep E H)).outcomeMeasure c.init {z}).toReal)
      (2 * q) := by
  rw [← isMarginalPoly_iff_isMarginalLinear]
  have h := isMarginalPoly_post_interleave (E := E) q c.step (IsMarginalPoly.const c.init.matrix)
  rw [zero_add] at h
  refine (isMarginalPoly_outcome c.final z h).congr fun H => ?_
  rw [QuantumComb.outcomeMeasure_run, ← QuantumComb.post_body]
  rfl

/-! ### Two-stage adversaries -/

/-- A two-stage quantum adversary in comb form (Section 2.3): both stages make queries to the
oracle `H : X → Y` on the shared register `(X × Y) × E`; stage one makes `q₁` queries and its steps
may depend on classical data `ch : Ch`, stage two makes `q₂` queries and its steps and final
measurement may depend on `ch` and on the classical input `P : Pp` it receives. -/
structure TwoStageAdversary (X Y E Ch Pp α : Type*) [Fintype X] [Fintype Y] [Fintype E]
    (q₁ q₂ : ℕ) where
  /-- The initial substate (classical coins are part of it). -/
  init : SubState ((X × Y) × E)
  /-- The steps of stage one. -/
  stage₁ : Ch → Fin (q₁ + 1) → SubInstrument ((X × Y) × E) ((X × Y) × E) Unit
  /-- The steps of stage two. -/
  stage₂ : Ch → Pp → Fin (q₂ + 1) → SubInstrument ((X × Y) × E) ((X × Y) × E) Unit
  /-- The final measurement of stage two. -/
  final : Ch → Pp → SubInstrument ((X × Y) × E) ((X × Y) × E) α

namespace TwoStageAdversary

variable {Ch Pp α : Type*} {q₁ q₂ : ℕ} (A : TwoStageAdversary X Y E Ch Pp α q₁ q₂)

/-- The run against `H`: stage one (`q₁` queries), stage two (`q₂` queries), final measurement. -/
noncomputable def run (ch : Ch) (P : Pp) (H : X → Y) : SubInstrument ((X × Y) × E) ((X × Y) × E) α :=
  ((interleave (queryStep E H) q₁ (A.stage₁ ch)).bind fun _ =>
    interleave (queryStep E H) q₂ (A.stage₂ ch P)).bind fun _ => A.final ch P

/-- The probability that the adversary outputs `o`. -/
noncomputable def outProb [MeasurableSpace α] (ch : Ch) (P : Pp) (H : X → Y) (o : α) : ℝ :=
  ((A.run ch P H).outcomeMeasure A.init {o}).toReal

/-- The state before the final measurement. -/
noncomputable def preFinal (ch : Ch) (P : Pp) (H : X → Y) : SubState ((X × Y) × E) :=
  (interleave (queryStep E H) q₂ (A.stage₂ ch P)).post
    ((interleave (queryStep E H) q₁ (A.stage₁ ch)).post A.init ()) ()

lemma outProb_eq [MeasurableSpace α] [MeasurableSingletonClass α] (ch : Ch) (P : Pp)
    (H : X → Y) (o : α) :
    A.outProb ch P H o = ((A.final ch P).branch o (A.preFinal ch P H).matrix).trace.re := by
  rw [outProb, run, DSubInstrument.outcomeMeasure_bind_unit, DSubInstrument.post_bind_unit,
    DSubInstrument.outcomeMeasure_apply_singleton,
    ENNReal.toReal_ofReal (DSubInstrument.trace_re_branch_apply_nonneg _ _ (SubState.posSemidef _))]
  rfl

lemma outProb_nonneg [MeasurableSpace α] (ch : Ch) (P : Pp) (H : X → Y) (o : α) :
    0 ≤ A.outProb ch P H o :=
  ENNReal.toReal_nonneg

/-- The outcome probabilities sum to at most one. -/
lemma sum_outProb_le_one [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] (ch : Ch)
    (P : Pp) (H : X → Y) : ∑ o, A.outProb ch P H o ≤ 1 := by
  simp only [outProb_eq]
  have h := (A.final ch P).tsum_trace_re_le (A.preFinal ch P H).posSemidef
  rw [tsum_fintype] at h
  exact h.trans (A.preFinal ch P H).trace_re_le_one

lemma outProb_le_one [MeasurableSpace α] [MeasurableSingletonClass α] (ch : Ch) (P : Pp)
    (H : X → Y) (o : α) : A.outProb ch P H o ≤ 1 := by
  rw [outProb_eq]
  exact ((A.final ch P).trace_re_branch_apply_le o (A.preFinal ch P H).posSemidef).trans
    (A.preFinal ch P H).trace_re_le_one

/-- **Lemma 1** for two-stage adversaries with `q₁ + q₂` queries in total, for fixed classical
data `ch`, `P`: the probability of each outcome is linear in the `2(q₁ + q₂)`-point marginals. -/
theorem isMarginalPoly_outProb [MeasurableSpace α] [MeasurableSingletonClass α] (ch : Ch) (P : Pp)
    (o : α) : IsMarginalPoly (fun H => A.outProb ch P H o) (2 * (q₁ + q₂)) := by
  have h₁ := isMarginalPoly_post_interleave (E := E) q₁ (A.stage₁ ch)
    (IsMarginalPoly.const A.init.matrix)
  have h₂ := isMarginalPoly_post_interleave (E := E) q₂ (A.stage₂ ch P) h₁
  refine ((isMarginalPoly_outcome (A.final ch P) o h₂).cast (by ring)).congr fun H => ?_
  rw [outProb, run, DSubInstrument.outcomeMeasure_bind_unit, DSubInstrument.post_bind_unit]

/-- **Lemma 1** for two-stage adversaries, in the form `IsMarginalLinear`. -/
theorem isMarginalLinear_outProb [MeasurableSpace α] [MeasurableSingletonClass α] (ch : Ch)
    (P : Pp) (o : α) : IsMarginalLinear (fun H => A.outProb ch P H o) (2 * (q₁ + q₂)) :=
  isMarginalPoly_iff_isMarginalLinear.mp (A.isMarginalPoly_outProb ch P o)

end TwoStageAdversary

end ShrincsSecurity.Undetectability
