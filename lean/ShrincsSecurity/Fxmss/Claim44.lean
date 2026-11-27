module

public import ShrincsSecurity.Fxmss.HybCommon

/-!
# Claim 4.4: the chain-value hybrids `F.3 → F.4` (SM-UD of `F`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.4** and the hop `F.3 → F.4` (txt lines
~3460–3580, Fig. 3, Algorithm 7, reduction `B₃,γ`).

The hybrid `H_γ` (`gameHyb γ`) reveals the blocks `σ_{j,i} = c_{m, a−m}(u_{j,i})`,
`m = min(γ, a − 1)`, for a uniform table `u`; `H_0` is `F.3` and `H_{w−2}` is `F.4`. The
reduction `B₃,γ` (SM-UD of `F ∈ Th_λ`, `L · lsf` targets) samples the setup, grinds every anchor
through the collection oracle, and queries the challenge oracle at `ADRS = chainAdrs(j, i, γ)`
for every anchor `j` and chain `i` with `a_{j,i} − 1 > γ`, writing the answers into `u`; its
second stage runs the hybrid `γ + 1` on the updated table and outputs the event `E6`.

* In the real world the answer is `F(ADRS, x)` for a fresh uniform `x`, and
  `c_{γ+1, a−γ−1}(F(chainAdrs γ, x)) = c_{γ, a−γ}(x)` (`blockVal_succ_F`); at the other
  positions the blocks of the hybrids `γ` and `γ + 1` coincide (`blockVal_succ_of_le`). So the
  real world is `H_γ` with the table resampled at the targets (`B3_real`).
* In the ideal world the answer is uniform, and the real world is `H_{γ+1}` with the table
  resampled at the targets (`B3_ideal`).

Telescoping over `γ = 0, …, w − 3` gives `claim_4_4`.

Differences from the paper: the hybrids are compared on the event `E6` only (the only event
moved from `F.3` to `F.4`, see `Theorem42.lean`), and the advantage of each hop is VCVio's
`boolDist` (the absolute advantage of Definition 4.6).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions
open ShrincsSecurity.Scheme.Structure (leafIds)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)
open Hyb

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

namespace Hyb

/-! ## The block identities -/

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- Above the hybrid index (`a − 1 > γ`): the block of hybrid `γ + 1` on `F(chainAdrs γ, x)` is
the block of hybrid `γ` on `x` (chain composition). -/
theorem blockVal_succ_F (pk : pr.PkSeed) (id : LeafId) (ch γ a : ℕ) (x : pr.Y)
    (h : γ < a - 1) :
    blockVal pr pk id ch (γ + 1) a (pr.F pk (SfAdrs.chainAdrs id ch γ).toAdrs x) =
      blockVal pr pk id ch γ a x := by
  unfold blockVal
  rw [min_eq_left (by omega : γ + 1 ≤ a - 1), min_eq_left (by omega : γ ≤ a - 1),
    show a - γ = 1 + (a - (γ + 1)) by omega,
    ← WotsC.chain_compose pr pk id ch x γ 1 (a - (γ + 1)), WotsC.chain_succ, WotsC.chain_zero]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- At or below the hybrid index (`a − 1 ≤ γ`, including `a = 0`): the blocks of the hybrids
`γ` and `γ + 1` coincide. -/
theorem blockVal_succ_of_le (pk : pr.PkSeed) (id : LeafId) (ch γ a : ℕ) (v : pr.Y)
    (h : ¬ γ < a - 1) : blockVal pr pk id ch (γ + 1) a v = blockVal pr pk id ch γ a v := by
  unfold blockVal
  rw [min_eq_right (by omega : a - 1 ≤ γ + 1), min_eq_right (by omega : a - 1 ≤ γ)]

/-! ## The reduction `B₃,γ` -/

/-- The targets of `B₃,γ`: chains with `a − 1 > γ`, queried at hash address `γ`. -/
def selUD (γ a : ℕ) : Option ℕ := if γ < a - 1 then some γ else none

/-- The second stage of `B₃,γ`: the hybrid `γ + 1` on the updated table, reporting `E6`. -/
noncomputable def dist3 (γ : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (pk : pr.PkSeed) : ProbComp Bool :=
  (fun o => decide (HybEvent Honest.E6 o)) <$>
    stageHyb pr Msg slKeygen A (betaOf pr (γ + 1) pk d.u) d pk

end Hyb

/-- **The reduction `B₃,γ` of Claim 4.4** (SM-UD of `F ∈ Th_λ`, `q₁ ≤ L · lsf` targets): the
shared first stage (`A₁`, `y`, `u`; grinding through the collection oracle; a challenge query
at `chainAdrs(j, i, γ)` for every anchor `j` and chain `i` with `a_{j,i} − 1 > γ`, answers
written into `u`), then the hybrid `γ + 1` on the updated table, outputting the event `E6`. -/
noncomputable def B3 (γ : ℕ) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Adversary (probUD pr (L * P.lsf)) :=
  udAdv pr Msg slKeygen (selUD γ) A (dist3 pr Msg slKeygen γ A.toFxmssAdversary)

namespace Hyb

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
theorem dist3_eq (γ : ℕ) {qs : ℕ} (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs)
    (d : Setup pr Msg A.State) (pk : pr.PkSeed) (u' : SkIdx P d.S → pr.Y) :
    dist3 pr Msg slKeygen γ A {d with u := u'} pk =
      evE6 pr Msg slKeygen A d pk (viewOf pr (γ + 1) pk d.ys u') :=
  betaOf_evE6 pr slKeygen (γ + 1) A {d with u := u'} pk u'

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- **Real world of `B₃,γ` is the hybrid `γ`.** -/
theorem B3_real (γ : ℕ) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment .real (B3 pr Msg slKeygen γ A) =ᵈ
      (fun o => decide (HybEvent Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen γ A.toFxmssAdversary := by
  refine (udExp_evalDistEq pr slKeygen .real (selUD γ) A _).trans ?_
  rw [gameHyb_E6]
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.trans (evalDistEq_of_eq ?_) (setupHyb_resample pr slKeygen
    A.toFxmssAdversary (fun S ys => targets pr pk (selUD γ) S ys)
    (fun d w => evE6 pr Msg slKeygen A.toFxmssAdversary d pk (viewOf pr γ pk d.ys w))
    fun _ _ _ _ _ _ _ => rfl)
  refine bind_congr fun d => ?_
  simp only [dist3_eq]
  by_cases hS : d.S.TreeValid P.hsf
  · have hl : ∀ pt ∈ targets pr pk (selUD γ) d.S d.ys, ∀ x,
        blockVal pr pk pt.1.1.1 pt.1.2.val (γ + 1)
          (relDig pr pk (digOf pr d.ys) pt.1.1.1 pt.1.2.val) (udAns pr .real pk pt.2 x) =
        blockVal pr pk pt.1.1.1 pt.1.2.val γ
          (relDig pr pk (digOf pr d.ys) pt.1.1.1 pt.1.2.val) x := by
      rintro ⟨p, t⟩ hpt x
      simp only [targets, hS, ite_true] at hpt
      obtain ⟨j, hj, rfl⟩ := (mem_targetsOf pr).1 hpt
      simp only [selUD] at hj
      split_ifs at hj with hγ
      cases hj
      exact blockVal_succ_F pr pk _ _ _ _ x hγ
    have hoff : ∀ q, q ∉ (targets pr pk (selUD γ) d.S d.ys).map Prod.fst →
        blockVal pr pk q.1.1 q.2.val (γ + 1) (relDig pr pk (digOf pr d.ys) q.1.1 q.2.val)
          (d.u q) =
        blockVal pr pk q.1.1 q.2.val γ (relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) (d.u q) := by
      intro q hq
      simp only [targets, hS, ite_true, mem_map_fst_targetsOf, selUD] at hq
      refine blockVal_succ_of_le pr pk _ _ _ _ _ fun hγ => hq ?_
      rw [relDig] at hγ
      simp [hγ]
    have hc := fillWith_couple (udAns pr .real pk) (fun _ x => x)
      (fun q y => blockVal pr pk q.1.1 q.2.val (γ + 1)
        (relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) y)
      (fun q y => blockVal pr pk q.1.1 q.2.val γ
        (relDig pr pk (digOf pr d.ys) q.1.1 q.2.val) y)
      (evE6 pr Msg slKeygen A.toFxmssAdversary d pk) _ hl d.u d.u hoff
    exact hc
  · simp only [targets, hS, ite_false, fillWith, pure_bind, evE6_invalid pr slKeygen _ d hS]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- **Ideal world of `B₃,γ` is the hybrid `γ + 1`.** -/
theorem B3_ideal (γ : ℕ) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_UD_Experiment .ideal (B3 pr Msg slKeygen γ A) =ᵈ
      (fun o => decide (HybEvent Honest.E6 o)) <$>
        gameHyb pr Msg slKeygen (γ + 1) A.toFxmssAdversary := by
  refine (udExp_evalDistEq pr slKeygen .ideal (selUD γ) A _).trans ?_
  rw [gameHyb_E6]
  refine EvalDistEq.bind_right _ fun pk => ?_
  refine EvalDistEq.trans (evalDistEq_of_eq ?_) (setupHyb_resample pr slKeygen
    A.toFxmssAdversary (fun S ys => targets pr pk (selUD γ) S ys)
    (fun d w => evE6 pr Msg slKeygen A.toFxmssAdversary d pk (viewOf pr (γ + 1) pk d.ys w))
    fun _ _ _ _ _ _ _ => rfl)
  refine bind_congr fun d => ?_
  simp only [dist3_eq]
  rfl

/-! ## Telescoping -/

theorem telescope (p d : ℕ → ℝ≥0∞) (h : ∀ γ, p γ ≤ p (γ + 1) + d γ) :
    ∀ n, p 0 ≤ p n + ∑ γ ∈ Finset.range n, d γ
  | 0 => by simp
  | n + 1 => by
    refine (telescope p d h n).trans ?_
    rw [Finset.sum_range_succ]
    calc p n + ∑ γ ∈ Finset.range n, d γ
        ≤ p (n + 1) + d n + ∑ γ ∈ Finset.range n, d γ := add_le_add (h n) le_rfl
      _ = p (n + 1) + (∑ γ ∈ Finset.range n, d γ + d n) := by ring

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- One hop: `Pr_{H_γ}[E6] ≤ Pr_{H_{γ+1}}[E6] + Adv^{sm-ud}(B₃,γ)`. -/
theorem prE6_le_succ (γ : ℕ) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen γ A.toFxmssAdversary}[HybEvent Honest.E6 o] ≤
      Pr{let o ← gameHyb pr Msg slKeygen (γ + 1) A.toFxmssAdversary}[HybEvent Honest.E6 o] +
        SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A) := by
  rw [prE6_gameHyb pr slKeygen, prE6_gameHyb pr slKeygen, SM_DT_UD_Advantage,
    MeasureTheory.Measure.boolDist,
    (B3_real pr Msg slKeygen γ A).evalDist_eq, (B3_ideal pr Msg slKeygen γ A).evalDist_eq]
  exact (ENNReal.absDiff_le_iff.1 le_rfl).1

end Hyb

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [DecidableEq pr.Digest] in
/-- **Claim 4.4** (`F.3 → F.4`, SM-UD of `F ∈ Th_λ`, `q₁ ≤ L · lsf`): moving the event `E6`
from the secret-key hybrid `H_0 = F.3` to `H_{w−2} = F.4` costs the SM-UD advantages of the
`w − 2` reductions `B₃,γ`. Parameter validity and Conjecture 3.1 are not needed for this hop
(the reductions grind with the scheme's own counter search, failures included). -/
theorem claim_4_4 (_hP : P.Valid) (_hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEvent Honest.E6 o] ≤
      Pr{let o ← gameHyb pr Msg slKeygen (P.w - 2) A.toFxmssAdversary}[HybEvent Honest.E6 o] +
        ∑ γ ∈ Finset.range (P.w - 2), SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A) :=
  telescope (fun γ => Pr{let o ← gameHyb pr Msg slKeygen γ A.toFxmssAdversary}[
      HybEvent Honest.E6 o])
    (fun γ => SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A))
    (fun γ => prE6_le_succ pr Msg slKeygen γ A) (P.w - 2)

end ShrincsSecurity.Fxmss.Rom

end
