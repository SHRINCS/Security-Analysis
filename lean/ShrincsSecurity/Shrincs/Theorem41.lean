module

public import ShrincsSecurity.Shrincs.Bridge0
public import ShrincsSecurity.Shrincs.Claim411
public import ShrincsSecurity.Shrincs.Claim412
public import ShrincsSecurity.Shrincs.Bridge2
public import ShrincsSecurity.Shrincs.Claim413
public import ShrincsSecurity.Shrincs.Claim414
public import ShrincsSecurity.Shrincs.Claim415
public import ShrincsSecurity.Shrincs.Claim416
public import ShrincsSecurity.Shrincs.PrfMsgBound
public import ShrincsSecurity.Shrincs.PrfBound

/-!
# Theorem 4.1: EU-CMA security of SHRINCS

`SHRINCS-Security-Analysis.pdf`, **Theorem 4.1** (txt lines 2874–2948) and its proof, Section 4.8
(txt lines 3926–4400), in the classical setting: `H_msg^sf` is a random oracle (the runtime
`ProbCompRuntime.rom`), every other named function is a fixed function of the primitive bundle
(the reading of Assumption 4.1 of the formalisation of Theorem 4.2, see `Model.lean`), and
Conjecture 3.1 (`GrindComplete`) is a hypothesis.

## Claim 4.16 (stateless route): proved unconditionally in `Claim416.lean`

In the paper, Claim 4.16 applies the reductions of [HK22] (Theorem 4.3, quoted) to the extended
games, asserting that the stateless-branch forgeries of `GAME.5` (`gameHybS`) have probability at
most the ten post-PRF summands of Theorem 4.3.

* `claim_4_16` (`Claim416.lean`) **proves Claim 4.16 directly** under
  `hinj : Function.Injective pr.yToBytes` and `henc : enc.Injective`, discharging `StatelessBound`
  with all ten explicit [HK22] post-PRF terms (ITSR for `H_msg^sl`, `w − 2` WOTS SM-UD terms,
  WOTS SM-PRE, WOTS `F` SM-TCR, XMSS `H` SM-TCR, `Th_k` SM-TCR, `Th_{l_sl}` SM-TCR, FORS `H`
  SM-TCR, `3 ·` FORS `F` SM-TCR, and FORS `F` SM-DSPR), via Stage-1 `O_coll` precomputation of the
  stateful FXMSS subtree (`SfPrecomp`).
* `theorem_4_1_full`, `theorem_4_1_full_of_ud_le`, and `corollary_4_1_full` plug
  `claim_4_16` into Theorem 4.1, giving the **complete 21-term SHRINCS EU-CMA bound with
  no `StatelessBound` hypothesis** (only `hinj`, `henc`, and Conjecture 3.1 `hgc`).
* The abstract `StatelessBound` versions (`theorem_4_1`, `theorem_4_1_of_ud_le`, `corollary_4_1`)
  are preserved for backwards compatibility.

## Statement

`theorem_4_1`: for every forger `A` (Definition 4.15; `q_s` signing queries, `q_{h,1} + q_{h,2}`
queries to `H_msg^sf`, structures with at most `L` anchors) with `StatelessBound A ε_sl`,

`Succ^{SHRINCS-EU-CMA}(A) ≤ Adv^{prf}_{PRF, q₁}(B_prf) + Adv^{prf}_{PRF_msg, q_s}(B_prfmsg)
  + Adv^{SM-rTCR,1}(B₀(A_F)) + Adv^{DI-Repro}(B₁⁺)
  + Succ^{S-TCR(Prop)}(B₂⁺) + Σ_{γ < w−2} Adv^{sm-ud}(B₃,γ⁺) + Succ^{sm-tcr}(B₄⁺)
  + Succ^{sm-pre}(B₅⁺) + Succ^{sm-tcr}(B₆⁺) + Succ^{sm-tcr}(B₇⁺)
  + Succ^{sm-tcr-excl}(B₈⁺) + ε_sl`.

`A_F` (`AF`) is the FXMSS forger that runs `A` and simulates the stateless path with uniform
secrets and randomizers; `B₀(A_F)` is the augmented `B₀`, `B₁⁺` (`B1S`) is the augmented `B₁`
whose output also covers the stateless branch (one shared reprogramming term), and `B₂⁺, …, B₈⁺`
(`B2S, …, B8S`, `Claim415.lean`) are the **Stage-1-precomputing augmented collection reductions**
of Claim 4.15 (each precomputing `PK.sl` and the full virtual SLH-DSA hypertree via `O_coll` in
Stage 1 using stateless-vs-stateful tweak disjointness, with zero stateless `Th_λ` evaluations in
Stage 2).

## The proof (telescoping, Claims 4.11–4.16)

`Succ = Succ₀` (`succ_eq_game0`) `≤ Succ₁ + Adv^{prf}` (Claim 4.11) `≤ Succ₂ + Adv^{prf}_{msg}`
(Claim 4.12); `Succ₂ = Pr[W_sf ∨ W_sl]` in the augmented game (`game2_eq_gameS`); a winning forgery
either triggers the abort of `GAME.3` (Claim 4.13) or wins `GAME.3`, which is at most `GAME.4`
plus `B₁⁺` (Claim 4.14); in `GAME.4` the stateful-branch wins are bounded by the seven collection
terms (Claim 4.15) and the stateless-branch wins by `ε_sl` (Claim 4.16, `StatelessBound`).
`GAME.6` cannot be won: every forgery verifies via exactly one branch (the constructor of the
signature), so `W_sf ∨ W_sl` is the whole success event.

## `ε_ds`

Theorem 4.1 adds `ε_ds ≤ 2^{-n} + 10 · 2^{-2n}`, the probability of the domain-separation events of
Lemma 4.3, "charged once, outside the sequence of games" (txt line 3947): it measures the gap
between the SHA-256 instantiation and the model of Assumption 4.1. In the formal model the named
functions are distinct objects (distinct fields of `Primitives` and a separate random oracle), so
no hop meets these events and the bound holds **without** `ε_ds`; adding any `ε_ds ≥ 0` to the
right-hand side is immediate.

## Deviations from the paper

* **Time and budgets** are replaced by explicit reductions, as in Theorem 4.2. Both PRF terms
  are advantages of adversaries of Definition 4.3 with the paper's budgets:
  `B_prf` (`BprfAdv`, `PrfBound.lean`) caches its oracle's answers and makes at most
  `q₁ = L · lsf + slSecretCount` pairwise distinct queries, `slSecretCount = wotsInstanceCount ·
  len + 2^h · k · 2^a` the number of secret elements of the hypertree; `B_prfmsg` (`BprfmsgAdv`,
  `PrfMsgBound.lean`) makes at most `q_s` (the completion of Remark 4.6 is not part of
  `GAME.0`–`GAME.2`, so `q_s` and not `q_s^{sl} + L`).
* **Collection budgets** `q̃_{λ,i}`, `q_λ` are not tracked (the collection games of VCVio carry
  none), as in Theorem 4.2; the augmented collection reductions `B2S … B8S` precompute the
  stateless virtual hypertree in Stage 1 via `O_coll` (`VirtualTree.lean`) and make zero stateless
  `Th_λ` evaluations in Stage 2 (`AFTable`), while stateful signing still runs in Stage 2.
* **Finite messages.** The message space is a finite type `Msg` encoding the pairs `(ctx, M)`
  (`MsgEnc`), so that the random oracle's input space is finite (Definition C.2).
* **`PK.sl` in the FXMSS games** is the constant `slKeygenS`; `A_F` computes the genuine `PK.sl`
  from its own uniform stateless secrets.
* **`H_msg^sl`** is a fixed public function (Model.lean).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys implG)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

/-- **Claim 4.16, the quoted stateless route** (the single assumption of `theorem_4_1` beyond
Conjecture 3.1): in `GAME.5` (for stateless-branch forgeries, `GAME.4`, `gameHybS`) the
probability that `A` outputs a forgery that is fresh for both paths and verifies via the stateless
branch is at most `ε_sl`, the ten summands of Theorem 4.3 [HK22] other than its two PRF terms. -/
def StatelessBound {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (εsl : ℝ≥0∞) : Prop :=
  Pr{let o ← gameHybS pr Msg enc A}[HEv Wsl o] ≤ εsl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] in
/-- A winning forgery of `GAME.2` either triggers the abort of `GAME.3` or wins `GAME.3`. -/
theorem prEvent_winS_le {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let o ← gameS pr Msg enc A (implG pr (BMsg pr Msg))}[OEv WinS o] ≤
      Pr{let o ← gameS pr Msg enc A (implG pr (BMsg pr Msg))}[OEv (fun p => Wsf p ∧ p.1.C1) o] +
      Pr{let o ← gameS pr Msg enc A (implG pr (BMsg pr Msg))}[OEv WinNotC1S o] := by
  refine (prEvent_mono _ _ (fun o => OEv (fun p => Wsf p ∧ p.1.C1) o ∨ OEv WinNotC1S o) ?_).trans
    (prEvent_or_le _ _ _)
  rintro (_ | p) h
  · exact h.elim
  · rcases h with h | h
    · by_cases hc : p.1.C1
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr (Or.inl ⟨h, hc⟩)
    · exact Or.inr (Or.inr h)

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- In `GAME.4` the success splits into the stateful- and the stateless-branch wins. -/
theorem prEvent_winNotC1S_le {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Pr{let o ← gameHybS pr Msg enc A}[HEv WinNotC1S o] ≤
      Pr{let o ← gameHybS pr Msg enc A}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] +
      Pr{let o ← gameHybS pr Msg enc A}[HEv Wsl o] := by
  refine (prEvent_mono _ _ (fun o => HEv (fun p => Wsf p ∧ ¬ p.1.C1) o ∨ HEv Wsl o) ?_).trans
    (prEvent_or_le _ _ _)
  rintro (_ | p) h
  · exact h.elim
  · exact h

/-- **Theorem 4.1** (SHRINCS EU-CMA security, classical, `H_msg^sf` a random oracle, under
Conjecture 3.1 and the quoted stateless route of Claim 4.16): the success of every forger is at
most the two PRF advantages, the SM-rTCR advantage of `B₀(A_F)`, the DI-Repro advantage of the
augmented `B₁⁺`, the seven collection terms of Theorem 4.2 for the Stage-1-precomputing augmented
reductions `B2S, B3S γ, B4S, B5S, B6S, B7S, B8S`, and the stateless bound `ε_sl`. -/
theorem theorem_4_1 (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) {εsl : ℝ≥0∞}
    (hsl : StatelessBound pr Msg enc A.toShrincsAdversary εsl) :
    succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) +
      Notions.STCR_Succ (B2S pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) +
      εsl := by
  rw [prfAdv_BprfAdv, show Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
      (BprfmsgAdv pr Msg enc A.toShrincsAdversary) =
    (Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage
      (Bprfmsg pr Msg enc A.toShrincsAdversary) from rfl]
  set A' := A.toShrincsAdversary
  have h0 := succ_eq_game0 pr Msg enc A'
  have h1 := claim_4_11 pr Msg enc A'
  have h2 := claim_4_12 pr Msg enc A'
  have h3 := game2_eq_gameS pr Msg enc A'
  have h4 := prEvent_winS_le pr Msg enc A'
  have h5 := claim_4_13 pr Msg enc A
  have h6 := claim_4_14 pr Msg enc A
  have h7 := prEvent_winNotC1S_le pr Msg enc A'
  have h8 := claim_4_15 pr Msg enc hinj hgc A
  rw [h0]
  refine h1.trans ?_
  calc _ ≤ (Pr{let o ← gameS pr Msg enc A' (implG pr (BMsg pr Msg))}[
          OEv (fun p => Wsf p ∧ p.1.C1) o] +
        (Pr{let o ← gameHybS pr Msg enc A'}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] +
          Pr{let o ← gameHybS pr Msg enc A'}[HEv Wsl o] +
          ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A))) +
        (Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage (Bprfmsg pr Msg enc A')) +
        (Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A') := by
        gcongr
        refine h2.trans ?_
        gcongr
        rw [h3]
        refine h4.trans ?_
        gcongr
        refine h6.trans ?_
        gcongr
    _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add h5 (add_le_add (add_le_add h8 hsl)
          (le_refl (ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A))))))
          (le_refl ((Notions.KeyedHash.toPRF (prfMsgF pr)).prfAdvantage (Bprfmsg pr Msg enc A'))))
          (le_refl ((Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A')))
        refine this.trans (le_of_eq ?_)
        ring

/-- **Theorem 4.1, the paper's `w · InSec^{sm-ud}` form**: with a common bound `ε` on the SM-UD
advantages of the `w − 2` hybrid reductions, the SM-UD term is at most `w · ε`. -/
theorem theorem_4_1_of_ud_le (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) {εsl ε : ℝ≥0∞}
    (hsl : StatelessBound pr Msg enc A.toShrincsAdversary εsl)
    (hε : ∀ γ < vp.params.w - 2, SM_DT_UD_Advantage (B3S pr Msg enc γ A) ≤ ε) :
    succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) +
      Notions.STCR_Succ (B2S pr Msg enc A) +
      vp.params.w * ε +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) +
      εsl := by
  refine (theorem_4_1 pr Msg enc hinj hgc A hsl).trans ?_
  gcongr
  calc ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A)
      ≤ ∑ _γ ∈ Finset.range (vp.params.w - 2), ε :=
        Finset.sum_le_sum fun γ hγ => hε γ (Finset.mem_range.mp hγ)
    _ = ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * ε := by simp
    _ ≤ vp.params.w * ε := by gcongr; exact_mod_cast Nat.sub_le _ _

/-- **Theorem 4.1 with the generic random-oracle bounds** (Corollaries G.1 and C.2/C.3): the
SM-rTCR term of `B₀(A_F)` is at most `(q_h + 2)/|Digest| + (q_h + 1)/|Y|`, and the DI-Repro term of
`B₁⁺` is at most `q_h/|Y|` (`B1S_diAdvantage_le`), with `q_h = q_{h,1} + q_{h,2}`. -/
theorem corollary_4_1 (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) {εsl : ℝ≥0∞}
    (hsl : StatelessBound pr Msg enc A.toShrincsAdversary εsl) :
    succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      (((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) + 1) / Fintype.card pr.Digest +
        ((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) / Fintype.card pr.Y +
      ((qh₁ + qh₂ : ℕ) : ℝ≥0∞) / Fintype.card pr.Y +
      Notions.STCR_Succ (B2S pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) +
      εsl := by
  refine (theorem_4_1 pr Msg enc hinj hgc A hsl).trans ?_
  have hr := Notions.Generic.RandomSamplingTCR.advantage_le_of_one (fun _ => true)
    (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A))
  have hd := B1S_diAdvantage_le pr Msg enc A
  have hsum :
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      ((((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) + 1) / Fintype.card pr.Digest +
        ((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) / Fintype.card pr.Y) =
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      (((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) + 1) / Fintype.card pr.Digest +
        ((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) / Fintype.card pr.Y := by ring
  rw [← hsum]
  gcongr

/-- **Theorem 4.1 (full, with Claim 4.16 proved unconditionally)**: SHRINCS EU-CMA security
in the classical ROM for `H_msg^sf`, under Conjecture 3.1 (`hgc`), digit-encoding injectivity
(`hinj`), and message-encoding injectivity (`henc`), with **no `StatelessBound` hypothesis**.
Combines the two PRF terms, SM-rTCR, DI-Repro, the seven stateful FXMSS collection terms
(Claim 4.15), and all ten stateless SLH-DSA post-PRF terms (Claim 4.16). -/
theorem theorem_4_1_full (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) +
      Notions.STCR_Succ (B2S pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) +
      (Notions.itsrSucc (Slhdsa.slHmsg pr) (Slhdsa.slMap vp)
          (Slhdsa.B_itsr pr (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        ∑ γ ∈ Finset.range (vp.params.w - 2),
          SM_DT_UD_Advantage (Slhdsa.B_ud pr
            (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) γ) +
        SM_DT_PRE_Advantage (Slhdsa.B_pre pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrF_wots pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_xmss pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThK pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThLsl pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        3 * SM_DT_TCR_Advantage (Slhdsa.B_tcrF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_DSPR_Advantage (Slhdsa.B_dsprF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) :=
  theorem_4_1 pr Msg enc hinj hgc A (claim_4_16 pr Msg enc hinj henc A.toShrincsAdversary)

/-- **Theorem 4.1 (full, `w · InSec^{sm-ud}` form)**: with common bounds `ε_sf` and `ε_sl` on
the `w − 2` stateful and stateless SM-UD hybrid advantages respectively, each sum is at most
`w · ε_sf` and `w · ε_sl`, with no `StatelessBound` hypothesis. -/
theorem theorem_4_1_full_of_ud_le (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L)
    {εsf εsl : ℝ≥0∞}
    (hεsf : ∀ γ < vp.params.w - 2, SM_DT_UD_Advantage (B3S pr Msg enc γ A) ≤ εsf)
    (hεsl : ∀ γ < vp.params.w - 2,
      SM_DT_UD_Advantage (Slhdsa.B_ud pr
        (sfStageShrincs pr Msg enc A.toShrincsAdversary)
        (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) γ) ≤ εsl) :
    succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) +
      Notions.STCR_Succ (B2S pr Msg enc A) +
      vp.params.w * εsf +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) +
      (Notions.itsrSucc (Slhdsa.slHmsg pr) (Slhdsa.slMap vp)
          (Slhdsa.B_itsr pr (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        vp.params.w * εsl +
        SM_DT_PRE_Advantage (Slhdsa.B_pre pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrF_wots pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_xmss pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThK pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThLsl pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        3 * SM_DT_TCR_Advantage (Slhdsa.B_tcrF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_DSPR_Advantage (Slhdsa.B_dsprF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) := by
  refine (theorem_4_1_full pr Msg enc hinj henc hgc A).trans ?_
  gcongr
  · calc ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A)
        ≤ ∑ _γ ∈ Finset.range (vp.params.w - 2), εsf :=
          Finset.sum_le_sum fun γ hγ => hεsf γ (Finset.mem_range.mp hγ)
      _ = ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * εsf := by simp
      _ ≤ vp.params.w * εsf := by gcongr; exact_mod_cast Nat.sub_le _ _
  · calc ∑ γ ∈ Finset.range (vp.params.w - 2),
          SM_DT_UD_Advantage (Slhdsa.B_ud pr
            (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) γ)
        ≤ ∑ _γ ∈ Finset.range (vp.params.w - 2), εsl :=
          Finset.sum_le_sum fun γ hγ => hεsl γ (Finset.mem_range.mp hγ)
      _ = ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * εsl := by simp
      _ ≤ vp.params.w * εsl := by gcongr; exact_mod_cast Nat.sub_le _ _

/-- **Theorem 4.1 (full) with the generic random-oracle bounds** (Corollaries G.1 and C.2/C.3)
and **no `StatelessBound` hypothesis**: replaces `B₀(A_F)` and `B₁⁺` by their classical ROM bounds
and discharges Claim 4.16 with all ten explicit stateless post-PRF terms. -/
theorem corollary_4_1_full (hinj : Function.Injective pr.yToBytes) (henc : enc.Injective)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    succ pr Msg enc A.toShrincsAdversary ≤
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfF pr)) (BprfAdv pr Msg enc A) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      (((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) + 1) / Fintype.card pr.Digest +
        ((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) / Fintype.card pr.Y +
      ((qh₁ + qh₂ : ℕ) : ℝ≥0∞) / Fintype.card pr.Y +
      Notions.STCR_Succ (B2S pr Msg enc A) +
      ∑ γ ∈ Finset.range (vp.params.w - 2), SM_DT_UD_Advantage (B3S pr Msg enc γ A) +
      SM_DT_TCR_Advantage (B4S pr Msg enc A) +
      SM_DT_PRE_Advantage (B5S pr Msg enc A) +
      SM_DT_TCR_Advantage (B6S pr Msg enc A) +
      SM_DT_TCR_Advantage (B7S pr Msg enc A) +
      Notions.SMTCRExcl_Succ (B8S pr Msg enc A) +
      (Notions.itsrSucc (Slhdsa.slHmsg pr) (Slhdsa.slMap vp)
          (Slhdsa.B_itsr pr (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        ∑ γ ∈ Finset.range (vp.params.w - 2),
          SM_DT_UD_Advantage (Slhdsa.B_ud pr
            (sfStageShrincs pr Msg enc A.toShrincsAdversary)
            (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) γ) +
        SM_DT_PRE_Advantage (Slhdsa.B_pre pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (Slhdsa.wotsStage2 pr (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrF_wots pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_xmss pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThK pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrThLsl pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_TCR_Advantage (Slhdsa.B_tcrH_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        3 * SM_DT_TCR_Advantage (Slhdsa.B_tcrF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary)) +
        SM_DT_DSPR_Advantage (Slhdsa.B_dsprF_fors pr
          (sfStageShrincs pr Msg enc A.toShrincsAdversary)
          (shrincsSlAdv pr Msg enc A.toShrincsAdversary))) :=
  corollary_4_1 pr Msg enc hinj hgc A (claim_4_16 pr Msg enc hinj henc A.toShrincsAdversary)

end ShrincsSecurity.Shrincs

end
