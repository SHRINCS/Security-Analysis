module

public import ShrincsSecurity.Shrincs.Bridge0
public import ShrincsSecurity.Shrincs.Claim411
public import ShrincsSecurity.Shrincs.Claim412
public import ShrincsSecurity.Shrincs.Bridge2
public import ShrincsSecurity.Shrincs.Claim413
public import ShrincsSecurity.Shrincs.Claim414
public import ShrincsSecurity.Shrincs.Claim415
public import ShrincsSecurity.Shrincs.PrfMsgBound

/-!
# Theorem 4.1: EU-CMA security of SHRINCS

`SHRINCS-Security-Analysis.pdf`, **Theorem 4.1** (txt lines 2874–2948) and its proof, Section 4.8
(txt lines 3926–4400), in the classical setting: `H_msg^sf` is a random oracle (the runtime
`ProbCompRuntime.rom`), every other named function is a fixed function of the primitive bundle
(the reading of Assumption 4.1 of the formalisation of Theorem 4.2, see `Model.lean`), and
Conjecture 3.1 (`GrindComplete`) is a hypothesis.

## The single quoted assumption: `StatelessBound` (Claim 4.16)

The paper does not prove the stateless route: Claim 4.16 applies the reductions of [HK22]
(Theorem 4.3, quoted) to the extended games, and asserts that the stateless-branch forgeries of
`GAME.5` have probability at most the ten summands of Theorem 4.3 other than its two PRF terms.
`StatelessBound A ε_sl` states **exactly this assertion, for the given forger `A`**:

`Pr_{GAME.5}[W_sl] ≤ ε_sl`,

where `GAME.5`, for stateless-branch forgeries, is `GAME.4` (`gameHybS`, `Wrapper.lean`): the
SHRINCS experiment with uniform secret elements on both paths (`GAME.1`), uniform randomizers
cached per `PRF_msg` input (`GAME.2`), the digests of the stateful signatures fixed uniformly at
setup and programmed into `H_msg^sf` (`GAME.4`), and `W_sl` the event that the forgery is fresh
for the signing queries of both paths and verifies via the stateless branch (the aborts of
`GAME.3` and `GAME.5` concern the stateful branch only, so `Pr_{GAME.5}[W_sl] = Pr_{GAME.4}[W_sl]`).
The quantity `ε_sl` is the paper's sum of the ten [HK22] summands, kept abstract. Nothing else
about the stateless path is assumed: `StatelessBound` is the only hypothesis of `theorem_4_1`
besides Conjecture 3.1 (`hgc`) and the injectivity of the digit encoding `yToBytes` (`hinj`, the
hypothesis of Claim 4.10 in Theorem 4.2).

## Statement

`theorem_4_1`: for every forger `A` (Definition 4.15; `q_s` signing queries, `q_{h,1} + q_{h,2}`
queries to `H_msg^sf`, structures with at most `L` anchors) with `StatelessBound A ε_sl`,

`Succ^{SHRINCS-EU-CMA}(A) ≤ Adv^{prf}_{PRF}(B_prf) + Adv^{prf}_{PRF_msg, q_s}(B_prfmsg)
  + Adv^{SM-rTCR,1}(B₀(A_F)) + Adv^{DI-Repro}(B₁⁺)
  + Succ^{S-TCR(Prop)}(B₂(A_F)) + Σ_{γ < w−2} Adv^{sm-ud}(B₃,γ(A_F)) + Succ^{sm-tcr}(B₄(A_F))
  + Succ^{sm-pre}(B₅(A_F)) + Succ^{sm-tcr}(B₆(A_F)) + Succ^{sm-tcr}(B₇(A_F))
  + Succ^{sm-tcr-excl}(B₈(A_F)) + ε_sl`.

`A_F` (`AF`) is the FXMSS forger that runs `A` and simulates the stateless path with uniform
secrets and randomizers; `B₀(A_F), …, B₈(A_F)` are therefore the **augmented reductions** of
Section 4.8 (the reductions of Section 4.7 extended by the stateless path), and `B₁⁺` (`B1S`) is
the augmented `B₁` whose output also covers the stateless branch (one shared reprogramming term).

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

* **Time and budgets** are replaced by explicit reductions, as in Theorem 4.2. `B_prfmsg` is an
  adversary of Definition 4.3 with the paper's budget `q_s` (`BprfmsgAdv`, `PrfMsgBound.lean`;
  the completion of Remark 4.6 is not part of `GAME.0`–`GAME.2`, so `q_s` and not `q_s^{sl} + L`).
  The `PRF` term is the advantage of the explicit reduction `B_prf` without the budget `q₁`
  (VCVio's `prfAdvantage`): `B_prf` queries its oracle once per stateful secret element and once
  per secret draw of the stateless programs, repeated draws included, and bounding the latter by
  the number of secret elements of the hypertree would need the address ranges of VCVio's FIPS 205
  programs, which the proof does not otherwise use.
* **Collection budgets** `q̃_{λ,i}`, `q_λ` are not tracked (the collection games of VCVio carry
  none), as in Theorem 4.2; the augmented reductions evaluate the stateless path inside `A_F`.
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
augmented `B₁⁺`, the seven collection terms of Theorem 4.2 for the augmented reductions
`B₂(A_F), …, B₈(A_F)`, and the stateless bound `ε_sl`. -/
theorem theorem_4_1 (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) {εsl : ℝ≥0∞}
    (hsl : StatelessBound pr Msg enc A.toShrincsAdversary εsl) :
    succ pr Msg enc A.toShrincsAdversary ≤
      (Notions.KeyedHash.toPRF (prfF pr)).prfAdvantage (Bprf pr Msg enc A.toShrincsAdversary) +
      Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
        (BprfmsgAdv pr Msg enc A.toShrincsAdversary) +
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ENNReal.ofReal (Repro.diAdvantage (B1S pr Msg enc A)) +
      Notions.STCR_Succ (Fxmss.Rom.B2 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (Fxmss.Rom.B3 pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A)) +
      SM_DT_TCR_Advantage (Fxmss.Rom.B4 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      SM_DT_PRE_Advantage (Fxmss.Rom.B5 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      SM_DT_TCR_Advantage (Fxmss.Rom.B6 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      SM_DT_TCR_Advantage (Fxmss.Rom.B7 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      Notions.SMTCRExcl_Succ (Fxmss.Rom.B8 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      εsl := by
  rw [show Notions.prfAdv (Notions.KeyedHash.toPRF (prfMsgF pr))
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

end ShrincsSecurity.Shrincs

end
