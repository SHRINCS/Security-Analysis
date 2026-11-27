module

public import ShrincsSecurity.Fxmss.Bridge
public import ShrincsSecurity.Fxmss.Remark46
public import ShrincsSecurity.Fxmss.Claim41
public import ShrincsSecurity.Fxmss.Claim42Pre
public import ShrincsSecurity.Fxmss.G2Hyb
public import ShrincsSecurity.Fxmss.Claim410
public import ShrincsSecurity.Fxmss.HybExtract
public import ShrincsSecurity.Fxmss.Claim43
public import ShrincsSecurity.Fxmss.Claim44
public import ShrincsSecurity.Fxmss.Claim45
public import ShrincsSecurity.Fxmss.Claim46
public import ShrincsSecurity.Fxmss.Claim47
public import ShrincsSecurity.Fxmss.Claim48
public import ShrincsSecurity.Fxmss.Claim49
public import ShrincsSecurity.Repro.Bound

/-!
# Theorem 4.2: EU-CMA security of FXMSS

`SHRINCS-Security-Analysis.pdf`, **Theorem 4.2** (txt lines 2949–3010) and its proof, Section 4.7
(txt lines 3116–3900), in the classical setting: `H_msg^sf` is a random oracle (the runtime
`ProbCompRuntime.rom`), every tweakable-hash member is a public function of `PK.seed`
(Assumption 4.1), and Conjecture 3.1 (`GrindComplete`) is a hypothesis.

## Statement

`theorem_4_2`: for every forger `A` (at most `q_s` signing queries, `q_{h,1} + q_{h,2}` queries to
`H_msg^sf`, structures with at most `L` anchors),

`Succ^{FXMSS-EU-CMA}(A) ≤ Succ^{SM-rTCR,1}(B₀) + Adv^{DI-Repro}(B₁) + Succ^{S-TCR(Prop)}(B₂)
  + Σ_{γ < w−2} Adv^{sm-ud}(B₃,γ) + Succ^{sm-tcr}(B₄) + Succ^{sm-pre}(B₅) + Succ^{sm-tcr}(B₆)
  + Succ^{sm-tcr}(B₇) + Succ^{sm-tcr-excl}(B₈)`,

where `B₀ … B₈` are the explicit reductions of Claims 4.1–4.9 built from `A`, with the paper's
target counts (`L`, `L·lsf`, `L·lsf·w`, `L`, `I = L − 1`, `L + I`) and query counts
(`q̃_h = q_h + 1` for `B₀`; `L + q_h + 1` hash queries and `L` reprogramming calls for `B₁`). The
`w`-term is a sum over the `w − 2` transitions; `theorem_4_2_of_ud_le` relaxes it to `w · ε` for a
common bound `ε`. `corollary_4_2` instantiates the two random-oracle terms with the generic
classical bounds: `Succ^{SM-rTCR,1}(B₀) ≤ (q_h + 2)/2^{2n} + (q_h + 1)/2^n` (Corollary G.1) and
`Adv^{DI-Repro}(B₁) ≤ E[q_pre]/2^n ≤ q_h/2^n` (Corollary C.2, `B1_diAdvantage_le`). The other terms
are standard-model (collection) advantages and stay as they are: the games of the generic bounds
of Appendix E (Theorem E.1) model `Th` as a random oracle without a collection oracle, which is
not the game `B₈` plays.

## The proof (telescoping)

`F.0 → F.1` (Claim 4.1): `Succ = Pr_{F.0}[Win] ≤ Pr[Win ∧ C₁] + Pr[Win ∧ ¬C₁]`, the first term
bounded by `B₀`. `F.1 → F.2` (Claim 4.2): the lazy reprogramming game, then the presampled form
(`gameG2_eq_gameHyb`). In `F.2` (`gameHyb 0`), Claim 4.10 (constructive) splits `Win ∧ ¬C₁` into
the events `E3, E5, …, E9`; Claims 4.3, 4.5, 4.7, 4.8, 4.9 bound `E3, E5, E7, E8, E9` in `F.2`
directly, and the chain-value hybrid of Claim 4.4 moves `E6` to `F.4 = gameHyb (w − 2)`, where
Claim 4.6 bounds it.

## Deviations from the paper

* **Order of hops.** The paper aborts on the events one after the other (`F.3 … F.9`) and applies
  the SM-UD hop before the TCR hops. Here the TCR events are bounded in `F.2` itself (their
  reductions build the honest secret-key chains through the challenge oracle, as SM-TCR permits),
  and the SM-UD hybrid is applied to the preimage event only. The final sum has exactly the
  paper's nine terms (with the `w`-term as a sum over the `w − 2` transitions).
* **Time accounting.** `ξ`, `ξ̃`, `ξ̃′` are replaced by the explicit reductions; the
  collection-query budgets `q_{λ,i}` are not bounded (the collection games of VCVio carry none;
  Conjecture 4.1 says they do not matter). The reductions evaluate in their first stage only what
  their targets need and the rest of the simulation in their second stage, with `PK.seed` known.
* **`PK.sl`** is an extra public value drawn by an arbitrary `slKeygen : PK.seed → ProbComp Y`.
* **Remark 4.6** is realised inside the games: after the forgery is verified, every anchor is
  signed (with a message different from `M*`); `Remark46.lean` proves the paper's wrapper lemma
  for the EU-CMA experiment itself (`succ_wrap`, no extra random-oracle query). Its signing
  budget is `q_s + L`, not `L`: signing queries answered `⊥` (leaves outside the structure or
  already used) still log their messages, so a forger whose `L` queries all miss the structure
  needs `L` more to sign every anchor, and dropping its `⊥` queries would change the message log
  (only `Succ(A) ≤ Succ(A′)` would remain). For forgers that, as the paper assumes, query only
  distinct anchors, `A`'s queries and the wrapper's together are the `L` anchors
  (`length_wrapIds`).
* **Claim 4.10** needs the digit encoding `yToBytes` injective (`hinj`), and is stated with
  witnesses computed from the forgery (`Events.lean`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-- The arithmetic of the telescoping sum. -/
private theorem telescope {s g1 g2 h e3 e5 e6 e6' e7 e8 e9 a0 a1 a2 ud a4 a5 a6 a7 a8 : ℝ≥0∞}
    (hs : s ≤ g1 + g2) (h1 : g1 ≤ a0) (h12 : g2 ≤ h + a1)
    (hx : h ≤ e3 + e5 + e6 + e7 + e8 + e9)
    (h3 : e3 ≤ a2) (h4 : e6 ≤ e6' + ud) (h5 : e5 ≤ a4) (h6 : e6' ≤ a5) (h7 : e7 ≤ a6)
    (h8 : e8 ≤ a7) (h9 : e9 ≤ a8) :
    s ≤ a0 + a1 + a2 + ud + a4 + a5 + a6 + a7 + a8 := by
  calc s ≤ g1 + g2 := hs
    _ ≤ a0 + ((a2 + a4 + (a5 + ud) + a6 + a7 + a8) + a1) := by
        gcongr
        refine h12.trans ?_
        gcongr
        refine hx.trans ?_
        gcongr
        exact h4.trans (by gcongr)
    _ = a0 + a1 + a2 + ud + a4 + a5 + a6 + a7 + a8 := by ring

omit [Fintype pr.Digest] in
/-- **Theorem 4.2** (FXMSS EU-CMA security, classical, `H_msg^sf` a random oracle, under
Conjecture 3.1): the success of every forger is at most the sum of the advantages of the nine
explicit reductions of Claims 4.1–4.9. -/
theorem theorem_4_2 (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    succ pr Msg slKeygen A.toFxmssAdversary ≤
      Generic.RandomSamplingTCR.advantage (fun _ => true) 1 (B0 pr Msg slKeygen A) +
      ENNReal.ofReal (Repro.diAdvantage (B1 pr Msg slKeygen A)) +
      STCR_Succ (B2 pr Msg slKeygen A) +
      ∑ γ ∈ Finset.range (P.w - 2), SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A) +
      SM_DT_TCR_Advantage (B4 pr Msg slKeygen A) +
      SM_DT_PRE_Advantage (B5 pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B6 pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B7 pr Msg slKeygen A) +
      SMTCRExcl_Succ (B8 pr Msg slKeygen A) := by
  set A' := A.toFxmssAdversary
  -- F.0: the experiment is `gameG`
  rw [succ_eq_gameG]
  -- F.0 → F.1 → F.2
  have h01 : Pr{let o ← gameG pr Msg slKeygen A'}[WinO o] ≤
      Pr{let o ← gameG pr Msg slKeygen A'}[WinC1 o] +
        Pr{let o ← gameG pr Msg slKeygen A'}[WinNotC1 o] := by
    refine (prEvent_mono _ _ (fun o => WinC1 o ∨ WinNotC1 o) ?_).trans (prEvent_or_le _ _ _)
    rintro (_ | tr) h
    · exact h.elim
    · by_cases hc : tr.C1
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
  have h12 := claim_4_2 pr Msg slKeygen hP A
  rw [gameG2_eq_gameHyb pr Msg slKeygen hP A'] at h12
  -- F.2: Claim 4.10 and the union bound, then Claims 4.3–4.9
  exact telescope h01 (claim_4_1 pr Msg slKeygen hP A) h12
    (gameHyb_winNotC1_le slKeygen hP hinj hgc 0 A')
    (claim_4_3 pr Msg slKeygen hP hgc A) (claim_4_4 pr Msg slKeygen hP hgc A)
    (claim_4_5 pr Msg slKeygen hP hgc A) (claim_4_6 pr Msg slKeygen hP hgc A)
    (claim_4_7 pr Msg slKeygen hP hgc A) (claim_4_8 pr Msg slKeygen hP hgc A)
    (claim_4_9 pr Msg slKeygen hP hgc A)

omit [Fintype pr.Digest] in
/-- **Theorem 4.2, the paper's `w · InSec^{sm-ud}` form**: with a common bound `ε` on the SM-UD
advantages of the `w − 2` hybrid reductions, the SM-UD term is at most `w · ε`. -/
theorem theorem_4_2_of_ud_le (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    {ε : ℝ≥0∞} (hε : ∀ γ < P.w - 2, SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A) ≤ ε) :
    succ pr Msg slKeygen A.toFxmssAdversary ≤
      Generic.RandomSamplingTCR.advantage (fun _ => true) 1 (B0 pr Msg slKeygen A) +
      ENNReal.ofReal (Repro.diAdvantage (B1 pr Msg slKeygen A)) +
      STCR_Succ (B2 pr Msg slKeygen A) +
      P.w * ε +
      SM_DT_TCR_Advantage (B4 pr Msg slKeygen A) +
      SM_DT_PRE_Advantage (B5 pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B6 pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B7 pr Msg slKeygen A) +
      SMTCRExcl_Succ (B8 pr Msg slKeygen A) := by
  refine (theorem_4_2 pr Msg slKeygen hP hinj hgc A).trans ?_
  gcongr
  calc ∑ γ ∈ Finset.range (P.w - 2), SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A)
      ≤ ∑ _γ ∈ Finset.range (P.w - 2), ε :=
        Finset.sum_le_sum fun γ hγ => hε γ (Finset.mem_range.mp hγ)
    _ = ((P.w - 2 : ℕ) : ℝ≥0∞) * ε := by simp
    _ ≤ P.w * ε := by gcongr; exact_mod_cast Nat.sub_le _ _

/-- **Theorem 4.2 with the generic random-oracle bounds** (Corollaries G.1 and C.2): the SM-rTCR
term of `B₀` (which makes `q̃_h = q_h + 1` queries to `H_msg^sf`) is at most
`(q̃_h + 1)/|{0,1}^{2n}| + q̃_h/|R|`, and the DI-Repro term of `B₁` is at most `q_h/|R|`
(`B1_diAdvantage_le`: only the forger's queries made before their point is reprogrammed count,
the `q_pre` of Corollary C.2; `B₁`'s read-backs and the verification query never do). The
remaining terms are standard-model (collection) advantages. -/
theorem corollary_4_2 (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    succ pr Msg slKeygen A.toFxmssAdversary ≤
      (((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) + 1) / Fintype.card pr.Digest +
        ((qh₁ + qh₂ + 1 : ℕ) : ℝ≥0∞) / Fintype.card pr.Y +
      ((qh₁ + qh₂ : ℕ) : ℝ≥0∞) / Fintype.card pr.Y +
      STCR_Succ (B2 pr Msg slKeygen A) +
      ∑ γ ∈ Finset.range (P.w - 2), SM_DT_UD_Advantage (B3 pr Msg slKeygen γ A) +
      SM_DT_TCR_Advantage (B4 pr Msg slKeygen A) +
      SM_DT_PRE_Advantage (B5 pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B6 pr Msg slKeygen A) +
      SM_DT_TCR_Advantage (B7 pr Msg slKeygen A) +
      SMTCRExcl_Succ (B8 pr Msg slKeygen A) := by
  refine (theorem_4_2 pr Msg slKeygen hP hinj hgc A).trans ?_
  have hr := Generic.RandomSamplingTCR.advantage_le_of_one (fun _ => true) (B0 pr Msg slKeygen A)
  have hd := B1_diAdvantage_le pr Msg slKeygen A
  gcongr

end ShrincsSecurity.Fxmss.Rom

end
