module

public import ShrincsSecurity.Shrincs.AFBounds

/-!
# Claim 4.15: `GAME.4 → GAME.5`, the stateful-branch forgeries

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.15** (txt lines 4180–4215):
`Succ₄ − Succ₅ = Pr_{GAME.4}[W_sf]` is at most the seven collection summands of Theorem 4.2 for
the augmented reductions, "the sum of Claims 4.3 to 4.10 for the augmented reductions".

Here the augmented reductions are the reductions `B₂ … B₈` of Section 4.7 run with the forger
`A_F` (`AF`), which simulates the stateless path with uniform secrets inside.

* `gameHybS_map`: `GAME.4` with presampled digests (`gameHybS`), with `A_F`'s extra output
  dropped, **is** `F.2` for `A_F` (`gameHyb 0`).
* `claim_4_15`: `Pr_{GAME.4}[W_sf ∧ ¬C₁] ≤ Pr_{F.2(A_F)}[Win ∧ ¬C₁]`, bounded by Claims 4.3–4.10
  as in the proof of Theorem 4.2.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys gameHyb)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

namespace Claim415

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Fintype pr.Y]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The signing phase `stage2Prog` of Section 4.7 played by `A_F` is `progS` with `A_F`'s extra
output dropped. -/
theorem stage2Prog_AFAdv {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : (AFAdv pr Msg enc A).State) (K : Keys pr) :
    Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A) st K =
      (fun r => r.1) <$> progS pr Msg enc A st K := by
  simp [Fxmss.Rom.stage2Prog, progS, AFAdv, map_bind]

/-- The arithmetic of the telescope of Theorem 4.2 after Claim 4.10. -/
theorem telescope {h e3 e5 e6 e6' e7 e8 e9 a2 ud a4 a5 a6 a7 a8 : ℝ≥0∞}
    (hx : h ≤ e3 + e5 + e6 + e7 + e8 + e9)
    (h3 : e3 ≤ a2) (h4 : e6 ≤ e6' + ud) (h5 : e5 ≤ a4) (h6 : e6' ≤ a5) (h7 : e7 ≤ a6)
    (h8 : e8 ≤ a7) (h9 : e9 ≤ a8) :
    h ≤ a2 + ud + a4 + a5 + a6 + a7 + a8 := by
  calc h ≤ e3 + e5 + e6 + e7 + e8 + e9 := hx
    _ ≤ a2 + a4 + (a5 + ud) + a6 + a7 + a8 := by
        gcongr
        exact h4.trans (by gcongr)
    _ = a2 + ud + a4 + a5 + a6 + a7 + a8 := by ring

end Claim415

open Claim415

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **`GAME.4` is `F.2` for `A_F`**: dropping `A_F`'s extra output from the augmented block game
gives the block game `F.2 = gameHyb 0` of Section 4.7 played by `A_F`. -/
theorem gameHybS_map {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Option.map (fun p => (p.1.1, p.2)) <$> gameHybS pr Msg enc A =
      gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 (AFAdv pr Msg enc A) := by
  simp only [gameHybS, gameHyb, map_bind]
  refine bind_congr fun pk => ?_
  change _ = setupHybS pr Msg enc A >>= _
  refine bind_congr fun d => ?_
  unfold stageHybS Fxmss.Rom.stageHyb
  split_ifs
  · simp only [map_bind]
    refine bind_congr fun pkSl => ?_
    rw [stage2Prog_AFAdv]
    simp [simulateQ_map, StateT.run_map]
  · simp

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y] in
/-- **Claim 4.15**: the stateful-branch wins of `GAME.4` without the abort of `GAME.3` have
probability at most the seven collection summands of Theorem 4.2 for the augmented reductions
`B₂(A_F), …, B₈(A_F)` (the `w`-term as the sum over the `w − 2` hybrid transitions). -/
theorem claim_4_15 (hinj : Function.Injective pr.yToBytes) (hgc : GrindComplete pr)
    {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] ≤
      Notions.STCR_Succ (Fxmss.Rom.B2 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      ∑ γ ∈ Finset.range (vp.params.w - 2),
        SM_DT_UD_Advantage (Fxmss.Rom.B3 pr (BMsg pr Msg) (slKeygenS pr) γ (AF pr Msg enc A)) +
      SM_DT_TCR_Advantage (Fxmss.Rom.B4 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      SM_DT_PRE_Advantage (Fxmss.Rom.B5 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      SM_DT_TCR_Advantage (Fxmss.Rom.B6 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      SM_DT_TCR_Advantage (Fxmss.Rom.B7 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) +
      Notions.SMTCRExcl_Succ (Fxmss.Rom.B8 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) := by
  set A' := AF pr Msg enc A
  have hF : Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[
        HEv (fun p => Wsf p ∧ ¬ p.1.C1) o] ≤
      Pr{let o ← gameHyb pr (BMsg pr Msg) (slKeygenS pr) 0 A'.toFxmssAdversary}[
        Fxmss.Rom.WinNotC1 (o.map Prod.fst)] := by
    calc Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[HEv (fun p => Wsf p ∧ ¬ p.1.C1) o]
        ≤ Pr{let o ← gameHybS pr Msg enc A.toShrincsAdversary}[
            Fxmss.Rom.WinNotC1 ((o.map (fun p => (p.1.1, p.2))).map Prod.fst)] := by
          refine prEvent_mono _ _ _ fun o h => ?_
          rcases o with _ | p
          · exact h.elim
          · exact ⟨h.1.2.2.2, h.2⟩
      _ = Pr{let o ← Option.map (fun p => (p.1.1, p.2)) <$> gameHybS pr Msg enc A.toShrincsAdversary}[
            Fxmss.Rom.WinNotC1 (o.map Prod.fst)] :=
          (prEvent_map (gameHybS pr Msg enc A.toShrincsAdversary)
            (Option.map fun p => (p.1.1, p.2))
            (fun o => Fxmss.Rom.WinNotC1 (o.map Prod.fst))).symm
      _ = _ := by rw [gameHybS_map]; rfl
  exact telescope (hF.trans (Fxmss.Rom.gameHyb_winNotC1_le (slKeygenS pr) vp.valid hinj hgc 0 _))
    (Fxmss.Rom.claim_4_3 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')
    (Fxmss.Rom.claim_4_4 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')
    (Fxmss.Rom.claim_4_5 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')
    (Fxmss.Rom.claim_4_6 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')
    (Fxmss.Rom.claim_4_7 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')
    (Fxmss.Rom.claim_4_8 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')
    (Fxmss.Rom.claim_4_9 pr (BMsg pr Msg) (slKeygenS pr) vp.valid hgc A')

end ShrincsSecurity.Shrincs

end
