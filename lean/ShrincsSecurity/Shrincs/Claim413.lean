module

public import ShrincsSecurity.Shrincs.AFBounds

/-!
# Claim 4.13: `GAME.2 → GAME.3`, the SM-rTCR abort on the stateful branch

`SHRINCS-Security-Analysis.pdf`, Section 4.8, **Claim 4.13** (txt lines 4005–4040): the abort
event of `GAME.3` (a stateful-branch forgery at a signed position whose digest equals that
position's) is bounded by `InSec^{SM-rTCR,1}(H_msg^sf, 1; …)`, through the reduction `B₃` of the
paper, "the reduction `B₀` of Algorithm 4 extended by the stateless path".

Here the extended reduction is `B₀` of Section 4.7 run with the forger `A_F` (`AF`), which
simulates the stateless path with uniform secrets and randomizers (`GAME.1`, `GAME.2`) itself.

* `gameS_implG_map`: `GAME.2` in the form of Section 4.7 (`gameS implG`), with `A_F`'s extra
  output dropped, **is** `F.0` for `A_F` (`gameG`).
* `claim_4_13`: `Pr_{GAME.2}[W_sf ∧ C₁] ≤ Pr_{F.0(A_F)}[Win ∧ C₁] ≤ Adv^{SM-rTCR,1}(B₀(A_F))`, by
  Claim 4.1 (`claim_4_1`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Shrincs

open Scheme
open Fxmss.Rom (Keys implG gameG)

variable {vp : ValidatedParams} (pr : Primitives vp.params) (Msg : Type) (enc : MsgEnc Msg)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [SampleableType pr.SkSeed] [SampleableType pr.SkPrf]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]

namespace Claim413

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Fintype pr.Y]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
/-- The signing phase `stage2Prog` of Section 4.7 played by `A_F` is `progS` with `A_F`'s extra
output dropped. -/
theorem stage2Prog_AFAdv {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs)
    (st : (AFAdv pr Msg enc A).State) (K : Keys pr) :
    Fxmss.Rom.stage2Prog pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A) st K =
      (fun r => r.1) <$> progS pr Msg enc A st K := by
  simp [Fxmss.Rom.stage2Prog, progS, AFAdv, map_bind]

end Claim413

open Claim413

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Fintype pr.Y]
  [DecidableEq pr.Digest] in
/-- **`GAME.2` is `F.0` for `A_F`**: dropping `A_F`'s extra output from the augmented game gives
the game `F.0` of Section 4.7 played by `A_F`. -/
theorem gameS_implG_map {qs : ℕ} (A : Notions.ShrincsAdversary (scheme pr Msg enc) qs) :
    Option.map Prod.fst <$> gameS pr Msg enc A (implG pr (BMsg pr Msg)) =
      gameG pr (BMsg pr Msg) (slKeygenS pr) (AFAdv pr Msg enc A) := by
  simp only [gameS, gameG, map_bind]
  refine bind_congr fun pk => ?_
  change _ = stage1S pr Msg enc A >>= _
  refine bind_congr fun z => ?_
  unfold stageGS Fxmss.Rom.stageG
  split_ifs
  · simp only [map_bind]
    refine bind_congr fun f => bind_congr fun pkSl => ?_
    rw [stage2Prog_AFAdv]
    simp [simulateQ_map, StateT.run_map]
  · simp

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Inhabited pr.Digest] [Fintype Msg] [Fintype pr.Y] in
/-- **Claim 4.13**: the abort event of `GAME.3`, a stateful-branch win `W_sf` with equal digests
at a signed position (`C₁`), has probability at most the SM-rTCR advantage of the augmented
reduction `B₀(A_F)`, which makes `q_{h,1} + q_{h,2} + 1` queries to `H_msg^sf`. -/
theorem claim_4_13 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg enc qs qh₁ qh₂ L) :
    Pr{let o ← gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg))}[
        OEv (fun p => Wsf p ∧ p.1.C1) o] ≤
      Notions.Generic.RandomSamplingTCR.advantage (fun _ => true) 1
        (Fxmss.Rom.B0 pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A)) := by
  calc Pr{let o ← gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg))}[
        OEv (fun p => Wsf p ∧ p.1.C1) o]
      ≤ Pr{let o ← gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg))}[
          Fxmss.Rom.WinC1 (o.map Prod.fst)] := by
        refine prEvent_mono _ _ _ fun o h => ?_
        rcases o with _ | p
        · exact h.elim
        · exact ⟨h.1.2.2.2, h.2⟩
    _ = Pr{let o ← Option.map Prod.fst <$>
          gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg))}[Fxmss.Rom.WinC1 o] :=
        (prEvent_map (gameS pr Msg enc A.toShrincsAdversary (implG pr (BMsg pr Msg)))
          (Option.map Prod.fst) Fxmss.Rom.WinC1).symm
    _ = Pr{let o ← gameG pr (BMsg pr Msg) (slKeygenS pr) (AF pr Msg enc A).toFxmssAdversary}[
          Fxmss.Rom.WinC1 o] := by rw [gameS_implG_map]; rfl
    _ ≤ _ := Fxmss.Rom.claim_4_1 pr (BMsg pr Msg) (slKeygenS pr) vp.valid (AF pr Msg enc A)

end ShrincsSecurity.Shrincs

end
