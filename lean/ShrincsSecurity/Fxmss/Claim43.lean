module

public import ShrincsSecurity.Fxmss.TcrCommon

/-!
# Claim 4.3: the hop `F.2 → F.3` (S-TCR(Prop) of `H_grind`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.3** (txt lines 3376–3412) and
**Algorithm 6** (the reduction `B₂`, lines 3440–3475).

`B₂` is built with `mkSTcrAdv`:
* **first stage**: the setup of the block games (`setupHyb`: the structure phase of the forger, the
  presampled digests `y_j` and the uniform secrets `u`), then one challenge query
  `O_Prop(ADRS^g_j[0:10], y_j)` per anchor, in the canonical order `anchorList` (no query on an
  invalid structure);
* **second stage**: with `PK.seed` revealed, it runs the signing phase of `F.3_0 = F.2`
  (`stageHyb`, all members of `Th_λ` being public functions of `PK.seed`, Assumption 4.1) and
  searches its recorded targets for the forgery's `(y*, c*)` at the grinding tweak of the forged
  leaf (`stcrFind`).

Under Conjecture 3.1 the oracle's least counter is the scheme's counter (`leastCounter_thGrind`),
so the honest encoded digest is the oracle's answer and the event `E3` of `F.3` is an
S-TCR(Prop) collision.

## Deviations from the paper
* `B₂` does not evaluate the FXMSS key generation and `PK.sl` through the collection oracle
  before the parameter is revealed (Algorithm 6, lines 6–7): it computes them in its second stage
  from `PK.seed` (Assumption 4.1: every member of `Th_λ` is a public function of `PK.seed`; the
  forger sees only the final public key). Time accounting (`ξ̃`) is replaced by this explicit
  construction; no collection query is made.
* The number of targets is bounded by `L` (the anchor bound of `Forger`) rather than `q_s`: by
  Remark 4.6 every anchor is signed, so `q_s = L` in the games.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace ShrincsSecurity.Fxmss.Rom

open Scheme Notions
open ShrincsSecurity.Scheme.Structure (leafIds)
open ShrincsSecurity.Scheme.Grinding (GrindComplete)

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

/-! ## The least counter of `O_Prop` is the scheme's counter -/

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] in
/-- **Remark 4.8**: when the scheme's counter search succeeds with counter `c`, the least counter
`i ∈ ℕ` of the S-TCR(Prop) oracle (`H_grind` reading `i mod 2^c`) is `c`. -/
theorem leastCounter_thGrind {pk : pr.PkSeed} {id : LeafId} {md : pr.Digest} {d : pr.Y}
    {c : Fin (2 ^ P.c)} (hg : WotsC.grind pr pk id md = some (d, c)) :
    leastCounter (thGrind pr) (targetSumProp pr) pk (SfAdrs.grindAdrs id).toAdrs md =
      some c.val := by
  classical
  obtain ⟨rfl, hT, hmin⟩ := (WotsC.grind_eq_some_iff pr).1 hg
  have heval : ∀ n (hn : n < 2 ^ P.c), (thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (md, n) =
      WotsC.encode pr pk id md ⟨n, hn⟩ := fun n hn => by
    simp only [thGrind, TweakableHash.ofFun, WotsC.encode, Nat.mod_eq_of_lt hn]
  have hex : ∃ i, targetSumProp pr ((thGrind pr).eval pk (SfAdrs.grindAdrs id).toAdrs (md, i)) =
      true := ⟨c.val, by rw [heval c.val c.isLt]; simpa [targetSumProp] using hT⟩
  unfold leastCounter
  rw [dite_eq_left_of_eq_true (eq_true hex), Option.some.injEq, Nat.find_eq_iff]
  refine ⟨by rw [heval c.val c.isLt]; simpa [targetSumProp] using hT, fun n hn => ?_⟩
  rw [heval n (hn.trans c.isLt)]
  simpa [targetSumProp] using hmin ⟨n, hn.trans c.isLt⟩ hn

/-! ## The reduction `B₂` (Algorithm 6) -/

/-- The challenge pairs `(ADRS^g_j, y_j)` of the anchors, in the canonical order. -/
noncomputable def grindPairs {State : Type} (d : Setup pr Msg State) :
    List (SLHDSA.Adrs × pr.Digest) :=
  (anchorList P d.S).map fun id => ((SfAdrs.grindAdrs id).toAdrs, digOf pr d.ys id)

open scoped Classical in
/-- The first-stage queries of `B₂`: `O_Prop(ADRS^g_j, y_j)` for every anchor of a valid
structure. -/
noncomputable def B2queries (L : ℕ) {State : Type} (d : Setup pr Msg State) :
    OracleComp (StcrSpec (probGrind pr L)) Unit :=
  if d.S.TreeValid P.hsf then stcrQueries (probGrind pr L) (grindPairs pr Msg d) else pure ()

open scoped Classical in
/-- The targets recorded by `B₂`'s first stage. -/
noncomputable def B2targets (L : ℕ) {State : Type} (d : Setup pr Msg State) (pk : pr.PkSeed) :
    List ((SLHDSA.Adrs × pr.Digest) × (pr.Y × ℕ)) :=
  if d.S.TreeValid P.hsf then (grindPairs pr Msg d).filterMap (stcrRecord (probGrind pr L) pk)
  else []

/-- The candidate read off a forgery: `(ADRS^g_{(z*, i*)}, y*, c*)`. -/
def B2cands (_H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr) :
    List (SLHDSA.Adrs × pr.Digest × ℕ) :=
  [((SfAdrs.grindAdrs idf).toAdrs, yf, w.wots.ctr.val)]

/-- The extraction of `B₂`: search the recorded targets for the candidate of the forgery. -/
noncomputable def B2extract (L : ℕ) {State : Type} (d : Setup pr Msg State) (pk : pr.PkSeed)
    (o : Option (Transcript pr Msg × Honest pr)) : ℕ × pr.Digest × ℕ :=
  stcrFind ((probGrind pr L).th.eval pk) (B2targets pr Msg L d pk)
    (forgeryCands pr Msg (B2cands pr) o)

/-- **The reduction `B₂` of Claim 4.3** (Algorithm 6) against S-TCR(Prop) of `H_grind ∈ Th_λ`
with `L` targets. -/
noncomputable def B2 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Notions.STCRAdversary (probGrind pr L) :=
  mkSTcrAdv (probGrind pr L) (setupHyb pr Msg slKeygen A.toFxmssAdversary) (B2queries pr Msg L)
    fun d pk => B2extract pr Msg L d pk <$>
      stageHyb pr Msg slKeygen A.toFxmssAdversary (betaOf pr 0 pk d.u) d pk

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg]
  [Nontrivial Msg] in
/-- The first stage of `B₂` records `B2targets`: the tweaks are pairwise distinct and there are at
most `L` of them. -/
theorem B2queries_run {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (pk : pr.PkSeed) (d : Setup pr Msg A.State)
    (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary)) :
    (simulateQ (STCR_oracles (probGrind pr L) pk) (B2queries pr Msg L d)).run ([], []) =
      pure ((), (B2targets pr Msg L d pk, [])) := by
  classical
  unfold B2queries B2targets
  split_ifs with hS
  · have h := stcrQueries_run (probGrind pr L) pk (grindPairs pr Msg d) [] []
      (by simpa [grindPairs] using setupHyb_length_anchorList_le pr Msg slKeygen A hd hS)
      (by
        simp only [List.map_nil, List.nil_append, grindPairs, List.map_map]
        exact (nodup_anchorList d.S).map fun a b h => SfAdrs.grindAdrs_inj.1 h)
      (by simp)
    simpa using h
  · simp

/-! ## Claim 4.3 -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] in
/-- **Claim 4.3** (`F.2 → F.3`): the abort event of `F.3` (a forged digest `y* ≠ y_j` at a signed
anchor with the honest encoded digest `H_grind(y*, c*) = H_grind(y_j, c_j)`) in the block game
`F.3_0 = F.2` is bounded by the S-TCR(Prop) success of `B₂` against `H_grind ∈ Th_λ` with `L`
targets, `Prop` the WOTS+C target sum. -/
theorem claim_4_3 (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEvent Honest.E3 o] ≤
      Notions.STCR_Succ (B2 pr Msg slKeygen A) := by
  classical
  rw [B2, mkSTcrAdv_succ (probGrind pr L) _ _ _ (fun d pk => B2targets pr Msg L d pk)
    (fun _ _ => []) fun pk d hd => B2queries_run pr Msg slKeygen A pk d hd]
  refine (prEvent_gameHyb_le pr Msg slKeygen 0 A.toFxmssAdversary Honest.E3
    (B2extract pr Msg L) (fun d pk out => STCR_IsCollision (probGrind pr L) pk
      (B2targets pr Msg L d pk) out = true) ?_).trans le_rfl
  intro pk d hd hS tr w hw hE
  obtain ⟨hid, hne, henc⟩ := hE
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  unfold B2extract
  rw [forgeryCands_some pr Msg _ hw]
  refine stcrIsCollision_stcrFind (probGrind pr L) pk _ _
    ⟨_, List.mem_singleton_self _, (((SfAdrs.grindAdrs tr.idf).toAdrs, digOf pr d.ys tr.idf),
      ((thGrind pr).eval pk (SfAdrs.grindAdrs tr.idf).toAdrs (digOf pr d.ys tr.idf, c.val), c.val)),
      ?_, rfl, ?_, hne⟩
  · simp only [B2targets, hS, ↓reduceIte, List.mem_filterMap]
    refine ⟨((SfAdrs.grindAdrs tr.idf).toAdrs, digOf pr d.ys tr.idf),
      List.mem_map.2 ⟨tr.idf, mem_anchorList.2 hid, rfl⟩, ?_⟩
    simp [stcrRecord, leastCounter_thGrind pr hg]
  · have h1 := hon_encoded pr (S := d.S) (β := betaOf pr 0 pk d.u) hg
    have h2 : (thGrind pr).eval pk (SfAdrs.grindAdrs tr.idf).toAdrs (digOf pr d.ys tr.idf, c.val) =
        WotsC.encode pr pk tr.idf (digOf pr d.ys tr.idf) c := by
      simp [thGrind, TweakableHash.ofFun, WotsC.encode, Nat.mod_eq_of_lt c.isLt]
    have h3 : (thGrind pr).eval pk (SfAdrs.grindAdrs tr.idf).toAdrs (tr.yf, w.wots.ctr.val) =
        WotsC.encode pr pk tr.idf tr.yf w.wots.ctr := by
      simp [thGrind, TweakableHash.ofFun, WotsC.encode, Nat.mod_eq_of_lt w.wots.ctr.isLt]
    rw [h2, h3]
    exact h1.symm.trans henc.symm

end ShrincsSecurity.Fxmss.Rom

end
