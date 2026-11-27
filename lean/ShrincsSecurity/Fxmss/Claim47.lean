module

public import ShrincsSecurity.Fxmss.TcrCommon

/-!
# Claim 4.7: the hop `F.6 → F.7` (SM-TCR of `Th_lsf`)

`SHRINCS-Security-Analysis.pdf`, Section 4.7, **Claim 4.7** (txt lines 3705–3726) and
**Algorithm 10** (the reduction `B₆`, lines 8110–8171).

`B₆` is built with `mkTcrAdv`:
* **first stage**: the setup of the block games (`setupHyb`), then, for every anchor `j` (in the
  canonical order `anchorList`): each chain `ch < lsf` from the uniform value `u_{j,ch}` through
  the **collection oracle** (`w − 1` chained queries to the member `F` of `Th_λ` at the
  `SF_WOTS_C_HASH` tweaks, `iterColl`), giving the uncompressed public key
  `pk_j = (c_{0,w−1}(u_{j,ch}))_{ch}`, and then the challenge query `O(ADRS^pk_j, pk_j)`; at most
  `L` targets, at pairwise distinct `SF_WOTS_C_PK` tweaks, none of which the collection queries
  touch;
* **second stage**: with `PK.seed` revealed, it runs the signing phase of the block game
  (`stageHyb`) itself and searches the forged uncompressed public key at `ADRS^pk_{(z*,i*)}`
  against its targets (`tcrFind`).

The event `E7` (at a signed anchor, a forged uncompressed public key different from the honest
one with the same `Th_lsf` compression) is then an SM-TCR collision, because under
Conjecture 3.1 the honest uncompressed public key is `c_{0,w−1}(u)` (`hon0_tops`).

## Deviations from the paper
* The event is measured in the block game `F.3_0` (secret key `u`), as fixed by the hybrid
  structure of the formalisation (`gameHyb 0`), rather than in `F.6`; the chains are therefore
  built from `u` at position `0`, and no grinding is needed in the first stage.
* The tree nodes, `PK.sl` and the signatures are computed in the second stage from `PK.seed`
  (Assumption 4.1) instead of through the collection oracle before the parameter is revealed
  (Algorithm 10, lines 12–13); time accounting is replaced by this explicit construction. The
  collection queries are the `L · lsf · (w − 1)` chain steps.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal TweakableHash

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

/-! ## The reduction `B₆` (Algorithm 10) -/

/-- `Y` as the message type of the member `F` of `Th_λ`. -/
def fEmb (L : ℕ) : pr.Y → (probTcrLsf pr L).thColl.Msg (some Primitives.Member.F) := fun y => y

/-- The chain `(id, ch)` from `x` through the collection oracle: `w − 1` chained queries to the
member `F` of `Th_λ`. -/
noncomputable def B6chain (L : ℕ) (id : LeafId) (ch : ℕ) (x : pr.Y) :
    OracleComp (TcrSpec (probTcrLsf pr L)) pr.Y :=
  iterColl (probTcrLsf pr L) (some Primitives.Member.F) (fEmb pr L) (chainTw id ch) 0 x (P.w - 1)

/-- The work of `B₆` at one anchor: the chains through the collection oracle, then the challenge
query `O(ADRS^pk, (pk_0, …, pk_{lsf−1}))`. -/
noncomputable def B6job (L : ℕ) {State : Type} (d : Setup pr Msg State) (id : LeafId) :
    OracleComp (TcrSpec (probTcrLsf pr L)) PUnit := do
  let l ← (List.range P.lsf).mapM fun ch => B6chain pr L id ch (skOf pr d.S d.u id ch)
  let _ ← tcrChal (probTcrLsf pr L)
    ((SfAdrs.pkAdrs id).toAdrs, Vector.ofFn fun ch : Fin P.lsf => l.getD ch.val default)
  pure PUnit.unit

open scoped Classical in
/-- The first-stage queries of `B₆`: the work of every anchor of a valid structure. -/
noncomputable def B6queries (L : ℕ) {State : Type} (d : Setup pr Msg State) :
    OracleComp (TcrSpec (probTcrLsf pr L)) Unit :=
  if d.S.TreeValid P.hsf then (anchorList P d.S).forM (B6job pr Msg L d) else pure ()

/-- The target of the anchor `id`: `(ADRS^pk, c_{0,w−1}(u_{id,·}))`. -/
def B6target (pk : pr.PkSeed) {S : Structure} (u : SkIdx P S → pr.Y) (id : LeafId) :
    SLHDSA.Adrs × Vector pr.Y P.lsf :=
  ((SfAdrs.pkAdrs id).toAdrs, WotsC.pkTops pr pk id (skOf pr S u id))

/-- The collection tweaks spent at the anchor `id`: its chain tweaks. -/
def B6collTws (P : Params) (id : LeafId) : List SLHDSA.Adrs :=
  (List.range P.lsf).flatMap fun ch => (List.range (P.w - 1)).map fun n => chainTw id ch (0 + n)

open scoped Classical in
/-- The targets recorded by `B₆`'s first stage. -/
noncomputable def B6targets {State : Type} (d : Setup pr Msg State) (pk : pr.PkSeed) :
    List (SLHDSA.Adrs × Vector pr.Y P.lsf) :=
  if d.S.TreeValid P.hsf then (anchorList P d.S).map (B6target pr pk d.u) else []

open scoped Classical in
/-- The collection tweaks spent by `B₆`'s first stage. -/
noncomputable def B6collTargets {State : Type} (d : Setup pr Msg State) : List SLHDSA.Adrs :=
  if d.S.TreeValid P.hsf then (anchorList P d.S).flatMap (B6collTws P) else []

/-- The candidate read off a forgery: the forged uncompressed public key at `ADRS^pk_{(z*,i*)}`. -/
def B6cands (H : Honest pr) (idf : LeafId) (yf : pr.Digest) (w : Scheme.Fxmss.Sig pr) :
    List (SLHDSA.Adrs × Vector pr.Y P.lsf) :=
  [((SfAdrs.pkAdrs idf).toAdrs, H.fTops idf yf w)]

/-- The extraction of `B₆`: search the Stage-1 recorded targets `savedQ` directly (computable). -/
def B6extract (savedQ : List (SLHDSA.Adrs × Vector pr.Y P.lsf)) (pk : pr.PkSeed)
    (o : Option (Transcript pr Msg × Honest pr)) : ℕ × Vector pr.Y P.lsf :=
  tcrFind (pr.ThLsf pk) savedQ (forgeryCands pr Msg (B6cands pr) o)

/-- **The reduction `B₆` of Claim 4.7** (Algorithm 10) against SM-TCR of `Th_lsf ∈ Th_λ` with
`L` targets. -/
noncomputable def B6 {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    SM_DT_TCR_Adversary (probTcrLsf pr L) :=
  mkTcrAdv (probTcrLsf pr L) (setupHyb pr Msg slKeygen A.toFxmssAdversary) (B6queries pr Msg L)
    fun st pk => B6extract pr Msg st.2 pk <$>
      stageHyb pr Msg slKeygen A.toFxmssAdversary (betaOf pr 0 pk st.1.u) st.1 pk

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest]
  [Inhabited pr.Digest] [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg] in
/-- The work of `B₆` at one anchor, from a state whose challenge tweaks (with the new one) are
pairwise distinct and avoid the collection tweaks: the chains are answered and the target is
recorded. -/
theorem B6job_run (L : ℕ) {State : Type} (d : Setup pr Msg State) (pk : pr.PkSeed) (id : LeafId)
    (qs : List (SLHDSA.Adrs × Vector pr.Y P.lsf)) (tws : List SLHDSA.Adrs)
    (hcap : qs.length + 1 ≤ L) (hnd : ((qs ++ [B6target pr pk d.u id]).map Prod.fst).Nodup)
    (hdis : ∀ t ∈ (qs ++ [B6target pr pk d.u id]).map Prod.fst, t ∉ tws ++ B6collTws P id) :
    (simulateQ (SM_DT_TCR_oracles (probTcrLsf pr L) pk) (B6job pr Msg L d id)).run (qs, tws) =
      pure (PUnit.unit, (qs ++ [B6target pr pk d.u id], tws ++ B6collTws P id)) := by
  unfold B6job
  rw [simulateQ_bind, StateT.run_bind, tcr_mapM_run (probTcrLsf pr L) pk _
    (fun ch => WotsC.chain pr pk id ch (skOf pr d.S d.u id ch) 0 (P.w - 1))
    (fun ch => (List.range (P.w - 1)).map fun n => chainTw id ch (0 + n)) qs (List.range P.lsf)
    (fun ch hch tws' => by
      rw [B6chain, iterColl_run (probTcrLsf pr L) pk _ _ _ 0 _ _ qs tws' fun e he n hn h => ?_,
        iterVal_chain pr pk id ch (fun t y => (probTcrLsf pr L).thColl.eval
          (some Primitives.Member.F) pk t (fEmb pr L y)) fun _ _ => rfl]
      refine hdis e.1 (by simp [List.mem_map_of_mem he]) ?_
      rw [h]
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ch, hch,
        List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩⟩)) tws, pure_bind]
  have hfresh : TweakFresh Prod.fst qs (tws ++ B6collTws P id) (SfAdrs.pkAdrs id).toAdrs := by
    refine ⟨(not_tweakReserved_iff _ _ _).2 fun e he h => ?_, hdis _ (by simp [B6target])⟩
    simp only [List.map_append, List.map_cons, List.map_nil] at hnd
    exact (List.nodup_append.1 hnd).2.2 _ (List.mem_map_of_mem he) _ (by simp [B6target]) h
  simp only [simulateQ_bind, StateT.run_bind, tcrChal_run]
  simp only [B6collTws] at hfresh ⊢
  rw [SM_DT_TCR_challengeOracle_run_of_fresh (by simpa using hcap) hfresh]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure]
  have hv : (Vector.ofFn fun ch : Fin P.lsf => ((List.range P.lsf).map fun ch =>
      WotsC.chain pr pk id ch (skOf pr d.S d.u id ch) 0 (P.w - 1)).getD ch.val default) =
      WotsC.pkTops pr pk id (skOf pr d.S d.u id) := by
    simp only [WotsC.pkTops]
    congr 1
    funext ch
    simp [List.getD_eq_getElem?_getD]
  rw [hv]
  rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest] [Fintype Msg]
  [Inhabited pr.Digest] [Nontrivial Msg] in
/-- The first stage of `B₆` records `B6targets`: at most `L` pairwise distinct `SF_WOTS_C_PK`
tweaks, disjoint from the chain tweaks spent on the collection oracle. -/
theorem B6queries_run {qs qh₁ qh₂ L : ℕ} (A : Forger pr Msg slKeygen qs qh₁ qh₂ L)
    (pk : pr.PkSeed) (d : Setup pr Msg A.State)
    (hd : d ∈ support (setupHyb pr Msg slKeygen A.toFxmssAdversary)) :
    (simulateQ (SM_DT_TCR_oracles (probTcrLsf pr L) pk) (B6queries pr Msg L d)).run ([], []) =
      pure ((), (B6targets pr Msg d pk, B6collTargets pr Msg d)) := by
  classical
  unfold B6queries B6targets B6collTargets
  split_ifs with hS
  · have h := tcr_forM_run (probTcrLsf pr L) pk (anchorList P d.S) (B6job pr Msg L d)
      (fun id => [B6target pr pk d.u id]) (B6collTws P)
      (fun id _ qs' tws hcap hnd hdis => B6job_run pr Msg L d pk id qs' tws (by simpa using hcap)
        hnd hdis)
      [] []
      (by simpa using setupHyb_length_anchorList_le pr Msg slKeygen A hd hS)
      (by
        simp only [List.nil_append, List.map_flatMap, List.map_cons, List.map_nil, B6target]
        rw [← List.map_eq_flatMap]
        exact (nodup_anchorList d.S).map fun a b h => SfAdrs.pkAdrs_inj.1 h)
      (by
        simp only [List.nil_append, List.map_flatMap, List.map_cons, List.map_nil, B6target,
          List.mem_flatMap, List.mem_singleton, B6collTws, List.mem_map, List.mem_range]
        rintro t ⟨id, -, rfl⟩ ⟨id', -, ch, -, n, -, h⟩
        exact SfAdrs.chainAdrs_ne_pkAdrs id' id ch _ h)
    rw [← List.map_eq_flatMap] at h
    simpa using h
  · simp

/-! ## Claim 4.7 -/

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [Fintype Msg] in
/-- **Claim 4.7** (`F.6 → F.7`): the abort event `E7` (at a signed anchor, a forged uncompressed
WOTS+C public key different from the honest one with the same `Th_lsf` compression) in the block
game `F.3_0` is bounded by the SM-TCR advantage of `B₆` against `Th_lsf ∈ Th_λ` with `L`
targets. -/
theorem claim_4_7 (hP : P.Valid) (hgc : GrindComplete pr) {qs qh₁ qh₂ L : ℕ}
    (A : Forger pr Msg slKeygen qs qh₁ qh₂ L) :
    Pr{let o ← gameHyb pr Msg slKeygen 0 A.toFxmssAdversary}[HybEvent Honest.E7 o] ≤
      SM_DT_TCR_Advantage (B6 pr Msg slKeygen A) := by
  classical
  rw [B6, mkTcrAdv_advantage (probTcrLsf pr L) _ _ _ (fun d pk => B6targets pr Msg d pk)
    (fun d _ => B6collTargets pr Msg d) fun pk d hd => B6queries_run pr Msg slKeygen A pk d hd]
  refine (prEvent_gameHyb_le pr Msg slKeygen 0 A.toFxmssAdversary Honest.E7
    (fun d pk => B6extract pr Msg (B6targets pr Msg d pk) pk)
    (fun d pk out => tcrWin (probTcrLsf pr L) pk
      (B6targets pr Msg d pk) out = true) ?_).trans le_rfl
  intro pk d hd hS tr w hw hE
  obtain ⟨hid, hne, heq⟩ := hE
  obtain ⟨c, hg⟩ := grind_eq_some pr hP hgc hS hid pk (digOf pr d.ys tr.idf)
  have ht := hon0_tops pr (u := d.u) hg
  unfold B6extract
  rw [forgeryCands_some pr Msg _ hw]
  refine tcrWin_tcrFind (probTcrLsf pr L) pk _ _ ⟨_, List.mem_singleton_self _,
    B6target pr pk d.u tr.idf, ?_, rfl, by rw [B6target, ← ht]; exact hne,
    by rw [B6target, ← ht]; exact heq⟩
  simp only [B6targets, hS, ↓reduceIte]
  exact List.mem_map.2 ⟨tr.idf, mem_anchorList.2 hid, rfl⟩

end ShrincsSecurity.Fxmss.Rom

end
