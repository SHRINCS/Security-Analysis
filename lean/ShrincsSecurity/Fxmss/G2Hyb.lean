module

public import ShrincsSecurity.Fxmss.Claim42

/-!
# `F.2` with presampled digests is the block game `gameHyb 0`

`SHRINCS-Security-Analysis.pdf`, Section 4.7, the game `F.2` (txt lines 3279–3290): "the
challenger pre-samples, at setup, `q_s` uniformly random digests `y_1, …, y_{q_s}`, one per
signing leaf of the committed structure, … and assigns `y_i` to the `i`-th leaf. On the query
naming the leaf … the challenger samples `R_i`, reprograms the random oracle so that
`H_msg^sf(R_i, …) := y_i`, uses `y_i` as the digest".

`gameG2` is `F.2` lazily: the digest of a signing query is drawn fresh when the query is answered.
`gameHyb 0` is `F.2` with the digests presampled per anchor (`Setup.ys`) and the honest data
precomputed from the setup (`hon`). They have the same output distribution
(`gameG2_evalDistEq_gameHyb`), hence the same success probability (`gameG2_eq_gameHyb`):

* **Presampling.** Each anchor is signed at most once, so a fresh digest drawn when the anchor is
  signed is a presampled digest read at that point. The eager game carries the presampled table in
  its state; the randomized state map `κ` completes the digests already consumed by the lazy game
  with a fresh uniform table (`fillYs`), and every step commutes with `κ` (uniform-cell
  resampling, `Repro.resample`). The induction is `run_evalDistEq_of_step`, the state-returning
  form of `Repro.run'_evalDistEq_of_step`.
* **Sample order.** `gameHyb` draws `y` and `u` before `PK.sl`; `gameG2` draws the secret key
  (`f`, playing the role of `u`), then `PK.sl`, and the digests lazily.
* **Pure identities.** With blocks `c_{0,a}(u)` (`betaOf 0`), the honest anchor values are the
  WOTS+C public keys of the secret key `u` (`hon_leafVal`), so `PK.sf` is the FXMSS root of `u`
  (`hon_pkSf`), and the precomputed signature of an anchor is `FXMSS.sign` of its digest
  (`hon_sig`); this holds also for a failed counter search, by construction of `hon`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace ShrincsSecurity.Fxmss.Rom

open Scheme
open ShrincsSecurity.Scheme.Structure (leafIds)

namespace Claim42

/-! ## Generic: simulation through a randomized state map, with the final state -/

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σL σE α : Type}

/-- **Simulation through a randomized state map, keeping the final state.** If drawing an eager
state from `κ sL` and taking one eager step is equal in distribution to taking one lazy step and
then drawing the eager state from `κ`, for every query and lazy state, then the eager simulation
started from `κ sL` is the lazy simulation started from `sL` followed by `κ` on its final state. -/
theorem run_evalDistEq_of_step
    (implL : QueryImpl spec (StateT σL ProbComp)) (implE : QueryImpl spec (StateT σE ProbComp))
    (κ : σL → ProbComp σE)
    (hstep : ∀ t sL, (κ sL >>= fun sE => (implE t).run sE) =ᵈ
      ((implL t).run sL >>= fun z => (z.1, ·) <$> κ z.2))
    (oa : OracleComp spec α) (sL : σL) :
    (κ sL >>= fun sE => (simulateQ implE oa).run sE) =ᵈ
      ((simulateQ implL oa).run sL >>= fun z => (z.1, ·) <$> κ z.2) := by
  induction oa using OracleComp.inductionOn generalizing sL with
  | pure a => simp [map_eq_bind_pure_comp]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    calc (κ sL >>= fun sE => (implE t).run sE >>= fun z => (simulateQ implE (k z.1)).run z.2)
        = ((κ sL >>= fun sE => (implE t).run sE) >>= fun z =>
            (simulateQ implE (k z.1)).run z.2) := by rw [bind_assoc]
      _ =ᵈ (((implL t).run sL >>= fun z => (z.1, ·) <$> κ z.2) >>= fun z =>
            (simulateQ implE (k z.1)).run z.2) := EvalDistEq.bind_left (hstep t sL) _
      _ = ((implL t).run sL >>= fun z => κ z.2 >>= fun sE =>
            (simulateQ implE (k z.1)).run sE) := by simp [bind_assoc, bind_map_left]
      _ =ᵈ ((implL t).run sL >>= fun z => (simulateQ implL (k z.1)).run z.2 >>= fun w =>
            (w.1, ·) <$> κ w.2) :=
          EvalDistEq.bind_right _ fun z => ih z.1 z.2
      _ = _ := by simp [bind_assoc]

end Generic

end Claim42

variable {P : Params} (pr : Primitives P) (Msg : Type)
  [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Inhabited pr.Y]
  [Fintype pr.PkSeed] [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed]
  [Fintype pr.Digest] [DecidableEq pr.Digest] [SampleableType pr.Digest] [Inhabited pr.Digest]
  [Fintype Msg] [DecidableEq Msg] [Nontrivial Msg]
  (slKeygen : pr.PkSeed → ProbComp pr.Y)

namespace Claim42

/-! ## Pure identities of the honest data with blocks `c_{0,a}(u)` -/

section Pure

variable {pr}

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- The block source of hybrid `0` reveals `c_{0,a}(sk)`. -/
theorem betaOf_zero {S : Structure} (pk : pr.PkSeed) (u : SkIdx P S → pr.Y) (id : LeafId)
    (ch a : ℕ) : betaOf pr 0 pk u id ch a = WotsC.chain pr pk id ch (skOf pr S u id ch) 0 a := by
  simp [betaOf, blockVal]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- In hybrid `0` the block signature is the WOTS+C signature of the secret key. -/
theorem blockSig_zero {S : Structure} (pk : pr.PkSeed) (u : SkIdx P S → pr.Y) (id : LeafId)
    (d : pr.Y) (c : Fin (2 ^ P.c)) :
    blockSig pr (betaOf pr 0 pk u) id d c = WotsC.signWith pr pk id (skOf pr S u id) d c := by
  simp [blockSig, WotsC.signWith, WotsC.signChains, betaOf_zero]

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- **The anchor values of hybrid `0` are the WOTS+C public keys of `u`**, whatever the digests
(also for a failed counter search). -/
theorem hon_leafVal (S : Structure) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (u : SkIdx P S → pr.Y) :
    (hon pr S pk dig (betaOf pr 0 pk u)).leafVal = Scheme.Fxmss.leaf pr pk (skOf pr S u) := by
  funext id
  simp only [hon, Scheme.Fxmss.leaf, WotsC.pkGen]
  split
  · rw [blockSig_zero, WotsC.topsFromSig_signWith]
  · congr 1

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- **`PK.sf` of hybrid `0` is the FXMSS root of `u`.** -/
@[simp] theorem hon_pkSf (S : Structure) (pk : pr.PkSeed) (dig : LeafId → pr.Digest)
    (u : SkIdx P S → pr.Y) :
    (hon pr S pk dig (betaOf pr 0 pk u)).pkSf = pkSfOf pr S pk (skOf pr S u) := by
  simp only [Honest.pkSf, Honest.value, hon_leafVal, pkSfOf, Scheme.Fxmss.root,
    Scheme.Fxmss.treeNode]
  rfl

omit [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y] [Fintype pr.PkSeed]
  [DecidableEq pr.PkSeed] [SampleableType pr.PkSeed] [Fintype pr.Digest] [DecidableEq pr.Digest]
  [SampleableType pr.Digest] [Inhabited pr.Digest] in
/-- **The precomputed signature of an anchor in hybrid `0` is `FXMSS.sign` of its digest.** -/
theorem hon_sig {S : Structure} (hS : S.TreeValid P.hsf) (pk : pr.PkSeed)
    (dig : LeafId → pr.Digest) (u : SkIdx P S → pr.Y) {id : LeafId}
    (hid : id ∈ leafIds P.hsf S) :
    (hon pr S pk dig (betaOf pr 0 pk u)).sig id =
      Scheme.Fxmss.sign pr S pk (skOf pr S u) (dig id) id := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hid
  have hz : (v.toLeafId P.hsf).height ≤ P.hsf := by simp [Node.toLeafId]
  have hA : Node.ofLeafId P.hsf (v.toLeafId P.hsf) ∈ S.anchors := by
    rw [Node.ofLeafId_toLeafId (hS.anchor_depth_le v hv)]; exact hv
  simp only [Honest.sig, Scheme.Fxmss.sign, hz, hA, and_self, ↓reduceIte, WotsC.sign,
    hon_leafVal]
  simp only [hon]
  cases WotsC.grind pr pk (v.toLeafId P.hsf) (dig (v.toLeafId P.hsf)) with
  | none => rfl
  | some dc => simp [blockSig_zero]

end Pure

/-! ## Presampling the digests -/

section Presample

variable {pr Msg}

/-- The presampled table read off a lazy state: at a used anchor, the digest it was signed with;
elsewhere, `g`. -/
def fillYs {S : Structure} (s : St pr Msg) (g : Anchor P S → pr.Digest) :
    Anchor P S → pr.Digest :=
  fun a => if a.1 ∈ s.used then ((s.recs a.1).map Rec.digest).getD default else g a

/-- The randomized state map: complete the consumed digests with a uniform table. -/
noncomputable def kappa (S : Structure) (s : St pr Msg) :
    ProbComp (St pr Msg × (Anchor P S → pr.Digest)) :=
  (fun g => (s, fillYs s g)) <$> ($ᵗ (Anchor P S → pr.Digest))

/-- The eager form of `F.2`: the presampled table is part of the state, and the honest data is
computed from it. -/
noncomputable def implE (K : Keys pr) (u : SkIdx P K.S → pr.Y) :
    QueryImpl (fullSpec pr Msg) (StateT (St pr Msg × (Anchor P K.S → pr.Digest)) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1, (z.2, p.2))) <$>
    (implHyb pr Msg K (hon pr K.S K.pk (digOf pr p.2) (betaOf pr 0 K.pk u)) t).run p.1

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Y] [DecidableEq pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Y] [SampleableType pr.Digest] [DecidableEq Msg] in
theorem fillYs_congr {S : Structure} {s s' : St pr Msg} (hu : s'.used = s.used)
    (hr : s'.recs = s.recs) : (fillYs s' : (Anchor P S → pr.Digest) → _) = fillYs s := by
  funext g a
  simp [fillYs, hu, hr]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Y] [DecidableEq pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Y] [SampleableType pr.Digest] [DecidableEq Msg] in
/-- After signing the unused anchor `a` with digest `d`, the table read off the state is the
previous one with `d` at `a`. -/
theorem fillYs_sign {S : Structure} (s : St pr Msg) (c : (roSpec pr Msg).QueryCache)
    (q : Msg × LeafId) (R : pr.Y) (d : pr.Digest) (σ : Option (Scheme.Fxmss.Sig pr))
    (a : Anchor P S) (ha : a.1 = q.2) (hnot : q.2 ∉ s.used) (g : Anchor P S → pr.Digest) :
    fillYs (stSign { s with cache := c } q R d σ) g = fillYs s (Function.update g a d) := by
  funext a'
  by_cases h : a' = a
  · subst h
    simp [fillYs, stSign, ha, hnot]
  · have h' : a'.1 ≠ q.2 := fun e => h (Subtype.ext (e.trans ha.symm))
    simp [fillYs, stSign, h, h']

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [Inhabited pr.Digest] [DecidableEq pr.Digest] in
/-- A step of the coins or of the random oracle keeps the used leaves and the records. -/
theorem impl_inl_support (K : Keys pr)
    (dig : LeafId → RoIn pr Msg → StateT (St pr Msg) ProbComp pr.Digest)
    (sigOf : LeafId → pr.Digest → Option (Scheme.Fxmss.Sig pr)) (t : (spec pr Msg).Domain)
    (s : St pr Msg) (z) (hz : z ∈ support ((impl pr Msg K dig sigOf (.inl t)).run s)) :
    z.2.used = s.used ∧ z.2.recs = s.recs := by
  rcases t with n | x
  · simp [impl] at hz
    obtain ⟨_, rfl⟩ := hz
    exact ⟨rfl, rfl⟩
  · simp only [impl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hz
    rcases h : s.cache x with _ | d
    · rw [roStep_run_none h, support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact ⟨rfl, rfl⟩
    · rw [roStep_run_some h, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, rfl⟩

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [SampleableType pr.PkSeed] [Fintype pr.Y] [DecidableEq pr.Y] [SampleableType pr.Y]
  [Inhabited pr.Y] [DecidableEq pr.PkSeed] [DecidableEq pr.Digest] [DecidableEq Msg] in
/-- A step that is the same in both games and keeps the used leaves and records commutes with
`kappa`. -/
theorem kappa_step_same {S : Structure} {β : Type} (X : ProbComp (β × St pr Msg))
    (Y : St pr Msg × (Anchor P S → pr.Digest) →
      ProbComp (β × (St pr Msg × (Anchor P S → pr.Digest))))
    (s : St pr Msg) (hY : ∀ ys, Y (s, ys) = (fun z => (z.1, (z.2, ys))) <$> X)
    (hX : ∀ z ∈ support X, z.2.used = s.used ∧ z.2.recs = s.recs) :
    (kappa S s >>= Y) =ᵈ (X >>= fun z => (z.1, ·) <$> kappa S z.2) := by
  simp only [kappa, hY, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind]
  refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  rw [fillYs_congr (hX z hz).1 (hX z hz).2]
  exact EvalDistEq.rfl

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [DecidableEq pr.Y] [DecidableEq pr.PkSeed]
  [DecidableEq pr.Digest] [SampleableType pr.Y] [SampleableType pr.Digest] [DecidableEq Msg] in
theorem fillYs_of_not_mem {S : Structure} (s : St pr Msg) (g : Anchor P S → pr.Digest)
    (a : Anchor P S) (ha : a.1 ∉ s.used) : fillYs s g a = g a := by
  simp [fillYs, ha]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [Inhabited pr.Y] [SampleableType pr.PkSeed] [Inhabited pr.Digest] [SampleableType pr.Y]
  [DecidableEq pr.Digest] [SampleableType pr.Digest] in
theorem progStep_run (x : RoIn pr Msg) (d : pr.Digest) (s : St pr Msg) :
    (progStep pr Msg x d).run s = pure (d, { s with cache := s.cache.cacheQuery x d }) := rfl

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [SampleableType pr.PkSeed] [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **Every step of `F.2` commutes with presampling.** -/
theorem kappa_step (K : Keys pr) (hS : K.S.TreeValid P.hsf) (u : SkIdx P K.S → pr.Y)
    (t : (fullSpec pr Msg).Domain) (s : St pr Msg) :
    (kappa K.S s >>= fun sE => (implE K u t).run sE) =ᵈ
      ((implG2 pr Msg K (skOf pr K.S u) t).run s >>= fun z => (z.1, ·) <$> kappa K.S z.2) := by
  rcases t with t | q
  · exact kappa_step_same _ (fun sE => (implE K u (.inl t)).run sE) s (fun ys => rfl)
      (impl_inl_support K _ _ t s)
  by_cases h : q.2 ∈ leafIds P.hsf K.S ∧ q.2 ∉ s.used
  swap
  · refine kappa_step_same _ (fun sE => (implE K u (.inr q)).run sE) s (fun ys => ?_) ?_
    · simp only [implE, StateT.run_mk, implHyb, implG2, impl, QueryImpl.add_apply_inr,
        signStep_run_else K _ _ q s h]
    · simp only [implG2, impl, QueryImpl.add_apply_inr, signStep_run_else K _ _ q s h,
        support_pure, Set.mem_singleton_iff]
      rintro z rfl
      exact ⟨rfl, rfl⟩
  set a : Anchor P K.S := ⟨q.2, h.1⟩
  set sk := skOf pr K.S u
  set σ : pr.Digest → Option (Scheme.Fxmss.Sig pr) := fun d =>
    Scheme.Fxmss.sign pr K.S K.pk sk d q.2
  set s1 : pr.Y → pr.Digest → St pr Msg := fun R d =>
    stSign { s with cache := s.cache.cacheQuery (roIn pr Msg R K.pk K.pkSf q.2 q.1) d } q R d
      (σ d)
  set Φ : pr.Y → (Anchor P K.S → pr.Digest) →
      ProbComp (Option (Sig pr) × (St pr Msg × (Anchor P K.S → pr.Digest))) :=
    fun R g => pure (some (R, σ (g a)), (s1 R (g a), fillYs s g))
  have hE : ∀ ys, (implE K u (.inr q)).run (s, ys) =
      ($ᵗ pr.Y) >>= fun R => pure (some (R, σ (ys a)), (s1 R (ys a), ys)) := by
    intro ys
    have hsig := hon_sig hS K.pk (digOf pr ys) u h.1
    have hdig : digOf pr ys q.2 = ys a := dite_eq_left h.1
    rw [hdig] at hsig
    have hd : (hon pr K.S K.pk (digOf pr ys) (betaOf pr 0 K.pk u)).dig q.2 = ys a := hdig
    simp only [implE, StateT.run_mk, implHyb, impl, QueryImpl.add_apply_inr,
      signStep_run_fresh K _ _ q s h, progStep_run, map_bind, pure_bind, map_pure, hd, hsig]
    rfl
  have hL : (implG2 pr Msg K sk (.inr q)).run s =
      ($ᵗ pr.Y) >>= fun R => ($ᵗ pr.Digest) >>= fun d => pure (some (R, σ d), s1 R d) := by
    simp only [implG2, impl, QueryImpl.add_apply_inr, signStep_run_fresh K _ _ q s h,
      freshProgStep_run, bind_map_left]
    rfl
  calc (kappa K.S s >>= fun sE => (implE K u (.inr q)).run sE)
      = ($ᵗ (Anchor P K.S → pr.Digest)) >>= fun g => ($ᵗ pr.Y) >>= fun R => Φ R g := by
        simp only [kappa, bind_map_left, hE, Φ, fillYs_of_not_mem s _ a h.2]
    _ =ᵈ ($ᵗ pr.Y) >>= fun R => ($ᵗ (Anchor P K.S → pr.Digest)) >>= fun g => Φ R g :=
        EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ ($ᵗ pr.Y) >>= fun R => ($ᵗ pr.Digest) >>= fun d =>
          ($ᵗ (Anchor P K.S → pr.Digest)) >>= fun g => Φ R (Function.update g a d) :=
        EvalDistEq.bind_right _ fun R => (Repro.resample a (Φ R)).symm
    _ = ((implG2 pr Msg K sk (.inr q)).run s >>= fun z => (z.1, ·) <$> kappa K.S z.2) := by
        rw [hL]
        simp only [bind_assoc, pure_bind, kappa, Φ, Function.update_self, map_eq_bind_pure_comp,
          Function.comp_apply]
        refine bind_congr fun R => bind_congr fun d => bind_congr fun g => ?_
        rw [fillYs_sign s _ q R d (σ d) a rfl h.2 g]

omit [Fintype pr.Y] [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [SampleableType pr.PkSeed] [DecidableEq pr.Digest] in
/-- The eager game with table `ys` is the block game with the digests `ys`. -/
theorem implE_run (K : Keys pr) (u : SkIdx P K.S → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s : St pr Msg) (ys : Anchor P K.S → pr.Digest) :
    Prod.map id Prod.fst <$> (simulateQ (implE K u) oa).run (s, ys) =
      (simulateQ (implHyb pr Msg K (hon pr K.S K.pk (digOf pr ys) (betaOf pr 0 K.pk u))) oa).run
        s :=
  map_run_simulateQ_eq_of_query_map_eq_inv' (implE K u) _ (fun p => p.2 = ys) Prod.fst
    (fun t p hp z hz => by
      simp only [implE, StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact hp)
    (fun t p hp => by
      obtain ⟨s, rfl⟩ : ∃ s, p = (s, ys) := ⟨p.1, Prod.ext rfl hp⟩
      simp [implE, Functor.map_map])
    oa (s, ys) rfl

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Nontrivial Msg]
  [SampleableType pr.PkSeed] [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **Presampling the digests of `F.2`**: the block game with uniform presampled digests is the
lazy `F.2`, from any state with no used leaf. -/
theorem presample (K : Keys pr) (hS : K.S.TreeValid P.hsf) (u : SkIdx P K.S → pr.Y) {α : Type}
    (oa : OracleComp (fullSpec pr Msg) α) (s₀ : St pr Msg) (h₀ : s₀.used = []) :
    (($ᵗ (Anchor P K.S → pr.Digest)) >>= fun ys =>
        (simulateQ (implHyb pr Msg K (hon pr K.S K.pk (digOf pr ys) (betaOf pr 0 K.pk u))) oa).run
          s₀) =ᵈ
      (simulateQ (implG2 pr Msg K (skOf pr K.S u)) oa).run s₀ := by
  have h := (run_evalDistEq_of_step (implG2 pr Msg K (skOf pr K.S u)) (implE K u) (kappa K.S)
    (kappa_step K hS u) oa s₀).map (Prod.map id Prod.fst)
  have hf : ∀ g : Anchor P K.S → pr.Digest, fillYs s₀ g = g := fun g => by
    funext a; simp [fillYs, h₀]
  simp only [kappa, bind_map_left, map_bind, implE_run, hf] at h
  refine h.trans ?_
  refine (EvalDistEq.bind_right _ fun z => ?_).trans (evalDistEq_of_eq (bind_pure _))
  simp only [Functor.map_map, Prod.map_apply, id_eq]
  exact EvalDistEq.map_const _ _

end Presample

/-! ## `F.2` lazily and with presampled digests -/

omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **`F.2` with fresh digests is `F.2` with presampled digests** (`gameHyb 0`, honest data
dropped), as distributions of transcripts. -/
theorem gameG2_evalDistEq_gameHyb {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    gameG2 pr Msg slKeygen A =ᵈ Option.map Prod.fst <$> gameHyb pr Msg slKeygen 0 A := by
  unfold gameG2 gameHyb setupHyb
  simp only [bind_assoc, pure_bind, map_bind]
  refine EvalDistEq.bind_right _ fun pk => EvalDistEq.bind_right _ fun z => ?_
  unfold stageG stageHyb
  by_cases hv : z.1.1.TreeValid P.hsf
  swap
  · simp only [hv, not_false_eq_true, ↓reduceIte, map_pure, Option.map_none]
    exact ((EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_const _ _)).symm
  simp only [hv, not_true_eq_false, ↓reduceIte, map_bind, map_pure, Option.map_some, hon_pkSf]
  refine EvalDistEq.symm ?_
  refine (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun u => ?_)
  refine (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun pkSl => ?_)
  have h := (presample (K := ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 u)⟩) hv u
    (stage2Prog pr Msg slKeygen A z.1.2 ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 u)⟩)
    (St.init pr Msg z.2) rfl).map
      (fun r => some (Transcript.ofRun pr Msg
        ⟨z.1.1, pk, pkSl, pkSfOf pr z.1.1 pk (skOf pr z.1.1 u)⟩ r))
  simp only [map_bind] at h
  simp only [bind_pure_comp]
  exact h

end Claim42

open Claim42 in
omit [Fintype pr.PkSeed] [Fintype pr.Digest] [Fintype Msg] [Fintype pr.Y] [DecidableEq pr.Digest] in
/-- **`F.2` (lazy) and `gameHyb 0` have the same success probability** (the presampling of `F.2`,
txt lines 3279–3290). -/
theorem gameG2_eq_gameHyb (_hP : P.Valid) {qs : ℕ}
    (A : Notions.FxmssAdversary (scheme pr Msg slKeygen) qs) :
    Pr{let o ← gameG2 pr Msg slKeygen A}[WinNotC1 o] =
      Pr{let o ← gameHyb pr Msg slKeygen 0 A}[WinNotC1 (o.map Prod.fst)] := by
  rw [(gameG2_evalDistEq_gameHyb pr Msg slKeygen A).prEvent_eq WinNotC1, Functor.map_map]

end ShrincsSecurity.Fxmss.Rom

end
