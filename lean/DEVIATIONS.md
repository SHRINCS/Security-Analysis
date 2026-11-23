# Where the Lean formalisation departs from the documents, and why

This file covers the three documents in the repository root:

| Code | Document |
|---|---|
| **M** | `SHRINCS-Security-Analysis.pdf` (draft of November 18, 2026) |
| **I** | `ITSR-Classical.pdf` |
| **U** | `Undetectability.pdf` |

Page numbers are printed page numbers. Every quotation was checked on the rendered page: the text
extractions in `notes/txt/` drop absolute-value bars and sub/superscripts, and one early claim in
these notes was wrong for that reason (§6.1). Lean names are given without the `ShrincsSecurity.`
prefix. Every theorem cited builds with `lake build` and depends only on `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, `axiom` or `native_decide` occurs anywhere.

Each departure is classified as one of:

- **Forced (proof):** the printed statement, or the obvious formal reading of it, is false or
  unprovable without the change. The evidence is a counterexample or a Lean theorem.
- **Forced (framework):** the change is required by VCVio/Mathlib as they exist at the pinned
  revisions. The evidence is the exact definition that imposes it. These are not claims about the
  mathematics.
- **Quoted:** the document itself does not prove the result; it cites another paper. The Lean
  development states the result as an explicit, named hypothesis and never as an axiom.
- **Choice:** a modelling decision that changes no proved bound. It is listed for transparency,
  not because it was needed.
- **Route:** the statement matches the document, but the proof takes a different path.

---

## 1. What is proved, and under which hypotheses

| Result | Lean | Hypotheses beyond the document's own |
|---|---|---|
| I Theorems 1, 2, Corollary 1 | `ITSR.advantage_le_crudeBound`, `advantage_le_mainBound`, `advantage_le_onePull` | none |
| I Lemmas 1–13, §7 tables (exact columns) | `ITSR/Coverage*`, `ITSR/Analytic/`, `ITSR/Concrete/` | none |
| M Lemma 3.1 (i) correctness | `Scheme.Shrincs.verify_sign`, `execute_correct` | none (abstract typed model, §4.1) |
| M Lemma 3.1 (ii), Lemma 3.2 | `Scheme.Grinding.prob_grind_fail`, `epsGc_shrincs_lt` | none |
| M Definitions 4.1–4.16 | `Notions/` | §4.3 |
| M Lemmas C.2, C.4, C.5, Corollary C.2 | `Repro.advantage_le`, `advantage_le_expectedSeedSum`, `experiment_filterRun`, `diAdvantage_le`, `corollaryC2` | none |
| M Lemmas C.6, C.7, C.9, Theorem E.1, Theorem F.2, Corollary G.1, Lemmas 4.1 (i), 4.2 (classical) | `Notions/Generic/`, `ITSR.advantage_le_theoremF2` | none |
| M Claim 4.10 | `Fxmss.HonestView.extraction`, `Fxmss.Rom.Honest.claim_4_10` | digest encoding injective (§4.4) |
| M Theorem 4.2 (classical, ROM for `H_msg^sf`) | `Fxmss.Rom.theorem_4_2`, `corollary_4_2` | Conjecture 3.1 (`GrindComplete`), digest encoding injective |
| M Theorem 4.1 (classical) | `Shrincs.theorem_4_1` | Conjecture 3.1, digest encoding injective, **Claim 4.16 as `StatelessBound`** (§2) |
| M §6 classical and quantum figures | `Concrete/`, `Concrete/Quantum/` | the SM-DSPR row is the document's conjecture (§2) |
| M Lemma C.8 (quantum ZeroDist) | `Undetectability.ZeroDist.Adaptive.advantage_le_of_lossless` | the document's halting assumption (Remark C.1) |
| M Corollaries C.1, C.3 | `Undetectability.corollaryC1`, `corollaryC3_*` | **Lemma C.3 as hypothesis** (§2) |
| U Lemmas 1, 2, 3 (endpoint), 7, 8, 11, 13, 14, 15; Theorems 9, 16; Corollary 12 | `Undetectability/` | quantum combs only (§5.1); Corollary 12 takes **Lemma 10 as hypothesis** (§2) |

---

## 2. Results the documents quote rather than prove (Quoted)

Each of these is an explicit hypothesis of the theorems that use it.

| Result | What the document says | Lean |
|---|---|---|
| M Theorem 4.3 / Claim 4.16 (stateless route of Theorem 4.1) | M p. 49: "We quote that bound, restated under the accounting of Section 4.3; its proof is in [HK22]." Claim 4.16 applies the [HK22] reductions, augmented. | `Shrincs.StatelessBound A εsl`: in the game after the PRF and reprogramming hops (`gameHybS`), a stateless-branch forgery wins with probability `≤ εsl`. It concerns the given forger only. `εsl` stands for the ten [HK22] summands. |
| M Lemma C.3 (quantum adaptive reprogramming) | M p. 94: "Adapted from the proof of [LGX25, Theorem 7]". Pp. 95–96 sketch how that external proof is modified; the base proof is not reproduced. | `lemmaC3` hypothesis of `corollaryC1`, `corollaryC3_*` (`Undetectability/Rest/ReproHalf.lean`) |
| M Lemma C.1 | M p. 94: "Lemma C.1 ([GHHM21])", stated without proof. | hypothesis of `corollaryC3_adv_le_min` |
| U Lemma 10 (quantum sm-ow) | U p. 13: "We use Lemma 10 as stated in [11] and do not reprove it." | `lemma10` hypothesis of `corollary12` |
| M Conjecture 3.1 | Stated as a conjecture; Theorems 4.1 and 4.2 assume it. Lemma 3.2 bounds its failure only in the ideal model. | `GrindComplete pr` hypothesis. Lemma 3.2 is proved separately (`epsGc_shrincs_lt : < 2^-994`). |
| M SM-DSPR row of Table 6 | Conjectured (M p. 77). | `Concrete/`: the stateless and full sums take `dspr` as an argument; the figures use `dsprRow`, and `slSum_le_slBound` holds for any smaller value. |
| M Conjecture 4.1 (collection oracle harmless) | Conjecture | Not assumed. Collection budgets are not tracked at all (§4.6). |

---

## 3. ITSR-Classical (I)

**No departures in statements.** Theorems 1 and 2, Corollary 1 and Lemmas 1–13 are proved as
printed, for any finite instance set `ι` (the document fixes `ι = {0,1}^h`, so `θ = 1/|ι|` is the
document's `2^-h`; `Concrete.theta_fin_two_pow`).

- **I §3.1, Definition 4. Choice.** The challenge oracle returns ⊥ after `r` queries; Lean bounds
  the adversary instead (`ITSR.Adversary.chalBound`, an `IsQueryBoundP` on every execution path).
  An adversary that respects the document's oracle makes at most `r` effective challenges, and a
  bounded adversary never sees ⊥, so the success probabilities coincide.
- **I Lemma 2. Route.** The challenge tape `V` is indexed by fresh challenges rather than by
  challenge number. A run that would exhaust the tape falls back to fresh sampling, and `inv_run`
  proves this never happens for bounded adversaries.
- **I Lemma 4. Route.** Any coordinate witness is accepted rather than preferring a fresh one. This
  makes the union larger, so the inclusion still holds. The search term is the `β = none` summand of
  the same union.
- **I Lemma 6. Route.** It is proved by induction over the adversary program using
  `(c)_m = (c−1)_m + m(c−1)_{m−1}`, not by the union over injective `σ`. The statement (Eq. 9)
  is the same, and uniform in the tapes.
- **I §7. Route.** `(1−θ)^r` is enclosed by repeated squaring with 2^-256 rounding rather than by
  the exponential brackets of Lemma 13(ii)/(iii). `R₂` is evaluated directly, because Lemma 11(b)'s
  hypothesis `η ≤ e^-(k−1)/2` fails at the top rows of Tables 4/5, so Lemma 11(b) cannot be used
  there. Every exact (“ex”) figure of Tables 3–5 is certified to within 0.01 bits.
- **I §7. Not certified (scope).** The “up” columns (Lemma 12 upper form) and the derived columns
  `q×, q₋₁₀, q₋₂₀, x_lin, λ, q_d` of Table 7 and Table 8 are not certified. The maximality of `q*`
  and `q₁` is not proved; only that the bound is ≤ 1 at a certified `q ≥ 2^(printed − 0.01)`.

---

## 4. Main paper (M)

### 4.1 Scheme model (Sections 2–3)

- **Byte layouts. Choice.** Addresses, keys and signatures are typed records with injectivity
  lemmas (`Scheme.Address`), not byte strings. The indicator byte is the `Signature` constructor;
  length checks become typed shapes. The domain-separation analysis of SHA-256 inputs (M Lemma 4.3)
  is therefore outside the model; see §4.7 for its consequence `ε_ds`.
- **Stateless path. Choice.** It reuses VCVio's FIPS 205 development
  (`HashSig/SLHDSA`) at the SHRINCS parameters through `Primitives.toSLHDSA`, whose `F`, `H`, `T_ℓ`
  are definitionally SHRINCS's. The parameters match Table 1 (`Scheme.shrincs_table1`,
  `shrincs_slParams`: 24-byte digest, `len = 35`, 5776-byte signature).
- **`keygen` returns `Option`. Choice.** It is `some` for every valid structure
  (`keygen_isSome`). `sign` returns ⊥ for `|ctx| > 255`, which is outside Algorithm 2's domain.
- **Grinding counter type. Choice.** The counter is `Fin (2^c)`. For the S-TCR(Prop) reduction,
  `H_grind` is read on counters in `ℕ` modulo `2^c`. Under Conjecture 3.1 the oracle's least
  counter equals the scheme's (`Fxmss.Rom.leastCounter_thGrind`), which is the document's
  Remark 4.8.
- **Lemma 3.2's ideal function. Forced (framework).** It is sampled on `PkSeed × GrindTweak × Digest`
  rather than on all addresses. VCVio can only sample uniformly from a finite type
  (`SampleableType`, `VCVio/OracleComp/Constructions/SampleableType/Basic.lean:51`, with
  `SampleableType.finite` at :81), and the typed address record is infinite. Only grinding
  addresses are ever passed to `H_grind`, so nothing is lost.

### 4.2 Security notions (Definitions 4.1–4.16)

- **Reuse of VCVio games. Choice.** PRF, SM-TCR, SM-PRE, SM-UD, SM-rTCR and SM-DSPR are VCVio's
  games. Where the formulations differ, equality with the printed game is proved:
  - `Notions.smPrePaperExperiment_eq` (the document records `(T, y)`, VCVio records `(T, m)`);
  - `smUdAdv_toReal` (absolute difference);
  - `smDsprAdv_toReal` (`max(0, succ − triv)`);
  - `secondPreimageExists_iff_card_fiber`;
  - `itsrSucc_eq_ITSRAdvantage` (VCVio's ITSR oracle returns only the key).
- **SM-TCR-EXCL. Choice.** The partition `T₁ ∪ T₂ ∪ T₃` with `ω : T₂ → T₃` is encoded as an
  involution `partner`. `exclReserved_iff_cases` and `mem_Omega_iff_cases` prove that the guards and
  the winning condition are the printed three-case ones.
- **S-TCR(Prop), Definition 4.8. Forced (proof).** The oracle refuses when no counter satisfies
  `Prop`. The printed oracle ("Find the smallest `i ∈ ℕ` with `Prop(...) = 1`", M p. 37) is
  undefined in that case. `Evidence.MainPaper.stcr_no_valid_counter` exhibits a `Th` and `Prop`
  with no valid counter. The two agree whenever a counter exists, in particular under
  Conjecture 3.1.
- **Query caps. Choice.** As in I: bounded adversaries replace "return ⊥ after `p` queries".
- **Collection tweak sets. Choice.** Every member admits every tweak. This only enlarges the
  adversary class; the document's restriction matters only for `H_grind`.
- **Definitions 4.15/4.16. Choice (literal reading).** Every queried message enters `{M_i}`,
  including queries answered ⊥ (`FxmssScheme.signOracle`, `Notions/Signature.lean:195–207`). This
  is the literal reading of `M* ∉ {M_i}_{i=1}^{q_s}` (M pp. 46, 51) and the more cautious one. It
  is what forces §4.5's wrapper budget.

### 4.3 Generic bounds (Appendices C–G)

- **Lemma 4.1 (i). Route; partial scope.** It is proved as
  `Pr[collection game] ≤ Pr[stand-alone game](A′) + 2q/|P|`
  (`CollectionLemma.prEvent_game0_collInterface_le`), for any property satisfying a stated
  reservation discipline, with `q` the first-stage evaluations, which is the document's `ξ`. The
  document's Step 3 is replaced by a second application of Lemma C.9. For advantage notions
  (SM-UD, SM-DSPR) this route would give `4q/|P|`; those instances are not formalised.
- **Lemma 4.2. Choice.** Classical only. "Time" is query bounds on the game's oracles. The
  simulated adversary uses only private coins, which are unbounded in every game.
- **Lemma C.4 / Corollary C.2. Route.** The expectation forms are stated in `ℝ≥0∞` and compared
  with the advantage through `ENNReal.ofReal`. Corollary C.2 is proved directly on the DI game
  (pending points), not via Lemma C.4 applied to C.5's adversary; Lemma C.5 is proved separately.
  The part of Lemma C.5 stating that `A′`'s calls have pairwise distinct inputs is not formalised.
- **Repro, one table. Choice.** The experiment keeps only the table the adversary reads, `O_b`;
  the other table is never observable.
- **Theorem E.1. Route.** The second game is bounded by a direct per-query argument instead of the
  reduction to Avg-Search (Algorithm 13). The result is the sharper `(q₂+1)/|N| + q₁/|P|`, which
  implies the printed bound (`succ_le_of_le`).
- **Corollary G.1. Route.** It is proved with a potential argument directly, not via Lemma C.4.
- **Theorem F.2. Scope.** It is stated for an oracle with uniform digests
  (`ITSR.advantage_le_theoremF2`, derived from I Theorem 1). The document's `MAP ∘ H` is such an
  oracle when `MAP` has equal-size fibres (M Remark F.1). That step is not formalised.

### 4.4 Claim 4.10 and the digest encoding

- **Hypothesis `Function.Injective pr.yToBytes`. Forced (proof) for the abstract model; automatic
  in the document's model.** The proof of Claim 4.10 (M p. 61) uses "d is determined by its `l_sf`
  base-w digits". In Lean the encoded-digest type `pr.Y` is abstract and is read through
  `yToBytes`. If two distinct `d ≠ d_j` have the same bytes, the verifier accepts a signature on
  `d` built from the honest blocks of `d_j`. None of the abort events fires: `H_grind` outputs
  differ in `Y`, and every chain is honest. So the claim is false without the hypothesis. In the
  document `d ∈ {0,1}^n` and `n = l_sf · log₂ w`, so the hypothesis holds:
  `Evidence.MainPaper.n_eq_lsf_mul_log_w : 128 = 32 * Nat.log 2 16 ∧ 2^128 = 16^32` and
  `claim410_digits_determine`.
- **Explicit witnesses in the abort events. Forced (proof).**
  - The first formalisation (`Fxmss.HonestView.extraction`, `Fxmss/Extraction.lean`) states the
    events existentially, e.g. "∃ x ≠ v, F(x) = F(v)".
  - As a game event that is useless: for a uniformly random `F : [N] → [N]` and fixed `v`, the
    other `N − 1` points each miss `F(v)` independently with probability `1 − 1/N`, so
    `Pr[∃ x ≠ v, F x = F v] = 1 − (1 − 1/N)^{N−1} → 1 − 1/e ≈ 0.63`. No reduction can bound such
    an event by a small advantage.
  - Theorem 4.2 therefore uses `Fxmss.Rom.Honest.claim_4_10` (`Fxmss/Claim410.lean`), where every
    event names a witness computed from the forgery. This is what the document's reductions do
    implicitly, since they output the colliding pair.
- **Walk up the path. Route.** The document's two minimal indices `t*`, `s` are replaced by one
  downward induction (`Fxmss.climb_walk`). Claim 4.10 needs no structure-validity hypothesis,
  because `treeNode` is ⊥ off `A ∪ I`.

### 4.5 Theorem 4.2 (FXMSS)

`theorem_4_2` bounds the forger's success by the nine terms of the document, each the advantage of
an explicit reduction `B0`–`B8` with the document's target counts: `L`, `L·l_sf`, `L·l_sf·w`, `L`,
`L − 1 (= I)`, `L + I`. The w-term is `Σ_{γ < w−2}`, relaxed to `w·ε` by `theorem_4_2_of_ud_le`.
`corollary_4_2` replaces two terms by their classical bounds:

- SM-rTCR: `(qh+2)/|Digest| + (qh+1)/|Y|` (Corollary G.1);
- DI-Repro: `qh/|Y|` with `qh = qh₁ + qh₂`, the forger's queries only (`B1_diAdvantage_le`). This
  matches the document's `q_h/2^n` (Corollary C.3).

Departures:

- **Order of hops. Route.** The target-collision events (F.3, F.5, F.7, F.8, F.9) are bounded in
  F.2, with secret-key chains, and the SM-UD hybrid is applied only to the preimage event (F.6).
  The final sum is the document's nine terms.
- **Remark 4.6 inside the games. Route.** After the forgery is verified, the games sign every
  unused anchor with a message different from `M*`, as Remark 4.6's wrapper would.
- **Separate Remark 4.6 wrapper: signing budget `q_s + L`, not `L`. Forced (proof), given §4.2's
  literal freshness.** `Fxmss.Rom.wrap` has `succ_wrap : succ (wrap L A) = succ A` and
  `wrap_signs_all`; it signs only anchors `A` did not name and makes no extra RO query.
  - The budget `L` is unattainable. Take a forger whose `L` queries all name leaves outside the
    structure: every one is answered ⊥, but its message is logged.
  - Signing every anchor then needs `L` further queries, `2L = q_s + L` in total.
  - A wrapper with budget `L` must drop some of `A`'s ⊥ queries. That removes their messages from
    `{M_i}`, so a forgery on such a message wins for the wrapper and not for `A`, and only
    `Succ(A) ≤ Succ(A′)` survives.
  - The document's `q_s = L` assumes "without loss of generality every query names a leaf of the
    structure" (M p. 50, Definition 4.16 item 2). For such forgers the total is exactly `L`
    (`length_wrapIds`).
  - The main theorem does not use the wrapper's budget.
- **Time `ξ`. Choice.** Running time is not modelled. Each term is the advantage of an explicit,
  named reduction, which is strictly more information than a time bound.
- **Collection budgets `q_{λ,i}`. Forced (framework).** VCVio's collection games carry no budget:
  `SM_DT_TCR_Problem` has only `th`, `thColl`, `numTargets`
  (`VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean:58–64`). Each reduction
  routes its other evaluations through the collection oracle and respects the tweak reservation;
  only the count is untracked. Under Conjecture 4.1, which the document's figures use, the count
  does not matter.
- **SM-TCR-EXCL term left as an advantage in `corollary_4_2`. Forced (proof of applicability).**
  Theorem E.1's game has `Th` as a random oracle with no collection oracle; `B8` plays the
  collection game. Lemma 4.1 does not transfer exactly (it has an additive `2q/|P|` loss), so
  substituting E.1 would change the bound.
- **`PK.sl`. Choice.** It is an arbitrary `slKeygen : PK.seed → ProbComp Y` in Theorem 4.2. The
  document generates it from the stateless key generation, which is an instance.
- **Finite message type `Msg`. Matches the document.** DI-Repro needs finite `X₁, X₂, Y`
  (M Definition C.1: "Let X1, X2, and Y be finite sets"), and footnote 16 (M p. 95) states the
  message set is finite. `idx` is `Fin 256 × Fin 2^64`.
- **`idx` injectivity. Implicit in the document, made explicit.** `B0`'s distinct tweaks and the
  never-firing guard of `B1` need `idx = toByte(z*,1) ‖ toByte(i*,8)` to be injective on leaves.
  The ranges are stated (M p. 18: `z ≤ h_sf = 255`, "only positions with `i < 2^64` are
  addressable"), but the reductions do not cite them. Outside the ranges `idx` collides:
  `Evidence.MainPaper.idx_collide_height : idx 256 0 = idx 0 0` and
  `idx_collide_index : idx 0 (2^64) = idx 0 0`. Within them it is injective (`idx_injOn`).

### 4.6 Theorem 4.1 (SHRINCS)

`theorem_4_1` bounds the forger's success by the sum of:

- the two PRF terms: `Adv^prf_{q₁}` and `Adv^prf_{q_s}` for `PRF_msg`;
- the nine Theorem 4.2 terms for the augmented reductions, which run with a forger `A_F` that
  simulates the stateless path itself;
- `εsl` from `StatelessBound` (§2).

`q₁ = L·l_sf + Σ_{i<d} 2^{h'(d−i)}·l_sl + 2^h·k·2^a`, the exact number of secret elements
(`cacheAdv_Bprf_bound`). This is at most the document's count.

Departures:

- **`ε_ds` absent. Forced (framework) / outside the model.**
  - M Assumption 4.1 charges `ε_ds ≤ 2^-n + 10·2^-2n` for SHA-256 calls of two different named
    functions receiving the same input (M Lemma 4.3, p. 43; "charged once in Theorem 4.1, outside
    the sequence of games", M p. 62).
  - In the model these functions are distinct objects with no common underlying hash. They are
    separate fields of `Scheme.Primitives`: `Th` (Primitives.lean:61), `Hgrind` (:63), `PRF` (:65),
    `PRFmsg` (:67), `HmsgSl` (:69).
  - `H_msg^sf` is the separate random oracle `Fxmss.Rom.roSpec` (Fxmss/Model.lean:75).
  - So a Lemma 4.3 event cannot be expressed in the model and no hop meets it. The bound holds as
    stated; adding `ε_ds ≥ 0` is trivial. Justifying the model against SHA-256 is exactly
    Assumption 4.1 and Lemma 4.3, which stay outside the formalisation.
- **`H_msg^sl` a fixed function. Choice.** M p. 47: H_msg^sl's security property "enters through
  the itsr notion (Definition 4.11), which is a standard-model notion". In Lean the itsr term is
  inside the quoted `εsl`. Claims 4.11–4.15 hold for an arbitrary `HmsgSl`, and modelling it as an
  oracle would change no bound proved here.
- **Augmented reductions. Route.** They are the §4.7 reductions run against `A_F`. The shared
  reprogramming hop uses one new distinguisher `B₁⁺` (Algorithm 5 on the augmented signing phase)
  covering both branches.
- **`PRF_msg` budget `q_s`. Route.** The document evaluates it at `q_s^sl + L`. The Lean games
  have no Remark 4.6 completion before the hop, so `q_s` suffices.
- **The `B_prf` reduction caches its answers. Forced (proof), and a gap in M's argument.**
  - M p. 62: "queries its oracle at ADRS instead; the queries are classical and pairwise distinct
    by the unique-address discipline."
  - They are not. The FIPS 205 key generation reads every WOTS secret of the top tree
    (`keygenInternalWithSecretM` → `xmssRootWithSecret`, VCVio `SecretProvider.lean:229, 639`).
  - Every stateless signature reads them again: `signFromPositionWithSecret` (:582) →
    `xmssSignWithSecret` → `intrinsicAuthPathM (xmssLeafWithSecret …)` (:199–207).
  - Addresses are unique per secret element, but the oracle queries repeat. Caching restores
    distinctness at no cost: `Shrincs.prfAdvantage_cacheAdv` proves the advantage is unchanged.
- **GAME.6. Route.** It is implicit: every forgery is on exactly one branch, so
  `Win = Wsf ∨ Wsl`.

### 4.7 Section 6 figures

Every figure listed below reproduces: the certified interval contains the printed value under the
document's rounding rule. Classical: Table 5, Eqs. (1), (3), (9), Section 6.4, Remark 6.1, Table 8.
Quantum: Table 5, Claims 6.1–6.4, Remark 6.1, the abstract's `2^58.0–2^59.2`.

- **Scope.** These files evaluate the document's sums of generic bounds; they do not restate
  `InSec ≤ row`. The link to the games exists only where the generic bound is proved: Corollary G.1,
  Corollary C.2/C.3, E.1, Theorem 16 and Corollary 12 (`smUdQ_theorem16`, `smPreQ_corollary12`).
- **Constants. Choice.** `w = 16` and the `2^128`/`2^256` space sizes are literals; verification
  counts and budgets are derived from `Scheme.Params`.
- **Not certified (scope):**
  - the "ν" sentence of Claims 6.1, 6.2, 6.4 ("ν moves log₂ ξ* by less than 0.01");
  - footnote 13 (constants `2√2`, `16`);
  - footnote 15's "changes nothing else";
  - Section 6.8's "unchanged under Convention M" for the full scheme. The stateless and stateful
    rows are certified.
- **Theorems F.3, G.1 (quantum). Scope.** They are not formalised; their Table 6 rows are
  definitions.

---

## 5. Undetectability (U) and the main paper's quantum lemmas

### 5.1 Program model

- **Quantum combs, not general adaptive programs. Forced (framework).**
  - Lemma 1 (the polynomial method) is proved for VCVio `QuantumComb`s: fixed query slots, any
    trace-nonincreasing instruments between queries, mixed initial state
    (`QuantumComb.isMarginalLinear_outcome`).
  - VCVio does not prove that a general `QuantumComp` program has an equivalent comb, and its
    design notes show this needs extra hypotheses (`VCVio/docs/design/quantum-layer.md` §1, lines
    75–96: "The converse, that a program has an equivalent comb, is not proved").
  - The document's adversaries are circuits with a fixed number of queries, i.e. combs.
  - Lemma C.8 (ZeroDist) does cover general adaptive programs (`ZeroDist.Adaptive`).
- **Abelian output group. Forced (framework).** U Theorem 16 is "for every group law on N"
  (U p. 18). VCVio's oracle unitary needs `[AddCommGroup Y]`
  (`QuantumFoundations/Oracle/Unitary.lean:90`, the section variable before `oracleUnitary` at
  :96). Theorem 16 is therefore proved for finite abelian groups. The SHRINCS instance (XOR,
  Theorem 9) is abelian (`smUdAdv_le_xor`). A non-abelian version needs a new oracle unitary; the
  proof (Lemmas 7, 13, 15) does not use commutativity.
- **Challenge answers fixed in a table. Choice that strengthens the result.**
  - In every world the challenge answer on a fresh tweak is fixed before the run (U p. 8: "we may
    therefore sample, before the run, one independent uniform input `x_T`").
  - The Lean adversary is indexed by the whole table `ch : T → N` and may read it in both stages.
    That class contains every Definition 4 adversary, and the bound `4q²/|M|` holds for it.
  - The embedding of the document's adversaries into this class is argued in the docstrings, not
    proved in Lean.
- **Lemma 11's reduction `C`. Choice.** `C` is given by its acceptance probability (run `A`, then
  classically check `Th(P, T, x*) = ch(T)`), not as a comb with an extra slot. Corollary 12 uses `C`
  only through Theorem 16, which needs `C`'s `2(q+1)`-point linearity; that is proved directly
  (`isMarginalLinear_hopAccept`).

### 5.2 Individual results

- **U Lemma 3 (Markov brothers). Scope.** Only the endpoint form `|P′(±1)| ≤ d²` is proved
  (`abs_derivative_eval_one_le`), from Mathlib's Chebyshev extremality. That is the only use in U
  (p. 9, proof of Lemma 7: "t = −1 gives…"). The full interior inequality is not in Mathlib.
- **U Lemma 7. Choice.** The measure-theoretic version needs the acceptance function to be
  `Measurable`; this is automatic on the document's discrete spaces.
- **U Lemma 14. Route; stronger.** It is proved by factoring the product point by point, for all
  real `λ`, not only `[0,1]`.
- **U Lemma 2. Choice.** It is an exact operator identity with a clean ancilla
  (`selection_mul_ancillaEmbed`). `U` carries an additive group so that `s(x)` can be written into
  it, as in the document (U §2.1 and the proof of Lemma 2: "U carries the group law of ℤ_|U|").
- **M Lemma C.8.**
  - In the adaptive model the bound `2q/√|P|` needs the first stage to be lossless. That is the
    document's standing assumption (M Remark C.1, p. 94: quantum adversaries "halt with
    probability 1"), so it is not a departure.
  - For possibly aborting programs only `4q/√|P|` is proved (`ZeroDist.Adaptive.advantage_le`).
  - The second stage is modelled as a measurement on the first stage's output. The reduction from
    an oracle-free second-stage program to its effect `(√E, √(1−E))` is not proved.

### 6.1 A correction to earlier notes

`notes/paper-structure.md` and `notes/quantum-feasibility.md` first claimed that U prints a
*signed* SM-UD advantage, making Lemma 11 inconsistent. That was an extraction artifact. U p. 8
(Definition 4) and p. 13 (Lemma 11) print absolute values, and Lemma 11 is correct as printed
(`Undetectability.lemma11 : |succPre − succOw| = smUdAdv …`). The notes have been corrected. The
signed reading is false on a 4-element instance (`Evidence.SmUdHop.Fixed.lemma11_signed_false`),
which only shows the bars matter.

---

## 7. Suggestions for the documents

Each item was checked on the rendered page. The full evidence is in `notes/paper-issues.md`
(sections A–L).

### 7.1 Gaps (a statement is undefined, or a step does not hold as written)

1. **M Definition 4.8 (S-TCR(Prop)), p. 37.**
   - "Find the smallest `i ∈ ℕ` with `Prop(Th(P,T,m‖i)) = 1`" can have no solution.
   - Remark 4.8 (p. 54) resolves this only under Conjecture 3.1.
   - Suggest: search `i < 2^c` and return ⊥ when none exists.
   - Lean: `stcr_no_valid_counter`.
2. **M Claim 4.11, p. 62.**
   - "the queries are classical and pairwise distinct by the unique-address discipline" is false
     for the reduction as described: the stateless signer re-reads top-tree secrets in every
     signature (§4.6).
   - Suggest: "the reduction caches its answers, so its queries are pairwise distinct".
3. **M Definition 4.9 (SM-rTCR), p. 37.**
   - Step 5 evaluates `Th(P, T_j, m_j‖ρ_j)` at `ρ_j = ⊥`; only App. G (p. 121) says to read this
     as a loss.
   - Suggest stating it in the definition. There is no effect on SHRINCS (`K = 1`, `Prop ≡ 1`).
4. **M Definition 4.16 / Remark 4.6, pp. 50–51.**
   - "without loss of generality every query names a leaf of the structure" is not free under the
     literal freshness condition `M* ∉ {M_i}`, which also covers queries answered ⊥.
   - Dropping such a query frees its message for a forgery. A wrapper that keeps them needs
     `q_s + L` queries, not `L` (§4.5).
   - Suggest: either define `{M_i}` as the answered queries only, or let the wrapper budget be
     `q_s + L`. The theorem itself is unaffected.

### 7.2 Hypotheses used but not cited

5. **`idx` injectivity (M pp. 18, 52–53).** The reductions `B0` (distinct tweaks) and `B1` (the
   DI guard never fires) need `idx = toByte(z*,1) ‖ toByte(i*,8)` injective on leaves, which holds
   only for `z ≤ 255` and `i < 2^64`. Suggest citing p. 18's ranges at both places. Lean:
   `idx_collide_height`, `idx_collide_index`, `idx_injOn`.
6. **Claim 4.10, p. 61.** "d is determined by its `l_sf` base-w digits" holds because `d ∈ {0,1}^n`
   with `n = l_sf · log₂ w = 128 = 32 · 4`. Suggest saying so; the step is false for any encoding
   with more than `l_sf · log₂ w` bits (§4.4).
7. **Abort events should name their witnesses (M §4.7).** Events such as "the forgery reaches a
   chain value via an input distinct from the honest one" are reduction outputs, not existential
   statements about `F`; read existentially they hold with probability about `1 − 1/e` for a random
   function (§4.4). The reductions already compute the witnesses. Phrasing the events as "the
   reduction's extracted pair collides" removes the ambiguity.

### 7.3 Imprecisions (stated results are correct)

8. **M Lemma 4.1 (i), p. 41 / proof p. 107.** The stated `2ξ/|P|` is correct but looser than the
   proof: `ξ₁/|P|` for success notions, `2ξ₁/|P|` for advantage notions.
9. **M §6.4, quantum item 1, p. 79.**
   - "they add less than `2^-102.3` on the stateful path to the value of the bound at `ξ = 0`"
     holds for the collection summands themselves.
   - The stateful bound's minimum at `ξ = 0` uses e = 1/2 at the hop, which doubles them to
     `≥ 2^-101.36` (`section_6_4_quantum_verification_doubled`).
   - Suggest "to the value of these summands". Also: "stoped" → "stopped".
10. **Symbol `q`.** It is the challenge cap in M Definition 4.11 (`ITSR_{H,q}`, p. 39) and the
    hash-query count in App. F and Table 6, where challenges are renamed `p` (pp. 77, 117).
    Suggest `p` in Definition 4.11 too.
11. **M Definition 4.7 vs Theorem E.1.** `p ∈ [|T₁ ∪ T₂|]` vs "p ≤ |T|". Harmless: the game admits
    at most `|T₁| + |T₂|` challenges and the bound is independent of `p`.
12. **M abstract and §6.1.** "between 121.4 and 122.7 bits" while Table 5 gives 122.75. This is
    consistent with the document's round-down convention; saying so once would help.

### 7.4 Results that hold under weaker hypotheses than printed (optional tightening)

- **I Lemma 11.**
  - (a) and the step of (c) hold for every `m ≥ 1`, not only `m ≤ min(k,q,r)`.
  - (b) needs no extra hypothesis.
  - The geometric bound needs only `1 ≤ m ≤ k`. `t ≥ 1` is used for `A_m > 0`; it is stated on
    I p. 4.
- **I Lemma 12** holds for all `j, m, t`.
- **I Lemma 13.**
  - (i) needs only `0 ≤ θ ≤ 1` and `rθ < G+2`.
  - (ii) needs only the one-sided conditions.
  - (iii) holds without `M ≥ x`, as an absolute-value bound.
- **M Theorem E.1** holds with the stage-split constants `(q₂+1)/|N| + q₁/|P|`.
- **U Lemma 14** holds for all real `λ`.
