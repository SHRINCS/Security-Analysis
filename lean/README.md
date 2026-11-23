# SHRINCS security analysis in Lean 4

A machine-checked formalisation of the security proofs in this repository's documents, built on
[VCVio](https://github.com/Verified-zkEVM/VCVio) (the framework behind leanEthereum/leanVM's
leanSPHINCS and leanXMSS proofs), with the same pins as leanVM: Lean `v4.36.0`, mathlib `v4.36.0`,
VCVio `f1e63c7`.

```sh
cd lean
lake exe cache get   # mathlib cache
lake build
```

## Status

Every result of the three documents that is proved in them is formalised, except the items listed
as out of scope in [`DEVIATIONS.md`](DEVIATIONS.md). That file records every departure from the
documents, the reason it was necessary, and suggestions for the documents. Each row names the
document's result and the Lean declaration that proves it. Every declaration depends only on
`propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, `axiom` or `native_decide`.

| Document | Result | Lean | Status |
|---|---|---|---|
| ITSR-Classical | Definitions 1–6 | `ShrincsSecurity/ITSR/Defs.lean` | done |
| ITSR-Classical | Definition 4 (ROM experiment) | `ShrincsSecurity/ITSR/Game.lean` | done |
| ITSR-Classical | Lemmas 1, 5, 7, 8 | `ITSR/Coverage.lean` (`prob_covered_positions`, `prob_covered_tape`, `prob_digestEvent`, `sum_witnessMaps`) | done |
| ITSR-Classical | Lemma 2 (pre-sampled oracle), Lemmas 3, 4 | `ITSR/Presample.lean`, `ITSR/Classification.lean` | done |
| ITSR-Classical | Lemma 6 (pull probability), Lemma 10 | `ITSR/Pull.lean`, `ITSR/Theorem1.lean` | done |
| ITSR-Classical | Theorem 1 | `advantage_le_crudeBound` (`ITSR/Theorem1.lean`) | done |
| ITSR-Classical | Theorem 2 (Lemma 9) | `advantage_le_mainBound` (`ITSR/Theorem2.lean`) | done |
| ITSR-Classical | Corollary 1 | `advantage_le_onePull` (`ITSR/Corollary1.lean`), `mainBound_eq_onePull` | done |
| ITSR-Classical | Lemmas 11–13 | `ITSR/Analytic/` | done |
| ITSR-Classical | Section 7: Tables 3–5 (exact columns), Table 7 Γ and q₁, Table 6 at SHRINCS-sl | `ITSR/Concrete/` (`decide +kernel` certificates; generator `Concrete/generate.py`) | done |
| Main, App. F | Theorem F.2, classical part | `advantage_le_theoremF2` (`ITSR/TheoremF2.lean`, from ITSR Theorem 1) | done |
| Main, §4.7 | Claim 4.10, deterministic core: a fresh verifying forgery contains one of the abort events of F.1–F.9 | `HonestView.extraction`, `claim_4_10` (`Fxmss/Extraction.lean`); with explicit witnesses `Fxmss.Rom.Honest.claim_4_10` (`Fxmss/Claim410.lean`) | done; needs the digest encoding `yToBytes` injective, which the paper's bit-string digests satisfy |
| Main, §3.1 | Lemma 3.1 (ii), Lemma 3.2 (`< 2^-994`), `1/p_sum ∈ (65.6, 65.8)` | `prob_grind_fail`, `prob_not_grindComplete_le_epsGc`, `epsGc_shrincs_lt` (`Scheme/Grinding.lean`) | done |
| Main, App. C | Definitions C.1, C.2; Lemma C.2 (`advantage_le`); Lemma C.4 (`advantage_le_expectedSeedSum`); Lemma C.5 (`experiment_filterRun`); Corollary C.2 (`diAdvantage_le`: `≤ q/|X₁|`, `corollaryC2`) | `ShrincsSecurity/Repro/` | done |
| Main, §4.2–4.5 | Definitions 4.1–4.16 (PRF, SM-TCR, SM-PRE, SM-UD, SM-rTCR, SM-DSPR reused from VCVio with equivalence proofs; SM-TCR-EXCL, S-TCR(Prop), ITSR, collections, EU-CMA games fresh) | `ShrincsSecurity/Notions/` | done |
| Main, App. C–G | Lemma C.6 (`AvgSearch.succ_le`), Lemma C.7 (`ZeroDist.advantage_le`), Lemma C.9 (`HiddenSlice.abs_game_sub_le`), Theorem E.1 classical (`SmTcrExcl.succ_le`), Corollary G.1 (`RandomSamplingTCR.advantage_le`), Lemma 4.1 (i) (`CollectionLemma.prEvent_game0_collInterface_le`) | `ShrincsSecurity/Notions/Generic/` | done |
| Main, §2–3 | Scheme, Lemma 3.1 (i) (correctness) | `Scheme/Shrincs.lean` (`verify_sign`, `execute_correct`) | done |
| Main, §4.3 / App. D.3 | Lemma 4.2, classical (independent functions are harmless), instantiated for Lemma C.9, SM-TCR, Repro, DI-Repro | `gameExt_eq_game_dropExt`, `smtcrGameExt_eq`, `diAdvantageExt_eq` (`Notions/Generic/IndependentFunctions.lean`) | done |
| Main, §4.7 | Theorem 4.2 (FXMSS, classical ROM for `H_msg^sf`, Conjecture 3.1 as hypothesis `GrindComplete`), Claims 4.1–4.10, Remark 4.6 | `Fxmss.Rom.theorem_4_2`, `corollary_4_2` (SM-rTCR and DI-Repro `q_h/|Y|` terms replaced by their classical bounds), `claim_4_1` … `claim_4_9`, `Honest.claim_4_10`, `wrap`/`succ_wrap` (`ShrincsSecurity/Fxmss/`) | done |
| Main, §4.8 | Theorem 4.1 (SHRINCS), Claims 4.11–4.15; Claim 4.16 (stateless route, which the paper takes from [HK22]) is the explicit hypothesis `StatelessBound` | `Shrincs.theorem_4_1`, `theorem_4_1_of_ud_le`, `corollary_4_1` (`B1S_diAdvantage_le`), `claim_4_11` … `claim_4_15`, Stage-1 `O_coll` virtual-tree precomputation `B2S`–`B8S` (`ShrincsSecurity/Shrincs/VirtualTree.lean`, `Claim415.lean`) | done (see `DEVIATIONS.md` §4.6) |
| Main, §6 | Classical figures: Table 5 (122.23 / 122.75 / 121.47 bits), Eqs. (1), (3), (9), Section 6.4, Remark 6.1, Table 8 | `ShrincsSecurity/Concrete/` (kernel-checked evaluation of the paper's sums of Table 6 bounds; SM-DSPR row taken as the paper's conjecture; row links to Cor. G.1, Cor. C.2, Thm. E.1, ITSR Thm. 2, Thm. F.2 in `Concrete/Generic.lean`) | done |
| Main, §6 | Quantum figures: Table 5 quantum columns, Claims 6.1–6.4, Remark 6.1 (11.7 / 11.2 bits, floor `2^-3.4`), abstract's `2^58.0`–`2^59.2` | `ShrincsSecurity/Concrete/Quantum/` | done |
| Main, App. C | Lemma C.8 (quantum ZeroDist `≤ 2q/√|P|`); Corollaries C.1, C.3 arithmetic from Lemma C.3 (quoted from [LGX25], a hypothesis) | `Undetectability/Quantum/ZeroDistAdaptive.lean` (`advantage_le_of_lossless`), `Undetectability/Rest/ReproHalf.lean` (real algebra only; see `DEVIATIONS.md` §5.2) | done |
| Undetectability | Lemmas 1, 2, 3 (endpoint form), 7, 8, 11, 13, 14, 15; Theorems 9, 16; Corollary 12 (Lemma 10, quoted from [11], a hypothesis) | `Undetectability/Poly/`, `Marginal/`, `Theorems/`, `Rest/` (quantum combs) | done |
| — | Evidence for `DEVIATIONS.md` and `notes/paper-issues.md` | `ShrincsSecurity/Evidence/` | done |

## Assumption ledger

The documents' bounds rest on assumptions that are not theorems. The formalisation keeps each one
an explicit hypothesis of the theorems that use it, never an axiom:

- **Conjecture 3.1** (grind-completeness): hypothesis `GrindComplete` of Theorems 4.1 and 4.2.
- **Conjecture 4.1** (collection-oracle queries do not affect insecurity): not assumed; collection
  budgets are not tracked. Lemma 4.1 proves the ideal-model version with an additive term.
- **Assumption 4.1** (named functions modeled as independent random functions): built into the
  model, in which the named functions are separate objects; `ε_ds` is therefore outside the model.
- **Theorem 4.3 / Claim 4.16** are quoted from [HK22]: hypothesis `StatelessBound` of Theorem 4.1.
- **Lemma C.3** (adapted from [LGX25]) and **Lemma C.1** ([GHHM21]): hypotheses of Corollaries C.1
  and C.3.
- **Undetectability Lemma 10** (quoted from [11]): hypothesis of Corollary 12.
- **The SM-DSPR bound of Table 6** is conjectured: an explicit argument of the Section 6 sums.

`notes/paper-structure.md` maps every definition, lemma and theorem of the three documents, with
their dependencies and the results they quote from other papers.
