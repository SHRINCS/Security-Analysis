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

Work in progress. Each row names the document's result and the Lean declaration that proves it.

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
| Main, App. C | Definitions C.1, C.2; Lemma C.2 (`advantage_le`); Lemma C.4 (`advantage_le_expectedSeedSum`); Lemma C.5 (`experiment_filterRun`); Corollary C.2 (`diAdvantage_le`: `≤ q/|X₁|`, `corollaryC2`) | `ShrincsSecurity/Repro/` | done |
| Main, §4.2–4.5 | Definitions 4.3–4.16 | `ShrincsSecurity/Notions/` | in progress |
| Main, App. C–G | Lemmas C.6, C.7, C.9; Theorem E.1; Corollary G.1 | `ShrincsSecurity/Notions/Generic/` | in progress |
| Main, §2–3 | Scheme, Lemma 3.1 (i) (correctness) | `Scheme/Shrincs.lean` (`verify_sign`, `execute_correct`) | done; Lemma 3.1 (ii) planned |
| Main, §4.7 | Theorem 4.2 (FXMSS), Claims 4.1–4.10 | | planned |
| Main, §4.8 | Theorem 4.1 (SHRINCS), Claims 4.11–4.16 | | planned |
| Main, §6 | Concrete bounds | | planned |
| Undetectability | quantum sm-ud / sm-pre bounds | | planned (VCVio quantum layer) |

## Assumption ledger

The documents' bounds rest on assumptions that are not theorems. The formalisation keeps each one
an explicit hypothesis of the theorems that use it, never an axiom:

- **Conjecture 3.1** (grind-completeness): every counter search succeeds within `2^c` counters.
- **Conjecture 4.1** (collection-oracle queries do not affect insecurity). Lemma 4.1 proves the
  ideal-model version with an additive parameter-guessing term.
- **Assumption 4.1** (named functions modeled as independent random functions).
- **Theorem 4.3** is quoted from [HK22]; the documents do not reprove it.
- **The SM-DSPR bound of Table 6** is conjectured.

`notes/paper-structure.md` maps every definition, lemma and theorem of the three documents, with
their dependencies and the results they quote from other papers.
