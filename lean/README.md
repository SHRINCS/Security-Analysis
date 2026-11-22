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
| ITSR-Classical | Lemmas 1, 5, 7, 8 | `ShrincsSecurity/ITSR/Coverage.lean` | in progress |
| ITSR-Classical | Theorems 1, 2 | `ShrincsSecurity/ITSR/` | in progress |
| ITSR-Classical | Corollary 1, Lemmas 11–13 | `ShrincsSecurity/ITSR/` | in progress |
| Main, App. C | Definitions C.1, C.2; Lemmas C.2, C.4, C.5; Corollary C.2 | `ShrincsSecurity/Repro/` | in progress |
| Main, §4.2–4.5 | Definitions 4.3–4.16 | `ShrincsSecurity/Notions/` | in progress |
| Main, App. C–G | Lemmas C.6, C.7, C.9; Theorem E.1; Corollary G.1 | `ShrincsSecurity/Notions/Generic/` | in progress |
| Main, §2–3 | Scheme, Lemma 3.1 (correctness) | `ShrincsSecurity/Scheme/` | in progress |
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
