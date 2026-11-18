# SHRINCS Security Analysis

This repository holds the security analysis of SHRINCS: the definitions, reductions, and concrete security bounds that accompany the specification in [`SHRINCS/shrincs-bip`](https://github.com/SHRINCS/shrincs-bip).

Author: Mikhail Kudinov

> [!WARNING]
>
> The documents in this repository are research drafts. They have not yet been sufficiently peer reviewed or independently audited, and they may contain errors in statements, proofs, or concrete figures.
>
> Nothing here is a guarantee that SHRINCS, or any implementation of it, is secure. Do not rely on these documents as the sole basis for deploying SHRINCS.

## Documents

| File | Contents |
|---|---|
| [`SHRINCS-Security-Analysis.pdf`](./SHRINCS-Security-Analysis.pdf) | The main paper: the SHRINCS construction, its security reduction, and the concrete security bounds for the stated parameter sets. |
| [`ITSR-Classical.pdf`](./ITSR-Classical.pdf) | A classical bound on interleaved target-subset resilience (ITSR) for the hash used in the few-time signature component. |
| [`Undetectability.pdf`](./Undetectability.pdf) | A bound on the undetectability (UD) of the tweakable hash function used in the reduction. |

Each theorem states the model it holds in (classical or quantum random oracle model, the adversary class, and single- or multi-target setting) and the assumptions it depends on. A bound holds only under those stated assumptions and for the parameters it is evaluated at. It says nothing about side channels, implementation bugs, key management, or misuse of the state.

The specification and the analysis are developed separately. If they disagree, treat that as a bug and report it. Neither document should be read as silently correcting the other.

## No warranty and no liability

These documents are provided "as is", without warranty of any kind, express or implied, including any warranty of correctness, completeness, or fitness for a particular purpose. The authors and contributors accept no responsibility or liability for any loss, damage, or other consequence arising from the use of, or reliance on, these documents or any result in them.

Publishing a proof here is not an endorsement of SHRINCS for any particular use. Anyone deploying SHRINCS is responsible for their own assessment of its security.

## Reporting errors

Errors in proofs, bounds, or parameters are the most valuable feedback this repository can receive. Please open an issue that names the document, the statement (theorem, lemma, or equation number), and what you believe is wrong. A concrete counterexample or a failing calculation is ideal, but a precise description of a gap is welcome too.

Issues found with AI assistance are welcome under the same rules as in the [shrincs-bip contributor guide](https://github.com/SHRINCS/shrincs-bip/blob/main/CONTRIBUTING.md#use-of-ai): validate the finding yourself, summarize it in your own words, and link to the conversation if your tool supports it.

Documents will be revised as errors are found. Cite a specific version (commit hash or release tag) when referring to a result.

## License

Copyright © 2026 Blockstream Corporation Inc.

The documents in this repository are licensed under the [Creative Commons Attribution 4.0 International License (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/). The full license text is in [`LICENSE`](./LICENSE).

You may share and adapt the documents for any purpose, provided you give appropriate credit, link to the license, and indicate whether you made changes. Section 5 of the license disclaims all warranties and limits liability.

Material quoted or reproduced from other works remains under the terms of its original source.
