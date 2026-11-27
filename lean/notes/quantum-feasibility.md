## Summary

VCVio already provides substantial quantum semantics, BBBV-style hybrid bounds, and a proved compressed-QROM equivalence. **The polynomial method and adaptive-reprogramming/O2H security theorems were not found.** Mathlib has **Chebyshev endpoint derivative extremality**, sufficient for the planted-family argument without formalizing the full Markov brothers inequality.

### Path conventions
All paths below are exact relative to:
- **V** = `lean/.lake/packages/VCVio/`
- **Q** = `lean/.lake/packages/QuantumFoundations/`
- **M** = `lean/.lake/packages/mathlib/`

Declaration names below are in namespace `Quantum` unless explicitly qualified otherwise.

## 1. Algorithms, queries, measurement, and QROM

| File | Declarations and meaning |
|---|---|
| **V**`VCVio/Quantum/Comp/Basic.lean` | `QuantumOracleSpec`: ports with `In`, `Out`, and classical `Result`. `QuantumComp L spec W A`: well-founded program tree, initially on finite register `A`, returning outcome-dependent registers. `QuantumComp₂ L spec A B α`: fixed final register. `QComp spec A B α`: arbitrary local instruments. |
| Same | `QuantumComp.primBind`, `queryBind`, `bind`; `QComp.act`. Local measurement outcomes select continuations; quantum state resides in registers, not tree branches. Calls expose a register factor and preserve its entangled workspace. |
| **V**`VCVio/Quantum/Comp/QueryBound.lean:81-180` | `QuantumComp.IsQueryBoundAt x i q`, `IsQueryBound x b`: at most the specified calls **on every syntactic path, including zero-weight branches**. `IsQueryBoundAt.bind`, `IsQueryBound.bind`: budgets add. Not expected query counts or running-time bounds. |
| **V**`VCVio/Quantum/Comp/TotalQueryBound.lean` | `QuantumComp.IsTotalQueryBound`: bounds total calls across all ports, rather than adding separately maximized port budgets. |
| **V**`VCVio/Quantum/Comp/Runtime.lean` | `QuantumRuntime spec` has private register `D`, `init : SubState D`, and `step : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)`. `run`, `run₂` interpret programs; `run_bind`, `run₂_bind` preserve sequencing. |
| Same | `QuantumRuntime.jointPost`, `reducedPost`, `evalDist`, `evalDistMap`, and fixed-register `₂` variants. Output probability is the outcome measure on the desired event; singleton weight is the trace of the corresponding unnormalized post-state. |
| **V**`VCVio/Quantum/Oracle/Comb.lean:181-237` | `QuantumComb M α q` explicitly stores `init`, `step : Fin (q+1) → SubInstrument M M Unit`, losslessness proofs, and `final : SubInstrument M M α`. `body`, `run`, `stateAfterStep`, `outcomeMeasure_run` give exactly-q-slot semantics and final measurement. |
| Same file | `QuantumComb.toComp`, `run_toComp` embed combs into programs. **No converse/deferred-measurement normalization theorem is proved.** |

A final measurement in a general program is an explicit local instrument, e.g. through `QComp.act`; returning a classical value does **not** implicitly measure its remaining register.

**Function oracle and random oracle:**
- **Q**`QuantumFoundations/Oracle/Unitary.lean:43-145`: `oracleEquiv H` maps `(x,y)` to `(x,y + H x)`; `oracleUnitary H` is its complex permutation matrix.
- `oracleUnitary_apply`, `oracleUnitary_mulVec_single`, `conjTranspose_oracleUnitary`, `oracleUnitary_mem_unitaryGroup`, `oracleQuery` supply matrix action, inverse/unitarity, and instrument semantics.
- Important scope: `oracleEquiv` needs only `[AddGroup Y]`, but **`oracleUnitary` and VCVio's standard QROM require `[AddCommGroup Y]`**. XOR is represented by an elementary abelian 2-group. Arbitrary nonabelian output groups need generalization.
- **V**`VCVio/Quantum/Oracle/Model.lean`: `qromSpec`, `additiveOracleRuntime`, `qromEvalDist`, `qromEvalDistMap`, `qromEvalDist₂`, `qromEvalDistMap₂`.
- `qromEvalDist` samples **one uniform function `H : X → Y` for the whole run**, then averages the complete run against its coherent unitary; it does not resample per query.
- `qromEvalDist_eq_sum` gives the finite uniform mixture. `qromEvalDistMap` permits a challenger observation depending on hidden `H` and the classical leaf.
- `sampledEvalDist`/`sampledEvalDistMap` generalize to uniformly sampled runtime parameters; arbitrary nonuniform oracle distributions require using measure mixtures directly, not pretending these definitions accept a distribution argument.
- `isProbabilityMeasure_qromEvalDist` supplies normalization under appropriate losslessness/normalized-input hypotheses; otherwise semantics is subprobabilistic.
- **V**`VCVio/Quantum/Oracle/Classical.lean`: `qromEvalDist₂_toQuantum_eq_randomOracle` proves agreement with the classical lazy random oracle.

**Two-stage and mixed interfaces: supported, with qualifications.**
- `bind`/`run_bind` preserve the adversary register and runtime private state across stages; classical data can select stage two without discarding quantum memory.
- Multi-port runtimes can combine coherent calls and classical challenge ports with shared private memory.
- **V**`VCVio/Quantum/Oracle/ClassicalRead.lean`: `ProjectiveClassicalAnswers`, `.instrument`, `.step` implement retained classical read outcomes alongside coherent access. These particular reads impose commuting-projector hypotheses, not arbitrary reprogramming.
- **V**`VCVio/Quantum/Oracle/Emulated.lean`: `EmulatedOracle`, `.toRuntime`, `.coherent`, `.extend`, `.addRegister`; coherent port selection is encoded explicitly in a selector register.
- **V**`VCVio/Quantum/Oracle/ClassicalCalls.lean`: `QComp.coinImpl` supports private classical randomness.
- General almost-surely terminating loops are **not represented**: trees are well-founded, although unbounded finite path lengths are possible.
- **V**`docs/design/quantum-layer.md` explicitly records the missing general program-to-comb theorem, loop semantics, general compilation interface, and remaining combined private-coins/classical-QROM agreement.

## 2. Existing security infrastructure

| Topic | Finding and exact supporting declarations |
|---|---|
| Zhandry/Beals polynomial method | **No statement or proof found** in quantum source/docs or QuantumFoundations: no oracle-indicator polynomial degree bound, 2q-marginal linearity, or corresponding limited-independence theorem. “Polynomial functor” in `Comp/Basic.lean` is unrelated syntax infrastructure. |
| BBBV hybrid | **Present.** **Q**`QuantumFoundations/Pure/Norm.lean`: `queryState`, `norm_queryState_sub_queryState_le`. **Q**`QuantumFoundations/Pure/Instrument.lean`: `DSubInstrument.abs_outcomeMeasure_real_ofKraus_ofVector_sub_le`, `..._le_two_mul` connect state distance to event probability. |
| General adaptive hybrid | **V**`VCVio/Quantum/Comp/Hybrid.lean`: `QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le`, `rpow_inv_two_outcomeLawWith_le`, `krausWeight_le`, `rpow_inv_two_outcomeLawWith_le_of_isQueryBound`. These cover arbitrary instrument programs, not just pure circuits. |
| Query-local refinement | **V**`VCVio/Quantum/Comp/HybridIndex.lean`: `Hybrid.IsCoherentIndex`, `Hybrid.RespectsIndex`, `QuantumRuntime.rpow_inv_two_outcomeLawWith_le_indexMass`. |
| O2H | **No packaged O2H theorem found.** Hybrid infrastructure is a foundation, not a theorem identifying a random hidden-point query probability and giving the requested O2H conclusion. |
| Compressed oracle | **Present and proved.** **V**`VCVio/Quantum/Oracle/Compressed/Equivalence.lean`: `compressedRuntime`, `purifiedRuntime`, `outcomeLawWith_compressedRuntime`, `outcomeLaw₂_compressedRuntime`, `trace_jointPost_compressedRuntime`, `trace_jointPost_purifiedRuntime`. |
| Compressed size invariant | **V**`VCVio/Quantum/Oracle/Compressed/Size.lean`: `DatabaseSupportedOn.run_compressedRuntime`, `forallQueries_compressedRuntime`; queries increase supported database size by at most one. |
| Fourier infrastructure | **V**`VCVio/Quantum/Oracle/Compressed/Phase.lean`: `fourierMatrix`, `fourierMatrix_mul_conjTranspose`, `conjTranspose_fourierMatrix_mul`, `queryFourier`, `phaseOracle`, `phaseOracle_apply`. Useful for Lemma 2, but not its simulation theorem. |
| GHHM21/adaptive reprogramming | **No quantum adaptive-reprogramming theorem found.** Classical cryptographic reprogramming code and literature citations are not substitutes. Need concrete challenge/reset runtimes, game equivalences, and disturbance/counting bounds. |

## 3. Mathlib: Markov versus Chebyshev

- **M**`Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean:283-293`:
  `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` proves
  `(derivative^[k] P).eval x ≤ (derivative^[k] (T ℝ n)).eval x`,
  assuming `1 ≤ x`, `P.degree ≤ n`, and `|P.eval t| ≤ 1` on `[-1,1]`.
- Same file: `coeff_le_of_forall_abs_le_one`, `leadingCoeff_le_of_forall_abs_le_one`, and equality/extremality characterizations.
- **M**`Mathlib/RingTheory/Polynomial/Chebyshev.lean`: `Polynomial.Chebyshev.derivative_T_eval_one`, `iterate_derivative_T_eval_one`, giving endpoint values including `T'_n(1)=n²`.
- **M**`Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean`: `Polynomial.Chebyshev.abs_iterate_derivative_T_real_le` bounds derivatives **of Chebyshev itself** throughout the interval.
- **Full Markov brothers bound for arbitrary P throughout `[-1,1]` was not found**, after both targeted and whole-Mathlib searches. Probability-tail “Markov inequalities” are unrelated.
- Crucially, applying endpoint extremality to `P` and `-P`, with the affine reflection `t ↦ (1-t)/2`, already gives the endpoint bound needed in Lemma 7. Full Lemma 3 is unnecessary for the main quadratic result.

## 4. Undetectability feasibility

**[INFERENCE] Ratings:** “direct” = routine assembly once named prerequisites exist; “new S/M/L” = small bridge, several substantial lemmas, or foundational theorem family. These are scope ratings, not measured implementation estimates. No requested quantum security bound is claimed already formalized.

| Result | Rating | Missing work / dependencies |
|---|---|---|
| Lemma 1: 2q-point marginal linearity | **New L** | Oracle-indicator expansion; degree/support accounting under each query; real outcome coefficients; averaging over arbitrary function distributions. Start with combs; general adaptive programs need a direct semantic argument or additional normalization infrastructure. Handle empty domains explicitly when padding to exactly `2q` tuple positions. |
| Lemma 2: one-query GF(2)-linear selection | **New M** | Character/Hadamard phase-kickback for GF(2) linear maps and transpose; explicit clean-ancilla circuit; equality with simulated oracle; program translation and one-call budget preservation. Existing Fourier matrices reduce groundwork. |
| Lemma 3: full Markov brothers inequality | **New M–L** | General-polynomial interior derivative extremality. Endpoint-only specialization is **direct** from Mathlib and suffices downstream. |
| Lemma 7: planted family | **New S–M** | Binomial-mixture probability identity, Bernstein derivative at zero `N(p₁-p₀)`, polynomial identity from interval agreement, endpoint Chebyshev bound. No quantum infrastructure needed. |
| Lemma 8: zero versus one marked point | **New M + Lemma 1** | Bernoulli function law versus uniform fixed-size subset mixture; repeated-point marginal polynomials; apply Lemma 7 with degree `2q`. |
| Theorem 9: XOR sm-ud | **New M + Lemmas 1,2,7,8** | Two-stage challenge game, distinct-tweak guard, one-query simulation, endpoint distributional equivalences and total budget preservation. |
| Lemma 10: sm-ow | **New L** | Average-case quantum Boolean search bound with the stated `8(q+1)²` constant; reduction preserving adaptive challenge semantics and one-query cost via Lemma 2. Compressed-database bounds alone do not establish adversary-output success. |
| Lemma 11: sm-ud hop | **New S–M** | Transcript-preserving wrapper, final classical verification counted as one query, exact game equalities. |
| Corollary 12: sm-pre | **Direct after prerequisites** | Combine Lemma 10 and Lemma 11 with Theorem 9 at `q+1`; basic arithmetic. End-to-end inherits their infrastructure. |
| Lemma 13: endpoints | **New M** | Uniform random-table planting invariance, shift bijection, independence, and observational equality for adaptive challenge interfaces. |
| Lemma 14: events on few points | **New S–M** | Deduplicate query points, enumerate consistent assignments, product Bernoulli probabilities, sum polynomial degree bounds. |
| Lemma 15: degree of planted acceptance | **Direct assembly after Lemmas 1,14 and game definitions** | Fix auxiliary randomness, identify each oracle constraint as a one-bit event, average finite coefficient families independent of λ. |
| Theorem 16: every-group sm-ud | **Direct after Lemmas 7,13,15; new S–M group generalization** | Existing QROM only covers abelian groups. Literal “every group law” requires generalizing permutation-oracle semantics without retaining false commutativity lemmas. Avoids Lemma 2 entirely. |

**Correction:** an earlier version of this note claimed a sign inconsistency in Lemma 11. The rendered PDF (p. 8 and p. 13) prints absolute values in both Definition 4 and Lemma 11; the bars were lost in the text extraction. There is no issue (`paper-issues.md` §A).

## 5. Main-paper quantum lemmas

| Result | Rating | Missing infrastructure |
|---|---|---|
| Lemma C.3: adaptive reprogramming, `4√(Σⱼ q̂ⱼ / |X₁|)` for exponents 1 and 1/2 | **New L; literal halting scope blocked in current program model** | Define the two shared-table mixed-oracle games and reset/challenge operations; prove equivalent recording/Fourier games, per-challenge occupied-cell bound using **running total** real queries, and disturbance accumulation with constant 4. Existing compressed size/hybrid theorems are ingredients, not this result. Almost-sure termination additionally needs truncation/limit semantics; fixed well-founded programs are a narrower theorem. |
| Corollary C.1: `Pr₀ ≤ 2Pr₁ + 32Σⱼq̂ⱼ/|X₁|` | **Direct conditional on C.3** | Square-root bound and `(a+b)²≤2a²+2b²`; symmetric game exchange. As an unconditional result it inherits C.3's model gap. |
| Lemma C.8: ZeroDist `2q/√|P|` | **New M** | Instantiate BBBV with zero versus singleton Boolean oracle; average hidden-point query mass `1/|P|`; retain the target for the target-dependent second-stage measurement; use trace-distance/pure-state event bound and Cauchy–Schwarz. No full O2H framework is necessary for this specialization. General adaptive/halting scope needs the corresponding semantic bridge. |

**Recommended dependency order [INFERENCE]:** endpoint Chebyshev bridge → Lemmas 7 and 14 → comb-level Lemma 1 → planted-game endpoints and degree → Theorem 16 for abelian outputs; separately build Lemma 2/search for sm-pre and the considerably larger adaptive-reprogramming development. No builds or tests were run.