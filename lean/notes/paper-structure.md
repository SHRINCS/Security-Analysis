**Artifact blocker:** this agent has only read/search tools and is explicitly read-only. I could not create `local://paper-structure.md`. The report below is ready for the main agent to save there; that path does **not** currently represent an artifact I created.

# Paper structure and classical-ROM formalisation plan

## Summary

- The main reduction is classical-compatible: Theorem 4.1 follows from Claims 4.11–4.16; its stateful component opens Theorem 4.2’s Claims 4.1–4.10, while its stateless component imports and adapts the HK22 proof.
- The classical ITSR companion contains a complete, independent proof of the stronger bound quoted as main-paper Theorem F.1. Its hardest adaptive step is Lemma 6, not the final summation.
- Classical distinct-input reprogramming is particularly valuable: Corollary C.2 gives `q/|X1|`, independent of the number of reprogrammings. Applied to the actual reductions, only the forger’s queries count.
- A fully proved classical ROM result must distinguish **proved reductions** from **assumptions used to instantiate them**. Collection-oracle equality is conjectured; the proved ideal-model replacement has additive error. The numerical SM-DSPR bound is also conjectured.
- The undetectability companion is principally quantum and unnecessary for the classical proof. (An earlier draft of these notes claimed a sign inconsistency in its SM-UD advantage; that was an artifact of the text extraction, which drops the absolute-value bars. The PDF prints `|·|` in Definition 4 and Lemma 11; see `paper-issues.md` §A, §K.)
- The model idealizes named functions, not their internal SHA-256 implementation. Domain-separation analysis does not establish independent random functions from SHA-256.

## Source conventions

All anchors below refer to these text extractions:

- **M** = `/tmp/SHRINCS-Security-Analysis.txt`
- **I** = `/tmp/ITSR-Classical.txt`
- **U** = `/tmp/Undetectability.txt`

Line numbers identify declaration starts, not PDF pages. Some declarations are repeated in appendices; those repetitions are listed explicitly. A heading `Claim (ii)` in M:1930 is a proof subsection of Lemma 3.1, not another numbered result.

Tags describe mathematical scope. `[both]` means the statement/game supports classical and quantum adversaries, not that VCVio can formalize its quantum interpretation.

---

# 1. Complete declaration inventory

## 1.1 Main paper

### Scheme and security definitions

| Declaration | Line | Tag | One-line statement |
|---|---:|---|---|
| Definition 3.1 | 1746 | [scheme-spec] | Honest state evolution, successful-signature correctness, and execution failure. |
| Lemma 3.1 | 1783 | [scheme-spec] | Every non-failing honest signature verifies; ideal grinding fails per call with probability `(1-p_sum)^(2^c)` and per execution at most `L` times that. |
| Conjecture 3.1 | 1958 | [scheme-spec] | Every seed, admissible grinding tweak, and message digest has a valid counter below `2^c`. |
| Lemma 3.2 | 1963 | [combinatorial/probability-only] | Global grind-completeness fails in the ideal model with probability at most `2^n 2^72 2^(2n)(1-p_sum)^(2^c) < 2^-994`. |
| Definition 4.1 | 2002 | [scheme-spec] | Keyed hash function `F : K × M → N`. |
| Definition 4.2 | 2009 | [scheme-spec] | Tweakable hash function `Th : P × T × M → N`. |
| Definition 4.3 | 2028 | [both] | PRF distinguishing game with bounded classical challenge access. |
| Definition 4.4 | 2085 | [both] | SM-TCR: chosen-message targets at distinct tweaks before public-parameter revelation. |
| Definition 4.5 | 2126 | [both] | SM-PRE: invert one image of a hidden uniform input at a challenged tweak. |
| Definition 4.6 | 2170 | [both] | SM-UD: distinguish hashed uniform inputs from uniform outputs. |
| Definition 4.7 | 2226 | [both] | SM-TCR-EXCL: target collision may use the challenge tweak or its exclusive partner. |
| Definition 4.8 | 2268 | [both] | S-TCR(Prop): target is the first counter-search output satisfying `Prop`. |
| Definition 4.9 | 2305 | [both] | SM-rTCR: known public parameter, distinct tweaks, up to `K` random-sampling attempts per challenge. |
| Definition 4.10 | 2350 | [both] | SM-DSPR: decide whether a challenged input has a second preimage, subtracting the always-yes baseline. |
| Definition 4.11 | 2394 | [both] | ITSR: fresh key-message pair whose mapped digest is covered by challenge digests. |
| Definition 4.12 | 2438 | [both] | Collection security adds first-stage collection access with bidirectional challenge-tweak reservation. |
| Conjecture 4.1 | 2541 | [both] | Collection-oracle queries do not increase insecurity under interface-separated accounting. |
| Corollary 4.1 | 2555 | [both] | Assuming Conjecture 4.1, stand-alone bounds apply unchanged to collection members. |
| Lemma 4.1 | 2564 | [both] | Ideal collection security is bounded by stand-alone security plus parameter-guessing error. |
| Lemma 4.2 | 2608 | [both] | Independent auxiliary random functions can be simulated without charging evaluations to the attacked function. |
| Lemma 4.3 | 2655 | [scheme-spec] | Byte-layout analysis classifies possible cross-function SHA-256 input coincidences. |
| Definition 4.13 | 2759 | [scheme-spec] | Digital signature scheme `(Kg, Sign, Verify)`. |
| Definition 4.14 | 2768 | [both] | Standard EU-CMA: valid signature on a previously unsigned message. |
| Definition 4.15 | 2802 | [both] | SHRINCS EU-CMA permits adversarial tree shape before keygen and signing-path choice per query. |
| Theorem 4.1 | 2874 | [both] | SHRINCS EU-CMA reduces to two PRFs, stateful message-hash/reprogramming terms, seven stateful and ten stateless summands, and `epsilon_ds`. |
| Theorem 4.2 | 2949 | [both] | Ideal-key FXMSS EU-CMA reduces to SM-rTCR, DI-Repro, and seven collection summands. |
| Theorem 4.3 | 3027 | [both] | HK22 SLH-DSA security bound restated with collection accounting and separated chain/FORS collision terms. |
| Definition 4.16 | 3116 | [both] | FXMSS EU-CMA idealizes secrets/randomizers, gives the full public key, and permits distinct adversarial signing anchors. |

### Main reductions and concrete bounds

| Declaration | Line | Tag | One-line statement |
|---|---:|---|---|
| Claim 4.1 | 3264 | [both] | `F.0→F.1` costs SM-rTCR for `Hmsg_sf`. |
| Claim 4.2 | 3354 | [both] | `F.1→F.2` costs distinct-input adaptive reprogramming. |
| Claim 4.3 | 3408 | [both] | `F.2→F.3` costs S-TCR for the grinding hash. |
| Claim 4.4 | 3563 | [both] | `F.3→F.4` costs `w` SM-UD advantages for chain replacement. |
| Claim 4.5 | 3676 | [both] | `F.4→F.5` costs SM-TCR for chain collisions. |
| Claim 4.6 | 3701 | [both] | `F.5→F.6` costs SM-PRE for chain inversion. |
| Claim 4.7 | 3724 | [both] | `F.6→F.7` costs SM-TCR for WOTS+C key compression. |
| Claim 4.8 | 3748 | [both] | `F.7→F.8` costs SM-TCR for ordinary tree-node collisions. |
| Claim 4.9 | 3794 | [both] | `F.8→F.9` costs SM-TCR-EXCL for mismatched node roles/tree shapes. |
| Claim 4.10 | 3833 | [both] | `Succ_F.9(A)=0`. |
| Corollary 4.2 | 3883 | [quantum] | FXMSS bound using square-root-free reprogramming, doubling post-hop collection terms. |
| Claim 4.11 | 3959 | [both] | Full-scheme secret derivation replacement costs one PRF term. |
| Claim 4.12 | 3973 | [both] | Both paths’ randomizer replacement costs one combined PRFmsg term. |
| Claim 4.13 | 4026 | [both] | Full-scheme stateful digest-collision abort costs SM-rTCR. |
| Claim 4.14 | 4084 | [both] | Full-scheme shared stateful reprogramming hop costs DI-Repro. |
| Claim 4.15 | 4194 | [both] | Stateful forgery route is bounded by seven augmented FXMSS collection summands. |
| Claim 4.16 | 4338 | [both] | Stateless forgery route is bounded by ten augmented HK22 summands, excluding PRFs. |
| Lemma 5.1 | 4532 | [scheme-spec] | Exact/worst-case per-function verification query counts for both branches. |
| Definition 5.1 | 4688 | [both] | Interface-separated Convention I versus monolithic Convention M resource accounting. |
| Claim 6.1 | 5188 | [numeric] | Concrete classical/quantum SLH-DSA bounds at `qs=2^40`, conditional on conjectured SM-DSPR bound. |
| Claim 6.2 | 5251 | [numeric] | Concrete classical/quantum FXMSS bounds at `qs=L`. |
| Claim 6.3 | 5320 | [both] | Full-scheme bounds with classical or alternative quantum treatments of the shared reprogramming hop. |
| Claim 6.4 | 5360 | [numeric] | Proposed-parameter full-scheme bounds, conditional on the SM-DSPR conjecture. |

### Appendices

| Declaration | Line | Tag | One-line statement |
|---|---:|---|---|
| Definition C.1 | 5842 | [both] | Adaptive reprogramming game at a uniform first coordinate and adversarial second coordinate. |
| Lemma C.1 | 5875 | [quantum] | GHHM21 reprogramming bound `3R/2 * sqrt(q/|X1|)`. |
| Lemma C.2 | 5883 | [classical] | Classical reprogramming advantage at most `Rq/|X1|`. |
| Lemma C.3 | 5916 | [quantum] | Adapted LGX25 bound on differences of probabilities or square roots using per-call query counts. |
| Corollary C.1 | 6030 | [quantum] | `Pr[Repro0⇒1] ≤ 2 Pr[Repro1⇒1] + 32 Σ qhat_j/|X1|`, symmetrically. |
| Lemma C.4 | 6135 | [classical] | Reprogramming costs at most `Σ E[n_j]/|X1|`, counting prior queried seeds at each call’s second coordinate. |
| Definition C.2 | 6172 | [both] | DI-Repro refuses repeated second-coordinate inputs. |
| Lemma C.5 | 6189 | [both] | DI-Repro is simulated exactly inside Repro by filtering refused calls. |
| Corollary C.2 | 6217 | [classical] | DI-Repro advantage at most `E[qpre]/|X1| ≤ q/|X1|`. |
| Corollary C.3 | 6248 | [both] | Concrete class-wide and reduction-specific reprogramming bounds; actual classical hop costs `qh/2^n`. |
| Definition C.3 | 6320 | [both] | Bernoulli-marked random-function average-case search. |
| Lemma C.6 | 6344 | [both] | Average search success at most `lambda(q+1)` classically, `8lambda(q+1)^2` quantumly. |
| Definition C.4 | 6360 | [both] | ZeroDist: distinguish zero from a uniformly located marked point, revealed after querying. |
| Lemma C.7 | 6383 | [classical] | ZeroDist advantage at most `q/|P|`. |
| Lemma C.8 | 6400 | [quantum] | ZeroDist advantage at most `2q/sqrt(|P|)`. |
| Lemma C.9 | 6471 | [both] | Hidden-slice reprogramming reduces to ZeroDist without increasing query count. |
| Definition D.1 | 6553 | [both] | Fully explicit SM-TCR collection game with separate challenge/collection query lists. |
| Lemma 4.1, repeated | 6602 | [both] | Restatement followed by ideal-collection proof. |
| Lemma 4.2, repeated | 6768 | [both] | Restatement followed by independent-function simulation proof. |
| Lemma 4.3, repeated | 6804 | [scheme-spec] | Restatement followed by byte-layout/domain-separation proof. |
| Definition 4.7, repeated | 7235 | [both] | Restatement of SM-TCR-EXCL. |
| Theorem E.1 | 7283 | [both] | Exclusive-tweak collision security reduces to average search and ZeroDist. |
| Lemma F.1 | 7396 | [combinatorial/probability-only] | Independent uniform challenge digests cover an independent digest with probability `Gamma_(h,k,t)(p)`. |
| Theorem F.1 | 7443 | [classical] | Strong ITSR search-plus-pulls bound quoted from Kud26a Theorem 2. |
| Theorem F.2 | 7508 | [both] | ITSR bound by ordinary reprogramming plus average search. |
| Theorem F.3 | 7623 | [quantum] | Improved ITSR reprogramming bounds, including square-root-free form. |
| Theorem G.1 | 7689 | [quantum] | Three generic SM-rTCR bounds using original/tighter/squared reprogramming. |
| Corollary G.1 | 7846 | [classical] | SM-rTCR success at most `(q+1)/|N| + [Kq+pK(K−1)/2]/|R|`. |

Additional assumptions, although not among the requested declaration categories:

- **Assumption 3.1**, M:1767 vicinity: independent uniform grinding outputs.
- **Assumption 4.1**, M:2723 vicinity: five independent named-function random objects; root-distribution premises and `epsilon_ds`.
- **Unnumbered SM-DSPR conjecture**, M:4870–4940, Table 6: classical advantage at most `(2q+1)/|N|` for length-preserving functions. This is an essential dependency of concrete stateless/full-scheme numbers.

## 1.2 ITSR-Classical

| Declaration | Line | Tag | One-line statement |
|---|---:|---|---|
| Definition 1 | 199 | [combinatorial/probability-only] | Digests, instance/coordinate projections, `N'=2^h t^k`, `theta=2^-h`. |
| Definition 2 | 209 | [combinatorial/probability-only] | Covered set is the union of per-instance Cartesian products of revealed coordinates. |
| Definition 3 | 220 | [combinatorial/probability-only] | Instance load counts challenge-list entries with that instance. |
| Definition 4 | 228 | [both] | ITSR game with random challenge keys and fresh covered output pair. |
| Definition 5 | 276 | [combinatorial/probability-only] | `Gamma_j(r)=E[(1−(1−1/t)^g)^j]`, `g~Bin(r,theta)`. |
| Lemma 1 | 290 | [combinatorial/probability-only] | `Gamma_j` is the coverage probability for any fixed set of `j` coordinates. |
| Definition 6 | 323 | [combinatorial/probability-only] | `Gamma+(r)=Σ_(omega=1)^k binom(k,omega)t^-omega Gamma_(k−omega)(r)`. |
| Theorem 1 | 436 | [classical] | Crude bound: search plus probability of any pulled challenge. |
| Theorem 2 | 446 | [classical] | Main bound: search plus a sum over distinct pulled witnesses. |
| Corollary 1 | 493 | [classical] | One-pull term expressed as expected covered-set increment plus higher-order remainder. |
| Lemma 2 | 662 | [classical] | Pre-sampled lazy oracle is distributionally identical to the real game. |
| Definition 7 | 683 | [classical] | Fresh direct-query table points receive immutable creation indices. |
| Lemma 3 | 692 | [classical] | Challenges partition into fresh, pulled, and repeated. |
| Lemma 4 | 709 | [classical] | Every win has a fresh/pulled coordinate-witness structure. |
| Lemma 5 | 773 | [combinatorial/probability-only] | Fixed direct-query digest is covered by pre-sampled fresh digests with probability `Gamma_k(r)`. |
| Lemma 6 | 790 | [classical] | Conditional probability of pulling fixed `m` creation indices is at most `(r)_m/|K|^m`. |
| Lemma 7 | 895 | [combinatorial/probability-only] | Digest conditions for a witness structure have probability `theta^m t^-omega Gamma_(k−omega)(r)`. |
| Lemma 8 | 922 | [combinatorial/probability-only] | Counts output indices, witness sets, coordinate sets, and surjections. |
| Lemma 9 | 938 | [classical] | Union-bound assembly proves Theorem 2. |
| Lemma 10 | 1056 | [classical] | Bounding all pulls as bad proves Theorem 1. |
| Lemma 11 | 1115 | [combinatorial/probability-only] | Higher-order pull terms admit factorial/geometric bounds relative to the one-pull term. |
| Lemma 12 | 1474 | [combinatorial/probability-only] | Binomial-moment upper bounds for `Gamma_j` and pull harm factors. |
| Lemma 13 | 2051 | [numeric] | Certified truncated-sum and exponential brackets for `Gamma_j`. |

No numbered Claim or Conjecture occurs as an independent declaration in this document.

## 1.3 Undetectability

The document uses a **single numbering sequence across declaration kinds**.

| Declaration | Line | Tag | One-line statement |
|---|---:|---|---|
| Lemma 1 | 187 | [quantum] | Output probabilities are linear combinations of oracle `2q`-point marginals. |
| Lemma 2 | 258 | [quantum] | A GF(2)-linear selection oracle can be simulated with one Boolean/vector-oracle query. |
| Lemma 3 | 384 | [combinatorial/probability-only] | Markov brothers’ inequality: bounded degree-`d` polynomial has derivative at most `d²` on `[-1,1]`. |
| Definition 4 | 404 | [both] | SM-UD game; advantage is the absolute difference, as in the main paper (bars lost in the text extraction). |
| Definition 5 | 417 | [both] | SM-PRE game. |
| Definition 6 | 429 | [both] | SM-OW replaces hash-generated targets by uniform outputs. |
| Lemma 7 | 454 | [combinatorial/probability-only] | Binomial planted-family mixture of acceptance degree `d` satisfies `|p1−p0|≤d²/N`. |
| Lemma 8 | 555 | [quantum] | Distinguish zero Boolean oracle from one uniform marked point with advantage at most `4q_f²/|M|`. |
| Theorem 9 | 648 | [quantum] | XOR-output SM-UD advantage at most `4q²/|M|`. |
| Lemma 10 | 678 | [quantum] | Quoted SM-OW bound `8(q+1)²/|N|`. |
| Lemma 11 | 706 | [both] | `|Succ_sm-pre − Succ_sm-ow| = Adv_sm-ud(C)`, with one extra classical verification query. |
| Corollary 12 | 727 | [quantum] | SM-PRE bound `8(q+1)²/|N| + 4(q+1)²/|M|`. |
| Lemma 13 | 857 | [both] | Planted-family endpoints reproduce uniform-output and hashed-input SM-UD games. |
| Lemma 14 | 880 | [combinatorial/probability-only] | Event depending on `t` Bernoulli oracle points has acceptance polynomial degree at most `t`. |
| Lemma 15 | 923 | [quantum] | Directly planted oracle acceptance polynomial has degree at most `2q`. |
| Theorem 16 | 990 | [quantum] | SM-UD advantage at most `4q²/|M|` for every output group law. |

No other numbered Definition/Theorem/Lemma/Claim/Corollary/Conjecture is present.

---

# 2. Dependency DAG and provenance

## 2.1 Main EU-CMA reductions

```text
Scheme specification, address uniqueness, valid full binary structure
    ├── Definition 4.15: SHRINCS game
    ├── Definition 4.16: ideal FXMSS game
    └── Conjecture 3.1: every grinding search terminates within cap

Definitions 4.3–4.12
    └── Claims 4.1–4.10
          ├── 4.1: SM-rTCR message-digest collision
          ├── 4.2: DI-Repro
          ├── 4.3: grinding S-TCR
          ├── 4.4: w-step SM-UD chain hybrid
          ├── 4.5: chain SM-TCR
          ├── 4.6: chain SM-PRE
          ├── 4.7: public-key-compression SM-TCR
          ├── 4.8: internal-node SM-TCR
          ├── 4.9: cross-role SM-TCR-EXCL
          └── 4.10: no winning route remains
                └── telescope → Theorem 4.2

HK22 corrected SPHINCS+ proof, adapted accounting
    └── Theorem 4.3: SLH-DSA
          └── ten non-PRF summands → augmented Claim 4.16

Claims 4.11,4.12: replace secrets and combined randomizers once
    → Claim 4.13: stateful message collision
    → Claim 4.14: shared stateful reprogramming
    → Claim 4.15: augmented Claims 4.3–4.10
    → Claim 4.16: augmented HK22 stateless reductions
    → Game 6 has success zero
    → telescope + epsilon_ds → Theorem 4.1
```

Important: Theorem 4.1 does **not** simply invoke Theorems 4.2 and 4.3 as opaque EU-CMA black boxes. It opens their primitive reductions to simulate the other path in the appropriate stage and account for shared collection access. See M:2830–2872, 4194–4210, 4338–4375.

### Auxiliary dependencies

- **Claim 4.10:** full-tree structure invariant, anchor exhaustion wrapper of Remark 4.6, constant-sum encoding, and all prior abort exclusions; proof at M:3833–3881.
- **Claims 4.2 and 4.14:** Definition C.2. Classical instantiation uses `C.4 → C.2 corollary → C.3 corollary`.
- **Claims 4.3–4.9 and augmented 4.15–4.16:** Definition 4.12’s reservation discipline.
- **Lemma 5.1:** supplies `V_sf`, `V_sl` for reduction query budgets.
- **Lemma 4.1:** collection-to-stand-alone transfer with additive loss, proved in Appendix D using C.9.
- **Lemma 4.2:** removes independent auxiliary-function evaluation costs.
- **Lemma 4.3 + Assumption 4.1:** distinguish layout facts from named-function independence assumptions.
- **Lemma 3.2:** proves rare failure of Conjecture 3.1 in an unconditioned ideal model; it is not automatically a proof of the conjecture.

## 2.2 Classical generic-bound DAG

```text
C.4: per-call queried-seed bound
    ├── C.2 lemma: Rq/|X1|
    ├── C.5 filtering → C.2 corollary: q/|X1| for distinct inputs
    │                    └── C.3 corollary: actual SHRINCS hop qh/2^n
    └── G.1 corollary: Kq + pK(K−1)/2 accounting

C.7: classical hidden-parameter search
    └── C.9: hidden-slice simulation
          ├── Lemma 4.1: ideal collection transfer
          └── E.1: exclusive-tweak collision security
C.6: classical average search
    ├── E.1
    ├── F.2 classical
    └── G.1 corollary

I.Definitions 1–7
    → I.Lemma 1: coverage identity
    → I.Lemma 2: pre-sampled lazy oracle
    → I.Lemma 3: classification
    → I.Lemma 4: winning witness decomposition
        ├── I.Lemma 5: search
        ├── I.Lemma 6: adaptive pull probability
        ├── I.Lemma 7: digest probability
        └── I.Lemma 8: counting
             → I.Lemma 9 = I.Theorem 2
                  ├── I.Corollary 1
                  └── M.Theorem F.1, quoted as Kud26a
                       + equal-fibre MAP lift, M.Remark F.1
                       → classical ITSR primitive bound

I.Lemmas 2–5 + pull union bound → I.Lemma 10 = I.Theorem 1
I.Lemma 11 → higher-pull remainder estimates
I.Lemma 12 → symbolic moment upper forms
I.Lemma 13 → certified numerical evaluation
```

## 2.3 External versus locally proved results

| Dependency | Status in supplied documents |
|---|---|
| HK22 corrected SPHINCS+/SLH-DSA security theorem | **Quoted**, M Theorem 4.3; resource restatement and split collision terms explained, complete original proof not reproduced. |
| BHK+19 | Security notions and proof architecture imported; main FXMSS sequence is written out. M Lemma F.1 is attributed coverage identity. |
| GHHM21 | M Lemma C.1 **quoted without proof**; irrelevant to a purely classical target. |
| LGX25/LGXZ26 | M Lemma C.3 is an **adaptation of an external theorem/proof**, not an independent quantum-foundations development. |
| HRS16/BHRvV21/Kud25 | M Lemma C.6 **quoted** average-search bound; its classical part is straightforward to prove independently. |
| Kud25 Lemma 6.1.8 | M Lemma C.7 **quoted** classical ZeroDist bound. |
| AHU18/GHHM21/HHK17 one-way-to-hiding | External justification for M Lemma C.8. |
| Kud26a | M Theorem F.1 **quoted**; its proof **is supplied** in I Theorem 2/Lemmas 1–9. |
| YTA23 | M F.2 re-derives the reprogramming proof with corrected counts. |
| DKKW25 | M G.1 proof follows its reduction and is reproduced; G.1 corollary proves improved classical accounting. |
| HKRY23 | Grinding-hop ancestry and generic S-TCR bound; the FXMSS hop is explained locally, generic primitive theorem remains external. |
| Classical PRF/SM-TCR/SM-PRE/SM-UD bounds | Table 6 imports these from BHK+19, HK22, Kud25, DSS05/Hül13, etc.; not all are proved in supplied papers. |
| SM-DSPR generic bound | **Conjectured**, not a theorem. |
| U Lemma 1 | External Zhandry result, but a proof is included. |
| U Lemma 3 | Markov brothers’ inequality **quoted without proof**. |
| U Lemma 10 | SM-OW bound explicitly **not reproved**. |
| U Lemmas 2,7,8,11,13–15; Theorems 9,16; Corollary 12 | Proofs supplied. |

---

# 3. ITSR-Classical: complete mathematical statements

## 3.1 Symbols and game

Source: I:149–174, 199–335.

- `h ≥ 0`; `k,t ≥ 1`.
- `K` is the finite, nonempty **key space**; `M` is the message space.
- `q` is the adversary’s maximum number of direct classical random-oracle queries.
- `r` is the maximum number of classical challenge queries.
- A digest is `u=(I,J_1,...,J_k)` in
  `D={0,1}^h × [t]^k`.
- `I(u)` is its instance, `J_i(u)` its `i`th coordinate.
- `N' = |D| = 2^h t^k`, `theta=2^-h`.
- For a finite digest set/list `G`:
  \[
  S_i(I)(G)=\{J_i(u):u\in G,\ I(u)=I\},
  \]
  \[
  S(G)=\bigcup_{I\in\{0,1\}^h}
       \{(I,J):\forall i\in[k],\ J_i\in S_i(I)(G)\}.
  \]
- Load, counting list multiplicity:
  \[
  g_I(V_1,\ldots,V_r)=|\{j:I(V_j)=I\}|.
  \]
  For iid uniform `V_j`, a fixed instance has load `Bin(r,theta)`.
- `(r)_m=r(r−1)...(r−m+1)`, zero if `m>r`.
- `St(omega,m)` is a Stirling number of the second kind;
  `m! St(omega,m)` counts surjections from an `omega`-set to an `m`-set.
- `0^0=1`.

The challenge oracle, on message `M_j`, samples independent uniform `K_j∈K`, records `(K_j,M_j)`, and returns `(K_j,H'(K_j,M_j))`. It refuses calls after `r`. Repeated messages and repeated pairs are allowed. The adversary wins by outputting a pair not in the challenge list whose digest belongs to the covered set of challenge digests. Verification is one extra direct evaluation, explaining `q+1`.

\[
\Gamma_j(r)=
\mathbb E_{g\sim\operatorname{Bin}(r,\theta)}
   [1-(1-1/t)^g]^j
=\sum_{g=0}^{r}\binom rg\theta^g(1-\theta)^{r-g}
   [1-(1-1/t)^g]^j,
\quad \Gamma_0(r)=1.
\]

\[
\Gamma^+(r)=\sum_{\omega=1}^{k}
  \binom k\omega t^{-\omega}\Gamma_{k-\omega}(r).
\]

Here `K` is a space; do not confuse it with the integer sampling budget `K` in main-paper Definition 4.9.

## 3.2 Theorems and corollary

### Theorem 1 — I:436–444

Let `H' : K × M → D` be a uniformly random function. For every classical computationally unbounded adversary making at most `q` direct queries and `r` adaptively interleaved challenge queries, with iid uniform challenge keys and repetitions allowed,
\[
\operatorname{Succ}^{ITSR}_{H'}(A)
\le (q+1)\Gamma_k(r)
+r\frac{\min(q,|K|)}{|K|}.
\]

### Theorem 2 — I:446–466

Under exactly the same model and resource conditions,
\[
\operatorname{Succ}^{ITSR}_{H'}(A)
\le (q+1)\Gamma_k(r)
+\sum_{m=1}^{\min(k,q,r)}
 (q+1)\binom qm(r)_m|K|^{-m}\theta^m
 \sum_{\omega=m}^{k}
 \binom k\omega m!\operatorname{St}(\omega,m)
 t^{-\omega}\Gamma_{k-\omega}(r).
\]

### Corollary 1 — I:477–504

Define, for uniform `I` independent of iid uniform `V=(V_1,...,V_r)`,
\[
\Delta^*(I,V)=
 \prod_{i=1}^{k}(|S_i(I)(V)|+1)
 -\prod_{i=1}^{k}|S_i(I)(V)|,
\]
and
\[
R_2=\sum_{m=2}^{\min(k,q,r)}
 (q+1)\binom qm(r)_m|K|^{-m}\theta^m
 \sum_{\omega=m}^{k}
 \binom k\omega m!\operatorname{St}(\omega,m)
 t^{-\omega}\Gamma_{k-\omega}(r).
\]
Then
\[
\operatorname{Succ}^{ITSR}_{H'}(A)
\le(q+1)\Gamma_k(r)
+\frac{rq(q+1)\mathbb E[\Delta^*]}{|K|N'}+R_2.
\]
The identity used is
\[
\theta\Gamma^+(r)=\mathbb E[\Delta^*]/N'.
\]

## 3.3 Lemmas 1–13

### Lemma 1 — I:290–301

Let `I` be uniform and `V_1,...,V_r` iid uniform digests, independent of `I`. Put `y_i=|S_i(I)(V)|/t`. For every `F⊆[k]`,
\[
\mathbb E\prod_{i\in F}y_i=\Gamma_{|F|}(r).
\]
Equivalently, independent uniform `J∈[t]^k` satisfies
\[
\Pr[\forall i\in F,\ J_i\in S_i(I)(V)]=\Gamma_{|F|}(r).
\]
In particular an independent uniform digest `u` satisfies
`Pr[u∈S(V)]=Gamma_k(r)`.

### Lemma 2 — I:662–675

Independently pre-sample:

- uniform digests `U_1,...,U_(q+1)`;
- uniform digests `V_1,...,V_r`;
- uniform keys `K_1,...,K_r`;
- adversary coins `rho`.

Use a persistent lazy table. The next previously unseen direct-query point receives the next unused `U`; a fresh final verification point receives the next unused `U`. Existing points return their stored values without consuming a `U`. Challenge `j` uses `K_j`, returning an existing value if its pair is already present, otherwise assigning `V_j`.

The resulting transcript has exactly the real-game distribution. Values never change; a point was created from a `V_j` iff it was created by a fresh challenge, in which case it is a challenge pair. Direct/verification-created points originate in `U`.

### Lemma 3 — I:692–703

Each challenge is exactly one of:

1. fresh: absent pair, digest `V_j`;
2. pulled: direct-query-created pair not yet challenged, digest `U_b`;
3. repeated: already a challenge pair, previous challenge digest.

Writing `H^f⊆{V_j}` and `H^p⊆{U_b:b∈[q]}`,
\[
S(H_{\rm final})=S(H^f\cup H^p).
\]

### Lemma 4 — I:709–732

A winning output is a non-challenge table point with a unique creation index `a∈[q+1]` and digest `U_a`. Put `I=I(U_a)`.

For each coordinate choose a fresh witness if available; let `F` be these coordinates. For every remaining `i∈W=[k]\F`, choose a pulled witness `U_(b_i)`. Then `b_i≠a`.

Put `B={b_i:i∈W}`, `m=|B|`, and `W_b={i:b_i=b}`. The `W_b` partition `W` into nonempty blocks and
`m≤min(k,q,r)`. Event `E(a,B,(W_b))` consists of:

1. every `b∈B` is pulled;
2. `I(U_b)=I(U_a)` for every `b∈B`;
3. `(U_b)_i=(U_a)_i` for all `b∈B,i∈W_b`;
4. `(U_a)_i∈S_i(I)(V)` for all `i∈F`.

For `W=∅`, write `E_0(a)={U_a∈S(V)}`. Then
\[
Win\subseteq\bigcup_aE_0(a)\ \cup\
 \bigcup_{a,B\ne\varnothing,(W_b)}E(a,B,(W_b)).
\]

### Lemma 5 — I:773–779

For each `a∈[q+1]`,
\[
\Pr[U_a\in S(V)]=\Gamma_k(r),
\qquad
\Pr[\bigcup_aE_0(a)]\le(q+1)\Gamma_k(r).
\]

### Lemma 6 — I:790–811

For fixed `a`, fixed `B⊆[q]` of size `m`, and nonempty disjoint `W_b` with union `W`, use conditions (i)–(iv) above. Uniformly in the pre-sampled values and adversary coins,
\[
\Pr[(i)\mid U,V,\rho]\le (r)_m/|K|^m.
\]
For `m>r`, both sides vanish. Consequently,
\[
\Pr[E(a,B,(W_b))]
=\mathbb E_{U,V,\rho}\left[
 1_{(ii)\wedge(iii)\wedge(iv)}
 \Pr[(i)\mid U,V,\rho]\right]
\le\frac{(r)_m}{|K|^m}
 \Pr[(ii)\wedge(iii)\wedge(iv)].
\]

The proof uses chronology and fresh independent keys, not independence between adaptive pull events.

### Lemma 7 — I:895–905

Let `a∈[q+1]`, `B⊆[q]\{a}`, `|B|=m`, and let `W⊆[k]`, `|W|=omega`, partition into nonempty labeled blocks `W_b`. Then
\[
\Pr[(ii)\wedge(iii)\wedge(iv)]
=\theta^m t^{-\omega}\Gamma_{k-\omega}(r).
\]

### Lemma 8 — I:922–931

For fixed `a,m`, choices of `B⊆[q]\{a}` number:

- exactly `binom(q−1,m)` if `a∈[q]`;
- exactly `binom(q,m)` otherwise;

hence at most `binom(q,m)`.

For `m≤omega≤k`, there are `binom(k,omega)` coordinate sets `W` and `m!St(omega,m)` surjections `W→B`. The output index has at most `q+1` choices.

### Lemma 9 — I:938–950

The union bound applied to Lemma 4, using Lemmas 5–8, gives exactly the inequality of Theorem 2 above.

### Lemma 10 — I:1056–1065

Let `Bad_j` mean that challenge `j` occurs and is pulled; `Bad=⋃_(j≤r)Bad_j`. Then
\[
\Pr[Bad_j]\le\min(q,|K|)/|K|,
\quad
\Pr[Bad]\le r\min(q,|K|)/|K|,
\]
and
\[
Succ^{ITSR}_{H'}(A)
\le\Pr[Win\land\neg Bad]+\Pr[Bad]
\le(q+1)\Gamma_k(r)+r\min(q,|K|)/|K|.
\]

### Lemma 11 — I:1092–1144

For `1≤m≤min(k,q,r)`, define
\[
A_m=\sum_{\omega=m}^{k}
 \binom k\omega m!St(\omega,m)t^{-\omega}\Gamma_{k-\omega}(r),
\quad
T_m=(q+1)\binom qm(r)_m|K|^{-m}\theta^m A_m,
\]
and `eta=qr theta/|K|`, so `A_1=Gamma+` and `T_1=(q+1)eta A_1`.

(a)
\[
T_m\le\frac{m^k\eta^{m-1}}{m!}T_1.
\]

(b) If `eta≤exp(−(k−1)/2)`, then
\[
R_2\le2^k\eta T_1.
\]

(c) For `k≥2`, define
\[
\lambda_m=\frac{A_{m+1}}{(m+1)A_m},\quad
\lambda=\max_{1\le m\le k-1}\lambda_m.
\]
Then
\[
T_{m+1}\le\lambda_m\eta T_m,
\quad
T_m\le\left(\prod_{i=1}^{m-1}\lambda_i\right)\eta^{m-1}T_1
\le(\lambda\eta)^{m-1}T_1.
\]
If `lambda eta<1`,
\[
R_2\le\frac{\lambda\eta}{1-\lambda\eta}T_1.
\]

### Lemma 12 — I:1474–1488

For integer `r≥0` and `g~Bin(r,theta)`:

(i) For `0≤j≤k`,
\[
\Gamma_j(r)\le\frac{\mathbb E[g^j]}{t^j},
\qquad
\mathbb E[g^j]=\sum_{s=0}^{j}St(j,s)(r)_s\theta^s.
\]

(ii) Define
\[
\Delta_m(x)=\sum_{s=0}^{m}(-1)^{m-s}\binom ms(x+s)^k.
\]
Replacing each `Gamma_(k−omega)(r)` in `A_m` by
`E[g^(k−omega)]/t^(k−omega)` gives exactly
`t^-k E[Delta_m(g)]`, and
\[
A_m\le t^{-k}\mathbb E[\Delta_m(g)].
\]

### Lemma 13 — I:2051–2068

Let `r≥1`, `theta∈(0,1)`, `t≥2`,
\[
P_g=\binom rg\theta^g(1-\theta)^{r-g},
\quad u_g=1-(1-1/t)^g.
\]

(i) For integer `G≥0` with `r theta<G+2`, and `j≥0`,
\[
\sum_{g=0}^{\min(G,r)}P_gu_g^j
\le\Gamma_j(r)
\le\sum_{g=0}^{\min(G,r)}P_gu_g^j
+\frac{(r\theta)^{G+1}}{(G+1)!}
 \frac1{1-r\theta/(G+2)}.
\]

(ii) For integer `n≥0`,
\[
e^{-n\theta/(1-\theta)}\le(1-\theta)^n\le e^{-n\theta}.
\]

(iii) For real `x≥0` and integer `M≥x`, the exponential Taylor remainder is bounded by
\[
\left|e^{-x}-\sum_{i=0}^{M}\frac{(-x)^i}{i!}\right|
\le\frac{x^{M+1}}{(M+1)!}.
\]

**Extraction qualification:** the text extraction drops visible absolute-value bars in part (iii); the accompanying proof at I:2134–2141 explicitly invokes the alternating-series remainder magnitude. The displayed formula above records that proof-supported interpretation rather than silently claiming the bars survived extraction.

---

# 4. Main-paper exact reduction statements

## 4.1 Compact notation for exact formulas

Write
`I_prop(f; time, targets, collectionBudget)` for the paper’s `InSec^prop`; omit the last parameter for noncollection notions.

All `q_i`, times, and budgets below are the paper’s bounds, not newly estimated quantities.

Define
\[
\begin{aligned}
C_{\rm sf}(\tau;\,s,q_i,b_i)={}&
 I_{S\text{-}TCR(Prop)}(H_{\rm grind}\in Th_\lambda;\tau,s,b_0)\\
&+w I_{sm\text{-}ud}(F\in Th_\lambda;\tau,q_1,b_1)\\
&+I_{sm\text{-}tcr}(F\in Th_\lambda;\tau,q_2,b_2)
 +I_{sm\text{-}pre}(F\in Th_\lambda;\tau,q_1,b_1)\\
&+I_{sm\text{-}tcr}(Th_{l_{\rm sf}}\in Th_\lambda;\tau,q_4,b_4)\\
&+I_{sm\text{-}tcr}(H\in Th_\lambda;\tau,q_3,b_3)\\
&+I_{sm\text{-}tcr\text{-}excl}(Th_{2\cup l_{\rm sf}}\in Th_\lambda;\tau,q_5,b_5).
\end{aligned}
\]

Define the **ten** stateless summands
\[
\begin{aligned}
C_{\rm sl}(\tau',\tau;\,s,q_h',q_i,b)={}&
 I_{itsr}(H_{\rm msg}^{sl};\tau',s,q_h')\\
&+wI_{sm\text{-}ud}(F\in Th_\lambda;\tau,q_2,b)\\
&+I_{sm\text{-}tcr}(F\in Th_\lambda;\tau,q_3,b)
 +I_{sm\text{-}tcr}(F\in Th_\lambda;\tau,q_7,b)\\
&+I_{sm\text{-}pre}(F\in Th_\lambda;\tau,q_2,b)\\
&+I_{sm\text{-}tcr}(H\in Th_\lambda;\tau,q_4,b)\\
&+I_{sm\text{-}tcr}(Th_k\in Th_\lambda;\tau,q_5,b)\\
&+I_{sm\text{-}tcr}(Th_{l_{\rm sl}}\in Th_\lambda;\tau,q_6,b)\\
&+3I_{sm\text{-}tcr}(F\in Th_\lambda;\tau,q_8,b)
 +I_{sm\text{-}dspr}(F\in Th_\lambda;\tau,q_8,b).
\end{aligned}
\]

These definitions are only report abbreviations for the fully expanded sums.

## 4.2 Theorem 4.2 — M:2949–3007

Parameters `n,w,h_sf,l_sf`; adversary commits to a valid structure with `L` anchors and `I` internal nodes. Key generation samples independent uniform WOTS+C secrets and includes `PK.sl` in the supplied public key. Randomizers are uniform in Definition 4.16. Model `Hmsg_sf` as an RO and assume Conjecture 3.1.

For classical or quantum adversaries of time `xi`, at most `qs≤L` signing queries and `qh` direct `Hmsg_sf` queries:
\[
\begin{aligned}
I_{EU\text{-}CMA}(FXMSS;\xi,q_s)\le{}&
 I_{SM\text{-}rTCR,1}(H_{\rm msg}^{sf},1;\tilde\xi',q_s,\tilde q_h)\\
&+I_{DI\text{-}Repro}(H_{\rm msg}^{sf};
                  \tilde\xi',q_s,q_s+q_h+1)\\
&+C_{\rm sf}(\tilde\xi;q_s,q_i,q_{\lambda,i}).
\end{aligned}
\]

The right side is evaluated at `qs:=L`. Bounds:
\[
q_1\le Ll_{\rm sf},\quad q_2\le Ll_{\rm sf}w,\quad
q_3\le I,\quad q_4\le L,\quad q_5\le L+I.
\]
\[
\begin{array}{ll}
q_{\lambda,0}\le L(l_{\rm sf}w+1)+I+q_{kg},&
q_{\lambda,1}\le L(l_{\rm sf}w+1)+I+q_g+q_{kg},\\
q_{\lambda,2}\le L+I+q_g+q_{kg},&
q_{\lambda,3}\le L(l_{\rm sf}w+1)+q_g+q_{kg},\\
q_{\lambda,4}\le Ll_{\rm sf}w+I+q_g+q_{kg},&
q_{\lambda,5}\le Ll_{\rm sf}w+q_g+q_{kg}.
\end{array}
\]
\[
\tilde\xi\le\xi+V_{\rm sf},\quad
\tilde\xi'\le\xi+t_{\rm sim},\quad
t_{\rm sim}\le L(l_{\rm sf}w+1)+I+q_g+q_{kg},\quad
\tilde q_h\le q_h+1.
\]
`qkg≤2^19`, `qg≤2^cL`, and
\[
V_{\rm sf}=l_{\rm sf}(w-1)-S_w^n+2+h_{\rm sf}.
\]
`Prop` is the constant-digit-sum predicate
`Σ_(i=0)^(l_sf−1) a_i=S_w^n`.
Every valid structure has `I=L−1`.

## 4.3 Theorem 4.1 — M:2874–2947

Under the stated scheme parameters, Assumption 4.1 and Conjecture 3.1, with `Hmsg_sf` modeled as an RO, for a classical or quantum adversary of time `xi`, at most `qs` signing queries, and at most `qh` queries to **each** message hash:
\[
\begin{aligned}
Succ^{SHRINCS\text{-}EU\text{-}CMA}_{SHRINCS,q_s}(A)\le{}&
 I_{prf}(PRF;\xi,q_1)
 +I_{prf}(PRF_{\rm msg};\xi,q_s)\\
&+I_{SM\text{-}rTCR,1}(H_{\rm msg}^{sf},1;
                  \tilde\xi_{\rm sf}',q_s^{sf},\tilde q_h^{sf})\\
&+I_{DI\text{-}Repro}(H_{\rm msg}^{sf};
                  \tilde\xi_{\rm sf}',q_s^{sf},q_s^{sf}+q_h+1)\\
&+C_{\rm sf}(\tilde\xi_{\rm sf};
               q_s^{sf},q_i^{sf},\tilde q_{\lambda,i})\\
&+C_{\rm sl}(\tilde\xi_{\rm sl}'',\tilde\xi_{\rm sl};
               q_s^{sl},\tilde q_h^{sl},q_i^{sl},q_\lambda)
+\epsilon_{ds}.
\end{aligned}
\]

Here `qs_sl+qs_sf=qs`; `q1` counts all PRF-derived secret elements across both paths. Stateful counts come from Theorem 4.2; stateless counts from Theorem 4.3. Evaluate `qs_sf:=L`, including `qs:=qs_sl+L` in PRFmsg.

\[
\begin{array}{ll}
\tilde\xi_{\rm sf}'\le\xi+t_{\rm sim}+t_{\rm sim}^{sl},
 &\tilde q_h^{sf}\le q_h+1,\\
\tilde\xi_{\rm sf}\le\xi+V_{\rm sf},
 &\tilde q_{\lambda,i}\le q_{\lambda,i}+Q_\Lambda^{sl},\\
\tilde\xi_{\rm sl}\le\xi+V_{\rm sl},
 &q_\lambda\le Q_\Lambda^{sl}+L(l_{\rm sf}w+1)+I+q_g,\\
\tilde\xi_{\rm sl}''\le\xi+t_{\rm sim}^{sl}
                   +L(l_{\rm sf}w+1)+I+q_g,
 &\tilde q_h^{sl}\le q_h+1.
\end{array}
\]

The theorem charges each PRF replacement once and stateful reprogramming once.

## 4.4 Theorem 4.3 resources — M:3027–3073

The exact statement is
\[
I_{EU\text{-}CMA}(SLH\text{-}DSA;\xi,q_s)
\le I_{prf}(PRF;\xi,q_1)
 +I_{prf}(PRF_{\rm msg}^{sl};\xi,q_s)
 +C_{\rm sl}(\tilde\xi_{\rm sl}',\tilde\xi_{\rm sl};
             q_s,\tilde q_h^{sl},q_i,q_\lambda).
\]

\[
\begin{array}{llll}
q_1<2^{h_{\rm sl}+1}(kt+l_{\rm sl}),&
q_2<2^{h_{\rm sl}+1}l_{\rm sl},&
q_3<2^{h_{\rm sl}+1}l_{\rm sl}w,&
q_4<2^{h_{\rm sl}+1}k\,2t,\\
q_5<2^{h_{\rm sl}},&
q_6<2^{h_{\rm sl}+1},&
q_7<2^{h_{\rm sl}+1}kt,&
q_8<2^{h_{\rm sl}}kt.
\end{array}
\]
\[
q_\lambda\le Q_\Lambda^{sl}
=2^{h_{\rm sl}+1}(l_{\rm sl}w+2)
 +2^{h_{\rm sl}}(2kt+1),
\]
\[
\tilde\xi_{\rm sl}\le\xi+V_{\rm sl},\quad
\tilde\xi_{\rm sl}'\le\xi+t_{\rm sim}^{sl},\quad
t_{\rm sim}^{sl}\le2^{18.2}+q_s2^{20.7},\quad
\tilde q_h^{sl}\le q_h+1.
\]
\[
V_{\rm sl}=k(a+1)+1+d(s_{\max}+h'+1).
\]

## 4.5 Claims 4.1–4.16

Let `S_F.i=Succ_F.i(A)` and `S_i=Succ_GAME.i(A)`.

| Claim | Exact inequality |
|---|---|
| 4.1 | `S_F.0−S_F.1 ≤ I_SM-rTCR,1(Hmsg_sf,1; xi_tilde',qs,qh_tilde)` |
| 4.2 | `S_F.1−S_F.2 ≤ I_DI-Repro(Hmsg_sf; xi_tilde',qs,qs+qh+1)` |
| 4.3 | `S_F.2−S_F.3 ≤ I_S-TCR(Prop)(Hgrind∈Th_lambda; xi_tilde,qs,q_lambda,0)` |
| 4.4 | `S_F.3−S_F.4 ≤ w I_sm-ud(F∈Th_lambda; xi_tilde,q1,q_lambda,1)` |
| 4.5 | `S_F.4−S_F.5 ≤ I_sm-tcr(F∈Th_lambda; xi_tilde,q2,q_lambda,2)` |
| 4.6 | `S_F.5−S_F.6 ≤ I_sm-pre(F∈Th_lambda; xi_tilde,q1,q_lambda,1)` |
| 4.7 | `S_F.6−S_F.7 ≤ I_sm-tcr(Th_lsf∈Th_lambda; xi_tilde,q4,q_lambda,4)` |
| 4.8 | `S_F.7−S_F.8 ≤ I_sm-tcr(H∈Th_lambda; xi_tilde,q3,q_lambda,3)` |
| 4.9 | `S_F.8−S_F.9 ≤ I_sm-tcr-excl(Th_(2∪lsf)∈Th_lambda; xi_tilde,q5,q_lambda,5)` |
| 4.10 | `S_F.9=0` |
| 4.11 | `S_0−S_1 ≤ I_prf(PRF;xi,q1)` |
| 4.12 | `S_1−S_2 ≤ I_prf(PRFmsg;xi,qs)` |
| 4.13 | `S_2−S_3 ≤ I_SM-rTCR,1(Hmsg_sf,1;xi_tilde_sf',qs_sf,qh_tilde_sf)` |
| 4.14 | `S_3−S_4 ≤ I_DI-Repro(Hmsg_sf;xi_tilde_sf',qs_sf,qs_sf+qh+1)` |
| 4.15 | `S_4−S_5 ≤ C_sf(xi_tilde_sf;qs_sf,q_i_sf,q_lambda_tilde_i)` |
| 4.16 | `S_5−S_6 ≤ C_sl(xi_tilde_sl'',xi_tilde_sl;qs_sl,qh_tilde_sl,q_i_sl,q_lambda)` |

Their anchors are in the inventory. Resource conditions are exactly those in §§4.2–4.4 above, except Claim 4.3 has the stronger `xi_tilde≤xi`. Claims 4.1 and 4.2 use `xi_tilde'≤xi+t_sim`; Claims 4.13 and 4.14 use `xi_tilde_sf'≤xi+t_sim+t_sim_sl`.

Claim 4.9 pairs internal-node and WOTS+C-compression tweaks with the same node identifier. Claim 4.15 explicitly sums augmented Claims 4.3–4.10.

## 4.6 Classical reprogramming statements

Sources: M:5842–5900, 6135–6246.

### Common Repro experiment

`X1,X2,Y` finite nonempty; sample uniform `O0:X1×X2→Y`, copy `O1:=O0`. Adversary queries `O_b` and classical `Reprogram(x2)`. The latter independently samples `(x1,y)←X1×Y`, sets `O1(x1,x2):=y`, and returns `x1`.

\[
Adv^{Repro}_{R,q}(A)
=|\Pr[Repro_0(A)=1]-\Pr[Repro_1(A)=1]|.
\]

### Lemma C.2

For a classical algorithm with `R` reprogramming calls and `q` oracle queries,
\[
Adv^{Repro}_{R,q}(A)\le Rq/|X1|.
\]

### Lemma C.4

For at most `R` calls, let `x2^(j)` be call `j`’s second coordinate and let `n_j` count **distinct** seeds `x1` such that `(x1,x2^(j))` was queried earlier. Put `n_j=0` if call `j` does not occur. With expectation in either game,
\[
Adv^{Repro}_{R,q}(A)\le\frac1{|X1|}\sum_{j=1}^{R}\mathbb E[n_j].
\]

### Definition C.2

DI-Repro maintains a set `L⊆X2`. A repeated `Reprogram(x2)` returns `⊥`, does not sample or modify either oracle, and still counts toward `R`. A fresh `x2` is inserted and processed as above.
\[
Adv^{DI\text{-}Repro}_{R,q}(A)
=|\Pr[DI\text{-}Repro_0(A)=1]-\Pr[DI\text{-}Repro_1(A)=1]|.
\]
`InSec_DI-Repro(G;xi,R,q)` maximizes this over the specified resource class.

### Corollary C.2

Let `qpre` count queries whose second input is **first** submitted to Reprogram later. Then, in either game,
\[
Adv^{DI\text{-}Repro}_{R,q}(A)
\le\mathbb E[qpre]/|X1|\le q/|X1|.
\]
Therefore `InSec_DI-Repro(G;xi,R,q)≤q/|X1|` for every `R`.

Read-backs after programming and verification after the last programming do not contribute to `qpre`.

## 4.7 Requested generic bounds

### Theorem E.1, classical — M:7283–7308

Let `Th:P×T×M→N` be an RO. For a classical SM-TCR-EXCL adversary with `p` targets and `q` queries, there exist classical adversaries `B` against `Avg-Search_(1/|N|)` and `C` against ZeroDist, each using at most `q` challenge-oracle queries, such that
\[
Succ^{sm\text{-}tcr\text{-}excl}_{Th,p}(A)
\le Succ^{Avg\text{-}Search_{1/|N|}}(B)+Adv^{ZeroDist}(C)
\le(q+1)/|N|+q/|P|.
\]
Definition 4.7 imposes the sharper admissible target range `p≤|T1∪T2|`; the theorem’s introductory wording says `p≤|T|`.

### Theorem F.2, classical — M:7508–7520

Let `H:K×{0,1}^alpha→{0,1}^m` be an RO, with the stated digest map; let `A` make `p` challenge and `q` direct queries. Put `Gamma=Gamma_(h,k,t)(p)`. Then
\[
Succ^{itsr}_{H,p}(A)
\le\frac{p(q+p+1)}{|K|}+(q+1)\Gamma.
\]

For the intended parameters the map has equal-size fibres. That condition matters for the coverage probability and for the stronger F.1 transfer; see M:7480–7500.

### Corollary G.1 — M:7846–7877

For a classical adversary in Definition 4.9, `Th` an RO, at most `p` challenge queries and `q` direct queries,
\[
Succ^{SM\text{-}rTCR,K}_{Th,p,Prop}(A)
\le\frac{q+1}{|N|}
+\frac{Kq+pK(K-1)/2}{|R|}.
\]
At `K=1`,
\[
Succ\le(q+1)/|N|+q/|R|.
\]

---

# 5. Security-notion games 4.3–4.12

Common convention: challenger queries are classical. In the ideal model, adversary direct evaluations of the public random function are separate counted queries. In two-stage games, the first stage does not initially receive `P`; the second receives `P` and loses challenge access.

### Definition 4.3: PRF — M:2028–2057

Sample `k←K`, uniform function `G:M→N`, and bit `b`. Answer at most `p` classical queries `m` with `F(k,m)` for `b=0`, `G(m)` for `b=1`, and `⊥` beyond the budget. Output adversary bit.
\[
Adv^{prf}_{F,p}(A)
=|\Pr[out=1\mid b=1]-\Pr[out=1\mid b=0]|.
\]
Repeated inputs to the ideal oracle return the same value.

### Definition 4.4: SM-TCR — M:2085–2117

Sample `P`, initialize list `Q`. Stage 1 submits `(T,m)`; refuse if full or `T` previously challenged. Otherwise append `(T,m)` and return `Th(P,T,m)`. Reveal `P`; stage 2 outputs `(j,m*)`. Win iff
\[
Th(P,T_j,m_j)=Th(P,T_j,m^*)\land m^*\ne m_j.
\]

### Definition 4.5: SM-PRE — M:2126–2161

Stage 1 submits distinct `T`; sample hidden `m←M`, return `y=Th(P,T,m)`, record `(T,y)`. After revealing `P`, output `(j,m*)`; win iff `Th(P,T_j,m*)=y_j`.

### Definition 4.6: SM-UD — M:2170–2202

Sample `b,P`. For each fresh challenged tweak `T`, return `Th(P,T,m)` for fresh hidden `m←M` when `b=0`, and fresh uniform `y←N` when `b=1`. Reveal `P` for stage 2. Advantage is the **absolute** difference of output-one probabilities.

### Definition 4.7: SM-TCR-EXCL — M:2226–2261

Disjoint partition `T=T1∪T2∪T3`, bijection `omega:T2→T3`; at most `p≤|T1∪T2|` targets. Reject repeated tweaks and queries whose partner was already challenged. Record `(T,m)` and return its image.

Stage 2 outputs `(j,T*,m*)`. Require:

- `T*=T_j` if `T_j∈T1`;
- `T*∈{T_j,omega(T_j)}` if `T_j∈T2`;
- `T*∈{T_j,omega^-1(T_j)}` if `T_j∈T3`;

and
\[
Th(P,T_j,m_j)=Th(P,T^*,m^*)\land m^*\ne m_j.
\]

The printed freshness condition is **message inequality**, not merely `(T*,m*)≠(T_j,m_j)`.

### Definition 4.8: S-TCR(Prop) — M:2268–2295

For a fresh `(T,m)`, find the **least** natural `i` with `Prop(Th(P,T,m||i))=1`; record `((T,m),(y,i))`, return `(y,i)`. After revealing `P`, stage 2 outputs `(j,m*,ctr)`. Win iff
\[
Th(P,T_j,m_j||i_j)=Th(P,T_j,m^*||ctr)\land m^*\ne m_j.
\]

The abstract oracle searches without a cap. Scheme agreement needs Conjecture 3.1 or an explicit failure/termination treatment.

### Definition 4.9: SM-rTCR — M:2305–2337

`Th:P×T×(M×R)→N`; integer `K` is the attempt budget. Reveal `P` **at the start**. For a fresh `(T,m)`, sample independent `rho←R` up to `K` times until `Prop(Th(P,T,m||rho))=1`. Record successful `(T,m,rho)` and return `(y,rho)`; on exhaustion record `(T,m,⊥)` and return failure. Repeated tweaks/full list are rejected.

Output `(j,m*,rho*)`; require equal images at `T_j` and
`(m*,rho*)≠(m_j,rho_j)`. M:7680–7687 explicitly interprets failed challenge entries as losing rather than evaluating `Th` on `⊥`.

### Definition 4.10: SM-DSPR — M:2350–2384

\[
SP_{P,T}(x)=1\iff|Th_{P,T}^{-1}(Th_{P,T}(x))|\ge2.
\]
Challenges are as in SM-TCR. Stage 2 outputs `(j,b)` and wins if `SP_(P,T_j)(m_j)=b`. Define
\[
succ=\Pr[win],\qquad triv=\Pr[SP_{P,T_j}(m_j)=1],
\quad Adv^{sm\text{-}dspr}=\max(0,succ-triv).
\]

### Definition 4.11: ITSR — M:2394–2422

`G=MAP_(h,k,t)∘H`; identify a digest with `{(I,i,J_i):i∈[k]}`. Challenge `M` receives fresh uniform `K` and `(K,G(K,M))`; record `(K,M)`. Output `(K*,M*)`. Win iff pair is unchallenged and
\[
G(K^*,M^*)\subseteq\bigcup_{(K_i,M_i)\in Q}G(K_i,M_i).
\]

### Definition 4.12: collection security — M:2438–2463

Add first-stage classical access to the shared-parameter collection oracle:

- select member by input message length;
- refuse invalid member tweaks;
- no collection query at **any member** may use a challenge-reserved tweak;
- conversely, refuse a challenge if its tweak was used by a collection query;
- for SM-TCR-EXCL, reserve/check the partner tweak too.

`Th_(2∪l_sf)` is a length-selected combination of two members, not literally one member. Its notation `∈Th_lambda` denotes this special collection experiment.

---

# 6. Scheme specification needed to state and prove EU-CMA

| File range | Necessary contents |
|---|---|
| M:274–331 | Parameters, bit/byte units, chain counts, heights, digest sizes. |
| M:332–681 | Hash-function signatures, named-function separation, combined PRFmsg, 22-byte address encoding/type rules. |
| M:682–817 | WOTS-TW chain function, message/checksum encoding, keygen/signature/root recovery. |
| M:818–996 | WOTS+C fixed-sum encoding, bounded least-counter search, keygen/signature/root recovery. |
| M:997–1281 | XMSS recursion, FXMSS full-tree invariant, anchor selection, authentication paths, shape-independent verification. |
| M:1282–1397 | FORS digest-to-leaf mapping, secret/leaf derivation, authentication and root compression. |
| M:1398–1506 | Hypertree composition, SLH digest parsing, signing/verification and context wrapper. |
| M:1507–1745 | Complete key formats, state rules, Algorithms 1–3, branch dispatch and serialization. |
| M:1746–1980 | Honest correctness, grinding failure, global grind-completeness. |
| M:6804 onward | Byte-layout proof for domain separation, if claiming instantiated-layout facts. |

Essential representations:

- Public key: `PK.seed || PK.sl || PK.sf`, 48 bytes at proposed parameters.
- Secret key: `SK.seed || SK.prf || PK.seed || PK.sl || structure || PK.sf`, 82 bytes.
- `structure=(shape,depth)` is two bytes.
- Stateful anchor `(z*,i*)`; `idx=toByte(z*,1)||toByte(i*,8)`.
- Address: 9-byte position prefix, 1-byte type, 12-byte payload. Stateless prefix is `(layer,tree)`; stateful prefix is `(height,index)`.
- Stateful bound message:
  `0x00 || toByte(|ctx|,1) || ctx || PK.sl || M`.
- Stateless path signs `PK.sf||M` through SLH’s context wrapper.
- State counter is monotone, consumed **before** signing work; lost/restored state switches permanently to stateless mode.
- A failed grinding call consumes its leaf.
- Stateful signature:
  `z* || R || encoded_i* || grinding_counter || WOTS+C_signature || auth`.
- `delta*=h_sf−z*`,
  `ell_idx(delta*)=ceil(min(delta*,64)/8)`.
- Stateful length:
  `1+n/8+ell_idx(delta*)+c/8+(l_sf+delta*)n/8`.
- Stateless signature: leading `h_sf` byte plus SLH signature.
- Verifier has no committed tree shape: it accepts based on decoded anchor/path/root. This is why exclusive-tweak security is necessary.
- Valid FXMSS structure: finite full binary tree rooted at `(0,0)` in depth coordinates, internal set `I`, leaf/anchor set `A`, disjoint sets, parent closure, both children of every internal node present, addressable node indices. Hence `|I|=|A|−1`.

For abstract EU-CMA, typed records and injective encodings suffice initially. Byte-exact parsing and SHA-256 layouts are separate refinement obligations, not substitutes for the game proof.

---

# 7. Formalisation assessment and important gaps

## 7.1 Classical scope

[INFERENCE] All of the following are suitable for a classical probabilistic oracle-computation framework:

1. The games and state machines in Definitions 4.3–4.16.
2. Lazy random functions, repeated-query consistency, query logs and origin indices.
3. Exact game simulation, coupling-until-bad and telescoping inequalities.
4. Classical C.2/C.4/C.5/Corollary C.2.
5. Classical average search, ZeroDist and hidden-slice simulation.
6. Exclusive-tweak reduction E.1.
7. Classical random-sampling reduction G.1.
8. The complete ITSR-Classical proof.
9. Tree/path collision extraction and WOTS fixed-sum arguments.
10. Named-function ideal-ROM composition theorem.

No quantum Hilbert spaces, amplitudes, density matrices, or coherent-oracle semantics are needed for those targets.

The undetectability companion’s pure polynomial/probability lemmas can be formalized separately, but they are not prerequisites for the classical security chain. Its quantum conclusions cannot be asserted merely by implementing its games with classical VCVio oracles.

## 7.2 Obstacles that must remain explicit

### Collection equality is not proved

M Lemma 4.1 proves classically:
\[
I_{Prop}(Th_m;\xi,p)
\le I_{Prop}(Th_m\in Th_\lambda;\xi,p,q_\lambda)
\le I_{Prop}(Th_m;\xi,p)+2\xi/|P|.
\]

It does **not** prove Conjecture 4.1’s exact equality. A theorem using Convention I unchanged must assume the conjecture. A fully proved ideal-ROM instantiation can instead retain the additive losses or use monolithic query accounting.

### Concrete SM-DSPR bound is conjectural

The generic classical row `(2q+1)/|N|` is explicitly conjectured in Table 6. Thus the exact numerical classical conclusions of Claims 6.1 and 6.4 are not currently unconditional consequences of the supplied proofs.

The reduction theorem with an explicit `InSec_sm-dspr` term remains a valid formalisation target.

### Grind-completeness versus random-oracle distribution

Conjecture 3.1 is a global property. Lemma 3.2 gives a rare bad-oracle event, not certainty.

[INFERENCE] To remove the conjecture, define failing signing explicitly and prove the reduction on the good event with an added `epsilon_gc`, or otherwise justify the conditioning carefully. Conditioning the entire random function on global grind-completeness destroys literal independent-uniform sampling, so it must not be silently combined with unconditioned RO bounds.

### Named-function ROM is not SHA-256 ROM

Assumption 4.1 treats the collection, both message hashes, PRF and combined PRFmsg as independent named random objects. Internal SHA calls are outside that model. The paper explicitly does not charge event (iii) of Lemma 4.3.

`epsilon_ds≤2^-n+10·2^-2n` also uses stated independent-uniform-root premises. It is not established solely by the deterministic byte-layout lemma.

### Repeated PRF inputs

Claim 4.12’s ideal randomizer function is consistent on repeats. ITSR challenge keys are fresh iid samples even for repeated messages.

[INFERENCE] The stateless reduction needs an explicit memoization/deduplication simulation for repeated deterministic signing requests, rather than treating a random function as independently resampled on every call. M:3963–3971 explicitly recognizes consistency on repeated inputs.

### Units

Main paper uses `n=128` **bits**; ITSR parameter tables use `n=16` **bytes**. Main `|K|=2^n` corresponds to ITSR `|K|=2^(8n)`. Keep semantic names for bit lengths and byte lengths.

## 7.3 Suggested module decomposition

[INFERENCE] A maintainable dependency order:

1. `Parameters`, finite digest/key/tweak types, encodings.
2. `RandomOracle`, query accounting, lazy-table simulation.
3. `Games`: primitive and signature experiments.
4. `Reprogramming.Classical`: per-call, distinct-input and read-back lemmas.
5. `Search.Classical`, `HiddenSlice`, `Collection`.
6. `ITSR.Coverage`, `ITSR.LazyOracle`, `ITSR.Pull`, `ITSR.Counting`, `ITSR.Security`.
7. `ExclusiveTweaks`, `RandomSamplingTCR`.
8. `WOTS`, `FORS`, `XMSS`, `FXMSS`, `SLH`, `SHRINCS`.
9. `FXMSS.Reduction`, `SLH.Reduction`, `SHRINCS.Reduction`.
10. `Instantiation.Classical`: explicit assumption ledger and final numerical bounds.
11. Optional `Numerics` and byte-level refinement.

Prove concrete adversary reductions first; derive insecurity-supremum statements afterward. The papers use maxima, but a formal development should not assume these maxima are attained for unrestricted adversary classes.

## 7.4 Rough size

[INFERENCE] These are planning estimates, **not measurements of existing Lean code or VCVio APIs**; upstream sources were not inspected in this assignment.

| Component | Approximate new Lean lines |
|---|---:|
| Typed scheme specification, tree/address invariants, correctness | 5,000–12,000 |
| Games, RO simulations, query accounting, classical reprogramming | 3,000–7,000 |
| ITSR-Classical full proof | 4,000–9,000 |
| Generic primitive/collection/exclusive-tweak/random-sampling reductions | 3,000–7,000 |
| FXMSS and full SHRINCS game sequences | 5,000–12,000 |
| Fully reconstructing imported SLH/HK22 proof if not reusable | 6,000–15,000 |
| Certified numerical bounds and serialization refinement | 2,000–6,000 |

A substantial existing SPHINCS/XMSS foundation could reduce this considerably. A complete proved classical development is plausibly **20,000–45,000 new lines with strong reuse**, versus **30,000–65,000** if most infrastructure and the HK22 reduction need rebuilding.

The best initial self-contained result is **ITSR Theorem 2**, followed by **classical distinct-input reprogramming**. The most important end-to-end deliverable is a classical Theorem 4.1 with an explicit assumption ledger—not numerical security claims that hide collection equality, SM-DSPR, grind-completeness, or named-function idealization.