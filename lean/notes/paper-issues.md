# Paper issues: evidence for `DEVIATIONS.md`

Every quotation below was checked against the **rendered PDF page**, not only the text extraction
(`pdftoppm -r 110`). Page numbers are printed page numbers, which equal PDF page indices for all
three documents. `M` = `SHRINCS-Security-Analysis.pdf`, `U` = `Undetectability.pdf`,
`I` = `ITSR-Classical.pdf`.

Lean evidence lives in `lean/ShrincsSecurity/Evidence/`:

* `SmUdHop.lean` (`ShrincsSecurity.Evidence.SmUdHop`), built with
  `lake build ShrincsSecurity.Evidence.SmUdHop`;
* `MainPaper.lean` (`ShrincsSecurity.Evidence.MainPaper`), built with
  `lake build ShrincsSecurity.Evidence.MainPaper`.

Both build with no `sorry`, `axiom` or `native_decide`.

## Summary

| Item | Verdict | Evidence | Lean |
|---|---|---|---|
| A. U Lemma 11 vs Def. 4 | **NOT AN ISSUE** (extraction artifact). Lemma 11 is printed with bars. | U p. 8 Def. 4 and U p. 13 Lemma 11 both print `\|·\|`. On a finite instance the printed statement holds, Corollary 12's step holds, and the signed reading fails. | `SmUdHop.Fixed.*`, `SmUdHop.Rom.*`, `SmUdHop.corollary12_of_lemma11` |
| B. M Def. 4.8 least counter | **CONFIRMED** (definitional gap, not a numerical error) | M p. 37: "Find the smallest i ∈ ℕ with Prop(Th(P,T,m‖i)) = 1" can have no solution. M p. 54 Remark 4.8 resolves this only under Conjecture 3.1. | `MainPaper.stcr_no_valid_counter` |
| C. M Def. 4.9 failed entries | **CONFIRMED** (definitional gap). It is patched in App. G and has no effect on SHRINCS (K = 1, Prop ≡ 1). | M p. 37 step 5 evaluates `Th(P,T_j,(m_j‖ρ_j))` at `ρ_j = ⊥`. M p. 121 fixes the reading. | — |
| D. M Lemma 4.1(i) constant | **IMPRECISION ONLY** (stated bound is correct but weaker) | M p. 107: the proof gives `ξ₁/\|P\|` for success notions and `2ξ₁/\|P\|` for advantage notions, both `≤ 2ξ/\|P\|`. | — |
| E. `q` in Def. 4.11 vs App. F / Table 6 | **IMPRECISION ONLY** (symbol overloading, explicitly renamed in App. F) | M p. 39 `ITSR_{H,q}` uses `q` as the challenge cap. M p. 117 and p. 77 use `p` for challenges and `q` for hash queries. | — |
| F. M Defs. 4.15/4.16: ⊥ queries in `{M_i}` | **IMPRECISION ONLY** (literal reading is clear and conservative) | M p. 46, p. 51: the freshness condition `M* ∉ {M_i}_{i=1}^{q_s}` ranges over all queries, including those answered ⊥. Every without-loss-of-generality step goes in the safe direction. | — |
| G. Def. 4.7 `p ∈ [\|T1∪T2\|]` vs Thm. E.1 `p ≤ \|T\|` | **IMPRECISION ONLY** | M p. 36/115 vs p. 115. The game admits at most `\|T1\|+\|T2\| = \|T1∪T2\|` challenges anyway, and the bound does not depend on `p`. | — |
| H. "121.4 and 122.7 bits" vs 122.75 | **IMPRECISION ONLY** (consistent with the paper's round-down convention) | M p. 4 and p. 75 vs M p. 76 Table 5. Rounding down to one decimal gives `⌊121.47⌋₁ = 121.4` and `⌊122.75⌋₁ = 122.7`. | `Concrete.table5_sf`, `Concrete.table5_full` (existing) |
| I. `idx` injectivity range | **IMPRECISION ONLY** (ranges are stated; injectivity is used without citing them) | M p. 18: `z ∈ {0,…,h_sf}`, `h_sf = 255`, "only positions with i < 2^64 are addressable". M p. 19: valid structures have addressable anchors. | `MainPaper.idx_injOn`, `idx_collide_height`, `idx_collide_index` |
| J. I Lemma 11(c) `A_m > 0` | **NOT AN ISSUE** | I p. 4: "Throughout the paper k and t are positive integers". I p. 21 uses `t^{-k} > 0`. | — |
| K. Notes claim the U advantage is signed | **NOTES ARE WRONG** | U p. 8, 12, 13, 18 all print absolute values. Corrections are listed below. | — |
| Claim 4.10 digits | **HOLDS** | M p. 61; Table 1 p. 6 gives `n = 128 = 32·4 = l_sf·log₂ w`. | `MainPaper.claim410_digits_determine`, `n_eq_lsf_mul_log_w` |
| L. M §6.4 quantum item 1: verification adds `< 2^-102.3` at ξ = 0 on the stateful path | **IMPRECISION ONLY** (true for the collection summands; the stateful bound at ξ = 0 uses e = 1/2 at the hop, which doubles them) | M p. 79, item 1. | `Concrete.Quantum.section_6_4_quantum_verification`, `section_6_4_quantum_verification_doubled` |

---

## A. Undetectability, Lemma 11 (sm-ud hop) vs Definition 4

**Printed text.**

* U p. 8, **Definition 4**:
  "The advantage is
  `Adv^{SM-UD}_{Th,p}(A) := |Pr[SM-UD_{Th,p}(A) ⇒ 1 | b = 1] − Pr[SM-UD_{Th,p}(A) ⇒ 1 | b = 0]|`."
  The rendered page shows the outer bars `|…|`. The text extraction (`Undetectability.txt:413–415`)
  drops them.
* U p. 13, **Lemma 11 (The sm-ud hop)**: "… The adversary C defined above from A makes at most
  q + 1 queries to Th, the last of them classical and in its second stage, and at most p challenge
  queries, and
  `|Succ^{SM-PRE}_{Th,p}(A) − Succ^{SM-OW}_{Th,p}(A)| = Adv^{SM-UD}_{Th,p}(C)`."
  The rendered page shows the bars here too. The extraction (`Undetectability.txt:711`) drops them.
* The proof (p. 13) gives `Pr[SM-UD(C) ⇒ 1 | b = 0] = Succ^{sm-pre}` and
  `Pr[SM-UD(C) ⇒ 1 | b = 1] = Succ^{sm-ow}`. "The claim is the definition of Adv^{sm-ud}."
* U p. 13, **Corollary 12**, proof: "By Lemma 11,
  `Succ^{SM-PRE}(A) ≤ Succ^{SM-OW}(A) + Adv^{SM-UD}(C)`."

**Verdict: NOT AN ISSUE.** The suspected error is an extraction artifact. The printed Lemma 11 is an
equality of absolute values. It follows from the proof's two identities and the printed Definition 4.
Corollary 12's inequality follows from it, because `x ≤ |x|`.

**Evidence (Lean, `ShrincsSecurity.Evidence.SmUdHop`).** The games are evaluated exactly, with the
reduction `C` of U §5.1 and its final classical query `Th(P, T_j, x*)`. There is one tweak, one
public parameter and `p = 1`, so every run makes exactly one admitted challenge and the only valid
index is `j = 1`.

* `Fixed`: a fixed `Th` with `M = Fin 4`, `N = Fin 2`, `Th(0) = 0` and `Th(1) = Th(2) = Th(3) = 1`.
  The adversary outputs `x* = 0`.
  * `succPre_eq : succPre = 1/4`: `y = Th(x)` with `x ←$ M`, and the adversary wins iff `y = 0`.
  * `succOw_eq : succOw = 1/2`: `y ←$ N`.
  * `prC_eq`: the proof's identities hold by `rfl`.
  * `advUd_eq : advUd = 1/4`.
  * `lemma11_printed : |succPre − succOw| = advUd`.
  * `lemma11_signed_false : succPre − succOw ≠ advUd`: the left side is `−1/4`, the right side `1/4`.
  * `signed_adv_eq`: without bars, `Pr[b=1] − Pr[b=0] = Succ^{ow} − Succ^{pre}`, which is the
    negative of the extracted left side.
  * `corollary12_step`.
* `Rom`: the same with `Th` **uniform over all 16 functions** `Fin 4 → Fin 2`, which is the
  random-oracle setting of the lemma. The adversary queries `Th` on all of `M`. If `y` has a unique
  preimage it outputs that preimage; otherwise it outputs the first `x` with `Th(x) ≠ y`.
  * `countPre_eq`, `countOw_eq` give `Succ^{pre} = 16/64 = 1/4` and `Succ^{ow} = 10/32 = 5/16`.
  * `ow_gt_pre`, `advUd_eq : advUd = 1/16`, `lemma11_printed`, `lemma11_signed_false`,
    `corollary12_step`.
* `corollary12_of_lemma11 : |pre − ow| = adv → pre ≤ ow + adv`, for all rationals.

The candidate counterexample in the brief (`Succ_pre = 1/4`, `Succ_ow = 1/2`) is reproduced as
`Fixed`. It refutes only the signed reading, which the paper does not print.

**Suggested fix.** None needed in the paper. The formalisation must use the absolute advantage, as
printed. A cosmetic option is to state Lemma 11 as `Adv(C) = |Succ^{pre} − Succ^{ow}|` and
Corollary 12 as `Succ^{pre} ≤ Succ^{ow} + Adv(C)`.

---

## B. Main paper, Definition 4.8 (S-TCR(Prop)): the least counter may not exist

**Printed text.** M p. 36–37, Definition 4.8, oracle `O^Prop(·,·)`:

> • If |Q| ≥ p or there is an m′ ∈ M with (T, m′) ∈ Q, return ⊥.
> • Find the smallest i ∈ ℕ with Prop(Th(P, T, m‖i)) = 1 and set y = Th(P, T, m‖i).
> • Insert {(T, m), (y, i)} into the list Q. • Return (y, i).

The definition quantifies over an arbitrary THF `Th` and an arbitrary predicate `Prop`. M p. 54,
**Remark 4.8**: "The scheme caps the counter search at 2^c = 2^16 attempts and returns ⊥ on
exhaustion, while the S-TCR(Prop) oracle of Definition 4.8 searches unboundedly for the smallest
valid counter. On non-⊥ signatures the two coincide …, and under Conjecture 3.1 no signature is ⊥."

The instantiation is `H_grind : {0,1}^n × T_g × {0,1}^{2n} × {0,1}^c → {0,1}^n` (M p. 7). Its
counter domain is `{0,1}^c`, so `Th(P,T,m‖i)` is not even defined for `i ≥ 2^c`.

**Verdict: CONFIRMED (definitional gap).** The step "find the smallest `i`" has no value whenever no
counter satisfies `Prop`. This happens for `Prop ≡ 0`, for any `Th` whose values avoid `Prop`, and
for `H_grind` exactly when Conjecture 3.1 fails. In the random-oracle model of Lemma 3.2 that
happens with positive probability, at most `ε_gc`. The experiment is therefore not well defined as
stated. Claim 4.3's quantity `InSec^{S-TCR(Prop)}(H_grind ∈ Th_λ; …)` is meaningful only under
Conjecture 3.1, which Theorem 4.2 assumes. This is not a numerical error in any bound.

**Evidence (Lean).** `ShrincsSecurity.Evidence.MainPaper.stcr_no_valid_counter`: for the toy
grinding function `thToy i = if i even then 0b00 else 0b11` and the target-sum predicate with
`l = 2` base-2 digits and `S = 1`, `¬ ∃ i : ℕ, propSum (thToy i) = true`.

**Suggested fix.** Bound the search as the scheme does: "Find the smallest
`i ∈ {0, …, 2^c − 1}` with …; if there is none, insert `(T, m, ⊥)` and return ⊥". A ⊥ entry cannot
be won, in the same way App. G treats failed SM-rTCR entries. Alternatively, restrict Definition 4.8
to pairs `(Th, Prop)` for which a valid counter always exists, and cite Conjecture 3.1 in the
definition. With the bounded oracle, Remark 4.8's coincidence holds unconditionally.

---

## C. Main paper, Definition 4.9 (SM-rTCR): failed entries `(T, m, ⊥)`

**Printed text.** M p. 37, Definition 4.9, oracle: "(d) Else: Set y := ⊥, ρ := ⊥. … • If y = ⊥:
Insert (T, m, ⊥) into Q. • Return (y, ρ)." Step 5: "Output 1 if
`Th(P, T_j, (m_j‖ρ_j)) = Th(P, T_j, (m*‖ρ*))` and `(m*, ρ*) ≠ (m_j, ρ_j)`."

At an entry with `ρ_j = ⊥`, `Th(P, T_j, (m_j‖⊥))` is undefined, because `Th` is defined on
`M × R` and `⊥ ∉ R`.

M p. 121, App. G preamble: "An entry `(T_j, m_j, ⊥)` of the list Q records a challenge query whose
K attempts all failed; the winning condition of Definition 4.9 evaluates Th at `(m_j‖ρ_j)` and is
read as false for such an entry; likewise the output ρ* is read as an element of R."

**Verdict: CONFIRMED (definitional gap).** The winning condition is undefined on failed entries in
Definition 4.9 itself and is fixed only in App. G. **No effect on SHRINCS:** Theorem 4.2 uses
`K = 1, Prop ≡ 1` (Algorithm 4, M p. 52), so no entry ever fails.

**Suggested fix.** Add to step 5 of Definition 4.9: "If `ρ_j = ⊥`, output 0", and state
`ρ* ∈ R`.

---

## D. Main paper, Lemma 4.1(i): additive term `2ξ/|P|`

**Printed text.** M p. 41 and restated on p. 105, Lemma 4.1:

> (i) for classical adversaries, `InSec^Prop(Th_m ∈ Th_λ; ξ, p, q_λ) ≤ InSec^Prop(Th_m; ξ, p) + 2ξ/|P|`;
>
> (ii) for adversaries that evaluate the collection themselves with quantum access, …, where
> `ξ₁ ≤ ξ` is the number of own evaluations performed in the first stage,
> `… + 2ξ₁/√|P|`, where the additive term is `4ξ₁/√|P|` for the advantage notions SM-UD and SM-DSPR.

Proof (M p. 106–107): "let `ξ₁ ≤ ξ` be the number of its own evaluations in the first stage. Write
`ε(ξ₁)` for the largest advantage `Adv^{ZeroDist}(B)` …" and later "… with `c = 1` for the
success-probability notions and `c = 2` for the advantage notions. … For classical adversaries,
Lemma C.7 gives `ε(ξ₁) ≤ ξ₁/|P|`, hence the terms `ξ₁/|P|` and `2ξ₁/|P|`, both at most `2ξ/|P|` as
in part (i)." Lemma C.7 (M p. 101): `Adv^{ZeroDist}(A) ≤ q/|P|`.

**Verdict: IMPRECISION ONLY.** The stated bound is correct and weaker than what the proof gives:

* `ξ₁/|P|` for SM-TCR, SM-PRE, S-TCR(Prop) and sm-tcr-excl;
* `2ξ₁/|P|` for SM-UD and SM-DSPR.

Part (i) uses `ξ`, and part (i) does not define `ξ₁`. The slack is at most a factor of 2 times
`ξ/ξ₁`. The Lemma 4.1 citations found in the page-by-page text (pp. 4, 41–42, 69–70, 74,
104–107) contain no numeric use. The figures of Section 6 assume Conjecture 4.1 (Convention I) or
charge the collection work (§6.8); see M p. 75.

**Suggested fix.** Either restate (i) as "`+ ξ₁/|P|`, and `+ 2ξ₁/|P|` for the advantage notions
SM-UD and SM-DSPR", moving the definition of `ξ₁` before (i), or keep `2ξ/|P|` and note that it is
the uniform weakening.

---

## E. Main paper: `q` in Definition 4.11 vs App. F / Table 6

**Printed text.** M p. 39, Definition 4.11: "Consider the following experiment `ITSR_{H,q}(A)`: …
If |Q| ≥ q, return ⊥." … "`Succ^{ITSR}_{H,q}(A) := Pr[ITSR_{H,q}(A) ⇒ 1]`." Here `q` is the
**challenge** budget. M p. 117, App. F: "We use the experiment of Definition 4.11 and, as in
Table 6, write p for its challenge count and q for the number of queries of A to H". M p. 77,
Table 6: rows `Succ^{ITSR}_{H,p}(A)`, with the caption "q counts hash queries and p challenge
queries".

**Verdict: IMPRECISION ONLY.** The symbol is overloaded, and App. F renames it explicitly.
Theorem 4.3's term `InSec^{itsr}(H^{sl}; ξ̃′, q_s, q̃^{sl})` (M p. 49) uses `q_s` as the challenge
count, consistent with App. F.

**Suggested fix.** Write `ITSR_{H,p}` and "If |Q| ≥ p" in Definition 4.11.

---

## F. Main paper, Definitions 4.15/4.16: do ⊥-answered signing queries count towards `{M_i}`?

**Printed text.** M p. 45, Definition 4.15, step 3: "If `b_i = 0` (stateful path): return
`Sign_sf(sk, M_i)` using the next unused stateful key; return ⊥ if all stateful keys are
exhausted." M p. 46: success requires `Verify(pk, σ*, M*) = 1 ∧ M* ∉ {M_i}_{i=1}^{q_s}`.

M p. 50, Definition 4.16, item 2: "the queried leaf identifiers are pairwise distinct, a query
outside the structure is answered by ⊥ (so without loss of generality every query names a leaf of
the structure)". M p. 51: success requires `… ∧ M* ∉ {M_i}_{i=1}^{q_s}`.

M p. 51, Remark 4.6: "the wrapper counts the stateful queries of A that are answered by a signature,
answers by ⊥ once all L anchors are used, …".

**Verdict: IMPRECISION ONLY.** The printed set `{M_i}_{i=1}^{q_s}` indexes **all** `q_s` queries,
so a ⊥-answered message counts as queried. This literal reading is the conservative one: the
adversary loses if it forges a message whose query was refused. Both without-loss-of-generality
steps (dropping ⊥-answered or out-of-structure queries in Definition 4.16 and Remark 4.6) shrink
the query set. A forgery that is fresh for the original adversary is therefore also fresh for the
wrapped one, so `Succ(A) ≤ Succ(A′)` holds in the direction the proof needs. No step depends on the
other reading. The paper never says so explicitly.

**Suggested fix.** Add "(including queries answered by ⊥)" after `{M_i}_{i=1}^{q_s}` in both
definitions.

---

## G. Definition 4.7 `p ∈ [|T1 ∪ T2|]` vs Theorem E.1 "p ≤ |T|"

**Printed text.** M p. 36 and restated on p. 114–115, Definition 4.7: "Let
`T = T1 ∪ T2 ∪ T3`, … `|T2| = |T3|` … `ω : T2 → T3` a bijection … Let `p ∈ [|T1 ∪ T2|]`." M p. 115,
Theorem E.1: "Let A be an adversary against sm-tcr-excl for `p ≤ |T|` targets that makes q queries
to Th." The bounds (M p. 116) are `8(q+1)²/|N| + 2q/√|P|` and `(q+1)/|N| + q/|P|`, both
independent of `p`.

**Verdict: IMPRECISION ONLY.** For `|T1 ∪ T2| < p ≤ |T|` the experiment is outside the range of
Definition 4.7. The game procedure still makes sense, and it is identical to the case
`p = |T1 ∪ T2|`. The guards admit at most one tweak of each pair `{T, ω(T)}` and each `T ∈ T1` at
most once, so `|Q| ≤ |T1| + |T2| = |T1 ∪ T2|` always holds. The bound does not depend on `p`, so the
theorem is true for every `p` under the obvious extension.

**Suggested fix.** In Theorem E.1 write "for `p ∈ [|T1 ∪ T2|]`", or note that Definition 4.7 extends
verbatim to `p ≤ |T|` with the same value.

---

## H. "121.4 and 122.7 bits" vs Table 5's 122.75

**Printed text.** M p. 4 (contributions): "Classically, the bounds certify between 121.4 and
122.7 bits in the query-counting sense of Section 5.1". M p. 75, §6.1: "Classically, every bound
certifies between 121.4 and 122.7 bits." M p. 76, Table 5, classical column: Theorem 4.3
`122.23 (−111.4)`, Theorem 4.2 `122.75 (−114.2)` for both shapes, Theorem 4.1 `121.47 (−111.2)`
for both shapes. The caption reads: "Each log₂ ξ* is rounded down … classical log₂ ξ* is given to
two decimals".

**Verdict: IMPRECISION ONLY.** The one-decimal range is consistent with the paper's round-down
convention: `⌊121.47⌋₁ = 121.4` and `⌊122.75⌋₁ = 122.7`. Certifying `Y` bits means
`ξ* ≥ 2^Y`, so understating the top end is sound. It is still imprecise next to Table 5's two-decimal
value. Lean certifies `log₂ ξ* ∈ [122.75, 122.76]` (`ShrincsSecurity.Concrete.table5_sf`) and
`[121.47, 121.48]` (`table5_full`). No new Lean is needed.

**Suggested fix.** Write "between 121.47 and 122.75 bits", or "between 121.4 and 122.7 bits
(rounded down)".

---

## I. Injectivity of the leaf identifier `idx`

**Printed text.**

* M p. 6: "`toByte(x, y)` for the y-byte big-endian encoding of the integer x". There is no
  modular reduction, so `toByte(x,y)` is meaningful only for `x < 256^y`. FIPS 205's `toByte`
  (Algorithm 3) is total and keeps the low `y` bytes.
* M p. 8: `idx = toByte(z*, 1) ‖ toByte(i*, 8) ∈ {0,1}^72`.
* M p. 6, Table 1: `h_sf = 255`.
* M p. 18: "nodes are identified by their height `z ∈ {0, …, h_sf}` … Since the node-index field of
  the stateful address is 8 bytes, only positions with `i < 2^64` are addressable". Footnote 5:
  "only the leftmost 2^64 nodes of each level can host keys or tree nodes … keeping a fixed-length
  index encoding."
* M p. 19: "A structure is valid if its anchors are addressable and …".
* M p. 45, Definition 4.15: `A₁` outputs Π "that describes a valid structure (Section 2.5)".
* M p. 26: the signature transmits "the anchor height z* as a leading indicator byte … the anchor
  index i* in `ℓ_idx(δ*) = ⌈min(δ*, 64)/8⌉` bytes … Since `i* < 2^{min(64,δ*)}` (Section 2.5), these
  `ℓ_idx(δ*)` bytes encode i* without loss". A forgery's `(z*, i*)` is therefore always in range.
* M p. 52 (B0): "All queries remain pairwise distinct through idx." M p. 53 (B1): "The guard of
  Definition C.2 never fires: the signing queries name pairwise distinct leaf identifiers, …, so the
  inputs `(PK.seed, PK.sf, idx_i, M̃_i)` of the calls are pairwise distinct".

**Verdict: IMPRECISION ONLY.** The ranges `z* ≤ 255 < 256` and `i* < 2^64` are stated in §2.5,
and Definition 4.15 restricts the adversary to valid structures, whose anchors are addressable.
`idx` is therefore injective on every leaf the proof considers. B0 and B1 use this injectivity
without citing the ranges. Outside the ranges, a truncating `toByte` collides.

**Evidence (Lean, `ShrincsSecurity.Evidence.MainPaper`).** `toByte` is the FIPS 205 total encoding,
`List.ofFn fun j : Fin y => x / 256^(y−1−j) % 256`.

* `idx_injOn : z, z' < 256 → i, i' < 2^64 → idx z i = idx z' i' → z = z' ∧ i = i'`.
* `idx_collide_height : idx 256 0 = idx 0 0`.
* `idx_collide_index : idx 0 (2^64) = idx 0 0`.

The existing model (`ShrincsSecurity.Fxmss.Rom.toIdx`, `toIdx_inj`) also encodes `idx` as
`Fin 256 × Fin 2^64` and proves injectivity under the same range hypotheses.

**Suggested fix.** At B0 and B1 add: "`idx` is injective on positions with `z* ≤ h_sf = 255` and
`i* < 2^64`, which holds for every anchor of a valid structure (Section 2.5)".

---

## J. ITSR-Classical, Lemma 11(c): `A_m > 0`

**Printed text.** I p. 20, (19): `A_m := Σ_{ω=m}^{k} C(k,ω) m! St(ω,m) t^{−ω} Γ_{k−ω}(r)`.
Lemma 11(c): "Let k ≥ 2, and put `λ_m := A_{m+1}/((m+1)A_m)` (1 ≤ m ≤ k − 1)". Proof, I p. 21: "For
1 ≤ m ≤ k the summand ω = k is `m! St(k,m) t^{−k} Γ_0(r) = m! St(k,m) t^{−k} > 0`, because Γ_0 = 1
and St(k,m) ≥ 1. Hence A_m > 0". I p. 4, §2.1: "Throughout the paper k and t are positive integers
and h is a nonnegative integer".

**Verdict: NOT AN ISSUE.** The positivity `t^{−k} > 0` requires `t ≥ 1`, which the global convention
on p. 4 states. In FORS, `t = 2^a` with `a = 13`.

---

## K. Corrections needed in the existing notes (signed-advantage claim)

**Finding.** U prints the sm-ud advantage **with absolute value** everywhere:

* Definition 4 (p. 8): `|Pr[⇒1 | b=1] − Pr[⇒1 | b=0]|`;
* Theorem 9's proof (p. 12): `Adv = |Pr_{f←S1}[B=1] − Pr_{f←S0}[B=1]|`;
* Lemma 11 (p. 13): `|Succ^{pre} − Succ^{ow}| = Adv(C)`;
* Theorem 16's proof (p. 18): `Adv = |p1 − p0|`.

There is no sign inconsistency. The notes' claim comes from the text extraction, which drops the bars
at `Undetectability.txt:413–415` and `:711`.

**Corrections (for the parent; not applied here).**

`lean/notes/paper-structure.md`:

1. Line 11 (Summary): delete "It contains a sign inconsistency in its signed advantage definition
   and subsequent reductions; do not transcribe it uncritically." Replace it with: "Its advantages
   are absolute values (U Def. 4, p. 8), as in the main paper."
2. §1.3 table, Definition 4 row (line 171): replace "printed advantage is signed, unlike main-paper
   absolute advantage" with "advantage is the absolute difference, as in main Def. 4.6".
3. §1.3 table, Lemma 11 row (line 178): replace "printed sign is inconsistent" with
   "`|Succ_pre − Succ_ow| = Adv_ud(C)` (p. 13)".
4. §2.3 table, row "U Lemmas 2,7,8,11,13–15; …" (line 298): delete ", subject to the
   signed-advantage inconsistency noted below".
5. §7.2 "Undetectability signed-advantage inconsistency" (lines 1086–1100): delete the subsection, or
   replace it with the finding above. Its three bullets are each refuted by the rendered pages:
   * Theorem 9 proof: the bars make the order irrelevant;
   * Lemma 11: printed with bars;
   * Theorem 16: consistent.
   The "[INFERENCE] … repairs …" paragraph is moot.

`lean/notes/quantum-feasibility.md` (§4):

6. Lemma 11 row (line 87): replace "**New S–M; statement caveat**" with "**New S–M**" and delete "The
   printed equality needs correction/clarification; see below."
7. Corollary 12 row (line 88): replace "the corrected Lemma 11" with "Lemma 11".
8. Delete the "**Paper consistency issue:**" paragraph (line 94). Optionally replace it with: "U
   Def. 4 and Lemma 11 print absolute values (pp. 8, 13); the extraction drops the bars. Lemma 11 is
   correct as printed, and the signed reading is false (`Evidence.SmUdHop.*.lemma11_signed_false`)."

---

## Claim 4.10: "d is determined by its l_sf base-w digits"

**Printed text.** M p. 61, proof of Claim 4.10: "Otherwise `d* ≠ d_j`, so the digit vectors differ,
since d is determined by its `l_sf` base-w digits; the verifier accepts only digests whose digits
sum to `S_wn`, so some chain i has `a*_i < a_{j,i}`."

M p. 7: `H_grind : {0,1}^n × T_g × {0,1}^{2n} × {0,1}^c → {0,1}^n`, so `d ∈ {0,1}^n`. M p. 15:
"the base-w representation `(a_0, …, a_{l_sf−1})` of d". M p. 6, Table 1: `n = 128`, `w = 16`
("each chain digit encodes log₂ w = 4 bits"), `l_sf = 32`.

**Verdict: HOLDS.** Since `n = l_sf · log₂ w`, that is `128 = 32 · 4`, every `d ∈ {0,1}^n` is
`< 2^128 = 16^32`. Its 32 base-16 digits determine it, because the base-`w` representation with
`l_sf` digits is a bijection `{0,1}^n ≅ [0, w−1]^{l_sf}`.

**Evidence (Lean, `ShrincsSecurity.Evidence.MainPaper`).**

* `n_eq_lsf_mul_log_w : 128 = 32 * Nat.log 2 16 ∧ 2^128 = 16^32`.
* `claim410_digits_determine : d, d' < 2^128 → (∀ i < 32, d / 16^i % 16 = d' / 16^i % 16) → d = d'`.
  This is an instance of the general `eq_of_digits_eq`.

**Suggested fix.** None. Optionally add "(`d ∈ {0,1}^n` and `n = l_sf log₂ w`)" after the sentence.

---

## L. Main paper, Section 6.4, quantum item 1: the verification charge at ξ = 0

**Printed text.** M p. 79, "Quantum adversaries", item 1: the quadratic summands "[...] Charged at
`q := ξ + V` instead of `q := ξ`, they add less than `2^-96.6` on the stateless path and `2^-102.3`
on the stateful path to the value of the bound at `ξ = 0`." (Same page: "stoped" for "stopped".)

**Verdict: IMPRECISION ONLY.** The figures are correct for the collection summands themselves. But
at `ξ = 0` the stateful bound's "minimum" column uses the e = 1/2 form at the reprogramming hop,
which doubles the collection terms (Corollary 4.2). There the verification adds
`2 · (52513168 − 148)/2^128 ≥ 2^-101.36`, which exceeds the printed `2^-102.3`. No printed table
entry depends on this sentence.

**Evidence (Lean, `ShrincsSecurity.Concrete.Quantum`).**

* `section_6_4_quantum_verification`: the undoubled increments are `< 2^-96.6` (stateless) and
  `< 2^-102.3` (stateful).
* `section_6_4_quantum_verification_doubled`: with e = 1/2 at the hop, the stateful increment of the
  bound at `ξ = 0` is `> 2^-102.3` (it is `≥ 2^-101.36`).

**Suggested fix.** Say "to the value of these summands at `ξ = 0`", or give `2^-101.3` for the
stateful bound under e = 1/2.
