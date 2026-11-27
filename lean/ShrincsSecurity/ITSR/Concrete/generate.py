"""Generate the per-set certificate modules of ShrincsSecurity.ITSR.Concrete.

Usage (from this directory): `python3 generate.py .` (or `python3 generate.py . ShrincsSl` for one
set). Mirrors the rational computations of Certify.lean exactly (Fractions), so that every
emitted `decide +kernel` goal is known to hold before Lean checks it; figures of the paper that do
not hold are replaced by the certified rounding and reported on stdout."""
from fractions import Fraction as F
import math, sys, os

P = 256
# name: (module, title, h, k, a, log2K, log2r, G, mid q exps (Table 3), grid (Tables 4/5), paper data)
def rupQ(x, P=P): return F(-((-x.numerator * 2**P) // x.denominator), 2**P)
def sqUpQ(P, e, x):
    for _ in range(e): x = rupQ(x * x, P)
    return x
def descf(n, g):
    p = 1
    for i in range(g): p *= n - i
    return p
def chooseQ(n, k): return F(descf(n, k), math.factorial(k))
def gammaHiQ(h, a, e, G, k):
    th = F(1, 2**h)
    A = sqUpQ(P, e, 1 - th)
    tail = (2**e * th)**(G + 1) / math.factorial(G + 1) * (1 / (1 - 2**e * th / (G + 2)))
    out = [F(0)] * (k + 1)
    for g in range(G + 1):
        w = A * chooseQ(2**e, g) * (th / (1 - th))**g
        u = 1 - (1 - F(1, 2**a))**g
        up = F(1)
        for j in range(k + 1):
            out[j] += w * up
            up *= u
    return [o + tail for o in out]
def ceil_dyadic(x, bits=64):
    # smallest m / 2^E >= x with m < 2^bits
    n, d = x.numerator, x.denominator
    E = bits - (n.bit_length() - d.bit_length()) - 1
    if E >= 0: m = -((-n * 2**E) // d)
    else: m = -((-n) // (d * 2**(-E)))
    return m, E
STIR = {}
def stir(n, m):
    if (n, m) not in STIR:
        if n == 0 and m == 0: v = 1
        elif n == 0 or m == 0: v = 0
        else: v = m * stir(n - 1, m) + stir(n - 1, m - 1)
        STIR[(n, m)] = v
    return STIR[(n, m)]
class Set:
    def __init__(s, h, k, a, lK, lr, G):
        s.h, s.k, s.a, s.lK, s.lr, s.G = h, k, a, lK, lr, G
        s.th = F(1, 2**h); s.t = 2**a; s.r = 2**lr; s.K = 2**lK
        gh = gammaHiQ(h, a, lr, G, k)
        s.gl = [ceil_dyadic(x) for x in gh]
        s.gv = [F(m, 2**E) if E >= 0 else F(m * 2**(-E)) for m, E in s.gl]
        assert all(g >= x for g, x in zip(s.gv, gh))
        s.harm = {}
    def pullHarm(s, m):
        if m not in s.harm:
            k = s.k
            s.harm[m] = sum(chooseQ(k, w) * math.factorial(m) * stir(w, m) * F(1, s.t)**w * s.gv[k - w]
                            for w in range(m, k + 1))
        return s.harm[m]
    def pullTerm(s, q, m):
        return (q + 1) * chooseQ(q, m) * descf(s.r, m) * F(1, s.K)**m * s.th**m * s.pullHarm(m)
    def search(s, q): return (q + 1) * s.gv[s.k]
    def pullSum(s, q): return sum((s.pullTerm(q, m) for m in range(1, min(s.k, q, s.r) + 1)), F(0))
    def rem2(s, q): return sum((s.pullTerm(q, m) for m in range(2, min(s.k, q, s.r) + 1)), F(0))
    def main(s, q): return s.search(q) + s.pullSum(q)
def log2(x):
    n, d = x.numerator, x.denominator
    sh = n.bit_length() - d.bit_length()
    return sh + math.log2(F(n, d) / F(2)**sh)
def holds(x, B, N=100):
    """x^N <= 2^B exactly."""
    if x <= 0: return True
    n, d = x.numerator**N, x.denominator**N
    return n <= d * 2**B if B >= 0 else n * 2**(-B) <= d

# ---------------------------------------------------------------- paper data (exact columns)
SETS = [
 # mod, title, (h, k, a, lK, lr, G), table3 rows [(lq, search, K, T1, T2)], qstar (log, search, T1, T2),
 # grid [(lq, search, T1, R2, total)], x_ex (Table 7), q1 (Table 7)
 ('SLH128s', 'SLH-DSA-128s', (63, 14, 12, 128, 64, 60),
  [(0, -132.75, -257.88, -257.88, None), (64, -69.75, -130.88, -130.88, -193.16)],
  (127.56, -6.19, -3.76, -2.48),
  [(112, -21.75, -34.88, -49.16, -21.75), (120, -13.75, -18.88, -25.15, -13.71),
   (124, -9.75, -10.88, -12.99, -9.10), (128, -5.75, -2.88, 2.12, 2.17)], 133.75, 127.56),
 ('SLH128f', 'SLH-DSA-128f', (66, 33, 6, 128, 64, 60),
  [(0, -130.36, -254.60, -254.60, None), (64, -67.36, -127.60, -127.60, -189.06)],
  (126.38, -4.99, -2.85, -1.94),
  [(112, -19.36, -31.60, -45.06, -19.36), (120, -11.36, -15.60, -21.04, -11.29),
   (124, -7.36, -7.60, -8.75, -6.21), (128, -3.36, 0.40, 8.44, 8.44)], 131.36, 126.36),
 ('SLH192s', 'SLH-DSA-192s', (63, 17, 14, 192, 64, 64),
  [(0, -192.91, -381.82, -381.82, None), (96, -97.91, -190.82, -190.82, -284.88)],
  (190.41, -3.50, -2.00, -1.65),
  [(176, -17.91, -30.82, -44.88, -17.90), (184, -9.91, -14.82, -20.86, -9.86),
   (188, -5.91, -6.82, -8.66, -5.16), (192, -1.91, 1.18, 7.24, 7.26)], 193.91, 190.37),
 ('SLH192f', 'SLH-DSA-192f', (66, 33, 8, 192, 64, 60),
  [(0, -194.16, -382.85, -382.85, None), (96, -99.16, -191.85, -191.85, -285.68)],
  (190.60, -4.57, -2.66, -1.90),
  [(176, -19.16, -31.85, -45.68, -19.16), (184, -11.16, -15.85, -21.67, -11.11),
   (188, -7.16, -7.85, -9.44, -6.29), (192, -3.16, 0.15, 7.01, 7.03)], 195.16, 190.58),
 ('SLH256s', 'SLH-DSA-256s', (64, 22, 14, 256, 64, 64),
  [(0, -255.01, -507.87, -507.87, None), (128, -128.01, -252.87, -252.87, -378.86)],
  (253.77, -2.23, -1.32, -1.55),
  [(240, -16.01, -28.87, -42.86, -16.01), (248, -8.01, -12.87, -18.85, -7.96),
   (252, -4.01, -4.87, -6.64, -3.23), (256, -0.01, 3.13, 9.50, 9.52)], 256.01, 253.66),
 ('SLH256f', 'SLH-DSA-256f', (68, 35, 9, 256, 64, 60),
  [(0, -254.91, -507.96, -507.96, None), (128, -127.91, -252.96, -252.96, -379.19)],
  (253.89, -2.03, -1.19, -1.53),
  [(240, -15.91, -28.96, -43.19, -15.91), (248, -7.91, -12.96, -19.18, -7.87),
   (252, -3.91, -4.96, -7.01, -3.23), (256, 0.09, 3.04, 8.07, 8.12)], 255.91, 253.76),
 ('ShrincsSl', 'SHRINCS-sl', (45, 10, 13, 128, 40, 60),
  [(0, -129.24, -255.99, -255.99, None), (40, -90.24, -176.99, -176.99, -265.36),
   (64, -66.24, -128.99, -128.99, -193.36), (80, -50.24, -96.99, -96.99, -145.36)],
  (127.99, -2.24, -1.00, -1.38),
  [(112, -18.24, -32.99, -49.36, -18.24), (120, -10.24, -16.99, -25.36, -10.22),
   (124, -6.24, -8.99, -13.33, -6.03), (128, -2.24, -0.99, -0.98, 0.29)], 130.24, 127.87),
]
TABLE6_SHR = (12235, [-12.29, -18.31, -25.82, -34.92, -45.38, -56.99, -69.63, -83.28, -98.00, -114.15])

def hund(v): return round(v * 100)
def fmt(B):  # hundredths -> Lean real literal
    s = '-' if B < 0 else ''
    a = abs(B)
    return f"({s}{a // 100}.{a % 100:02d} : ℝ)"
def floor_pow2(B, N=100):
    """largest q with q^N <= 2^B"""
    lo, hi = 1, 2**(B // N + 1)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**N <= 2**B: lo = mid
        else: hi = mid
    return lo

REPORT = []
def emit(mod, title, par, t3, star, grid, xex, q1p):
    h, k, a, lK, lr, G = par
    S = Set(h, k, a, lK, lr, G)
    th, tt, rr, KK = f"(1 / 2 ^ {h})", f"(2 ^ {a})", f"(2 ^ {lr})", f"(2 ^ {lK})"
    def qs(lq): return "1" if lq == 0 else f"(2 ^ {lq})"
    def qname(lq): return "q1" if lq == 0 else f"q2e{lq}"
    def qtxt(lq): return "q = 1" if lq == 0 else f"q = 2^{lq}"
    L = []
    w = L.append
    def check(x, B, what):
        ok = holds(x, B)
        if not ok:
            REPORT.append(f"{title} {what}: paper bound 2^{B/100:.2f} NOT certifiable, value 2^{log2(x):.4f}")
        return ok
    def certify(X, x, paper, what, hX):
        """emit a proof of X ≤ 2^(paper + 0.01); falls back to the true rounding if the paper is off."""
        B = hund(paper) + 1
        if not check(x, B, what):
            B = math.ceil(log2(x) * 100) + 1
            assert holds(x, B)
        return (f"{X} ≤ (2 : ℝ) ^ {fmt(B)}",
                f"le_two_rpow_of_check (N := 100) (by norm_num) ({B}) (by norm_num)\n      ({hX}) (by decide +kernel)", B)
    hγ = "gamma_le"
    def srch(q): return f"searchTerm {th} {tt} {k} {rr} {q}"
    def psum(q): return f"pullSum {th} {tt} {k} {rr} {q} {KK}"
    def pterm(q, m): return f"pullTerm {th} {tt} {k} {rr} {q} {KK} {m}"
    def rem(q): return f"remainderTwo {th} {tt} {k} {rr} {q} {KK}"
    def mb(q): return f"mainBound {th} {tt} {k} {rr} {q} {KK}"
    hTh = f"theta_eq (by norm_num) {hγ}"
    w(f"""module

public import ShrincsSecurity.ITSR.Concrete.Certify

/-!
# Concrete bounds at {title}

`ITSR-Classical.pdf`, Section 7, Tables 2–5 and 7 (exact columns), at {title}:
`h = {h}` (`θ = 2^-{h}`), `k = {k}`, `t = 2^{a}`, `|K| = 2^{lK}`, `r = 2^{lr}`.

`gammaHi j` are 64-bit dyadic upper bounds on `Γ_j(r)`, `j ≤ {k}`, checked by the kernel against the
bracket of Lemma 13 (`gammaHiQ`, truncation point `G = {G}`, rounding `2^-{P}`); every row below
is then a rational computation from these bounds checked by `decide +kernel`. Each printed figure
`v` of the paper (a rounding to two decimals of `log₂` of a term) is certified as the bound
`term ≤ 2^(v + 0.01)`, unless stated otherwise.
-/

@[expose] public section

namespace ShrincsSecurity.ITSR.Concrete.{mod}

set_option maxRecDepth 100000

/-- Upper bounds on `Γ_j(2^{lr})`, `j = 0, …, {k}`, at {title}. -/
def gammaHi (j : ℕ) : ℚ :=
  [""")
    w(",\n".join(f"    {m} / 2 ^ {E}" if E >= 0 else f"    {m} * 2 ^ {-E}" for m, E in S.gl))
    w(f"""  ].getD j 0

theorem gammaHi_check : ∀ j ≤ {k}, gammaHiQ {h} {a} {lr} {G} {P} j ≤ gammaHi j := by
  decide +kernel

/-- `Γ_j(2^{lr}) ≤ gammaHi j` for `j ≤ {k}` (Lemma 13). -/
theorem gamma_le : ∀ j ≤ {k}, gamma {th} {tt} {rr} j ≤ (gammaHi j : ℝ) := fun j hj =>
  (gamma_le_gammaHiQ (by norm_num) {a} {lr} {G} {P} j (by norm_num) (by norm_num)).trans
    (by exact_mod_cast gammaHi_check j hj)

theorem theta_eq : ({th[1:-1]} : ℝ) = (({th[1:-1]} : ℚ) : ℝ) := by push_cast; rfl
""")
    # Table 7: Gamma_k
    st, pf, B = certify(f"gamma {th} {tt} {rr} {k}", S.gv[k], -xex, "Γ_k", f"{hγ} {k} le_rfl")
    w(f"""/-- Table 7 (`x^ex = {xex:.2f}`): `Γ_{k}(2^{lr}) ≤ 2^-(x^ex - 0.01)`, i.e. the search term is at most
`(q + 1) 2^-(x^ex - 0.01)`. -/
theorem table7_gamma : {st} :=
  {pf}
""")
    # Table 3
    for (lq, s, K, T1, T2) in t3:
        q = 1 if lq == 0 else 2**lq
        crude = lr + min(lq, lK) - lK
        parts, pfs = [], []
        for X, x, v, nm, hX in [(srch(qs(lq)), S.search(q), s, "search", f"searchTerm_le_Q {hγ} _"),
                                (psum(qs(lq)), S.pullSum(q), K, "K-term", f"pullSum_le_Q {hTh} _ _"),
                                (pterm(qs(lq), 1), S.pullTerm(q, 1), T1, "T1", f"pullTerm_le_Q {hTh} _ _ 1")] + \
                               ([(pterm(qs(lq), 2), S.pullTerm(q, 2), T2, "T2", f"pullTerm_le_Q {hTh} _ _ 2")] if T2 is not None else []) + \
                               [(mb(qs(lq)), S.main(q), s, "total", f"mainBound_le_Q {hTh} _ _")]:
            st, pf, B = certify(X, x, v, f"Table 3 q=2^{lq} {nm}", hX)
            parts.append(st); pfs.append(pf)
            if nm == "K-term": BK = B
        assert BK + 8890 <= crude * 100, (title, lq)
        parts.append(f"{psum(qs(lq))} ≤\n      (2 : ℝ) ^ (-88.9 : ℝ) * crudeTerm {rr} {qs(lq)} {KK}")
        pfs.append(f"le_two_rpow_mul_of_le hK (crudeTerm_two_pow {lr} {lq} {lK} (by norm_num)) (by norm_num)")
        t2s = f", `T₂ = 2^{T2:.2f}`" if T2 is not None else " (`T₂ = 0`)"
        w(f"""/-- Table 3, {title}, `{qtxt(lq)}` (exact column): search term `2^{s:.2f}`,
`|K|`-term `2^{K:.2f}`, `T₁ = 2^{T1:.2f}`{t2s};
the bound of Theorem 2 is the search term up to rounding; and the `|K|`-term is below the
`|K|`-term `r · min(q, |K|) / |K| = 2^{crude}` of Theorem 1 by more than 88.9 bits (Section 4). -/
theorem table3_{qname(lq)} :
    """ + " ∧\n    ".join(parts) + " := by\n  have hK :\n      " + parts[1] + " :=\n    " + pfs[1] + "\n  exact ⟨" +
          ",\n    ".join([pfs[0], "hK"] + pfs[2:]) + "⟩\n")
    # q* row
    lstar, s, T1, T2 = star
    lo, hi = 1, 2**(lK + 1)
    while hi - lo > 1:  # largest q with certified K-term <= 1
        mid = (lo + hi) // 2
        if S.pullSum(mid) <= 1: lo = mid
        else: hi = mid
    qc = lo
    Bq = hund(lstar) - 1
    okq = qc**100 >= 2**Bq
    if not okq: REPORT.append(f"{title} q*: certified q {log2(F(qc)):.4f} below printed {lstar}")
    parts, pfs = [], []
    parts.append(f"(2 : ℝ) ^ {fmt(Bq)} ≤ (qStar : ℝ)")
    pfs.append(f"two_rpow_le_of_check (N := 100) (by norm_num) {Bq} (by norm_num) (by decide +kernel)")
    parts.append(f"{psum('qStar')} ≤ 1")
    pfs.append(f"le_one_of_check (pullSum_le_Q {hTh} _ _) (by decide +kernel)")
    for X, x, v, nm, hX in [(srch('qStar'), S.search(qc), s, "search", f"searchTerm_le_Q {hγ} _"),
                            (pterm('qStar', 1), S.pullTerm(qc, 1), T1, "T1", f"pullTerm_le_Q {hTh} _ _ 1"),
                            (pterm('qStar', 2), S.pullTerm(qc, 2), T2, "T2", f"pullTerm_le_Q {hTh} _ _ 2")]:
        st, pf, B = certify(X, x, v, f"Table 3 q* {nm}", hX)
        parts.append(st); pfs.append(pf)
    w(f"""/-- The `q` of the last row of Table 3 at {title}: the largest `q` at which the certified
upper bound on the `|K|`-term is at most `1` (`log₂ qStar ≈ {log2(F(qc)):.4f}`; the paper
prints `q* = 2^{lstar:.2f}`). -/
def qStar : ℕ := {qc}

/-- Table 3, {title}, last row (`q = q* = 2^{lstar:.2f}`, exact column): at a
`q ≥ 2^{(Bq/100):.2f}` the `|K|`-term is at most `1`, the search term is `2^{s:.2f}`,
`T₁ = 2^{T1:.2f}`, `T₂ = 2^{T2:.2f}`. -/
theorem table3_qStar :
    """ + " ∧\n    ".join(parts) + " :=\n  ⟨" + ",\n    ".join(pfs) + "⟩\n")
    # Tables 4/5
    tab = 4 if mod in ('SLH128s', 'SLH128f', 'ShrincsSl') else 5
    for (lq, s, T1, R2, tot) in grid:
        q = 2**lq
        parts, pfs = [], []
        for X, x, v, nm, hX in [(srch(qs(lq)), S.search(q), s, "search", f"searchTerm_le_Q {hγ} _"),
                                (pterm(qs(lq), 1), S.pullTerm(q, 1), T1, "T1", f"pullTerm_le_Q {hTh} _ _ 1"),
                                (rem(qs(lq)), S.rem2(q), R2, "R2", f"remainderTwo_le_Q {hTh} _ _"),
                                (mb(qs(lq)), S.main(q), tot, "total", f"mainBound_le_Q {hTh} _ _")]:
            st, pf, B = certify(X, x, v, f"Table {tab} q=2^{lq} {nm}", hX)
            parts.append(st); pfs.append(pf)
        w(f"""/-- Table {tab}, {title}, `log₂ q = {lq}` (exact column): search term `2^{s:.2f}`,
`T₁ = 2^{T1:.2f}`, `R₂ = 2^{R2:.2f}`, and the bound of Theorem 2 `2^{tot:.2f}`. -/
theorem table{tab}_{qname(lq)} :
    """ + " ∧\n    ".join(parts) + " :=\n  ⟨" + ",\n    ".join(pfs) + "⟩\n")
    # Table 7 q1
    B1 = hund(q1p) - 1
    q1 = floor_pow2(B1) + 1  # smallest q with 2^B1 <= q^100 (up to the exact power case)
    while (q1 - 1)**100 >= 2**B1: q1 -= 1
    ok1 = S.main(q1) <= 1
    if not ok1: REPORT.append(f"{title} q1: bound at 2^{B1/100} exceeds 1")
    w(f"""/-- The smallest `q` with `q ≥ 2^{B1/100:.2f}` (Table 7 prints `q₁ = 2^{q1p:.2f}`). -/
def qOne : ℕ := {q1}

/-- Table 7, {title}: the bound of Theorem 2 is at most `1` at `q = qOne ≥ 2^{B1/100:.2f}`,
consistent with `q₁ = 2^{q1p:.2f}`, the largest `q` at which it is at most `1`. -/
theorem table7_qOne :
    (2 : ℝ) ^ {fmt(B1)} ≤ (qOne : ℝ) ∧
    {mb('qOne')} ≤ 1 :=
  ⟨two_rpow_le_of_check (N := 100) (by norm_num) {B1} (by norm_num) (by decide +kernel),
    le_one_of_check (mainBound_le_Q {hTh} _ _) (by decide +kernel)⟩
""")
    if mod == 'ShrincsSl':
        Bq6, vals = TABLE6_SHR
        q6 = floor_pow2(Bq6)
        parts, pfs = [f"qSix ^ 100 ≤ 2 ^ {Bq6}", f"2 ^ {Bq6} < (qSix + 1) ^ 100"], ["by decide +kernel", "by decide +kernel"]
        for m, v in enumerate(vals, 1):
            st, pf, B = certify(pterm('qSix', m), S.pullTerm(q6, m), v, f"Table 6 T{m}", f"pullTerm_le_Q {hTh} _ _ {m}")
            parts.append(st); pfs.append(pf)
        w(f"""/-- `⌊2^{Bq6/100:.2f}⌋` (characterised in `table6_terms`). -/
def qSix : ℕ := {q6}

/-- Table 6, last row: the summands `T₁, …, T₁₀` of Theorem 2 at SHRINCS-sl and `q = ⌊2^{Bq6/100:.2f}⌋`. -/
theorem table6_terms :
    """ + " ∧\n    ".join(parts) + " :=\n  ⟨" + ",\n    ".join(pfs) + "⟩\n")
    w(f"end ShrincsSecurity.ITSR.Concrete.{mod}\n\nend\n")
    return "\n".join(L)

if __name__ == '__main__':
    out = sys.argv[1]
    only = sys.argv[2:] or None
    for row in SETS:
        if only and row[0] not in only: continue
        txt = emit(*row)
        open(os.path.join(out, row[0] + '.lean'), 'w').write(txt)
    print("\n".join(REPORT) or "all paper figures certified")
