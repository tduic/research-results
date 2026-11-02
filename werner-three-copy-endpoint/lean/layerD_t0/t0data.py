#!/usr/bin/env python3
"""Layer D (t = 0): read a t = 0 certificate directory and recompute the small exact objects layer D needs.

Everything here is untrusted: the Lean kernel re-checks every claim made from it.  The certificate directory is a
parameter (LAYERD_CERT, default all_d/exact_t0_v2/cert, the compact v2 certificate; v1 is all_d/exact_t0/cert).

Conventions are verify_t0.py's: PERMS (itertools order), comp(p, q)[j] = p[q[j]], gamma_pairs, literal tables at d = 3.
"""
import itertools, json, math, os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_WE = os.path.normpath(os.path.join(HERE, "..", ".."))
GEN = os.environ.get("LAYERD_T0_GEN", os.path.join(HERE, "LayerDT0", "Gen"))
CERT = os.environ.get("LAYERD_CERT", os.path.join(REPO_WE, "all_d", "exact_t0_v2", "cert"))

PERMS = list(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(PERMS)}


def comp(p, q):
    return tuple(p[q[j]] for j in range(4))


def inv(p):
    out = [0] * 4
    for j, pj in enumerate(p):
        out[pj] = j
    return tuple(out)


INVI = [IDX[inv(p)] for p in PERMS]
MULI = [[IDX[comp(a, b)] for b in PERMS] for a in PERMS]
E_ = IDX[(0, 1, 2, 3)]

# cut key in sites.json -> (tuple, Lean Finset literal, Lean name suffix)
CUTS = [((), "∅", "E"), ((3,), "{3}", "T3"), ((0,), "{0}", "T0"), ((0, 1), "{0, 1}", "T01"),
        ((2,), "{2}", "T2"), ((0, 2), "{0, 2}", "T02"), ((2, 3), "{2, 3}", "T23")]
CUT_NAME = {c: n for c, _, n in CUTS}
CUT_LEAN = {c: l for c, l, _ in CUTS}


def parse_cut(key):
    return tuple(json.loads(key.replace("(", "[").replace(")", "]").replace(",]", "]")))


def gamma_pairs(p, d, T):
    out = []
    for x in itertools.product(range(d), repeat=4):
        y = [0] * 4
        for j in range(4):
            y[p[j]] = x[j]
        yy, xx = list(y), list(x)
        for j in T:
            yy[j], xx[j] = xx[j], yy[j]
        out.append((((yy[0] * d + yy[1]) * d + yy[2]) * d + yy[3], ((xx[0] * d + xx[1]) * d + xx[2]) * d + xx[3]))
    return out


def literal_table(T, d=3):
    """verify_t0.literal_table at one d: S[a][b], L[a][b] with D_a D_b = d^L D_S."""
    G = [frozenset(gamma_pairs(p, d, T)) for p in PERMS]
    key = {M: s for s, M in enumerate(G)}
    assert len(key) == 24
    cols = []
    for M in G:
        bycol = {}
        for (r, c) in M:
            bycol.setdefault(r, []).append(c)
        cols.append(bycol)
    S = [[0] * 24 for _ in range(24)]
    L = [[0] * 24 for _ in range(24)]
    for a in range(24):
        for b in range(24):
            prod = {}
            for (r, c) in G[a]:
                for c2 in cols[b].get(c, ()):
                    prod[(r, c2)] = prod.get((r, c2), 0) + 1
            vals = set(prod.values())
            assert len(vals) == 1
            v = vals.pop()
            l = round(math.log(v, d))
            assert d ** l == v
            S[a][b], L[a][b] = key[frozenset(prod)], l
    return S, L


def tables():
    out = {}
    for T, _, _ in CUTS:
        t3, t4 = literal_table(T, 3), literal_table(T, 4)
        assert t3 == t4
        out[T] = t3
    return out


def load_qubit():
    """{cut: [dict(k, J (16 x k), F (24 x k x k) = J^T Gamma_T(P_p) J)]}, F cross-checked against E_q = G pi."""
    QM = json.load(open(os.path.join(CERT, "qubit.json")))
    out = {}
    for rep in QM["representations"]:
        assert rep["d"] == 2
        T = tuple(rep["cut"])
        mods = []
        for m in rep["modules"]:
            k = m["dim"]
            J = [[int(Fraction(v)) for v in row] for row in m["embedding"]]
            G = [[int(Fraction(v)) for v in row] for row in m["gram"]]
            pi = [[[int(Fraction(v)) for v in row] for row in P] for P in m["basis"]]
            F = []
            for p in PERMS:
                M = [[0] * k for _ in range(k)]
                for r, c in gamma_pairs(p, 2, T):
                    for a in range(k):
                        for b in range(k):
                            M[a][b] += J[r][a] * J[c][b]
                F.append(M)
            Eq = [[[sum(G[i][s] * pi[p][s][j] for s in range(k)) for j in range(k)] for i in range(k)] for p in range(24)]
            assert F == Eq, "J^T Gamma J != G pi"
            mods.append(dict(k=k, J=J, F=F))
        out[T] = mods
    return out


def load_sites():
    """{cut: [dict(k, alpha, F[p][i][j] (int coeff lists, low first), N[p][i][j] (Fraction coeff lists))]}"""
    S = json.load(open(os.path.join(CERT, "sites.json")))
    out = {}
    for key, irs in S["cuts"].items():
        T = parse_cut(key)
        mods = []
        for ir in irs:
            k = ir["dim"]
            F = [[[[int(c) for c in ir["F"][p][i][j]] for j in range(k)] for i in range(k)] for p in range(24)]
            N = [[[[Fraction(c) for c in ir["N"][p][i][j]] for j in range(k)] for i in range(k)] for p in range(24)]
            mods.append(dict(k=k, alpha=int(ir["alpha"]), F=F, N=N))
        out[T] = mods
    return out, [Fraction(v) for v in S["den"]]


def lean_list(x):
    if isinstance(x, (list, tuple)):
        return "[" + ", ".join(lean_list(v) for v in x) + "]"
    return str(int(x))


def fixing(r):
    return [IDX[p] for p in PERMS if p[r] == r]


def remove_slot(w, r):
    w = PERMS[w]
    if w[r] == r:
        return IDX[w]
    out = list(w)
    out[w.index(r)] = w[r]
    out[r] = r
    return IDX[tuple(out)]


PI_ABB = (3, 1, 0, 2)


def rowdef():
    """verify_t0.ROWDEF, plus a code for each row: ('trace',), ('contrast', fam, r, w), ('3122', w), ('2213', w)."""
    R = [("31", [(2, (E_, E_, E_, E_))])]
    C = [("trace",)]
    for fam, r in (("31", 0), ("22", 0), ("13", 3)):
        fx = fixing(r)
        for w in itertools.product(fx, fx, fx, range(24)):
            R.append((fam, [(2, w), (-(2 if PERMS[w[3]][r] == r else 1), (w[0], w[1], w[2], remove_slot(w[3], r)))]))
            C.append(("contrast", fam, r, w))
    for w in itertools.product(fixing(2), repeat=4):
        R.append(("31-22", w, w))
        C.append(("3122", w))
    for w in itertools.product(fixing(1), repeat=4):
        R.append(("22-13", w, tuple(IDX[comp(comp(PI_ABB, PERMS[x]), inv(PI_ABB))] for x in w)))
        C.append(("2213", w))
    assert len(R) == 18145
    return R, C


def load_multipliers():
    M = json.load(open(os.path.join(CERT, "multipliers.json")))
    return M["rows"], [Fraction(v) for v in M["lam"]], int(M["delta_den"])


FAM_LEAN = {"31": ".f31", "22": ".f22", "13": ".f13"}


def lean_rowcode(c):
    if c[0] == "trace":
        return ".trace"
    if c[0] == "contrast":
        _, fam, r, w = c
        return f".contrast {FAM_LEAN[fam]} {r} {w[0]} {w[1]} {w[2]} {w[3]}"
    w = c[1]
    return f".r{c[0]} {w[0]} {w[1]} {w[2]} {w[3]}"
