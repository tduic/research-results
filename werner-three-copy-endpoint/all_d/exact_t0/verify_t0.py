#!/usr/bin/env python3
"""Standalone exact verifier for the t = 0 (d -> infinity) certificate of the three-copy Werner moment lift.

If it PASSES, then (with the lemma chain of all_d/README.md) q(C) >= 0 for every rank-<=2 C on (C^e)^{(x)3}, for
every e.  Exact integer / rational arithmetic only: Python ints and Fractions, and int64 numpy arithmetic modulo
primes p < 2^26 with explicit no-overflow bounds and CRT under a rigorous magnitude bound.  No floating point.

Checks:
 (A) d-uniform site modules (sites.json), for every cut T and every module r, as statements for ALL d >= 4:
     (A0) the literal walled-Brauer table D_p D_q = d^{l(p,q)} D_{s(p,q)} and D_p^T = D_{p^-1}, recomputed on literal
          tensor indices at d = 3 and confirmed at d = 4;
     (A1) the 24 diagrams are linearly independent for every d >= 4:  det G_d = prod_{lam |- 4} prod_{cells}
          (d + content)^{f_lam^2}  as polynomials (checked at 100 points > degree), whose roots are in [-3, 3];
     (A2) F_r(p)(d) in Z[d]: F(p)^T = F(p^-1) and F(p) adj(F(e)) F(q) = d^l det(F(e)) F(s) as polynomial identities,
          so pi(p) = F(e)^-1 F(p) is a *-representation (w.r.t. the form F(e)) of the abstract algebra, i.e. by (A1)
          of the operator algebra A_T(d);
     (A3) F_r(e)(d) is positive definite for every real d >= 4: every leading principal minor, written in u = d - 4,
          has nonnegative coefficients and a positive constant term;
     (A4) N_r(p)(t) in Q[t]: sum_p' d^{cyc(p^-1 p')} N_r(p')(1/d) = den(1/d) d^{alpha_r + 4} F_r(p)(d) as Laurent
          polynomials in d, with den(t) = (1 - t^2)(1 - 4 t^2)(1 - 9 t^2) (> 0 for 0 < t <= 1/4);
     the t = 0 site matrices are then E_r(p) = D_r N_r(p)(0) with an integer D_r > 0 chosen here.
 (B) qubit modules (qubit.json, d = 2): Gamma_T(P_p) J = J pi(p) on literal tensor indices and G = J^T J;
     E_q(p) = G pi(p).
 (C) literal coupled-block maps (T = {3}, T = {2,3}) by index rearrangement; orbits of the 24^4 diagram tuples;
     objective and equality rows in trace coordinates m (d-free):  Tr[(x)P_w (x) P_wq . Y] =
     sum_q 2^{cyc(wq q)} m[(w1^-1, w2^-1, w3^-1), q].
 (D) every block multiplier X_b = X0_b / 2^s + diag(Delta_b) / DEN is positive definite (Bareiss + margin).
 (E) the identity c = sum_b <X_b, M_b(e_j)> + sum_i lam_i row_i[j] exactly on every orbit coordinate j, with
     M_b(m) = B^T [sum_s m_s (x)_f E_f(s_f)] B (coupled: Bu/Bv parts and diagram maps).
 (F) the trace-row multiplier is >= 0 (every row is 2 x its trace functional; the trace row is 2 Tr = 2 at a
     normalised physical point, so q >= 2 lam_trace >= 0).

Usage: python3 -I verify_t0.py CERT_DIR
"""
import itertools, json, math, os, sys, time, resource
from fractions import Fraction
import numpy as np

T0 = time.time()
CERT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "cert")
PERMS = list(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(PERMS)}


def comp(p, q):
    return tuple(p[q[j]] for j in range(4))


def inv(p):
    out = [0] * 4
    for j, pj in enumerate(p):
        out[pj] = j
    return tuple(out)


def require(cond, msg):
    if not cond:
        raise SystemExit("VERIFY FAIL: " + msg)


def log(msg):
    print(f"[{time.time() - T0:7.1f}s] {msg}", flush=True)


INVI = [IDX[inv(p)] for p in PERMS]
MULI = [[IDX[comp(a, b)] for b in PERMS] for a in PERMS]


def cyc(p):
    seen, c = set(), 0
    for i in range(4):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j); j = p[j]
    return c


CYC = [cyc(p) for p in PERMS]
E_ = IDX[(0, 1, 2, 3)]

PR = []
_q = (1 << 26) - 1
while len(PR) < 600:
    if all(_q % k for k in range(2, int(math.isqrt(_q)) + 1)):
        PR.append(_q)
    _q -= 2


def mm(A, B, p):
    require(A.dtype == np.int64 and B.dtype == np.int64 and p < (1 << 26), "mm: int64 operands and p < 2^26 required")
    out = np.zeros((A.shape[0], B.shape[1]), dtype=np.int64)
    for s in range(0, A.shape[1], 64):
        out = (out + (A[:, s:s + 64] @ B[s:s + 64]) % p) % p
    return out


def crt_vec(res, primes):
    x = [int(v) for v in res[0]]
    M = primes[0]
    for r, p in zip(res[1:], primes[1:]):
        iv = pow(M, -1, p)
        x = [xi + M * (((int(ri) - xi) * iv) % p) for xi, ri in zip(x, r)]
        M *= p
    return [xi - M if xi > M // 2 else xi for xi in x], M


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


# ------------------------------------------------------------------ polynomials over Q (coefficient lists, low first)
def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pmul(a, b):
    if not a or not b:
        return [0]
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def peq(a, b):
    return ptrim(a) == ptrim(b)


def pmat_mul(A, B):
    n, m, k = len(A), len(B), len(B[0])
    return [[ptrim(psum(pmul(A[i][t], B[t][j]) for t in range(m))) for j in range(k)] for i in range(n)]


def psum(lst):
    out = [0]
    for a in lst:
        out = padd(out, a)
    return out


def pdet(M):
    """determinant of a small polynomial matrix by Laplace expansion (k <= 4)"""
    k = len(M)
    if k == 1:
        return M[0][0]
    tot = [0]
    for j in range(k):
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        term = pmul(M[0][j], pdet(minor))
        tot = padd(tot, term if j % 2 == 0 else [-x for x in term])
    return ptrim(tot)


def padj(M):
    k = len(M)
    if k == 1:
        return [[[1]]]
    out = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            minor = [row[:j] + row[j + 1:] for r, row in enumerate(M) if r != i]
            cof = pdet(minor)
            out[j][i] = cof if (i + j) % 2 == 0 else [-x for x in cof]
    return out


def pshift(a, s):
    """coefficients of a(u + s)"""
    out = [0]
    for k_, c in reversed(list(enumerate(a))):
        out = padd(pmul(out, [s, 1]), [c])
    return ptrim(out)


# ======================================================================================== (A) site modules
SITES = json.load(open(os.path.join(CERT, "sites.json")))
den = [Fraction(v) for v in SITES["den"]]
require(peq(den, pmul(pmul([1, 0, -1], [1, 0, -4]), [1, 0, -9])), "den(t) is not (1-t^2)(1-4t^2)(1-9t^2)")


def parse_cut(key):
    return tuple(json.loads(key.replace("(", "[").replace(")", "]").replace(",]", "]")))


def literal_table(T):
    out = {}
    for d in (3, 4):
        G = []
        for p in PERMS:
            M = {}
            for r, c in gamma_pairs(p, d, T):
                M[(r, c)] = 1
            G.append(M)
        key = {frozenset(M): s for s, M in enumerate(G)}
        require(len(key) == 24, "diagrams not distinct")
        S = [[0] * 24 for _ in range(24)]; L = [[0] * 24 for _ in range(24)]
        cols = []
        for M in G:
            bycol = {}
            for (r, c) in M:
                bycol.setdefault(r, []).append(c)
            cols.append(bycol)
        for a in range(24):
            for b in range(24):
                prod = {}
                for (r, c) in G[a]:                         # (Ga Gb)[r, c'] = sum_c Ga[r, c] Gb[c, c']
                    for c2 in cols[b].get(c, ()):
                        prod[(r, c2)] = prod.get((r, c2), 0) + 1
                vals = set(prod.values())
                require(len(vals) == 1, "product of diagrams is not a multiple of a diagram")
                v = vals.pop()
                l = round(math.log(v, d))
                require(d ** l == v, "loop factor not a power of d")
                s = key.get(frozenset(prod))
                require(s is not None, "product support is not a diagram")
                S[a][b], L[a][b] = s, l
        for a in range(24):                               # involution
            require(frozenset((c, r) for (r, c) in G[a]) == frozenset(G[INVI[a]]), "D_p^T != D_{p^-1}")
        out[d] = (S, L)
    require(out[3] == out[4], "walled-Brauer table differs between d = 3 and d = 4")
    return out[3]


# (A1) linear independence of the diagrams for all d >= 4 (same Gram matrix for every cut: HS form is T-invariant)
CHARS = {(4,): [1, 1, 1, 1, 1], (3, 1): [3, 1, -1, 0, -1], (2, 2): [2, 0, 2, -1, 0], (2, 1, 1): [3, -1, -1, 0, 1],
         (1, 1, 1, 1): [1, -1, 1, 1, -1]}
claimed = [1]
for lam, ch in CHARS.items():
    f = ch[0]
    cells = [(i, j) for i, r in enumerate(lam) for j in range(r)]
    for (i, j) in cells:
        for _ in range(f * f):
            claimed = pmul(claimed, [j - i, 1])
require(len(claimed) - 1 == 96, "degree of the claimed Gram determinant")


def bareiss_det(A):
    M = [list(r) for r in A]
    n = len(M); prev = 1; sign = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if M[i][k] != 0), None)
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


for d in range(4, 104):
    G = [[d ** CYC[MULI[INVI[a]][b]] for b in range(24)] for a in range(24)]
    require(bareiss_det(G) == sum(c * d ** i for i, c in enumerate(claimed)), f"Gram determinant at d = {d}")
log("(A1) det G_d = prod (d + content)^{f^2} (degree 96, checked at d = 4..103): the 24 diagrams are linearly "
    "independent for every d >= 4")

SITE = {}
nsite = 0
for key, irs in SITES["cuts"].items():
    T = parse_cut(key)
    S, L = literal_table(T)
    mods = []
    for ir in irs:
        k = ir["dim"]
        require(1 <= k <= 4 and len(ir["F"]) == 24 and len(ir["N"]) == 24, "module shape")
        F = [[[[int(c) for c in ir["F"][p][i][j]] for j in range(k)] for i in range(k)] for p in range(24)]
        require(all(type(c) is int for p in range(24) for i in range(k) for j in range(k) for c in ir["F"][p][i][j]),
                "F entries must be integers")
        # (A2) invariance and homomorphism (polynomial identities)
        for p in range(24):
            for i in range(k):
                for j in range(k):
                    require(peq(F[p][i][j], F[INVI[p]][j][i]), "F(p)^T != F(p^-1)")
        Fe = F[E_]
        dete, adje = pdet(Fe), padj(Fe)
        require(peq(pmat_mul(Fe, adje)[0][0], dete), "adjugate")
        FA = [pmat_mul(F[p], adje) for p in range(24)]
        for p in range(24):
            for q in range(24):
                lhs = pmat_mul(FA[p], F[q])
                rhs_scale = pmul([0] * L[p][q] + [1], dete)
                for i in range(k):
                    for j in range(k):
                        require(peq(lhs[i][j], pmul(rhs_scale, F[S[p][q]][i][j])), f"homomorphism fails T={T}")
        # (A3) positive definiteness of F(e) for all d >= 4
        for m in range(1, k + 1):
            mi = pshift(pdet([row[:m] for row in Fe[:m]]), 4)
            require(mi[0] > 0 and all(c >= 0 for c in mi), "F(e) not certified positive definite for d >= 4")
        # (A4) N(t) relation:  sum_p' d^{cyc(p^-1 p')} N(p')(1/d) * d^K = den(1/d) d^{alpha+4} F(p)(d) * d^K
        al = int(ir["alpha"])
        Nq = [[[[Fraction(c) for c in ir["N"][p][i][j]] for j in range(k)] for i in range(k)] for p in range(24)]
        degN = max(len(Nq[p][i][j]) - 1 for p in range(24) for i in range(k) for j in range(k))
        K = degN + 6 + abs(al) + 8

        def laurent_to_poly(coef_neg):      # sum_n c_n d^{-n} * d^K  -> poly in d
            out = [0] * (K + 1)
            for n, c in enumerate(coef_neg):
                require(K - n >= 0, "K too small")
                out[K - n] += c
            return out
        denK = laurent_to_poly(den)
        for p in range(24):
            for i in range(k):
                for j in range(k):
                    lhs = [0]
                    for q in range(24):
                        lhs = padd(lhs, pmul([0] * CYC[MULI[INVI[p]][q]] + [1], laurent_to_poly(Nq[q][i][j])))
                    rhs = pmul(denK, F[p][i][j])
                    sh = al + 4
                    rhs = [0] * sh + rhs if sh >= 0 else rhs[-sh:]
                    require(peq(lhs, rhs), f"N(t) relation fails T={T} p={p}")
        N0 = [[[Nq[p][i][j][0] for j in range(k)] for i in range(k)] for p in range(24)]
        D = 1
        for M in N0:
            for r in M:
                for v in r:
                    D = math.lcm(D, v.denominator)
        E = np.array([[[int(v * D) for v in r] for r in M] for M in N0], dtype=np.int64)
        require(int(np.abs(E).max()) < 2 ** 40, "t = 0 site matrix too large")
        mods.append(dict(k=k, E=E))
        nsite += 1
    SITE[T] = mods
log(f"(A0, A2-A4) {nsite} d-uniform site modules: literal walled-Brauer tables; *-representations with F(e) positive "
    f"definite for every d >= 4; N(t) = positive multiple of the dual-basis matrices at t = 1/d; t = 0 matrices E")

# ======================================================================================== (B) qubit modules
QM = json.load(open(os.path.join(CERT, "qubit.json")))
QUB = {}
nq = 0
for rep in QM["representations"]:
    require(rep["d"] == 2, "qubit modules must be d = 2")
    T = tuple(rep["cut"])
    pairs = [gamma_pairs(p, 2, T) for p in PERMS]
    mods = []
    for m in rep["modules"]:
        k = m["dim"]
        require(type(k) is int and 1 <= k <= 16, "qubit module dimension must be in 1..16 (no-overflow bound of contract: k^2 p^2 < 2^63)")
        J = [[Fraction(v) for v in row] for row in m["embedding"]]
        require(all(v.denominator == 1 for row in J for v in row), "embedding not integral")
        J = [[int(v) for v in row] for row in J]
        G = [[int(Fraction(v)) for v in row] for row in m["gram"]]
        pi = [[[Fraction(v) for v in row] for row in P] for P in m["basis"]]
        require(all(v.denominator == 1 for P in pi for row in P for v in row), "pi not integral")
        pi = [[[int(v) for v in row] for row in P] for P in pi]
        require(len(pi) == 24, "24 matrices")
        for a in range(k):
            for b in range(k):
                require(G[a][b] == sum(J[t][a] * J[t][b] for t in range(16)), "G != J^T J")
        for pi_, pp in zip(pi, pairs):
            GJ = [[0] * k for _ in range(16)]
            for r, c in pp:
                for a in range(k):
                    GJ[r][a] += J[c][a]
            for t in range(16):
                for a in range(k):
                    require(GJ[t][a] == sum(J[t][b] * pi_[b][a] for b in range(k)), "qubit module identity fails")
        E = np.array([[[sum(G[i][s] * pi[p][s][j] for s in range(k)) for j in range(k)] for i in range(k)]
                      for p in range(24)], dtype=np.int64)
        mods.append(dict(k=k, E=E))
        nq += 1
    QUB[T] = mods
log(f"(B) {nq} qubit modules: literal Gamma_T(P_p) J = J pi(p), G = J^T J at d = 2; E_q = G pi")

# ======================================================================================== (C) maps, orbits, rows
NAMES = ["i0", "i1", "i2", "i3", "j0", "j1", "j2", "j3"]


def literal_map(mpos, T, d=3):
    src = "".join("abcdefgh"[NAMES.index(x)] for x in mpos)
    n = d ** 4

    def perm_t(p):
        M = np.zeros((d,) * 8, dtype=np.int8)
        for x in itertools.product(range(d), repeat=4):
            y = [0] * 4
            for j in range(4):
                y[p[j]] = x[j]
            M[tuple(y) + tuple(x)] = 1
        return M

    def gam(p):
        ax = list(range(8))
        for j in T:
            ax[j], ax[4 + j] = ax[4 + j], ax[j]
        return perm_t(p).transpose(ax).reshape(n, n)

    Gs = [gam(s) for s in PERMS]
    out = []
    for p in PERMS:
        Bm = np.einsum(src + "->abcdefgh", perm_t(p)).reshape(n, n)
        hits = [k for k, Gk in enumerate(Gs) if np.array_equal(Gk, Bm)]
        require(len(hits) == 1, "rearranged diagram is not a unique partially transposed diagram")
        out.append(hits[0])
    return np.array(out)


MAPS = {"c3": {"31": literal_map(["i0", "i1", "j3", "i2", "i3", "j0", "j1", "j2"], (3,)),
               "13": literal_map(["i0", "i1", "j3", "i2", "i3", "j0", "j1", "j2"], (3,)),
               "22": literal_map(["i0", "i1", "i2", "j3", "i3", "j2", "j0", "j1"], (3,))},
        "c23": {"31": literal_map(["i1", "j2", "j3", "i0", "i2", "i3", "j1", "j0"], (2, 3)),
                "13": literal_map(["i0", "i1", "j2", "j3", "i2", "j0", "j1", "i3"], (2, 3)),
                "22": literal_map(["i1", "j3", "i0", "j2", "i2", "i3", "j0", "j1"], (2, 3))}}
log("(C) coupled-block diagram maps recomputed by literal index rearrangement")

BOS = {"31": [(0, 1, 2)], "13": [(0, 1, 2)], "22": [(0, 1), (2, 3)]}
FAMS = ["31", "22", "13"]


def group_perms(groups):
    out = []
    for p in PERMS:
        ok = True
        for j in range(4):
            g = [G for G in groups if j in G]
            if (g and p[j] not in g[0]) or (not g and p[j] != j):
                ok = False
        if ok:
            out.append(IDX[p])
    return out


def orbits(fam):
    G = group_perms(BOS[fam])
    NC = 24 ** 4
    oid = -np.ones(NC, dtype=np.int64)
    n = 0
    for i in range(NC):
        if oid[i] >= 0:
            continue
        t0 = (i // 13824, (i // 576) % 24, (i // 24) % 24, i % 24)
        stack, mem = [t0], {t0}
        while stack:
            t = stack.pop()
            nb = [(t[1], t[0], t[2], t[3]), (t[1], t[2], t[0], t[3]), tuple(INVI[x] for x in t)]
            for g in G:
                nb.append(tuple(MULI[g][x] for x in t)); nb.append(tuple(MULI[x][g] for x in t))
            for s in nb:
                if s not in mem:
                    mem.add(s); stack.append(s)
        for t in mem:
            oid[((t[0] * 24 + t[1]) * 24 + t[2]) * 24 + t[3]] = n
        n += 1
    return oid, n


OID, NV = {}, {}
for fam in FAMS:
    OID[fam], NV[fam] = orbits(fam)
OFF = {"31": 0, "22": NV["31"], "13": NV["31"] + NV["22"]}
NT = sum(NV.values())
ORD = {}
for fam in FAMS:
    o = np.argsort(OID[fam], kind="stable")
    ORD[fam] = (o, np.searchsorted(OID[fam][o], np.arange(NV[fam])), np.bincount(OID[fam], minlength=NV[fam]))
require(max(int(ORD[f][2].max()) for f in FAMS) <= 432, "orbit size bound")
log(f"(C) orbits recomputed: {NV} (total {NT})")


def mrow(fam, terms):
    """trace functional sum coef Tr[(x)P_w (x) P_wq . Y] in m coordinates, orbit-summed (exact integers)"""
    tot = np.zeros((24, 24, 24, 24), dtype=np.int64)
    for cf, w in terms:
        q = np.array([2 ** CYC[MULI[w[3]][x]] for x in range(24)], dtype=np.int64)
        tot[INVI[w[0]], INVI[w[1]], INVI[w[2]], :] += cf * q
    o, st, _ = ORD[fam]
    out = [0] * NT
    for j, v in enumerate(np.add.reduceat(tot.reshape(-1)[o], st)):
        out[OFF[fam] + j] = int(v)
    return out


S03 = IDX[(3, 1, 2, 0)]
c16 = mrow("31", [((-1) ** sum(S) * 2 ** (4 - sum(S)), tuple(S03 if S[i] else E_ for i in range(3)) + (S03,))
                  for S in itertools.product([0, 1], repeat=3)])


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
# every row is TWICE the trace functional (integer coefficients; same scale as the construction's A2 = 2 A_m)
ROWDEF = [("31", [(2, (E_, E_, E_, E_))])]
for fam, r in (("31", 0), ("22", 0), ("13", 3)):
    fx = fixing(r)
    for w in itertools.product(fx, fx, fx, range(24)):
        ROWDEF.append((fam, [(2, w), (-(2 if PERMS[w[3]][r] == r else 1), (w[0], w[1], w[2], remove_slot(w[3], r)))]))
for w in itertools.product(fixing(2), repeat=4):
    ROWDEF.append(("31-22", w, w))
for w in itertools.product(fixing(1), repeat=4):
    ROWDEF.append(("22-13", w, tuple(IDX[comp(comp(PI_ABB, PERMS[x]), inv(PI_ABB))] for x in w)))
require(len(ROWDEF) == 18145, "row enumeration")


def eq_row(i):
    rd = ROWDEF[i]
    if rd[0] == "31-22":
        a, b = mrow("31", [(2, rd[1])]), mrow("22", [(2, rd[2])])
        return [x - y for x, y in zip(a, b)]
    if rd[0] == "22-13":
        a, b = mrow("22", [(2, rd[1])]), mrow("13", [(2, rd[2])])
        return [x - y for x, y in zip(a, b)]
    return mrow(rd[0], rd[1])


MUL = json.load(open(os.path.join(CERT, "multipliers.json")))
rows_sel = MUL["rows"]
lam = [Fraction(v) for v in MUL["lam"]]
require(len(rows_sel) == len(lam) and len(set(rows_sel)) == len(rows_sel), "multiplier rows")
require(all(type(i) is int and 0 <= i < len(ROWDEF) for i in rows_sel), "row index out of range")
EQ = [eq_row(i) for i in rows_sel]
log(f"(C) objective (x16) and {len(EQ)} selected rows recomputed as d-free trace functionals in m "
    f"(trace row {'selected' if 0 in rows_sel else 'not selected'})")

# ======================================================================================== blocks
SPECS = {}
for fam in FAMS:
    for T in {"31": [(), (3,), (0,), (0, 1)], "13": [(), (3,), (0,), (0, 1)], "22": [(), (0,), (2,), (0, 1), (0, 2)]}[fam]:
        SPECS[f"w{fam}{T}"] = dict(T=T, kind="word", fam=fam)
SPECS["c3"] = dict(T=(3,), kind="coupled", maps=MAPS["c3"])
SPECS["c23"] = dict(T=(2, 3), kind="coupled", maps=MAPS["c23"])


def contract(Zm, fs, p):
    ks = [f["k"] for f in fs]
    # no-overflow guard, independent of where the modules came from: each tensordot sums k^2 products < p^2 < 2^52,
    # so k <= 16 keeps every int64 sum below 2^60 (review F1: an unbounded qubit module made these sums wrap silently)
    require(all(type(k) is int and 1 <= k <= 16 for k in ks) and p < (1 << 26), "contract: module dimension must be in 1..16")
    F = Zm.reshape(ks + ks).transpose(0, 4, 1, 5, 2, 6, 3, 7).reshape([k * k for k in ks])
    for f in fs:
        Em = f["E"].reshape(24, -1) % p                 # inner dimension k^2 <= 16: sums < 2^56
        F = np.tensordot(F, Em, axes=([0], [1])) % p
    return F


def osum(F, fam, m, p):
    if m is not None:
        F = F[np.ix_(m, m, m, m)]
    o, st, _ = ORD[fam]
    return np.add.reduceat(F.reshape(-1)[o], st) % p


def to_mod(A, p):
    return np.array([[int(v) % p for v in r] for r in A], dtype=np.int64)


def block_functional(spec, fs, parts, X, primes):
    k = len(X)
    xmax = max(abs(int(v)) for r in X for v in r)
    bmax = max(abs(int(v)) for B in parts for r in B for v in r)
    n = len(parts[0])
    emax = 1
    for f in fs:
        emax *= int(np.abs(f["E"]).max())
    bound = 3 * 432 * 2 * (k * bmax) ** 2 * xmax * n * n * emax
    use, M = [], 1
    for p in primes:
        if M > 2 * bound:
            break
        use.append(p); M *= p
    require(M > 2 * bound, "not enough primes")
    res = []
    for p in use:
        Xm = to_mod(X, p)
        out = np.zeros(NT, dtype=np.int64)
        if spec["kind"] == "word":
            Bm = to_mod(parts[0], p)
            Z = mm(Bm, mm(Xm, Bm.T.copy(), p), p)
            fam = spec["fam"]
            out[OFF[fam]:OFF[fam] + NV[fam]] = osum(contract(Z, fs, p), fam, None, p)
        else:
            Bu, Bv = to_mod(parts[0], p), to_mod(parts[1], p)
            for fam, Z in (("31", mm(Bu, mm(Xm, Bu.T.copy(), p), p)), ("13", mm(Bv, mm(Xm, Bv.T.copy(), p), p)),
                           ("22", 2 * mm(Bu, mm(Xm, Bv.T.copy(), p), p) % p)):
                out[OFF[fam]:OFF[fam] + NV[fam]] = osum(contract(Z, fs, p), fam, spec["maps"][fam], p)
        res.append(out)
    vals, _ = crt_vec(res, use)
    return vals


def leading_minors_positive(A):
    n = len(A)
    M = [list(map(int, r)) for r in A]
    prev = 1
    for k in range(n):
        if M[k][k] <= 0:
            return False
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return True


DEN = int(MUL["delta_den"])
require(DEN > 0, "delta denominator")
total = [Fraction(0)] * NT
corr_acc = [0] * NT
nb, ncorr = 0, 0
names = set()
with open(os.path.join(CERT, "blocks.jsonl")) as fh:
    for line in fh:
        blk = json.loads(line)
        spec = SPECS[blk["spec"]]
        T = spec["T"]
        rs, rq = tuple(blk["rs"]), blk["rq"]
        require(len(rs) == 3 and list(rs) == sorted(rs), "tuple")
        require(all(type(r) is int and 0 <= r < len(SITE[T]) for r in rs) and type(rq) is int
                and 0 <= rq < len(QUB[T]), "module index out of range")
        require((blk["spec"], rs, rq) not in names, "duplicate block"); names.add((blk["spec"], rs, rq))
        fs = [SITE[T][r] for r in rs] + [QUB[T][rq]]
        n = int(np.prod([f["k"] for f in fs]))
        parts = [blk["B"]] if spec["kind"] == "word" else [blk["Bu"], blk["Bv"]]
        parts = [[[int(v) for v in r] for r in B] for B in parts]
        k = len(parts[0][0])
        require(all(len(B) == n and all(len(r) == k for r in B) for B in parts), "basis shape")
        X0 = [[int(v) for v in r] for r in blk["X0"]]
        s = int(blk["s"])
        require(len(X0) == k and all(len(r) == k for r in X0), "X0 shape")
        require(all(X0[i][j] == X0[j][i] for i in range(k) for j in range(i)), "X0 symmetric")
        mu = Fraction(int(blk["mu_num"]), 2 ** int(blk["mu_exp"]))
        require(mu >= 0, "mu")
        sh = Fraction(2 ** s) * mu if s >= 0 else mu / Fraction(2 ** (-s))
        e = sh.denominator
        Y = [[X0[i][j] * e - (sh.numerator if i == j else 0) for j in range(k)] for i in range(k)]
        require(leading_minors_positive(Y), f"X0 - mu I not positive definite in block {blk['spec']} {rs} {rq}")
        corr = [(int(i), int(v)) for i, v in blk.get("delta", [])]
        require(len({i for i, _ in corr}) == len(corr), "duplicate Delta index")
        for i, v in corr:
            require(0 <= i < k, "delta index")
            require(Fraction(abs(v), DEN) <= mu, f"|Delta| exceeds mu in block {blk['spec']} {rs} {rq}")
        F0 = block_functional(spec, fs, parts, X0, PR)
        sc = Fraction(1, 2 ** s) if s >= 0 else Fraction(2 ** (-s))
        for j in range(NT):
            if F0[j]:
                total[j] += F0[j] * sc
        for i, v in corr:
            Eii = [[0] * k for _ in range(k)]; Eii[i][i] = 1
            Fi = block_functional(spec, fs, parts, Eii, PR)
            for j in range(NT):
                if Fi[j]:
                    corr_acc[j] += Fi[j] * v
            ncorr += 1
        nb += 1
        if nb % 100 == 0:
            log(f"   blocks processed: {nb} (corrected diagonal entries so far {ncorr})")
log(f"(D) {nb} blocks positive definite (X0 - mu I > 0 exactly, |Delta_ii| <= mu); {ncorr} corrected entries")
for j in range(NT):
    if corr_acc[j]:
        total[j] += Fraction(corr_acc[j], DEN)
for lv, row in zip(lam, EQ):
    if lv:
        for j in range(NT):
            if row[j]:
                total[j] += lv * row[j]
bad = [j for j in range(NT) if total[j] != Fraction(c16[j], 16)]
require(not bad, f"identity fails on {len(bad)} orbit coordinates (first {bad[:5]})")
log(f"(E) exact identity c = sum_b <X_b, M_b(.)> + sum_i lam_i row_i holds on all {NT} orbit coordinates")
lt = lam[rows_sel.index(0)] if 0 in rows_sel else Fraction(0)
require(lt >= 0, "trace multiplier negative")
log(f"(F) trace-row multiplier = {lt} >= 0")
ru = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
print(json.dumps(dict(status="PASS", blocks=nb, corrected_entries=ncorr, orbit_coordinates=NT, equality_rows=len(EQ),
                      trace_multiplier=str(lt), site_modules=nsite, qubit_modules=nq,
                      seconds=round(time.time() - T0, 1), peak_rss_MB=round(ru / 1024, 1))), flush=True)
