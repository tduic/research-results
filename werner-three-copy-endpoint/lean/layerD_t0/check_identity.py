#!/usr/bin/env python3
"""Layer D (t = 0): numerical cross-check that the Lean hypothesis `IdentityT0` is the certificate's true identity.

Evaluates both sides of IdentityT0 modulo primes p < 2^26 at random orbit-invariant mu, following the Lean
definitions (not the verifier's code paths): mObj / mTr / mRowVal from WernerEndpoint.AllD_MCoord, BlockSpec.L via
blockOp with N(0) = the constant coefficients of the generated SiteData.N lists, Fq = the generated qubit tables,
B in the Kronecker order of LayerDT0.flatIdx, the coupled maps mT3_* / mT23_* parsed from LayerC_Walled.lean
(permMap m p = permTab (m (idx p))), X = X0 / 2^s + diag(Delta) / DEN, lambda = lamNum / lamDen, and the rows
RowCode.row.  A mismatch in any encoding makes the two sides differ at a random point with probability ~1 - 1/p.

Usage: python3 check_identity.py [NPOINTS] [--control]   (prints PASS / FAIL; about 5 minutes per point;\n--control reverses the site order of blocks with rs[0] != rs[2] and must FAIL)
"""
import itertools, math, os, random, re, sys
import numpy as np
import t0data as D
import gen_sites as GS

sys.path.insert(0, os.path.join(D.HERE, "..", "layerD_proto"))
os.environ.setdefault("LAYERD_CERT", D.CERT)
import certdata as C  # noqa: E402

PERMS, IDX, INVI, MULI = D.PERMS, D.IDX, D.INVI, D.MULI


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
BOS = {"31": [(0, 1, 2)], "13": [(0, 1, 2)], "22": [(0, 1), (2, 3)]}


def bos_idx(groups):   # LayerC_Twirl.bos f: g preserves the family's letter pattern
    pat = {"31": [0, 0, 0, 1], "22": [0, 0, 1, 1], "13": [1, 1, 1, 0]}[groups]
    return [IDX[p] for p in PERMS if all(pat[p[k]] == pat[k] for k in range(4))]


def orbit_ids(fam):
    """orbits of the orbitGens generators (site permutations, componentwise inversion, left / right bos mult)"""
    G = bos_idx(fam)
    oid = -np.ones(24 ** 4, dtype=np.int64)
    n = 0
    for i in range(24 ** 4):
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


def lean_maps():
    src = open(os.path.join(D.REPO_WE, "lean", "WernerEndpoint", "LayerC_Walled.lean")).read()
    out = {}
    for nm in ("mT3_31", "mT3_22", "mT3_13", "mT23_31", "mT23_22", "mT23_13"):
        m = re.search(r"def " + nm + r" : Fin 24 → Fin 24 :=\s*!\[([^\]]*)\]", src)
        out[nm] = [int(x) for x in m.group(1).split(",")]
    return out


def mtr(w, mu_f, p):
    """mTr 2 w mu = sum_q 2^cyc(wq * q) mu((w_i^-1)_i, q)"""
    a, b, c, wq = INVI[w[0]], INVI[w[1]], INVI[w[2]], w[3]
    return sum(pow(2, CYC[MULI[wq][q]], p) * int(mu_f[a, b, c, q]) for q in range(24)) % p


def row_terms(code):
    """RowCode.row as [(coef, fam, (w0, w1, w2, wq))]"""
    E = 0
    if code[0] == "trace":
        return [(2, "31", (E, E, E, E))]
    if code[0] == "contrast":
        _, fam, r, w = code
        c = 2 if PERMS[w[3]][r] == r else 1
        return [(2, fam, w), (-c, fam, (w[0], w[1], w[2], D.remove_slot(w[3], r)))]
    w = code[1]
    if code[0] == "3122":
        return [(2, "31", w), (-2, "22", w)]
    cj = tuple(D.IDX[D.comp(D.comp(D.PI_ABB, PERMS[x]), D.inv(D.PI_ABB))] for x in w)
    return [(2, "22", w), (-2, "13", cj)]


def contract(Z, Es, p):
    ks = [E.shape[1] for E in Es]
    F = Z.reshape(ks + ks).transpose(0, 4, 1, 5, 2, 6, 3, 7).reshape([k * k for k in ks]) % p
    for E in Es:
        F = np.tensordot(F, E.reshape(24, -1) % p, axes=([0], [1])) % p
    return F                       # F[s0, s1, s2, sq] = sum_{x,y} Z[x, y] prod_f E_f(s_f)[x_f, y_f]


def mm(A, B, p):
    out = np.zeros((A.shape[0], B.shape[1]), dtype=np.int64)
    for s in range(0, A.shape[1], 64):
        out = (out + (A[:, s:s + 64] @ B[s:s + 64]) % p) % p
    return out


def check(p, seed, control=False):
    rnd = random.Random(seed)
    sites, _ = D.load_sites()
    qub = D.load_qubit()
    sd = {T: [GS.site_data(T, r, m) for r, m in enumerate(mods)] for T, mods in sites.items()}
    E_site = {T: [np.array([[[l[0] if l else 0 for l in row] for row in s["N"][q]] for q in range(24)], dtype=np.int64)
                  for s in v] for T, v in sd.items()}
    E_q = {T: [np.array(Q["F"], dtype=np.int64) for Q in v] for T, v in qub.items()}
    maps = lean_maps()
    mu = {}
    for fam in ("31", "22", "13"):
        oid, n = orbit_ids(fam)
        vals = np.array([rnd.randrange(p) for _ in range(n)], dtype=np.int64)
        mu[fam] = vals[oid].reshape(24, 24, 24, 24)
    inv2 = pow(2, -1, p)
    # objective: sum_S (-1/2)^|S| mTr 2 (objSites S, swap 0 3) mu31
    S03 = IDX[(3, 1, 2, 0)]
    lhs = 0
    for S in itertools.product([0, 1], repeat=3):
        w = tuple(S03 if S[i] else 0 for i in range(3)) + (S03,)
        lhs += pow(-inv2 % p, sum(S), p) * mtr(w, mu["31"], p)
    lhs %= p
    rows_sel, lam, _ = D.load_multipliers()
    _, codes = D.rowdef()
    den = 1
    for x in lam:
        den = den * x.denominator // math.gcd(den, x.denominator)
    rhs = 0
    for i, lv in zip(rows_sel, lam):
        val = sum(c * mtr(w, mu[f], p) for c, f, w in row_terms(codes[i])) % p
        rhs += (int(lv * den) % p) * pow(den, -1, p) * val
    _, _, DEN = D.load_multipliers()
    for blk in C.load_blocks():
        spec = blk["spec"]
        T = (3,) if spec == "c3" else (2, 3) if spec == "c23" else D.parse_cut(spec[3:])
        Es = [E_site[T][r] for r in blk["rs"]] + [E_q[T][blk["rq"]]]
        if control and blk["rs"][0] != blk["rs"][2]:      # negative control: wrong site order in the Kronecker layout
            Es = [Es[2], Es[1], Es[0], Es[3]]
        k = len(blk["X0"])
        X = np.array([[int(v) % p for v in r] for r in blk["X0"]], dtype=np.int64) * pow(2, -int(blk["s"]), p) % p
        for i, v in blk.get("delta", []):
            X[i, i] = (X[i, i] + int(v) % p * pow(DEN, -1, p)) % p
        tomod = lambda B: np.array([[int(v) % p for v in r] for r in B], dtype=np.int64)
        if "B" in blk:
            B = tomod(blk["B"])
            F = contract(mm(B, mm(X, B.T.copy(), p), p), Es, p)
            rhs += int((F * mu[spec[1:3]] % p).sum() % p)
        else:
            Bu, Bv = tomod(blk["Bu"]), tomod(blk["Bv"])
            tag = "mT3_" if spec == "c3" else "mT23_"
            parts = (("31", mm(Bu, mm(X, Bu.T.copy(), p), p)), ("13", mm(Bv, mm(X, Bv.T.copy(), p), p)),
                     ("22", (mm(Bu, mm(X, Bv.T.copy(), p), p) + mm(Bu, mm(X.T.copy(), Bv.T.copy(), p), p)) % p))
            for fam, Z in parts:
                m = maps[tag + fam]
                F = contract(Z, Es, p)[np.ix_(m, m, m, m)]
                rhs += int((F * mu[fam] % p).sum() % p)
    rhs %= p
    return lhs == rhs, lhs, rhs


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    n = int(args[0]) if args else 1
    control = "--control" in sys.argv
    ok = True
    for i in range(n):
        p = [67108859, 67108837, 67108819][i % 3]
        r, l, rr = check(p, 1000 + i, control)
        print(f"point {i}: p = {p}  lhs = {l}  rhs = {rr}  {'equal' if r else 'DIFFERENT'}", flush=True)
        ok &= r
    print(("CONTROL " if control else "") + ("PASS" if ok else "FAIL"))


if __name__ == "__main__":
    main()
