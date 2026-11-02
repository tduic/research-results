#!/usr/bin/env python3
"""Route 2 for the identity (E): symmetrize on the block side, then evaluate at orbit representatives.

For a block part with tuple-space functional F[t] = <Y, (x)_f rho_f(m(t_f))> (Y = Bl X Br^T), the orbit
coordinate the verifier needs is  sum_{t in orb j} F[t] = (|orb j| / |H|) sum_{h in H} F[h t_j].
H = (site permutations x inversion) . (G_L x G_R), G = the family's bosonic group (|H| = 432 / 288).

* Bosonic part on the block side: for the subgroup K of G whose action is module-local (rho_r(m(k s)) =
  A_r(k) rho_r(m(s)) for every module), sum_{k in K} F[k u] = <Pi_L^T Y, (x)rho(m(u))>, Pi_L = sum_k (x)_f A_f(k);
  likewise on the right. So Y-bar = Pi_L^T Y Pi_R'^T = (Pi_L^T Bl) X (Pi_R Br)^T: the symmetrization is a
  change of the basis matrices (data), not kernel work. The remaining coset representatives c, c' of K in G
  each need one contraction with the re-indexed tables rho(m(c s c')).
* Site permutations and inversion: evaluate F_bos at the 12 images of each orbit representative.

This script checks, on real blocks, that route 2 reproduces the verifier's orbit sums exactly, and counts
the costs (cosets per block) for the whole certificate.

Usage: python3 route2.py [block indices...]      route 2 (bosonic fold + coset contractions) vs the verifier
       python3 route2.py recipe [blocks...]       the tree-grid recipe (E') vs the verifier, per block part
       python3 route2.py census [out.json]        contractions per block part for the whole certificate
       python3 route2.py full                     the whole reformulated identity (E') on the real certificate
       python3 route2.py costs                    per-part inputs of the Lean cost model (route2_census.json)
"""
import itertools, math, sys
import numpy as np
from certdata import load_blocks, load_modules, load_multipliers
from gen_identity import rho_tables, coupled_maps, tuple_tensor, spec_info, PERMS

IDX = {p: i for i, p in enumerate(PERMS)}
comp = lambda p, q: tuple(p[q[j]] for j in range(4))
inv = lambda p: tuple(sorted(range(4), key=lambda j: p[j]))
MULI = [[IDX[comp(a, b)] for b in PERMS] for a in PERMS]
INVI = [IDX[inv(p)] for p in PERMS]
BOS = {"31": [(0, 1, 2)], "13": [(0, 1, 2)], "22": [(0, 1), (2, 3)]}


def group_perms(groups):
    out = []
    for p in PERMS:
        ok = all((p[j] in [g for g in groups if j in g][0]) if any(j in g for g in groups) else p[j] == j
                 for j in range(4))
        if ok:
            out.append(IDX[p])
    return out


def orbits(fam):
    """verify_d5.py's orbit partition (same generators)."""
    G = group_perms(BOS[fam])
    oid = -np.ones(24 ** 4, dtype=np.int64)
    reps, n = [], 0
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
        reps.append((t0, len(mem)))
        n += 1
    return oid, reps


def site_inv_images(t):
    """the 12 images of t under site permutations (first three components) and inversion"""
    out = []
    for p in itertools.permutations(range(3)):
        u = (t[p[0]], t[p[1]], t[p[2]], t[3])
        out.append(u)
        out.append(tuple(INVI[x] for x in u))
    return out


def module_local(rho, k, side, g):
    """A with rho(g s) = A rho(s) (side L) or C with rho(s g) = rho(s) C (side R) for all s, exactly
    (rational solve), or None. rho: list of 24 k x k integer matrices (already re-indexed by the map)."""
    from fractions import Fraction
    import sympy
    if side == "L":
        lhs = [rho[MULI[g][s]] for s in range(24)]
        # A rho(s) = lhs(s) for all s: A [rho(0) .. rho(23)] = [lhs(0) .. lhs(23)]
        Rm = sympy.Matrix(np.hstack([np.array(r, dtype=object) for r in rho]))
        Lm = sympy.Matrix(np.hstack([np.array(r, dtype=object) for r in lhs]))
        try:
            sol = Rm.T.solve_least_squares(Lm.T)
        except Exception:
            return None
        A = sol.T
        return A if A * Rm == Lm else None
    else:
        lhs = [rho[MULI[s][g]] for s in range(24)]
        Rm = sympy.Matrix(np.vstack([np.array(r, dtype=object) for r in rho]))
        Lm = sympy.Matrix(np.vstack([np.array(r, dtype=object) for r in lhs]))
        try:
            C = Rm.solve_least_squares(Lm)
        except Exception:
            return None
        return C if Rm * C == Lm else None


def kron_all(ms):
    out = ms[0]
    for m in ms[1:]:
        out = sympy_kron(out, m)
    return out


def sympy_kron(a, b):
    import sympy
    return sympy.Matrix(np.kron(np.array(a.tolist(), dtype=object), np.array(b.tolist(), dtype=object)))


def block_parts(blk, RHO, MAPS):
    si = spec_info(blk["spec"])
    T = si["T"]
    fs = [RHO[(5, T)][r] for r in blk["rs"]] + [RHO[(2, T)][blk["rq"]]]
    if si["kind"] == "word":
        return T, fs, [(si["fam"], blk["B"], blk["B"], 1, None)]
    mp = MAPS[blk["spec"]]
    return T, fs, [("31", blk["Bu"], blk["Bu"], 1, mp["31"]), ("13", blk["Bv"], blk["Bv"], 1, mp["13"]),
                   ("22", blk["Bu"], blk["Bv"], 2, mp["22"])]


def route2_part(blk, part, fs, X, ORB):
    """orbit sums of one block part by route 2; returns (vector, number of coset contractions, |K_L|, |K_R|)"""
    import sympy
    fam, Bl, Br, fac, mp = part
    G = group_perms(BOS[fam])
    rhos = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
    # compatible subgroups: g with a module-local A for every factor
    KL, KR, AL, CR = [], [], {}, {}
    for g in G:
        As = [module_local(r, f["k"], "L", g) for r, f in zip(rhos, fs)]
        if all(a is not None for a in As):
            KL.append(g); AL[g] = As
        Cs = [module_local(r, f["k"], "R", g) for r, f in zip(rhos, fs)]
        if all(c is not None for c in Cs):
            KR.append(g); CR[g] = Cs
    # coset representatives: G = U_c K c  (left side: g = k c), G = U_c' c' K (right: g' = c' k')
    cl, seen = [], set()
    for g in G:
        cos = frozenset(MULI[k][g] for k in KL)
        if cos not in seen:
            seen.add(cos); cl.append(g)
    cr, seen = [], set()
    for g in G:
        cos = frozenset(MULI[g][k] for k in KR)
        if cos not in seen:
            seen.add(cos); cr.append(g)
    n = math.prod(f["k"] for f in fs)
    PiL = sum((kron_all(AL[k]) for k in KL), sympy.zeros(n, n))
    PiR = sum((kron_all(CR[k]) for k in KR), sympy.zeros(n, n))
    Bl_ = sympy.Matrix(Bl); Br_ = sympy.Matrix(Br)
    BL = PiL.T * Bl_            # new basis matrices: Y-bar = BL X BR^T
    BR = PiR * Br_
    Ybar = (BL * sympy.Matrix(X) * BR.T) * fac
    Ybar = [[int(v) for v in row] for row in Ybar.tolist()]
    ks = [f["k"] for f in fs]
    Fbos = np.zeros(24 ** 4, dtype=object)
    for c in cl:
        for c2 in cr:
            tabs = [[r[MULI[MULI[c][s]][c2]] for s in range(24)] for r in rhos]
            Fbos = Fbos + tuple_tensor(Ybar, ks, tabs)
    oid, reps = ORB[fam]
    Hsz = 12 * len(G) ** 2
    out = []
    for (t0, size) in reps:
        tot = sum(Fbos[((u[0] * 24 + u[1]) * 24 + u[2]) * 24 + u[3]] for u in site_inv_images(t0))
        assert (tot * size) % Hsz == 0
        out.append(tot * size // Hsz)
    return out, len(cl) * len(cr), len(KL), len(KR)


def reference_part(blk, part, fs, X, ORB):
    fam, Bl, Br, fac, mp = part
    rhos = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
    Y = (np.array(Bl, dtype=object).dot(np.array(X, dtype=object)).dot(np.array(Br, dtype=object).T) * fac).tolist()
    F = tuple_tensor(Y, [f["k"] for f in fs], rhos)
    oid, reps = ORB[fam]
    out = [0] * len(reps)
    for t in range(24 ** 4):
        out[oid[t]] += F[t]
    return out


def main():
    blocks = load_blocks()
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    sel = [int(a) for a in sys.argv[1:]] or [190, 197, 834]
    fams = set()
    for bi in sel:
        T, fs, parts = block_parts(blocks[bi], RHO, MAPS)
        fams |= {p[0] for p in parts}
    ORB = {f: orbits(f) for f in sorted(fams)}
    for bi in sel:
        blk = blocks[bi]
        T, fs, parts = block_parts(blk, RHO, MAPS)
        X = [[int(v) for v in r] for r in blk["X0"]]
        for pi_, part in enumerate(parts):
            r2, ncos, kl, kr = route2_part(blk, part, fs, X, ORB)
            ref = reference_part(blk, part, fs, X, ORB)
            print(f"block {bi} {blk['spec']} part {pi_} fam {part[0]} T={T}: |K_L|={kl} |K_R|={kr} "
                  f"coset contractions={ncos}; route 2 == verifier orbit sums: {r2 == ref}", flush=True)



# ---------------------------------------------------------------------------------------------
# Full H-symmetrization with data folds: census of the contractions the kernel must do
# ---------------------------------------------------------------------------------------------
# An element h = (sigma, eps, g, g') of H acts by (h t)_f = g . eps(t_{sigma(f)}) . g'  (f = 0,1,2; the qubit
# component q is not permuted).  F[h t] = <P_sigma Y P_sigma^T, (x)_u tau_u(t_u)> with the re-indexed tables
# tau_u(s) = rho_{sigma^-1 u}(g eps(s) g').  h is FOLDABLE when every tau_u(s) = A_u rho_u(s) C_u (or
# A_u rho_u(s)^T C_u) for all s: then F o h = F_{Y'} with Y' a fixed linear image of Y (data, no kernel work).
# The foldable elements form a subgroup K; Sym_H F = sum over the right cosets K r of F_fold o r, one
# contraction per coset representative r.

def _vec_rows(tabs):
    import sympy
    return sympy.Matrix([[int(v) for v in np.array(m, dtype=object).reshape(-1)] for m in tabs])


_PHI_CACHE = {}


def phi_kron(src, dst, key=None):
    """Is s -> dst(s) of the form A src(s) C or A src(s)^T C (the src(s) span the full matrix algebra)?
    Returns 'N' (plain), 'T' (transposed) or None."""
    import sympy
    if key is not None and key in _PHI_CACHE:
        return _PHI_CACHE[key]
    k = len(src[0])
    if len(dst[0]) != k:
        _PHI_CACHE[key] = None
        return None
    S = _vec_rows(src); Dm = _vec_rows(dst)
    # pick k^2 independent rows of S
    rows, cur = [], sympy.zeros(0, k * k)
    for i in range(24):
        cand = cur.col_join(S[i, :])
        if cand.rank() > cur.rows:
            cur = cand; rows.append(i)
        if len(rows) == k * k:
            break
    Ssub = S.extract(rows, list(range(k * k))); Dsub = Dm.extract(rows, list(range(k * k)))
    PhiT = Ssub.inv() * Dsub                  # vec(dst)^T = vec(src)^T PhiT  (row vectors)
    res = None
    if S * PhiT == Dm:
        for mode in ("N", "T"):
            Phi = PhiT.T
            if mode == "T":                   # precompose with transposition of src
                perm = [(j % k) * k + j // k for j in range(k * k)]
                Phi = Phi.extract(list(range(k * k)), perm)
            # reshuffle: Phi[(i,j),(i',j')] -> R[(i,i'),(j,j')]; Kronecker iff rank 1
            R = sympy.zeros(k * k, k * k)
            for i in range(k):
                for j in range(k):
                    for i2 in range(k):
                        for j2 in range(k):
                            R[i * k + i2, j * k + j2] = Phi[i * k + j, i2 * k + j2]
            if R.rank() <= 1:
                res = mode
                break
    if key is not None:
        _PHI_CACHE[key] = res
    return res


def h_elements(fam):
    G = group_perms(BOS[fam])
    return [(sg, e, g, g2) for sg in itertools.permutations(range(3)) for e in (0, 1) for g in G for g2 in G]


def h_act_s(h, s):
    """the S4 map s -> g eps(s) g' of h"""
    sg, e, g, g2 = h
    x = INVI[s] if e else s
    return MULI[MULI[g][x]][g2]


def h_act(h, t):
    sg = h[0]
    src = (t[sg[0]], t[sg[1]], t[sg[2]], t[3])
    return tuple(h_act_s(h, x) for x in src)


_PROBE = [(0, 5, 11, 17), (3, 9, 22, 1), (7, 13, 2, 20)]
_SIG = {}


def h_compose(h1, h2, fam):
    """element h with h t = h1 (h2 t) (lookup by the action on three probe tuples, which separates H)"""
    if fam not in _SIG:
        tab = {}
        for h in h_elements(fam):
            tab[tuple(h_act(h, t) for t in _PROBE)] = h
        assert len(tab) == len(h_elements(fam))
        _SIG[fam] = tab
    return _SIG[fam][tuple(h_act(h1, h_act(h2, t)) for t in _PROBE)]


def generators(K, fam):
    """a small generating set of the subgroup K"""
    gens, span = [], {h for h in K if h_act(h, _PROBE[0]) == _PROBE[0] and h_act(h, _PROBE[1]) == _PROBE[1]
                      and h_act(h, _PROBE[2]) == _PROBE[2]}
    for h in K:
        if h in span:
            continue
        gens.append(h)
        frontier = list(span)
        span.add(h)
        frontier = list(span)
        while frontier:
            new = []
            for a in frontier:
                for g in gens:
                    c = h_compose(a, g, fam)
                    if c not in span:
                        span.add(c); new.append(c)
            frontier = new
    assert span == set(K)
    return gens


def fold_subgroup(tabs, mods, fam):
    """K = foldable elements of H for one block part (tabs: the four re-indexed tables, mods: ids for caching)"""
    K = []
    for h in h_elements(fam):
        sg = h[0]
        inv_sg = [sg.index(u) for u in range(3)] + [3]
        ok = True
        for u in range(4):
            srcf = inv_sg[u]                 # tau_u(s) = rho_{sigma^-1 u}(h_s(s))
            dst = [tabs[srcf][h_act_s(h, s)] for s in range(24)]
            if phi_kron(tabs[u], dst, key=(mods[u], mods[srcf], h[1:])) is None:
                ok = False
                break
        if ok:
            K.append(h)
    return K


def census(out_json=None):
    """For every block part: n, |H|, |K|, number of contractions |H|/|K|."""
    import json, collections
    blocks = load_blocks()
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    rows = []
    for bi, blk in enumerate(blocks):
        T, fs, parts = block_parts(blk, RHO, MAPS)
        for pi_, (fam, Bl, Br, fac, mp) in enumerate(parts):
            tabs = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
            mods = [(blk["spec"] if mp else "", fam, T, f_i, r) for f_i, r in
                    enumerate(list(blk["rs"]) + [("q", blk["rq"])])]
            # cache key must identify the table: (map, T, module index); site modules share tables
            mods = [(blk["spec"] if mp else "w", fam if mp else "", T, ("q", blk["rq"]) if u == 3 else blk["rs"][u])
                    for u in range(4)]
            K = fold_subgroup(tabs, mods, fam)
            H = 12 * len(group_perms(BOS[fam])) ** 2
            assert H % len(K) == 0
            n = math.prod(f["k"] for f in fs)
            rows.append(dict(block=bi, part=pi_, spec=blk["spec"], fam=fam, n=n, k=len(Bl[0]),
                             H=H, K=len(K), contractions=H // len(K)))
        if bi % 100 == 99:
            print(f"census: {bi + 1} blocks", flush=True)
    if out_json:
        json.dump(rows, open(out_json, "w"))
    return rows


# ---------------------------------------------------------------------------------------------
# The reformulated check (E'): Sym_H D = 0 on a tree grid R that meets every H-orbit
# ---------------------------------------------------------------------------------------------
# R = { t : t_q = d in DCOS, t_2 in S1[d], t_0, t_1 arbitrary }, DCOS = representatives of the double cosets
# G \ S4 / G, S1[d] = representatives of the orbits of Stab(d) = {(g, g') : g d g' = d} on S4 (s -> g s g').
# Every bosonic orbit (hence every H-orbit) meets R.  For a block part with K-invariant F (K = the fold subgroup),
#   Sym_H F (t) = |K| sum_{r in K\H} F(r t),   F(r t) = <Y, (x)_f rho_f(r_s(t_{sigma(f)}))>,
# so each coset representative r = (sigma, eps, g, g') is one packed contraction of Y in which Y-axis f is
# contracted against the table s -> rho_f(r_s(s)) at the stride of output coordinate sigma(f).

def tree_grid(fam):
    G = group_perms(BOS[fam])
    seen, DC = set(), []
    for s in range(24):
        if s not in seen:
            DC.append(s)
            seen |= {MULI[MULI[g][s]][h] for g in G for h in G}
    S1 = {}
    for d in DC:
        st = [(g, h) for g in G for h in G if MULI[MULI[g][d]][h] == d]
        seen, reps = set(), []
        for s in range(24):
            if s not in seen:
                reps.append(s)
                seen |= {MULI[MULI[g][s]][h] for g, h in st}
        S1[d] = reps
    return DC, S1


def grid_points(fam):
    DC, S1 = tree_grid(fam)
    pts = []
    for d in DC:
        for t0 in range(24):
            for t1 in range(24):
                for i2, t2 in enumerate(S1[d]):
                    pts.append((d, (t0, t1, t2, d)))
    return pts


def right_coset_reps(K, fam):
    """representatives r of the right cosets K r (r ranges over H; K r = {k o r})"""
    Ks = set(K)
    reps, covered = [], set()
    for h in h_elements(fam):
        if h in covered:
            continue
        reps.append(h)
        for k in K:
            covered.add(h_compose(k, h, fam))
    return reps


def recipe_tables(r, d, S1d, ntabs):
    """for coset rep r and grid value d: per Y-axis f the selection list (table indices) and the stride unit
    (in digits) of its output coordinate; output digit index = i2 + |S1d| (t1 + 24 t0)."""
    sg = r[0]
    sel, unit = [], []
    for f in range(4):
        c = sg[f] if f < 3 else 3          # output coordinate paired with Y-axis f: (r t)_f uses t_{sigma(f)}
        if c == 3:
            sel.append([h_act_s(r, d)]); unit.append(0)
        elif c == 2:
            sel.append([h_act_s(r, s) for s in S1d]); unit.append(1)
        elif c == 1:
            sel.append([h_act_s(r, s) for s in range(24)]); unit.append(len(S1d))
        else:
            sel.append([h_act_s(r, s) for s in range(24)]); unit.append(24 * len(S1d))
    return sel, unit


def recipe_part(Y, ks, tabs, reps, fam):
    """kernel recipe in exact Python: {d: list of digit values over (t0, t1, i2)} of sum_r F(r t)"""
    DC, S1 = tree_grid(fam)
    out = {}
    Yt = np.array(Y, dtype=object).reshape(ks + ks).transpose(0, 4, 1, 5, 2, 6, 3, 7).reshape([k * k for k in ks])
    for d in DC:
        acc = np.zeros((24, 24, len(S1[d])), dtype=object)
        for r in reps:
            sel, unit = recipe_tables(r, d, S1[d], 4)
            # contract each Y-axis f against rho_f at the selected indices; then place by output coordinate
            F = Yt
            for f in range(4):
                R = np.array([np.array(tabs[f][s], dtype=object).reshape(-1) for s in sel[f]], dtype=object)
                F = np.tensordot(F, R, axes=([0], [1]))
            # F axes: (sel0, sel1, sel2, sel3); map to output (t0, t1, i2) by sigma
            sg = r[0]
            F = F[:, :, :, 0]
            order = [None, None, None]
            for f in range(3):
                order[sg[f]] = f
            acc = acc + np.transpose(F, order)
        out[d] = acc.reshape(-1)
    return out


def validate_recipe(sel_blocks):
    """route-2' recipe vs the verifier's orbit sums: |K| sum_r F(r t) == |H| / |orb(t)| * orbit_sum(oid(t))"""
    blocks = load_blocks()
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    ORB = {}
    ok_all = True
    for bi in sel_blocks:
        blk = blocks[bi]
        T, fs, parts = block_parts(blk, RHO, MAPS)
        X = [[int(v) for v in r] for r in blk["X0"]]
        for pi_, part in enumerate(parts):
            fam, Bl, Br, fac, mp = part
            if fam not in ORB:
                ORB[fam] = orbits(fam)
            oid, reps_o = ORB[fam]
            sizes = [s for _, s in reps_o]
            tabs = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
            mods = [(blk["spec"] if mp else "w", fam if mp else "", T, ("q", blk["rq"]) if u == 3 else blk["rs"][u])
                    for u in range(4)]
            Y = (np.array(Bl, dtype=object).dot(np.array(X, dtype=object)).dot(np.array(Br, dtype=object).T) * fac).tolist()
            # K_b: the elements of the fold subgroup under which this part's functional is invariant (exact)
            F0 = np.array(tuple_tensor(Y, [f["k"] for f in fs], tabs), dtype=object)
            K = [h for h in fold_subgroup(tabs, mods, fam) if _invariant(F0, h)]
            reps = right_coset_reps(K, fam)
            Hn = 12 * len(group_perms(BOS[fam])) ** 2
            ref = reference_part(blk, part, fs, X, ORB)
            got = recipe_part(Y, [f["k"] for f in fs], tabs, reps, fam)
            DC, S1 = tree_grid(fam)
            ok = True
            for d in DC:
                vals = got[d]
                idx = 0
                for t0 in range(24):
                    for t1 in range(24):
                        for t2 in S1[d]:
                            j = oid[((t0 * 24 + t1) * 24 + t2) * 24 + d]
                            if len(K) * vals[idx] * sizes[j] != Hn * ref[j]:
                                ok = False
                            idx += 1
            ok_all &= ok
            print(f"block {bi} {blk['spec']} part {pi_} fam {fam}: |K|={len(K)} coset reps={len(reps)} "
                  f"grid={sum(576 * len(S1[d]) for d in DC)}: recipe == verifier orbit sums: {ok}", flush=True)
    return ok_all


# ---------------------------------------------------------------------------------------------
# The whole identity in the reformulated form, on the real certificate
# ---------------------------------------------------------------------------------------------
# For every family phi:  Sym_{H_phi}( sum_b F_b^phi + sum_i lam_i row_i^phi - c^phi / 8 ) (t) = 0  for all t in R_phi,
# with X_b = X0_b / 2^s_b + diag(Delta_b) / DEN (the verifier's (E), multiplied through by |H| / |orbit|).
# Objective and rows: the verifier's definitions (rank-one Kronecker functionals from the trace formula).

DIM = 5
CYC = []
for _p in PERMS:
    _seen, _c = set(), 0
    for _i in range(4):
        if _i not in _seen:
            _c += 1
            _j = _i
            while _j not in _seen:
                _seen.add(_j); _j = _p[_j]
    CYC.append(_c)
E_, S03 = IDX[(0, 1, 2, 3)], IDX[(3, 1, 2, 0)]
PI_ABB = (3, 1, 0, 2)


def _fixing(r):
    return [IDX[p] for p in PERMS if p[r] == r]


def _remove_slot(w, r):
    w = PERMS[w]
    if w[r] == r:
        return IDX[w]
    out = list(w)
    out[w.index(r)] = w[r]
    out[r] = r
    return IDX[tuple(out)]


def rowdefs():
    """verify_d5.py's ROWDEF, as {family: [(coef, w)]} per row"""
    R = [{"31": [(1, (E_, E_, E_, E_))]}]
    for fam, r in (("31", 0), ("22", 0), ("13", 3)):
        fx = _fixing(r)
        for w in itertools.product(fx, fx, fx, range(24)):
            R.append({fam: [(2, w), (-(2 if PERMS[w[3]][r] == r else 1), (w[0], w[1], w[2], _remove_slot(w[3], r)))]})
    for w in itertools.product(_fixing(2), repeat=4):
        R.append({"31": [(1, w)], "22": [(-1, w)]})
    for w in itertools.product(_fixing(1), repeat=4):
        R.append({"22": [(1, w)], "13": [(-1, tuple(IDX[comp(comp(PI_ABB, PERMS[x]), inv(PI_ABB))] for x in w))]})
    assert len(R) == 18145
    return R


def objective():
    return {"31": [((-1) ** sum(S) * 2 ** (3 - sum(S)), tuple(S03 if S[i] else E_ for i in range(3)) + (S03,))
                   for S in itertools.product([0, 1], repeat=3)]}


def sym_rank1(fam, terms):
    """Sym_H of t -> sum coef prod_{i<3} 5^cyc(w_i t_i) 2^cyc(w_q t_q), on the grid points (exact int64)"""
    pts = np.array([t for _, t in grid_points(fam)], dtype=np.int64)
    out = np.zeros(len(pts), dtype=object)
    CY = np.array(CYC, dtype=np.int64)
    acc = np.zeros(len(pts), dtype=np.int64)
    for h in h_elements(fam):
        sg = h[0]
        hs = np.array([h_act_s(h, s) for s in range(24)], dtype=np.int64)
        img = hs[pts[:, [sg[0], sg[1], sg[2], 3]]]
        for cf, w in terms:
            v = np.full(len(pts), cf, dtype=np.int64)
            for i in range(4):
                tab = np.array([(DIM if i < 3 else 2) ** CYC[MULI[w[i]][p]] for p in range(24)], dtype=np.int64)
                v = v * tab[img[:, i]]
            acc = acc + v                    # |v| <= 8 * 5^12 * 16 < 2^35; 432 * #terms terms: < 2^48
    return [int(x) for x in acc]


PRIMES = []
_q = (1 << 26) - 1
while len(PRIMES) < 64:
    if all(_q % _k for _k in range(2, int(math.isqrt(_q)) + 1)):
        PRIMES.append(_q)
    _q -= 2


def _crt(res, primes):
    x = [int(v) for v in res[0]]
    M = primes[0]
    for r, p in zip(res[1:], primes[1:]):
        iv = pow(M, -1, p)
        x = [xi + M * (((int(ri) - xi) * iv) % p) for xi, ri in zip(x, r)]
        M *= p
    return [xi - M if xi > M // 2 else xi for xi in x]


def recipe_exact(Y, ks, tabs, reps, fam):
    """recipe_part, exactly, by int64 arithmetic modulo enough primes p < 2^26 and CRT (rigorous bound)."""
    DC, S1 = tree_grid(fam)
    Yo = np.array(Y, dtype=object)
    ymax = max(1, int(np.abs(Yo).max()))
    bound = len(reps) * ymax * Yo.size
    for t in tabs:
        bound *= max(1, max(abs(int(v)) for m in t for r in m for v in r))
    use, M = [], 1
    for p in PRIMES:
        if M > 2 * bound:
            break
        use.append(p); M *= p
    assert M > 2 * bound
    Ytt = Yo.reshape(ks + ks).transpose(0, 4, 1, 5, 2, 6, 3, 7).reshape([k * k for k in ks])
    TA = [np.array([np.array(m, dtype=object).reshape(-1) for m in t], dtype=object) for t in tabs]   # 24 x k^2
    out = {}
    YP = {p: (Ytt % p).astype(np.int64) for p in use}
    TP = {p: [(t % p).astype(np.int64) for t in TA] for p in use}
    for d in DC:
        res = []
        for p in use:
            Yp, Tp = YP[p], TP[p]
            acc = np.zeros((24, 24, len(S1[d])), dtype=np.int64)
            for r in reps:
                sel, unit = recipe_tables(r, d, S1[d], 4)
                sg = r[0]
                # contract Y-axis 3 (one point) first, then the axis paired with coordinate 2, then the others
                order = [3] + sorted(range(3), key=lambda f: -sg[f])
                F, axes = Yp, [0, 1, 2, 3]
                for f in order:
                    R = Tp[f][sel[f]]                                    # |sel| x k_f^2
                    F = np.tensordot(F, R, axes=([axes.index(f)], [1])) % p
                    axes = [a for a in axes if a != f] + [("o", f)]
                # F axes: ('o',3), then ('o', f) for the other three in `order`; map to (t0, t1, i2)
                F = F.reshape(F.shape[1:])
                ofs = [a[1] for a in axes[1:]]                           # Y-axes in current order
                perm = [ofs.index(next(f for f in range(3) if sg[f] == c)) for c in range(3)]
                acc = (acc + np.transpose(F, perm)) % p
            res.append(acc.reshape(-1))
        out[d] = np.array(_crt(res, use), dtype=object)
    return out


def stabilizer(tabs, Fexact_list, coefs, K, fam):
    """{k in K : sum_i coefs_i F_i o k == sum_i coefs_i F_i} exactly, where F_i are exact integer tuple tensors
    (int64-safe) and coefs are Python ints: the unique rows of the matrix [F_i o k - F_i] are tested exactly."""
    idx = np.arange(24 ** 4)
    tup = np.stack([idx // 13824, (idx // 576) % 24, (idx // 24) % 24, idx % 24], 1)
    out = []
    for h in K:
        sg = h[0]
        hs = np.array([h_act_s(h, s) for s in range(24)])
        img = hs[tup[:, [sg[0], sg[1], sg[2], 3]]]
        j = ((img[:, 0] * 24 + img[:, 1]) * 24 + img[:, 2]) * 24 + img[:, 3]
        G = np.stack([F[j] - F for F in Fexact_list], 1)
        U = np.unique(G, axis=0)
        if all(sum(int(c) * int(g) for c, g in zip(coefs, row)) == 0 for row in U):
            out.append(h)
    return out


def full_identity_check(limit=None, log_every=50):
    """The reformulated identity (E') on the whole certificate, exactly.  Returns True iff it holds.
    Per block part: K = fold subgroup (data folds of the module tables); K_b = the elements of K under which the
    part's actual functional (X0 / 2^s + diag(Delta) / DEN) is invariant (exact test); one tree-grid contraction
    per right coset K_b r."""
    from fractions import Fraction
    import time
    t0 = time.time()
    blocks = load_blocks()
    if limit:
        blocks = blocks[:limit]
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    MUL = load_multipliers()
    DEN = int(MUL["delta_den"])
    lam = [Fraction(v) for v in MUL["lam"]]
    smax = max(int(b["s"]) for b in load_blocks())
    L = math.lcm(8, *[l.denominator for l in lam]) * DEN * 2 ** smax
    fams = ["31", "22", "13"]
    npts = {f: len(grid_points(f)) for f in fams}
    acc = {f: np.zeros(npts[f], dtype=object) for f in fams}
    ncontr, nshrunk, stats = 0, 0, []
    for bi, blk in enumerate(blocks):
        T, fs, parts = block_parts(blk, RHO, MAPS)
        s = int(blk["s"])
        X0 = [[int(v) for v in r] for r in blk["X0"]]
        k = len(X0)
        corr = [(int(i), int(v)) for i, v in blk.get("delta", [])]
        for pi_, part in enumerate(parts):
            fam, Bl, Br, fac, mp = part
            ks = [f["k"] for f in fs]
            tabs = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
            mods = [(blk["spec"] if mp else "w", fam if mp else "", T, ("q", blk["rq"]) if u == 3 else blk["rs"][u])
                    for u in range(4)]
            K = fold_subgroup(tabs, mods, fam)
            Bl_, Br_ = np.array(Bl, dtype=object), np.array(Br, dtype=object)
            Ys = [(Bl_.dot(np.array(X0, dtype=object)).dot(Br_.T) * fac)]
            for i, _ in corr:
                Ys.append(np.outer(Bl_[:, i], Br_[:, i]) * fac)
            # K_b: candidates by int64 arithmetic modulo two primes, then an exact check on generators
            F0 = np.array(tuple_tensor(Ys[0].tolist(), ks, tabs), dtype=object)
            Fs = [np.array(tuple_tensor(Y.tolist(), ks, tabs), dtype=object) for Y in Ys[1:]]
            hashes = []
            for p in PRIMES[:2]:
                H0 = (F0 % p).astype(np.int64)
                for (i, v), Fi in zip(corr, Fs):
                    H0 = (H0 + (Fi % p).astype(np.int64) * (v * 2 ** s % p)) % p
                hashes.append(H0)
            Kb = [h for h in K if all(_invariant(Hh, h) for Hh in hashes)]
            Ftot = F0 * DEN + sum((Fi * (v * 2 ** s) for (i, v), Fi in zip(corr, Fs)), np.zeros(1, dtype=object))
            assert all(_invariant(Ftot, g) for g in generators(Kb, fam)), "K_b candidate not exact"
            nshrunk += len(Kb) < len(K)
            reps = right_coset_reps(Kb, fam)
            DC, _ = tree_grid(fam)
            vals = [recipe_exact(Y.tolist(), ks, tabs, reps, fam) for Y in Ys]
            v0 = np.concatenate([vals[0][d] for d in DC])
            tot = v0 * (DEN * (L // (2 ** s * DEN)))
            for (i, v), vv in zip(corr, vals[1:]):
                tot = tot + np.concatenate([vv[d] for d in DC]) * (v * (L // DEN))
            acc[fam] = acc[fam] + tot * len(Kb)
            ncontr += len(reps) * len(DC) * len(Ys)
            stats.append(dict(block=bi, part=pi_, fam=fam, K=len(K), Kb=len(Kb), reps=len(reps), ys=len(Ys)))
        if (bi + 1) % log_every == 0:
            print(f"[{time.time() - t0:7.1f}s] blocks {bi + 1}, contractions {ncontr}, parts with K_b < K: {nshrunk}",
                  flush=True)
    R = rowdefs()
    for i, lv in zip(MUL["rows"], lam):
        if lv == 0:
            continue
        for fam, terms in R[i].items():
            acc[fam] = acc[fam] + np.array(sym_rank1(fam, terms), dtype=object) * int(lv * L)
    for fam, terms in objective().items():
        acc[fam] = acc[fam] - np.array(sym_rank1(fam, terms), dtype=object) * (L // 8)
    ok = True
    for fam in fams:
        nz = int(sum(1 for v in acc[fam] if v != 0))
        print(f"family {fam}: {npts[fam]} grid points, nonzero residuals: {nz}", flush=True)
        ok &= nz == 0
    print(f"[{time.time() - t0:7.1f}s] reformulated identity (E') on the real certificate: {'PASS' if ok else 'FAIL'}; "
          f"{ncontr} tree-grid contractions; {nshrunk} parts where Delta shrinks K", flush=True)
    import json
    json.dump(stats, open("route2_full_stats.json", "w"))
    return ok


_TUP = None


def _invariant(F, h):
    global _TUP
    if _TUP is None:
        idx = np.arange(24 ** 4)
        _TUP = np.stack([idx // 13824, (idx // 576) % 24, (idx // 24) % 24, idx % 24], 1)
    sg = h[0]
    hs = np.array([h_act_s(h, s) for s in range(24)])
    img = hs[_TUP[:, [sg[0], sg[1], sg[2], 3]]]
    j = ((img[:, 0] * 24 + img[:, 1]) * 24 + img[:, 2]) * 24 + img[:, 3]
    return bool((F[j] == F).all())


def cost_census(out_json="route2_census.json", stats_json="route2_full_stats.json"):
    """Per block part, the quantities the Lean cost model needs: n, k, k_q, |K|, coset representatives (for K and,
    from the full check's stats, for K_b), grid values d, the (d, qubit diagram) pairs that share the packed first
    level, and the scalar units sum_(rep, d) (n / k_q)^2 (packed first level) and n^2 (scalar first level)."""
    import json, os
    blocks = load_blocks()
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    kb = {}
    if os.path.exists(stats_json):
        for x in json.load(open(stats_json)):
            kb[(x["block"], x["part"])] = x["reps"]
    rows = []
    for bi, blk in enumerate(blocks):
        T, fs, parts = block_parts(blk, RHO, MAPS)
        ks = [f["k"] for f in fs]
        n = math.prod(ks)
        for pi_, (fam, Bl, Br, fac, mp) in enumerate(parts):
            tabs = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
            mods = [(blk["spec"] if mp else "w", fam if mp else "", T, ("q", blk["rq"]) if u == 3 else blk["rs"][u])
                    for u in range(4)]
            K = fold_subgroup(tabs, mods, fam)
            reps = right_coset_reps(K, fam)
            DC, S1 = tree_grid(fam)
            l1 = {(d, h_act_s(r, d)) for r in reps for d in DC}
            n1 = n // ks[3]
            rows.append(dict(block=bi, part=pi_, spec=blk["spec"], fam=fam, n=n, k=len(Bl[0]), ks=ks, K=len(K),
                             reps=len(reps), reps_b=kb.get((bi, pi_)), D=len(DC), l1=len(l1),
                             units_packed=len(reps) * len(DC) * n1 * n1, units_scalar=len(reps) * len(DC) * n * n))
    json.dump(rows, open(out_json, "w"))
    return rows


if __name__ == "__main__":
    if sys.argv[1:2] == ["full"]:                  # the whole identity (E') on the real certificate
        sys.exit(0 if full_identity_check() else 1)
    if sys.argv[1:2] == ["recipe"]:                # the tree-grid recipe vs the verifier, per block part
        sys.exit(0 if validate_recipe([int(a) for a in sys.argv[2:]] or [0, 120, 495, 834, 919]) else 1)
    if sys.argv[1:2] == ["costs"]:                 # per-part cost-model inputs (route2_census.json)
        cost_census()
        sys.exit(0)
    if sys.argv[1:2] == ["census"]:
        census(sys.argv[2] if len(sys.argv) > 2 else None)
        sys.exit(0)
    main()
