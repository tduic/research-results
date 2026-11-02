#!/usr/bin/env python3
"""Route 2' (layer D's reformulated identity (E')) on a t = 0 certificate.

Runs layerD_proto/route2.py's `full_identity_check` (copied unchanged next to the d = 5 v2 work; path below) with the
t = 0 data substituted:
  * site tables E_r(p) = D_r N_r(p)(0) and qubit tables E_q = G pi (exactly verify_t0.py's), in place of rho = G^T pi;
  * the certificate (blocks, multipliers) of CERT_DIR;
  * rows and objective as d-free trace functionals in m: a term (cf, w) is the tuple function
      t -> cf * [t_0 = w_0^-1][t_1 = w_1^-1][t_2 = w_2^-1] * 2^cyc(w_q t_q),
    the rows being verify_t0.py's (2 x trace functionals) and the objective c = c16 / 16 (passed to route2 as c16 / 2,
    which route2 divides by 8).
For every block part it finds K (fold subgroup of the t = 0 tables) and K_b (the part's actual stabilizer, exact on
generators), contracts once per right coset of K_b on the tree grid, and requires Sym_H D = 0 at every grid point.
Usage: python3 route2_t0.py CERT_DIR [STATS_JSON]
"""
import os, sys, json, itertools
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "construction"))
sys.dont_write_bytecode = True
import t0lib                                                            # noqa: E402

R2 = os.environ.get("ROUTE2_DIR", os.path.join(HERE, "construction", "route2_ref"))   # copy of layerD_proto/{route2,certdata,gen_identity}.py
sys.path.insert(0, R2)
import route2                                                           # noqa: E402

CERT = sys.argv[1]
STATS = sys.argv[2] if len(sys.argv) > 2 else None
blocks, mul = t0lib.load_cert(CERT)
route2.load_blocks = lambda: [dict(b) for b in blocks]
route2.load_multipliers = lambda: mul
route2.load_modules = lambda: None
route2.rho_tables = lambda _m: t0lib.rho_tables(CERT)
CYC, MULI, INVI = route2.CYC, route2.MULI, route2.INVI


def sym_rank1_t0(fam, terms):
    """Sym_H of t -> sum cf [t_i = w_i^-1, i < 3] 2^cyc(w_q t_q) on the grid points (exact)"""
    pts = np.array([t for _, t in route2.grid_points(fam)], dtype=np.int64)
    acc = np.zeros(len(pts), dtype=np.int64)
    for h in route2.h_elements(fam):
        sg = h[0]
        hs = np.array([route2.h_act_s(h, s) for s in range(24)], dtype=np.int64)
        img = hs[pts[:, [sg[0], sg[1], sg[2], 3]]]
        for cf, w in terms:
            v = np.full(len(pts), cf, dtype=np.int64)
            for i in range(3):
                v = v * (img[:, i] == INVI[w[i]])
            tab = np.array([2 ** CYC[MULI[w[3]][p]] for p in range(24)], dtype=np.int64)
            acc = acc + v * tab[img[:, 3]]
    return [int(x) for x in acc]


def rowdefs_t0():
    out = []
    for rd in t0lib.ROWDEF:
        if rd[0] == "31-22":
            out.append({"31": [(2, rd[1])], "22": [(-2, rd[2])]})
        elif rd[0] == "22-13":
            out.append({"22": [(2, rd[1])], "13": [(-2, rd[2])]})
        else:
            out.append({rd[0]: rd[1]})
    return out


E_, S03 = t0lib.E_, t0lib.S03
route2.sym_rank1 = sym_rank1_t0
route2.rowdefs = rowdefs_t0
# c16 / 2 terms (route2 multiplies the objective by L / 8)
route2.objective = lambda: {"31": [((-1) ** sum(S) * 2 ** (3 - sum(S)), tuple(S03 if S[i] else E_ for i in range(3)) + (S03,))
                                   for S in itertools.product([0, 1], repeat=3)]}
cwd = os.getcwd()
ok = route2.full_identity_check()
if STATS:
    os.replace(os.path.join(cwd, "route2_full_stats.json"), STATS)
print(json.dumps(dict(route2_t0="PASS" if ok else "FAIL")))
sys.exit(0 if ok else 1)
