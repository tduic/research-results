#!/usr/bin/env python3
"""Generate the identity-slice experiments (c) for the layer-D prototype.

For a slice of blocks, the kernel computes each block part's packed tuple-space tensor
P = sum_t F[t] 2^(D t) (Contract.lean) and checks it against Python's exact value through two
residues (a measurement device: it forces the whole computation). The bignum corrections Delta enter
as a second contraction of Y_Delta = B diag(Delta) B^T per corrected block (digit width ~ 8.2k bits).

Usage: python3 gen_identity.py NAME FIRST COUNT [--delta] [--scatter]
       python3 gen_identity.py NAME I1,I2,...  - [--delta] [--scatter]
  e.g. gen_identity.py Id1 196 1 ; gen_identity.py Id10 190,191,192,193,194,196,197,198,199,200 -
"""
import itertools, json, math, os, sys
import numpy as np
from certdata import load_blocks, load_modules, load_multipliers, lean_bigint, packed, GEN

PERMS = list(itertools.permutations(range(4)))
NAMES = ["i0", "i1", "i2", "i3", "j0", "j1", "j2", "j3"]
M1, M2 = (1 << 61) - 1, 1 << 64


def literal_map(mpos, T, d=3):
    """verify_d5.py's literal_map (coupled-block diagram maps), copied verbatim in substance."""
    src = "".join("abcdefgh"[NAMES.index(x)] for x in mpos)
    n = d ** 4

    def perm_t(p):
        Mt = np.zeros((d,) * 8, dtype=np.int8)
        for x in itertools.product(range(d), repeat=4):
            y = [0] * 4
            for j in range(4):
                y[p[j]] = x[j]
            Mt[tuple(y) + tuple(x)] = 1
        return Mt

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
        assert len(hits) == 1
        out.append(hits[0])
    return out


def coupled_maps():
    return {"c3": {"31": literal_map(["i0", "i1", "j3", "i2", "i3", "j0", "j1", "j2"], (3,)),
                   "13": literal_map(["i0", "i1", "j3", "i2", "i3", "j0", "j1", "j2"], (3,)),
                   "22": literal_map(["i0", "i1", "i2", "j3", "i3", "j2", "j0", "j1"], (3,))},
            "c23": {"31": literal_map(["i1", "j2", "j3", "i0", "i2", "i3", "j1", "j0"], (2, 3)),
                    "13": literal_map(["i0", "i1", "j2", "j3", "i2", "j0", "j1", "i3"], (2, 3)),
                    "22": literal_map(["i1", "j3", "i0", "j2", "i2", "i3", "j0", "j1"], (2, 3))}}


def spec_info(spec):
    if spec.startswith("c"):
        return dict(kind="coupled", T=(3,) if spec == "c3" else (2, 3))
    fam = spec[1:3]
    T = eval(spec[3:])
    return dict(kind="word", fam=fam, T=tuple(T) if isinstance(T, tuple) else (T,))


def rho_tables_t0(cert):
    """t = 0 certificate (all_d/exact_t0/cert): site tables E_r(p) = D_r N_r(p)(0) (D_r = lcm of the denominators,
    as verify_t0.py) under the key (5, cut), qubit tables E_q(p) = G pi(p) under (2, cut); the verifier contracts
    B X B^T with E directly, so rho = E."""
    import json, math
    from fractions import Fraction
    out = {}
    S = json.load(open(os.path.join(cert, "sites.json")))
    for key, irs in S["cuts"].items():
        T = tuple(int(x) for x in key.strip("()").split(",") if x.strip())
        mods = []
        for ir in irs:
            k = ir["dim"]
            N0 = [[[Fraction(ir["N"][p][i][j][0]) for j in range(k)] for i in range(k)] for p in range(24)]
            D = 1
            for M in N0:
                for r in M:
                    for v in r:
                        D = math.lcm(D, v.denominator)
            mods.append(dict(k=k, rho=[[[int(v * D) for v in r] for r in M] for M in N0]))
        out[(5, T)] = mods
    Q = json.load(open(os.path.join(cert, "qubit.json")))
    for rep in Q["representations"]:
        T = tuple(rep["cut"])
        mods = []
        for m in rep["modules"]:
            G = np.array([[int(Fraction(v)) for v in r] for r in m["gram"]], dtype=object)
            pis = [np.array([[int(Fraction(v)) for v in r] for r in P], dtype=object) for P in m["basis"]]
            mods.append(dict(k=m["dim"], rho=[(G.dot(P)).tolist() for P in pis]))
        out[(2, T)] = mods
    return out


def rho_tables(MOD):
    """rho(s) = G pi(s) for every module, keyed by (d, cut). With MOD = None: the t = 0 tables (rho_tables_t0)."""
    if MOD is None:
        from certdata import CERT
        return rho_tables_t0(CERT)
    out = {}
    for rep in MOD["representations"]:
        d, T = rep["d"], tuple(rep["cut"])
        if d not in (2, 5):
            continue
        mods = []
        for m in rep["modules"]:
            G = np.array([[int(v) for v in r] for r in m["gram"]], dtype=object)
            pis = [np.array([[int(v) for v in r] for r in P], dtype=object) for P in m["basis"]]
            mods.append(dict(k=m["dim"], rho=[(G.T.dot(P)).tolist() for P in pis]))
        out[(d, T)] = mods
    return out


def tuple_tensor(Y, ks, rhos):
    """exact F[t1,t2,t3,t4] = sum_{c,b} Y[c,b] prod_f rho_f(t_f)[c_f,b_f] (object ints)."""
    F = np.array(Y, dtype=object).reshape(ks + ks).transpose(0, 4, 1, 5, 2, 6, 3, 7).reshape([k * k for k in ks])
    for f in range(4):
        R = np.array([np.array(r, dtype=object).reshape(-1) for r in rhos[f]], dtype=object)   # 24 x k^2
        F = np.tensordot(F, R, axes=([0], [1]))
    return F.reshape(-1)          # index ((t1*24+t2)*24+t3)*24+t4


def pack_signed(vals, D):
    """sum_t vals[t] 2^(D t) by balanced recursive summation."""
    def rec(lo, hi):
        if hi - lo == 1:
            return int(vals[lo])
        mid = (lo + hi) // 2
        return rec(lo, mid) + (rec(mid, hi) << (D * (mid - lo)))
    return rec(0, len(vals))


def lean_mat(rows):
    return "[" + ", ".join("[" + ", ".join(str(int(v)) if v >= 0 else f"({int(v)})" for v in r) + "]" for r in rows) + "]"


def main():
    name = sys.argv[1]
    if "," in sys.argv[2]:
        sel = [int(x) for x in sys.argv[2].split(",")]
    else:
        sel = list(range(int(sys.argv[2]), int(sys.argv[2]) + int(sys.argv[3])))
    with_delta = "--delta" in sys.argv
    blocks = load_blocks()
    MOD = load_modules()
    RHO = rho_tables(MOD)
    MAPS = coupled_maps()
    DEN = int(load_multipliers()["delta_den"])
    body = ""
    checks = []
    stats = []
    for bi in sel:
        blk = blocks[bi]
        si = spec_info(blk["spec"])
        T = si["T"]
        fs = [RHO[(5, T)][r] for r in blk["rs"]] + [RHO[(2, T)][blk["rq"]]]
        ks = [f["k"] for f in fs]
        n = math.prod(ks)
        X0 = [[int(v) for v in r] for r in blk["X0"]]
        k = len(X0)
        if si["kind"] == "word":
            parts = [(si["fam"], blk["B"], blk["B"], 1, None)]
        else:
            mp = MAPS[blk["spec"]]
            parts = [("31", blk["Bu"], blk["Bu"], 1, mp["31"]), ("13", blk["Bv"], blk["Bv"], 1, mp["13"]),
                     ("22", blk["Bu"], blk["Bv"], 2, mp["22"])]
        mats = [("X0", X0)]
        if with_delta and blk.get("delta"):
            Xd = [[0] * k for _ in range(k)]
            for i, v in blk["delta"]:
                Xd[int(i)][int(i)] = int(v)
            mats.append(("Xd", Xd))
        tag = f"b{bi}"
        body += f"\n-- block {bi}: {blk['spec']} rs={blk['rs']} rq={blk['rq']} k={k} n={n} ks={ks}\n"
        body += f"def {tag}X0 : List (List Int) := {lean_mat(X0)}\n"
        if len(mats) > 1:
            body += f"def {tag}Xd : List (List Int) := [" + ", ".join(
                "[" + ", ".join(lean_bigint(v) if v else "0" for v in r) + "]" for r in mats[1][1]) + "]\n"
        Bnames = {}
        for (fam, Bl, Br, fac, mp) in parts:
            for B in (Bl, Br):
                key = id(B)
                if key not in Bnames:
                    nm = f"{tag}B{len(Bnames)}"
                    Bnames[key] = nm
                    body += f"def {nm} : List (List Int) := {lean_mat([[int(v) for v in r] for r in B])}\n"
        for pi_, (fam, Bl, Br, fac, mp) in enumerate(parts):
            rhos = [f["rho"] if mp is None else [f["rho"][m] for m in mp] for f in fs]
            rname = f"{tag}rho{pi_}"
            body += f"def {rname} : List (List (List (List Int))) := [" + ", ".join(
                "[" + ", ".join(lean_mat(r) for r in rr) + "]" for rr in rhos) + "]\n"
            Bl_ = np.array([[int(v) for v in r] for r in Bl], dtype=object)
            Br_ = np.array([[int(v) for v in r] for r in Br], dtype=object)
            for mname, X in mats:
                Xa = np.array(X, dtype=object)
                BX = Bl_.dot(Xa)
                Y = (BX.dot(Br_.T) * fac)
                w1 = max(1, max(abs(int(v)) for v in BX.reshape(-1))).bit_length() + 2
                w2 = max(1, max(abs(int(v)) for v in (BX.dot(Br_.T)).reshape(-1))).bit_length() + 2
                F = tuple_tensor(Y.tolist(), ks, rhos)
                D = max(1, max(abs(int(v)) for v in F)).bit_length() + 2
                P = pack_signed(F, D)
                lhs = f"tensorP {D} {ks} {rname} (yMat {n} {k} {w1} {w2} {tag}{mname} {Bnames[id(Bl)]} {Bnames[id(Br)]})"
                pn = f"{tag}P{pi_}{mname}"
                body += f"/-- family {fam}, part {pi_}, {mname}: digit width D = {D} bits ({D * 24 ** 4 / 8e6:.1f} MB packed) -/\n"
                body += f"def {pn} : Int := {fac} * {lhs}\n"
                checks.append((pn, P % M1, P % M2))
                stats.append(dict(block=bi, spec=blk["spec"], part=pi_, fam=fam, mat=mname, k=k, n=n, ks=ks, D=D))
    body += "\nset_option profiler true\nset_option profiler.threshold 50\n"
    for pn, h1, h2 in checks:
        body += f"theorem {pn}_ok : {pn} % {M1} = {h1} ∧ {pn} % {M2} = {h2} := by decide +kernel\n"
    if "--scatter" in sys.argv:
        # measurement: the first 2^depth digits of the last part's tensor, a tree, and `nlook` lookups
        import random
        depth, nlook = 14, 10000
        random.seed(0)
        Fs = F[: 2 ** depth]
        idx = [random.randrange(2 ** depth) for _ in range(nlook)]
        body += f"def slice : Int := {pn} % pow2 ({D} * {2 ** depth})\n"
        body += f"def idx : List Nat := {idx}\n"
        body += "set_option profiler true\n"
        body += f"theorem scatter_ok : gather {depth} (build {D} {depth} (bal ({D} * {2 ** depth}) slice)) idx = {sum(int(Fs[i]) for i in idx)} := by decide +kernel\n"
        checks.clear()
    hdr = f"""-- GENERATED by layerD_proto/gen_identity.py {' '.join(sys.argv[1:])}. Do not edit.
import LayerDProto.Contract
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace LayerDProto.Gen.{name}
open LayerDProto
"""
    os.makedirs(GEN, exist_ok=True)
    with open(os.path.join(GEN, name + ".lean"), "w") as fh:
        fh.write(hdr + body + f"\nend LayerDProto.Gen.{name}\n")
    with open(os.path.join(GEN, name + ".json"), "w") as fh:
        json.dump(stats, fh)
    for st in stats:
        print(st)


if __name__ == "__main__":
    main()
