#!/usr/bin/env python3
"""Layer D (t = 0): the part lists `PsT0 f` of `LayerDT0/Gen/IdentityParts.lean`, in Python (untrusted mirror).

`IdentityDec.allParts` lists, in this order: the 8 objective unit parts (`objParts`), the parts of every block
in `blocks.jsonl` order (`blockParts`: one part for a word block, the 31, 22, 13 parts for a coupled block), and
the unit parts of every selected row in row order (`rowParts`, `RowCode.uterms`). `PsT0 f` keeps the parts of
family f in that order. This module returns, per family, the list of part descriptors with their `fac`:

  ("obj", S_index, fac)            unit part of the objective subset subsets3[S_index]
  ("blk", j, part, fac)            part in {"w", "31", "22", "13"} of block j
  ("row", r, i, fac)               unit term i of row r

The identity-module generator writes one PartData per descriptor; the kernel then checks that the generated
list has the same `PartData.core` as `PsT0 f` (`famZero_congr`), so a mistake here makes the build fail, never
proves anything false.
"""
import math
import os
import sys

import t0data as D

sys.path.insert(0, os.path.join(D.HERE, "..", "layerD_proto"))
os.environ.setdefault("LAYERD_CERT", D.CERT)
import certdata as C  # noqa: E402

FAMS = ["31", "22", "13"]
SUBSETS3 = [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]


def scale(blocks, lam_den, den):
    """idS = lcm(8, lamDen, 2^{s_b} DEN)."""
    return math.lcm(8, lam_den, *[(2 ** int(b["s"])) * den for b in blocks])


def lam_num_den(lam):
    den = 1
    for x in lam:
        den = den * x.denominator // math.gcd(den, x.denominator)
    return [int(x * den) for x in lam], den


def row_uterm_coefs(code):
    """The integer coefficients and families of RowCode.uterms (same order)."""
    if code[0] == "trace":
        return [(2, "31")]
    if code[0] == "contrast":
        _, fam, r, w = code
        return [(2, fam), (-(2 if D.PERMS[w[3]][r] == r else 1), fam)]
    if code[0] == "3122":
        return [(2, "31"), (-2, "22")]
    if code[0] == "2213":
        return [(2, "22"), (-2, "13")]
    raise ValueError(code)


def all_parts():
    """[(family, descriptor)] in allParts order, and S."""
    blocks = C.load_blocks()
    rows_sel, lam, den = D.load_multipliers()
    num, lam_den = lam_num_den(lam)
    S = scale(blocks, lam_den, den)
    out = []
    for i, Sub in enumerate(SUBSETS3):
        k = len(Sub)
        out.append(("31", ("obj", i, -((-1) ** k * 2 ** (3 - k) * (S // 8)))))
    for j, b in enumerate(blocks):
        fc = S // (2 ** int(b["s"]) * den)
        if b["spec"] in ("c3", "c23"):
            out += [("31", ("blk", j, "31", fc)), ("22", ("blk", j, "22", 2 * fc)), ("13", ("blk", j, "13", fc))]
        else:
            out.append((b["spec"][1:3], ("blk", j, "w", fc)))
    _, allcodes = D.rowdef()
    for r, c in enumerate(allcodes[i] for i in rows_sel):
        for i, (coef, fam) in enumerate(row_uterm_coefs(c)):
            out.append((fam, ("row", r, i, coef * num[r] * (S // lam_den))))
    return out, S


# ---- the PartData cores, for the identity-module generator (gen_totals.py --parts step1) ----

def _comp(p, q):
    return tuple(p[q[j]] for j in range(4))


def _inv(p):
    r = [0] * 4
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def _swap(a, b):
    s = list(range(4)); s[a], s[b] = b, a
    return tuple(s)


PERMS, IDX = D.PERMS, D.IDX
INVI = [IDX[_inv(p)] for p in PERMS]
MULI = [[IDX[_comp(p, q)] for q in PERMS] for p in PERMS]
REMTAB = [[IDX[_comp(_swap(r, p[r]), p)] for r in range(4)] for p in PERMS]          # IdentityUnit.remTab
CONJTAB = [IDX[_comp(_comp(D.PI_ABB, p), _inv(D.PI_ABB))] for p in PERMS]            # IdentityUnit.conjTab
SW = IDX[_swap(0, 3)]                                                                # swIdx = 21


def _cyc(p):
    seen, c = set(), 0
    for i in range(4):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j); j = p[j]
    return c


CYC = [_cyc(p) for p in PERMS]


def dtab(j):
    return [[[1 if i == j else 0]] for i in range(24)]


def qtab(a):
    return [[[2 ** CYC[MULI[a][i]]]] for i in range(24)]


def row_uterms(code):
    """RowCode.uterms as [(coef, fam, (j0, j1, j2), a)]"""
    if code[0] == "trace":
        return [(2, "31", (0, 0, 0), 0)]
    if code[0] == "contrast":
        _, fam, r, w = code
        iv = tuple(INVI[x] for x in w[:3])
        return [(2, fam, iv, w[3]), (-(2 if PERMS[w[3]][r] == r else 1), fam, iv, REMTAB[w[3]][r])]
    w = code[1]
    iv = tuple(INVI[x] for x in w[:3])
    if code[0] == "3122":
        return [(2, "31", iv, w[3]), (-2, "22", iv, w[3])]
    return [(2, "22", iv, w[3]), (-2, "13", tuple(CONJTAB[x] for x in iv), CONJTAB[w[3]])]


def _key(t):
    return ("tab", hash(repr(t)))


def unit_part(fac, j, a, fam, name):
    tabs = [dtab(j[0]), dtab(j[1]), dtab(j[2]), qtab(a)]
    return dict(ks=[1, 1, 1, 1], X=[[1]], Bl=[[1]], Br=[[1]], fac=int(fac), tabs=tabs,
                mods=[_key(t) for t in tabs], fam=fam, name=name)


def _site_tables():
    import gen_sites as GS
    sites, _ = D.load_sites()
    qub = D.load_qubit()
    st = {T: [[[[l[0] if l else 0 for l in row] for row in GS.site_data(T, r, m)["N"][q]] for q in range(24)]
              for r, m in enumerate(mods)] for T, mods in sites.items()}
    sk = {T: [m["k"] for m in mods] for T, mods in sites.items()}
    qt = {T: [[[[int(v) for v in row] for row in M] for M in Q["F"]] for Q in v] for T, v in qub.items()}
    qk = {T: [Q["k"] for Q in v] for T, v in qub.items()}
    return st, sk, qt, qk


def _lean_maps():
    import re
    src = open(os.path.join(D.REPO_WE, "lean", "WernerEndpoint", "LayerC_Walled.lean")).read()
    out = {}
    for nm in ("mT3_31", "mT3_22", "mT3_13", "mT23_31", "mT23_22", "mT23_13"):
        m = re.search(r"def " + nm + r" : Fin 24 → Fin 24 :=\s*!\[([^\]]*)\]", src)
        out[nm] = [int(x) for x in m.group(1).split(",")]
    return out


def xint(blk, den):
    """IdentityBlock.xint: X0 DEN + delta_{pq} Delta_p 2^s  (= 2^s DEN X_b)"""
    X = [[int(v) * den for v in r] for r in blk["X0"]]
    for i, v in blk.get("delta", []):
        X[int(i)][int(i)] += int(v) << int(blk["s"])
    return X


def parts(fam):
    """The parts of `PsT0 fam`, in order, as gen_asm part dicts (ks, X, Bl, Br, fac, tabs, mods, fam, name).
    Their cores (ks, k, X, Bl, Br, fac, rhos) are meant to equal those of `PsT0 fam`, which the kernel checks."""
    blocks = C.load_blocks()
    rows_sel, lam, den = D.load_multipliers()
    num, lam_den = lam_num_den(lam)
    S = scale(blocks, lam_den, den)
    _, allcodes = D.rowdef()
    st, sk, qt, qk = _site_tables()
    maps = _lean_maps()
    out = []
    if fam == "31":
        for i, Sub in enumerate(SUBSETS3):
            k = len(Sub)
            j = tuple(SW if u in Sub else 0 for u in range(3))
            out.append(unit_part(-((-1) ** k * 2 ** (3 - k) * (S // 8)), j, SW, "31", f"obj{i}"))
    for bi, blk in enumerate(blocks):
        spec = blk["spec"]
        T = (3,) if spec == "c3" else (2, 3) if spec == "c23" else D.parse_cut(spec[3:])
        base = [st[T][r] for r in blk["rs"]] + [qt[T][blk["rq"]]]
        ks = [sk[T][r] for r in blk["rs"]] + [qk[T][blk["rq"]]]
        fc = S // (2 ** int(blk["s"]) * den)
        X = xint(blk, den)
        mk = lambda Bl, Br, f, tabs, nm: dict(ks=ks, X=X, Bl=[[int(v) for v in r] for r in Bl],
                                              Br=[[int(v) for v in r] for r in Br], fac=f, tabs=tabs,
                                              mods=[_key(t) for t in tabs], fam=fam, name=nm)
        if spec in ("c3", "c23"):
            tag = "mT3_" if spec == "c3" else "mT23_"
            m = maps[tag + fam]
            tabs = [[t[m[j]] for j in range(24)] for t in base]
            Bl, Br, f = {"31": (blk["Bu"], blk["Bu"], fc), "22": (blk["Bu"], blk["Bv"], 2 * fc),
                         "13": (blk["Bv"], blk["Bv"], fc)}[fam]
            out.append(mk(Bl, Br, f, tabs, f"b{bi}f{fam}"))
        elif spec[1:3] == fam:
            out.append(mk(blk["B"], blk["B"], fc, base, f"b{bi}"))
    for r, c in enumerate(allcodes[i] for i in rows_sel):
        for i, (coef, f, j, a) in enumerate(row_uterms(c)):
            if f == fam:
                out.append(unit_part(coef * num[r] * (S // lam_den), j, a, fam, f"r{r}t{i}"))
    return out


def family_parts():
    parts, S = all_parts()
    return {f: [d for g, d in parts if g == f] for f in FAMS}, S


# ---- the segment layout of `PsT0` (gen_assemble.py writes it, gen_identity_t0.py indexes into it) ----

GB, GR = 20, 30   # blocks per block segment (inside one PD group), rows per row segment


def block_chunks(groups):
    """the block segments: chunks of <= GB consecutive blocks inside each PD group (Gen/PD/groups.json)"""
    return [[g[i:i + GB] for i in range(0, len(g), GB)] for g in groups]


def segments(lf):
    """[(lean term of the segment for family lf (e.g. '.f22'), kind, data)] in `PsT0` order"""
    import json
    groups = json.load(open(os.path.join(D.HERE, "LayerDT0", "Gen", "PD", "groups.json")))
    rows_sel, _, _ = D.load_multipliers()
    out = [(f"segO idS {lf}", "O", None)]
    g = 0
    for cs in block_chunks(groups):
        for ch in cs:
            out.append((f"segB cuts DEN idS {lf} bzG{g}", "B", ch)); g += 1
    for r in range((len(rows_sel) + GR - 1) // GR):
        out.append((f"segR idS lamDen {lf} rzG{r}", "R", (r * GR, min(len(rows_sel), (r + 1) * GR))))
    return out


def part_segment(name, segs):
    """the segment index of a part (by its `parts()` name)"""
    if name.startswith("obj"):
        return 0
    if name.startswith("b"):
        j = int(name[1:].split("f")[0])
        return next(i for i, (_, k, d) in enumerate(segs) if k == "B" and j in d)
    r = int(name[1:].split("t")[0])
    return next(i for i, (_, k, d) in enumerate(segs) if k == "R" and d[0] <= r < d[1])


if __name__ == "__main__":
    fp, S = family_parts()
    print("S bits", S.bit_length(), {f: len(v) for f, v in fp.items()})
