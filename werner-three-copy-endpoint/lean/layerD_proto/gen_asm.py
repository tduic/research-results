#!/usr/bin/env python3
"""Generate an end-to-end (E') assembly instance (LayerDProto/R2Assembly.lean) for one family on a few parts.

For every part: its data (PartData), the fold data of the generators of K_b, the listing of K_b with a spanning
tree, and, per grid value d, the right-coset representatives, the coset decomposition data and the chunks of
`partD` with their values (PartAtD). Per grid value: one digit width beta for all parts.

Modes:
  values  family_at_d for every grid value: Sym_H D(t) = digit of the packed total at every grid point
          (the digits are unpacked by the kernel); a few digits are compared with Python's direct
          symmetrization sum_{h in H} D(h t) (an independent computation).
  zero    every part is paired with its negation (fac -> -fac); then family_at_d_zero at every grid value
          and family_zero: sum_t D(t) x_t = 0 for every x with layer C's invariances (a plumbing test of the
          whole chain with a functional that vanishes).
  rzero   as zero, through the reduced (literal-free) totals: every chunk claims only its digits at one grid
          position per H-orbit (`partDR`, R2RedKernel.lean), the orbit witnesses are kernel-checked (`orbOK`),
          and `family_at_d_zeroR` + `famZero_of_grid` give `LayerDT0.FamZero` for the parts.

Usage: python3 gen_asm.py NAME FAM MODE B:P,B:P,...[,obj]
"""
import json, math, os, sys
import numpy as np
import route2
import fold_data
from certdata import load_blocks, load_modules, lean_bigint, GEN
from gen_identity import rho_tables, coupled_maps, lean_mat, pack_signed, tuple_tensor, PERMS
import reduced
import recompress

MULI, INVI = route2.MULI, route2.INVI
BOSN = {"31": [0, 2, 6, 8, 12, 14], "13": [0, 2, 6, 8, 12, 14], "22": [0, 1, 6, 7]}
LEAN_FAM = {"31": ".f31", "13": ".f13", "22": ".f22"}
PERMS3 = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]


def cyc(a):
    p, seen, c = PERMS[a], set(), 0
    for i in range(4):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j); j = p[j]
    return c


def code(h):
    sg, e, g, g2 = h
    return (tuple(sg), bool(e), g, g2)


def mulK(p, q):
    (ps, pe, pg, pg2), (qs, qe, qg, qg2) = p, q
    comp = (qs[ps[0]], qs[ps[1]], qs[ps[2]])
    if pe:
        return (comp, pe != qe, MULI[pg][INVI[qg2]], MULI[INVI[qg]][pg2])
    return (comp, pe != qe, MULI[pg][qg], MULI[qg2][pg2])


def hcodes(bosL):
    return [(tuple(s), e, g, g2) for s in PERMS3 for e in (False, True) for g in bosL for g2 in bosL]


def lean_k(c):
    s, e, g, g2 = c
    return f"([{s[0]}, {s[1]}, {s[2]}], {'true' if e else 'false'}, {g}, {g2})"


def lean_list(xs):
    return "[" + ", ".join(xs) + "]"


def ent_max(M):
    return max([abs(int(v)) for r in M for v in r] + [0])


def row_sum_max(M):
    return max([sum(abs(int(v)) for v in r) for r in M] + [0])


def tr(M):
    return [list(c) for c in zip(*M)]


def word_part(coef, word):
    """the n = 1 part of a word (d = 5 on the sites, e = 2 on the qubit) with coefficient coef"""
    tabs = [[[[5 ** cyc(MULI[word[f]][s])]] for s in range(24)] for f in range(3)] + \
           [[[[2 ** cyc(MULI[word[3]][s])]] for s in range(24)]]
    return dict(ks=[1, 1, 1, 1], X=[[coef]], Bl=[[1]], Br=[[1]], fac=1, tabs=tabs,
                mods=[("word", tuple(word), u) for u in range(4)], name=f"w{word}")


def block_part(blocks, RHO, MAPS, bi, pi_):
    blk = blocks[bi]
    T, fs, parts = route2.block_parts(blk, RHO, MAPS)
    fam, Bl, Br, fac, mp = parts[pi_]
    tabs = [[f["rho"][m] for m in mp] if mp else f["rho"] for f in fs]
    mods = [(blk["spec"] if mp else "w", fam if mp else "", T, ("q", blk["rq"]) if u == 3 else blk["rs"][u])
            for u in range(4)]
    return dict(ks=[f["k"] for f in fs], X=[[int(v) for v in r] for r in blk["X0"]],
                Bl=[[int(v) for v in r] for r in Bl], Br=[[int(v) for v in r] for r in Br], fac=int(fac),
                tabs=tabs, mods=mods, fam=fam, name=f"b{bi}p{pi_}")


def prepare(part, fam):
    """K_b, its generators with fold data, the closure tree, the full tuple tensor"""
    ks, X, Bl, Br, tabs = part["ks"], part["X"], part["Bl"], part["Br"], part["tabs"]
    Ybase = np.array(Bl, dtype=object).dot(np.array(X, dtype=object)).dot(np.array(Br, dtype=object).T)
    Y = (Ybase * part["fac"]).tolist()
    F0 = np.array(tuple_tensor(Y, ks, tabs), dtype=object)
    K = route2.fold_subgroup(tabs, part["mods"], fam)
    Kb = [h for h in K if route2._invariant(F0, h)]
    gens = route2.generators(Kb, fam)
    folds = []
    n = math.prod(ks)
    for h in gens:
        fd = fold_data.kappa_fold(h, ks, tabs, Bl, Br, X)
        assert not isinstance(fd, str), (part["name"], h, fd)
        Cts = [tr(C) for C in fd["Cs"]]
        Xt = tr(X) if fd["tau"] else X
        dL = n * math.prod(ent_max(A) for A in fd["As"]) * (ent_max(Bl) + ent_max(Br))
        dG = n * math.prod(ent_max(C) for C in Cts) * (ent_max(Bl) + ent_max(Br))
        dB = (row_sum_max(Bl) + row_sum_max(Br)) * (ent_max(fd["Q"]) + ent_max(fd["R"]))
        dX = row_sum_max(tr(fd["Q"])) * ent_max(Xt) * row_sum_max(tr(fd["R"])) + abs(fd["al"]) * ent_max(X)
        fd["w"] = max((4 * dd).bit_length() for dd in (dL, dG, dB, dX)) + 1
        folds.append(fd)
    gcodes = [code(h) for h in gens]
    ident = ((0, 1, 2), False, 0, 0)
    Ks, tree, idx = [ident], [], {ident: 0}
    i = 0
    while i < len(Ks):
        for j, g in enumerate(gcodes):
            c = mulK(g, Ks[i])
            if c not in idx:
                idx[c] = len(Ks); Ks.append(c); tree.append((j, i))
        i += 1
    assert set(Ks) == {code(h) for h in Kb}, part["name"]
    kq = ks[3]
    tq = max(1, max(abs(int(v)) for m_ in tabs[3] for row in m_ for v in row))
    ymax = max(1, row_sum_max(Bl) * ent_max(X) * row_sum_max(Br))
    w = (4 * kq * kq * tq * ymax).bit_length() + 1
    tabmax = [max(ent_max(m) for m in tabs[f]) for f in range(4)]
    fbound = n * n * (row_sum_max(Bl) * ent_max(X) * row_sum_max(Br)) * math.prod(tabmax)
    return dict(part, Y=Y, F0=F0, Kb=Kb, folds=folds, Ks=Ks, tree=tree, w=w, bnd=2 ** (kq * w - 2) - 1,
                fbound=fbound)


def at_d(P, fam, d, S1d, budget=int(os.environ.get('ASM_BUDGET', '2000'))):
    """the representatives in group order, the coset data, the chunks (groups only; values later)"""
    reps = route2.right_coset_reps(P["Kb"], fam)
    ks = P["ks"]; n = math.prod(ks); n1 = n // ks[3]
    byq = {}
    for r in reps:
        byq.setdefault(route2.h_act_s(r, d), {}).setdefault(tuple(r[0]), []).append(r)
    items = [(m, sg, r) for m in sorted(byq) for sg in sorted(byq[m]) for r in byq[m][sg]]
    chunks, cur, used, seen = [], [], 0, set()
    for it in items:
        add = n1 * n1 + (n + n1 * n1 if it[0] not in seen else 0)
        if cur and used + add > budget:
            chunks.append(cur); cur, used, seen = [], 0, set()
            add = n1 * n1 + n + n1 * n1
        cur.append(it); used += add; seen.add(it[0])
    if cur:
        chunks.append(cur)
    reps_d = [code(it[2]) for ch in chunks for it in ch]
    H = hcodes(BOSN[fam])
    pos = {}
    for i, k_ in enumerate(P["Ks"]):
        for j, r in enumerate(reps_d):
            c = mulK(k_, r)
            assert c not in pos
            pos[c] = (i, j)
    assert len(pos) == len(H) and len(P["Ks"]) * len(reps_d) == len(H)
    dec = [pos[c] for c in H]
    return dict(reps=reps_d, dec=dec, chunks=chunks)


def groups_lean(ch):
    gl = {}
    for m, sg, r in ch:
        gl.setdefault(m, {}).setdefault(sg, []).append(r)
    return "[" + ", ".join(f"({m}, [" + ", ".join(
        f"([{sg[0]}, {sg[1]}, {sg[2]}], " + lean_list([lean_k(code(r)) for r in rs]) + ")"
        for sg, rs in sgs.items()) + "])" for m, sgs in gl.items()) + "]"


def hdr(name, imports, opens="LayerDProto WernerEndpoint"):
    return (f"-- GENERATED by layerD_proto/gen_asm.py {' '.join(sys.argv[1:])}. Do not edit.\n"
            + "".join(f"import {m}\n" for m in imports) +
            "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n\n"
            f"namespace LayerDProto.Gen.{name}\nopen {opens}\n"
            "set_option profiler true\nset_option profiler.threshold 200\n")
# (part modules import only the core kernel: Mathlib and layer C are needed by the family module only)


def chain(names):
    inner = "List.forall_mem_nil _"
    for nm in reversed(names):
        inner = f"List.forall_mem_cons.mpr ⟨{nm}, {inner}⟩"
    return inner


def write_reduced(name, fam, DC, S1, RG):
    """the reduced positions (imported by the part modules) and the orbit checks (imported by the family)"""
    bosN = "bosN22" if fam == "22" else "bosN31"
    pb = "".join(f"\n/-- reduced positions at t_q = {d}: one per H-orbit, {len(RG[d]['pos'])} of {RG[d]['N']} -/\n"
                 f"def pos{d} : List Nat := {lean_list([str(c) for c in RG[d]['pos']])}\n" for d in DC)
    with open(os.path.join(GEN, name + "Pos.lean"), "w") as fh:
        fh.write(hdr(name, ["LayerDProto.R2RedKernel"], "LayerDProto") + pb + f"\nend LayerDProto.Gen.{name}\n")
    orbs = [reduced.lean_orb(d, RG[d], bosN) for d in DC]
    ob = "".join(o for o, _ in orbs)
    with open(os.path.join(GEN, name + "Orb.lean"), "w") as fh:
        fh.write(hdr(name, [f"LayerDProto.Gen.{name}Pos"], "LayerDProto") + ob + f"\nend LayerDProto.Gen.{name}\n")


def main():
    name, fam, mode, spec = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    blocks = load_blocks()
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    parts = []
    for item in spec.split(","):
        if item == "obj":
            for coef, word in route2.objective()[fam]:
                parts.append(word_part(coef, word))
        else:
            bi, pi_ = (int(x) for x in item.split(":"))
            p = block_part(blocks, RHO, MAPS, bi, pi_)
            assert p["fam"] == fam, (item, p["fam"])
            parts.append(p)
    red = mode == "rzero"
    # coupled parts (B_l, B_r not of full column rank): full-rank re-presentation Y = L Z R^T (recompress.py);
    # the kernel checks it against the part as given (rel<i>) and the family module carries FamZero back (famZeroO)
    parts = recompress.recompress_all(parts)
    anyrc = any("orig" in p for p in parts)   # (only rzero ties the family back to the parts as given)
    if mode in ("zero", "rzero"):
        parts = [q for p in parts for q in (p, dict(p, fac=-p["fac"], name=p["name"] + "neg"))]
    parts = [prepare(p, fam) for p in parts]
    DC, S1 = route2.tree_grid(fam)
    lf = LEAN_FAM[fam]
    bosN = "bosN22" if fam == "22" else "bosN31"
    hb = {"31": "bosN31_f31", "13": "bosN31_f13", "22": "bosN22_f22"}[fam]
    hc = {"31": "bosN31_comp31", "13": "bosN31_comp13", "22": "bosN22_comp22"}[fam]
    hn = "hcodes22_nodup" if fam == "22" else "hcodes31_nodup"
    RG = reduced.reduced_grid(fam) if red else None
    # per grid value: representatives, one digit width, the chunk values
    ats, betas, vbs, totals = {}, {}, {}, {}
    for d in DC:
        ats[d] = [at_d(P, fam, d, S1[d]) for P in parts]
        fb = sum(abs(P["fac"]) * len(P["Ks"]) * len(a["reps"]) * P["fbound"] for P, a in zip(parts, ats[d]))
        betas[d] = (4 * fb).bit_length() + 1
        vbs[d] = fb if mode == "values" else 0
        total = np.zeros(24 * 24 * len(S1[d]), dtype=object)
        for P, a in zip(parts, ats[d]):
            a["L"] = []
            for ch in a["chunks"]:
                vals = route2.recipe_exact(P["Y"], P["ks"], P["tabs"], [it[2] for it in ch], fam)[d]
                total = total + len(P["Ks"]) * np.array(vals, dtype=object)
                if red:
                    assert all(4 * abs(int(vals[j])) < 2 ** betas[d] for j in RG[d]["pos"])
                    a["L"].append(pack_signed([int(vals[j]) for j in RG[d]["pos"]], betas[d]))
                else:
                    a["L"].append(pack_signed(list(vals), betas[d]))
        totals[d] = total
        if mode in ("zero", "rzero"):
            assert all(v == 0 for v in total)
    os.makedirs(GEN, exist_ok=True)
    mods = []
    partimp = ["LayerDProto.R2AsmKernel"]
    if red:
        write_reduced(name, fam, DC, S1, RG)
        partimp = [f"LayerDProto.Gen.{name}Pos"] + ([recompress.KERNEL_IMPORT] if anyrc else [])
        mods += [f"LayerDProto.Gen.{name}Pos", f"LayerDProto.Gen.{name}Orb"]
    # one module per part: its data, its checks and its chunk values
    for i, P in enumerate(parts):
        mn = f"{name}P{i}"
        mods.append(f"LayerDProto.Gen.{mn}")
        fds = []
        for fd in P["folds"]:
            fds.append("{ κ := " + lean_k(code(fd["h"])) + ", τ := " + ("true" if fd["tau"] else "false") +
                       ", As := " + lean_list([lean_mat(A) for A in fd["As"]]) +
                       ", Cs := " + lean_list([lean_mat(C) for C in fd["Cs"]]) +
                       ", als := " + lean_list([str(a) if a >= 0 else f"({a})" for a in fd["als"]]) +
                       f", Q := {lean_mat(fd['Q'])}, R := {lean_mat(fd['R'])}, w := {fd['w']} }}")
        rhos = lean_list([lean_list([lean_mat(m) for m in t]) for t in P["tabs"]])
        b = (f"\n-- part {i}: {P['name']} ks={P['ks']} |K_b|={len(P['Ks'])}\n"
             f"def P{i} : PartData :=\n  {{ ks := {P['ks']}, k := {len(P['X'])}, X := {lean_mat(P['X'])},\n"
             f"    Bl := {lean_mat(P['Bl'])}, Br := {lean_mat(P['Br'])}, fac := {lean_bigint(P['fac'])},\n"
             f"    rhos := {rhos},\n    w := {P['w']}, bnd := {P['bnd']},\n"
             f"    folds := {lean_list(fds)},\n    Ks := {lean_list([lean_k(c) for c in P['Ks']])},\n"
             f"    tree := {lean_list([f'({j}, {k_})' for j, k_ in P['tree']])} }}\n"
             f"theorem pstat{i} : partStaticOK {bosN} P{i} = true := by decide +kernel\n")
        b += recompress.lean_orig(i, P, lean_mat)
        for d in DC:
            a, beta, S1d = ats[d][i], betas[d], S1[d]
            chs = []
            for ci, ch in enumerate(a["chunks"]):
                gn = f"G{i}d{d}c{ci}"
                b += f"def {gn} : List MGroup := {groups_lean(ch)}\n"
                chs.append((gn, a["L"][ci]))
            if mode == "measure":
                # kernel cost only: force every chunk's packed value (compare with 0) without shipping it as a literal
                for ci, (gn, L) in enumerate(chs):
                    b += (f"theorem m{i}d{d}c{ci} : ((partD {beta} P{i}.w P{i}.bnd P{i}.ks P{i}.k P{i}.X P{i}.Bl P{i}.Br "
                          f"P{i}.fac P{i}.rhos {d} {S1d} {gn}).getD 0 % 2 != 2) = true := by decide +kernel\n")
                continue
            if red:
                b += (f"def Q{i}d{d} : PartAtD :=\n  {{ reps := {lean_list([lean_k(c) for c in a['reps']])},\n"
                      f"    dec := {lean_list([f'({x}, {y})' for x, y in a['dec']])},\n"
                      f"    chunks := {lean_list([f'({gn}, {lean_bigint(L)})' for gn, L in chs])} }}\n"
                      f"theorem at{i}d{d} : partAtDOK {bosN} P{i} Q{i}d{d} = true := by decide +kernel\n")
                for ci, (gn, L) in enumerate(chs):
                    b += (f"theorem ch{i}d{d}c{ci} : partDR {beta} P{i}.w P{i}.bnd P{i}.ks P{i}.k P{i}.X P{i}.Bl P{i}.Br "
                          f"P{i}.fac P{i}.rhos {d} {S1d} {gn} pos{d} = some {lean_bigint(L)} := by decide +kernel\n")
                b += (f"theorem hc{i}d{d} : ∀ c ∈ (P{i}, Q{i}d{d}).2.chunks, partDR {beta} (P{i}, Q{i}d{d}).1.w "
                      f"(P{i}, Q{i}d{d}).1.bnd (P{i}, Q{i}d{d}).1.ks (P{i}, Q{i}d{d}).1.k (P{i}, Q{i}d{d}).1.X "
                      f"(P{i}, Q{i}d{d}).1.Bl (P{i}, Q{i}d{d}).1.Br (P{i}, Q{i}d{d}).1.fac (P{i}, Q{i}d{d}).1.rhos "
                      f"{d} {S1d} c.1 pos{d} = some c.2 :=\n  {chain([f'ch{i}d{d}c{ci}' for ci in range(len(chs))])}\n")
                continue
            b += (f"def Q{i}d{d} : PartAtD :=\n  {{ reps := {lean_list([lean_k(c) for c in a['reps']])},\n"
                  f"    dec := {lean_list([f'({x}, {y})' for x, y in a['dec']])},\n"
                  f"    chunks := {lean_list([f'({gn}, {lean_bigint(L)})' for gn, L in chs])} }}\n"
                  f"theorem at{i}d{d} : partAtDOK {bosN} P{i} Q{i}d{d} = true := by decide +kernel\n")
            for ci, (gn, L) in enumerate(chs):
                b += (f"theorem ch{i}d{d}c{ci} : partD {beta} P{i}.w P{i}.bnd P{i}.ks P{i}.k P{i}.X P{i}.Bl P{i}.Br "
                      f"P{i}.fac P{i}.rhos {d} {S1d} {gn} = some {lean_bigint(L)} := by decide +kernel\n")
            b += (f"theorem hc{i}d{d} : ∀ c ∈ (P{i}, Q{i}d{d}).2.chunks, partD {beta} (P{i}, Q{i}d{d}).1.w "
                  f"(P{i}, Q{i}d{d}).1.bnd (P{i}, Q{i}d{d}).1.ks (P{i}, Q{i}d{d}).1.k (P{i}, Q{i}d{d}).1.X "
                  f"(P{i}, Q{i}d{d}).1.Bl (P{i}, Q{i}d{d}).1.Br (P{i}, Q{i}d{d}).1.fac (P{i}, Q{i}d{d}).1.rhos "
                  f"{d} {S1d} c.1 = some c.2 :=\n  {chain([f'ch{i}d{d}c{ci}' for ci in range(len(chs))])}\n")
        with open(os.path.join(GEN, mn + ".lean"), "w") as fh:
            fh.write(hdr(name, partimp, "LayerDProto") + b + f"\nend LayerDProto.Gen.{name}\n")
    if mode == "measure":
        json.dump(dict(parts=len(parts), reps={d: [len(a["reps"]) for a in ats[d]] for d in DC},
                       chunks={d: [len(a["chunks"]) for a in ats[d]] for d in DC}, betas=betas),
                  open(os.path.join(GEN, name + "_measure.json"), "w"))
        print("measure modules:", " ".join(mods))
        return
    # the family module
    n = len(parts)
    body = "".join(reduced.lean_orb(d, RG[d], bosN)[1] for d in DC) if red else ""
    kb = f"\ndef Ps : List PartData := {lean_list([f'P{i}' for i in range(n)])}\n"
    kb += f"theorem stat : ∀ P ∈ Ps, partStaticOK {bosN} P = true :=\n  {chain([f'pstat{i}' for i in range(n)])}\n"
    stats = []
    for d in DC:
        beta, S1d, vb = betas[d], S1[d], vbs[d]
        N = 24 * 24 * len(S1d)
        kb += f"\ndef Qs{d} : List PartAtD := {lean_list([f'Q{i}d{d}' for i in range(n)])}\n"
        kb += (f"theorem hD{d} : ∀ x ∈ Ps.zip Qs{d}, ∀ c ∈ x.2.chunks, {'partDR' if red else 'partD'} {beta} x.1.w x.1.bnd x.1.ks x.1.k "
                 f"x.1.X x.1.Bl x.1.Br x.1.fac x.1.rhos {d} {S1d} c.1{f' pos{d}' if red else ''} = some c.2 :=\n  "
                 f"{chain([f'hc{i}d{d}' for i in range(n)])}\n")
        kb += (f"theorem at{d} : ∀ x ∈ Ps.zip Qs{d}, partAtDOK {bosN} x.1 x.2 = true :=\n  "
                 f"{chain([f'at{i}d{d}' for i in range(n)])}\n"
                 f"theorem stat{d} : ∀ x ∈ Ps.zip Qs{d}, partStaticOK {bosN} x.1 = true :=\n"
                 f"  fun x hx => stat x.1 (List.of_mem_zip hx).1\n")
        vexpr = f"(List.replicate {N} 0)" if mode == "zero" else f"(unpkB {beta} 20 {N} (famTotal (Ps.zip Qs{d})))"
        if mode in ("zero", "rzero"):
            # the zero check does not build or pack the 24 * 24 * |S1| zero digits (familyZeroOK_spec)
            kb += f"theorem famz{d} : familyZeroOK {beta} (Ps.zip Qs{d}) = true := by decide +kernel\n"
        else:
            kb += (f"theorem fam{d} : familyAtDOK {beta} {S1d} (Ps.zip Qs{d}) {vexpr} {vb} = true := "
                   f"by decide +kernel\n")
        if red:
            body += (f"theorem zero{d} : ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < List.length {S1d}, ∑ p : PF {lf}, "
                     f"(Ps.map fun P => P.fac * FTP P (actF p.1 (gpt {S1d} {d} t0 t1 i2))).sum = 0 :=\n"
                     f"  family_at_d_zeroR (f := {lf}) {bosN} {hb} {hc} {hn} {beta} (by norm_num) {S1d} (by decide) {d} "
                     f"(by norm_num) pos{d} mask{d} posok{d} cov{d} Ps Qs{d} rfl stat{d} at{d} hD{d} famz{d}\n")
        elif mode == "zero":
            body += (f"theorem zero{d} : ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < List.length {S1d}, ∑ p : PF {lf}, "
                     f"(Ps.map fun P => P.fac * FTP P (actF p.1 (gpt {S1d} {d} t0 t1 i2))).sum = 0 :=\n"
                     f"  family_at_d_zero (f := {lf}) {bosN} {hb} {hc} {hn} {beta} {S1d} (by decide) {d} "
                     f"(by norm_num) Ps Qs{d} rfl {vb} stat{d} at{d} hD{d} (familyZeroOK_spec {beta} {S1d} _ famz{d})\n")
        else:
            body += (f"/-- `Sym_H D` at every grid point with `t_q = {d}` is the corresponding digit. -/\n"
                     f"theorem sym{d} : ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < List.length {S1d}, ∑ p : PF {lf}, "
                     f"((Ps.zip Qs{d}).map fun x => x.1.fac * FTP x.1 (actF p.1 (gpt {S1d} {d} t0 t1 i2))).sum = "
                     f"(unpkB {beta} 20 {N} (famTotal (Ps.zip Qs{d}))).getD ((t0 * 24 + t1) * List.length {S1d} + i2) 0 :=\n"
                     f"  family_at_d (f := {lf}) {bosN} {hb} {hc} {hn} {beta} {S1d} (by decide) {d} "
                     f"(by norm_num) (Ps.zip Qs{d}) _ {vb} stat{d} at{d} hD{d} fam{d}\n")
            Ffull = sum(P["F0"] for P in parts)
            H = route2.h_elements(fam)
            rng = np.random.default_rng(d)
            for k_ in range(3):
                t0, t1, i2 = int(rng.integers(24)), int(rng.integers(24)), int(rng.integers(len(S1d)))
                t = (t0, t1, S1d[i2], d)
                direct = 0
                for h in H:
                    u = route2.h_act(h, t)
                    direct += Ffull[((u[0] * 24 + u[1]) * 24 + u[2]) * 24 + u[3]]
                pos = (t0 * 24 + t1) * len(S1d) + i2
                assert direct == totals[d][pos], (d, t, direct, totals[d][pos])
                kb += (f"theorem digit{d}_{k_} : (unpkB {beta} 20 {N} (famTotal (Ps.zip Qs{d}))).getD "
                       f"(({t0} * 24 + {t1}) * List.length {S1d} + {i2}) 0 = {lean_bigint(int(direct))} := "
                       f"by decide +kernel\n")
                body += (f"/-- `Sym_H D` at the grid point {t}; Python's direct sum over `H` gives {int(direct)}. -/\n"
                         f"theorem sample{d}_{k_} : ∑ p : PF {lf}, (Ps.map fun P => P.fac * FTP P (actF p.1 "
                         f"(gpt {S1d} {d} {t0} {t1} {i2}))).sum = {lean_bigint(int(direct))} := by\n"
                         f"  have h := sym{d} {t0} (by norm_num) {t1} (by norm_num) {i2} (by decide)\n"
                         f"  rw [digit{d}_{k_}] at h\n"
                         f"  rw [← h]\n"
                         f"  exact Finset.sum_congr rfl fun p _ => (sum_zip_fst Ps Qs{d} (by decide) _).symm\n")
        stats.append(dict(d=d, beta=beta, reps=[len(a["reps"]) for a in ats[d]],
                          chunks=[len(a["chunks"]) for a in ats[d]]))
    tail = ""
    if mode in ("zero", "rzero"):
        dcF = "dc22" if fam == "22" else "dc31"
        s1F = "s1_22" if fam == "22" else "s1_31"
        bosF = "bos22L" if fam == "22" else "bos31L"
        memF = {"31": "bos31L_mem", "13": "bos13L_mem", "22": "bos22L_mem"}[fam]
        mF = "meetsR_22" if fam == "22" else "meetsR_31"
        cases = ""
        for d in DC:
            cases += (f"  · have e : ({s1F} {d}).map Fin.val = {S1[d]} := by decide\n"
                      f"    rw [e]\n"
                      f"    exact zero{d} t0 ht0 t1 ht1 i2 (by rw [← e, List.length_map]; exact hi2)\n")
        rc = " | ".join(["rfl"] * len(DC))
        body += (f"\ntheorem hz : ∀ dd ∈ {dcF}, ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < ({s1F} dd).length, ∑ p : PF {lf}, "
                 f"(Ps.map fun P => P.fac * FTP P (actF p.1 (gpt (({s1F} dd).map Fin.val) dd t0 t1 i2))).sum = 0 := by\n"
                 f"  intro dd hdd t0 ht0 t1 ht1 i2 hi2\n"
                 f"  simp only [{dcF}, List.mem_cons, List.not_mem_nil, or_false] at hdd\n"
                 f"  rcases hdd with {rc}\n" + cases)
        body += (f"\n/-- **The chain end to end**: `∑_t D(t) x_t = 0` for this (vanishing) family functional. -/\n"
                 f"theorem identity {{x : Tup (Fin 3) → ℝ}} (hs : ∀ π t, x (sitePermT π t) = x t)\n"
                 f"    (hi : ∀ t, x (invT t) = x t) (hl : ∀ g ∈ bos {lf}, ∀ t, x (lmulT g t) = x t)\n"
                 f"    (hr : ∀ g ∈ bos {lf}, ∀ t, x (rmulT g t) = x t) :\n"
                 f"    ∑ t, ((Ps.map fun P => P.fac * FTP P t).sum : ℂ) * (x t : ℂ) = 0 :=\n"
                 f"  family_zero Ps hs hi hl hr {bosF} {dcF} {s1F} {memF} {mF} hz\n")
        tail = "#print axioms identity\n"
        if red:
            body += (f"\n/-- The same conclusion as `LayerDT0.FamZero` (the interface of step 1). -/\n"
                     f"theorem famZero : LayerDT0.FamZero {lf} Ps :=\n"
                     f"  LayerDT0.famZero_of_grid Ps {bosF} {dcF} {s1F} {memF} {mF} hz\n")
            tail += "#print axioms famZero\n"
            if anyrc:
                body += recompress.lean_os(parts, lf)
                tail += "#print axioms famZeroO\n"
    else:
        tail = "".join(f"#print axioms sample{d}_0\n" for d in DC)
    with open(os.path.join(GEN, name + "K.lean"), "w") as fh:
        fh.write(hdr(name, mods, "LayerDProto") + kb + f"\nend LayerDProto.Gen.{name}\n")
    mods.append(f"LayerDProto.Gen.{name}K")
    with open(os.path.join(GEN, name + ".lean"), "w") as fh:
        fh.write(hdr(name, ["LayerDProto.R2Families"] + (["LayerDProto.R2Reduced", "LayerDT0.IdentityAsm"] if red else [])
                     + ([recompress.SOUND_IMPORT] if anyrc else [])
                     + mods) + body + "\n" + tail + f"\nend LayerDProto.Gen.{name}\n")
    with open(os.path.join(GEN, name + ".json"), "w") as fh:
        json.dump(dict(parts=len(parts), modules=mods, grid=stats), fh)
    print(json.dumps(stats))
    print(" ".join(m.replace("LayerDProto.", "") for m in mods + [f"LayerDProto.Gen.{name}"]))


if __name__ == "__main__":
    main()
