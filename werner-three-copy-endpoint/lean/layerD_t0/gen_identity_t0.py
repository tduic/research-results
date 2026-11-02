#!/usr/bin/env python3
"""Layer D (t = 0): the IdentityT0 part modules for step 1's parts `PsT0 f` (steps 4 and 5 of the README).

For one family f it reads step 1's parts (`identity_parts.parts(f)`: the cores of `PsT0 f`, in order) and writes,
under LayerDT0/Gen/Id/F<f>/ (git-ignored; Pos.lean and Orb.lean come from `gen_totals.py F --grid-only`):

  Tab.lean     every distinct table ρ of the family once (`tb<n>`); the parts' `rhos` refer to them, so the
               tables are not repeated per part (core Lean only)
  P<i>.lean    part i of `PsT0 f` (`P<i> : PartData`: X = step 1's xint, B_l, B_r, fac literal, rhos = table
               names, fold data, K, tree), per grid value the coset data `Q<i>d<d>` and `at<i>d<d>`; matrices are
               packed rows (`lean_matp`; the bases of a block part as the block code's own packed rows)
  P<i>f<g>.lean  fold generator checks (`pshape<i>`, `fo<i>_<g>`, `pstat<i>`)
  P<i>x<m>.lean  the chunk claims `ch<i>d<d>c<c> : partDR β … pos<d> = some L`, at most --per-module per module
  P<i>q.lean   block parts: `Q<i>`, the part as `PsT0` writes it (X = `xint DEN pdb<j>`, `XInt.lean`), and the
               core-Lean check `qr<i>` of Q<i> against P<i> (re-presented parts: against `O<i>`, the given
               presentation with a literal X)
  P<i>s<g>.lean, P<i>r.lean  re-presented parts: `rel<i> : ycoreOK w O<i> P<i>` (row slices `sl<i>_<g>` and the
               frame `fr<i>`, `RecompSlice.ycoreOK_of_slices`, for the largest parts)
  CE<m>.lean   `yr<i> : YRel (seg.getD m default) P<i>`, seg the part's segment of `PsT0` (IdentityParts.lean):
               block parts through Q<i> by `yRel_of_fields` (the kernel identifies the fields by unfolding), unit
               parts by `sameCoreOK`; and per segment `sr<s> : Forall₂ YRel seg PsS<s>` (`forall2_yRel_of_getD`)
  K.lean       hc / hD / at / stat chains and `famz<d> : familyZeroOK β (Ps.zip Qs<d>) = true` (only if the family
               total vanishes, i.e. if every part of the family was generated)
  Fam.lean     `famZero : FamZero .f<f> Ps` (family_at_d_zeroR, famZero_of_grid)
  Core.lean    `relT0 : Forall₂ YRel (PsT0 .f<f>) Ps` (`forall2_append` over the segments) and
               `famZeroT0 : FamZero .f<f> (PsT0 .f<f>)` (famZero_ycongr)

and replaces the family's part lines in identity_modules.txt (after its Pos and Orb lines).

Claims are exact: a part's functional is linear in Y = B_l X B_rᵀ, so with X = xint = X0 · DEN + diag(Δ) · 2^s the
claim is fac · (DEN · F(Y0) + 2^s · F(YΔ)), each computed by route2.recipe_exact at small size.  Nothing here is
trusted: the kernel re-checks every claim, and a wrong part list fails the core equality.

Usage:  python3 layerD_t0/gen_identity_t0.py FAM [--parts 0:100] [--budget UNITS] [--per-module N] [--skip-bad]
        [--list layerD_t0/identity_modules.txt] [--reuse]   (--reuse: prepared parts and claims from prep_cache.pkl)
"""
import argparse, json, math, os, pickle, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "layerD_proto"))
sys.set_int_max_str_digits(0)
import identity_parts as IP  # noqa: E402  (sets LAYERD_CERT to the v2 default before certdata is imported)
import numpy as np  # noqa: E402
import route2  # noqa: E402
import reduced  # noqa: E402
import gen_asm  # noqa: E402
import recompress  # noqa: E402
from certdata import lean_bigint, load_blocks, packed  # noqa: E402
from gen_identity import lean_mat, pack_signed  # noqa: E402

GEN = os.environ.get("LAYERD_T0_GEN", os.path.join(HERE, "LayerDT0", "Gen"))
LEAN_FAM = {"31": ".f31", "13": ".f13", "22": ".f22"}
BOSN = {"31": "bosN31", "13": "bosN31", "22": "bosN22"}
HB = {"31": "bosN31_f31", "13": "bosN31_f13", "22": "bosN22_f22"}
HC = {"31": "bosN31_comp31", "13": "bosN31_comp13", "22": "bosN22_comp22"}
HN = {"31": "hcodes31_nodup", "13": "hcodes31_nodup", "22": "hcodes22_nodup"}
DCF = {"31": "dc31", "13": "dc31", "22": "dc22"}
S1F = {"31": "s1_31", "13": "s1_31", "22": "s1_22"}
BOSF = {"31": "bos31L", "13": "bos31L", "22": "bos22L"}
MEMF = {"31": "bos31L_mem", "13": "bos13L_mem", "22": "bos22L_mem"}
MEETS = {"31": "meetsR_31", "13": "meetsR_31", "22": "meetsR_22"}


def lean_int(v):
    return f"(Int.ofNat 0x{v:x})" if v >= 0 else f"(-(Int.ofNat 0x{-v:x}))"


def lean_matp(M):
    """a list matrix as `[row codes].map (LayerDProto.unpk b n)` (balanced base-2^b rows): the elaborator takes
    minutes for a 74 x 74 matrix of 190-bit numerals written out (one `OfNat` instance problem per distinct literal),
    about a second packed; the kernel unpacks with Nat arithmetic"""
    if not M:
        return "[]"
    n = len(M[0])
    assert all(len(r) == n for r in M)
    b = max([abs(int(v)) for r in M for v in r] + [0]).bit_length() + 2
    rows = [sum(int(x) << (b * i) for i, x in enumerate(r)) for r in M]
    off = sum(1 << (b - 1) << (b * i) for i in range(n))
    for P, r in zip(rows, M):   # LayerDProto.unpk, digit by digit
        q = P + off
        assert all(((q >> (b * i)) % (1 << b)) - (1 << (b - 1)) == int(r[i]) for i in range(n))
    return f"(([{', '.join(lean_int(P) for P in rows)}] : List Int).map (LayerDProto.unpk {b} {n}))"


def block_pack(blk):
    """the packed bases of a block code exactly as gen_assemble.gen_block writes `bc<j>.Bp` / `.Bvp`"""
    parts = [blk["B"], []] if "B" in blk else [blk["Bu"], blk["Bv"]]
    rows = [[int(v) for v in r] for P in parts for r in P]
    ncol = len(rows[0])
    bb = max(abs(v) for r in rows for v in r).bit_length() + 2
    pk = lambda P: ("(([" + ", ".join(lean_bigint(packed(r, bb)) for r in P) +
                    f"] : List Int).map (LayerDProto.unpk {bb} {ncol}))") if P else "[]"
    return pk(parts[0]), pk(parts[1])


def part_bases(name, fam, blk):
    """(B_l, B_r) of a block part of PsT0 as the block code's packed rows (bpart: basisRows b b.Bp / b.Bvp)"""
    bp, bv = block_pack(blk)
    if "B" in blk:
        return bp, bp
    return {"31": (bp, bp), "22": (bp, bv), "13": (bv, bv)}[fam]


# estimated kernel memory of one ycoreOK declaration (GB above the core baseline; block 834: ~0, 835: 1.6,
# 838: 1.3, 917: 2.9 measured) and the slice budget
def rel_cost(P):
    o = P["orig"]
    k, R = len(o["X"]), len(o["Bl"])
    return 1.5e-4 * (R * k + k * k) * P["yw"] / 170


def rel_slices(P, budget=0.9):
    """(n, c): row slices of n rows (c of them) for the ycoreOK of a re-presented part; (0, 0): one declaration"""
    if rel_cost(P) <= 1.6:
        return 0, 0
    o = P["orig"]
    k, R = len(o["X"]), len(o["Bl"])
    rows_cost = 1.5e-4 * R * k * P["yw"] / 170
    c = max(2, math.ceil(rows_cost / budget))
    n = math.ceil(R / c)
    return n, math.ceil(R / n)


def lean_q(i, P, j, pdg, bases):
    """`Q<i>` (the part as `PsT0` writes it: X = `xint DEN pdb<j>`, the block code's packed bases) and the core check
    `qr<i>` against the generated part (word parts) or against `O<i>` (re-presented parts: the given presentation
    with X as a literal), for P<i>q.lean"""
    k0 = len(P.get("orig", P)["X"])
    t = (f"/-- part {i} as `PsT0` writes it (block {j}) -/\n"
         f"def Q{i} : PartData :=\n  {{ P{i} with\n    k := {k0}, X := LayerDT0.xint LayerDT0.DEN LayerDT0.pdb{j},\n"
         f"    Bl := {bases[0]},\n    Br := {bases[1]} }}\n")
    if "orig" in P:
        t += (f"/-- part {i} as given ({P['recomp']}): `Q{i}` with `X` computed; `P{i}` is its re-presentation -/\n"
              f"def O{i} : PartData := {{ Q{i} with X := {lean_matp(P['orig']['X'])} }}\n"
              f"theorem qr{i} : sameCoreOK Q{i} O{i} = true := by decide +kernel\n")
    else:
        t += f"theorem qr{i} : sameCoreOK Q{i} P{i} = true := by decide +kernel\n"
    # the part's Fbound, for the family check (FamBound.familyZeroOK_of_bounds; 136 s for block 496 alone)
    t += f"theorem fb{i} : Fbound P{i} ≤ {P['fbound']} := by decide +kernel\n"
    return t


def lean_rel(i, P):
    """`rel<i> : ycoreOK w O<i> P<i>` (one declaration), or its frame (the slices are in P<i>s<g>.lean)"""
    n, c = rel_slices(P)
    w = P["yw"]
    if not n:
        return f"theorem rel{i} : ycoreOK {w} O{i} P{i} = true := by decide +kernel\n", []
    sls = [f"theorem sl{i}_{g} : (ySl {w} O{i} ({g} * {n}) {n} == ySl {w} P{i} ({g} * {n}) {n}) = true := by decide +kernel\n"
           for g in range(c)]
    cases = "".join(f"\n    | {g}, _ => sl{i}_{g}" for g in range(c))
    t = (f"theorem fr{i} : yframeOK {w} O{i} P{i} = true := by decide +kernel\n"
         f"theorem rel{i} : ycoreOK {w} O{i} P{i} = true :=\n"
         f"  ycoreOK_of_slices {w} O{i} P{i} {n} {c} (by decide) fr{i} (by decide)\n"
         f"    fun g hg => match g, hg with{cases}\n    | _ + {c}, h => absurd h (by omega)\n")
    return t, sls


def lean_yrel(i, P, src, block):
    """`yr<i> : YRel src P<i>`: a block part through `Q<i>` (`yRel_of_fields`: the kernel identifies the fields by
    unfolding, nothing is computed in this Mathlib module), then `qr<i>` (and `rel<i>` for a re-presented part); a
    unit part by `sameCoreOK` against P<i> directly"""
    if not block:
        return f"theorem yr{i} : LayerDT0.YRel {src} P{i} :=\n  LayerDT0.yRel_of_sameCoreOK (by decide +kernel)\n"
    tail = (f"(LayerDT0.yRel_trans (LayerDT0.yRel_of_sameCoreOK qr{i}) (LayerDT0.yRel_of_ycoreOK rel{i}))"
            if "orig" in P else f"(LayerDT0.yRel_of_sameCoreOK qr{i})")
    return (f"theorem yr{i} : LayerDT0.YRel {src} P{i} :=\n  LayerDT0.yRel_trans "
            f"(LayerDT0.yRel_of_fields (Q := Q{i}) (by decide +kernel) rfl rfl rfl)\n    {tail}\n")


def no_code(out):
    """every generated `def` is `noncomputable`: the kernel checks never run compiled code, and the C output of a part
    module was 1-1.8 MB (2.8 GB for the whole identity); Pos / Orb (gen_totals.py) are left as they are"""
    import re
    for f in os.listdir(out):
        if f.endswith(".lean") and f not in ("Pos.lean", "Orb.lean"):
            p = os.path.join(out, f)
            t = open(p).read()
            u = re.sub(r"^def ", "noncomputable def ", t, flags=re.M)
            if u != t:
                open(p, "w").write(u)



def stable_cmd(argv):
    """the generator arguments for the GENERATED header, without --list PATH and --reuse (which do not change
    the generated Lean), so regenerating does not change unchanged files and Lake keeps their builds"""
    out, skip = [], False
    for x in argv:
        if skip:
            skip = False
            continue
        if x == "--list":
            skip = True
            continue
        if x.startswith("--list=") or x == "--reuse":
            continue
        out.append(x)
    return " ".join(out)

def hdr(ns, imports, cmd, opens="LayerDProto WernerEndpoint"):
    return (f"-- GENERATED by layerD_t0/gen_identity_t0.py {cmd}. Do not edit.\n"
            + "".join(f"import {m}\n" for m in imports) +
            "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n\n"
            f"namespace {ns}\nopen {opens}\n")


def lin_parts(fam, raw, blocks, den):
    """for every part: [(mult, X_small)] with X = sum mult X_small (block parts: X0 and diag(Delta))"""
    out = []
    for p in raw:
        nm = p["name"]
        if nm.startswith("b"):
            bi = int(nm[1:].split("f")[0])
            blk = blocks[bi]
            X0 = [[int(v) for v in r] for r in blk["X0"]]
            k = len(X0)
            Xd = [[0] * k for _ in range(k)]
            for i, v in blk.get("delta", []):
                Xd[int(i)][int(i)] = int(v)
            terms = [(den, X0)]
            if any(any(r) for r in Xd):
                terms.append((2 ** int(blk["s"]), Xd))
            assert [[sum(m * X[a][b] for m, X in terms) for b in range(k)] for a in range(k)] == p["X"], nm
            out.append(terms)
        else:
            out.append([(1, [[1]])])
    return out


def claims(P, terms, ks, tabs, reps, fam, d):
    O = P.get("orig", P)   # claims depend only on Y: use the given presentation (B_l, B_r of PsT0)
    Bl = np.array(O["Bl"], dtype=object); Br = np.array(O["Br"], dtype=object)
    tot = None
    for m, Xs in terms:
        Y = Bl.dot(np.array(Xs, dtype=object)).dot(Br.T).tolist()
        v = np.array(route2.recipe_exact(Y, ks, tabs, reps, fam)[d], dtype=object) * m
        tot = v if tot is None else tot + v
    return tot * P["fac"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fam", choices=["31", "22", "13"])
    ap.add_argument("--parts", default="all", help="a:b, a range of part indices to (re)generate")
    ap.add_argument("--budget", type=int, default=6000, help="partD units per chunk")
    ap.add_argument("--per-module", type=int, default=8, help="chunk claims per module")
    ap.add_argument("--rep-budget", type=int, default=500, help="coset representatives per claim module (at most)")
    ap.add_argument("--ce-per-module", type=int, default=10, help="core relations yr<i> per module (at most)")
    ap.add_argument("--fold-group", type=int, default=7, help="fold generator checks per module")
    ap.add_argument("--skip-bad", action="store_true", help="skip parts whose fold data cannot be built")
    ap.add_argument("--list", default=os.path.join(HERE, "identity_modules.txt"))
    ap.add_argument("--reuse", action="store_true", help="reuse prepared parts and claims from prep_cache.pkl")
    ap.add_argument("--test", action="store_true", help="prepare only the --parts range (widths not final; no list update)")
    a = ap.parse_args()
    fam, cmd = a.fam, stable_cmd(sys.argv[1:])
    t0 = time.time()
    blocks = load_blocks()
    _, _, den = IP.D.load_multipliers()
    pdgrp = {j: c for c, g in enumerate(json.load(open(os.path.join(GEN, "PD", "groups.json")))) for j in g}
    raw = IP.parts(fam)
    n = len(raw)
    lins = lin_parts(fam, raw, blocks, den)
    lo, hi = (0, n) if a.parts == "all" else tuple(int(x) for x in a.parts.split(":"))
    F = f"F{fam}"
    ns = mp = f"LayerDT0.Gen.Id.{F}"
    out = os.path.join(GEN, "Id", F)
    assert os.path.exists(os.path.join(out, "Orb.lean")), "run gen_totals.py FAM --grid-only first"
    DC, S1 = route2.tree_grid(fam)
    RG = reduced.reduced_grid(fam)
    # shared tables (all parts of the family, so that indices are stable across --parts runs)
    tabidx, tabsrc = {}, []
    for p in raw:
        for t in p["tabs"]:
            key = repr(t)
            if key not in tabidx:
                tabidx[key] = len(tabsrc)
                tabsrc.append(f"def tb{len(tabsrc)} : List (List (List Int)) := {gen_asm.lean_list([lean_mat(m) for m in t])}\n")
    with open(os.path.join(out, "Tab.lean"), "w") as fh:
        fh.write(hdr(ns, ["LayerDProto.R2AsmKernel"], f"{fam} (tables)", "LayerDProto") + "".join(tabsrc) + f"\nend {ns}\n")
    # parts: fold data, chunks (betas need every part, so prepare all, cache in summary)
    stfile = os.path.join(out, "parts_state.json")
    state = json.load(open(stfile)) if os.path.exists(stfile) else {}
    prepared, failed = {}, []
    cfile = os.path.join(out, "prep_cache.pkl")   # prepared parts and claim digits (--reuse), git-ignored
    cache = pickle.load(open(cfile, "rb")) if a.reuse and os.path.exists(cfile) else {"prep": {}, "dig": {}}
    for i, p in enumerate(raw):
        if a.test and not lo <= i < hi:
            continue
        if p["name"] in cache["prep"]:
            prepared[i] = cache["prep"][p["name"]]
            continue
        if recompress.needs_recompress(p):   # full-rank re-presentation of a coupled part (claims unchanged)
            p = recompress.recompress_part(p)
        q = dict(p, fac=1)
        try:
            P = gen_asm.prepare(q, fam)
        except (ValueError, AssertionError) as ex:
            if not a.skip_bad:
                raise
            failed.append((i, p["name"], str(ex)[:80]))
            continue
        P.pop("F0")
        P["fac"] = p["fac"]
        prepared[i] = P
        cache["prep"][p["name"]] = P
        if i % 50 == 0:
            print(f"prepared {i}/{n} ({time.time() - t0:.0f} s)", flush=True)
    ats = {d: {i: gen_asm.at_d(P, fam, d, S1[d], a.budget) for i, P in prepared.items()} for d in DC}
    betas = {}
    for d in DC:
        fb = sum(abs(P["fac"]) * len(P["Ks"]) * len(ats[d][i]["reps"]) * P["fbound"] for i, P in prepared.items())
        betas[d] = (4 * fb).bit_length() + 1
    totals = {d: np.zeros(len(RG[d]["pos"]), dtype=object) for d in DC}
    pmods = {}
    for i, P in prepared.items():
        fds = []
        for fd in P["folds"]:
            fds.append("{ κ := " + gen_asm.lean_k(gen_asm.code(fd["h"])) + ", τ := " + ("true" if fd["tau"] else "false") +
                       ", As := " + gen_asm.lean_list([lean_mat(A) for A in fd["As"]]) +
                       ", Cs := " + gen_asm.lean_list([lean_mat(C) for C in fd["Cs"]]) +
                       ", als := " + gen_asm.lean_list([str(x) if x >= 0 else f"({x})" for x in fd["als"]]) +
                       f", Q := {lean_mat(fd['Q'])}, R := {lean_mat(fd['R'])}, w := {fd['w']} }}")
        rhos = gen_asm.lean_list([f"tb{tabidx[repr(t)]}" for t in P["tabs"]])
        isb = P["name"].startswith("b")
        if isb:
            bj = int(P["name"][1:].split("f")[0])
            bases = part_bases(P["name"], fam, blocks[bj])
        pbl, pbr = (bases if isb and "orig" not in P else (lean_matp(P["Bl"]), lean_matp(P["Br"])))
        b = (f"\n-- part {i}: {P['name']} ks={P['ks']} |K_b|={len(P['Ks'])}\n"
             + "".join(f"def FD{i}_{g} : FoldDatum := {fd}\n" for g, fd in enumerate(fds)) +
             f"def P{i} : PartData :=\n  {{ ks := {P['ks']}, k := {len(P['X'])}, X := {lean_matp(P['X'])},\n"
             f"    Bl := {pbl}, Br := {pbr}, fac := {lean_bigint(P['fac'])},\n"
             f"    rhos := {rhos},\n    w := {P['w']}, bnd := {P['bnd']},\n"
             f"    folds := {gen_asm.lean_list([f'FD{i}_{g}' for g in range(len(fds))])},\n"
             f"    Ks := {gen_asm.lean_list([gen_asm.lean_k(c) for c in P['Ks']])},\n"
             f"    tree := {gen_asm.lean_list([f'({j}, {k_})' for j, k_ in P['tree']])} }}\n")
        shape = (f"theorem pshape{i} : (P{i}.ks.length == 4 && P{i}.Bl.all (·.length == P{i}.k) && "
                 f"P{i}.Br.all (·.length == P{i}.k) && closureOK {BOSN[fam]} (P{i}.folds.map (·.κ)) P{i}.Ks P{i}.tree) = true "
                 ":= by decide +kernel\n")
        # fold generator checks in groups of --fold-group per module (one declaration each: ~0.5 GB per generator
        # in one declaration, ~2.4 GB for 7 separate declarations in one module); shape first, pstat last
        thms = [shape] + [f"theorem fo{i}_{g} : foldDatumOK P{i} FD{i}_{g} = true := by decide +kernel\n" for g in range(len(fds))]
        thms.append(f"theorem pstat{i} : partStaticOK {BOSN[fam]} P{i} = true :=\n"
                    f"  LayerDT0.partStaticOK_of {BOSN[fam]} P{i} pshape{i}\n"
                    f"    ({gen_asm.chain([f'fo{i}_{h}' for h in range(len(fds))])})\n")
        fold_mods = []
        # one generator per module for the large parts (block 496, k = 58: 4 generators in one module, > 3.6 GB)
        fg = 1 if len(P["X"]) >= 25 else a.fold_group
        grp = [thms[0:fg + 1]] + [thms[m:m + fg] for m in range(fg + 1, len(thms), fg)]
        for g, th in enumerate(grp):
            imp = [f"{mp}.P{i}" if g == 0 else f"{mp}.P{i}f{g - 1}", "LayerDT0.StatSplit"]
            fold_mods.append((f"P{i}f{g}", hdr(ns, imp, cmd, "LayerDProto") + "".join(th) + f"\nend {ns}\n"))
        chs_all = []
        for d in DC:
            at, beta, pos = ats[d][i], betas[d], RG[d]["pos"]
            names = []
            for ci, ch in enumerate(at["chunks"]):
                gn = f"G{i}d{d}c{ci}"
                b += f"def {gn} : List MGroup := {gen_asm.groups_lean(ch)}\n"
                ck = (P["name"], d, ci, a.budget)
                if ck not in cache["dig"]:
                    vals = claims(P, lins[i], P["ks"], P["tabs"], [it[2] for it in ch], fam, d)
                    cache["dig"][ck] = [int(vals[j]) for j in pos]
                dig = cache["dig"][ck]
                assert all(4 * abs(v) < 2 ** beta for v in dig)
                totals[d] = totals[d] + len(P["Ks"]) * np.array(dig, dtype=object)
                names.append((gn, lean_bigint(pack_signed(dig, beta))))
            b += (f"def Q{i}d{d} : PartAtD :=\n  {{ reps := {gen_asm.lean_list([gen_asm.lean_k(c) for c in at['reps']])},\n"
                  f"    dec := {gen_asm.lean_list([f'({x}, {y})' for x, y in at['dec']])},\n"
                  f"    chunks := {gen_asm.lean_list([f'({gn}, {lit})' for gn, lit in names])} }}\n"
                  f"theorem at{i}d{d} : partAtDOK {BOSN[fam]} P{i} Q{i}d{d} = true := by decide +kernel\n")
            chs_all += [(d, ci, gn, lit, len(at["chunks"][ci])) for ci, (gn, lit) in enumerate(names)]
        nsl = rel_slices(P)[1] if "orig" in P else 0
        mods = ([f"{mp}.P{i}"] + ([f"{mp}.P{i}q"] if isb else []) + [f"{mp}.P{i}s{g}" for g in range(nsl)] +
                ([f"{mp}.P{i}r"] if "orig" in P else []) + [f"{mp}.{nm}" for nm, _ in fold_mods])
        if lo <= i < hi:
            with open(os.path.join(out, f"P{i}.lean"), "w") as fh:
                fh.write(hdr(ns, [f"{mp}.Pos", f"{mp}.Tab"], cmd, "LayerDProto") + b + f"\nend {ns}\n")
            if isb:   # Q<i> (and O<i>) with the core check qr<i>; rel<i> (and its slices) in modules of their own
                with open(os.path.join(out, f"P{i}q.lean"), "w") as fh:
                    fh.write(hdr(ns, [f"{mp}.P{i}", recompress.KERNEL_IMPORT, "LayerDT0.XInt", f"LayerDT0.Gen.PD.G{pdgrp[bj]}"],
                                 cmd, "LayerDProto") + lean_q(i, P, bj, pdgrp[bj], bases) + f"\nend {ns}\n")
            if "orig" in P:
                rt, sls = lean_rel(i, P)
                for g, st in enumerate(sls):
                    with open(os.path.join(out, f"P{i}s{g}.lean"), "w") as fh:
                        fh.write(hdr(ns, [f"{mp}.P{i}q", "LayerDT0.RecompSlice"], cmd, "LayerDProto LayerDT0") + st + f"\nend {ns}\n")
                with open(os.path.join(out, f"P{i}r.lean"), "w") as fh:
                    fh.write(hdr(ns, [f"{mp}.P{i}q", "LayerDT0.RecompSlice"] + [f"{mp}.P{i}s{g}" for g in range(len(sls))],
                                 cmd, "LayerDProto LayerDT0") + rt + f"\nend {ns}\n")
            for nm, txt in fold_mods:
                with open(os.path.join(out, nm + ".lean"), "w") as fh:
                    fh.write(txt)
        # fewer claims per module for the largest parts (block 496, k = 58, xint X: 8 claims in one module passed
        # 3 GB after 22 min)
        ks_ = P["ks"]
        upr = (ks_[0] * ks_[1] * ks_[2]) ** 2 * ks_[3]
        pm = 1 if len(P["X"]) >= 40 else 2 if (len(P["X"]) >= 25 or upr >= 10000) else a.per_module
        # at most pm claims per module, and at most --rep-budget coset representatives per module unless a single
        # claim has more (two 432-representative claims of the ks = [1,1,1,1] parts in one module peak at 5.6-6.3 GB,
        # over a 6 GB process limit); parts whose modules all fit keep exactly the pm-claim grouping
        xgroups, cur, nr = [], [], 0
        for c in chs_all:
            if cur and (len(cur) == pm or nr + c[4] > a.rep_budget):
                xgroups.append(cur); cur, nr = [], 0
            cur.append(c); nr += c[4]
        if cur:
            xgroups.append(cur)
        for x, grp_x in enumerate(xgroups):
            body = "".join(f"theorem ch{i}d{d}c{ci} : partDR {betas[d]} P{i}.w P{i}.bnd P{i}.ks P{i}.k P{i}.X P{i}.Bl "
                           f"P{i}.Br P{i}.fac P{i}.rhos {d} {S1[d]} {gn} pos{d} = some {lit} := by decide +kernel\n"
                           for d, ci, gn, lit, _ in grp_x)
            if lo <= i < hi:
                with open(os.path.join(out, f"P{i}x{x}.lean"), "w") as fh:
                    fh.write(hdr(ns, [f"{mp}.P{i}"], cmd, "LayerDProto") + body + f"\nend {ns}\n")
            mods.append(f"{mp}.P{i}x{x}")
        pmods[i] = (mods, {d: [ci for dd, ci, _, _, _ in chs_all if dd == d] for d in DC})
        state[str(i)] = dict(name=P["name"], ks=P["ks"], K=len(P["Ks"]),
                             reps={d: len(ats[d][i]["reps"]) for d in DC}, chunks={d: len(ats[d][i]["chunks"]) for d in DC},
                             modules=mods)
    zero = not failed and len(prepared) == n and all(all(v == 0 for v in totals[d]) for d in DC)
    later = []
    # K and Fam (only when every part is there; the chains need all of them)
    if len(prepared) == n and not failed:
        allm = [m for i in range(n) for m in pmods[i][0]]
        kb = f"\ndef Ps : List PartData := {gen_asm.lean_list([f'P{i}' for i in range(n)])}\n"
        kb += f"def FBs : List Nat := {gen_asm.lean_list([str(prepared[i]['fbound']) for i in range(n)])}\n"
        kb += f"theorem stat : ∀ P ∈ Ps, partStaticOK {BOSN[fam]} P = true :=\n  {gen_asm.chain([f'pstat{i}' for i in range(n)])}\n"
        body = "".join(reduced.lean_orb(d, RG[d], BOSN[fam])[1] for d in DC)  # cov<d>, by witSlice_cover
        for d in DC:
            beta = betas[d]
            for i in range(n):
                kb += (f"theorem hc{i}d{d} : ∀ c ∈ (P{i}, Q{i}d{d}).2.chunks, partDR {beta} (P{i}, Q{i}d{d}).1.w "
                       f"(P{i}, Q{i}d{d}).1.bnd (P{i}, Q{i}d{d}).1.ks (P{i}, Q{i}d{d}).1.k (P{i}, Q{i}d{d}).1.X "
                       f"(P{i}, Q{i}d{d}).1.Bl (P{i}, Q{i}d{d}).1.Br (P{i}, Q{i}d{d}).1.fac (P{i}, Q{i}d{d}).1.rhos "
                       f"{d} {S1[d]} c.1 pos{d} = some c.2 :=\n  "
                       f"{gen_asm.chain([f'ch{i}d{d}c{ci}' for ci in pmods[i][1][d]])}\n")
            kb += (f"\ndef Qs{d} : List PartAtD := {gen_asm.lean_list([f'Q{i}d{d}' for i in range(n)])}\n"
                   f"theorem hD{d} : ∀ x ∈ Ps.zip Qs{d}, ∀ c ∈ x.2.chunks, partDR {beta} x.1.w x.1.bnd x.1.ks x.1.k "
                   f"x.1.X x.1.Bl x.1.Br x.1.fac x.1.rhos {d} {S1[d]} c.1 pos{d} = some c.2 :=\n  "
                   f"{gen_asm.chain([f'hc{i}d{d}' for i in range(n)])}\n"
                   f"theorem at{d} : ∀ x ∈ Ps.zip Qs{d}, partAtDOK {BOSN[fam]} x.1 x.2 = true :=\n  "
                   f"{gen_asm.chain([f'at{i}d{d}' for i in range(n)])}\n"
                   f"theorem stat{d} : ∀ x ∈ Ps.zip Qs{d}, partStaticOK {BOSN[fam]} x.1 = true :=\n"
                   f"  fun x hx => stat x.1 (List.of_mem_zip hx).1\n")
            if zero:
                fbl = "LayerDT0.FbLe.nil"
                for i in reversed(range(n)):
                    h = f"fb{i}" if prepared[i]["name"].startswith("b") else "(by decide +kernel)"
                    fbl = f"(LayerDT0.FbLe.cons {h} {fbl})"
                kb += (f"theorem fbs{d} : LayerDT0.FbLe (Ps.zip Qs{d}) FBs :=\n  {fbl}\n"
                       f"theorem famz{d} : familyZeroOK {beta} (Ps.zip Qs{d}) = true :=\n"
                       f"  LayerDT0.familyZeroOK_of_bounds {beta} (Ps.zip Qs{d}) FBs fbs{d} (by decide +kernel)\n")
                body += (f"theorem zero{d} : ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < List.length {S1[d]}, ∑ p : PF {LEAN_FAM[fam]}, "
                         f"(Ps.map fun P => P.fac * FTP P (actF p.1 (gpt {S1[d]} {d} t0 t1 i2))).sum = 0 :=\n"
                         f"  family_at_d_zeroR (f := {LEAN_FAM[fam]}) {BOSN[fam]} {HB[fam]} {HC[fam]} {HN[fam]} {beta} "
                         f"(by norm_num) {S1[d]} (by decide) {d} (by norm_num) pos{d} mask{d} posok{d} cov{d} Ps Qs{d} rfl "
                         f"stat{d} at{d} hD{d} famz{d}\n")
        with open(os.path.join(out, "K.lean"), "w") as fh:
            fh.write(hdr(ns, [f"{mp}.Orb", "LayerDT0.FamBound"] + allm, cmd, "LayerDProto") + kb + f"\nend {ns}\n")
        later.append(f"{mp}.K")
        if zero:
            cases = "".join(f"  · have e : ({S1F[fam]} {d}).map Fin.val = {S1[d]} := by decide\n    rw [e]\n"
                            f"    exact zero{d} t0 ht0 t1 ht1 i2 (by rw [← e, List.length_map]; exact hi2)\n" for d in DC)
            body += (f"\ntheorem hz : ∀ dd ∈ {DCF[fam]}, ∀ t0 < 24, ∀ t1 < 24, ∀ i2 < ({S1F[fam]} dd).length, "
                     f"∑ p : PF {LEAN_FAM[fam]}, (Ps.map fun P => P.fac * FTP P (actF p.1 (gpt (({S1F[fam]} dd).map Fin.val) "
                     f"dd t0 t1 i2))).sum = 0 := by\n  intro dd hdd t0 ht0 t1 ht1 i2 hi2\n"
                     f"  simp only [{DCF[fam]}, List.mem_cons, List.not_mem_nil, or_false] at hdd\n"
                     f"  rcases hdd with {' | '.join(['rfl'] * len(DC))}\n" + cases)
            body += (f"\n/-- **The family's route-2′ zero** for the generated list `Ps`. -/\n"
                     f"theorem famZero : LayerDT0.FamZero {LEAN_FAM[fam]} Ps :=\n"
                     f"  LayerDT0.famZero_of_grid Ps {BOSF[fam]} {DCF[fam]} {S1F[fam]} {MEMF[fam]} {MEETS[fam]} hz\n")
            with open(os.path.join(out, "Fam.lean"), "w") as fh:
                fh.write(hdr(ns, ["LayerDProto.R2Families", "LayerDProto.R2Reduced", "LayerDT0.IdentityAsm", f"{mp}.K"], cmd)
                         + body + f"\nend {ns}\n")
            later.append(f"{mp}.Fam")
    # core relations, segment by segment: PsT0 f is a concatenation of short segments (IdentityParts.lean,
    # identity_parts.segments), and part i is compared with element m of its segment (no walk over the family list)
    lf = LEAN_FAM[fam]
    segs = IP.segments(lf)
    pseg = [IP.part_segment(p["name"], segs) for p in raw]
    assert pseg == sorted(pseg), "parts out of segment order"
    segpos, cnt = {}, {}
    for i, sg in enumerate(pseg):
        segpos[i] = (sg, cnt.get(sg, 0))
        cnt[sg] = cnt.get(sg, 0) + 1
    # modules follow the segments (a segment is split only if it has more than --ce-per-module parts), so that a
    # segment relation sr<s> imports at most the other modules of its own segment
    groups_ce, cur = [], []
    for sg in range(len(segs)):
        ids = [i for i in range(n) if pseg[i] == sg and i in prepared]
        if cur and len(cur) + len(ids) > a.ce_per_module:
            groups_ce.append(cur); cur = []
        while len(ids) > a.ce_per_module:
            groups_ce.append(ids[:a.ce_per_module]); ids = ids[a.ce_per_module:]
        cur += ids
    if cur:
        groups_ce.append(cur)
    modof = {i: m for m, g in enumerate(groups_ce) for i in g}
    # segment relation sr<s> goes to the module of the segment's last part (empty segments: the previous one's)
    full = len(prepared) == n and not failed
    sr_mod, last = {}, 0
    for sg in range(len(segs)):
        ids = [i for i in range(n) if pseg[i] == sg]
        if ids:
            last = modof.get(ids[-1], -1)
        sr_mod[sg] = last
    cem = []
    for m, idx in enumerate(groups_ce):
        body = "".join(lean_yrel(i, prepared[i], f"(({segs[segpos[i][0]][0]}).getD {segpos[i][1]} default)",
                                 prepared[i]["name"].startswith("b")) for i in idx)
        imps = [f"{mp}.P{i}r" if "orig" in prepared[i] else f"{mp}.P{i}q" if prepared[i]["name"].startswith("b")
                else f"{mp}.P{i}" for i in idx]
        for sg in range(len(segs)):
            if not full or sr_mod[sg] != m:
                continue
            ids = [i for i in range(n) if pseg[i] == sg]
            imps += sorted({f"{mp}.CE{modof[i]}" for i in ids if modof[i] != m})
            term = segs[sg][0]
            body += (f"def PsS{sg} : List PartData := {gen_asm.lean_list([f'P{i}' for i in ids])}\n"
                     f"theorem sl{sg} : ({term}).length = {len(ids)} := by decide +kernel\n"
                     f"theorem sr{sg} : List.Forall₂ YRel ({term}) PsS{sg} :=\n"
                     f"  forall2_yRel_of_getD {len(ids)} sl{sg} rfl default {gen_asm.lean_list([str(x) for x in range(len(ids))])} "
                     f"(by decide +kernel)\n    ({gen_asm.chain([f'yr{i}' for i in ids])})\n")
        nm = f"CE{m}"
        with open(os.path.join(out, nm + ".lean"), "w") as fh:
            fh.write(hdr(ns, ["LayerDT0.Gen.IdentityParts", "LayerDT0.IdentityFin", "LayerDT0.Recomp", "LayerDT0.IdentitySeg"]
                         + imps, cmd, "LayerDProto WernerEndpoint LayerDT0") + body + f"\nend {ns}\n")
        cem.append(f"{mp}.{nm}")
    if zero:
        chain2 = "sr0"
        for sg in range(1, len(segs)):
            chain2 = f"forall2_append ({chain2}) sr{sg}"
        body = (f"theorem ps_eq : Ps = {' ++ '.join(f'PsS{sg}' for sg in range(len(segs)))} := rfl\n"
                f"theorem relT0 : List.Forall₂ YRel (PsT0 {lf}) Ps := by\n"
                f"  rw [ps_eq]\n  exact {chain2}\n"
                f"/-- **`FamZero` for step 1's part list** (`famZero_ycongr`). -/\n"
                f"theorem famZeroT0 : FamZero {lf} (PsT0 {lf}) := famZero_ycongr relT0 famZero\n"
                f"\n#print axioms famZeroT0\n")
        with open(os.path.join(out, "Core.lean"), "w") as fh:
            fh.write(hdr(ns, ["LayerDT0.IdentityFin", "LayerDT0.Recomp", "LayerDT0.IdentitySeg", f"{mp}.Fam"] + cem, cmd,
                         "LayerDProto WernerEndpoint LayerDT0") + body + f"\nend {ns}\n")
        later.append(f"{mp}.Core")
    no_code(out)
    if a.test:
        print(json.dumps(dict(test=True, prepared=sorted(prepared), failed=failed, betas=betas)))
        return
    json.dump(state, open(stfile, "w"), indent=0)
    pickle.dump(cache, open(cfile, "wb"))
    # module list: replace this family's part lines (keep Pos / Orb)
    old = open(a.list).read().splitlines() if os.path.exists(a.list) else []
    keep = [l for l in old if not (l.startswith(mp + ".") and l not in (f"{mp}.Pos", f"{mp}.Orb"))
            and not l.startswith(f"# family {fam} parts")]
    ordered = [f"{mp}.Tab"] + [m for i in sorted(prepared) for m in pmods[i][0]] + cem + later
    ins = keep.index(f"{mp}.Orb") + 1
    keep[ins:ins] = [f"# family {fam} parts: {len(prepared)} of {n} generated by gen_identity_t0.py {cmd}"] + ordered
    open(a.list, "w").write("\n".join(keep) + "\n")
    summ = dict(fam=fam, parts=n, prepared=len(prepared), failed=failed, zero=zero, betas=betas,
                modules=len(ordered), declarations=sum(sum(v["chunks"].values()) for v in state.values()),
                secs=round(time.time() - t0, 1))
    json.dump(summ, open(os.path.join(out, "summary_t0.json"), "w"), indent=1)
    print(json.dumps(summ))


if __name__ == "__main__":
    main()
