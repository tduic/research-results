#!/usr/bin/env python3
"""Full-rank re-presentation of a block part for the K-fold (coupled parts).

A part's functional F(t) = fac <Y, (x)_u rho_u(t_u)> depends on (X, B_l, B_r) only through Y = B_l X B_r^T
(`FTP P = FT ... (Ymat P.k P.X P.Bl P.Br)`). The fold check `foldBOK` asks for Q, R with
Lambda P B_l = B_l Q^T, Gamma P B_r = B_r R^T and Q^T X R = alpha X. `fold_data.kappa_fold` solves the first two
for Q, R and needs B_l, B_r of full column rank (otherwise Q, R are not unique and Q^T X R = alpha X can fail
for the solution it picks, or the range of B_l is not even invariant: only range(Y) and range(Y^T) are).
In a coupled block, X lives on U (+) V and B_u = [B_u' 0], B_v = [0 B_v'], so B_u and B_v always have
rank about n/2 < n: every coupled part (31, 13 and 22) fails.

`recompress(Bl, X, Br)` returns integer (L, Z, R) with L Z R^T = Y exactly and L, R of full column rank
r = rank Y (Z r x r invertible). Then range(L) = range(Y), range(R) = range(Y^T) are invariant under the
fold of every kappa in K_b (K_b is defined by the invariance of F, i.e. of Y), the solutions Q, R are unique
and Q^T Z R = alpha Z follows from L (Q^T Z R - alpha Z) R^T = 0. The kernel then checks, per part,
`yEqOK` (R2RecompKernel.lean): the packed rows of B_l X B_r^T and of L Z R^T agree (digit bounds checked), and
`famZero_ycongr` (LayerDT0/Recomp.lean) carries FamZero from the re-presented parts to the original ones.

Construction (all integer, exact):
  B_l = L_b M_l, B_r = R_b M_r with L_b, R_b Z-bases of the column lattices (echelon form of the columns),
  M_l, M_r integer; Z_0 = M_l X M_r^T (r_l x r_r, rank r).
  r = r_l = r_r:  (L, Z, R) = (L_b, Z_0, R_b)
  otherwise:      Z_0 = U W (U a Z-basis of the column lattice of Z_0), (L, Z, R) = (L_b U, I_r, R_b W^T).
  r = 0:          (L, Z, R) = (0, [[0]], 0) with k = 1 (the part vanishes).

Usage: python3 recompress.py census [BLOCK ...]   fold data of every coupled part (all coupled blocks by default)
"""
import json, math, os, sys, time
from fractions import Fraction


def mm(A, B):
    if not A:
        return []
    k = len(B[0]) if B else 0
    Bt = list(zip(*B)) if B else [()] * k
    return [[sum(a * b for a, b in zip(r, c)) for c in Bt] for r in A]


def tr(M):
    return [list(c) for c in zip(*M)]


def rank(M):
    """exact rank (Fractions)"""
    A = [[Fraction(v) for v in r] for r in M]
    m = len(A); n = len(A[0]) if A else 0
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(r + 1, m):
            if A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r


def row_echelon_int(rows):
    """integer row echelon form (Euclid on each pivot column) of the lattice spanned by `rows`:
    a list H of linearly independent integer rows with the same Z-span"""
    R = [list(r) for r in rows if any(r)]
    n = len(R[0]) if R else 0
    H = []
    for c in range(n):
        while True:
            nz = [i for i, r in enumerate(R) if r[c] != 0]
            if len(nz) <= 1:
                break
            i0 = min(nz, key=lambda i: abs(R[i][c]))
            for i in nz:
                if i != i0:
                    q = R[i][c] // R[i0][c]
                    R[i] = [a - q * b for a, b in zip(R[i], R[i0])]
            R = [r for r in R if any(r)]
        nz = [i for i, r in enumerate(R) if r[c] != 0]
        if nz:
            piv = R.pop(nz[0])
            if piv[c] < 0:
                piv = [-v for v in piv]
            H.append(piv)
    return H


def solve_full(L, M):
    """C with L C = M, L of full column rank (Fractions), or None if inconsistent"""
    m, r = len(L), len(L[0])
    A = [[Fraction(v) for v in L[i]] + [Fraction(v) for v in M[i]] for i in range(m)]
    w = len(A[0])
    piv, row = [], 0
    for c in range(r):
        p = next((i for i in range(row, m) if A[i][c] != 0), None)
        assert p is not None, "L not of full column rank"
        A[row], A[p] = A[p], A[row]
        inv = 1 / A[row][c]
        A[row] = [x * inv for x in A[row]]
        for i in range(m):
            if i != row and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[row])]
        piv.append(c); row += 1
    if any(A[i][j] != 0 for i in range(row, m) for j in range(r, w)):
        return None
    return [A[i][r:] for i in range(r)]


def lattice_basis(M):
    """integer (Lb, C) with M = Lb C, Lb (rows of M) x r of full column rank, C integer r x cols(M)"""
    H = row_echelon_int(tr(M))           # Z-basis of the lattice of the columns of M
    if not H:
        return None, None
    if len(H) > 1:                       # LLL: the echelon basis can have large entries (block 917: +85 bits on |Y|)
        from sympy import ZZ
        from sympy.polys.matrices import DomainMatrix
        H = [[int(v) for v in r] for r in
             DomainMatrix([[ZZ(v) for v in r] for r in H], (len(H), len(H[0])), ZZ).lll().to_Matrix().tolist()]
    Lb = tr(H)
    C = solve_full(Lb, M)
    assert C is not None and all(x.denominator == 1 for r in C for x in r), "lattice basis: non-integral"
    return Lb, [[int(x) for x in r] for r in C]


def recompress(Bl, X, Br):
    """integer (L, Z, R, info) with L Z R^T = Bl X Br^T, L, R of full column rank (see the module docstring)"""
    Y = mm(mm(Bl, X), tr(Br))
    N = len(Bl)
    r = rank(Y)
    if r == 0:
        return [[0] for _ in range(N)], [[0]], [[0] for _ in range(len(Br))], dict(r=0, case="zero")
    Lb, Ml = lattice_basis(Bl)
    if Br == Bl:
        Rb, Mr = Lb, Ml
    else:
        Rb, Mr = lattice_basis(Br)
    Z0 = mm(mm(Ml, X), tr(Mr))
    rl, rr = len(Lb[0]), len(Rb[0])
    I = [[int(i == j) for j in range(r)] for i in range(r)]
    if r == rl == rr:
        L, Z, R, case = Lb, Z0, Rb, "square"
    elif r == rl:                       # Z_0 has full row rank: Y = L_b I (R_b Z_0^T)^T
        L, Z, R, case = Lb, I, mm(Rb, tr(Z0)), "left"
    elif r == rr:                       # Z_0 has full column rank: Y = (L_b Z_0) I R_b^T
        L, Z, R, case = mm(Lb, Z0), I, Rb, "right"
    else:
        U, W = lattice_basis(Z0)
        L, Z, R, case = mm(Lb, U), I, mm(Rb, tr(W)), "general"
    assert len(L[0]) == r and len(R[0]) == r and rank(L) == r and rank(R) == r
    assert mm(mm(L, Z), tr(R)) == Y, "re-presentation does not reproduce Y"
    return L, Z, R, dict(r=r, rl=rl, rr=rr, case=case)


def ent_max(M):
    return max([abs(int(v)) for r in M for v in r] + [0])


def row_sum_max(M):
    return max([sum(abs(int(v)) for v in r) for r in M] + [0])


def ybound(Bl, X, Br):
    """the a-priori bound rowsum(B_l) |X| rowsum(B_r) of |Y| that partOK / yEqOK use"""
    return row_sum_max(Bl) * ent_max(X) * row_sum_max(Br)


def yeq_width(Bl, X, Br, L, Z, R):
    """digit width w for yEqOK: 4 max(ym, ym') < 2^w"""
    return (4 * max(ybound(Bl, X, Br), ybound(L, Z, R), 1)).bit_length() + 1


def recompress_part(part):
    """the part dict (gen_asm.block_part format) with (X, Bl, Br) replaced by its full-rank re-presentation;
    the original fields are kept under 'orig' (for the kernel's yEqOK against them)"""
    L, Z, R, info = recompress(part["Bl"], part["X"], part["Br"])
    q = dict(part, X=Z, Bl=L, Br=R, recomp=info,
             orig=dict(X=part["X"], Bl=part["Bl"], Br=part["Br"]),
             yw=yeq_width(part["Bl"], part["X"], part["Br"], L, Z, R))
    return q


PRIME = (1 << 61) - 1


def rank_mod(M, p=PRIME):
    """rank modulo p (<= the rank over Q; equal to k certifies full column rank)"""
    A = [[int(v) % p for v in r] for r in M]
    m = len(A); n = len(A[0]) if A else 0
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(r + 1, m):
            if A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * b) % p for a, b in zip(A[i], A[r])]
        r += 1
    return r


def needs_recompress(part):
    """True unless B_l and B_r certainly have full column rank (rank mod p = k). A false positive only costs
    an (exact, checked) re-presentation."""
    k = len(part["X"])
    return rank_mod(part["Bl"]) < k or rank_mod(part["Br"]) < k


def recompress_all(parts):
    """re-present the parts that need it (coupled block parts); the others are returned unchanged"""
    return [recompress_part(p) if needs_recompress(p) else p for p in parts]


# --- Lean emission (gen_asm.py rzero, layerD_t0/gen_totals.py) ------------------------------------------

KERNEL_IMPORT = "LayerDProto.R2RecompKernel"   # part modules with a re-presented part
SOUND_IMPORT = "LayerDT0.Recomp"               # the family module


def lean_orig(i, P, lean_mat):
    """part module: the original presentation O<i> of a re-presented part P<i> and its kernel check rel<i>
    (empty for a part that is not re-presented)"""
    if "orig" not in P:
        return ""
    o = P["orig"]
    return (f"/-- part {i} as given ({P['recomp']}); `P{i}` is its full-rank re-presentation -/\n"
            f"def O{i} : PartData :=\n  {{ P{i} with\n    k := {len(o['X'])}, X := {lean_mat(o['X'])},\n"
            f"    Bl := {lean_mat(o['Bl'])}, Br := {lean_mat(o['Br'])} }}\n"
            f"theorem rel{i} : ycoreOK {P['yw']} O{i} P{i} = true := by decide +kernel\n")


def lean_yrel(i, P, src):
    """`yr<i> : LayerDT0.YRel <src> P<i>` for a part P<i> generated from the original part `src` (a Lean term, e.g.
    `((PsT0 .f22).getD 5 default)`): by `ycoreOK` if P<i> is re-presented, else by `sameCoreOK` (equal cores). Feed the yr<i> to
    `LayerDT0.forall2_yRel_of_getD` and `LayerDT0.famZero_ycongr` (in place of ce<i>, map_core_eq, famZero_congr)."""
    if "orig" in P:
        return (f"theorem yr{i} : LayerDT0.YRel {src} P{i} :=\n"
                f"  LayerDT0.yRel_of_ycoreOK (w := {P['yw']}) (by decide +kernel)\n")
    return f"theorem yr{i} : LayerDT0.YRel {src} P{i} :=\n  LayerDT0.yRel_of_sameCoreOK (by decide +kernel)\n"


def lean_os(parts, lf):
    """family module: `Os` (the parts as given), `rel : Forall₂ YRel Os Ps`, `famZeroO : FamZero f Os`
    (needs `famZero : FamZero f Ps` above it)"""
    n = len(parts)
    os_ = "[" + ", ".join(f"O{i}" if "orig" in P else f"P{i}" for i, P in enumerate(parts)) + "]"
    chain = "List.Forall₂.nil"
    for i in reversed(range(n)):
        r = f"(LayerDT0.yRel_of_ycoreOK rel{i})" if "orig" in parts[i] else f"(LayerDT0.yRel_refl P{i})"
        chain = f"List.Forall₂.cons {r} ({chain})" if i < n - 1 else f"List.Forall₂.cons {r} {chain}"
    return (f"\n/-- The parts as given (coupled parts in their own presentation, not re-presented). -/\n"
            f"def Os : List PartData := {os_}\n"
            f"theorem rel : List.Forall₂ LayerDT0.YRel Os Ps :=\n  {chain}\n"
            f"/-- **`FamZero` for the parts as given** (`famZero_ycongr`). -/\n"
            f"theorem famZeroO : LayerDT0.FamZero {lf} Os := LayerDT0.famZero_ycongr rel famZero\n")


def census(blocks_sel):
    import numpy as np
    import route2, fold_data
    from certdata import load_blocks, load_modules
    from gen_identity import rho_tables, coupled_maps
    from gen_asm import block_part
    blocks = load_blocks()
    RHO = rho_tables(load_modules())
    MAPS = coupled_maps()
    sel = blocks_sel or [i for i, b in enumerate(blocks) if "Bu" in b]
    for bi in sel:
        for pi_ in range(3):
            t = time.time()
            p = block_part(blocks, RHO, MAPS, bi, pi_)
            q = recompress_part(p)
            ks, tabs = q["ks"], q["tabs"]
            Y = mm(mm(q["Bl"], q["X"]), tr(q["Br"]))
            F0 = np.array(route2.tuple_tensor(Y, ks, tabs), dtype=object)
            K = route2.fold_subgroup(tabs, q["mods"], q["fam"])
            Kb = [h for h in K if route2._invariant(F0, h)]
            gens = route2.generators(Kb, q["fam"])
            res = []
            for h in gens:
                try:
                    fd = fold_data.kappa_fold(h, ks, tabs, q["Bl"], q["Br"], q["X"])
                    res.append(fd if isinstance(fd, str) else "ok")
                except ValueError as e:
                    res.append("EXC " + str(e))
            print(json.dumps(dict(block=bi, part=pi_, fam=q["fam"], ks=ks, n=len(p["X"]), **q["recomp"],
                                  K=len(K), Kb=len(Kb), gens=len(gens), ok=all(x == "ok" for x in res),
                                  res=sorted(set(res)), ym=ybound(p["Bl"], p["X"], p["Br"]).bit_length(),
                                  ym2=ybound(q["Bl"], q["X"], q["Br"]).bit_length(), sec=round(time.time() - t, 1))),
                  flush=True)


if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "census":
        census([int(x) for x in sys.argv[2:]])
    else:
        print(__doc__)
