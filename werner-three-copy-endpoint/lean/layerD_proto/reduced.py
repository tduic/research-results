"""Reduced grids for the literal-free family totals (Lean side: LayerDProto/R2RedKernel.lean, R2Reduced.lean).

At grid value d the tree grid has N = 24 * 24 * |S1[d]| points, position j = (t0 * 24 + t1) |S1| + i2.
`reduced_grid(fam)` returns, per grid value d:
  pos  -- the reduced positions: the smallest position of every H-orbit of grid points (sorted);
  wit  -- one witness code per grid position j: e = c + 2^15 h with c = pos of j's orbit and
          h = g' + 24 (g + 24 (eps + 2 sigma)) a parameter of H (sigma = index in PERMS3) with h . gpt(j) = gpt(c)
          (the kernel's `witOK`);
  mask -- sum of 2^c over pos.
"""
import functools
import route2

PERMS3 = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]


def grid_pt(S1d, d, j):
    s = len(S1d)
    return (j // (24 * s), j // s % 24, S1d[j % s], d)


def h_code(h):
    sg, e, g, g2 = h
    return g2 + 24 * (g + 24 * (int(bool(e)) + 2 * PERMS3.index(list(sg))))


@functools.lru_cache(maxsize=None)
def reduced_grid(fam):
    DC, S1 = route2.tree_grid(fam)
    H = route2.h_elements(fam)
    out = {}
    for d in DC:
        s1 = S1[d]
        s = len(s1)
        idx = {t2: i for i, t2 in enumerate(s1)}
        N = 576 * s

        def posof(u):
            if u[3] != d or u[2] not in idx:
                return None
            return (u[0] * 24 + u[1]) * s + idx[u[2]]

        rep = [None] * N
        for j in range(N):
            if rep[j] is None:
                t = grid_pt(s1, d, j)
                for h in H:
                    q = posof(route2.h_act(h, t))
                    if q is not None and rep[q] is None:
                        rep[q] = j
                assert rep[j] == j
        pos = sorted(set(rep))
        wit = []
        for j in range(N):
            t, c = grid_pt(s1, d, j), rep[j]
            for h in H:
                if posof(route2.h_act(h, t)) == c:
                    wit.append(c + 32768 * h_code(h))
                    break
            else:
                raise AssertionError((fam, d, j))
        out[d] = dict(pos=pos, wit=wit, mask=sum(1 << c for c in pos), S1=s1, N=N)
    return out


def check_witnesses(fam):
    """independent re-check in Python of what the kernel's orbOK checks"""
    R = reduced_grid(fam)
    for d, r in R.items():
        s1, N, pset = r["S1"], r["N"], set(r["pos"])
        assert len(r["wit"]) == N
        for j, e in enumerate(r["wit"]):
            c, h = e % 32768, e // 32768
            sg, eps, g, g2 = PERMS3[h // 1152], h // 576 % 2, h // 24 % 24, h % 24
            assert c in pset and c < N
            assert route2.h_act((tuple(sg), eps, g, g2), grid_pt(s1, d, j)) == grid_pt(s1, d, c)
    return {d: len(r["pos"]) for d, r in R.items()}


if __name__ == "__main__":
    for fam in ("31", "22", "13"):
        print(fam, check_witnesses(fam))


SLICE = int(__import__("os").environ.get("ORB_SLICE", "1024"))


def lean_hex(v, chunk=10000):
    """a Nat literal (long ones split into hex chunks joined by the kernel, as certdata.lean_bigint)"""
    h = format(v, "x")
    if len(h) <= chunk:
        return "0x" + h
    parts = [h[max(0, i - chunk):i] for i in range(len(h), 0, -chunk)]
    return "(LayerDProto.joinHex " + str(4 * chunk) + " [" + ", ".join("0x" + p for p in parts) + "])"


def lean_orb(d, r, bosN, slice_=SLICE):
    """Lean source of the orbit checks of grid value d: (kernel part: mask, posOK and one witSlice theorem per
    slice of positions; core Lean only) and (cov<d>: every grid position has a checked witness, by
    witSlice_cover; for the module that imports Mathlib anyway)"""
    S1d, N = r["S1"], r["N"]
    out = (f"\ndef mask{d} : Nat := {lean_hex(r['mask'])}\n"
           f"theorem posok{d} : posOK {S1d} pos{d} mask{d} = true := by decide +kernel\n")
    starts = list(range(0, N, slice_))
    for k, j0 in enumerate(starts):
        n = min(slice_, N - j0)
        W = sum(e << (32 * i) for i, e in enumerate(r["wit"][j0:j0 + n]))
        out += (f"theorem orb{d}_{k} : witSlice {bosN} {S1d} {d} {N} mask{d} 20 {j0} {n} {lean_hex(W)} = true := "
                f"by decide +kernel\n")
    cov = (f"theorem cov{d} : ∀ j < 24 * 24 * List.length {S1d}, ∃ e, witOK {bosN} {S1d} {d} "
            f"(24 * 24 * List.length {S1d}) mask{d} j e = true := by\n"
            f"  intro j hj\n  have hN : 24 * 24 * List.length {S1d} = {N} := by decide\n  rw [hN] at hj ⊢\n")
    for k, j0 in enumerate(starts):
        n = min(slice_, N - j0)
        if k < len(starts) - 1:
            cov += (f"  rcases Nat.lt_or_ge j {j0 + n} with h | h\n"
                    f"  · exact witSlice_cover _ _ _ _ _ _ _ _ _ orb{d}_{k} j (by omega) (by omega)\n")
        else:
            cov += f"  exact witSlice_cover _ _ _ _ _ _ _ _ _ orb{d}_{k} j (by omega) (by omega)\n"
    return out, cov
