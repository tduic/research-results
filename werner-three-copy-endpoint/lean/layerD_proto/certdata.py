"""Shared helpers for the layer-D prototype generators: load the d = 5 certificate, exact Bareiss,
and Lean literal encodings (plain lists vs. packed big-integer literals)."""
import json, os, sys
from fractions import Fraction

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.environ.get("LAYERD_CERT") or os.path.normpath(os.path.join(HERE, "..", "..", "exact_certificate_d5", "cert"))
# LAYERD_CERT: any certificate directory with the d = 5 layout (modules.json) or the t = 0 layout (sites.json, qubit.json)
GEN = os.environ.get("LAYERD_GEN") or os.path.join(HERE, "LayerDProto", "Gen")  # LAYERD_GEN: write elsewhere (tests)


def load_blocks():
    with open(os.path.join(CERT, "blocks.jsonl")) as fh:
        return [json.loads(line) for line in fh]


def load_multipliers():
    with open(os.path.join(CERT, "multipliers.json")) as fh:
        return json.load(fh)


def load_modules():
    """the d = 5 modules.json, or None for the t = 0 layout (sites.json + qubit.json; see rho_tables_t0)"""
    if not os.path.exists(os.path.join(CERT, "modules.json")):
        return None
    with open(os.path.join(CERT, "modules.json")) as fh:
        return json.load(fh)


def shifted(blk):
    """Integer matrix X0 - sh I with sh = 2^s mu (an integer for every block: s >= mu_exp)."""
    s, mn, me = int(blk["s"]), int(blk["mu_num"]), int(blk["mu_exp"])
    assert s >= me
    sh = mn << (s - me)
    X0 = [[int(v) for v in r] for r in blk["X0"]]
    return [[X0[i][j] - (sh if i == j else 0) for j in range(len(X0))] for i in range(len(X0))], sh


def bareiss_W(A):
    """Fraction-free elimination of [A | I]: lower-triangular integer W with W A upper triangular and
    W A W^T = diag(e), e_i = Delta_{i-1} Delta_i (leading minors). Raises if a pivot is <= 0."""
    k = len(A)
    M = [list(A[i]) + [1 if j == i else 0 for j in range(k)] for i in range(k)]
    prev = 1
    for p in range(k):
        piv = M[p][p]
        if piv <= 0:
            raise ValueError("not positive definite")
        for i in range(p + 1, k):
            m = M[i][p]
            M[i] = [(M[i][j] * piv - m * M[p][j]) // prev for j in range(2 * k)]
        prev = piv
    W = [row[k:] for row in M]
    e = [W[i][i] * M[i][i] for i in range(k)]
    return W, e


def check_WAWt(A, W, e):
    k = len(A)
    WA = [[sum(W[i][t] * A[t][j] for t in range(k)) for j in range(k)] for i in range(k)]
    for i in range(k):
        for j in range(k):
            v = sum(WA[i][t] * W[j][t] for t in range(k))
            assert v == (e[i] if i == j else 0)


def pd_params(A, W, e):
    k = len(A)
    w = max(abs(v) for r in W for v in r)
    a = max(abs(v) for r in A for v in r)
    c = max(abs(v) for v in e)
    wb, ab, cb = w.bit_length(), a.bit_length(), c.bit_length()
    bound = 2 * (k * k * (2 ** (2 * wb + ab)) + 2 ** cb)      # the bound checkPD evaluates
    beta = bound.bit_length()
    assert bound < 2 ** beta
    return dict(k=k, beta=beta, wb=wb, ab=ab, cb=cb)


# ------------------------------------------------------------------------------- Lean literals
def lean_int(v):
    return str(v) if v >= 0 else f"({v})"


def lean_list(vals):
    return "[" + ", ".join(lean_int(v) for v in vals) + "]"


def lean_rows(rows, indent="  "):
    return "[\n" + ",\n".join(indent + lean_list(r) for r in rows) + "]"


def packed(vals, b):
    """sum_i vals[i] 2^(b i) (signed digits, |v| < 2^(b-1) required)."""
    assert all(2 * abs(v) < 2 ** b for v in vals)
    out = 0
    for v in reversed(vals):
        out = out * (1 << b) + v
    return out


def lean_bigint(v, chunk=10000):
    """An Int literal; very long literals are split into hex chunks combined in the kernel
    (literal parsing is quadratic in the number of digits)."""
    neg = v < 0
    h = format(abs(v), "x")
    if len(h) <= chunk:
        lit = "0x" + h
    else:
        parts = [h[max(0, i - chunk):i] for i in range(len(h), 0, -chunk)]   # least significant first
        lit = "LayerDProto.joinHex " + str(4 * chunk) + " [" + ", ".join("0x" + p for p in parts) + "]"
        lit = "(" + lit + ")"
    return f"(-(Int.ofNat {lit}))" if neg else f"(Int.ofNat {lit})"


def short_W(A, bits):
    """Short W: the rows of the exact Bareiss W normalised to W_i / sqrt(e_i) (so that W A W^T ~ I)
    and rounded to the integer grid 2^-bits. Returns (W', E' = W' A W'^T) with E' exact."""
    from math import isqrt
    W, e = bareiss_W(A)
    k = len(A)
    Ws = []
    for i in range(k):
        r = isqrt(e[i] << 64)          # sqrt(e_i) * 2^32
        Ws.append([((v << (bits + 32)) + r // 2) // r for v in W[i]])
    WA = [[sum(Ws[i][t] * A[t][j] for t in range(k)) for j in range(k)] for i in range(k)]
    E = [[sum(WA[i][t] * Ws[j][t] for t in range(k)) for j in range(k)] for i in range(k)]
    return Ws, E


def dd_ok(E):
    return all(2 * E[i][i] > sum(abs(v) for v in E[i]) for i in range(len(E)))


def dd_params(A, W, E):
    k = len(A)
    wb = max(abs(v) for r in W for v in r).bit_length()
    ab = max(abs(v) for r in A for v in r).bit_length()
    eb = max(abs(v) for r in E for v in r).bit_length()
    bound = 2 * (k * k * (2 ** (2 * wb + ab)) + 2 ** eb)
    return dict(k=k, beta=bound.bit_length(), wb=wb, ab=ab, eb=eb)
