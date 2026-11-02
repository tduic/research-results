#!/usr/bin/env python3
"""Size statistics of a t = 0 certificate directory (format of ../exact_t0/verify_t0.py).

total bit size = sum of bit lengths of every integer the certificate stores: block bases (B, Bu, Bv), X0, Delta,
the margins mu (numerator and exponent), the block exponents s, the multipliers lambda (numerator + denominator),
the common Delta denominator, and the integers of sites.json / qubit.json (rationals counted as numerator +
denominator).  Indices (rs, rq, Delta positions, row indices) are not counted.
Usage: python3 cert_stats.py CERT_DIR [CERT_DIR ...]   (prints one JSON line per directory)
"""
import json, os, sys
from fractions import Fraction


def bits(v):
    return abs(int(v)).bit_length()


def frac_bits(s):
    f = Fraction(s)
    return bits(f.numerator) + (bits(f.denominator) if f.denominator != 1 else 0)


def walk_numbers(x):
    if isinstance(x, list):
        for y in x:
            yield from walk_numbers(y)
    elif isinstance(x, dict):
        for y in x.values():
            yield from walk_numbers(y)
    elif isinstance(x, bool):
        return
    elif isinstance(x, (int, str)):
        try:
            yield Fraction(x)
        except (ValueError, ZeroDivisionError):
            return


def stats(cert):
    out = dict(cert=cert, bytes={}, bits={}, max_bits={})
    for fn in ("blocks.jsonl", "multipliers.json", "sites.json", "qubit.json"):
        out["bytes"][fn] = os.path.getsize(os.path.join(cert, fn))
    out["bytes"]["total"] = sum(out["bytes"].values())
    tb = dict(basis=0, X0=0, delta=0, mu_s=0)
    mx = dict(basis=0, X0=0, delta=0, block_s=0)
    nent = dict(X0=0, delta=0, blocks=0)
    with open(os.path.join(cert, "blocks.jsonl")) as fh:
        for line in fh:
            b = json.loads(line)
            nent["blocks"] += 1
            for key in ("B", "Bu", "Bv"):
                for r in b.get(key, []):
                    for v in r:
                        tb["basis"] += bits(v); mx["basis"] = max(mx["basis"], bits(v))
            for r in b["X0"]:
                for v in r:
                    tb["X0"] += bits(v); mx["X0"] = max(mx["X0"], bits(v)); nent["X0"] += 1
            for _, v in b.get("delta", []):
                tb["delta"] += bits(v); mx["delta"] = max(mx["delta"], bits(v)); nent["delta"] += 1
            tb["mu_s"] += bits(b["mu_num"]) + bits(b["mu_exp"]) + bits(b["s"])
            mx["block_s"] = max(mx["block_s"], int(b["s"]))
    m = json.load(open(os.path.join(cert, "multipliers.json")))
    lam = [Fraction(v) for v in m["lam"]]
    tb["lambda"] = sum(bits(f.numerator) + (bits(f.denominator) if f.denominator != 1 else 0) for f in lam)
    tb["delta_den"] = bits(m["delta_den"])
    tb["sites_qubit"] = 0
    for fn in ("sites.json", "qubit.json"):
        for f in walk_numbers(json.load(open(os.path.join(cert, fn)))):
            tb["sites_qubit"] += bits(f.numerator) + (bits(f.denominator) if f.denominator != 1 else 0)
    tb["total"] = sum(tb.values())
    out["bits"] = tb
    mx["lambda_num"] = max(bits(f.numerator) for f in lam)
    mx["lambda_den"] = max(bits(f.denominator) for f in lam)
    mx["delta_den"] = tb["delta_den"]
    out["max_bits"] = mx
    out["counts"] = dict(nent, lambda_nonzero=sum(1 for f in lam if f), rows=len(lam))
    return out


if __name__ == "__main__":
    for c in sys.argv[1:]:
        print(json.dumps(stats(c)))
