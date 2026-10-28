"""Independent check: decode every Lean certificate exactly as Trifference.dec does, compare with JSON,
re-check trifference with numpy. Usage: python3 -I verification/rt_check.py .  (from trifferent-codes/)"""
import sys, os, re, json, itertools
import numpy as np
P = sys.argv[1]
LD = os.path.join(P, "lean", "Trifference")
claims = {10: 30, 11: 36, 12: 48, 16: 108, 17: 109}

def lean_list(n, M):
    f = os.path.join(LD, f"N{n}M{M}_Code.lean")
    if not os.path.exists(f): f = os.path.join(LD, f"N{n}M{M}.lean")
    s = open(f).read()
    m = re.search(r"def codeN%dM%d : List \(ℕ × ℕ\) := \[(.*?)\]" % (n, M), s, re.S)
    body = m.group(1)
    pairs = re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", body)
    # make sure nothing else is hiding in the list body
    assert re.sub(r"\(\s*\d+\s*,\s*\d+\s*\)|[\s,]", "", body) == "", "unexpected tokens"
    return [(int(p), int(q)) for p, q in pairs], s

def dec(n, p, q):  # mirrors Trifference.dec: bit i of p -> 1, else bit i of q -> 2, else 0
    return tuple(1 if (p >> i) & 1 else (2 if (q >> i) & 1 else 0) for i in range(n))

def trifferent_np(W):
    A = np.array(W, dtype=np.int8); M, n = A.shape
    bad = 0
    for a in range(M):
        for b in range(a + 1, M):
            dab = A[a] != A[b]
            # rainbow at i with c iff c_i = 3 - a_i - b_i (mod 3) and a_i != b_i
            third = (3 - A[a].astype(int) - A[b].astype(int)) % 3
            ok = ((A[b + 1:] == third) & dab).any(axis=1)
            bad += int((~ok).sum())
    return bad

for n, M in claims.items():
    L, src = lean_list(n, M)
    W = [dec(n, p, q) for p, q in L]
    js = [tuple(int(ch) for ch in w) for w in json.load(open(os.path.join(P, "codes", f"code_n{n}_M{M}.json")))]
    overlap = sum(1 for p, q in L if p & q & ((1 << n) - 1))
    high = sum(1 for p, q in L if (p | q) >> n)
    # theorem statement
    thm = re.search(r"theorem T_ge_N%dM%d : (.*?) := by" % (n, M), open(os.path.join(LD, f"N{n}M{M}.lean")).read(), re.S).group(1)
    print(f"n={n} M={M}: lean len={len(L)} distinct={len(set(W))} == json? {sorted(W)==sorted(js)} "
          f"p&q overlaps={overlap} high bits={high} bad triples={trifferent_np(W)}")
    print("   statement:", " ".join(thm.split()))
