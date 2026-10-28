"""R4 red-team part 2.
(i) Tiny exhaustive check of the Jacobi formula, incl. the borderline 2l+1 = d_perp = n+1 used by the paper (l = n/2).
(ii) Advantage ratio R(t) = XP_trials(t) * P_DQI(score >= t) at the headline instance, for mean-opt and tail-opt P.
"""
import itertools, json, random, sys
import numpy as np
import mpmath as mp
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from r4_redteam_exact import jacobi, krawtchouk_table, binom_pmf, dist_from_w, tail_opt, xp_trials

mp.mp.dps = 50


def gf_tables(b, poly):
    q = 1 << b
    exp, log = [0] * (2 * q), [0] * q
    x = 1
    for i in range(q - 1):
        exp[i] = x; log[x] = i
        x <<= 1
        if x & q: x ^= poly
    for i in range(q - 1, 2 * q): exp[i] = exp[i - (q - 1)]
    return exp, log


def tiny(b, poly, n, r, l, seed):
    q = 1 << b; m = q - 1
    exp, log = gf_tables(b, poly)
    rng = random.Random(seed)
    Fs = [set(rng.sample(range(q), r)) for _ in range(m)]
    alphas = [exp[i] for i in range(m)]
    # evaluation table: value of monomial y^j at alpha
    pw = [[exp[(log[a] * j) % (q - 1)] for j in range(n)] for a in alphas]
    def mul(a, c):
        return 0 if a == 0 or c == 0 else exp[log[a] + log[c]]
    hist = np.zeros(m + 1)
    for coeffs in itertools.product(range(q), repeat=n):
        s = 0
        for i in range(m):
            v = 0
            for j in range(n):
                v ^= mul(coeffs[j], pw[i][j])
            s += v in Fs[i]
        hist[s] += 1
    p = mp.mpf(r) / q
    A = jacobi(m, l, p)
    ev, V = mp.eigsy(A)
    i = max(range(l + 1), key=lambda i: ev[i])
    w = [V[k, i] for k in range(l + 1)]
    E = krawtchouk_table(m, l, p)
    num = den = mp.mpf(0)
    for s in range(m + 1):
        a = sum(w[k] * E[k][s] for k in range(l + 1)) ** 2
        num += hist[s] * a * s; den += hist[s] * a
    return dict(b=b, n=n, r=r, l=l, d_perp=n + 1, two_l_plus_1=2 * l + 1,
                eig=float(ev[i]), brute=float(num / den), diff=float(num / den - ev[i]))


if __name__ == "__main__":
    out = {"tiny": []}
    for (n, l) in [(3, 1), (4, 2), (4, 1)]:
        for seed in range(3):
            out["tiny"].append(tiny(4, 0b10011, n, 7, l, seed))
    m, n, b, r = 4095, 70, 12, 2016
    p = mp.mpf(r) / 4096
    l = 35
    E = krawtchouk_table(m, l, p); B = binom_pmf(m, p)
    A = jacobi(m, l, p); ev, V = mp.eigsy(A)
    i = max(range(l + 1), key=lambda i: ev[i])
    w = [V[k, i] for k in range(l + 1)]
    pi, _ = dist_from_w(E, B, w)
    rows = []
    for t in range(2340, 2441, 10):
        Pm = float(sum(pi[t:]))
        Pt, _ = tail_opt(E, B, l, t)
        X = xp_trials(m, n, b, t)
        rows.append(dict(t=t, xp=X, P_meanopt=Pm, P_tailopt=Pt, ratio_meanopt=X * Pm, ratio_tailopt=X * Pt))
    out["ratio"] = rows
    json.dump(out, sys.stdout, indent=1)
