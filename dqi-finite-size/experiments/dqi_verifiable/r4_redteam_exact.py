"""R4 red-team: independent re-derivation of finite-size DQI score statistics and XP trial counts.

Derivation (independent of dqi_exact_t.py): with g_i = (1[sat_i] - p)/sqrt(p(1-p)), g_i^2 = 1 + c g_i,
c = (1-2p)/sqrt(p(1-p)). For elementary symmetric P^(k) of the g_i:
  sum_i g_i P^(k) = (k+1) P^(k+1) + c k P^(k) + (m-k+1) P^(k-1)   (exact multilinear identity)
With e_k = P^(k)/sqrt(C(m,k)) orthonormal (valid when j+k' < d_perp = n+1 for all pairs used):
  s e_k = mp e_k + sqrt(p(1-p)) [ sqrt((k+1)(m-k)) e_{k+1} + c k e_k + sqrt(k(m-k+1)) e_{k-1} ].
e_k depends on x only via s, so e_k(s) are orthonormal Krawtchouk polys under Binom(m,p).
DQI output law over s (score histogram ~ q^n Binom(m,p)): pi(s) = Binom(m,p)(s) * (sum_k w_k e_k(s))^2.
"""
import json, sys
import mpmath as mp

mp.mp.dps = 60


def semicircle(m, l, p):
    return m * (mp.sqrt(mp.mpf(l) / m * (1 - p)) + mp.sqrt((1 - mp.mpf(l) / m) * p)) ** 2


def jacobi(m, l, p):
    sp = mp.sqrt(p * (1 - p))
    A = mp.zeros(l + 1, l + 1)
    for k in range(l + 1):
        A[k, k] = m * p + (1 - 2 * p) * k
        if k < l:
            A[k, k + 1] = A[k + 1, k] = sp * mp.sqrt((k + 1) * (m - k))
    return A


def krawtchouk_table(m, l, p):
    """E[k][s] = e_k(s) for s=0..m, k=0..l+1, via the three-term recurrence (mp precision)."""
    sp = mp.sqrt(p * (1 - p))
    E = [[mp.mpf(1)] * (m + 1)]
    prev = [mp.mpf(0)] * (m + 1)
    for k in range(l + 1):
        cur = E[k]
        nxt = []
        for s in range(m + 1):
            v = (s - m * p - (1 - 2 * p) * k) * cur[s] - sp * mp.sqrt(k * (m - k + 1)) * prev[s]
            nxt.append(v / (sp * mp.sqrt((k + 1) * (m - k))))
        prev = cur
        E.append(nxt)
    return E


def binom_pmf(m, p):
    return [mp.binomial(m, s) * p ** s * (1 - p) ** (m - s) for s in range(m + 1)]


def dist_from_w(E, B, w):
    m = len(B) - 1
    pi = []
    for s in range(m + 1):
        a = sum(w[k] * E[k][s] for k in range(len(w)))
        pi.append(B[s] * a * a)
    Z = sum(pi)
    return [x / Z for x in pi], Z


def stats(pi, ts):
    m = len(pi) - 1
    mean = sum(s * pi[s] for s in range(m + 1))
    var = sum((s - mean) ** 2 * pi[s] for s in range(m + 1))
    cdf, med = mp.mpf(0), None
    for s in range(m + 1):
        cdf += pi[s]
        if med is None and cdf >= 0.5:
            med = s
    tails = {t: float(sum(pi[t:])) for t in ts}
    return float(mean), float(mp.sqrt(var)), med, tails


def tail_opt(E, B, l, t):
    """max_w P(s>=t) = top generalized eigval of M_jk = sum_{s>=t} B e_j e_k (Gram = I)."""
    m = len(B) - 1
    M = mp.zeros(l + 1, l + 1)
    for j in range(l + 1):
        for k in range(j, l + 1):
            v = sum(B[s] * E[j][s] * E[k][s] for s in range(t, m + 1))
            M[j, k] = M[k, j] = v
    ev, V = mp.eigsy(M)
    i = max(range(l + 1), key=lambda i: ev[i])
    return float(ev[i]), [V[k, i] for k in range(l + 1)]


def xp_trials(m, n, b, t):
    k = b // 2
    F = (n * b) // (k + 1)
    p0 = mp.mpf(1) / 2 - mp.mpf(2) ** (-k - 1)
    need = t - F
    N = m - F
    P = sum(mp.binomial(N, j) * p0 ** j * (1 - p0) ** (N - j) for j in range(max(need, 0), N + 1))
    return float(1 / P)


if __name__ == "__main__":
    m, n, b, r = 4095, 70, 12, 2016
    q = 2 ** b
    p = mp.mpf(r) / q
    out = {}
    t_sc = semicircle(m, 35, p)
    out["semicircle_t_l35"] = float(t_sc)
    E = krawtchouk_table(m, 36, p)
    B = binom_pmf(m, p)
    # orthonormality check
    G = max(abs(sum(B[s] * E[j][s] * E[kk][s] for s in range(m + 1)) - (1 if j == kk else 0))
            for j in (0, 10, 35, 36) for kk in (0, 10, 35, 36))
    out["orthonormality_maxerr"] = float(G)
    for l in (34, 35):
        A = jacobi(m, l, p)
        ev, V = mp.eigsy(A)
        i = max(range(l + 1), key=lambda i: ev[i])
        w = [V[k, i] for k in range(l + 1)]
        if sum(w) < 0:
            w = [-x for x in w]
        pi, Z = dist_from_w(E, B, w)
        mean, sd, med, tails = stats(pi, [2360, 2366, 2393])
        out[f"l{l}"] = dict(top_eig=float(ev[i]), semicircle=float(semicircle(m, l, p)), dist_mean=mean,
                            sd=sd, median=med, tails=tails, Z=float(Z))
        if l == 35:
            pt, wt = tail_opt(E, B, l, 2393)
            pit, _ = dist_from_w(E, B, wt)
            mt, sdt, medt, tt = stats(pit, [2393])
            out["l35_tailopt_2393"] = dict(P=pt, mean=mt, sd=sdt, median=medt)
            # t at which mean-optimal DQI succeeds w.p. >= 1/2
    for t in (2393, 2360, 2366, out["l35"]["median"]):
        out[f"xp_t{t}"] = xp_trials(m, n, b, t)
    out["prange_t2393"] = float(1 / sum(mp.binomial(m - n, s - n) * p ** (s - n) * (1 - p) ** (m - s)
                                        for s in range(2393, m + 1)))
    json.dump(out, sys.stdout, indent=1)
