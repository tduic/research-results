"""Core: exact finite-size DQI score law (float64, log-scaled) + XP trial counts.

Model (derivation as in ../dqi_verifiable/r4_redteam_exact.py): with e_k(s) the orthonormal Krawtchouk polynomials under Binom(m,p),
DQI with enhancing polynomial weights w (degree <= l) outputs score s w.p. pi(s) = Binom(m,p)(s) * (sum_k w_k e_k(s))^2.
Mean-optimal w = top eigenvector of the (l+1)x(l+1) Jacobi matrix; its eigenvalue is the exact mean.
Tail-optimal w for P(s>=t) = top eigenvector of M(t)_jk = sum_{s>=t} psi_j(s) psi_k(s), psi_k(s) = sqrt(B(s)) e_k(s).
Exact when 2l+1 < n+1 (= d_perp of the RS dual); the paper's l = n/2 is borderline (+-0.015 in tiny exhaustive checks).

Numerics: e_k(s) by forward three-term recurrence (dominant solution, stable) with a per-s running log scale so that
nothing over/underflows; validated against the 60-digit mpmath implementation (see validate()).
"""
import math
import numpy as np
from scipy.linalg import eigh_tridiagonal, eigh
from scipy.special import gammaln, logsumexp

A1 = 2.338107410459767  # |a_1|, first zero of Ai


def semicircle(m, l, p):
    return m * (math.sqrt(l / m * (1 - p)) + math.sqrt((1 - l / m) * p)) ** 2


def jacobi_diag(m, l, p):
    k = np.arange(l + 1, dtype=float)
    d = m * p + (1 - 2 * p) * k
    e = math.sqrt(p * (1 - p)) * np.sqrt((k[:-1] + 1) * (m - k[:-1]))
    return d, e


def exact_mean(m, l, p, vec=False):
    d, e = jacobi_diag(m, l, p)
    if not vec:
        return float(eigh_tridiagonal(d, e, eigvals_only=True, select='i', select_range=(l, l))[0])
    lam, V = eigh_tridiagonal(d, e, select='i', select_range=(l, l))
    w = V[:, 0]
    if w.sum() < 0:
        w = -w
    return float(lam[0]), w


def exact_sd_closed(m, l, p, w):
    """Var = b_l^2 w_l^2 exactly (residual of truncated eigvec in the full (m+1) Jacobi operator)."""
    bl = math.sqrt(p * (1 - p) * (l + 1) * (m - l))
    return bl * abs(w[-1])


def log_binom_pmf(m, p):
    s = np.arange(m + 1, dtype=float)
    return gammaln(m + 1) - gammaln(s + 1) - gammaln(m - s + 1) + s * math.log(p) + (m - s) * math.log1p(-p)


def psi_table(m, l, p, smin=0):
    """psi_k(s) = sqrt(B(s)) e_k(s). Forward recurrence; falls back to the full (m+1) Jacobi eigendecomposition
    (columns = psi(.)(s), sign fixed by psi_0>0) when the recurrence loses orthonormality (large l at small p)."""
    LM, SG = _psi_rec(m, l, p, 0)
    nrm = np.exp(2 * LM).sum(1) if l < 2000 else None
    if nrm is not None and np.all(np.abs(nrm - 1) < 1e-6):
        return LM[:, smin:], SG[:, smin:]
    if m > 8192:
        raise RuntimeError('recurrence unstable and m too large for full eigendecomposition')
    d, e = jacobi_diag(m, m, p)
    lam, V = eigh_tridiagonal(d, e)  # lam ~ 0..m
    V = V * np.sign(V[0])
    P = V[:l + 1, smin:]
    with np.errstate(divide='ignore'):
        return np.log(np.abs(P)), np.sign(P).astype(np.int8)


def _psi_rec(m, l, p, smin=0):
    """Return logpsi_mag (l+1, S) and sign (l+1, S) of psi_k(s) for s = smin..m."""
    s = np.arange(smin, m + 1, dtype=float)
    lB = log_binom_pmf(m, p)[smin:]
    sp = math.sqrt(p * (1 - p))
    prev = np.zeros_like(s)
    cur = np.ones_like(s)
    S = 0.5 * lB.copy()  # running log scale: psi_k = cur * exp(S)
    LM = np.empty((l + 1, len(s)))
    SG = np.empty((l + 1, len(s)), dtype=np.int8)

    def store(k, v):
        with np.errstate(divide='ignore'):
            LM[k] = np.log(np.abs(v)) + S
        SG[k] = np.sign(v)

    store(0, cur)
    for k in range(l):
        nxt = ((s - m * p - (1 - 2 * p) * k) * cur - sp * math.sqrt(k * (m - k + 1)) * prev) / (sp * math.sqrt((k + 1) * (m - k)))
        big = np.maximum(np.abs(nxt), np.abs(cur))
        resc = big > 1e100
        if resc.any():
            f = big[resc]
            nxt[resc] /= f; cur[resc] /= f
            S[resc] += np.log(f)
        prev, cur = cur, nxt
        store(k + 1, cur)
    return LM, SG


def dist_from_w(m, l, p, w, smin=0):
    """pi(s) for s=smin..m (float64; deep tails underflow to 0 harmlessly)."""
    LM, SG = psi_table(m, l, p, smin)
    psi = SG * np.exp(LM - LM.max())
    a = w @ psi
    pi = a * a
    if smin == 0:
        pi /= pi.sum()
    else:
        pi *= math.exp(2 * LM.max())
    return pi


def dist_meanopt(m, l, p):
    """Mean-optimal DQI law via Christoffel-Darboux: w_k ∝ e_k(lam) with e_{l+1}(lam)=0, so
    sum_k w_k e_k(s) ∝ e_{l+1}(s)/(s-lam). Cancellation-free. Returns normalised pi(s), s=0..m, and lam."""
    lam = exact_mean(m, l, p)
    LM, SG = psi_table(m, l + 1, p, 0)
    s = np.arange(m + 1, dtype=float)
    lg = 2 * LM[l + 1] - 2 * np.log(np.abs(s - lam) + 1e-300)
    lg -= lg.max()
    pi = np.exp(lg)
    return pi / pi.sum(), lam


def dist_stats(pi, smin=0):
    s = np.arange(smin, smin + len(pi))
    Z = pi.sum()
    mu = (s * pi).sum() / Z
    var = ((s - mu) ** 2 * pi).sum() / Z
    sk = ((s - mu) ** 3 * pi).sum() / Z / var ** 1.5
    cdf = np.cumsum(pi) / Z
    med = int(s[np.searchsorted(cdf, 0.5)])
    return dict(Z=float(Z), mean=float(mu), sd=float(math.sqrt(var)), skew=float(sk), median=med)


def tail_opt_curve(m, l, p, t_lo, t_hi=None):
    """log P_tailopt(s>=t) for t in [t_lo, t_hi] via a downward log-scaled sweep of M(t)."""
    if t_hi is None:
        t_hi = m
    LM, SG = psi_table(m, l, p, t_lo)
    S = LM.shape[1]
    M = np.zeros((l + 1, l + 1))
    Lam = -np.inf  # M_true = M * exp(2 Lam)
    out = {}
    for j in range(S - 1, -1, -1):
        col = LM[:, j]
        cm = col.max()
        if np.isfinite(cm):
            newLam = max(Lam, cm)
            if np.isfinite(Lam):
                M *= math.exp(2 * (Lam - newLam))
            v = SG[:, j] * np.exp(col - newLam)
            M += np.outer(v, v)
            Lam = newLam
        t = t_lo + j
        if t <= t_hi:
            ev = np.linalg.eigvalsh(M)[-1]
            out[t] = math.log(max(ev, 1e-300)) + 2 * Lam
    ts = np.array(sorted(out))
    return ts, np.array([out[t] for t in ts])


def tail_opt_vec(m, l, p, t):
    LM, SG = psi_table(m, l, p, t)
    lam = LM.max()
    psi = SG * np.exp(LM - lam)
    M = psi @ psi.T
    ev, V = eigh(M)
    return math.log(ev[-1]) + 2 * lam, V[:, -1]


def xp_params(n, b):
    k = b // 2
    F = (n * b) // (k + 1)
    p0 = 0.5 - 2.0 ** (-k - 1)
    return F, p0


def log_xp_success(m, n, b, ts):
    """log P_XP(score >= t) for array ts; XP trials = exp(-.)."""
    F, p0 = xp_params(n, b)
    N = m - F
    j = np.arange(N + 1, dtype=float)
    lp = gammaln(N + 1) - gammaln(j + 1) - gammaln(N - j + 1) + j * math.log(p0) + (N - j) * math.log1p(-p0)
    # reverse cumulative logsumexp
    rc = np.logaddexp.accumulate(lp[::-1])[::-1]
    out = []
    for t in np.atleast_1d(ts):
        need = int(t) - F
        out.append(0.0 if need <= 0 else (rc[need] if need <= N else -np.inf))
    return np.array(out)


def validate():
    m, n, b, r = 4095, 70, 12, 2016
    p = r / 4096; l = 35
    lam, w = exact_mean(m, l, p, vec=True)
    pi = dist_from_w(m, l, p, w)
    st = dist_stats(pi)
    ts, lt = tail_opt_curve(m, l, p, 2300, 2450)
    Pt = dict(zip(ts.tolist(), np.exp(lt).tolist()))
    xp = np.exp(-log_xp_success(m, n, b, [2393, 2360]))
    return dict(eig=lam, sd_closed=exact_sd_closed(m, l, p, w), **st,
                P_meanopt_2393=float(pi[2393:].sum()), P_tailopt_2393=Pt[2393], P_tailopt_2440=Pt[2440],
                xp_2393=float(xp[0]), xp_2360=float(xp[1]),
                ref=dict(eig=2359.747, sd=31.79, median=2362, P_mean=0.0283, P_tail=0.0596, P_tail_2440=2.7e-5,
                         xp_2393=1.966e23, xp_2360=7.99e18))


if __name__ == "__main__":
    import json
    print(json.dumps(validate(), indent=1))
