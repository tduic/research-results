"""Reproduce Table VI of Khattar et al. 2510.10967 (all 10 rows): DQI semicircle t, Prange trials (Eq.18), XP trials (Eq.22)
XP: optimise allocation counts c_s (number of coordinates paying s bits) maximising P(sum Ber >= t).
Allocations searched have the form: c_K forced (s=k+1, P=1), plus c_j coords at one intermediate s=j, rest at s=0.
(also mixed 2-level) -- exact Poisson-binomial tails via log-space binomial convolution."""
import numpy as np, math, json, sys
from scipy.stats import binom
from scipy.special import logsumexp

def semicircle(l_over_m, rho):
    return (math.sqrt(l_over_m*(1-rho)) + math.sqrt((1-l_over_m)*rho))**2

def Ps(k):
    P = {0: 0.5 - 2.0**(-k-1), 1: 0.5}
    for s in range(2, k+1): P[s] = 0.5 + 2.0**(s-k-2)
    for s in range(k+1, 2*k+1): P[s] = 1.0
    return P

def logpmf_binom(N, p):
    return binom.logpmf(np.arange(N+1), N, p)

def tail_mix(groups, t):
    """groups: list of (count, prob). returns log P(sum >= t)"""
    pr = np.array([1.0]); shift = 0
    for c, p in groups:
        if c == 0: continue
        if p >= 1.0: shift += c; continue
        pr = np.convolve(pr, binom.pmf(np.arange(c+1), c, p))
    tt = t - shift
    if tt <= 0: return 0.0
    if tt >= len(pr): return -np.inf
    v = pr[tt:].sum()
    return math.log(v) if v > 0 else -np.inf

def xp_best(m, n, b, t, verbose=False):
    k = b//2; P = Ps(k); B = n*b; K = k+1
    best = (-np.inf, None)
    # pure forced
    for cK in range(0, B//K+1):
        rem = B - cK*K
        for j in range(1, K):
            cj = min(rem//j, m-cK)
            for cj2 in sorted(set([cj, cj//2, 0])):
                c0 = m - cK - cj2
                lp = tail_mix([(cK, 1.0), (cj2, P[j]), (c0, P[0])], t)
                if lp > best[0]: best = (lp, dict(cK=cK, j=j, cj=cj2, c0=c0))
    return best

def prange_logp(m, n, rho, t):
    return binom.logsf(t-n-1, m-n, rho)

if __name__ == "__main__":
    rows = []
    for (m, n, b, r, tabP, tabXP) in [(1023,60,10,496,5.49e19,1.92e15),(1023,70,10,496,1.26e22,4.64e16),
                                      (1023,80,10,496,4.30e24,1.22e18),(1023,90,10,496,1.07e27,2.08e19),(1023,100,10,496,1.75e29,2.56e20),
                                      (4095,60,12,2016,2.02e23,4.02e20),(4095,70,12,2016,4.75e26,1.97e23),
                                      (4095,80,12,2016,9.48e29,7.99e25),(4095,90,12,2016,1.41e33,2.27e28),(4095,100,12,2016,2.10e36,5.91e30)]:
        q = 2**b; rho = r/q; l = n//2
        tf = m*semicircle(l/m, rho); t = int(round(tf))
        lpP = prange_logp(m, n, rho, t)
        lpX, alloc = xp_best(m, n, b, t)
        row = dict(m=m,n=n,b=b,r=r,t_float=tf,t=t, prange_trials=math.exp(-lpP), table_prange=tabP,
                   xp_trials=math.exp(-lpX), table_xp=tabXP, alloc=alloc,
                   xp_mean=alloc['cK']+alloc['cj']*Ps(b//2)[alloc['j']]+alloc['c0']*Ps(b//2)[0])
        rows.append(row); print(json.dumps(row))
    json.dump(rows, open("results/dqi_verifiable/xp_table.json","w"), indent=1)
