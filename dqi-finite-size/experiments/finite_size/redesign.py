"""Repetition-optimised DQI design at GF(2^12), m=4095, r=2016.
minimise  Toffoli(n) / P_DQI(score >= t)   over n (l = floor(n/2)), t, enhancing polynomial (tail-optimal at t)
subject to (FAIR)  XP(t) * P_DQI(>=t) >= T      [classical trials per quantum run]
       or  (ABS)   XP(t) >= T                     [absolute classical trials per certificate]
Toffoli(n), qubits(n): quadratic / linear fits to Table VI b=12 rows (n=60..100; extrapolation flagged outside).
"""
import json, math, sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from dqi_core import exact_mean, tail_opt_curve, log_xp_success, dist_meanopt

M, B, R = 4095, 12, 2016
P = R / 4096
LN10 = math.log(10)
NS = np.array([60, 70, 80, 90, 100])
TOF = np.array([4.64e6, 5.72e6, 6.92e6, 8.27e6, 9.75e6])
QB = np.array([1640, 1885, 2125, 2366, 2606])
TOF_C = np.polyfit(NS, TOF, 2)
QB_C = np.polyfit(NS, QB, 1)


def toffoli(n):
    return float(np.polyval(TOF_C, n))


def qubits(n):
    return float(np.polyval(QB_C, n))


_cache = {}


def curves(n):
    if n in _cache:
        return _cache[n]
    l = n // 2
    pi, lam = dist_meanopt(M, l, P)
    s = np.arange(M + 1)
    sd = math.sqrt(((s - lam) ** 2 * pi).sum())
    t_lo = max(int(lam - 3 * sd), 0)
    t_hi = min(int(lam + 25 * sd), M)
    ts, lPt = tail_opt_curve(M, l, P, t_lo, t_hi)
    lX = log_xp_success(M, n, B, ts)
    tail_mean = np.cumsum(pi[::-1])[::-1][ts]
    _cache[n] = dict(n=n, l=l, mean=lam, sd=sd, ts=ts, lPt=lPt, lX=lX, lPm=np.log(np.maximum(tail_mean, 1e-300)))
    return _cache[n]


def best_for_n(n, T, mode, poly='tail'):
    c = curves(n)
    lP = c['lPt'] if poly == 'tail' else c['lPm']
    lhs = (-c['lX'] + lP) if mode == 'fair' else -c['lX']
    ok = lhs >= math.log(T)
    if not ok.any():
        return None
    lcost = math.log(toffoli(n)) - lP
    lcost = np.where(ok, lcost, np.inf)
    i = int(np.argmin(lcost))
    return dict(n=n, l=c['l'], t=int(c['ts'][i]), t_minus_mean_sd=float((c['ts'][i] - c['mean']) / c['sd']),
                P=float(math.exp(lP[i])), runs=float(math.exp(-lP[i])), xp=float(math.exp(-c['lX'][i])),
                fair_ratio=float(math.exp(-c['lX'][i] + lP[i])), toffoli_per_run=toffoli(n),
                toffoli_per_success=float(math.exp(lcost[i])), qubits=qubits(n),
                extrapolated=bool(n < 60 or n > 100))


def design(T, mode, nrange=range(30, 161, 2), poly='tail'):
    rows = [r for n in nrange if (r := best_for_n(n, T, mode, poly))]
    best = min(rows, key=lambda r: r['toffoli_per_success'])
    return best, rows


def naive(T, mode):
    """smallest n whose single run at t = ceil(exact mean) (mean-opt poly) meets the constraint."""
    for n in range(40, 200):
        c = curves(n)
        t = math.ceil(c['mean'])
        i = int(t - c['ts'][0])
        lhs = -c['lX'][i] + (c['lPm'][i] if mode == 'fair' else 0)
        if lhs >= math.log(T):
            Pm = math.exp(c['lPm'][i])
            return dict(n=n, t=t, P=Pm, xp=float(math.exp(-c['lX'][i])), fair_ratio=float(math.exp(-c['lX'][i]) * Pm),
                        toffoli_per_run=toffoli(n), toffoli_per_success=toffoli(n) / Pm, qubits=qubits(n))


if __name__ == '__main__':
    out = dict(toffoli_fit=TOF_C.tolist(), qubit_fit=QB_C.tolist(),
               fit_resid=[float(toffoli(n) / t - 1) for n, t in zip(NS, TOF)])
    for T in (1e20, 1e22, 1e23):
        for mode in ('fair', 'abs'):
            best, rows = design(T, mode)
            bm, _ = design(T, mode, poly='mean')
            nv = naive(T, mode)
            # at paper's n=70
            n70 = best_for_n(70, T, mode)
            key = f'{mode}_{T:.0e}'
            out[key] = dict(best=best, best_meanopt_poly=bm, naive=nv, at_n70=n70,
                            gain_vs_naive=nv['toffoli_per_success'] / best['toffoli_per_success'],
                            frontier=[{k: r[k] for k in ('n', 't', 'P', 'toffoli_per_success', 'xp', 'fair_ratio')} for r in rows])
            print(key, 'BEST', {k: (f'{v:.3g}' if isinstance(v, float) else v) for k, v in best.items()})
            print('   naive', {k: (f'{v:.3g}' if isinstance(v, float) else v) for k, v in nv.items()})
            print('   n70  ', n70 and {k: (f'{v:.3g}' if isinstance(v, float) else v) for k, v in n70.items()})
            print('   mean-opt poly best', bm['n'], bm['t'], f"{bm['toffoli_per_success']:.3g}", ' gain vs naive %.2f' % out[key]['gain_vs_naive'])
    json.dump(out, open('results/finite_size/redesign.json', 'w'), indent=1)
