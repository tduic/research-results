"""Finite-size DQI deficit (Airy) law + corrected Khattar Table VI.

Deficit D = semicircle - exact mean. Note semicircle(m,l,p) == f(l) := a_l + 2 b_l, the local band edge of the Jacobi
matrix (a_k = mp + (1-2p)k, b_k = sqrt(p(1-p)(k+1)(m-k)) -> continuum sqrt(p(1-p) k (m-k))). The top eigenvalue of the
truncated (l+1)-dim Jacobi matrix sits an Airy distance below the edge (hard wall at k = l):
    D ~= g [ |a1| X + c0 + c1 / X ],   X = (beta/g)^(1/3),
    beta = sqrt(p(1-p) l (m-l)),  g = f'(l) = (1-2p) + sqrt(p(1-p)) (m-2l)/sqrt(l(m-l)).
For l << m: g^(2/3) beta^(1/3) -> sqrt(m p(1-p)) l^(-1/6) = sd_binom * l^(-1/6), so D/sd ~= |a1| l^(-1/6) + c0' l^(-1/2).
"""
import json, math, sys, time
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from dqi_core import (exact_mean, semicircle, A1, dist_from_w, dist_stats, tail_opt_curve, log_xp_success,
                      exact_sd_closed, xp_params, dist_meanopt)

OUT = 'results/finite_size/'
LN10 = math.log(10)


def gbeta(m, l, p):
    sp = math.sqrt(p * (1 - p))
    return (1 - 2 * p) + sp * (m - 2 * l) / math.sqrt(l * (m - l)), sp * math.sqrt(l * (m - l))


def airy_pred(m, l, p, c0, c1, a=A1):
    g, be = gbeta(m, l, p)
    X = (be / g) ** (1 / 3)
    return g * (a * X + c0 + c1 / X)


def grid():
    rows = []
    for e in range(7, 15):
        m = 2 ** e
        for fr in np.geomspace(1e-3, 0.3, 15):
            l = int(round(fr * m))
            if l < 1:
                continue
            for p in [0.05, 0.1, 0.2, 0.3, 0.4, 0.5]:
                lam, w = exact_mean(m, l, p, vec=True)
                sc = semicircle(m, l, p)
                sd = exact_sd_closed(m, l, p, w)
                rows.append(dict(m=m, l=l, lm=l / m, p=p, semicircle=sc, exact=lam, D=sc - lam,
                                 D_over_sdbin=(sc - lam) / math.sqrt(m * p * (1 - p)), sd_dqi=sd,
                                 sd_ratio=sd / math.sqrt(m * p * (1 - p))))
    # dedupe (rounding can repeat l)
    seen, out = set(), []
    for r in rows:
        key = (r['m'], r['l'], r['p'])
        if key not in seen:
            seen.add(key); out.append(r)
    return out


def fit(rows, lmin):
    sel = [r for r in rows if r['l'] >= lmin]
    Y, A = [], []
    for r in sel:
        g, be = gbeta(r['m'], r['l'], r['p'])
        X = (be / g) ** (1 / 3)
        Y.append(r['D'] / g - A1 * X); A.append([1, 1 / X])
    c, *_ = np.linalg.lstsq(np.array(A), np.array(Y), rcond=None)
    errs = [airy_pred(r['m'], r['l'], r['p'], *c) / r['D'] - 1 for r in sel]
    # also leading-only (parameter-free) and l^-1/6 simple form
    lead = [airy_pred(r['m'], r['l'], r['p'], 0, 0) / r['D'] - 1 for r in sel]
    return dict(lmin=lmin, c0=float(c[0]), c1=float(c[1]), n=len(sel), max_rel_err=float(np.max(np.abs(errs))),
                rms_rel_err=float(np.sqrt(np.mean(np.square(errs)))), leading_only_max_rel_err=float(np.max(np.abs(lead))))


def simple_fit(rows, lmin):
    """D/sd_binom = |a1| l^-1/6 + c l^-1/2 (small-l/m form)."""
    sel = [r for r in rows if r['l'] >= lmin and r['lm'] <= 0.05]
    Y = np.array([r['D_over_sdbin'] - A1 * r['l'] ** (-1 / 6) for r in sel])
    Xs = np.array([r['l'] ** (-0.5) for r in sel])
    c = float((Xs @ Y) / (Xs @ Xs))
    err = [(A1 * r['l'] ** (-1 / 6) + c * r['l'] ** -0.5) / r['D_over_sdbin'] - 1 for r in sel]
    return dict(lmin=lmin, lm_max=0.05, c=c, n=len(sel), max_rel_err=float(np.max(np.abs(err))))


TABLE_VI = [  # (m, n, b, r, Toffoli, Clifford, qubits, Prange, XP)
    (1023, 60, 10, 496, 2.76e6, 3.89e7, 1364, 5.49e19, 1.92e15),
    (1023, 70, 10, 496, 3.59e6, 4.91e7, 1569, 1.26e22, 4.64e16),
    (1023, 80, 10, 496, 4.52e6, 6.04e7, 1769, 4.30e24, 1.22e18),
    (1023, 90, 10, 496, 5.56e6, 7.30e7, 1970, 1.07e27, 2.08e19),
    (1023, 100, 10, 496, 6.71e6, 8.68e7, 2170, 1.75e29, 2.56e20),
    (4095, 60, 12, 2016, 4.64e6, 1.27e8, 1640, 2.02e23, 4.02e20),
    (4095, 70, 12, 2016, 5.72e6, 1.52e8, 1885, 4.75e26, 1.97e23),
    (4095, 80, 12, 2016, 6.92e6, 1.79e8, 2125, 9.48e29, 7.99e25),
    (4095, 90, 12, 2016, 8.27e6, 2.08e8, 2366, 1.41e33, 2.27e28),
    (4095, 100, 12, 2016, 9.75e6, 2.41e8, 2606, 2.10e36, 5.91e30),
]


def table_row(m, n, b, r, tof, cliff, qb, prange, xp_paper):
    p = r / 2 ** b
    l = n // 2
    sc = semicircle(m, l, p)
    t_pap = int(round(sc))
    pi, lam = dist_meanopt(m, l, p)
    st = dist_stats(pi)
    t_lo = int(lam - 6 * st['sd'])
    ts, lP_tail = tail_opt_curve(m, l, p, t_lo, m)
    lX = log_xp_success(m, n, b, ts)          # log P_XP
    cdf_tail = np.cumsum(pi[::-1])[::-1]       # P_meanopt(s>=t)
    lP_mean = np.log(np.maximum(cdf_tail[ts], 1e-300))
    lr_tail = (lP_tail - lX) / LN10
    lr_mean = (lP_mean - lX) / LN10
    idx = lambda t: int(t - ts[0])
    t_mean = math.ceil(lam)
    # one-shot: largest t with P_tail >= 1/2; capped: largest t with P_tail >= floor
    def cap(floor):
        ok = np.where(lP_tail >= math.log(floor))[0]
        i = ok[-1]
        return dict(t=int(ts[i]), P=float(math.exp(lP_tail[i])), xp=float(math.exp(-lX[i])), log10_ratio=float(lr_tail[i]))
    imax = int(np.argmax(lr_tail))
    mono = bool(np.all(np.diff(lr_tail[idx(t_mean):]) > -1e-9))
    return dict(
        m=m, n=n, b=b, r=r, l=l, toffoli=tof, qubits=qb, paper_xp=xp_paper, paper_prange=prange,
        t_semicircle=sc, t_paper=t_pap, exact_mean=lam, deficit=sc - lam, sd=st['sd'], median=st['median'],
        xp_at_paper_t=float(math.exp(-lX[idx(t_pap)])),
        xp_at_exact_mean=float(math.exp(-lX[idx(t_mean)])), P_meanopt_at_ceil_mean=float(cdf_tail[t_mean]),
        P_meanopt_paper_t=float(math.exp(lP_mean[idx(t_pap)])), P_tailopt_paper_t=float(math.exp(lP_tail[idx(t_pap)])),
        ratio_paper_t_meanopt=float(10 ** lr_mean[idx(t_pap)]), ratio_paper_t_tailopt=float(10 ** lr_tail[idx(t_pap)]),
        oneshot=cap(0.5), cap_1e2=cap(1e-2), cap_1e3=cap(1e-3), cap_1e6=cap(1e-6),
        sup=dict(t=int(ts[imax]), log10_ratio=float(lr_tail[imax]), log10_P=float(lP_tail[imax] / LN10)),
        ratio_monotone_in_t=mono,
        prange_at_exact_mean=None,
    )


if __name__ == '__main__':
    t0 = time.time()
    rows = grid()
    fits = [fit(rows, lm) for lm in (1, 3, 5, 10)]
    sfits = [simple_fit(rows, lm) for lm in (5, 20)]
    # distribution shape on a sub-grid (sd and skew of mean-opt DQI law)
    shape = []
    for m in (512, 4096, 16384):
        for fr in (0.003, 0.03, 0.3):
            l = max(2, int(fr * m))
            for p in (0.1, 0.5):
                try:
                    pi, lam = dist_meanopt(m, l, p)
                except RuntimeError:
                    continue
                st = dist_stats(pi)
                sc = semicircle(m, l, p)
                shape.append(dict(m=m, l=l, p=p, mean=st['mean'], eig=lam, sd_over_sdbin=st['sd'] / math.sqrt(m * p * (1 - p)),
                                  skew=st['skew'], P_ge_semicircle=float(pi[math.ceil(sc):].sum())))
    table = [table_row(*row) for row in TABLE_VI]
    json.dump(dict(grid=rows, fits=fits, simple_fits=sfits, shape=shape, table=table, secs=time.time() - t0),
              open(OUT + 'airy_deficit.json', 'w'), indent=1)
    for f in fits: print('fit', f)
    for f in sfits: print('simple', f)
    for s in shape: print('shape', {k: (round(v, 4) if isinstance(v, float) else v) for k, v in s.items()})
    print('%-22s %8s %8s %6s %9s %9s %9s %9s %16s %16s %16s %14s' % ('row', 't_pap', 'mean', 'D', 'XPpaper', 'XP@mean',
          'R@t_tail', 'R@1shot', 'R@P>=1e-2 (t)', 'R@P>=1e-3 (t)', 'R@P>=1e-6 (t)', 'sup(t)'))
    for T in table:
        print('%-22s %8d %8.1f %6.1f %9.2e %9.2e %9.2e %9.2e %9.2e (%d) %9.2e (%d) %9.2e (%d) 1e%.0f (%d) mono=%s' % (
            (T['m'], T['n'], T['b'], T['r']), T['t_paper'], T['exact_mean'], T['deficit'], T['paper_xp'], T['xp_at_exact_mean'],
            T['ratio_paper_t_tailopt'], 10 ** T['oneshot']['log10_ratio'], 10 ** T['cap_1e2']['log10_ratio'], T['cap_1e2']['t'],
            10 ** T['cap_1e3']['log10_ratio'], T['cap_1e3']['t'], 10 ** T['cap_1e6']['log10_ratio'], T['cap_1e6']['t'],
            T['sup']['log10_ratio'], T['sup']['t'], T['ratio_monotone_in_t']))
    print('secs', time.time() - t0)
