"""DQI score distribution for OPI with |F|=r, perfect decoding (2l+1<d_perp regime; we also allow l=n/2 as the paper does).
DQI state  sum_x P(f(x))|x>.  If the score histogram of the instance is ~ q^n Binom(m,rho) (true for moments < d_perp),
Pr_DQI[f=j] = P(j)^2 Binom(m,rho)(j) with P = sum_k w_k p_k (Krawtchouk orthonormal), w = top eigvec of the
(l+1) Jacobi matrix.  Full Jacobi matrix (m+1) gives the quadrature nodes j=0..m exactly.
Outputs P_DQI(f>=t) and XP / Prange trials vs t, and 'advantage ratio' = XP_trials(t) * P_DQI(f>=t)."""
import numpy as np, math, json, sys
sys.path.insert(0, 'experiments/dqi_verifiable')
from xp_formula import xp_best, prange_logp, semicircle
from scipy.linalg import eigh_tridiagonal
from scipy.stats import binom

def dqi_dist(m, l, rho):
    # Jacobi matrix for Binomial(m,rho) in score units: diag_k = m rho + k(1-2rho), off_k = sqrt(rho(1-rho) k (m-k+1))
    k = np.arange(m+1)
    diag = m*rho + k*(1-2*rho)
    off = np.sqrt(rho*(1-rho)*np.arange(1, m+1)*(m - np.arange(1, m+1) + 1.0))
    # top eigvec of truncated (l+1)
    ev, W = eigh_tridiagonal(diag[:l+1], off[:l], select='i', select_range=(l, l))
    w = W[:, 0]
    # orthonormal polynomials p_k(j) via recurrence, evaluate at j=0..m (log-stable: compute with binomial weight sqrt)
    j = np.arange(m+1, dtype=float)
    sw = np.sqrt(binom.pmf(j, m, rho))
    # psi_k(j) = p_k(j)*sqrt(w(j)); recurrence off_k psi_k = (j - diag_{k-1}) psi_{k-1} - off_{k-1} psi_{k-2}
    psi_prev = np.zeros(m+1); psi = sw.copy()
    amp = w[0]*psi
    for kk in range(1, l+1):
        nxt = ((j - diag[kk-1])*psi - (off[kk-2] if kk >= 2 else 0)*psi_prev)/off[kk-1]
        psi_prev, psi = psi, nxt
        amp += w[kk]*psi
    pr = amp**2
    return ev[0], pr/pr.sum(), pr.sum()

if __name__ == "__main__":
    out = []
    for (m, n, b, r) in [(1023,70,10,496),(4095,60,12,2016),(4095,70,12,2016),(4095,100,12,2016)]:
        rho = r/2**b
        for l in sorted(set([n//2 - 1, n//2])):
            mean, pr, norm = dqi_dist(m, l, rho)
            j = np.arange(m+1); mu = (j*pr).sum(); sd = math.sqrt(((j-mu)**2*pr).sum())
            tsemi = math.ceil(m*semicircle((n//2)/m, rho))
            rows = []
            for t in range(int(mu)-10, tsemi+60, 5 if m>2000 else 3):
                pq = pr[t:].sum()
                lx, _ = xp_best(m, n, b, t)
                rows.append(dict(t=t, P_dqi=pq, xp_trials=math.exp(-lx), xp_per_dqi_success=math.exp(-lx)*pq))
            res = dict(m=m, n=n, b=b, l=l, dqi_mean_eig=mean, dqi_mean=mu, dqi_sd=sd, norm=norm, t_semi=tsemi,
                       P_dqi_at_tsemi=pr[tsemi:].sum(), rows=rows)
            print(m, n, b, l, "mean", round(mean,2), round(mu,2), "sd", round(sd,2), "norm", round(norm,6),
                  "t_semi", tsemi, "P_DQI(>=t_semi)", "%.3g" % pr[tsemi:].sum())
            for rw in rows[::2]: print("   t=%d P_dqi=%.3g XP=%.3g XP*P=%.3g" % (rw['t'], rw['P_dqi'], rw['xp_trials'], rw['xp_per_dqi_success']))
            out.append(res)
    json.dump(out, open('results/dqi_verifiable/dqi_distribution.json','w'), indent=1)
