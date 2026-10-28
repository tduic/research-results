"""Exact finite-m DQI expected score (Jordan et al. 2408.08292 Thm 4.1):
<f> = m p + sqrt(p(1-p)) * lambda_max(A),  A tridiagonal (l+1)x(l+1), diag k*d (k=0..l), offdiag a_k = sqrt(k(m-k+1)),
d = (1-2p)/sqrt(p(1-p)). Compare with semicircle used by Khattar et al. and recompute XP trials at the exact t."""
import numpy as np, math, json, sys
sys.path.insert(0, 'experiments/dqi_verifiable')
from xp_formula import semicircle, xp_best, prange_logp
from scipy.linalg import eigh_tridiagonal
def dqi_exact(m, l, p):
    d = (1-2*p)/math.sqrt(p*(1-p))
    diag = np.arange(l+1)*d
    off = np.sqrt(np.arange(1, l+1)*(m - np.arange(1, l+1) + 1.0))
    lam = eigh_tridiagonal(diag, off, eigvals_only=True)[-1]
    return m*p + math.sqrt(p*(1-p))*lam
if __name__=='__main__':
    # sanity: large m
    for m in [10**4, 10**6]:
        print("check", m, dqi_exact(m, m//10, 0.3)/m, semicircle(0.1, 0.3))
    rows=[]
    for (m,n,b,r) in [(1023,70,10,496),(4095,60,12,2016),(4095,70,12,2016),(4095,80,12,2016),(4095,100,12,2016)]:
        p=r/2**b; l=n//2
        ts=m*semicircle(l/m,p); te=dqi_exact(m,l,p)
        out=dict(m=m,n=n,b=b,t_semicircle=ts,t_exact=te)
        for lab,t in [("semi",math.ceil(ts)),("exact",math.ceil(te))]:
            lp,al=xp_best(m,n,b,t); out[f"xp_trials_{lab}"]=math.exp(-lp); out[f"prange_trials_{lab}"]=math.exp(-prange_logp(m,n,p,t))
        print(json.dumps(out)); rows.append(out)
    json.dump(rows,open('results/dqi_verifiable/exact_t.json','w'),indent=1)
