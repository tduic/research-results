"""Best DQI single-run success probability Pr[f>=t] over ALL degree-l enhancing polynomials P
(generalized eigenproblem in the orthonormal Krawtchouk basis via full Jacobi quadrature), and the fair
'classical XP trials per DQI run' = XP_trials(t) * Pmax_DQI(t)."""
import numpy as np, math, json, sys
from scipy.linalg import eigh_tridiagonal, eigh
sys.path.insert(0,'experiments/dqi_verifiable')
from xp_formula import xp_best, semicircle
def basis(m,rho):
    k=np.arange(m+1); diag=m*rho+k*(1-2*rho); off=np.sqrt(rho*(1-rho)*np.arange(1,m+1)*(m-np.arange(1,m+1)+1.0))
    lam,V=eigh_tridiagonal(diag,off); return np.rint(lam).astype(int),V
out=[]
for (m,n,b,r) in [(4095,70,12,2016),(4095,60,12,2016),(4095,100,12,2016),(1023,70,10,496)]:
    rho=r/2**b; l=n//2; nodes,V=basis(m,rho); Vl=V[:l+1,:]
    tsemi=int(round(m*semicircle(l/m,rho)))
    for t in sorted(set([tsemi-40,tsemi-30,tsemi-20,tsemi-10,tsemi,tsemi+10,tsemi+20,tsemi+40,tsemi+60])):
        mask=nodes>=t; T=Vl[:,mask]@Vl[:,mask].T
        pmax=eigh(T,eigvals_only=True)[-1]
        # mean-optimal P
        J=(Vl*nodes)@Vl.T; ev,W=eigh(J); w=W[:,-1]; amp=w@Vl; pmean=float((amp**2)[mask].sum())
        xp=math.exp(-xp_best(m,n,b,t)[0])
        row=dict(m=m,n=n,b=b,l=l,t=t,t_semi=tsemi,P_meanopt=pmean,P_tailopt=float(pmax),xp=xp,
                 xp_per_run_meanopt=xp*pmean,xp_per_run_tailopt=xp*float(pmax))
        print("%d %d t=%d (semi %d) Pmeanopt=%.3g Ptailopt=%.3g XP=%.3g  XP*Ptail=%.3g"%(m,n,t,tsemi,pmean,pmax,xp,xp*pmax),flush=True)
        out.append(row)
json.dump(out,open('results/dqi_verifiable/dqi_tail_opt.json','w'),indent=1)
