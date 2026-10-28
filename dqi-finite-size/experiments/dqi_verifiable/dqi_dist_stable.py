"""Stable DQI score distribution via full Jacobi-matrix eigendecomposition (Gauss quadrature of Binomial(m,rho)).
Nodes of the (m+1) Jacobi matrix = j=0..m; eigvec components = p_k(j) sqrt(w_j). Pr_DQI(j) = (sum_k w_k p_k(j) sqrt(w_j))^2.
Valid when the instance's score histogram matches Binomial moments to degree 2l+1 (needs 2l+1 < d_perp = n+1)."""
import numpy as np, math, sys, json
from scipy.linalg import eigh_tridiagonal
def dist(m,l,rho):
    k=np.arange(m+1); diag=m*rho+k*(1-2*rho); off=np.sqrt(rho*(1-rho)*np.arange(1,m+1)*(m-np.arange(1,m+1)+1.0))
    lam,V=eigh_tridiagonal(diag,off)                         # V[k, node]
    ev,W=eigh_tridiagonal(diag[:l+1],off[:l],select='i',select_range=(l,l)); w=W[:,0]
    amp=w@V[:l+1,:]; pr=amp**2
    nodes=np.rint(lam).astype(int)
    return lam,pr,ev[0]
if __name__=="__main__":
    out={}
    for (m,n,b,r) in [(4095,70,12,2016),(1023,70,10,496),(4095,100,12,2016)]:
        rho=r/2**b; l=n//2
        lam,pr,mean_eig=dist(m,l,rho)
        mu=(lam*pr).sum(); sd=math.sqrt(((lam-mu)**2*pr).sum())
        print(m,n,b,"l",l,"mean",round(mu,2),"(eig %.2f)"%mean_eig,"sd",round(sd,2),"nodes integer?",np.allclose(lam,np.rint(lam),atol=1e-6))
        tails={}
        for t in [int(mu)-20,int(mu),int(mu)+10,int(mu)+20,int(mu)+33,int(mu)+50,int(mu)+80]:
            tails[t]=float(pr[lam>=t-1e-6].sum()); print("   P(f>=%d)=%.4g"%(t,tails[t]))
        out[f"{m}_{n}_{b}"]=dict(mean=mu,sd=sd,tails=tails)
    json.dump(out,open('results/dqi_verifiable/dqi_dist_stable.json','w'),indent=1)
