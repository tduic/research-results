"""Exhaustive check of the finite-size DQI expectation on tiny TBT-OPI instances.
Enumerate all q^n polynomials -> exact score histogram H(j). DQI state amplitude P(f(x)), P degree-l polynomial in f.
Optimal P maximises sum_j H(j) P(j)^2 j / sum_j H(j) P(j)^2 = top generalized eigenvalue on degree-<=l polys under H.
Compare: (i) exact optimum under the TRUE histogram, (ii) Jordan et al. eigen formula (binomial moments),
(iii) asymptotic semicircle used by Khattar et al."""
import numpy as np, itertools, math, json, sys
sys.path.insert(0,'experiments/dqi_verifiable')
from dqi_exact_t import dqi_exact
from xp_formula import semicircle
prim={4:0x13,6:0x43,8:0x11d}
def field(b):
    q=1<<b; exp=[0]*(2*q); log=[0]*q; x=1
    for i in range(q-1):
        exp[i]=x; log[x]=i; x<<=1
        if x&q: x^=prim[b]
    for i in range(q-1,2*q): exp[i]=exp[i-(q-1)]
    return exp,log
def instance(b,seed):
    rng=np.random.default_rng(seed); k=b//2; q=1<<b; m=q-1
    def inS(w): return bin((w&((1<<k)-1)) & (w>>k)).count('1')&1
    mem=np.zeros((m,q),bool)
    for a in range(m):
        while True:
            M=rng.integers(0,2,(b,b))
            if round(abs(np.linalg.det(M)))%2==1: break   # det odd -> invertible mod 2
        # F_a = A S : v in F iff A^{-1} v in S ; equivalently mem[v] = inS(Minv v); just use M as A^{-1} (uniform GL too)
        for v in range(q):
            bits=np.array([(v>>i)&1 for i in range(b)]); w=(M@bits)%2
            mem[a,v]=inS(int(sum(int(w[i])<<i for i in range(b))))
    return mem
def scores_all(b,n,mem):
    exp,log=field(b); q=1<<b; m=q-1
    # values table: for each point a (alpha=exp[a]) and each coefficient position j, multiplication table c*alpha^j
    mul=np.zeros((q,q),np.int64)
    for x in range(1,q):
        for y in range(1,q): mul[x,y]=exp[log[x]+log[y]]
    sc=np.zeros(q**n,np.int32)
    coeffs=np.array(list(itertools.product(range(q),repeat=n)))  # q^n x n
    for a in range(m):
        al=exp[a]; v=np.zeros(len(coeffs),np.int64)
        for j in range(n):
            aj=exp[(a*j)%(q-1)] if j>0 else 1
            v^=mul[coeffs[:,j],aj]
        sc+=mem[a][v]
    return sc
def best_mean(H, l):
    j=np.arange(len(H),dtype=float); w=H/H.sum()
    V=np.vander(j-j.mean(),l+1,increasing=True)
    G=V.T@(w[:,None]*V); F=V.T@((w*j)[:,None]*V)
    from scipy.linalg import eigh
    return eigh(F,G,eigvals_only=True)[-1]

def main():
    out=[]
    for (b,n,seeds) in [(4,4,[1,2]),(4,5,[1,2]),(6,3,[1,2])]:
        q=1<<b; m=q-1; k=b//2; r=2**(2*k-1)-2**(k-1); rho=r/q
        for s in seeds:
            mem=instance(b,s); assert all(mem[a].sum()==r for a in range(m))
            sc=scores_all(b,n,mem); H=np.bincount(sc,minlength=m+1).astype(float)
            for l in range(1,n//2+1):
                ex=best_mean(H,l); jf=dqi_exact(m,l,rho); sm=m*semicircle(l/m,rho)
                row=dict(b=b,n=n,seed=s,l=l,cond_2l1_lt_dperp=(2*l+1<n+1),exact_true_hist=ex,eig_formula=jf,semicircle=sm,
                         max_score=int(sc.max()))
                print(row); out.append(row)
    json.dump(out,open('results/dqi_verifiable/tiny_dqi_exact.json','w'),indent=1)


if __name__ == '__main__':
    main()
