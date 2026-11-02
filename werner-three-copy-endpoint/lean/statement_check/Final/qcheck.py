import itertools, numpy as np
rng = np.random.default_rng(1)

def q_indep(C, d):
    """independent: reshape to (d,d,d,d,d,d) tensor, einsum partial traces"""
    T = C.reshape([d]*6)
    tot = 0.0
    letters_in, letters_out = 'abc', 'xyz'
    for S in itertools.chain.from_iterable(itertools.combinations(range(3), k) for k in range(4)):
        ins = list(letters_in); outs = list(letters_out)
        for s in S: outs[s] = ins[s]
        keep = ''.join(ins[i] for i in range(3) if i not in S) + ''.join(outs[i] for i in range(3) if i not in S)
        M = np.einsum(''.join(ins)+''.join(outs)+'->'+keep, T)
        tot += (-0.5)**len(S) * np.sum(np.abs(M)**2)
    return tot

def q_lean(C, d):
    """transcription of WernerEndpoint.qfun / partialTrace / merge / frobSq; index x : Fin 3 -> Fin d,
    flattened row-major x0*d^2 + x1*d + x2 (consistent with reshape above)"""
    flat = lambda x: x[0]*d*d + x[1]*d + x[2]
    tot = 0.0
    for mask in range(8):
        S = [r for r in range(3) if mask >> r & 1]
        notS = [r for r in range(3) if r not in S]
        fro = 0.0
        for u in itertools.product(range(d), repeat=len(notS)):
            for v in itertools.product(range(d), repeat=len(notS)):
                acc = 0j
                for z in itertools.product(range(d), repeat=len(S)):
                    def merge(w):
                        x = [None]*3
                        for k, r in enumerate(S): x[r] = z[k]
                        for k, r in enumerate(notS): x[r] = w[k]
                        return x
                    acc += C[flat(merge(u)), flat(merge(v))]
                fro += abs(acc)**2
        tot += (-0.5)**len(S) * fro
    return tot

for d in (1, 2, 3):
    for rank in (1, 2, 3, 8):
        worst = np.inf; maxdiff = 0
        for _ in range(200 if d < 3 else 30):
            n = d**3; r = min(rank, n)
            A = rng.normal(size=(n, r)) + 1j*rng.normal(size=(n, r))
            B = rng.normal(size=(n, r)) + 1j*rng.normal(size=(n, r))
            C = A @ B.conj().T
            a, b = q_indep(C, d), q_lean(C, d)
            maxdiff = max(maxdiff, abs(a-b)/max(1, abs(a)))
            worst = min(worst, a / np.sum(np.abs(C)**2))
        print(f"d={d} rank<={rank}: max rel diff indep vs lean-transcription {maxdiff:.2e}, min q/|C|^2 {worst:.4f}")
c = 2+1j
print("d=1 [c]:", q_lean(np.array([[c]]), 1), abs(c)**2/8)
