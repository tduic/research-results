"""How exact is the binomial-model score law (paper eq. 1)?

(a) Instance-averaged: averaging over the random twist of the instance, the score histogram of a uniformly
    random assignment is a mixture over the number z of roots of Q in F_q^* (indicator 0 there) of
    Binomial(m - z, r/(q-1)). This compares the resulting DQI law with the binomial model at the Table VI instances.
(b) Per instance: on tiny instances (b = 4, n = 5, l = 2) the true histogram is enumerated exhaustively and the
    DQI law H(s) * P(s)^2 compared with the model for the mean and the tail probabilities.

Run from dqi-finite-size/:  python experiments/finite_size/score_law_check.py
"""
import json
import math
import os
import sys

import numpy as np
from scipy.special import logsumexp
from scipy.stats import binom

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, "..", "dqi_verifiable")]
import dqi_core as dc  # noqa: E402
import tiny_dqi_exact as tiny  # noqa: E402

OUT = os.path.join(HERE, "..", "..", "results", "finite_size", "score_law_check.json")


def averaged(m, b, r, l, ts):
    q = m + 1
    p, pp = r / q, r / (q - 1)
    lam, w = dc.exact_mean(m, l, p, vec=True)
    LM, SG = dc.psi_table(m, l, p)
    s = np.arange(m + 1)
    lB = binom.logpmf(s, m, p)
    comb = np.einsum("k,ks->s", w, np.exp(LM) * SG)
    lpi = np.log(np.maximum(comb ** 2, 1e-300))
    zs = np.arange(0, 15)
    lpz = binom.logpmf(zs, m, 1 / q)
    lH = logsumexp(np.array([lpz[j] + binom.logpmf(s, m - zs[j], pp) for j in range(len(zs))]), axis=0)
    pim = np.exp(lpi)
    pim /= pim.sum()
    lpa = lpi + lH - lB
    pia = np.exp(lpa - lpa.max())
    pia /= pia.sum()
    return dict(m=m, l=l, mean_model=float((s * pim).sum()), mean_avg=float((s * pia).sum()),
                tails={str(t): [float(pim[t:].sum()), float(pia[t:].sum())] for t in ts})


def per_instance(b=4, n=5, l=2, seeds=range(1, 9)):
    q = 2 ** b
    m = q - 1
    r = 2 ** (b - 1) - 2 ** (b // 2 - 1)
    p = r / q
    lam, w = dc.exact_mean(m, l, p, vec=True)
    LM, SG = dc.psi_table(m, l, p)
    psi = np.exp(LM) * SG
    B = binom.pmf(np.arange(m + 1), m, p)
    amp = (w @ psi) / np.sqrt(B)
    s = np.arange(m + 1)
    model = B * amp ** 2
    model /= model.sum()
    rows = []
    for seed in seeds:
        mem = tiny.instance(b, seed)
        H = np.bincount(tiny.scores_all(b, n, mem), minlength=m + 1).astype(float)
        tr = H * amp ** 2
        tr /= tr.sum()
        rows.append(dict(seed=seed, mean=float((s * tr).sum()),
                         tails={str(t): float(tr[t:].sum()) for t in (10, 11, 12)}))
    return dict(b=b, n=n, l=l, model_mean=float((s * model).sum()),
                model_tails={str(t): float(model[t:].sum()) for t in (10, 11, 12)}, instances=rows)


def main():
    out = dict(averaged=[averaged(4095, 12, 2016, 35, [2360, 2380, 2393, 2410]),
                         averaged(1023, 10, 496, 35, [682, 690])],
               per_instance=per_instance())
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps(out, indent=1)[:1500])


if __name__ == "__main__":
    main()
