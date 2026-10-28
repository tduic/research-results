# Google's verifiable DQI instance: a finite-size correction

> **Status:** Complete (October 2026) · re-derived independently and red-teamed · regression tests in [`tests/test_dqi_finite_size.py`](../tests/test_dqi_finite_size.py)
>
> **Paper:** [Finite-size corrections to the classical cost of a verifiable decoded-quantum-interferometry advantage](paper/main.pdf) ([LaTeX source](paper/main.tex))

## Bottom line

Khattar et al. ([arXiv 2510.10967](https://arxiv.org/abs/2510.10967)) propose Decoded Quantum Interferometry (DQI) on polynomial intersection over GF(2¹²) as a verifiable quantum-advantage experiment, at about 5.7 million Toffoli gates, and report that the best classical attack (extended Prange, "XP") needs 1.97×10²³ trials.

That classical figure scores the attacker against a target the quantum algorithm rarely reaches. The paper sets the target score with the asymptotic semicircle law; at this finite size DQI falls short of it by a predictable amount. Measured fairly — classical trials per quantum run — **every row of the paper's Table VI overstates the classical gap by 14–18.5× (16.8× at the headline instance).** The advantage itself survives, and a modestly larger instance restores the claimed margin.

- **At the headline instance** (m = 4095, n = 70, ℓ = 35), the paper's target is t = 2,393. The DQI score has mean 2,359.7, median 2,362 and standard deviation 31.8 (from the score law below); one run reaches 2,393 only about 3% of the time (6% with the polynomial re-optimized for the tail), so it takes about 17 runs.
- **The shortfall follows a simple law.** Truncating DQI's enhancing polynomial at degree ℓ acts like a hard wall at the edge of a Jacobi spectrum, so the top eigenvalue sits an Airy distance below the semicircle edge. A law with the first Airy zero |a₁| = 2.338 fixed and two fitted correction terms predicts the shortfall within 4.3% (1.2% rms) over 588 grid points with m = 2⁷…2¹⁴, and within 1.1% on a fresh grid with m = 2¹⁵…2¹⁸ that was not used in the fit. At the headline instance it predicts 33.4 against 33.2 from the Jacobi matrix.
- **The fix is a bigger instance, not repetition.** Classical cost grows 260–490× per +10 in n while the Toffoli count grows about 1.2×. The cheapest design reaching 10²³ classical trials per quantum success is **n = 96 at 90% success: about 9.1 million Toffoli gates per run (10.2 million per success) and 2,510 logical qubits.** Keeping n = 70 and repeating needs about 67 runs, 38× worse.

The paper's asymptotic theorem is unaffected; only its concrete Table VI numbers shift.

## Method

**Finite-size score law.** For a DQI run with enhancing-polynomial weights w of degree ≤ ℓ, the model score law is π(s) = Binom(m, p)(s) · (Σₖ wₖ eₖ(s))², where eₖ are the Krawtchouk polynomials orthonormal under Binom(m, p) and p is the target density. Its mean is exact when 2ℓ + 1 is below the dual distance (n + 1). Its tail probabilities are exact for the paper's random-instance ensemble (averaged over the twist they agree to 10⁻¹⁴ at the Table VI instances), while an individual instance's tails fluctuate slightly around them (0.181–0.184 against 0.182 on small exhaustive instances; [`results/finite_size/score_law_check.json`](results/finite_size/score_law_check.json)). The paper's ℓ = n/2 is the borderline case, where the mean picks up a correction that exhaustive checks on tiny instances put within 0.016 ([`results/dqi_verifiable/`](results/dqi_verifiable/)); it is not bounded at the Table VI sizes. The mean-optimal w is the top eigenvector of an (ℓ+1)×(ℓ+1) Jacobi matrix, whose eigenvalue is the expected score; the tail-optimal w for P(s ≥ t) is the top eigenvector of a truncated Gram matrix.

**Independent derivations.** The exact mean was first computed from the expected-score theorem of Jordan et al. ([`experiments/dqi_verifiable/dqi_exact_t.py`](experiments/dqi_verifiable/dqi_exact_t.py)). A red team then re-derived the full score law separately, from a multilinear identity on the constraint indicators, in 60-digit arithmetic ([`experiments/dqi_verifiable/r4_redteam_exact.py`](experiments/dqi_verifiable/r4_redteam_exact.py)). The production code ([`experiments/finite_size/dqi_core.py`](experiments/finite_size/dqi_core.py)) implements the red team's derivation in float64 with a log-scaled recurrence, for speed at large m. The tests check all three against each other.

**Classical cost.** XP trial counts are reproduced from the paper's formula by two separate codes, matching all eight Table VI rows checked to the paper's three significant figures (1.966×10²³ at the headline point; [`results/dqi_verifiable/xp_table.json`](results/dqi_verifiable/xp_table.json)).

**The fair comparison.** For each row, the paper's classical trial count at its target t is divided by the number of quantum runs needed to reach t once with the tail-optimal polynomial. That is the classical cost per quantum run; the published figure is larger by exactly that number of runs.

**The Airy law.** With β = √(p(1−p)ℓ(m−ℓ)), g = (1−2p) + √(p(1−p))·(m−2ℓ)/√(ℓ(m−ℓ)) and X = (β/g)^(1/3),

```
D ≈ g · ( 2.338·X − 1.46 + 0.137/X )
```

where D is the semicircle value minus the top Jacobi eigenvalue. The leading term is the classical Airy edge asymptotic for the extreme zeros of Krawtchouk- and Hermite-type orthogonal polynomials, so it is not new; what is new here is its use for DQI, the two fitted corrections (constants fitted on m = 2⁷…2¹⁴, ℓ ≥ 3, ℓ/m from 0.001 to 0.3, p from 0.05 to 0.5; [`results/finite_size/airy_deficit.json`](results/finite_size/airy_deficit.json), `fits`) and the audit. The leading term alone is off by up to 82% at small ℓ, so the corrections matter. This is an empirical law, not a theorem.

## Results

| Instance (m, n) | Paper's classical trials | Classical trials per quantum run | Overstatement (= quantum runs needed to reach t) |
|---|---|---|---|
| 1023, 60 | 1.92×10^15 | 1.25×10^14 | 15.4× |
| 1023, 70 | 4.64×10^16 | 3.30×10^15 | 14.0× |
| 1023, 80 | 1.22×10^18 | 7.58×10^16 | 16.1× |
| 1023, 90 | 2.08×10^19 | 1.17×10^18 | 17.9× |
| 1023, 100 | 2.56×10^20 | 1.39×10^19 | 18.5× |
| 4095, 60 | 4.02×10^20 | 2.51×10^19 | 16.0× |
| **4095, 70 (headline)** | 1.97×10^23 | 1.17×10^22 | **16.8×** |
| 4095, 80 | 7.99×10^25 | 4.58×10^24 | 17.5× |
| 4095, 90 | 2.27×10^28 | 1.31×10^27 | 17.3× |
| 4095, 100 | 5.91×10^30 | 3.32×10^29 | 17.8× |

Per-row numbers: [`results/finite_size/airy_deficit.json`](results/finite_size/airy_deficit.json) (`table`). Redesign search: [`results/finite_size/redesign.json`](results/finite_size/redesign.json).

## Caveats

- Resource counts (Toffoli gates, logical qubits) for the redesigned instances are interpolated from the paper's own table (fit residuals below 0.1%), not compiled circuits.
- The comparison assumes the attacker is measured against the score a quantum run actually reaches; other operational definitions of "advantage" shift the factor but not the conclusion that the asymptotic target is too generous at this size.

## Reproducing

From this folder (Python 3, NumPy, SciPy, mpmath):

```
python experiments/finite_size/airy_deficit.py          # Airy fit + corrected Table VI (~10 s)
python experiments/finite_size/redesign.py              # cheapest redesign
python experiments/dqi_verifiable/r4_redteam_exact.py   # independent 60-digit re-derivation
python experiments/dqi_verifiable/dqi_exact_t.py        # exact mean from the expected-score theorem
```
