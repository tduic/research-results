"""Checks for dqi-finite-size/: the exact finite-size DQI score law, the Airy shortfall law,
the corrected Table VI ratios and the n = 96 redesign."""
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import pytest

import dqi_core
import r4_redteam_exact as rt
import airy_deficit as ta

ROOT = Path(__file__).resolve().parent.parent / "dqi-finite-size" / "results"
TASK_A = json.load(open(ROOT / "finite_size" / "airy_deficit.json"))
TASK_B = json.load(open(ROOT / "finite_size" / "redesign.json"))
REDTEAM = json.load(open(ROOT / "dqi_verifiable" / "r4_redteam_exact.json"))

# Google's headline instance (Khattar et al., arXiv 2510.10967): GF(2^12), m = 4095, n = 70, l = 35, r = 2016
M, L, P = 4095, 35, 2016 / 2 ** 12


def test_independent_derivations_agree():
    """Exact mean three ways: Jordan et al.'s expected-score theorem (dqi_exact_t), the red team's
    independent 60-digit re-derivation (r4_redteam_exact), and the float64 production code (dqi_core)."""
    import dqi_exact_t
    for m, l, p in [(127, 5, 0.3), (255, 12, 0.49), (511, 20, 0.1), (M, L, P)]:
        theorem = dqi_exact_t.dqi_exact(m, l, p)
        fast = dqi_core.exact_mean(m, l, p)
        assert abs(theorem - fast) < 1e-7 * m
        if m < 1000:
            ev = mp.eig(rt.jacobi(m, l, mp.mpf(p)), left=False, right=False)
            slow = float(max(mp.re(z) for z in ev))
            assert abs(theorem - slow) < 1e-8 * m and abs(fast - slow) < 1e-8 * m


def test_headline_instance_exact_mean_and_shortfall():
    lam, w = dqi_core.exact_mean(M, L, P, vec=True)
    sc = dqi_core.semicircle(M, L, P)
    assert round(sc) == 2393                       # the paper's target t
    assert lam == pytest.approx(2359.747, abs=0.01)
    assert dqi_core.exact_sd_closed(M, L, P, w) == pytest.approx(31.79, abs=0.01)
    assert sc - lam == pytest.approx(33.22, abs=0.01)
    assert REDTEAM["l35"]["top_eig"] == pytest.approx(lam, abs=1e-6)  # independent derivation
    assert 0.02 < REDTEAM["l35"]["tails"]["2393"] < 0.06              # one run reaches t only a few % of the time


def test_airy_law_at_headline():
    fit = next(f for f in TASK_A["fits"] if f["lmin"] == 3)
    pred = ta.airy_pred(M, L, P, fit["c0"], fit["c1"])
    exact = dqi_core.semicircle(M, L, P) - dqi_core.exact_mean(M, L, P)
    assert pred == pytest.approx(33.4, abs=0.05)
    assert abs(pred - exact) / exact < 0.01


def test_airy_law_on_fresh_points():
    """Points not in the fit grid (odd m, other densities): within the stated 4.3 % envelope."""
    fit = next(f for f in TASK_A["fits"] if f["lmin"] == 3)
    assert fit["max_rel_err"] < 0.045 and fit["rms_rel_err"] < 0.013
    rng = np.random.default_rng(7)
    for _ in range(40):
        m = int(rng.integers(300, 6000)) | 1
        l = max(3, int(m * rng.uniform(0.002, 0.25)))
        p = float(rng.uniform(0.07, 0.5))
        exact = dqi_core.semicircle(m, l, p) - dqi_core.exact_mean(m, l, p)
        pred = ta.airy_pred(m, l, p, fit["c0"], fit["c1"])
        assert abs(pred - exact) / exact < 0.05, (m, l, p, exact, pred)


def test_xp_trials_reproduce_paper():
    assert REDTEAM["xp_t2393"] == pytest.approx(1.97e23, rel=0.01)
    rows = json.load(open(ROOT / "dqi_verifiable" / "xp_table.json"))
    assert len(rows) == 8
    for r in rows:
        assert float("%.3g" % r["xp_trials"]) == r["table_xp"]  # matches the published 3 significant figures


def test_table_vi_overstatement_range():
    """Overstatement = quantum runs needed to reach the paper's t with the tail-optimal polynomial, every row."""
    ratios = {(r["m"], r["n"]): 1 / r["P_tailopt_paper_t"] for r in TASK_A["table"]}
    assert len(ratios) == 10
    assert min(ratios.values()) == pytest.approx(14.0, abs=0.1)
    assert max(ratios.values()) == pytest.approx(18.5, abs=0.1)
    assert ratios[(4095, 70)] == pytest.approx(16.8, abs=0.1)
    # independent red-team value at the headline instance
    assert 1 / REDTEAM["l35_tailopt_2393"]["P"] == pytest.approx(16.8, abs=0.1)


def test_airy_law_held_out_large_m():
    """Fresh points at m = 2^15 .. 2^18, outside the fitted grid (m <= 2^14): within 1 %."""
    fit = next(f for f in TASK_A["fits"] if f["lmin"] == 3)
    assert max(r["m"] for r in TASK_A["grid"]) <= 2 ** 14
    rng = np.random.default_rng(2026)
    errs = []
    for _ in range(40):
        m = int(2 ** rng.uniform(15, 18))
        l = max(3, int(m * rng.uniform(0.001, 0.3)))
        p = float(rng.uniform(0.05, 0.5))
        exact = dqi_core.semicircle(m, l, p) - dqi_core.exact_mean(m, l, p)
        errs.append(abs(ta.airy_pred(m, l, p, fit["c0"], fit["c1"]) - exact) / exact)
    assert max(errs) < 0.01


def test_n96_redesign():
    best = TASK_B["fair_1e+23"]["best"]
    assert best["n"] == 96 and best["P"] >= 0.9
    assert best["fair_ratio"] >= 1e23
    assert best["toffoli_per_run"] == pytest.approx(9.14e6, rel=0.01)
    assert best["toffoli_per_success"] == pytest.approx(1.02e7, rel=0.01)
    assert round(best["qubits"]) == 2510


def test_score_law_check():
    """Model score law vs the twist-averaged instance ensemble (exact) and individual tiny instances (close)."""
    S = json.load(open(ROOT / "finite_size" / "score_law_check.json"))
    for row in S["averaged"]:
        assert abs(row["mean_model"] - row["mean_avg"]) < 1e-9
        for model, avg in row["tails"].values():
            assert abs(model - avg) < 1e-12
    head = next(r for r in S["averaged"] if r["m"] == 4095)
    assert head["tails"]["2393"][0] == pytest.approx(REDTEAM["l35"]["tails"]["2393"], rel=1e-6)
    tiny = S["per_instance"]
    assert len(tiny["instances"]) == 8
    for inst in tiny["instances"]:
        assert inst["mean"] == pytest.approx(tiny["model_mean"], abs=1e-9)  # 2l+1 < n+1: mean exact
        assert abs(inst["tails"]["11"] - tiny["model_tails"]["11"]) < 0.005    # tails only close


def test_boundary_mean_correction_small():
    """At the boundary 2l+1 = n+1 the mean is off by a small amount on exhaustive tiny instances (paper: < 0.016)."""
    tiny = json.load(open(ROOT / "dqi_verifiable" / "tiny_dqi_exact.json"))
    ratio = json.load(open(ROOT / "dqi_verifiable" / "r4_redteam_ratio.json"))
    diffs = [abs(r["exact_true_hist"] - r["eig_formula"]) for r in tiny if not r["cond_2l1_lt_dperp"]]
    assert diffs and max(diffs) < 0.016
    assert all(abs(r["exact_true_hist"] - r["eig_formula"]) < 1e-9 for r in tiny if r["cond_2l1_lt_dperp"])
    rt = [abs(r["diff"]) for r in ratio["tiny"] if r["two_l_plus_1"] >= r["d_perp"]]
    assert rt and max(rt) < 0.016
    assert all(abs(r["diff"]) < 1e-9 for r in ratio["tiny"] if r["two_l_plus_1"] < r["d_perp"])
