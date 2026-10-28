"""Generate numbers.tex and table_vi.tex for the paper from the shipped results.

Run from dqi-finite-size/:  python paper/make_numbers.py
Every number in the paper that comes from a computation is a macro defined here,
so the text cannot drift from the data (tests/test_papers.py checks the files are current).
"""
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path[:0] = [str(ROOT / "experiments" / "finite_size"), str(ROOT / "experiments" / "dqi_verifiable")]
import dqi_core  # noqa: E402
import airy_deficit as ad  # noqa: E402
import numpy as np  # noqa: E402
from xp_formula import xp_best  # noqa: E402

A = json.load(open(ROOT / "results" / "finite_size" / "airy_deficit.json"))
B = json.load(open(ROOT / "results" / "finite_size" / "redesign.json"))
R = json.load(open(ROOT / "results" / "dqi_verifiable" / "r4_redteam_exact.json"))
X = json.load(open(ROOT / "results" / "dqi_verifiable" / "xp_table.json"))
S = json.load(open(ROOT / "results" / "finite_size" / "score_law_check.json"))


def sci(x, digits=2):
    e = int(math.floor(math.log10(abs(x))))
    return f"{x / 10 ** e:.{digits}f}\\times 10^{{{e}}}"


def main():
    head = next(r for r in A["table"] if r["m"] == 4095 and r["n"] == 70)
    fit = next(f for f in A["fits"] if f["lmin"] == 3)
    m, l, p = 4095, 35, 2016 / 4096
    airy_head = ad.airy_pred(m, l, p, fit["c0"], fit["c1"])
    over = [1 / r["P_tailopt_paper_t"] for r in A["table"]]
    best = B["fair_1e+23"]["best"]
    n70 = B["fair_1e+23"]["at_n70"]
    grid_m = sorted({g["m"] for g in A["grid"]})
    rows4095 = [r for r in A["table"] if r["m"] == 4095]
    growth = [rows4095[i + 1]["paper_xp"] / rows4095[i]["paper_xp"] for i in range(len(rows4095) - 1)]
    tof = [rows4095[i + 1]["toffoli"] / rows4095[i]["toffoli"] for i in range(len(rows4095) - 1)]
    # held-out check of the Airy law on a grid covering the stated ranges at m = 2^15 .. 2^18
    worst = 0.0
    for e in range(15, 19):
        mm = 2 ** e
        for fr in np.geomspace(1e-3, 0.3, 8):
            ll = max(3, int(round(fr * mm)))
            for pp in [0.05, 0.1, 0.2, 0.3, 0.4, 0.5]:
                ex = dqi_core.semicircle(mm, ll, pp) - dqi_core.exact_mean(mm, ll, pp)
                worst = max(worst, abs(ad.airy_pred(mm, ll, pp, fit["c0"], fit["c1"]) - ex) / ex)
    # n = 96 design re-priced with the paper's own XP allocation
    xp96 = math.exp(-xp_best(4095, best["n"], 12, best["t"])[0]) * best["P"]
    avg = S["averaged"][0]
    tiny = S["per_instance"]
    tail11 = [r["tails"]["11"] for r in tiny["instances"]]
    xp_ok = all(float("%.3g" % r["xp_trials"]) == r["table_xp"] for r in X)

    macros = {
        "tPaper": f"{head['t_paper']:,}".replace(",", "{,}"),
        "exactMean": f"{head['exact_mean']:,.1f}".replace(",", "{,}"),
        "exactMedian": f"{head['median']:,}".replace(",", "{,}"),
        "exactSd": f"{head['sd']:.1f}",
        "deficitExact": f"{head['deficit']:.1f}",
        "deficitAiry": f"{airy_head:.1f}",
        "PmeanHead": f"{100 * R['l35']['tails']['2393']:.1f}",
        "PtailHead": f"{100 * R['l35_tailopt_2393']['P']:.1f}",
        "runsHead": f"{1 / head['P_tailopt_paper_t']:.1f}",
        "overMin": f"{min(over):.1f}",
        "overMax": f"{max(over):.1f}",
        "overHead": f"{1 / head['P_tailopt_paper_t']:.1f}",
        "xpHead": sci(R["xp_t2393"], 3),
        "perRunHead": sci(head["paper_xp"] * head["P_tailopt_paper_t"], 1),
        "xpRowsChecked": str(len(X)),
        "fitCzero": f"{fit['c0']:.2f}",
        "fitCone": f"{fit['c1']:.3f}",
        "fitPoints": str(fit["n"]),
        "fitMaxErr": f"{100 * fit['max_rel_err']:.1f}",
        "fitRmsErr": f"{100 * fit['rms_rel_err']:.1f}",
        "leadOnlyErr": f"{100 * fit['leading_only_max_rel_err']:.0f}",
        "gridMmin": str(int(round(math.log2(min(grid_m))))),
        "gridMmax": str(int(round(math.log2(max(grid_m))))),
        "airyZero": f"{dqi_core.A1:.4f}",
        "growthMin": f"{min(growth):.0f}",
        "growthMax": f"{max(growth):.0f}",
        "tofGrowth": f"{sum(tof) / len(tof):.2f}",
        "bestN": str(best["n"]),
        "bestP": f"{100 * best['P']:.0f}",
        "bestToffRun": f"{best['toffoli_per_run'] / 1e6:.1f}",
        "bestToffSucc": f"{best['toffoli_per_success'] / 1e6:.1f}",
        "bestQubits": f"{round(best['qubits']):,}".replace(",", "{,}"),
        "bestFair": sci(best["fair_ratio"], 2),
        "nSeventyRuns": f"{n70['runs']:.0f}",
        "heldOutMax": f"{100 * worst:.1f}",
        "bestFairPaperXP": sci(xp96, 2),
        "avgTailDiff": "10^{%d}" % (math.floor(math.log10(max(1e-300, max(abs(a - b) for a, b in avg["tails"].values())))) + 1),
        "tinyTailModel": f"{tiny['model_tails']['11']:.3f}",
        "tinyTailMin": f"{min(tail11):.3f}",
        "tinyTailMax": f"{max(tail11):.3f}",
        "nSeventyWorse": f"{n70['toffoli_per_success'] / best['toffoli_per_success']:.0f}",
    }
    assert xp_ok, "XP reproduction no longer matches Table VI to 3 significant figures"
    lines = ["% Generated by paper/make_numbers.py from results/ -- do not edit by hand."]
    lines += [f"\\newcommand{{\\{k}}}{{{v}}}" for k, v in macros.items()]
    (HERE / "numbers.tex").write_text("\n".join(lines) + "\n")

    t = ["% Generated by paper/make_numbers.py from results/finite_size/airy_deficit.json -- do not edit by hand.",
         "\\begin{tabular}{rrrrcc}", "\\toprule",
         "$m$ & $n$ & $t$ (paper) & expected score & paper's classical trials & overstatement \\\\", "\\midrule"]
    for r in A["table"]:
        star = r["m"] == 4095 and r["n"] == 70
        o = f"{1 / r['P_tailopt_paper_t']:.1f}"
        o = f"\\textbf{{{o}}}" if star else o
        t.append(f"{r['m']} & {r['n']} & {r['t_paper']} & {r['exact_mean']:.1f} & ${sci(r['paper_xp'])}$ & {o} \\\\")
    t += ["\\bottomrule", "\\end{tabular}"]
    (HERE / "table_vi.tex").write_text("\n".join(t) + "\n")


if __name__ == "__main__":
    main()
