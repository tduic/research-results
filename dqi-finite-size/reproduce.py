"""Rerun every computation behind this result from scratch and compare with the committed results.

The project is copied to a temporary folder first, so the committed results/ are never touched.
Each script is run there, and every JSON file it writes is compared with the committed copy:
numbers must agree to a relative tolerance of 1e-9 (reruns differ only by floating-point noise,
about 1e-13), everything else must match exactly, and timing fields ("secs") are ignored.
Finally the paper's generated numbers (paper/numbers.tex, paper/table_vi.tex) are rebuilt from
the fresh results and must match the committed files.

Usage (from this folder):
    python reproduce.py                 # everything, about 10 minutes on one core
    python reproduce.py --fast          # skip the two slowest scripts (about 3 minutes)
    python reproduce.py airy_deficit    # only scripts whose name contains a given string
"""
import argparse
import json
import math
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

PROJECT = Path(__file__).resolve().parent
RTOL = 1e-9
IGNORED_KEYS = {"secs"}

# (script, results it writes, approximate seconds on one core)
SCRIPTS = [
    ("experiments/finite_size/airy_deficit.py", ["results/finite_size/airy_deficit.json"], 5),
    ("experiments/finite_size/redesign.py", ["results/finite_size/redesign.json"], 10),
    ("experiments/finite_size/score_law_check.py", ["results/finite_size/score_law_check.json"], 6),
    ("experiments/dqi_verifiable/xp_formula.py", ["results/dqi_verifiable/xp_table.json"], 11),
    # these two print their JSON to stdout; the committed file is that output
    ("experiments/dqi_verifiable/r4_redteam_exact.py", ["stdout:results/dqi_verifiable/r4_redteam_exact.json"], 12),
    ("experiments/dqi_verifiable/r4_redteam_tiny_and_ratio.py", ["stdout:results/dqi_verifiable/r4_redteam_ratio.json"], 50),
    ("experiments/dqi_verifiable/tiny_dqi_exact.py", ["results/dqi_verifiable/tiny_dqi_exact.json"], 3),
    ("experiments/dqi_verifiable/dqi_dist_stable.py", ["results/dqi_verifiable/dqi_dist_stable.json"], 5),
    ("experiments/dqi_verifiable/dqi_tail_opt.py", ["results/dqi_verifiable/dqi_tail_opt.json"], 52),
    ("experiments/dqi_verifiable/dqi_exact_t.py", ["results/dqi_verifiable/exact_t.json"], 159),
    ("experiments/dqi_verifiable/dqi_distribution.py", ["results/dqi_verifiable/dqi_distribution.json"], 224),
]
SLOW = 120


def diff(a, b, path=""):
    """Yield human-readable differences between two JSON values."""
    if isinstance(a, dict) and isinstance(b, dict):
        for k in sorted(set(a) | set(b)):
            if k in IGNORED_KEYS:
                continue
            if k not in a or k not in b:
                yield f"{path}.{k}: present in only one file"
            else:
                yield from diff(a[k], b[k], f"{path}.{k}")
    elif isinstance(a, list) and isinstance(b, list):
        if len(a) != len(b):
            yield f"{path}: length {len(a)} vs {len(b)}"
        for i, (x, y) in enumerate(zip(a, b)):
            yield from diff(x, y, f"{path}[{i}]")
    elif isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool):
        if isinstance(a, float) and isinstance(b, float) and math.isnan(a) and math.isnan(b):
            return
        if a != b and abs(a - b) > RTOL * max(abs(a), abs(b)):
            yield f"{path}: {a!r} vs {b!r}"
    elif a != b:
        yield f"{path}: {a!r} vs {b!r}"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("only", nargs="*", help="run only scripts whose path contains one of these strings")
    ap.add_argument("--fast", action="store_true", help=f"skip scripts that take more than {SLOW} s")
    args = ap.parse_args()

    chosen = [s for s in SCRIPTS
              if (not args.only or any(o in s[0] for o in args.only)) and not (args.fast and s[2] > SLOW)]
    if not chosen:
        sys.exit("no scripts selected")
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "project"
        shutil.copytree(PROJECT, work, ignore=shutil.ignore_patterns("__pycache__", "*.aux", "*.log", "*.bbl"))
        for script, outputs, est in chosen:
            t0 = time.time()
            print(f"run  {script} (about {est} s) ...", flush=True)
            r = subprocess.run([sys.executable, script], cwd=work, capture_output=True, text=True)
            if r.returncode != 0:
                print(r.stdout[-2000:] + r.stderr[-2000:])
                print(f"FAIL {script}: exit code {r.returncode}")
                failures += 1
                continue
            for out in outputs:
                if out.startswith("stdout:"):
                    out = out[len("stdout:"):]
                    fresh = json.loads(r.stdout)
                else:
                    fresh = json.loads((work / out).read_text())
                problems = list(diff(json.loads((PROJECT / out).read_text()), fresh))
                status = "ok  " if not problems else "FAIL"
                print(f"{status} {out} ({time.time() - t0:.0f} s){'' if not problems else ': ' + str(len(problems)) + ' differences'}")
                for p in problems[:10]:
                    print("       ", p)
                failures += bool(problems)
        if not args.only and not args.fast:
            r = subprocess.run([sys.executable, "paper/make_numbers.py"], cwd=work, capture_output=True, text=True)
            for f in ["paper/numbers.tex", "paper/table_vi.tex"]:
                same = r.returncode == 0 and (work / f).read_text() == (PROJECT / f).read_text()
                print(f"{'ok  ' if same else 'FAIL'} {f} regenerated from the fresh results")
                failures += not same
    print("\nREPRODUCED: every rerun matches the committed results." if not failures
          else f"\n{failures} problem(s): see FAIL lines above.")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
