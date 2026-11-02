"""Run the standalone exact verifier on the shipped certificate.

This is the slowest quick-level check (about 132 s on the recorded
machine); it is kept in the quick suite because it is the only check
that actually verifies the certificate's exact identity, rather than
its hashes. It needs numpy (pinned in requirements.txt).
"""
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def test_verify_t0_passes():
    out = subprocess.run(
        [sys.executable, "-I", str(ROOT / "all_d/exact_t0/verify_t0.py"),
         str(ROOT / "all_d/exact_t0_v2/cert")],
        capture_output=True, text=True, timeout=600, cwd=ROOT)
    assert out.returncode == 0, out.stdout[-2000:] + out.stderr[-2000:]
    last = [ln for ln in out.stdout.splitlines() if ln.startswith("{")]
    assert last, "verifier produced no JSON summary"
    summary = json.loads(last[-1])
    assert summary["status"] == "PASS"
    assert summary["blocks"] == 1000
    assert summary["orbit_coordinates"] == 4675
    assert summary["equality_rows"] == 273
