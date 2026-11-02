#!/usr/bin/env bash
# Verify this result on its own. Nothing outside this folder is needed
# except the pinned Mathlib dependency (Lean v4.24.0, Mathlib v4.24.0)
# and, for the paper level, a TeX Live install.
#
#   ./verify.sh          quick checks (about 2-3 min, mostly the exact verifier): tests, paper numbers,
#                        certificate and identity manifests, Lean scan,
#                        and no private-repo reference anywhere shipped.
#   ./verify.sh paper    rebuild the paper and check the committed PDF
#                        matches its source.
#   ./verify.sh lean     MANUAL ONLY, NOT run by CI. Regenerate the
#                        identity modules from the shipped certificate,
#                        build the Lean proofs in lean/ (needs elan),
#                        and check the final theorem's axioms.
#                        Recorded build: ~12 h wall, ~18 CPU-hours.
#   ./verify.sh all      quick + paper. Lean is excluded by design.
#
# Setup: python3 -m pip install -r requirements.txt
#        (paper also needs latexmk and a TeX Live install)
set -euo pipefail
cd "$(dirname "$0")"
PY=${PYTHON:-python3}

quick() {
  echo "== quick: tests"
  "$PY" -m pytest -q tests
  echo "== quick: paper numbers regenerate"
  "$PY" scripts/generate_numbers.py
  echo "== quick: python files compile"
  "$PY" - <<'EOF'
import pathlib, py_compile, sys, tempfile
bad = n = 0
with tempfile.TemporaryDirectory() as tmp:
    for p in sorted(pathlib.Path(".").rglob("*.py")):
        if {".lake", ".git", "__pycache__"} & set(p.parts):
            continue
        n += 1
        try:
            py_compile.compile(str(p), cfile=f"{tmp}/{n}.pyc", doraise=True)
        except py_compile.PyCompileError as e:
            print(e.msg, file=sys.stderr); bad += 1
print(f"{n} python files, {bad} failed")
sys.exit(1 if bad else 0)
EOF
  echo "ok   quick checks passed (Lean proof NOT rebuilt; see lean level)"
}

lean() {
  echo "== lean: MANUAL ONLY. This level is NOT run by CI, by design."
  echo "== lean: recorded build was ~12 h wall / ~18 CPU-hours."
  command -v lake >/dev/null || { echo "lake not found: install elan (https://github.com/leanprover/elan)" >&2; exit 1; }
  (cd lean && lake exe cache get || true && sh layerD_t0/run_full.sh)
  log=$(mktemp)
  (cd lean && lake env lean - <<'LEAN' 2>&1 | tee "$log"
import LayerDT0.Final
#print axioms LayerDT0.werner3_endpoint_all_d
LEAN
  )
  grep -q "propext, Classical.choice, Quot.sound" "$log" || { echo "FAIL: standard-axioms line not found"; rm -f "$log"; exit 1; }
  if grep "depends on axioms" "$log" | grep -v "propext, Classical.choice, Quot.sound" | grep -q .; then echo "FAIL: non-standard axioms found"; rm -f "$log"; exit 1; fi
  rm -f "$log"
  echo "ok   Lean build checked: final theorem, standard axioms only"
}

paper() {
  echo "== paper: rebuild and compare with the committed PDF"
  command -v latexmk >/dev/null || { echo "latexmk not found: install TeX Live to build the paper" >&2; exit 1; }
  test -f paper/main.pdf || { echo "FAIL: no committed paper/main.pdf yet" >&2; exit 1; }
  tmp=$(mktemp -d); trap 'rm -rf "$tmp"' RETURN
  cp -R paper "$tmp/paper"
  if ! (cd "$tmp/paper" && rm -f main.pdf && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex >/dev/null 2>&1); then
    tail -30 "$tmp/paper/main.log"; echo "FAIL: paper does not build" >&2; exit 1
  fi
  if grep -E "undefined|Rerun to get" "$tmp/paper/main.log"; then echo "FAIL: unresolved references" >&2; exit 1; fi
  if command -v pdftotext >/dev/null; then
    pdftotext -layout paper/main.pdf "$tmp/committed.txt"; pdftotext -layout "$tmp/paper/main.pdf" "$tmp/built.txt"
    if cmp -s "$tmp/committed.txt" "$tmp/built.txt"; then echo "ok   paper/main.pdf matches its source"
    else echo "FAIL paper/main.pdf does not match its source"; diff "$tmp/committed.txt" "$tmp/built.txt" | head -20; exit 1; fi
  else
    echo "ok   paper builds (install poppler's pdftotext to also compare it with the committed PDF)"
  fi
}

case "${1:-quick}" in
  quick) quick ;;
  lean) lean ;;
  paper) paper ;;
  all) quick; paper ;;
  *) sed -n '2,13p' "$0"; exit 2 ;;
esac
