#!/usr/bin/env bash
# Verify this result on its own. Nothing outside this folder is needed.
#
#   ./verify.sh                 quick checks: the test suite (about 10 s)
#   ./verify.sh reproduce-fast  rerun every computation except the two slowest and compare (about 3 min)
#   ./verify.sh reproduce       rerun every computation from scratch and compare (about 10 min)
#   ./verify.sh paper           rebuild the paper and check the committed PDF matches its source
#   ./verify.sh all             everything above
#
# Setup: python3 -m pip install -r requirements.txt   (paper also needs latexmk and a TeX Live install)
set -euo pipefail
cd "$(dirname "$0")"
PY=${PYTHON:-python3}

quick()     { echo "== quick: test suite"; "$PY" -m pytest -q tests; }
reproduce() { echo "== reproduce: rerun computations and compare with results/"; "$PY" reproduce.py "$@"; }
paper() {
  echo "== paper: rebuild and compare with the committed PDF"
  command -v latexmk >/dev/null || { echo "latexmk not found: install TeX Live to build the paper"; exit 1; }
  tmp=$(mktemp -d); trap 'rm -rf "$tmp"' RETURN
  cp -R paper "$tmp/paper"
  if ! (cd "$tmp/paper" && rm -f main.pdf && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex >/dev/null 2>&1); then
    tail -30 "$tmp/paper/main.log"; echo "FAIL: paper does not build"; exit 1
  fi
  if grep -E "undefined|Rerun to get" "$tmp/paper/main.log"; then echo "FAIL: unresolved references"; exit 1; fi
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
  reproduce) reproduce ;;
  reproduce-fast) reproduce --fast ;;
  paper) paper ;;
  all) quick; reproduce; paper ;;
  *) sed -n '2,12p' "$0"; exit 2 ;;
esac
