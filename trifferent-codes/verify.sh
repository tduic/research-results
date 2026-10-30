#!/usr/bin/env bash
# Verify this result on its own. Nothing outside this folder is needed.
#
#   ./verify.sh          quick checks (about 5 s): every code re-checked triple by triple, rebuilt from its
#                        description in the paper, matched to its Lean certificate; the literature baseline
#                        recomputed; and an independent decoder and triple check
#   ./verify.sh lean     build the Lean proofs from scratch and check their axioms (needs elan; about 5 min
#                        after the Mathlib cache download)
#   ./verify.sh paper    rebuild the paper and check the committed PDF matches its source
#   ./verify.sh all      everything above
#
# Setup: python3 -m pip install -r requirements.txt   (paper also needs latexmk and a TeX Live install)
set -euo pipefail
cd "$(dirname "$0")"
PY=${PYTHON:-python3}

quick() {
  echo "== quick: test suite"; "$PY" -m pytest -q tests
  echo "== quick: rebuild every code from its algebraic description"; "$PY" verification/constructions.py
  echo "== quick: independent decoder and triple check"; "$PY" -I verification/rt_check.py .
}
lean() {
  echo "== lean: build the proofs and check axioms"
  command -v lake >/dev/null || { echo "lake not found: install elan (https://github.com/leanprover/elan)"; exit 1; }
  log=$(mktemp)
  (cd lean && lake exe cache get && ./ci-build.sh) 2>&1 | tee "$log"
  n=$(grep -o "'[^']*' depends on axioms" "$log" | sort -u | wc -l | tr -d ' ')
  bad=$(grep "depends on axioms" "$log" | grep -vc "\[propext, Classical.choice, Quot.sound\]" || true)
  rm -f "$log"
  if [ "$n" -lt 6 ] || [ "$bad" -ne 0 ]; then echo "FAIL: $n axiom reports, $bad non-standard"; exit 1; fi
  echo "ok   $n theorems (5 bounds + independent restatements) checked by the Lean kernel, standard axioms only"
}
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
  lean) lean ;;
  paper) paper ;;
  all) quick; lean; paper ;;
  *) sed -n '2,13p' "$0"; exit 2 ;;
esac
