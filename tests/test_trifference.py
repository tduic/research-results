"""Checks for trifferent-codes/.

Re-checks every code in trifferent-codes/codes/ (all triples separated) and recomputes
the published baseline as the closure of known values under T(n) >= T(n-1) + 1
and shortening T(n-1) >= ceil(2 T(n) / 3), asserting exactly which bounds are new.
"""
import json
import math
from pathlib import Path

import numpy as np
import pytest

CODES = sorted((Path(__file__).resolve().parent.parent / "trifferent-codes" / "codes").glob("code_n*_M*.json"))

KNOWN = {1: 3, 2: 4, 3: 6, 4: 9, 5: 10, 6: 13, 7: 16, 8: 20, 9: 27,   # Kurz 2023 (exact)
         14: 81, 19: 243, 21: 243, 22: 243, 24: 729}                    # minimal linear codes (BDGP)
# Walker-Colbourn 2007 Table 6 (best known PHF(N; k, 3, 3), N = 1..24; see trifferent-codes/data/)
WC2007 = {int(n): v[0] for n, v in json.load(open(Path(__file__).resolve().parent.parent / "trifferent-codes" / "data" / "walker_colbourn_2007_table6.json"))["rho"].items()}
CLAIMED_NEW = {10: 30, 11: 36, 12: 48, 16: 108, 17: 109}
MATCHED = {13: 54, 18: 162}  # bounds that equal the published closure (shortenings of minimal codes)


def load(path):
    d = json.load(open(path))
    words = d["code"] if isinstance(d, dict) and "code" in d else d.get("codewords") if isinstance(d, dict) else d
    return np.array([[int(x) for x in (list(w) if isinstance(w, str) else w)] for w in words], dtype=np.int8)


def closure(base, top=24):
    L = {n: base.get(n, 0) for n in range(1, top + 1)}
    changed = True
    while changed:
        changed = False
        for n in range(2, top + 1):
            if L[n - 1] + 1 > L[n]:
                L[n], changed = L[n - 1] + 1, True
            if math.ceil(2 * L[n] / 3) > L[n - 1]:
                L[n - 1], changed = math.ceil(2 * L[n] / 3), True
    return L


@pytest.mark.parametrize("path", CODES, ids=lambda p: p.stem)
def test_code_is_trifferent(path):
    A = load(path)
    n, m = A.shape[1], A.shape[0]
    assert set(np.unique(A)) <= {0, 1, 2}
    assert len({tuple(r) for r in A}) == m
    assert path.stem == f"code_n{n}_M{m}"
    for i in range(m):
        for j in range(i + 1, m):
            rest = A[j + 1:]
            rainbow = (A[i] != A[j]) & (rest != A[i]) & (rest != A[j])
            assert rainbow.any(axis=1).all(), f"triple ({i},{j},·) not separated"


def test_shortening_rule_is_sound_on_our_codes():
    for path in CODES:
        A = load(path)
        col, sym = min(((c, s) for c in range(A.shape[1]) for s in range(3)), key=lambda cs: (A[:, cs[0]] == cs[1]).sum())
        B = np.delete(A[A[:, col] != sym], col, axis=1)
        assert len(B) >= math.ceil(2 * len(A) / 3)


def test_baseline_closure_and_novelty():
    assert all(WC2007[n] <= KNOWN[n] for n in KNOWN if n in WC2007 and n <= 9)   # consistent with Kurz's exact values
    base = {n: max(KNOWN.get(n, 0), WC2007.get(n, 0)) for n in set(KNOWN) | set(WC2007)}
    L = closure(base)
    assert [L[n] for n in range(10, 21)] == [29, 30, 36, 54, 81, 82, 83, 108, 162, 243, 244]
    for n, k in CLAIMED_NEW.items():
        assert k > L[n], f"T({n}) >= {k} is not above the published closure {L[n]}"
    for n, k in MATCHED.items():
        assert k == L[n]
    codes = {int(p.stem.split("_")[1][1:]): int(p.stem.split("_")[2][1:]) for p in CODES}
    assert codes == CLAIMED_NEW


LEAN = Path(__file__).resolve().parent.parent / "trifferent-codes" / "lean"
BANNED = ["sorry", "admit", "native_decide", "implemented_by", "@[extern]", "unsafe", "ofReduceBool"]


def test_lean_sources_clean():
    for f in sorted((LEAN / "Trifference").glob("*.lean")) + [LEAN / "Trifference.lean"]:
        text = f.read_text()
        for word in BANNED:
            assert word not in text, f"{word} in {f.name}"
        assert "\naxiom " not in text and not text.startswith("axiom ")


def test_lean_certificates_match_json_codes():
    import re
    for path in CODES:
        n, M = (int(x[1:]) for x in path.stem.split("_")[1:])
        src = (LEAN / "Trifference" / f"N{n}M{M}.lean").read_text()
        body = re.search(r"def codeN%dM%d : List \(ℕ × ℕ\) := \[(.*?)\]" % (n, M), src, re.S).group(1)
        pairs = [(int(p), int(q)) for p, q in re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", body)]
        words = {tuple(1 if (p >> i) & 1 else (2 if (q >> i) & 1 else 0) for i in range(n)) for p, q in pairs}
        assert len(pairs) == M and words == {tuple(r) for r in load(path).tolist()}
        assert f"theorem T_ge_N{n}M{M} : ∃ C : Finset (Fin {n} → Fin 3), Trifferent C ∧ {M} ≤ C.card" in " ".join(src.split())


def test_committed_axiom_reports_standard():
    for path in CODES:
        n, M = (int(x[1:]) for x in path.stem.split("_")[1:])
        line = (LEAN / "logs" / f"N{n}M{M}.axioms").read_text()
        assert "[propext, Classical.choice, Quot.sound]" in line
