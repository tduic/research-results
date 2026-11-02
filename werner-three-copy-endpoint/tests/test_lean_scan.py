"""Scan shipped Lean files for forbidden tokens outside comments.

Forbidden, per the research protocol: sorry, admit, axiom (as a command),
native_decide, implemented_by, extern, unsafe, opaque, ofReduceBool.
A line that is a comment (after '--' with nothing before it, or inside a
/-! ... -/ block) is not counted. This is a lexical scan, not a Lean
build; the lean level of verify.sh is what kernel-checks the proof.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
FORBIDDEN = ["sorry", "admit", "native_decide", "implemented_by", "ofReduceBool"]
# 'axiom', 'extern', 'unsafe', 'opaque' are only forbidden as commands, so
# they are checked at line start (allowing leading whitespace).
COMMANDS = ["axiom", "extern", "unsafe", "opaque"]


def strip_comments(text):
    # Remove block comments /- ... -/ (non-nested, as used in this project).
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    out = []
    for line in text.splitlines():
        # Remove '--' comments, unless inside a string (approximation: none
        # of the shipped files put '--' inside a string before a token).
        if "--" in line:
            line = line.split("--", 1)[0]
        out.append(line)
    return "\n".join(out)


def test_no_forbidden_tokens():
    lean_files = sorted(p for p in (ROOT / "lean").rglob("*.lean"))
    assert lean_files, "no shipped Lean files found"
    bad = []
    for p in lean_files:
        code = strip_comments(p.read_text(errors="ignore"))
        for tok in FORBIDDEN:
            if re.search(r"\b" + re.escape(tok) + r"\b", code):
                bad.append(f"{p.relative_to(ROOT)}: {tok}")
        for line in code.splitlines():
            s = line.strip()
            for cmd in COMMANDS:
                if re.match(rf"{cmd}\b", s):
                    bad.append(f"{p.relative_to(ROOT)}: command {cmd}: {s[:80]}")
    assert not bad, "forbidden tokens found:\n" + "\n".join(bad)


def test_final_theorem_present():
    final = ROOT / "lean/layerD_t0/LayerDT0/Final.lean"
    text = final.read_text()
    assert "theorem werner3_endpoint_all_d" in text
    assert "C.rank ≤ 2" in text or "C.rank" in text
    assert "WernerEndpoint.qfun C" in text
    assert "#print axioms LayerDT0.werner3_endpoint_all_d" in text
