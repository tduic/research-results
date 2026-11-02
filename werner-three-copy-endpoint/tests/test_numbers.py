"""Paper numbers are generated from shipped evidence, not hand-typed."""
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def test_numbers_regenerate_cleanly():
    subprocess.run([sys.executable, "scripts/generate_numbers.py"], cwd=ROOT, check=True)
    text = (ROOT / "paper/numbers.tex").read_text()
    for macro in (r"\nmodules", r"\nblocks", r"\nblocks", r"\runid", r"\walltime", r"\cpuhours"):
        assert macro in text, macro
    # The paper must use the macros, not re-type the headline figures.
    paper = (ROOT / "paper/main.tex").read_text()
    assert r"\input{numbers}" in paper
    assert r"\nmodules{}" in paper
    assert "8,199" not in paper, "headline module count typed by hand in paper"
    assert "41356979845" not in paper, "run id typed by hand in paper"


def test_paper_first_person():
    paper = (ROOT / "paper/main.tex").read_text()
    # No first-person plural anywhere (standalone 'we'/'We'/'our'/'Our').
    assert not re.search(r"\bwe\b", paper, flags=re.I), "paper uses 'we'"
    assert not re.search(r"\bour\b", paper, flags=re.I), "paper uses 'our'"
    assert "I " in paper or "I\n" in paper


def test_no_private_repo_reference():
    # Built by concatenation so this test file itself does not contain
    # the forbidden string it scans for.
    # The private repo is tduic/research; the target public repo is
    # tduic/research-results, which legitimately appears in README
    # clone instructions. So forbid the private name only when it is
    # NOT followed by "-results".
    pat = re.compile("tduic/" + "research(?!-results)")
    hits = []
    for p in sorted(ROOT.rglob("*")):
        if p.is_file() and p.suffix not in (".pdf",) and ".lake" not in p.parts and "tests" not in p.parts:
            try:
                text = p.read_text(errors="ignore")
            except Exception:
                continue
            if pat.search(text):
                hits.append(str(p.relative_to(ROOT)))
    assert not hits, "\n".join(hits)


def test_no_front_running_sections():
    for name in ("paper/main.tex", "README.md"):
        text = (ROOT / name).read_text()
        assert "## Next steps" not in text and "\\section{Next steps}" not in text
        assert "what to try next" not in text.lower()
        assert "four-copy roadmap" not in text.lower()
