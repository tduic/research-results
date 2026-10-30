"""The paper ships with the project, cites exactly its bibliography, and takes every number from results/."""
import re
import subprocess
import sys
from pathlib import Path

import pytest

PROJECT = Path(__file__).resolve().parent.parent
PAPER = PROJECT / "paper"
LEFTOVERS = re.compile(r"TODO|FIXME|XXX|TBD|lorem ipsum|as an ai|\[citation needed\]|insert .* here", re.I)


def test_paper_files_present_and_linked():
    for f in ["main.tex", "references.bib", "main.pdf"]:
        assert (PAPER / f).is_file(), f"paper/{f} missing"
    assert "paper/main.pdf" in (PROJECT / "README.md").read_text(), "README.md does not link the paper"


def test_citations_match_bibliography():
    tex = (PAPER / "main.tex").read_text()
    cited = {k.strip() for group in re.findall(r"\\cite[pt]?(?:\[[^\]]*\])?\{([^}]*)\}", tex) for k in group.split(",")}
    keys = set(re.findall(r"@\w+\{([^,]+),", (PAPER / "references.bib").read_text()))
    assert cited and cited == keys, (cited - keys, keys - cited)


def test_no_placeholder_text():
    for f in PAPER.glob("*.tex"):
        hit = LEFTOVERS.search(f.read_text())
        assert hit is None, f"{f.name}: {hit.group(0)!r}"


@pytest.mark.parametrize("path", [PROJECT / "README.md", PAPER / "main.tex"], ids=["README.md", "paper/main.tex"])
def test_single_author_voice(path):
    """One person did this work: write "I", not "we"/"our"/"us"."""
    text = re.sub(r"\\cite\{[^}]*\}|https?://\S+", "", path.read_text())
    hits = re.findall(r".{0,30}\b(?:[Ww]e|[Oo]ur|[Oo]urs|[Uu]s|[Oo]urselves)\b.{0,30}", text)
    assert not hits, hits[:5]


def test_paper_numbers_are_generated_from_results():
    before = {f: (PAPER / f).read_text() for f in ["numbers.tex", "table_vi.tex"]}
    subprocess.run([sys.executable, str(PAPER / "make_numbers.py")], check=True, cwd=PROJECT)
    for f, text in before.items():
        assert (PAPER / f).read_text() == text, f"{f} is stale: rerun paper/make_numbers.py"
    tex = (PAPER / "main.tex").read_text()
    # every macro defined in numbers.tex is used, and the text carries no hand-typed copy of key results
    for macro in re.findall(r"\\newcommand\{\\(\w+)\}", before["numbers.tex"]):
        assert "\\" + macro in tex, f"unused macro {macro}"
    for literal in ["16.8", "2359", "2,359", "33.2", "9.1 million", "2,510"]:
        assert literal not in tex, f"hand-typed number {literal!r} in main.tex; use the generated macro"
