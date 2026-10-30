"""The paper ships with the project, cites exactly its bibliography, and its code descriptions rebuild the codes."""
import importlib.util
import re
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


def test_paper_constructions_match_builder():
    spec = importlib.util.spec_from_file_location("constructions", PROJECT / "verification" / "constructions.py")
    con = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(con)
    tex = (PAPER / "main.tex").read_text()
    words = set(re.findall(r"\\w\{([012]+)\}", tex))
    expected = {r for _, reps in con.ORBIT_CODES.values() for r in reps} | set(con.D16_BASIS) | set(con.C16_COSET_REPS)
    assert expected <= words, expected - words
    for n, (s, reps) in con.ORBIT_CODES.items():
        assert f"$G_{s}$-orbits" in tex
    for n, C in con.all_codes().items():
        assert f"giving ${len(C)}$ words" in tex or f"with ${len(C)}$ words" in tex, n
