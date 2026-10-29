"""Every result folder ships a LaTeX paper whose numbers and constructions match the shipped data."""
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
RESULTS = sorted(re.findall(r"\]\(([a-z0-9-]+)/\)", (ROOT / "README.md").read_text()))
LEFTOVERS = re.compile(r"TODO|FIXME|XXX|TBD|lorem ipsum|as an ai|\[citation needed\]|insert .* here", re.I)


def test_results_table_is_nonempty():
    assert RESULTS, "no result folders found in README table"


@pytest.mark.parametrize("name", RESULTS)
def test_result_has_paper(name):
    paper = ROOT / name / "paper"
    for f in ["main.tex", "references.bib", "main.pdf"]:
        assert (paper / f).is_file(), f"{name}/paper/{f} missing"
    assert "paper/main.pdf" in (ROOT / name / "README.md").read_text(), f"{name}/README.md does not link its paper"


@pytest.mark.parametrize("name", RESULTS)
def test_citations_match_bibliography(name):
    paper = ROOT / name / "paper"
    tex = (paper / "main.tex").read_text()
    cited = {k.strip() for group in re.findall(r"\\cite[pt]?(?:\[[^\]]*\])?\{([^}]*)\}", tex) for k in group.split(",")}
    keys = set(re.findall(r"@\w+\{([^,]+),", (paper / "references.bib").read_text()))
    assert cited and cited == keys, (cited - keys, keys - cited)


@pytest.mark.parametrize("name", RESULTS)
def test_no_placeholder_text(name):
    for f in (ROOT / name / "paper").glob("*.tex"):
        hit = LEFTOVERS.search(f.read_text())
        assert hit is None, f"{f.name}: {hit.group(0)!r}"


def test_dqi_paper_numbers_are_generated_from_results(tmp_path):
    paper = ROOT / "dqi-finite-size" / "paper"
    before = {f: (paper / f).read_text() for f in ["numbers.tex", "table_vi.tex"]}
    subprocess.run([sys.executable, str(paper / "make_numbers.py")], check=True, cwd=ROOT / "dqi-finite-size")
    for f, text in before.items():
        assert (paper / f).read_text() == text, f"{f} is stale: rerun paper/make_numbers.py"
    tex = (paper / "main.tex").read_text()
    # every macro defined in numbers.tex is used, and the text carries no hand-typed copy of key results
    for macro in re.findall(r"\\newcommand\{\\(\w+)\}", before["numbers.tex"]):
        assert "\\" + macro in tex, f"unused macro {macro}"
    for literal in ["16.8", "2359", "2,359", "33.2", "9.1 million", "2,510"]:
        assert literal not in tex, f"hand-typed number {literal!r} in main.tex; use the generated macro"


def test_trifference_paper_constructions_match_builder():
    spec = importlib.util.spec_from_file_location(
        "constructions", ROOT / "trifferent-codes" / "verification" / "constructions.py")
    con = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(con)
    tex = (ROOT / "trifferent-codes" / "paper" / "main.tex").read_text()
    words = set(re.findall(r"\\w\{([012]+)\}", tex)) | set(re.findall(r"\\w\{([012]+)\}", tex.replace(" ", "")))
    expected = {r for _, reps in con.ORBIT_CODES.values() for r in reps} | set(con.D16_BASIS) | set(con.C16_COSET_REPS)
    assert expected <= words, expected - words
    for n, (s, reps) in con.ORBIT_CODES.items():
        assert f"$G_{s}$-orbits" in tex or f"$G_{{{s}}}$-orbits" in tex
    for n, C in con.all_codes().items():
        assert f"giving ${len(C)}$ words" in tex or f"with ${len(C)}$ words" in tex, n


PROSE = [ROOT / "README.md"] + [ROOT / n / "README.md" for n in RESULTS] + [ROOT / n / "paper" / "main.tex" for n in RESULTS]


@pytest.mark.parametrize("path", PROSE, ids=lambda p: str(p.relative_to(ROOT)))
def test_single_author_voice(path):
    """One person did this work: write "I", not "we"/"our"/"us"."""
    text = re.sub(r"\\cite\{[^}]*\}|https?://\S+", "", path.read_text())
    hits = re.findall(r".{0,30}\b(?:[Ww]e|[Oo]ur|[Oo]urs|[Uu]s|[Oo]urselves)\b.{0,30}", text)
    assert not hits, hits[:5]


def test_citation_file_lists_every_paper():
    cff = (ROOT / "CITATION.cff").read_text()
    for name in RESULTS:
        tex = (ROOT / name / "paper" / "main.tex").read_text()
        title = " ".join(re.search(r"\\title\{(.*?)\}\n", tex, re.S).group(1).replace("\\\\", " ").split())
        assert f'title: "{title}"' in cff, title
        assert f"{name}/paper/main.pdf" in cff
