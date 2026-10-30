"""Repository-level checks only. Each result's own checks live in <result>/tests and run on their own."""
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
RESULTS = sorted(re.findall(r"\]\(([a-z0-9-]+)/\)", (ROOT / "README.md").read_text()))
FOLDERS = sorted(p.name for p in ROOT.iterdir() if p.is_dir() and (p / "paper").is_dir())


def test_readme_lists_every_result_folder():
    assert RESULTS, "no result folders found in the README table"
    assert RESULTS == FOLDERS, (RESULTS, FOLDERS)


@pytest.mark.parametrize("name", RESULTS)
def test_result_is_self_contained(name):
    """Everything needed to verify a result lives in its folder, plus one CI workflow of its own."""
    p = ROOT / name
    for f in ["README.md", "requirements.txt", "verify.sh", "tests", "paper/main.tex", "paper/main.pdf"]:
        assert (p / f).exists(), f"{name}/{f} missing"
    assert (p / "verify.sh").stat().st_mode & 0o111, f"{name}/verify.sh is not executable"
    wf = ROOT / ".github" / "workflows" / f"{name}.yml"
    assert wf.is_file(), f"no workflow for {name}"
    text = wf.read_text()
    assert f"{name}/**" in text and f"sparse-checkout: {name}" in text
    assert "## Verify this result" in (p / "README.md").read_text()


@pytest.mark.parametrize("name", RESULTS)
def test_result_does_not_reach_outside_its_folder(name):
    """No project file refers to another project or to repo-level files."""
    others = [o for o in RESULTS if o != name]
    for f in (ROOT / name).rglob("*"):
        if not f.is_file() or ".lake" in f.parts or f.suffix not in {".py", ".sh", ".tex", ".toml", ".txt", ".cfg"}:
            continue
        text = f.read_text(errors="replace")
        for o in others:
            assert o not in text, f"{f.relative_to(ROOT)} mentions {o}"
        assert "../tests" not in text and "../tools" not in text, f"{f.relative_to(ROOT)} reaches outside {name}/"


def test_root_readme_voice():
    text = re.sub(r"https?://\S+", "", (ROOT / "README.md").read_text())
    hits = re.findall(r".{0,30}\b(?:[Ww]e|[Oo]ur|[Oo]urs|[Uu]s|[Oo]urselves)\b.{0,30}", text)
    assert not hits, hits[:5]


def test_citation_file_lists_every_paper():
    cff = (ROOT / "CITATION.cff").read_text()
    for name in RESULTS:
        tex = (ROOT / name / "paper" / "main.tex").read_text()
        title = " ".join(re.search(r"\\title\{(.*?)\}\n", tex, re.S).group(1).replace("\\\\", " ").split())
        assert f'title: "{title}"' in cff, title
        assert f"{name}/paper/main.pdf" in cff
