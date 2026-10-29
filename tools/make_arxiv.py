"""Build an arXiv source bundle for every paper and prove it compiles on its own.

For each <result>/paper/ this:
  1. runs latexmk in place so main.bbl is current (arXiv does not run BibTeX);
  2. copies main.tex, every file it \\input's, and main.bbl into a clean directory;
  3. compiles that directory twice with plain pdflatex (no bibtex, no network) and fails on any
     undefined citation or reference;
  4. writes dist/<result>-arxiv.tar.gz and dist/<result>-arxiv-metadata.txt.

Usage (from the repo root):  python tools/make_arxiv.py
"""
import re
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DIST = ROOT / "dist"

META = {
    "dqi-finite-size": dict(
        categories="quant-ph (primary); cross-list cs.CC",
        comments="4 pages, 1 table. Code, data and tests: https://github.com/tduic/research-results/tree/main/dqi-finite-size",
        msc="", acm=""),
    "trifferent-codes": dict(
        categories="math.CO (primary); cross-list cs.IT, math.IT",
        comments="4 pages, 1 table. Explicit codes and Lean 4 proofs: https://github.com/tduic/research-results/tree/main/trifferent-codes",
        msc="05B30 (primary); 94B25, 68R05", acm=""),
}


def run(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout[-3000:] + r.stderr[-3000:])
        raise SystemExit(f"failed: {' '.join(cmd)} in {cwd}")
    return r


def inputs(tex):
    return re.findall(r"\\input\{([^}]+)\}", tex)


def expand_macros(text, numbers):
    defs = dict(re.findall(r"\\newcommand\{\\(\w+)\}\{(.*)\}", numbers))
    for k in sorted(defs, key=len, reverse=True):
        text = re.sub(r"\\" + k + r"(?![A-Za-z])", lambda _m, v=defs[k]: v, text)
    return text


def abstract_text(paper):
    tex = (paper / "main.tex").read_text()
    a = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, re.S).group(1)
    nums = (paper / "numbers.tex").read_text() if (paper / "numbers.tex").exists() else ""
    a = expand_macros(a, nums)
    a = a.replace("{,}", ",").replace("\\ ", " ").replace("\\%", "%").replace("--", "–").replace("~", " ")
    a = re.sub(r"\\mathbb\{F\}", r"\\mathbb{F}", a)
    a = " ".join(a.split())
    # plain numbers need no math mode in the arXiv abstract field
    a = re.sub(r"\$([0-9.,%()–\s]+)\$", r"\1", a)
    a = a.replace("$–$", "–")
    a = re.sub(r"\$n=([0-9]+)\$", r"n = \1", a)
    assert not re.search(r"\\(?!mathbb|times|ge|le|ldots|dots|subseteq|mathrm|in|setminus|lceil|rceil)[A-Za-z]+", a), a
    return a


def build(paper):
    name = paper.parent.name
    work = DIST / f"{name}-build"
    shutil.rmtree(work, ignore_errors=True)
    shutil.copytree(paper, work, ignore=shutil.ignore_patterns("main.pdf", "*.aux", "*.log", "*.bbl", "*.blg", "*.fls", "*.fdb_latexmk", "*.out"))
    run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "-quiet", "main.tex"], work)
    tex = (paper / "main.tex").read_text()
    files = ["main.tex", "main.bbl"] + [f if f.endswith(".tex") else f + ".tex" for f in inputs(tex)]
    stage = DIST / f"{name}-arxiv"
    shutil.rmtree(stage, ignore_errors=True)
    stage.mkdir(parents=True)
    for f in files:
        shutil.copy(work / f, stage / f)
    for _ in range(2):
        run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape", "main.tex"], stage)
    log = (stage / "main.log").read_text(errors="replace")
    bad = re.findall(r".*(?:undefined|Rerun to get).*", log)
    if bad:
        raise SystemExit(f"{name}: {bad[:5]}")
    tarball = DIST / f"{name}-arxiv.tar.gz"
    with tarfile.open(tarball, "w:gz") as t:
        for f in files:
            t.add(stage / f, arcname=f)
    title = re.search(r"\\title\{(.*?)\}\n", tex, re.S).group(1).replace("\\\\", " ")
    title = " ".join(title.split())
    m = META[name]
    lines = [f"Title: {title}", "Authors: Tyler Duic", f"Categories: {m['categories']}",
             f"Comments: {m['comments']}"]
    if m["msc"]:
        lines.append(f"MSC classes: {m['msc']}")
    lines += ["License: CC BY 4.0 (suggested)", "", "Abstract:", abstract_text(paper), "",
              f"Files in {tarball.name}: {', '.join(files)}"]
    (DIST / f"{name}-arxiv-metadata.txt").write_text("\n".join(lines) + "\n")
    shutil.copy(stage / "main.pdf", DIST / f"{name}-arxiv-preview.pdf")
    print(f"{name}: {tarball.relative_to(ROOT)} ({tarball.stat().st_size // 1024} KB), files: {files}")


def main():
    DIST.mkdir(exist_ok=True)
    papers = sorted(p for p in ROOT.glob("*/paper") if (p / "main.tex").exists())
    if not papers:
        raise SystemExit("no papers found")
    for p in papers:
        build(p)


if __name__ == "__main__":
    main()
