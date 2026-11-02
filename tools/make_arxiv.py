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
    "werner-three-copy-endpoint": dict(
        categories="quant-ph (primary)",
        comments="4 pages. Complete kernel-only Lean 4 proof of the three-copy Werner endpoint for every dimension: https://github.com/tduic/research-results/tree/main/werner-three-copy-endpoint",
        msc="", acm=""),
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


# Commands safe to leave in an arXiv metadata abstract. This is the full
# set, defined once: standard LaTeX math symbols, Greek letters, operators,
# relations, arrows, delimiters, font and text commands, and citation and
# reference commands. Single-letter commands (for example \\C, \\R, \\N for
# number fields) are also allowed, since they are the usual field shorthands.
# Deliberately NOT in this set, so they still fail loudly instead of
# shipping broken metadata: anything that defines or pulls in content
# (\\def, \\newcommand, \\renewcommand, \\input, \\include,
# \\usepackage, \\begin, \\end) and any other multi-letter command,
# which is a custom macro the metadata builder does not know how to handle.
SAFE_ABSTRACT_COMMANDS = frozenset({
    # Greek letters
    "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta",
    "iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", "sigma",
    "tau", "upsilon", "phi", "chi", "psi", "omega",
    "varepsilon", "vartheta", "varpi", "varrho", "varsigma", "varphi",
    "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Upsilon",
    "Phi", "Psi", "Omega",
    # Operators and functions
    "sum", "prod", "int", "iint", "iiint", "oint", "lim", "limsup",
    "liminf", "sup", "inf", "min", "max", "arg", "det", "gcd", "deg",
    "dim", "ker", "hom", "sin", "cos", "tan", "cot", "sec", "csc",
    "sinh", "cosh", "tanh", "coth", "arcsin", "arccos", "arctan",
    "log", "ln", "lg", "exp", "Pr", "Tr", "tr", "rank", "trace", "diag",
    # Relations
    "le", "leq", "ge", "geq", "ne", "neq", "equiv", "approx", "cong",
    "sim", "simeq", "propto", "ll", "gg", "prec", "succ", "preceq",
    "succeq", "subset", "subseteq", "supset", "supseteq", "sqsubset",
    "sqsupset", "sqsubseteq", "sqsupseteq", "in", "ni", "notin", "owns",
    "mid", "parallel", "perp", "models", "vdash", "dashv", "asymp",
    "doteq", "triangleq", "coloneq",
    # Binary operators and symbols
    "pm", "mp", "times", "div", "cdot", "ast", "star", "circ", "bullet",
    "oplus", "ominus", "otimes", "oslash", "odot", "cup", "cap",
    "setminus", "wedge", "vee", "neg", "partial", "nabla", "infty",
    "aleph", "hbar", "ell", "emptyset", "varnothing", "forall",
    "exists", "top", "bot", "wr", "bigcup", "bigcap", "bigoplus",
    "bigotimes", "bigvee", "bigwedge", "sqcup", "sqcap", "uplus",
    "amalg", "diamond", "bigtriangleup", "bigtriangledown", "triangle",
    "clubsuit", "diamondsuit", "heartsuit", "spadesuit",
    # Arrows
    "to", "rightarrow", "leftarrow", "Rightarrow", "Leftarrow",
    "leftrightarrow", "Leftrightarrow", "mapsto", "longrightarrow",
    "longleftarrow", "longmapsto", "hookrightarrow", "hookleftarrow",
    "uparrow", "downarrow", "Uparrow", "Downarrow", "nearrow",
    "searrow", "swarrow", "nwarrow", "rightleftharpoons",
    # Delimiters
    "lVert", "rVert", "lvert", "rvert", "langle", "rangle", "lfloor",
    "rfloor", "lceil", "rceil", "lbrace", "rbrace", "Vert", "vert",
    # Fonts, accents, and text
    "mathbb", "mathcal", "mathbf", "mathrm", "mathit", "mathsf",
    "mathfrak", "mathscr", "text", "textbf", "textit", "texttt",
    "textsc", "emph", "overline", "underline", "hat", "widehat",
    "tilde", "widetilde", "bar", "vec", "dot", "ddot", "acute",
    "grave", "check", "breve", "quad", "qquad",
    # Dots and ellipses
    "ldots", "cdots", "vdots", "ddots", "dots",
    # Citations and references
    "cite", "citet", "citep", "ref", "eqref",
})


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
    for _cmd in re.findall(r"\\([A-Za-z]+)", a):
        assert len(_cmd) == 1 or _cmd in SAFE_ABSTRACT_COMMANDS, a
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
