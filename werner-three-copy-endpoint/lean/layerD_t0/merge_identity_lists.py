#!/usr/bin/env python3
"""Merge per-family module lists written by parallel gen_identity_t0.py runs into identity_modules.txt.

Usage: python3 merge_identity_lists.py FAM:LIST [FAM:LIST ...]   (each LIST's lines of family FAM replace that
family's part lines in identity_modules.txt, after its Pos / Orb lines)
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
MAIN = os.path.join(HERE, "identity_modules.txt")
lines = open(MAIN).read().splitlines()
for arg in sys.argv[1:]:
    fam, path = arg.split(":", 1)
    mp = f"LayerDT0.Gen.Id.F{fam}"
    grid = (f"{mp}.Pos", f"{mp}.Orb")
    new = [l for l in open(path).read().splitlines()
           if (l.startswith(mp + ".") and l not in grid) or l.startswith(f"# family {fam} parts")]
    lines = [l for l in lines if not ((l.startswith(mp + ".") and l not in grid) or l.startswith(f"# family {fam} parts"))]
    i = lines.index(f"{mp}.Orb") + 1
    lines[i:i] = new
open(MAIN, "w").write("\n".join(lines) + "\n")
print("merged", sys.argv[1:])
