#!/usr/bin/env python3
"""Layer D (t = 0): regenerate every generated Lean module from the certificate into a temporary directory and
compare SHA-256 hashes with gen_manifest.json (and, for the committed modules, with the files in LayerDT0/Gen/).
The manifest also pins the certificate itself: the SHA-256 of its four files (cert/...) and its path (cert_path).

Usage: python3 gen_manifest.py [--write]   (prints OK on success)
"""
import hashlib, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
MAN = os.path.join(HERE, "gen_manifest.json")
GEN = os.path.join(HERE, "LayerDT0", "Gen")
STEPS = ["gen_small.py", "gen_sites.py", "gen_pd.py", "gen_assemble.py"]


def hashes(root):
    out = {}
    for d, _, fs in os.walk(root):
        for f in fs:
            p = os.path.join(d, f)
            out[os.path.relpath(p, root)] = hashlib.sha256(open(p, "rb").read()).hexdigest()
    return out


def cert_hashes():
    """SHA-256 of the certificate files the modules are generated from (keys cert/<file>), and its path."""
    sys.path.insert(0, HERE)
    import t0data as D
    out = {f"cert/{f}": hashlib.sha256(open(os.path.join(D.CERT, f), "rb").read()).hexdigest()
           for f in ("blocks.jsonl", "multipliers.json", "qubit.json", "sites.json")}
    out["cert_path"] = os.path.relpath(D.CERT, os.path.normpath(os.path.join(HERE, "..", "..")))
    return out


def main():
    with tempfile.TemporaryDirectory() as tmp:
        env = dict(os.environ, LAYERD_T0_GEN=tmp)
        for s in STEPS:
            subprocess.run([sys.executable, os.path.join(HERE, s)], cwd=HERE, env=env, check=True, capture_output=True)
        h = hashes(tmp)
    h.update(cert_hashes())
    if "--write" in sys.argv:
        json.dump(h, open(MAN, "w"), indent=1, sort_keys=True)
        print("wrote", MAN)
        return
    want = json.load(open(MAN))
    bad = sorted(k for k in set(h) | set(want) if h.get(k) != want.get(k))
    committed = hashes(GEN)
    bad += sorted(k for k in committed if k in h and committed[k] != h[k])
    print("OK" if not bad else "MISMATCH " + " ".join(bad[:20]))


if __name__ == "__main__":
    main()
