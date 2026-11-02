"""Certificate and identity manifests match the shipped files."""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def test_cert_manifest():
    man = json.loads((ROOT / "all_d/exact_t0_v2/cert_manifest.json").read_text())
    for name, info in man["files"].items():
        p = ROOT / "all_d/exact_t0_v2/cert" / name
        assert p.is_file(), f"missing certificate file {name}"
        assert p.stat().st_size == info["bytes"], name
        assert sha(p) == info["sha256"], name


def test_gen_manifest_cert_hashes():
    gen = json.loads((ROOT / "lean/layerD_t0/gen_manifest.json").read_text())
    for name in ("blocks.jsonl", "multipliers.json", "qubit.json", "sites.json"):
        assert gen[f"cert/{name}"] == sha(ROOT / "all_d/exact_t0_v2/cert" / name), name
    assert gen["cert_path"] == "all_d/exact_t0_v2/cert"


def test_identity_manifest_totals():
    ident = json.loads((ROOT / "lean/layerD_t0/identity_manifest.json").read_text())
    total = sum(v["files"] for v in ident.values() if isinstance(v, dict) and "files" in v)
    run = json.loads((ROOT / "evidence/run2.json").read_text())
    assert total == run["modules_total"] == 8199
    modules = [ln.strip() for ln in (ROOT / "lean/layerD_t0/identity_modules.txt").read_text().splitlines()
               if ln.strip() and not ln.strip().startswith("#")]
    assert len(modules) == 8199, len(modules)
    # Every module name in the list must resolve to a soundness file or a
    # generated-module name (Gen/Id/...), never to a path outside the folder.
    for m in modules:
        assert m.startswith("LayerDT0.") or m.startswith("LayerDProto."), m


def test_identity_generator_hashes():
    ident = json.loads((ROOT / "lean/layerD_t0/identity_manifest.json").read_text())
    scripts = ident["scripts"]
    # Keys are paths relative to lean/layerD_t0, with ../layerD_proto/ for
    # the proto helpers. Resolve them folder-locally.
    base = ROOT / "lean/layerD_t0"
    for rel, want in scripts.items():
        p = (base / rel).resolve()
        assert str(p).startswith(str(base.resolve().parent.resolve())), rel
        assert p.is_file(), rel
        assert sha(p) == want, rel
