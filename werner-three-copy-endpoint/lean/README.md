# Lean proof shipped in this folder

Pinned project: Lean v4.24.0, Mathlib v4.24.0
(`lean-toolchain`, `lake-manifest.json`).

- `WernerEndpoint/` — the abstract lemma chain, including
  `endpoint_of_t0_cert`: given a $t = 0$ certificate, the endpoint
  follows in every dimension.
- `layerD_t0/LayerDT0/` — Layer D soundness modules, plus the generated
  data modules in `LayerDT0/Gen/` (committed, SHA-256 pinned by
  `layerD_t0/gen_manifest.json`).
- `layerD_t0/` — the generators. The identity modules themselves are
  generated at build time from the shipped certificate
  (`../all_d/exact_t0_v2/cert/`) by `gen_identity_t0.py` and pinned by
  `identity_manifest.json`; they are not pre-generated files.
- `layerD_proto/LayerDProto/` — Lean modules imported by the generated
  identity modules (packed rows, re-presentation, families), plus the
  Python helpers the generators import (`certdata.py`, `gen_identity.py`,
  `route2.py`, `reduced.py`, `gen_asm.py`, `recompress.py`,
  `timebench.py`).
- `statement_check/Final/` — the independent statement check of the
  final theorem (`QCheck.lean`, `Frob.lean`, `D1.lean`, `qcheck.py`).

## Build (manual only, not run by CI)

From this folder:

```
cd lean
lake exe cache get || true
sh layerD_t0/run_full.sh
```

`run_full.sh` regenerates the identity modules if they differ from
`identity_manifest.json`, kernel-checks all 8,199 modules in
`layerD_t0/identity_modules.txt`, builds `LayerDT0.Final`, and prints
its axioms. Recorded build: 12 h 3 min wall, 18.0 CPU-hours, peak
6.40 GB for one module; see `../evidence/run2.json`.
Rebuilding is the `lean` level of `../verify.sh`; do not run it in CI.
