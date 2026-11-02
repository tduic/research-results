# Layer D: the certificate identity in the kernel

`LayerDT0/` holds the soundness modules and the generated data modules
in `LayerDT0/Gen/` (SHA-256 pinned by `gen_manifest.json`).
`Final.lean` proves `identityT0` from the three family zero checks and,
with it, `werner3_endpoint_all_d`.

- Bridge: `Bridge.lean` rewrites each block pairing as a sum over family
  parts, so the identity becomes a vanishing statement for family totals.
- Glue: `IdentityAsm.lean`, `IdentityUnit.lean`, `IdentityBlock.lean`,
  `IdentityDec.lean` reduce that statement to `FamZero` for the three
  families.
- Compute: the identity modules, generated at build time from the
  shipped certificate (`../all_d/exact_t0_v2/cert/`) by
  `gen_identity_t0.py`, pinned by `identity_manifest.json`, and listed
  in `identity_modules.txt` (8,199 modules).

## Build

From `lean/`:

```
sh layerD_t0/run_full.sh
```

`run_full.sh` regenerates the identity modules if they differ from the
manifest, kernel-checks all 8,199 modules, builds `LayerDT0.Final`, and
prints its axioms. Recorded build: 12 h 3 min wall, 18.0 CPU-hours,
peak 6.40 GB for one module; see `../evidence/run2.json`.
This is the `lean` level of `../verify.sh`; it is manual only and is
not run by CI.

The generators need the certificate at the folder-local default path
(`all_d/exact_t0_v2/cert` under this folder's root, via `t0data.py`),
or at the path given by the `LAYERD_CERT` environment variable.
