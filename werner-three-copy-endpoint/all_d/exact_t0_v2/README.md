# Compact v2 t = 0 certificate (shipped data)

`cert/` holds the four exact rational certificate files used by the
Lean proof in this folder:

- `blocks.jsonl` — 1,000 blocks
- `multipliers.json` — multipliers and rows
- `qubit.json` — qubit modules
- `sites.json` — site modules

Hashes, byte counts, and bit counts are in `cert_manifest.json`;
`cert_stats.py` recomputes the statistics from the files.
The standalone exact verifier is at `../exact_t0/verify_t0.py`; run it as:

```
python3 -I ../exact_t0/verify_t0.py cert
```

from this directory (about 136 s on the recorded machine).
The Lean generators read this certificate by default through
`../lean/layerD_t0/t0data.py` (same relative layout as in the proof
sources: `all_d/exact_t0_v2/cert` under this folder's root).
