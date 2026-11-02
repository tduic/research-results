# Recorded build run — summary

This is a summary of the recorded complete build of the proof shipped in
this folder. It is not itself a build log; the `lean` level of `verify.sh`
rebuilds the proof and re-checks the axioms from an actual build.

- Run: 41356979845, job `t0full`, one 8-CPU, 9 GB container.
- Started 2026-11-01 22:26:47 UTC, finished 2026-11-02 10:29:39 UTC
  (12 h 3 min wall time, 18.0 CPU-hours summed over the modules).
- Regeneration from the shipped v2 certificate matched
  `lean/layerD_t0/identity_manifest.json`; all three families sum to zero.
- All 8,199 modules of `lean/layerD_t0/identity_modules.txt`
  kernel-checked with return code 0
  (prep 9, light 7,829, heavy 145, final 216).
- 62 attempts of the parallel light pass were killed for memory and passed
  in the serial retry; the run summary records no Lean error anywhere.
- Peak memory was 6.40 GB for one module (`F31.P576x1`).
- `LayerDT0.Final` built, with the axiom lists in `evidence/axioms.txt`.

Machine-readable form of these figures: `evidence/run2.json`, which is
what `scripts/generate_numbers.py` reads to produce `paper/numbers.tex`.
