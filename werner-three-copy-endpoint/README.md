# Three-copy Werner endpoint: a complete kernel-only Lean proof for every dimension

> **Status:** Complete (November 2026) · complete kernel-only Lean proof in Lean 4, standard axioms only · independent statement check: faithful · paper is a preprint (not peer reviewed)
>
> **Paper:** [A complete kernel-only Lean proof of the three-copy Werner endpoint for every dimension](paper/main.pdf) ([LaTeX source](paper/main.tex), [references](paper/references.bib))
>
> **What is new here, and what is not.** The theorem itself is **not** new. T. S. Tomar (2026, Zenodo preprint, not peer reviewed) proves the three-copy endpoint for every $d \ge 3$. What I contribute is, as far as I have found, the **first complete kernel-only Lean proof of that endpoint for every $d$**: Tomar's work is kernel-checked in Lean only for $3 \le d \le 8$, and states that "the case $d \ge 9$ is not formalized". I do not claim the theorem, and I do not claim anything about any other number of copies.

## Problem

For $C$ an operator on $(\mathbb{C}^d)^{\otimes 3}$ of rank at most $2$, let

$$q_\alpha(C) = \sum_{S \subseteq \{1,2,3\}} (-\alpha)^{|S|} \lVert \operatorname{Tr}_S C \rVert_F^2, \qquad q = q_{1/2}.$$

The Werner state $\rho_\alpha \propto I - \alpha F$ is three-copy undistillable exactly when $q_\alpha \ge 0$ on rank-$\le 2$ operators $C$. By the continuation identity, $q_\alpha \ge (1-2\alpha)(1-\alpha)^2 \lVert C \rVert^2$ on $[0, 1/2]$ holds in dimension $d$ exactly when the endpoint $q \ge 0$ holds there. The endpoint is therefore the sharp three-copy statement: it settles three-copy undistillability up to the one-copy threshold.

## Result

**Theorem.** For every $d$ and every operator $C$ on $(\mathbb{C}^d)^{\otimes 3}$ of rank at most $2$, $q(C) \ge 0$.

In Lean 4, this is the theorem `LayerDT0.werner3_endpoint_all_d`:

```lean
theorem werner3_endpoint_all_d :
    ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ WernerEndpoint.qfun C
```

I prove it for every $d \in \mathbb{N}$ in Lean, including the degenerate cases; the physically substantive range is $d \ge 3$, which is the range Tomar proves by non-formalized means. Nothing in this folder should be read as claiming a new mathematical theorem about Werner states. My claim is about formalization: one proof, checked by the Lean kernel from scratch, covering every dimension at once, by a route that does not depend on Tomar's proof.

## Method (proof outline only)

I use a strengthened moment relaxation, taken to its $t = 1/d \to 0$ limit, plus a lemma chain that carries a single $t = 0$ certificate back to every dimension:

1. **Moment lift.** A rank-$\le 2$ operator $C$ lifts to moments built from its factors. Twirling over the relevant symmetries lands in a commutative algebra spanned by diagram operators, and the question becomes whether a certain moment functional is nonnegative on the physical moment set.
2. **Trace coordinates.** Replacing orbit variables by trace coordinates $m$ makes the relaxation $d$-free except for the site modules: the objective and the equality rows are trace functionals, so they have $d$-free coefficients in $m$. Only the positive-semidefinite blocks depend on $d$, through site matrices $N_r(p)(t)$ with $t = 1/d$.
3. **The $t = 0$ certificate.** At $t = 0$ no site module degenerates: every module's limit matrices span the full matrix algebra. An exact rational certificate $X_b \succeq 0$ and multipliers $\lambda$ for the $t = 0$ relaxation therefore suffices, by the lemma chain, to prove $q(C) \ge 0$ in every dimension. The certificate shipped here is the compact v2 certificate: it passes the standalone exact verifier `verify_t0.py`, is $11.1\times$ smaller in bits than the v1 certificate (2.11M bits versus 23.48M bits), and has correction denominator 131 bits (v1: 5,941 bits). The exact verifier reports 1,000 blocks positive definite.
4. **Lemma chain (Lean layers B and C, `AllD`).** The chain is an abstract theorem, `endpoint_of_t0_cert`: given a $t = 0$ certificate, the endpoint follows in every dimension. Its steps are embedding (a physical point of dimension $e$ embeds into $d \ge \max(e, 4)$ without changing $m$ or $q$), validity of the pipeline at dimension $d$, $d$-freeness of rows and objective in $m$, positivity of the blocks at $t = 1/d$ as positive multiples of compressions of the true blocks, continuity to $t = 0$ (the positive-semidefinite cone is closed), and pairing ($q(C)$ equals a sum of nonnegative pairings plus $\lambda_{\mathrm{trace}} \ge 0$).
5. **Layer D: the certificate identity in the kernel (the hard part).** The one hypothesis of `endpoint_of_t0_cert` that is not generic is the exact identity for the explicit certificate data, `IdentityT0`: for every orbit-invariant $\mu$, the objective equals the sum over blocks of $\langle X_b, L_b(\mu) \rangle$ plus the row terms. Layer D proves this identity in the Lean kernel. The bridge rewrites each block pairing as a sum over family parts; the glue reduces the identity to `FamZero` for the three families, i.e. to literal-free family totals; coupled block parts fold through a kernel-checked full-rank re-presentation. The generated identity modules are pinned by SHA-256 in `lean/layerD_t0/identity_manifest.json`, together with the hashes of the four certificate files (`all_d/exact_t0_v2/cert/blocks.jsonl`, `multipliers.json`, `qubit.json`, `sites.json`).

## Verification

- **Lean 4 / Mathlib, shipped in this folder (`lean/`).** The final theorem and the identity it rests on were built in one run from a clean checkout: run 41356979845, in one 8-CPU, 9 GB container, started 2026-11-01 22:26:47 UTC and finished 2026-11-02 10:29:39 UTC (12 h 3 min wall time, 18.0 CPU-hours summed over the modules). All 8,199 modules of `lean/layerD_t0/identity_modules.txt` kernel-checked with return code 0 (prep 9, light 7,829, heavy 145, final 216); 62 attempts of the parallel light pass were killed for memory and passed in the serial retry; the run summary records no Lean error anywhere. Peak memory was 6.40 GB for one module (`F31.P576x1`). Regeneration from the v2 certificate matched `identity_manifest.json`, and all three families sum to zero. See [`evidence/run2-summary.md`](evidence/run2-summary.md), [`evidence/run2.json`](evidence/run2.json), and [`evidence/axioms.txt`](evidence/axioms.txt). The identity modules themselves are generated at build time from the shipped certificate by `lean/layerD_t0/gen_identity_t0.py` (see `lean/layerD_t0/run_identity.sh` and `run_full.sh`); I ship the generators, the certificate, and the manifest, not 8,199 pre-generated files.
- **Axioms.** `#print axioms` gives, for both `LayerDT0.identityT0` and `LayerDT0.werner3_endpoint_all_d`, exactly `[propext, Classical.choice, Quot.sound]`: the standard Lean/Mathlib axioms, no new axioms. I scanned every shipped Lean file for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, and `opaque` outside comments; the scan found none (see `tests/test_lean_scan.py`).
- **Independent statement check.** An independent agent that had not seen the work producing the proof checked the final theorem's statement and rated it **faithful**. `qfun` is proved equal in Lean to an independently written `myq` (the six proper partial traces written out on index triples, Mathlib's `Matrix.trace` for the full trace, `Complex.normSq` for squared entries), the theorem is restated with `myq`, rank is checked to be Mathlib's `Matrix.rank` with no coercions, and no shadowing declarations, notation, macros, or extra axioms were found in the import chain (two tactic macros in one tables file only). Sanity checks: at $d = 1$, $q = \lVert c \rVert^2 / 8$ proved in Lean, matching $1 - 3/2 + 3/4 - 1/8$; an independent NumPy comparison against a literal transcription of the Lean definitions on random complex $C$ ($d = 1, 2, 3$; ranks 1, 2, 3, full) gave maximum relative difference approximately $3 \times 10^{-15}$. The proof term itself was out of scope for that check; the kernel build above is what checks it. The statement-check code is shipped in `lean/statement_check/Final/`; see [`evidence/statement-check-summary.md`](evidence/statement-check-summary.md).
- **Exact certificate check (non-Lean).** The t = 0 certificate passes the standalone exact verifier `verify_t0.py` (shipped at `all_d/exact_t0/verify_t0.py`, run as `python3 -I all_d/exact_t0/verify_t0.py all_d/exact_t0_v2/cert`). This is a rational-arithmetic check of the certificate data, not a substitute for the Lean identity proof; Layer D is what moves the same identity into the kernel. Its runtime is about 136 s on the recorded machine; see Verify this result.

## Prior art

- Tejasvi Singh Tomar, *Undistillability of Werner states from three, four and five copies*, Zenodo, DOI 10.5281/zenodo.23718035, v4, October 2026 (preprint, not peer reviewed), proves the three-copy endpoint for every $d \ge 3$. Its route uses a base certificate polynomial in $1/d$ for $d \ge 9$, plus exact certificates for smaller $d$. It is kernel-checked in Lean for $3 \le d \le 8$ only; the paper states that "the case $d \ge 9$ is not formalized".
- The all-$d$ $t = 0$ certificate in this folder is therefore an independent confirmation by a different route, not a new theorem. This proof is self-contained: it does not use Tomar's certificate, argument, or result as a step. It proves the endpoint from the $t = 0$ certificate and lemma chain shipped in this folder, and its Lean proof does not import or formalize Tomar's proof. The new contribution claimed here is the complete kernel-only Lean proof for every $d$, closing the formalization gap at $d \ge 9$.
- As far as I have found, no other work formalizes the all-$d$ endpoint in Lean. If you know of an earlier complete kernel-only Lean proof for every $d$, please open an issue.

## Caveats

- The paper in this folder is a preprint. It has not been peer reviewed, and neither has Tomar (2026).
- Nothing in this folder concerns any other number of copies.
- My claim is the all-$d$ proof via the $t = 0$ certificate only.
- The Lean build is long and memory-heavy (see Verification). Rebuilding it is a manual, documented level only; it is not run by CI, and CI passing does not mean the Lean proof was rebuilt. CI checks the shipped evidence, the tests, and the paper only (see Verify this result).
- Everything needed to verify this result is in this folder. Nothing in this folder refers outside it except the pinned Mathlib dependency (Lean v4.24.0, Mathlib v4.24.0, in `lean/lake-manifest.json`) and the public prior-art citation above.

## Verify this result

Everything needed is in this folder; you do not need anything else. To fetch only this folder:

```
git clone --filter=blob:none --sparse https://github.com/tduic/research-results
cd research-results && git sparse-checkout set werner-three-copy-endpoint && cd werner-three-copy-endpoint
python3 -m pip install -r requirements.txt
```

Then pick how deep to go:

| Command | What it checks | Time |
|---|---|---|
| `./verify.sh` | Quick checks: tests, including the standalone exact verifier on the shipped certificate (about 132 s), paper numbers regenerated from shipped data and matching, Lean scan (no forbidden tokens), certificate manifest hashes | about 2-3 min |
| `./verify.sh paper` | Rebuilds the paper (needs TeX Live) and checks the committed PDF matches its source | ~1 min |
| `./verify.sh lean` | **Manual only, not run by CI.** Regenerates the identity modules from the shipped certificate, builds the Lean proofs in `lean/` (needs [elan](https://github.com/leanprover/elan), Mathlib cache), and checks the final theorem's axioms | ~12 h wall, ~18 CPU-hours on the recorded build; do not run this in CI |
| `./verify.sh all` | Quick plus paper (lean is excluded by design; run it explicitly if you want it) | about 3-4 min |
| `python3 -I all_d/exact_t0/verify_t0.py all_d/exact_t0_v2/cert` | Standalone exact verifier for the t = 0 certificate (needs numpy) | ~136 s on the recorded machine |

CI runs the quick and paper jobs with a checkout of this folder only: [workflow](../.github/workflows/werner-three-copy-endpoint.yml) on every change to the folder, plus weekly. There is deliberately no Lean job in CI.
