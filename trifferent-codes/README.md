# Trifferent codes: new lower bounds at lengths 10, 11, 12, 16 and 17

> **Status:** Complete (October 2026) · every code verified in Lean 4 (kernel-checked, standard axioms only) · independent statement review and re-check · regression tests in [`tests/test_trifference.py`](../tests/test_trifference.py)

## Problem

A code C ⊆ {0,1,2}ⁿ is **trifferent** if any three distinct codewords have a coordinate where all three differ. T(n) is the largest size of a trifferent code of length n; equivalently, the largest k for which a perfect hash family PHF(n; k, 3, 3) exists. The exponential growth rate of T(n) is a long-standing open problem, and small-n values are a standard benchmark (Kurz 2023 determined T(7), T(8), T(9) exactly).

## Results

| n | Best published bound (closure) | **New bound** | Gain | Construction |
|---|---|---|---|---|
| 10 | 29 | **T(10) ≥ 30** | +1 | union of orbits of ⟨x ↦ x + 1⟩ × (cyclic shift by 2) |
| 11 | 30 | **T(11) ≥ 36** | +6 | union of orbits of ⟨x ↦ x + 1⟩ × (cyclic shift) |
| 12 | 36 | **T(12) ≥ 48** | +12 | union of orbits of ⟨x ↦ x + 1⟩ × (cyclic shift by 2) |
| 16 | 83 | **T(16) ≥ 108** | +25 | 4 cosets of a minimal [16, 3]₃ linear code |
| 17 | 108 | **T(17) ≥ 109** | +1 | the n = 16 code extended by one coordinate and one word (Kurz, Lemma 1) |

The codes are in [`codes/`](codes/) as JSON lists of words over {0, 1, 2}.

**The baseline.** "Best published bound" is the closure of everything we found in the literature — T(1..9) exact (Kurz 2023), T(14) ≥ 81 and T(19) ≥ 243 from minimal linear codes (Bishnoi, D'haeseleer, Gijswijt, Potukuchi), and the perfect-hash-family table of Walker and Colbourn (2007, Table 6; transcribed in [`data/`](data/)) — under the two elementary rules T(n) ≥ T(n−1) + 1 and *shortening*, T(n−1) ≥ ⌈2T(n)/3⌉ (keep the words avoiding the rarest symbol in one coordinate and delete that coordinate). The test suite recomputes this closure and asserts that each of the five bounds is strictly above it.

## Verification

- **Lean 4 / Mathlib** ([`lean/`](lean/), pinned toolchain and Mathlib). `Trifferent` is defined directly over `Finset (Fin n → Fin 3)`, and each result is the statement `∃ C : Finset (Fin n → Fin 3), Trifferent C ∧ k ≤ C.card`. A bitmask checker is proved sound once (`trifferent_of_check`) and evaluated by the kernel with `decide`, in chunks. No `sorry`, no new axioms, no `native_decide`; `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for every bound ([`lean/logs/`](lean/logs/)). CI rebuilds the whole project on every push.
- **Independent statement check** ([`lean/Trifference/Statement.lean`](lean/Trifference/Statement.lean)). A separate reviewer wrote an independent definition of trifference, proved it equivalent to the one used, restated each bound in their own words, and proved that the definition rejects a non-trifferent code (so it is not vacuous).
- **Independent re-check** ([`verification/rt_check.py`](verification/rt_check.py)). Decodes every Lean certificate exactly as the Lean decoder does, confirms it is the same set of words as the JSON code, and re-checks every triple with separate code (0 bad triples for all five codes).
- **Regression tests.** Every JSON code is re-checked triple by triple, the Lean certificates are matched to the JSON codes, and the published-baseline closure is recomputed.

## Novelty check and remaining risk

Trifferent codes are exactly perfect hash families PHF(n; k, 3, 3), so we checked the PHF literature as well as the trifferent-code literature: Kurz's papers, Walker and Colbourn 2007 (their best values for N = 10…18 are 29, 30, 36, 37, 48, 57, 81, 82, 83, each below the bound used here), the Dwyer covering-array database, and Martirosyan and van Trung's tables. The online PHF tables that succeeded the 2007 table (phftables.com and R. E. Dougherty's tables) could not be reached, so a better entry posted only there cannot be ruled out. Please let us know if you are aware of one.

Lengths 13 and 18 are deliberately not listed: codes of size 54 and 162 exist there, but they equal the shortenings of known minimal linear codes, so they are not new.

## Reproducing

```
python -m pytest -q ../tests/test_trifference.py         # re-check codes, baseline and certificates
python3 -I verification/rt_check.py .                     # independent decoder + triple check
cd lean && lake exe cache get && ./ci-build.sh            # Lean build (≈ 5 minutes after the Mathlib cache)
```
