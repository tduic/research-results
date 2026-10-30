# Trifferent codes: new lower bounds at lengths 10, 11, 12, 16 and 17

> **Status:** Complete (October 2026) · every code verified in Lean 4 (kernel-checked, standard axioms only) · independent statement review and re-check · paper is a preprint (not peer reviewed) · regression tests in [`tests/test_trifference.py`](../tests/test_trifference.py)
>
> **Paper:** [New lower bounds for trifferent codes of lengths 10, 11, 12, 16 and 17](paper/main.pdf) ([LaTeX source](paper/main.tex))

## Problem

A code C ⊆ {0,1,2}ⁿ is **trifferent** if any three distinct codewords have a coordinate where all three differ. T(n) is the largest size of a trifferent code of length n; equivalently, the largest k for which a perfect hash family PHF(n; k, 3, 3) exists. The exponential growth rate of T(n) is a long-standing open problem, and small-n values are a standard benchmark (Kurz 2024 determined T(7), T(8), T(9) exactly).

## Results

| n | Best published bound (closure) | **New bound** | Gain | Construction |
|---|---|---|---|---|
| 10 | 29 | **T(10) ≥ 30** | +1 | union of orbits of ⟨x ↦ x + 1⟩ × (cyclic shift by 2) |
| 11 | 30 | **T(11) ≥ 36** | +6 | union of orbits of ⟨x ↦ x + 1⟩ × (cyclic shift) |
| 12 | 36 | **T(12) ≥ 48** | +12 | union of orbits of ⟨x ↦ x + 1⟩ × (cyclic shift by 2) |
| 16 | 83 | **T(16) ≥ 108** | +25 | 4 cosets of a minimal [16, 3]₃ linear code |
| 17 | 108 | **T(17) ≥ 109** | +1 | the n = 16 code extended by one coordinate and one word (Kurz, Lemma 1) |

The codes are in [`codes/`](codes/) as JSON lists of words over {0, 1, 2}. Each also has a few-line algebraic description, given in the paper; [`verification/constructions.py`](verification/constructions.py) rebuilds every code from that description, and the tests confirm it matches the JSON exactly.

**The baseline.** "Best published bound" is the closure of everything I found in the literature — T(1..9) exact (Della Fiore–Gnutti–Polak 2022, Kurz 2024), T(14) ≥ 81 and T(19) ≥ 243 from minimal linear codes (Bishnoi, D'haeseleer, Gijswijt, Potukuchi), and the perfect-hash-family table of Walker and Colbourn (2007, Table 6; transcribed in [`data/`](data/)) — under the two elementary rules T(n) ≥ T(n−1) + 1 and *shortening*, T(n−1) ≥ ⌈2T(n)/3⌉ (keep the words avoiding the rarest symbol in one coordinate and delete that coordinate). The test suite recomputes this closure and asserts that each of the five bounds is strictly above it.

## Verification

- **Lean 4 / Mathlib** ([`lean/`](lean/), pinned toolchain and Mathlib). `Trifferent` is defined directly over `Finset (Fin n → Fin 3)`, and each result is the statement `∃ C : Finset (Fin n → Fin 3), Trifferent C ∧ k ≤ C.card`. A bitmask checker is proved sound once (`trifferent_of_check`) and evaluated by the kernel with `decide`, in chunks. No `sorry`, no new axioms, no `native_decide`; `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for every bound ([`lean/logs/`](lean/logs/)). CI rebuilds the whole project on every push.
- **Independent statement check** ([`lean/Trifference/Statement.lean`](lean/Trifference/Statement.lean)). A separately written definition of trifference is proved equivalent to the one used, each bound is restated with it, and the definition is shown to reject a non-trifferent code (so it is not vacuous).
- **Independent re-check** ([`verification/rt_check.py`](verification/rt_check.py)). Decodes every Lean certificate exactly as the Lean decoder does, confirms it is the same set of words as the JSON code, and re-checks every triple with separate code (0 bad triples for all five codes).
- **Regression tests.** Every JSON code is re-checked triple by triple, rebuilt from its description in the paper, and matched to its Lean certificate, and the published-baseline closure is recomputed.

## Novelty check and remaining risk

Trifferent codes are exactly perfect hash families PHF(n; k, 3, 3), so I checked the PHF literature as well as the trifferent-code literature: Kurz's papers, Walker and Colbourn 2007 (their best values for N = 10…18 are 29, 30, 36, 37, 48, 57, 81, 82, 83, each below the bound used here), the Dwyer covering-array database, and Martirosyan and van Trung's tables. The online PHF tables that succeeded the 2007 table (phftables.com and R. E. Dougherty's tables) could not be reached, so a better entry posted only there cannot be ruled out. If you know of one, please open an issue.

Lengths 13 and 18 are deliberately not listed: I also found codes of size 54 and 162 there, but those sizes equal the shortenings of known minimal linear codes, so they are not new bounds.

## Verify this result

Everything needed is in this folder; you do not need the rest of the repository. To fetch only this folder:

```
git clone --filter=blob:none --sparse https://github.com/tduic/research-results
cd research-results && git sparse-checkout set trifferent-codes && cd trifferent-codes
python3 -m pip install -r requirements.txt
```

Then pick how deep to go:

| Command | What it checks | Time |
|---|---|---|
| `./verify.sh` | Every code re-checked triple by triple, rebuilt from its description in the paper and matched to its Lean certificate; the literature baseline recomputed; an independent decoder and triple check | ~5 s |
| `./verify.sh lean` | Builds the Lean proofs from scratch (needs [elan](https://github.com/leanprover/elan)) and checks every theorem uses only the standard axioms | ~5 min after the Mathlib cache download |
| `./verify.sh paper` | Rebuilds the paper (needs TeX Live) and checks the committed PDF matches its source | ~1 min |
| `./verify.sh all` | All of the above | ~7 min |

CI runs the same commands with a checkout of this folder only: [checks and paper](../.github/workflows/trifferent-codes.yml) on every change to the folder, and the [Lean build](../.github/workflows/trifferent-codes-lean.yml) when the proofs or codes change, plus weekly.
