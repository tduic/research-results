# Independent statement check: the final theorem

Verdict: faithful (see `../../evidence/statement-check-summary.md`).

`QCheck.lean` defines its own `myq` from the formula for $q$ and proves
`qfun_eq_myq : ∀ d C, WernerEndpoint.qfun C = myq C`;
`restated` restates the final theorem with `myq`.
`Frob.lean` identifies the squared Frobenius norm; `D1.lean` checks
rank and the $d = 1$ sanity case. `qcheck.py` compares an independent
NumPy computation with a literal transcription of the Lean definitions.

Re-run (with the Mathlib cache in `lean/`):

```
cd lean && lake env lean statement_check/Final/QCheck.lean
```
