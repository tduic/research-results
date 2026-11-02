# Independent statement check — summary

- Status: Complete (Nov 2, 2026). Verdict: faithful.
- Checked by an independent agent that had not seen the work producing the
  proof; the proof term was out of scope.
- Statement checked:
  `theorem werner3_endpoint_all_d : ∀ (d : ℕ) (C : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ), C.rank ≤ 2 → 0 ≤ WernerEndpoint.qfun C`
- `qfun` is q, proved in Lean: `lean/statement_check/Final/QCheck.lean`
  defines its own `myq` from the formula (the six proper partial traces
  written out on index triples, Mathlib's `Matrix.trace` for the full
  trace, `Complex.normSq` for squared entries) and proves
  `qfun_eq_myq : ∀ d C, WernerEndpoint.qfun C = myq C`
  (axioms: propext, Classical.choice, Quot.sound); `restated` restates
  the final theorem with `myq`.
- Rank: `C.rank` is Mathlib's `Matrix.rank` over ℂ, checked by `rfl`;
  `≤ 2` in ℕ, no coercions.
- Nothing shadowed: the theorem has no binders before the colon;
  `Final.lean` has no `variable`/`open`. No declaration named qfun,
  rank, Matrix, Fin, Complex or Real exists in the project other than
  the real `qfun`; no notation, macro_rules, syntax, elab, export
  or axiom commands in the import chain (two tactic macros in
  `L5_Tables.lean` only).
- Sanity: d = 1, C = [c]: `qfun = ‖c‖²/8` proved in Lean, matching
  $1 - 3/2 + 3/4 - 1/8$.
- `lean/statement_check/Final/qcheck.py`: an independent numpy einsum q
  vs a literal transcription of the Lean definitions on random complex
  C (d = 1, 2, 3; ranks 1, 2, 3, full): max relative difference
  approximately 3e-15.
- Nothing weaker: d ranges over all of ℕ (d = 0: every sum empty, q = 0).
- Re-run a check (with the Lean project in this folder):
  `cd lean && lake env lean statement_check/Final/QCheck.lean`
  (requires the Mathlib cache; the full build is the `lean` level of
  `verify.sh`).
