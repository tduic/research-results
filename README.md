# Research results

Finished results from Tyler Duic's research program, published once they have cleared the full verification bar. Each folder is self-contained: a paper (LaTeX source and PDF), a write-up, the code and data behind every number, and the checks that CI runs on every push.

| Result | Area | What it shows | Paper |
|---|---|---|---|
| [**DQI finite-size correction**](dqi-finite-size/) | Quantum advantage | Google's verifiable DQI instance overstates its classical gap 14–18.5× per quantum run across its whole resource table (16.8× at the headline instance). A finite-size law built on the Airy edge asymptotic predicts DQI's shortfall within 4.3%; an n = 96 instance (~9.1M Toffoli per run, 2,510 logical qubits) restores the claimed margin. | [PDF](dqi-finite-size/paper/main.pdf) |
| [**Trifferent codes**](trifferent-codes/) | Combinatorics | New lower bounds T(10) ≥ 30, T(11) ≥ 36, T(12) ≥ 48, T(16) ≥ 108, T(17) ≥ 109, each above every bound we found in the literature, with every code verified in Lean 4. | [PDF](trifferent-codes/paper/main.pdf) |

## What it takes to appear here

- **Every number has been independently checked.** A separate reviewer re-derived or re-ran each headline result against the raw outputs, and a final audit checked every claim in these write-ups against the data shipped here.
- **Every mathematical claim stated as proved is formalized in Lean 4** — pinned toolchain and Mathlib, no `sorry`, no new axioms, no `native_decide`, `#print axioms` showing only `propext`, `Classical.choice` and `Quot.sound` — and an independent reviewer has checked that the Lean statement says what the write-up claims. Numerical and empirical results are labelled as such, with their caveats.
- **Nothing in progress, nothing minor.** Results are added only when the work on them is finished and they say something worth knowing on their own.

## Running the checks

```
pip install numpy scipy mpmath pytest
python -m pytest -q tests
```

The tests re-derive the headline numbers (the DQI score law derived three ways and checked against the instance ensemble, the Airy law on fresh points outside its fitting range, every trifferent code re-checked triple by triple) and check the Lean sources and axiom reports. CI also builds the Lean proofs and every paper from scratch, checks that the committed PDFs match their sources, and builds arXiv-ready source bundles (`python tools/make_arxiv.py`; downloadable from each CI run as the `arxiv-bundles` artifact).

## Contact

Corrections and pointers to prior work are welcome — open an issue.

## License

Code, data and Lean proofs are released under the [Apache License 2.0](LICENSE). If you use a result, please cite this repository.
