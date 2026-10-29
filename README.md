# Research results

Finished results from my research, published once they have cleared the full verification bar. Each folder is self-contained: a short paper (LaTeX source and PDF), a write-up, the code and data behind every number, and the checks that CI runs on every push.

| Result | Area | What it shows | Paper |
|---|---|---|---|
| [**DQI finite-size correction**](dqi-finite-size/) | Quantum advantage | Google's verifiable DQI instance overstates its classical gap 14–18.5× per quantum run across its whole resource table (16.8× at the headline instance). A finite-size law built on the Airy edge asymptotic predicts DQI's shortfall within 4.3%; an n = 96 instance (~9.1M Toffoli per run, 2,510 logical qubits) restores the claimed margin. | [PDF](dqi-finite-size/paper/main.pdf) |
| [**Trifferent codes**](trifferent-codes/) | Combinatorics | New lower bounds T(10) ≥ 30, T(11) ≥ 36, T(12) ≥ 48, T(16) ≥ 108, T(17) ≥ 109, each above every bound I found in the literature, with every code verified in Lean 4. | [PDF](trifferent-codes/paper/main.pdf) |

The papers are preprints: they have not been peer reviewed.

## What it takes to appear here

- **Every number is independently checked.** A separate review, working from the raw outputs rather than the original analysis, re-derived or re-ran each headline result, and a final audit checked every claim in these write-ups and papers against the data shipped here.
- **Every mathematical claim stated as proved is formalized in Lean 4.** Each proof uses a pinned toolchain and Mathlib, with no `sorry`, no new axioms and no `native_decide`, and `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. An independent check confirms that each Lean statement says what the write-up claims. Numerical and empirical results are labelled as such, with their caveats.
- **Nothing in progress, nothing minor.** A result is added only when the work on it is finished and it says something worth knowing on its own.

## How this work was done

I did this work with substantial help from AI models (Anthropic's Claude): searching, writing code and Lean proofs, and running the independent reviews described above. I directed the work and am responsible for every claim. That is why everything here is backed by code, data, tests and machine-checked proofs that anyone can rerun.

## Layout

```
<result>/
  README.md        write-up: bottom line, method, results, caveats, how to reproduce
  paper/           main.tex, references.bib, main.pdf (CI checks the PDF matches the source)
  experiments/ or verification/   code behind every number
  results/ or codes/, data/       outputs and inputs, as JSON
  lean/            Lean 4 proofs (pinned Lake project), where a result is proved
tests/             pytest suite run by CI: re-derives the headline numbers and ties each paper to its data
tools/make_arxiv.py   builds standalone arXiv source bundles for every paper
```

## Running the checks

```
pip install numpy scipy mpmath pytest
python -m pytest -q tests
```

The tests re-derive the headline numbers and check the Lean sources and axiom reports. They cover the DQI score law, derived three ways and checked against the instance ensemble; all ten rows of Google's Table VI; the Airy law on fresh points outside its fitting range; and every trifferent code, re-checked triple by triple and rebuilt from the paper's description.

On every push, CI also:
- builds the Lean proofs and every paper from scratch;
- checks that the committed PDFs match their sources;
- builds arXiv-ready source bundles (`python tools/make_arxiv.py`), downloadable from each run as the `arxiv-bundles` artifact.

## Citing

If you use a result, please cite its paper. [CITATION.cff](CITATION.cff) has the details, and GitHub's "Cite this repository" button reads it.

## Contact

Corrections and pointers to prior work are welcome. Please open an issue.

Author: Tyler Duic, ORCID [0009-0005-4675-3045](https://orcid.org/0009-0005-4675-3045).

## License

Code, data, papers and Lean proofs are released under the [Apache License 2.0](LICENSE).
