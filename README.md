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

## Verifying a result

Each result is self-contained: its folder has its own dependencies (`requirements.txt`), tests, paper and a `verify.sh`, and nothing in it depends on the rest of the repository. To check one result you only need its folder:

```
git clone --filter=blob:none --sparse https://github.com/tduic/research-results
cd research-results && git sparse-checkout set <result>    # e.g. dqi-finite-size
cd <result> && python3 -m pip install -r requirements.txt
./verify.sh                                                 # quick checks, seconds
```

`./verify.sh` takes a level: the default runs the quick checks, and each result's README lists the deeper ones — rerunning every computation from scratch and comparing with the committed outputs, rebuilding the Lean proofs, rebuilding the paper — with how long each takes.

| Result | Quick | Deeper levels |
|---|---|---|
| [dqi-finite-size](dqi-finite-size/#verify-this-result) | ~10 s | `reproduce-fast` (~3 min), `reproduce` (~10 min), `paper` |
| [trifferent-codes](trifferent-codes/#verify-this-result) | ~5 s | `lean` (~5 min), `paper` |

CI does the same thing. Each result has its own workflow that checks out only that result's folder, which proves it stands alone. The workflow runs only when that folder changes, plus a weekly re-run. A small [repo-level workflow](.github/workflows/repo.yml) checks this README, the citation file and the folder structure, and [another](.github/workflows/arxiv.yml) builds arXiv-ready source bundles for every paper (`python tools/make_arxiv.py`).

## Layout

```
<result>/
  README.md        write-up: bottom line, method, results, caveats, how to verify
  verify.sh        one command per verification level
  requirements.txt pinned Python dependencies for this result only
  tests/           this result's test suite
  paper/           main.tex, references.bib, main.pdf
  experiments/, results/, codes/, data/, verification/, lean/   code, outputs and proofs behind every number
tests/             repository-level checks only
tools/make_arxiv.py   builds standalone arXiv source bundles for every paper
```

## Citing

If you use a result, please cite its paper. [CITATION.cff](CITATION.cff) has the details, and GitHub's "Cite this repository" button reads it.

## Contact

Corrections and pointers to prior work are welcome. Please open an issue.

Author: Tyler Duic, ORCID [0009-0005-4675-3045](https://orcid.org/0009-0005-4675-3045).

## License

Code, data, papers and Lean proofs are released under the [Apache License 2.0](LICENSE).
