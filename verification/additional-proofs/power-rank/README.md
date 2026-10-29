# A positive constant-recursive sequence with nonquasipolynomial power ranks

The main theorem and the companion-family theorem have complete Lean formalizations. The companion generating function and its polynomial and rank-three corollaries retain their conventional proofs.

I give a complete conventional proof for an explicit positive integer-valued sequence of recurrence rank 13. The minimal characteristic polynomial of every positive termwise power is determined. Its degree is a cubic polynomial minus twice a parity-restricted square count, so the power-rank sequence is not eventually quasipolynomial.

I also give a companion family with infinitely many distinct power-rank sequences at every fixed initial rank at least three. Its principal-relation Hilbert-function mechanism is standard supporting algebra. The companion family contradicts the unnumbered fixed-rank finiteness conjecture as written on page 2 of the author-hosted Rowland–Sistos Barrón preprint. I make no claim that rank 13 is minimal or that the rank-13 example has simple characteristic roots. Its nonquasipolynomial conclusion is not identified with the source’s undefined term “pseudo-polynomial.” Historical novelty, subsequent corrections and correspondence with a specific arXiv version remain unresolved.

## Files

- [manuscript.pdf](manuscript.pdf) and [manuscript.tex](manuscript.tex): full mathematical argument.
- [references.bib](references.bib): author-hosted primary source, with the exact source distinction explained in the manuscript.
- [PROOF_MAP.md](PROOF_MAP.md): claim map, recurrence conventions, and formal-verification boundary.
- [CITATION.cff](CITATION.cff) and [citation.bib](citation.bib): unpublished-manuscript citation metadata.
- [AUTHORSHIP.md](AUTHORSHIP.md) and [LICENSE](LICENSE): truthful contribution disclosure and intended repository license.
- [formalization/](formalization/README.md): the main and companion theorem Lean package, with pinned dependencies, source hashes, and a reproducible verifier.
- `supplement/`: finite integer-arithmetic checkers with explicit rejection of optimized Python, a focused startup test, and a recorded bounded result file.

## Build and reproduce

The manuscript uses pdfLaTeX and BibTeX through latexmk:

```sh
mkdir -p .build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build manuscript.tex
cp .build/manuscript.pdf manuscript.pdf
```

With Python 3.10 or later, the finite checks can be run independently:

```sh
mkdir -p .build
python3 -B supplement/test_optimization_guard.py
python3 supplement/check_revision.py --max-power 14 --max-bm 3 --output .build/revision-checks.json
```

The safety test checks normal startup and rejection of `-O`, `-OO`, and `PYTHONOPTIMIZE`. The arithmetic command checks supports, normal forms, square counts, individual coefficient degrees, and modular recurrence polynomials. Finite ranges are recorded in the output. The infinite arguments in the paper prove both constructions. The main rank-thirteen theorem also has a complete Lean proof, including eventual complex minimality, every power's integral minimal polynomial, equal rational and real ranks, the exact square-count and floor formulas, the error bound, and nonquasipolynomiality. The formal proof also covers the literal companion family for all ranks r >= 3, all parameters d >= 2, and all powers M >= 0. It includes the full minimal polynomial, integral recurrences, equal rational/real/complex ranks, odd-prime existence, and infinitely many distinct power-rank sequences at each initial rank. The generating function, eventual polynomial degree and leading coefficient, and rank-three examples are outside the formal package.

To reproduce the formal proofs, run `python3 check_package.py`, `lake exe cache get`, and `python3 verify.py` in `formalization/`. The verifier rejects incomplete proof coverage and permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Disclosure

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex produced formal proofs and verification software for the accompanying package. I am responsible for publication.
