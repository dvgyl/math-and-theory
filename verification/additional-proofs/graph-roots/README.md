# Sharp escape of complex domination roots in square flowers

Unpublished manuscript.

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex contributed formal proofs and verification software. I am responsible for publication. No expert validation or peer review is claimed.

I prove a sharp largest-root law for the graph formed by n squares sharing one vertex. If R_n is the largest modulus of a domination root, then

`R_n < 2 + sqrt(4n/W(4n))` for every n≥1, and

`4n/R_n² = log(4n) − log log(4n) + o(1)`.

The matching lower estimate constructs actual complex roots. Complete real-root classifications for square flowers and book graphs, and the motion of the real flower roots, are companion results. Counting formulas and standard analytic tools are supporting mathematics. I make no claim of first priority or resolution of a specifically numbered source conjecture.

## Files

- [manuscript.pdf](manuscript.pdf), [manuscript.tex](manuscript.tex), and [references.bib](references.bib): complete conventional proofs and related references.
- [PROOF_MAP.md](PROOF_MAP.md): exact claim and proof coverage.
- [CITATION.cff](CITATION.cff) and [citation.bib](citation.bib): unpublished-manuscript metadata.
- [AUTHORSHIP.md](AUTHORSHIP.md) and [LICENSE](LICENSE): truthful disclosure and intended repository license.
- [formalization/README.md](formalization/README.md): the portable Lean package for all numbered theorem conclusions.
- `supplement/`: finite checker, supplied bounded records, and startup safety test.

## Build and reproduce

With pdfLaTeX and BibTeX, run from this directory:

```sh
set -e
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build manuscript.tex
bibtex build/manuscript
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build manuscript.tex
cp build/manuscript.pdf manuscript.pdf
```

With Python 3.10 or later, SymPy and mpmath:

```sh
python3 -B supplement/test_optimization_guard.py
python3 -B supplement/checks.py --max-n 20 --output build/replayed-checks.json
```

The supplied result file records graph enumeration for flowers n=1..6 and books n=1..8, exact real-root checks for both families through n=20, symbolic identities, and six high-precision root diagnostics. The arithmetic body of the candidate checker is unchanged from the supplied program. Its new startup guard rejects `-O`, `-OO`, and `PYTHONOPTIMIZE`, because the checks use assertions. Candidate preparation ran only the focused startup test, not the full enumeration again.

Finite checks do not prove the infinite claims. Numerical residuals do not certify maximum modulus. The paper gives complete conventional proofs.

The Lean development proves the main escape theorem for the actual finite graph. It includes the domination-subset counting identity, degree, origin multiplicity, the complete finite nonzero root set, and its maximum modulus. It proves the strict bound for every n≥1, the additive reciprocal-square law, and the leading equivalent. The formal transfer constructs actual roots by a contraction argument. Its final statements retain the conclusions of the paper's Rouché argument.

The Lean sources also prove the full square-flower and book real-root classifications, nonzero real-root simplicity, strict even-order flower-root motion, and the original endpoint expansions with O(n^-2) errors. The actual book graph and its counting identity are included. The conclusions of all numbered manuscript results are covered. The [formal package](formalization/README.md) provides 70 source modules, 258 explicit statement checks and transitive-axiom reports, and a bounded verifier. Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

## Disclosure

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex contributed formal proofs and verification software. I am responsible for publication. Historical novelty and precise source correspondence remain provisional.
