# Unbounded coalesced-mass certificates for resolution trees

I prove a self-contained theorem about finite ordinary resolution trees. For each clause label, I first add the dyadic weights of every leaf with that label. I then form the functional displayed in the paper from the square roots of these coalesced clause masses and the corresponding variable-incidence masses.

For the formula of all full signed clauses on `n` variables, the exact supremum over finite unrestricted resolution refutations is `n+1`, for every `n ≥ 3`. The construction uses nonregular trees. The functional is unbounded. The formulas are minimally unsatisfiable. An exact three-variable witness exceeds `61/25 > 1+sqrt(2)`.

I retain credit to Kunisky for the attributed source context, arXiv:2111.02974. The primary definitions, quantifiers, effective-depth convention, proof restrictions, and journal/current-version correspondence remain unverified. Any external-conjecture comparison is conditional on literal agreement with the displayed model. I make no first-priority claim. This theorem does not determine the optimal Komlós constant or exclude a suitable choice of one proof per formula.

## Contents and build

- [paper.pdf](paper.pdf) and [paper.tex](paper.tex): full conventional proof and exact functional.
- [formalization/](formalization/): sixteen Lean modules, pins, fail-closed audit wrapper and tests.
- [FORMALIZATION.md](FORMALIZATION.md): endpoints and precise limits.
- [checks/](checks/): exact finite witness and standard-library rational checker.
- [AUTHORSHIP.md](AUTHORSHIP.md), [CITATION.cff](CITATION.cff), [CITATION.bib](CITATION.bib), and [LICENSE](LICENSE).

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build paper.tex
cp .build/paper.pdf paper.pdf
python3 checks/verify_exact.py
cd formalization
lake exe cache get
bash build.sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests -v
```

The Lean project pins Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Dependency setup requires network access. A fresh build and trust-zero audit of twelve required reports succeeded on 28 October 2026 before the source-context comment repair. Only `propext`, `Classical.choice`, and `Quot.sound` occurred. All non-comment code and pins are byte-identical to that checked source; no new Lean run is claimed for the comment-only repair. Existing intermediate linter warnings are not proof holes. The Python checker checks only the fixed finite witness.

## Disclosure

This work is fully autonomous agentic research. Automated systems produced the research, proofs, formalization, and manuscript preparation. Dev D. Goyal is responsible for publication. No expert validation or peer review is claimed.
