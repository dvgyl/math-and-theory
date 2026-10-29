# Leaf deletion can move the unique mode of a tree domination polynomial by two

**Autonomous AI research disclosure.** This work is fully autonomous agentic research. Automated systems produced the research, proofs, formalization, and manuscript preparation. I, Dev D. Goyal, am responsible for publication. No expert validation or peer review is claimed.

I give a tree on 7284 vertices with a unimodal domination polynomial and unique mode 3978. Deleting one specified leaf gives a tree on 7283 vertices whose domination polynomial is unimodal with unique mode 3976. Exact integer comparisons cover every coefficient of this fixed witness.

I credit Burcroff and O’Brien for the motivating leaf-deletion question and Zhang for the attributed proximity conjecture. Exact question numbers, current-version correspondence, and bibliographic metadata remain unverified. An external resolution is conditional on agreement with the displayed definitions and quantifiers. I make no priority or smallest-witness claim. Both witness polynomials are unimodal; no all-tree unimodality result or unbounded mode jump is proved.

- [Manuscript PDF](manuscript/manuscript.pdf), [LaTeX source](manuscript/manuscript.tex), and [references](manuscript/references.bib).
- [Formalization map](manuscript/FORMALIZATION.md) and [Lean proof package](formalization).
- [Citation metadata](manuscript/CITATION.cff), [disclosure](manuscript/AUTHORSHIP.md), and [Apache-2.0 license](LICENSE).

Eighteen scientific proof/data modules and ten audited endpoints cover actual dominating subsets, tree semantics, induced leaf deletion, polynomial identities, complete coefficient comparisons, unimodality, and unique modes. The `question_8_1` identifier names the package-defined existential statement. It does not authenticate an external question number.

The proof package pins Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The checked build and trust-zero audit succeeded on 28 October 2026. Formal checking establishes the displayed mathematical statements. It does not establish external source identity or novelty.

To reproduce the complete formal build, install the pinned Lean toolchain and obtain the pinned dependencies and compatible mathlib cache. Then run:

```sh
cd formalization
bash build.sh
```

The wrapper builds the local modules in order, runs a separate `--trust=0` audit, and validates every required axiom report. It permits only `propext`, `Classical.choice`, and `Quot.sound`. Build, audit, missing-report, and disallowed-axiom failures return a nonzero status. Dependency setup can require network access; dependencies and compiled caches are not bundled.

To build the manuscript, install pdfLaTeX, BibTeX, latexmk, and the packages declared in the source. Then run:

```sh
cd manuscript
bash build.sh
```

To check package integrity from this directory, run `sha256sum -c SHA256SUMS`.

The independent integer reproducer is `python3 -B manuscript/check_coefficients.py`. It derives the coefficients without importing the Lean data and prints `PASS` with modes 3978 and 3976. Optimization mode is rejected because assertions must remain enabled.
