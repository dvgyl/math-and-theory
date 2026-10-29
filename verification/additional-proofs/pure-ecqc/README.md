# A pure-state matched-basis information inequality violation in dimension five

**Autonomous AI research disclosure.** This work is fully autonomous agentic research. Automated systems produced the research, proofs, formalization, and manuscript preparation. I, Dev D. Goyal, am responsible for publication. No expert validation or peer review is claimed.

I give an exact normalized pure state in dimension five and six explicit mutually unbiased bases. Both parties use identical basis vectors at each setting. Every five-setting selection has classical information sum `5 log 5`, while quantum mutual information is `2 log 5`. The exact excess is `3 log 5` and the ratio is `5/2`.

The result tests the displayed fixed-family information inequality. The definition does not optimize over other basis collections or local basis changes. I credit Iqbal for the motivating ECQC proposal and pure-state question, and Wang, Wang, and Chen for the attributed earlier mixed-state counterexamples. Exact source definitions, bibliographic metadata, later-work comparisons, and historical priority remain unverified. I make no first or minimal-dimension claim.

- [Manuscript PDF](manuscript/manuscript.pdf), [LaTeX source](manuscript/manuscript.tex), and [references](manuscript/references.bib).
- [Formalization map](manuscript/FORMALIZATION.md) and [Lean proof package](formalization/).
- [Citation metadata](manuscript/CITATION.cff), [disclosure](manuscript/AUTHORSHIP.md), and [Apache-2.0 license](LICENSE).

The Lean package checks the five-dimensional state, six bases, actual Born tables, purity, reduced states, entropy, and every allowed five-setting selection: five scientific modules and eight audited endpoints. The [all-prime companion](prime-family-proof.md) proves an unbounded-ratio extension conventionally. It is not a general Lean theorem.

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
