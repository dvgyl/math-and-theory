# A polygon enclosure fails for sums of normal matrices

**Autonomous AI research disclosure.** This work is fully autonomous agentic research. Automated systems produced the research, proofs, formalization, and manuscript preparation. I, Dev D. Goyal, am responsible for publication. No expert validation or peer review is claimed.

I give two exact normal 3 by 3 matrices with determinant `2/3 + 2i/9`. It lies outside every bounded component closure of the displayed Jordan polygon. The polygon is the boundary of the exterior defined by arbitrarily long straight segments avoiding the full transposition graph. The determinant remains an explicit convex combination of permutation values.

I credit Alexander Kovačec for the motivating enclosure proposal. Literal source definitions, current hypotheses, and bibliographic metadata remain unverified. Comparison with an external Conjecture 7 is conditional on agreement with the definitions in the paper. This example satisfies the ordinary Marcus–de Oliveira convex-hull inclusion. I make no priority claim.

- [Manuscript PDF](manuscript/manuscript.pdf), [LaTeX source](manuscript/manuscript.tex), and [references](manuscript/references.bib).
- [Formalization map](manuscript/FORMALIZATION.md) and [Lean proof package](formalization).
- [Citation metadata](manuscript/CITATION.cff), [disclosure](manuscript/AUTHORSHIP.md), and [Apache-2.0 license](LICENSE).

## Priority and subsequent correspondence

On 29 October 2026, following my correspondence with Professor Alexander Kovačec, he informed me that he had independently discovered a counterexample to his own conjecture in June 2026, documented in an unpublished preprint. He also mentioned that Wenlin Zhang had independently contacted him with another counterexample, apparently involving Lean. These developments were previously unknown to me, and my agents' original novelty searches had not found them.

I acknowledge both earlier discoveries. I have not seen either counterexample, and it has not been established whether either is equivalent to my construction. The matrices, determinant, proof and Lean formalization here are unchanged. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#kovačec-polygon-enclosure) gives the details.

## Formal proof and reproduction

Nine scientific source files check the actual matrices, six permutations, nine transposition edges, straight-segment exterior, full Jordan boundary, a nonempty bounded component, exclusion from every bounded component closure, and the convex identity. Six audited endpoints cover the integrated scope. The names `Conjecture7`, `sourceGraph`, and `sourceBoundary` refer to definitions in the package; they do not authenticate an external source.

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
