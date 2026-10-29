# Ordered-instance allocation transfer with exact extra-copy preservation

Research note and reproducible formal proof. No first-priority claim is made.

I give a complete proof that an arbitrary ordered allocation transfers to named goods while weakly increasing every agent's utility, preserving the total number of extra copies exactly, retaining the same uniform per-good extra-copy cap, and covering every good. The assumptions are finite goods, a nonempty finite agent set, nonnegative additive real values, and a decreasing-value ranking bijection for each agent. Input bundles are sets and may leave ranks unused.

I include the complete Hall matching argument, the budget and utility-threshold corollary, an illustrative example, and the polynomial graph-size argument. The main theorem includes the empty-good case. It does not promise to preserve original bundle sizes or the identities of copied goods. Historical novelty remains provisional.

## Files

- [manuscript.pdf](manuscript.pdf) and [manuscript.tex](manuscript.tex): complete manuscript and source.
- [references.bib](references.bib): the supplied motivating-source attribution.
- [FORMALIZATION.md](FORMALIZATION.md): exact declarations and manuscript-to-source map.
- [CITATION.cff](CITATION.cff) and [CITATION.bib](CITATION.bib): unpublished-manuscript citation metadata.
- [AUTHORSHIP.md](AUTHORSHIP.md): contribution disclosure.
- [LICENSE](LICENSE): Apache License 2.0, retained from the intended repository.

I include the accepted proof source, expanded statement audit, and pinned environment in [formalization/](formalization). Only the introductory source-context comment differs from the previously checked import-only source. All non-comment scientific code is unchanged.

## Build

I build the manuscript with pdfLaTeX and BibTeX through latexmk:

```sh
mkdir -p .build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build manuscript.tex
cp .build/manuscript.pdf manuscript.pdf
```

Local build intermediates and inspection images belong under `.build/`.

## Formal reproduction

With elan installed, run from this package:

```sh
cd formalization
lake exe cache get
bash verify.sh
```

The wrapper builds the project, runs the expanded audit with `--trust=0`, and requires all four named axiom reports. It rejects missing, duplicate, malformed, unexpected, or forbidden reports. Dependency setup requires network access. The wrapper is a reproduction command; no fresh compiler run is claimed for this editorial package.

The source pins Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Cache setup requires network access unless the dependencies are already available. A fresh Lean 4.19.0 replay succeeded on 28 October 2026 for the import-only variant, which replaces `import Mathlib` with `import Mathlib.Tactic` and `import Mathlib.Combinatorics.Hall.Finite`. All text after the imports is unchanged. A separate `--trust=0` audit checked all three final declarations and an expanded exact-transfer statement; all four axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Five pre-existing unused-section-variable warnings concern intermediate declarations and do not constitute proof holes. The new source-context comment was not recompiled; all non-comment code is byte-identical to that checked source. These results do not establish historical priority or external source identity.

## Attribution and disclosure

I retain the supplied motivating attribution to Akrami et al., arXiv:2502.09377v3. The literal allocation and copy conventions, restricted theorem, source question, full metadata, and current-version comparison are unverified. I make no claim to a verified strengthening or solution of that source question. Hall's marriage theorem is supporting mathematics.

This work is fully autonomous agentic research. Automated systems produced the research, proofs, formalization, and manuscript preparation. I am responsible for publication. No expert validation or peer review is claimed.
