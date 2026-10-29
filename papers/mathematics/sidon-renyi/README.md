# Sharp universal Rényi threshold for iid sums on finite Sidon sets

Research note and reproducible formal proof. No first-priority claim is made.

I present a proof of the following statement. For every real order α > 1, uniform input maximizes the Rényi entropy of the sum of two independent draws from the same law on every nonempty finite strong Sidon support if and only if

    2^(α − 1) ≤ 2α − 1.

The critical order is the unique solution above one of `2^(α − 1) = 2α − 1`. It lies strictly between 3 and 4. The proof includes the critical endpoint and laws with zero probabilities. Above the threshold, a nonuniform law on `{0,1}` beats uniform input. This is a universal classification; it does not classify optimizers for each larger fixed support above the threshold.

I credit Gu and Hillion–Johnson for the attributed binary threshold, obstruction, and related method. These comparisons come from supplied source context. Primary definitions, exact propositions, and current-version correspondence remain unverified. I present the displayed strong-B2 theorem independently; I do not claim a verified published gap.

## Contents

- [manuscript.pdf](manuscript.pdf): complete human-readable proof.
- [manuscript.tex](manuscript.tex) and [references.bib](references.bib): manuscript and bibliography sources.
- [formalization/](formalization): unchanged Lean proof sources and pinned dependencies.
- [FORMALIZATION.md](FORMALIZATION.md): exact declarations and reproduction instructions.
- [CITATION.cff](CITATION.cff) and [CITATION.bib](CITATION.bib): citation metadata for this unpublished manuscript.
- [AUTHORSHIP.md](AUTHORSHIP.md): contribution disclosure.
- [LICENSE](LICENSE): Apache License 2.0, retained from the intended repository.

## Build the manuscript

I use pdfLaTeX and BibTeX through latexmk:

```sh
mkdir -p .build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build manuscript.tex
cp .build/manuscript.pdf manuscript.pdf
```

The bibliography metadata comes from the supplied source package; its primary-source verification remains incomplete.

## Reproduce the formal proof

I include the Lean sources without changing them. The pinned toolchain is Lean 4.19.0. The mathlib revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

After installing [elan](https://lean-lang.org/install/), run:

```sh
cd formalization
lake exe cache get
bash verify.sh
```

The cache command requires network access. `verify.sh` runs `lake build` and `lake env lean AxiomAudit.lean`. Lake failures retain their exit codes. The standard-library Python helper `check_axioms.py` then requires exactly one report for each of the twelve named declarations in `AxiomAudit.lean`, rejects missing, duplicate, malformed, or unexpected reports, and permits only `propext`, `Classical.choice`, and `Quot.sound`. Empty or truncated output fails the check. The pinned manifest is included; dependency resolution must preserve its revisions. A fresh run of this wrapper succeeded on 28 October 2026 with all twelve Lean source files unchanged. A separate `lake env lean --trust=0 AxiomAudit.lean` audit also succeeded and accepted all twelve required declarations with only the permitted foundational axioms. These results concern the stated proof; they do not establish historical priority or external source identity. From the package root, test the wrapper and audit parser without running Lean:

```sh
cd formalization
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests -v
```

The test fixture contains the twelve axiom-report lines from the supplied audit. Failure controls alter that text and use a fake Lake command. Their success checks the validation tooling; it does not establish a successful Lean build or final mathematical acceptance.

## Disclosure

This work is fully autonomous agentic research. Automated systems produced the research, proofs, formalization, and manuscript preparation. I am responsible for publication. No expert validation or peer review is claimed.
