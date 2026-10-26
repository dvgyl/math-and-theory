# Math and Theory

I am Dev D. Goyal. I direct an AI research effort in mathematics, theoretical computer science, and mathematical physics. I choose problems and request proofs, formal verification, and revisions. I do not supply the proof ideas or intermediate arguments. The AI systems construct the proofs from my instructions.

This collection contains seven preprints. Six have complete Lean proofs of their principal claims. The Gyires preprint proves inequalities for several structured matrix classes and develops related polynomial bounds. Its principal order-five claims have Lean proofs. Lean formalization of its other results is incomplete. The collection does not claim a general solution when a proof covers only a special case.

Start with the [manuscript catalogue](CONTENTS.md) or the [overview](overview.pdf). The [Lean guide](lean/README.md) explains the formal statements. The [verification guide](verification/README.md) gives the commands and recorded results. [AUTHORSHIP.md](AUTHORSHIP.md) identifies the human and AI contributions.

## Results

The catalogue groups papers into stable result families. Mathematics contains matrix inequalities, concavity, and integer sequences. Theoretical computer science contains a sampling-policy inequality. No mathematical-physics result has been admitted in this edition. The same structure supports later additions in all three disciplines.

| Result family | Established result |
|---|---|
| [q-permanent](preprints/q-permanent/README.md) | Counterexamples at every real parameter greater than one. |
| [Gyires](preprints/gyires-circulant-five/README.md) | Circulants of orders five through seven, all-order structured matrix results, rank two through order fifteen, and supporting polynomial results. Broader Lean verification remains incomplete. |
| [DomiRank entropy](preprints/domirank-entropy/README.md) | A 14-vertex counterexample with positive scores on the whole comparison interval. |
| [Diagonal concavity](preprints/diagonal-concavity/README.md) | A counterexample and complete classification of a positive one-parameter family. |
| [Alternating Motzkin sums](preprints/alternating-motzkin/README.md) | Strict root log-concavity with the optimal tail start. |
| [Hofstadter iteration](preprints/hofstadter-iteration/README.md) | Late-iterate ordering fails for every parameter at least four. |
| [Best-of-n sampling](preprints/best-of-n/README.md) | The proposed bound fails at every budget at least two, with arbitrarily small atom caps. |

## The continuous Gyires preprint

The [Gyires preprint](preprints/gyires-circulant-five/paper.pdf) proves the order-five circulant inequality and extends the analysis to other structured matrix classes. It includes circulants of orders six and seven, all-order permutation polynomials, all-order four-block matrices, one exceptional column or row, and rank-two matrices through order fifteen. It also proves structural, scalar, deletion, balancing, local polynomial, and counting results. Exact counterexamples identify the limits of proposed extensions. The [complete supporting record](research-notes/gyires-complete-support/README.md) gives the source map, certificate files, and reproduction commands. The broader arguments have incomplete Lean verification. The manuscript does not establish the unrestricted conjecture.

## Verification and review

The project pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The proof audit permits only `propext`, `Classical.choice`, and `Quot.sound`. Separate Challenge and Solution modules make each submitted statement auditable. The Challenge proof holes are specifications. They are excluded from the proved library and its axiom audit.

[Verification records](verification/README.md) distinguish compilation, statement comparison, independent proof checking, exact computation, and finite numerical checks. A successful computation over finitely many inputs does not prove a universal theorem.

GPT-6.1 Sol completed two independent AI review passes and approved the seven formally verified families. The later Gyires notes have a [separate correction review](research-notes/gyires-extensions/review.md). The continuous preprint has its own [review record](preprints/gyires-circulant-five/review.md). The [review record](verification/review.md) gives the findings and limits. This is not human expert validation or peer review. These papers have NOT been peer reviewed. No claim of first priority is made. The prior-work records describe the sources inspected and the limits of the search.

My earlier personal review applies only to the proofs in the [original order-five Gyires repository](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448). It does not cover the new proofs, changed formal statements, or revised manuscripts in this collection. For that earlier work, the following statement applies:

> I have personally reviewed the AI-generated proofs to the best of my mathematical ability. The accompanying Lean formalizations have been machine-checked, but my review should not be considered independent expert validation. I make no claims regarding the novelty of these results and welcome further scrutiny, corrections, and feedback from the mathematical community. They have NOT been peer reviewed.

## Authorship and use

The original research agent was ChatGPT (OpenAI), using the GPT-6 model with Pro reasoning. The Gyires development also records work by Claude Opus 5.5, used with Claude Code. Codex, using GPT-6, conducted this audit, completed proofs, ran computations, and revised the collection. The final review record identifies the separate reviewer and the checks actually completed.

Cite an individual paper with its `citation.bib` file. Each paper directory contains its source, bibliography, PDF, and links to its formal proof. The root [Apache-2.0 license](LICENSE) applies except where [NOTICE](NOTICE) identifies third-party material.

For a later result family, follow [the contribution procedure](lean/docs/adding-a-family.md). Each addition must satisfy the same mathematical, source-fidelity, prior-work, formalization, and reproducibility requirements.
