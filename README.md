# Math and Theory

I publish mathematical manuscripts and supporting proof artifacts from fully autonomous agentic research in mathematics, theoretical computer science, and mathematical physics. AI agents generated the research, proofs, computations and manuscripts. I am responsible for publication.

The collection contains results with different formal verification scopes. Each paper states its checked claims, conventional proofs and remaining limits. The papers have not been externally peer reviewed. I make no claim of first priority.

## Navigating the collection

The current catalogue contains 30 manuscripts and research notes across 29 result families. A result family groups related work, including principal theorems, companion arguments and supporting results. I organize the collection by discipline and subject.

- Start with the [overview](overview.pdf) for descriptions of the result families.
- Use the [manuscript map](CONTENTS.md) to find individual papers, abstracts and supporting materials.
- The [preprints directory](preprints/) and [standalone study packages](verification/additional-proofs/) contain manuscripts, sources, citations and build instructions.
- The [Lean library](lean/README.md), [formalization catalogue](lean/formalization.yaml) and [verification guide](verification/README.md) identify formal proofs, associated papers and checking commands.
- [Research status](RESEARCH_STATUS.md) and [unfinished proofs](UNFINISHED.md) state the remaining limits.

## Standout results

### Mathematics

**[The exact last-gradient bound for constant-step gradient descent in the strongly convex case](verification/additional-proofs/strong-gradient/manuscript.pdf).** The exact final-gradient guarantee for constant-step gradient descent holds on every real Hilbert space, for every natural horizon and all normalized steps in [0,2], including positive strong convexity. The actual-function bound and normalized attaining functions are formalized; sharpness at arbitrary scale follows by conventional rescaling.

**[The exact asymmetric Merino–Welsh region for finite matroids](verification/additional-proofs/asymmetric-tutte/manuscript.pdf).** The exact nonnegative parameter region for T_M(x,0) T_M(0,y) ≥ T_M(1,1)² is characterized uniformly over all finite matroids without loops or coloops. The formal statement uses actual matroids and their subset-rank Tutte sum, including the empty ground set.

**[A positive constant-recursive sequence with nonquasipolynomial power ranks](verification/additional-proofs/power-rank/manuscript.pdf).** A positive constant-recursive sequence of rank thirteen has explicit minimal recurrences for all its powers and nonquasipolynomial power ranks. The main theorem and arbitrary-rank companions are formalized; generating-function and polynomial corollaries have conventional proofs.

**[A rational five-cycle for two-block ADMM with multiplier step below two](verification/additional-proofs/admm-counterexample/paper/admm_counterexample.pdf).** An exact rational period-five orbit occurs in multiplier-only two-block ADMM at multiplier step 199/100. The orbit, minimizers and optimizer are formalized; analytic regularity of the strongly convex extension has a conventional proof.

### Mathematical physics

**[A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](verification/additional-proofs/higuchi-sudbery/manuscript.pdf).** Every pure four-qubit state has average two-qubit marginal entropy at most log(2) + log(3)/2. The Higuchi–Sudbery state attains the bound, and the actual-state inequality and attainment are formalized.

**[Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](verification/additional-proofs/universal-embezzlement/manuscript.pdf).** A target-independent catalyst of local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector with m entries. The formal proof constructs local basis permutations and their finite complex Hilbert-space interpretation.

**[The three-state root-fidelity entropy bound](verification/additional-proofs/fidelity-three-state/manuscript.pdf).** The weighted three-by-three root-fidelity matrix has entropy at least the Holevo quantity of every three-state ensemble in arbitrary finite dimension. The formal theorem includes mixed and singular states and zero probabilities.

**[A sharp universal skewness bound for unicyclic currents](verification/additional-proofs/unicyclic-skewness/manuscript.pdf).** The net marked-edge current on every finite bidirectional Markov ring with at least three states, positive rates and unequal forward and reverse rate products satisfies −1/16 ≤ C₃/C₁ ≤ 1. The matrix-derivative bound is formalized; stochastic identification and sharpness have conventional proofs.

**[Exact three-setting correlation bounds at fixed steering centre](verification/additional-proofs/steering-bounds/paper/steering_bounds.pdf).** The exact upper envelope of the three-setting squared correlation value is determined at every two-qubit steering-centre length, including attainment and nonattainment. A value greater than one is possible exactly when c < 2/3; the formal proof uses actual density matrices and the stated canonical centre.

## Result families

### Mathematics

- [Matrix theory](CONTENTS.md#matrix-theory): q-permanent counterexamples, Gyires structured permanent inequalities, a normal-matrix polygon counterexample, projection AM–GM obstruction.
- [Graph theory and graph polynomials](CONTENTS.md#graph-theory-and-graph-polynomials): DomiRank entropy, domination-sequence ultra-log-concavity, domination-root escape, leaf-deletion mode movement.
- [Inequalities and real analysis](CONTENTS.md#inequalities-and-real-analysis): diagonal concavity.
- [Integer sequences and combinatorics](CONTENTS.md#integer-sequences-and-combinatorics): Motzkin root log-concavity, bounded-forcing Motzkin bounds, Hofstadter iteration, nonquasipolynomial power ranks.
- [Discrete analysis, probability and entropy](CONTENTS.md#discrete-analysis-probability-and-entropy): the sharp one-eighth Fourier bound, ranking entropy, Sidon-set Rényi thresholds.
- [Matroid theory](CONTENTS.md#matroid-theory): the asymmetric Merino–Welsh region.
- [Optimization](CONTENTS.md#optimization): an ADMM five-cycle, the exact strong-convexity gradient bound.

### Theoretical computer science

- [Sampling algorithms and information theory](CONTENTS.md#sampling-algorithms-and-information-theory): best-of-n counterexamples.
- [Boolean functions and decision trees](CONTENTS.md#boolean-functions-and-decision-trees): decision-tree covariance.
- [Fair division](CONTENTS.md#fair-division): ordered-allocation transfer.
- [Proof complexity](CONTENTS.md#proof-complexity): resolution-tree mass certificates.

### Mathematical physics

- [Stochastic thermodynamics](CONTENTS.md#stochastic-thermodynamics): thermal current kurtosis, unicyclic current skewness.
- [Quantum information](CONTENTS.md#quantum-information): universal entanglement embezzlement, the Higuchi–Sudbery entropy bound, a matched-basis information counterexample, exact steering correlation bounds, three-state root fidelity.

## Proof coverage

The shared Lean library covers seven families and 29 selected Comparator statements. Standalone packages have separate pinned environments and audits. The permitted proof axioms are `propext`, `Classical.choice` and `Quot.sound`. Exact finite computations do not replace universal proofs.

The Gyires family has complete Lean proofs for order-five and order-six circulants, all-order permutation-polynomial and four-block matrices, exceptional vectors, and rank-two matrices of orders 2 through 8. General order-seven circulants and rank-two orders 9 through 15 remain incomplete in Lean. The unrestricted conjecture remains outside these results. Each other paper states its own formal and conventional proof boundaries in the manuscript map.

## Versions and citations

I preserve corrections and revisions in the repository history. Cite an individual manuscript with the citation file linked from its catalogue entry. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) for the collection. The [Apache-2.0 license](LICENSE) applies except where [NOTICE](NOTICE) identifies third-party material.

## How the results were produced

I publish fully autonomous agentic research and am responsible for publication. The original collection records GPT 6 with Pro Reasoning in ChatGPT for initial research and GPT 6 Astra in Codex for formalizations and corrections, together with its stated author check. The later packages give their own contribution disclosures, including actual GPT 6.1 Sol formalization and verification work. Each manuscript states its own contribution and review history. These disclosures do not claim expert validation or external peer review.
