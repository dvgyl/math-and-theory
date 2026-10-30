# Math and Theory: mathematical research and Lean 4 proofs

[**Browse the searchable research catalogue**](https://dvgyl.github.io/math-and-theory/) — individual paper pages, abstracts, and proof limits.

I am Dev D. Goyal. I publish mathematical research papers, proofs, counterexamples, and Lean 4 formalizations from fully autonomous agentic research in mathematics, theoretical computer science, and mathematical physics. AI agents generated the research, proofs, computations and manuscripts. I am responsible for publication.

The collection contains results with different formal verification scopes. Each paper states its checked claims, conventional proofs and remaining limits. The papers have not been externally peer reviewed. I make no claim of first priority.

[Browse papers and abstracts](CONTENTS.md) · [Standout results](#standout-results) · [Find a result](#find-a-result) · [Check the proofs](verification/README.md) · [Cite the collection](CITATION.cff)

## Navigating the collection

The current catalogue contains 38 manuscripts and research notes across 37 result families. A result family groups related work, including principal theorems, companion arguments and supporting results. I organize the collection by discipline and subject.

- Start with the [overview](overview.pdf) for descriptions of the result families.
- Use the [manuscript map](CONTENTS.md) to find individual papers, abstracts and supporting materials.
- The [papers directory](papers/) groups every manuscript and its supporting material by subject and result family.
- The [Lean library](lean/README.md), [formalization catalogue](lean/formalization.yaml) and [verification guide](verification/README.md) identify formal proofs, associated papers and checking commands.
- [Unfinished formal proofs](UNFINISHED.md) lists the remaining Lean gaps and conventional-proof boundaries.
- [Adding a result](docs/ADDING_RESULTS.md) explains the family layout, metadata template and required checks.

## Standout results

The results I consider the strongest, in order of significance.

### Mathematics

**[A narrow interval for the universal multiplier step of two-block ADMM](papers/mathematics/admm-multiplier-step/manuscript.pdf).** Two-block ADMM with relaxation only in the multiplier update converges for every constant step 0 < τ ≤ 1.886 on finite-dimensional convex problems with attained proximal steps and a saddle point. Fixed compact polytopes in R¹²⁸ have a nonconstant periodic orbit for every τ ≥ 1.8868954…, so the universal threshold lies in an interval of width below 0.0009. The convergence theorem, its certificates and the periodic orbit are formalized in Lean.

**[The small-coefficient upper half of the Keller–Klein conjecture](papers/mathematics/keller-klein/manuscript.pdf).** For a Rademacher sum with unit variance and every coefficient at most 7/100 in absolute value, P(|X| ≤ x) ≤ 2Φ(x) + 2Φ(a) − 2 for every x ≥ 0. This closes the range of the Keller–Klein conjecture left open by Ivanisvili's computer-assisted results; with them it implies the full conjecture, conditionally on those unrefereed results. The theorem, including Prawitz smoothing and both analytic zones, is formalized in Lean.

**[The exact last-gradient bound for constant-step gradient descent in the strongly convex case](papers/mathematics/strong-gradient/manuscript.pdf).** The exact final-gradient guarantee for constant-step gradient descent holds on every real Hilbert space, for every natural horizon and all normalized steps in [0,2], including positive strong convexity. The actual-function bound and normalized attaining functions are formalized; sharpness at arbitrary scale follows by conventional rescaling.

**[Escaping Nesterov flows and iterates below critical damping](papers/mathematics/nesterov-subcritical/manuscript.pdf).** For X″ + (r/t)X′ + ∇F(X) = 0 from rest and for the Nesterov iteration with momentum k/(k+r), universal boundedness over convex objectives with 1-Lipschitz gradient and attained minimum holds on the Hilbert space ℓ² exactly when r ≥ 3. An explicit convex planar potential has an escaping trajectory for every 0 < r ≤ 2. The Hilbert-space and discrete thresholds and the planar escape for 1 < r ≤ 2 are formalized; the finite-dimensional range 2 < r < 3 remains open.

**[The exact asymmetric Merino–Welsh region for finite matroids](papers/mathematics/asymmetric-tutte/manuscript.pdf).** The exact nonnegative parameter region for T_M(x,0) T_M(0,y) ≥ T_M(1,1)² is characterized uniformly over all finite matroids without loops or coloops. The formal statement uses actual matroids and their subset-rank Tutte sum, including the empty ground set.

**[A positive constant-recursive sequence with nonquasipolynomial power ranks](papers/mathematics/power-rank/manuscript.pdf).** A positive constant-recursive sequence of rank thirteen has explicit minimal recurrences for all its powers and nonquasipolynomial power ranks. The main theorem and arbitrary-rank companions are formalized; generating-function and polynomial corollaries have conventional proofs. Eric Rowland has independently obtained an infinite family of rank sequences at rank three ([priority note](PRIORITY_AND_NOVELTY.md#power-ranks-of-a-constant-recursive-sequence)).

### Mathematical physics

**[A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](papers/physics/higuchi-sudbery/manuscript.pdf).** Every pure four-qubit state has average two-qubit marginal entropy at most log(2) + log(3)/2. The Higuchi–Sudbery state attains the bound, and the actual-state inequality and attainment are formalized. The Omega Institute published an algebraically equivalent certificate earlier, and I make no originality or priority claim ([priority note](PRIORITY_AND_NOVELTY.md#higuchisudbery-four-qubit-entropy-bound)).

**[Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](papers/physics/universal-embezzlement/manuscript.pdf).** A target-independent catalyst of local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector with m entries. The formal proof constructs local basis permutations and their finite complex Hilbert-space interpretation.

**[Exact conditional contraction for Pauli channels and depolarization in every dimension](papers/physics/quantum-exact-contraction/quantum_exact_contraction.pdf).** The conditional hockey-stick contraction coefficient is exact for every stochastic Pauli qubit channel and the full physical depolarizing family in every dimension d ≥ 2. The formal proof covers every γ ≥ 1, arbitrary finite quantum references, all boundary cases, and matching density-state witnesses.

**[The three-state root-fidelity entropy bound](papers/physics/fidelity-three-state/manuscript.pdf).** The weighted three-by-three root-fidelity matrix has entropy at least the Holevo quantity of every three-state ensemble in arbitrary finite dimension. The formal theorem includes mixed and singular states and zero probabilities. Another group has claimed a solution of the same conjecture; the proofs have not been compared ([priority note](PRIORITY_AND_NOVELTY.md#three-state-root-fidelity-entropy-bound)).

**[A sharp universal skewness bound for unicyclic currents](papers/physics/unicyclic-skewness/manuscript.pdf).** The net marked-edge current on every finite bidirectional Markov ring with at least three states, positive rates and unequal forward and reverse rate products satisfies −1/16 ≤ C₃/C₁ ≤ 1. The matrix-derivative bound is formalized; stochastic identification and sharpness have conventional proofs.

**[Exact three-setting correlation bounds at fixed steering centre](papers/physics/steering-bounds/paper/steering_bounds.pdf).** The exact upper envelope of the three-setting squared correlation value is determined at every two-qubit steering-centre length, including attainment and nonattainment. A value greater than one is possible exactly when c < 2/3; the formal proof uses actual density matrices and the stated canonical centre.

## Result families

### Mathematics

- [Matrix theory](CONTENTS.md#matrix-theory): q-permanent counterexamples, Gyires structured permanent inequalities, a normal-matrix polygon counterexample, projection AM–GM obstruction.
- [Graph theory and graph polynomials](CONTENTS.md#graph-theory-and-graph-polynomials): DomiRank entropy, domination-sequence ultra-log-concavity, domination-root escape, leaf-deletion mode movement.
- [Inequalities and real analysis](CONTENTS.md#inequalities-and-real-analysis): diagonal concavity.
- [Integer sequences and combinatorics](CONTENTS.md#integer-sequences-and-combinatorics): Motzkin root log-concavity, bounded-forcing Motzkin bounds, Hofstadter iteration, nonquasipolynomial power ranks.
- [Discrete analysis, tilings, probability and entropy](CONTENTS.md#discrete-analysis-tilings-probability-and-entropy): the sharp one-eighth Fourier bound, a spectral tile in F₂⁹ with no periodic complement, the small-coefficient Keller–Klein bound, ranking entropy, Sidon-set Rényi thresholds.
- [Matroid theory](CONTENTS.md#matroid-theory): the asymmetric Merino–Welsh region.
- [Optimization](CONTENTS.md#optimization): the ADMM multiplier-step interval, an ADMM five-cycle, escaping subcritical Nesterov flows, Chambolle–Pock cycles, the exact strong-convexity gradient bound.

### Theoretical computer science

- [Sampling algorithms and information theory](CONTENTS.md#sampling-algorithms-and-information-theory): critical hard-core influence bounds, best-of-n counterexamples.
- [Boolean functions and decision trees](CONTENTS.md#boolean-functions-and-decision-trees): decision-tree covariance.
- [Fair division](CONTENTS.md#fair-division): ordered-allocation transfer.
- [Proof complexity](CONTENTS.md#proof-complexity): resolution-tree mass certificates.

### Mathematical physics

- [Stochastic thermodynamics](CONTENTS.md#stochastic-thermodynamics): thermal current kurtosis, unicyclic current skewness.
- [Quantum information](CONTENTS.md#quantum-information): universal entanglement embezzlement, the Higuchi–Sudbery entropy bound, a matched-basis information counterexample, exact steering correlation bounds, three-state root fidelity, exact conditional quantum contraction, Schmidt numbers of tensor powers of the Tiles state.

## Find a result

I use the names below to connect common search terms to each result and its files. Each result directory contains its manuscript and supporting material. The [full manuscript map](CONTENTS.md) includes the other families and their abstracts.

| Search terms | Result and files |
|---|---|
| Higuchi–Sudbery, Higuchi-Sudbery, four-qubit entanglement, marginal entropy | [Four-qubit entropy bound](papers/physics/higuchi-sudbery/) |
| Strong convexity, gradient descent, Taylor–Hendrickx–Glineur, last-gradient bound | [Exact gradient bound](papers/mathematics/strong-gradient/) |
| Entanglement embezzlement, quantum catalysts, logarithmic infidelity | [Universal entanglement embezzlement](papers/physics/universal-embezzlement/) |
| Root fidelity, three-state ensemble, Holevo quantity, quantum entropy | [Three-state root-fidelity bound](papers/physics/fidelity-three-state/) |
| Merino–Welsh, Merino-Welsh, Tutte polynomial, finite matroids | [Asymmetric Merino–Welsh region](papers/mathematics/asymmetric-tutte/) |
| Pauli channels, depolarizing channels, hockey-stick divergence, quantum contraction | [Exact conditional contraction](papers/physics/quantum-exact-contraction/) |
| Alternating direction method of multipliers, ADMM dual step size, Glowinski golden ratio, multiplier relaxation | [ADMM multiplier-step interval](papers/mathematics/admm-multiplier-step/) |
| ADMM convergence counterexample, period-five orbit | [Rational period-five ADMM orbit](papers/mathematics/admm-counterexample/) |
| Keller–Klein conjecture, Rademacher sums, Berry–Esseen bound, normal approximation | [Keller–Klein small-coefficient bound](papers/mathematics/keller-klein/) |
| Nesterov accelerated gradient flow and iteration, vanishing damping, subcritical damping, unbounded trajectories | [Escaping subcritical Nesterov flows](papers/mathematics/nesterov-subcritical/) |
| Hard-core model, spectral independence, uniqueness threshold, Glauber dynamics | [Critical hard-core influence bounds](papers/theoretical-computer-science/critical-hardcore/) |
| Unextendible product bases, UPB, Schmidt number, bound entanglement, Tiles state | [Minimum-rank multiplicativity and the Tiles state](papers/physics/upb-tensor-rank/) |
| Chambolle–Pock, Chambolle-Pock, PDHG, primal-dual hybrid gradient, extrapolation, periodic orbits | [Chambolle–Pock periodic obstructions](papers/mathematics/chambolle-pock-cycles/) |
| C-finite sequences, constant-recursive sequences, power ranks, nonquasipolynomial | [Power-rank sequence and companion results](papers/mathematics/power-rank/) |
| Markov rings, stochastic currents, unicyclic networks, skewness | [Unicyclic current bound](papers/physics/unicyclic-skewness/) |
| Quantum steering, steering ellipsoids, two-qubit correlations, three-setting bounds | [Fixed-centre steering bounds](papers/physics/steering-bounds/) |

To search the source on GitHub, use `repo:dvgyl/math-and-theory` followed by a name or term. For example, use `repo:dvgyl/math-and-theory Higuchi`. To find a file by name, open the repository and press **t**. For proof scope and known gaps, read [UNFINISHED.md](UNFINISHED.md).

## Proof coverage

The shared Lean library covers seven families and 29 selected Comparator statements. Standalone packages have separate pinned environments and audits. The permitted proof axioms are `propext`, `Classical.choice` and `Quot.sound`. Exact finite computations do not replace universal proofs.

The Gyires family has complete Lean proofs for order-five and order-six circulants, all-order permutation-polynomial and four-block matrices, exceptional vectors, and rank-two matrices of orders 2 through 8. General order-seven circulants and rank-two orders 9 through 15 remain incomplete in Lean. The unrestricted conjecture remains outside these results. Each other paper states its own formal and conventional proof boundaries in the manuscript map.

## Priority and novelty disclosures

After publication, correspondence with researchers in the field brought earlier or overlapping work on five results to my attention: the Higuchi–Sudbery entropy bound, the Kovačec polygon enclosure, the root-fidelity entropy bound, the power-rank sequences and the binary spectral tile. My agents' original novelty searches had not found this work. [PRIORITY_AND_NOVELTY.md](PRIORITY_AND_NOVELTY.md) records when and how I learned of it, the public sources, and what remains uncertain. Each affected README and manuscript carries a dated note.

## Versions and citations

I preserve corrections and revisions in the repository history. Cite an individual manuscript with the citation file linked from its catalogue entry. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) for the collection. The [Apache-2.0 license](LICENSE) applies except where [NOTICE](NOTICE) identifies third-party material.

## How the results were produced

I publish fully autonomous agentic research and am responsible for publication. Models used: GPT 6 Astra by OpenAI in ChatGPT and Codex, GPT 6.1 Sol by OpenAI in Codex, and Opus 5.5 by Anthropic in Claude Code. Each manuscript states how they were used and its review history; the [authorship record](AUTHORSHIP.md) gives the details. These disclosures do not claim expert validation or external peer review.
