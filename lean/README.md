# Lean proof map

This is the entry point for **all formal proofs in the collection**. The shared library below uses Lean 4.35.0. Standalone families live with their manuscripts under `papers/` and retain their own pinned Lean and Mathlib versions. The tables identify the correct environment for every formalized family; these environments are intentionally separate because their toolchains differ.

## Shared library layout

| Directory | Contents |
|---|---|
| [MathAndTheory/Mathematics](MathAndTheory/Mathematics/) | Mathematical proof families, including one Gyires family with a `CirculantFive` development and its all-order companion results. |
| [MathAndTheory/TheoreticalCS](MathAndTheory/TheoreticalCS/) | Theoretical computer science proofs. |
| [Solutions](Solutions/) | Proved specification interfaces, grouped by discipline and family. |
| [Challenges](Challenges/) | Independent specification interfaces in the same discipline/family layout. Their deliberate proof holes are not accepted proofs. |
| [comparator](comparator/) | Exact statement-comparison configurations, grouped by discipline. |
| [docs](docs/) | Family guides and instructions for adding a family. |
| [Audit.lean](Audit.lean) | Stated-type checks and transitive axiom audit for the shared library. |
| [scripts](scripts/) | Source, metadata and independent-kernel checking tools. |

The proved library does not import `Challenges`. Mathematical declaration names remain stable across the directory organization. The [formalization catalogue](formalization.yaml) specifies the 29 selected Comparator statements and their manuscripts.

## Shared proof families

| Family | Proof source | Guide | Comparator |
|---|---|---|---|
| [Real positive-definite counterexamples to extended q-permanent monotonicity](../papers/mathematics/q-permanent/paper.pdf) | [Source](MathAndTheory/Mathematics/QPermanent/) | [Guide](docs/mathematics/q-permanent.md) | [Configuration](comparator/mathematics/q-permanent.json) |
| [Gyires's permanent inequality for structured matrices](../papers/mathematics/gyires/paper.pdf) | [Source](MathAndTheory/Mathematics/Gyires/) | [Guide](docs/mathematics/gyires.md) | [Configuration](comparator/mathematics/gyires.json) |
| [An entropy increase for a structurally disassortative DomiRank graph](../papers/mathematics/domirank-entropy/paper.pdf) | [Source](MathAndTheory/Mathematics/DomiRank/) | [Guide](docs/mathematics/domirank-entropy.md) | [Configuration](comparator/mathematics/domirank-entropy.json) |
| [Diagonal concavity does not imply concavity for sums of elementary symmetric polynomials](../papers/mathematics/diagonal-concavity/paper.pdf) | [Source](MathAndTheory/Mathematics/DiagonalConcavity/) | [Guide](docs/mathematics/diagonal-concavity.md) | [Configuration](comparator/mathematics/diagonal-concavity.json) |
| [Sharp root log-concavity of alternating Motzkin sums](../papers/mathematics/motzkin/paper.pdf) | [Source](MathAndTheory/Mathematics/Motzkin/) | [Guide](docs/mathematics/motzkin.md) | [Configuration](comparator/mathematics/motzkin.json) |
| [Counterexamples to a late-iterate ordering conjecture for generalized Hofstadter functions](../papers/mathematics/hofstadter-iteration/paper.pdf) | [Source](MathAndTheory/Mathematics/Hofstadter/) | [Guide](docs/mathematics/hofstadter-iteration.md) | [Configuration](comparator/mathematics/hofstadter-iteration.json) |
| [Counterexamples to a best-of-n win-rate bound at every budget](../papers/theoretical-computer-science/best-of-n/paper.pdf) | [Source](MathAndTheory/TheoreticalCS/BestOfN/) | [Guide](docs/theoretical-computer-science/best-of-n.md) | [Configuration](comparator/theoretical-computer-science/best-of-n.json) |

## Standalone proof families

Each linked package contains its own toolchain pin, manuscript, proof sources and reproduction instructions. Follow that package's guide rather than building it with the shared toolchain above.

| Discipline | Family and proof package | Manuscript |
|---|---|---|
| Mathematics | [A polygon enclosure fails for sums of normal matrices](../papers/mathematics/kovacec/) | [PDF](../papers/mathematics/kovacec/manuscript/manuscript.pdf) |
| Mathematics | [An unbounded obstruction to projection AM–GM in Loewner order](../papers/mathematics/projection-amgm/) | [PDF](../papers/mathematics/projection-amgm/paper.pdf) |
| Mathematics | [Ultra-log-concavity of domination sequences of powers of paths and cycles](../papers/mathematics/galvin-zhang/) | [PDF](../papers/mathematics/galvin-zhang/manuscript.pdf) |
| Mathematics | [Sharp escape of complex domination roots in square flowers](../papers/mathematics/graph-roots/) | [PDF](../papers/mathematics/graph-roots/manuscript.pdf) |
| Mathematics | [Leaf deletion can move the unique mode of a tree domination polynomial by two](../papers/mathematics/leaf-deletion/) | [PDF](../papers/mathematics/leaf-deletion/manuscript/manuscript.pdf) |
| Mathematics | [Sharp log-concavity for alternating Motzkin sums](../papers/mathematics/motzkin/bounded-forcing/) | [PDF](../papers/mathematics/motzkin/bounded-forcing/manuscript.pdf) |
| Mathematics | [A positive constant-recursive sequence with nonquasipolynomial power ranks](../papers/mathematics/power-rank/) | [PDF](../papers/mathematics/power-rank/manuscript.pdf) |
| Mathematics | [The sharp level-one Fourier weight at density one eighth](../papers/mathematics/sharp-eighth/) | [PDF](../papers/mathematics/sharp-eighth/manuscript.pdf) |
| Mathematics | [A quartic entropy deficit for random rankings](../papers/mathematics/quartic-rankings/) | [PDF](../papers/mathematics/quartic-rankings/manuscript.pdf) |
| Mathematics | [Sharp universal Rényi threshold for iid sums on finite Sidon sets](../papers/mathematics/sidon-renyi/) | [PDF](../papers/mathematics/sidon-renyi/manuscript.pdf) |
| Mathematics | [The exact asymmetric Merino–Welsh region for finite matroids](../papers/mathematics/asymmetric-tutte/) | [PDF](../papers/mathematics/asymmetric-tutte/manuscript.pdf) |
| Mathematics | [A rational five-cycle for two-block ADMM with multiplier step below two](../papers/mathematics/admm-counterexample/) | [PDF](../papers/mathematics/admm-counterexample/paper/admm_counterexample.pdf) |
| Mathematics | [The exact last-gradient bound for constant-step gradient descent in the strongly convex case](../papers/mathematics/strong-gradient/) | [PDF](../papers/mathematics/strong-gradient/manuscript.pdf) |
| Theoretical computer science | [Logarithmic influence bounds and variance counterexamples for Boolean decision-tree covariance](../papers/theoretical-computer-science/readk-covariance/) | [PDF](../papers/theoretical-computer-science/readk-covariance/docs/manuscript.pdf) |
| Theoretical computer science | [Ordered-instance allocation transfer with exact extra-copy preservation](../papers/theoretical-computer-science/ordered-allocation/) | [PDF](../papers/theoretical-computer-science/ordered-allocation/manuscript.pdf) |
| Theoretical computer science | [Unbounded coalesced-mass certificates for resolution trees](../papers/theoretical-computer-science/kunisky/) | [PDF](../papers/theoretical-computer-science/kunisky/paper.pdf) |
| Mathematical physics | [A three-state thermal counterexample to a heat-current kurtosis conjecture](../papers/physics/thermal-kurtosis-counterexample/) | [PDF](../papers/physics/thermal-kurtosis-counterexample/report.pdf) |
| Mathematical physics | [A sharp universal skewness bound for unicyclic currents](../papers/physics/unicyclic-skewness/) | [PDF](../papers/physics/unicyclic-skewness/manuscript.pdf) |
| Mathematical physics | [Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](../papers/physics/universal-embezzlement/) | [PDF](../papers/physics/universal-embezzlement/manuscript.pdf) |
| Mathematical physics | [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](../papers/physics/higuchi-sudbery/) | [PDF](../papers/physics/higuchi-sudbery/manuscript.pdf) |
| Mathematical physics | [A pure-state matched-basis information inequality violation in dimension five](../papers/physics/pure-ecqc/) | [PDF](../papers/physics/pure-ecqc/manuscript/manuscript.pdf) |
| Mathematical physics | [Exact three-setting correlation bounds at fixed steering centre](../papers/physics/steering-bounds/) | [PDF](../papers/physics/steering-bounds/paper/steering_bounds.pdf) |
| Mathematical physics | [The three-state root-fidelity entropy bound](../papers/physics/fidelity-three-state/) | [PDF](../papers/physics/fidelity-three-state/manuscript.pdf) |
| Mathematical physics | [Exact conditional contraction for Pauli channels and depolarization in every dimension](../papers/physics/quantum-exact-contraction/) | [PDF](../papers/physics/quantum-exact-contraction/quantum_exact_contraction.pdf) |

## Gyires companion environments

The unified [Gyires family](../papers/mathematics/gyires/) also contains the separate [order-six](../papers/mathematics/gyires/formalization/circulant-six/), [permutation-polynomial](../papers/mathematics/gyires/formalization/permutation-polynomial/) and [rank-two](../papers/mathematics/gyires/formalization/rank-two/) projects. Rank-two orders 2 through 8 are proved. General order-seven circulants and rank-two orders 9 through 15 remain incomplete in Lean; see [UNFINISHED.md](../UNFINISHED.md).

## Reproduce and interpret the checks

From `lean/`, run:

```sh
lake exe cache get
lake build MathAndTheory Solutions Challenges
lake env lean Audit.lean
```

Use the [verification guide](../verification/README.md) for Comparator, independent-kernel checks and the standalone commands. Only `propext`, `Classical.choice` and `Quot.sound` are accepted in proved theorem dependencies. Source-integrity checks are separate from completed Lean builds. Formal checking establishes the stated propositions, not novelty, source identity or human peer review.
