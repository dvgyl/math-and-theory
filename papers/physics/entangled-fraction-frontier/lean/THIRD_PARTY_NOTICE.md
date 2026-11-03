# Third-party code in the Lean project

`AllProofs.lean` is a single compilation unit assembled from 21 constituent files. Each constituent is a section headed `/-! ## Source: <name>.lean -/`; [source_manifest.json](source_manifest.json) records the constituent hashes and the line mapping. The following sections contain or adapt third-party code. All of it is distributed under the Apache License 2.0; the license texts are in [third_party/](third_party/).

## Omega Institute, trureturing (sections `LocalPrerequisites` and `Replay`)

- Repository: https://github.com/the-omega-institute/trureturing, commit `609e95e447fb1045172423c4d7bcf2a6e321eef0`. License: Apache License 2.0 ([third_party/trureturing-LICENSE](third_party/trureturing-LICENSE)). No NOTICE file was found at the root of the repository.
- Target file: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.lean`, 53,592 bytes, SHA-256 `12103d831e2f56d8f24c17b678402aa33562c8b0c88b4d964277e76b83e3ab1d`. It proves Conjecture 2 of Milne, Jennings, Jevtic and Rudolph (arXiv:1404.3951), issue #14206.
- Changes: in section `Replay`, the six `import D5...` lines of the target are removed and three `#print axioms` commands are appended; the statements and proof bodies are unchanged. Section `LocalPrerequisites` replaces those six imports by copies of the declarations the target consumes, taken from `D5/S3/Quantum/FiniteDimensional.lean`, `D5/S3/QuantumBounds/CHSHWitness.lean`, `D5/S3/Quantum/Information/PartialTraceMutualInformation.lean`, `D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.lean`, `D5/S3/Quantum/Information/ActualPureQubitGeometry.lean` and `D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction.lean` at the same commit.
- The upstream file `PartialTraceMutualInformation.lean` states that its partial-trace positivity and trace proofs are adapted from `CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` of https://github.com/zblore/csd-lean4, revision `13eda16971c66de4bc9f550e418dd4fdf59a5121`, Copyright (c) 2026 Zayn Blore, Apache License 2.0 ([third_party/csd-lean4-LICENSE](third_party/csd-lean4-LICENSE)).

## QICLean (sections `WeylMonotonicity` and `GramUnitaryExtension`)

- Copyright (c) 2026 Sirui Lu and QICLean contributors. Apache License 2.0 ([third_party/QICLean-LICENSE](third_party/QICLean-LICENSE)). Repository https://github.com/LionSR/QICLean, commit `c457682404aa548b4acd16ac27be5d3835e68892`.
- `WeylMonotonicity`: extracted from `QICLean/Analysis/WeylMonotonicity.lean`; the mathematical proofs are unchanged, a later theorem and unused imports are removed, provenance comments and axiom reports are added. [third_party/weyl_manifest.json](third_party/weyl_manifest.json) records the hashes and scope.
- `GramUnitaryExtension`: the first theorem of `QICLean/Algebra/MatrixGramUnitary.lean` with its proof; later theorems and two unused imports are removed.

## Mathlib (sections `SubstochasticRearrangement` and `WeightedTrace`)

- Apache License 2.0 ([third_party/Mathlib-LICENSE](third_party/Mathlib-LICENSE)).
- `MilneSharp.abel_comparison` adapts `Finset.sum_mul_le_sum_mul_of_sum_range_le` (Mathlib `Mathlib/Algebra/Order/Chebyshev.lean`, Copyright (c) 2023 Mantas Bakšys, Yaël Dillies), specialized to real sequences and renamed.
- The private lemmas `unitary_row_sq_norm` and `unitary_col_sq_norm` adapt the interior calculation of `Matrix.entry_norm_bound_of_unitary` (Mathlib `Mathlib/Analysis/CStarAlgebra/Matrix.lean`, Copyright (c) 2022 Hans Parshall), adding the column analogue.

The remaining sections and the five modules `OptimizerComplementarity`, `MarginalRank`, `RectangularOptimizerRank`, `NilpotentTensor` and `NilpotentState` were written for this work. `RankOneExtraction` generalizes the finite two-qubit Cauchy–Schwarz and rank-one subtraction step of the Omega proof to arbitrary finite dimension; this standard lemma is not claimed as new.
