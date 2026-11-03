# Provenance of the reused quantum matrix lemmas

The 22 modules in this directory are adapted, with attribution, from my own earlier Lean formalization of two-qubit steering-ellipsoid results. That is the development from which the repository's [steering-bounds](../../../steering-bounds/) package was released. They are not new contributions of this package. [PROVENANCE.json](PROVENANCE.json) records, for each module, the original file name, its SHA-256 before adaptation, the SHA-256 of the adapted file and how it compares with `steering-bounds` at repository commit 88bc641:

- 4 modules match the original `steering-bounds` file exactly;
- 8 modules also exist in `steering-bounds`, whose later editorial revision changed comments and a few tactic lines;
- 10 modules were not released with `steering-bounds`. They are the Bloch identities, complex filtering, the one-sided orbit quadratic, the physical orbit and its filter, the qubit effect ball, the geometry and geometry bridge, the centre coordinates, and the extracted Pauli algebra.

The adaptation prefixes local import names with `QuantumPrior` and narrows broad imports. Namespaces (`Milne`), statements and proof bodies are otherwise unchanged. `MilnePauliAlgebra` extracts `spin_hermitian` and `spin_squared` from `MilneGeometryConsequences` and `psd_real_smul` from `MilneSharpness`, all unchanged. Every module is compiled from source in this project's build and is covered by the axiom audit.

The reused results concern actual complex matrices: Pauli reconstruction, the correlation-norm and purity identity, determinant covariance under arbitrary complex two-by-two filters, positivity of the qubit effect ball, physical realization of every effect-ball point, and whitening of a density matrix with nonsingular filtered marginal. `MilneCore` and `MilneAllStates` also contain the fully-entangled-fraction bound f(ρ) ≤ 1 − c/2, Conjecture 2 of Milne, Jennings, Jevtic and Rudolph. This package does not use it for its main theorem and claims no priority for it. The [package README](../../README.md#prior-work-and-priority) gives the earlier public record.
