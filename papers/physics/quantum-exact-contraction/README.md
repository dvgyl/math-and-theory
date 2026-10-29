# Exact conditional contraction for Pauli channels and depolarization in every dimension

I present in the [manuscript](quantum_exact_contraction.pdf) exact values of the conditional hockey-stick contraction coefficient for every stochastic Pauli qubit channel and the entire physical depolarizing family in every dimension d ≥ 2. The coefficient is a supremum over actual positive-denominator density-state ratios with arbitrary finite quantum references, including unequal reference marginals.

For the two smallest Pauli probabilities a,b, the value is 1 − 8ab/(a+b), with value 1 when a=b=0. For negative depolarization λ=−s, it is s[1+(d²−1)s]/[1−(d²−3)s]; for λ≥0 it is λ. These formulas hold for every hockey-stick parameter γ≥1, including all ties and parameter boundaries.

## Proof scope

The Lean project constructs the actual channels, proves the upper bounds for arbitrary finite references, and supplies matching normalized density witnesses and the passage to the supremum. The Pauli theorem uses `PauliConditionalExact.every_pauli_channel`; the all-dimensional signed depolarizing theorem uses `DepolarizingExact.actual_full_channel`. The audit requests 42 transitive axiom reports. The standard foundations permitted are `propext`, `Classical.choice` and `Quot.sound`.

The unital-qubit normal-form existence theorem is cited, not separately formalized. Erasure simulation and ensemble-guessing consequences have conventional manuscript proofs. No minimal reference dimension, general pure-state reduction, relative-entropy contraction, capacity or arbitrary-channel finite-reference computability result is claimed. Historical priority remains provisional.

## Reproduction

Install the toolchain in `lean-toolchain` (Lean 4.19.0), then run:

```sh
lake exe cache get
python3 verify.py
```

An existing clean checkout of the exact pinned Mathlib and its sibling dependencies can instead be used:

```sh
python3 verify.py --lean /path/to/lean --mathlib /path/to/mathlib
```

The verifier checks the exact compiler version/commit, all nine dependency revisions, tracked source cleanliness and local source hashes. It deletes local object files, rebuilds every local proof with trust level zero and warnings treated as errors, enforces bounded runtime and memory, checks each requested axiom report exactly once, and compares the external source/object dependency closure before and after compilation. Reproduction logs and dependency snapshots are written to `.verification/`; local objects are written to `.lake/`. No local compiled objects are distributed.

Build the manuscript with `latexmk -pdf quantum_exact_contraction.tex`. Install `requirements-diagnostics.txt` for optional plots and diagnostics. The figure source is `plot_exact_curves.py`; `tight_frame_validation.py` provides optional numerical diagnostics, not mathematical proof.

## Disclosure and citation

This is fully autonomous agentic research: AI systems produced the research, manuscript, proofs and formalization. Dev D. Goyal is responsible for publication. No expert human validation or external peer review is claimed. See [CITATION.cff](CITATION.cff) and the manuscript for attribution and scope. The repository license is [Apache-2.0](LICENSE).
