# Formal verification scope

The theorem applies to every normalized pure state of four distinguishable qubits. A state is a vector with sixteen complex amplitudes. The conclusion is

`average entropy ≤ log(2) + log(3)/2`.

The average uses the three partitions AB|CD, AC|BD, and AD|BC. Each entropy uses the actual eigenvalues of the corresponding reduced density matrix. The theorem does not assume that the one-qubit reduced states are maximally mixed. The Higuchi–Sudbery state attains the bound.

The proof establishes an exact sum-of-squares identity over all sixteen complex amplitudes. It then connects this identity to the reduced matrices, their eigenvalues, and the entropy bound. The homogeneous polynomial statements include the zero vector. The normalized entropy statement has only the squared-norm hypothesis.

The package uses Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The submission branch ports the proof sources to the module system and adds an
independent Challenge. These changed files require a fresh full Palomar preflight.
Earlier compiler records do not certify this snapshot. The workflow checks the exact
commit, complete Solution, Challenge comparison, and permitted axioms before intake.
Compiled objects are not distributed.

`HS/Audit.lean` prints eleven exact axiom reports and the types of three entropy endpoints. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The proof does not depend on an added mathematical axiom, a proof placeholder, or `native_decide`.

The main endpoints are `HS.higuchi_sudbery_bound`, `HS.higuchi_sudbery_maximum`, and `HS.higuchi_sudbery_bound_bits`. They give the upper bound, its attainment, and the same bound in bits. The result does not classify all maximizing states. It does not cover mixed states or unequal weights on the three cuts.

The Python certificate checker is a separate exact integer check. It does not replace the Lean proof. See [README.md](README.md) for research attribution and the limits of author review. A formal proof does not establish novelty or expert peer review.
