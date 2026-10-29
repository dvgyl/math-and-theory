# Formal verification scope

The two selected Challenge statements are
`PalomarQuantum.every_pauli_channel` and `PalomarQuantum.actual_full_channel`.
Each states existence of an actual complex-linear, completely positive,
trace-preserving channel with the explicit map. Each gives the exact
conditional coefficient for every channel with that map.

The Pauli statement includes every nonnegative four-weight probability vector.
It selects two distinct labels for the smallest weights, with multiplicity.
All ties and zero-weight cases remain included. The depolarizing statement
includes every dimension `d ≥ 2` and the full closed signed physical interval.
Both statements include every hockey-stick parameter `γ ≥ 1`.

A density matrix has positive-semidefiniteness and trace-one proofs.
The positive spectral trace uses the actual Hermitian eigenvalues.
The reference marginal is an explicit partial trace. The coefficient is
`sSup` of the actual final-gap/initial-gap ratios with strictly positive
initial gap. The reference system ranges over every finite type. There is
no equal-reference-marginal hypothesis and no fixed reference-dimension bound.

`PalomarEndpoints.lean` derives these forms from the original channel
constructors and exact coefficient theorems. Channel structure fields other
than the linear map are proofs. Equality of the map therefore gives equality
of the channels. The wrappers do not assume a contraction inequality.
The depolarizing wrapper uses the original theorem for every actual channel
with the stated map, and also supplies the proved constructor.

The complete source retains its normalized density witnesses and the limiting
arguments for sharpness. The finite Pauli witness covers a zero minimum pair.
The signed depolarizing proof includes both physical endpoints and zero.
These facts do not imply attainment of every supremum.

The active pins are Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The local proof sources use `module`,
`public import`, and exposed public sections. The port updates removed import
paths and proof APIs for matrix positivity, eigenvectors, square roots,
matrix blocks, and scalar algebra. The mathematical statements remain intact.
The independent Challenge retains the source definitions and instance scopes.

The complete package was checked locally on 2026-10-29. All 60 modules
and the default library target passed actual Lake builds with `--trust=0`. The original audit reported 42 theorem closures.
The wrapper audit reported two more. Each closure used only `propext`,
`Classical.choice`, and `Quot.sound`. Both audit imports also compiled with
warnings treated as errors.

The bundled `lake comparator` accepted both selected Challenge statements
and their full dependency closure. It accepted the permitted axioms and
replayed Solution with the default Lean kernel. The comparison used exports
from the checked modules and ran without a sandbox. A full sandboxed Palomar
preflight of the exact published commit remains required before intake.
No verification certificate is supplied.

The original manuscript records historical verification under Lean 4.19.0.
That record does not certify the active pins or changed sources.
`AuditExactContraction.lean` contains the original audit requests.
`PalomarAudit.lean` adds the two wrappers. The two deliberate Challenge holes
are excluded from Solution imports.
