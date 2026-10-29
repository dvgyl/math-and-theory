# Verification status

A local source replay compiled all 20 proof modules and Solution with Lean 4.35.0
and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Each process used
`--trust=0`, one Lean worker, and a 4096 MiB Lean memory limit. The replay used a
fresh project output directory and source-bound logs. No old project objects
were reused. Official pinned dependency caches supplied the external libraries.

The actual-function upper bound, radius corollary, and normalized attainment
declaration depend only on `propext`, `Classical.choice`, and `Quot.sound`.
[Selected types and axioms](verification/selected-types-and-axioms.txt) gives the
compiler output. [The local summary](verification/local-replay-summary.json)
records the exact compiler, source hashes, and limits. Proof-source warnings
were recorded and were not errors. The separate endpoint audit used warnings
as errors. No proof hole or custom axiom was accepted in Solution.

Challenge compiled independently with only its two specific Mathlib imports.
Its two deliberate theorem holes are excluded from Solution. A local Comparator
check and a full pinned Palomar preflight remain required before intake. The
local direct Lean replay does not establish the Lake package build or registry
acceptance. No repaired-version Palomar success is claimed here.

The selected upper bound uses actual functions and gradients. Formal attainment
has L = R = 1. Arbitrary-scale attainment remains a conventional manuscript
rescaling proof. The mathematical statement definitions and selected declaration
headers are unchanged from the recorded source.

The retained manuscript records historical Lean 4.19.0 verification. It does not
certify the changed package. Earlier compiler logs, old release manifests, and
the version-specific verifier remain excluded. The new local evidence concerns
the source hashes recorded in its summary. `source-sha256.json` records package
integrity only. No formal check establishes bibliographic priority or expert
validation.
