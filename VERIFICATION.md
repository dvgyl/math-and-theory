# Verification status

A local source replay compiled all 18 proof modules and Solution with Lean 4.35.0
and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Each process
used trust level zero, one Lean worker, and a 4096 MiB Lean memory limit.
The project output directory was fresh. Official pinned dependency caches
supplied the external libraries. No old project objects were reused.

The five selected declarations and five square-root or reconstruction support
lemmas depend only on propext, Classical.choice, and Quot.sound. The separate
endpoint audit used warnings as errors. Proof-module compilation recorded
warnings without rejecting them. No proof hole or custom axiom was accepted
in Solution. The [local summary](verification/local-replay-summary.json) records
source hashes and limits. [Selected types and axioms](verification/selected-types-and-axioms.txt)
gives the compiler output.

The positive canonical filter now uses the current CFC.sqrt API on twice Bob's
marginal. The complete proof checks its Hermitian form, square identity,
positive-filter uniqueness, weighted positivity, and actual state reconstruction.
The selected theorem headers and domains are unchanged. No abstract scalar
filter or assumed correlation inequality replaces the actual matrix model.

Challenge compiled separately with specific Mathlib imports and its five
deliberate theorem holes. The local bundled Comparator passed exact comparison
of all five selected theorems, the permitted axiom check, and the default Lean
kernel check. This local run had no sandbox. No external kernel was checked.
Full pinned Palomar preflight remains required before intake. These local checks
do not establish the Lake build or registry acceptance. No repaired-version
Palomar pass is claimed.

The threshold concerns the specified three-setting correlation expression.
Measurement optimization and the steering-ellipsoid interpretation use cited
external correspondences. This does not characterize all steerable states.
The related fully entangled fraction theorem remains included in Solution.

The retained manuscript describes historical Lean 4.19.0 verification. It does
not certify this changed package. Earlier compiler records remain excluded.
The new local evidence concerns its exact recorded source hashes.
source-sha256.json records integrity only. No formal check certifies priority
or expert validation.
