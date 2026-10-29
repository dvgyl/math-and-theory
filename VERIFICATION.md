# Formal verification scope

The selected statement is `AsymmetricTutte.universal_iff_region`.
For nonnegative real parameters `x` and `y`, it gives an equivalence between
the universal finite-matroid inequality and `AsymmetricTutte.Region x y`.
The region requires `1 < x`, `1 < y`, and both scalar families for every
natural number `k ≥ 2`.

`AsymmetricMerinoWelsh.Universal` quantifies over every `α : Type` and every
actual Mathlib `Matroid α` with finite ground set. `IsAdmissible` excludes loops
and coloops. `tutte` uses the literal finite subset rank sum. Empty ground sets
are included. The intermediate rank-model lemmas do not add hypotheses to the
final theorem. The final theorem does not assume an abstract rank-axiom model.

The active configuration pins Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The public Challenge
definitions and selected theorem are exact. Local support interfaces use
private imports and declarations.
The substantive upstream dependency remains pinned at
`636352f0fef47b19d7d5de364858ccee2317fd66`. Its sources are not redistributed.
The local build reads the exact dependency files in place. A guarded build
configuration assigns separate module identities through ModuleSetup.
The source files are unchanged. Their declaration namespaces stay unchanged.
No upstream proof source is included or ported in this package.

A local sequential Lake build passed for all 36 modules, including the ten
guarded upstream modules, the complete local proof, Challenge, Solution, and
Audit. Audit used warnings as errors. The selected theorem and five support
results use only `propext`, `Classical.choice`, and `Quot.sound`.

The actual Challenge and Solution exports passed the bundled exact Comparator,
the permitted axiom check, and the default Lean kernel check. This local run
had no sandbox. No external kernel or full Palomar preflight was run. Full
pinned Palomar preflight remains required before intake. The local summary
records the checked source hashes and limits. The only intended proof
placeholder is in Challenge. It is excluded from Solution imports.

The classification applies to the nonnegative quadrant. It does not classify
negative parameters or all equality cases. No new check of mathematical
novelty or expert review is claimed.
