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
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The complete local proof is ported
to `module`, `public import`, and `@[expose] public section`.
The substantive upstream dependency remains pinned at
`636352f0fef47b19d7d5de364858ccee2317fd66`. Its sources are not redistributed.
Its compatibility with the new Mathlib pin is not established.

These files require a fresh full Palomar preflight. No build, comparator run,
or axiom audit was performed for this package. No verification certificate
is supplied. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. `Audit.lean` contains the requested checks. The only intended
proof placeholder is in Challenge. It is excluded from Solution imports.

The classification applies to the nonnegative quadrant. It does not classify
negative parameters or all equality cases. No new check of mathematical
novelty or expert review is claimed.
