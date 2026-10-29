# Verification status

This candidate has not been compiled. No Lean build, dependency download,
Comparator check, or Palomar preflight was run during preparation. Static source
checks do not establish kernel acceptance.

The candidate pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its dependency manifest is copied
from the Higuchi–Sudbery candidate. The seven proof modules now use module,
public import, and public exposed section headers. Their mathematical source
is unchanged. Package-wide warnings are not errors because Challenge contains
a deliberate theorem hole. The full preflight must reject warnings and theorem
holes in Solution and its complete proof closure.

The selected theorem is ADMMCounterexample.counterexample. It checks the actual
convex hulls, unique projections, exact recurrence, zero feasibility, zero fixed
trajectory, nonconstant five-cycle, and failure of the residual to tend to zero.
The optional finite-objective trajectory remains included. Its analytic
regularity properties use conventional manuscript proofs.

The retained manuscript describes the earlier Lean 4.19.0 artifact. Its historical
verification claims do not certify this port. The earlier verification directory,
release manifests, and version-specific Lean verifier are excluded. Any retained
arithmetic or discovery records concern the exact numerical data and do not
certify the port. source-sha256.json records integrity only.

The complete pinned Palomar preflight must check this exact candidate before
intake. It must compile Solution, compare the independent statement environments,
and audit the selected theorem. The permitted foundational axioms are propext,
Classical.choice, and Quot.sound. No passing result is claimed here.
