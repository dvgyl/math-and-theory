# A five-cycle of classical two-block ADMM

This is an uncompiled submission candidate. It pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. No successful compilation,
Comparator check, or Palomar preflight is claimed for these bytes.

The exact multiplier step is 199/100. The penalty is one. Both sets are the
convex hulls of five displayed vectors in four real coordinates. They are
compact and convex, and both contain zero. Zero is an optimizer for the indicator
feasibility problem. The same instance has a zero fixed ADMM trajectory.
A different initialization gives an actual nonconstant five-cycle. Its squared
primal residual is at least 500000 at every iteration and does not tend to zero.

The update is

```text
x^(k+1) = P_C(z^k - u^k)
z^(k+1) = P_D(x^(k+1) + u^k)
u^(k+1) = u^k + (199/100) * (x^(k+1) - z^(k+1)).
```

Each projection is the unique global minimizer of the complete squared-distance
subproblem. Only the multiplier update is changed. The other overrelaxed ADMM
convention changes a primal argument as well.

[Challenge.lean](Challenge.lean) imports only Mathlib. It copies the exact finite
data, convex hulls, projection definition, trajectory definition, and selected
theorem statement. Its deliberate theorem hole is separate from
[Solution.lean](Solution.lean), which imports every local proof module.
[formalization.yaml](formalization.yaml) records scope and attribution.
The family-specific Comparator path is
[comparator/admm-counterexample.json](comparator/admm-counterexample.json).

The alternative finite-objective trajectory is retained in
`Research/ADMMHingeTrajectory.lean`. It checks the actual infinite orbit, unique
proximal minimizers, and unique constrained optimizer. Its convexity, strong
convexity, C2 regularity, and Lipschitz-gradient properties use conventional
manuscript proofs. These properties are not checked by the supplied Lean modules.

The complete manuscript, source, exact arithmetic certificates, optional discovery
scripts, licenses, citation files, and third-party notices are retained.
The manuscript's earlier Lean 4.19.0 verification claims describe the historical
source. They do not certify this port. Earlier compiler receipts, release hashes,
and the version-specific Lean verifier are excluded. `source-sha256.json` records
integrity only. See [VERIFICATION.md](VERIFICATION.md) for the current status.

This release was prepared through fully autonomous agentic research. AI agents
audited the supplied proof sources and reran earlier checks. The original model
history is not documented. No human proof review, external peer review, or
literature-priority determination is claimed. Dev D. Goyal is responsible for
publication. The package retains [Apache-2.0](LICENSE) and
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
