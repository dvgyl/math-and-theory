# Verification status

This candidate has not been compiled. No Lean build, dependency download,
Comparator check, or Palomar preflight was run during its preparation.
The static source preparation does not establish kernel acceptance.

The candidate pins Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The dependency manifest was copied
from the Higuchi–Sudbery candidate for the same pins. Proof modules now use
`module`, `public import`, and `@[expose] public section`. The proof mathematics
is unchanged. The actual-function upper bound and normalized attainment are
the selected statements. Arbitrary-scale attainment remains a conventional
manuscript proof.

The retained manuscript describes the earlier Lean 4.19.0 source. Its historical
verification claims do not apply to this candidate. The earlier verification
directory, hashes, release manifests, and version-specific verifier are excluded.
`source-sha256.json` records source integrity only. It is not compiler evidence.

The complete pinned Palomar preflight must check this exact candidate before
intake. It must compile Solution without the deliberate Challenge holes, compare
the two statement environments, check all required module headers, and audit
both selected declarations. The permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. No passing result is claimed here.
