# Formal statement and verification scope

This package is an uncompiled module-system port. It retains Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The complete source came from commit `a6574b1bf6a591d81c3314d5333fc5da26712d6b` of `dvgyl/math-and-theory`.

The public recurrence definitions use the actual sequence shift `u(n) ↦ u(n+1)`. A polynomial acts through that shift. An admissible recurrence polynomial is monic, has nonzero constant coefficient, and annihilates the sequence after some index. The rank is the infimum of the possible natural degrees. For the constructed sequences, the supplied minimal characteristic polynomial makes this the least eventual recurrence order.

The main sequence is the literal integer expression

`1 + 2^n + 3^n(1 - 2^n)^2 + n9^n(1 + 2^n)^3`.

The selected main theorem states positivity, agreement with the complex-valued sequence, rank 13, and the complete minimal characteristic polynomial of every termwise power. It includes the exact natural-number rank formula

`(M + 1)(2M + 1)(7M + 6)/6 - 2Q(M)`.

Here `Q(M)` counts natural `q` with `M < q² < 3M` and parity opposite to `M`. The strict endpoints and natural-number division and subtraction are preserved in Challenge. The formula includes `M = 0`. The square-root estimate has error at most two for every `M ≥ 1`.

An eventually quasipolynomial sequence uses one real polynomial on each residue class of a positive integer period, after a common threshold. The selected theorem excludes this definition for the main power-rank sequence.

The companion statement uses the actual positive sequence `1 + 2^n + 2^(dn) + ∑ p_i^n`, where `d ≥ 2` and the `r - 3` values `p_i` are distinct odd primes. It gives initial rank `r` for every `r ≥ 3`, the complete minimal characteristic polynomial of every natural power, and the exact binomial-difference rank formula. A second selected companion statement supplies suitable prime data and infinitely many different power-rank profiles at each fixed initial rank. The zeroth-power boundaries remain in the complete source.

The complete package has 35 proof modules. Solution imports `CompleteAudit`, which imports the main theorem and companion existence theorem. The audit requests 25 transitive-axiom reports. Its requests are not current compiler results. The expected permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The companion generating function, eventual polynomial degree and leading coefficient, and simplified rank-three examples retain their conventional manuscript proofs. They are outside the selected formal claim. The rank-13 example is not asserted to have simple characteristic roots. The package does not claim that 13 is the minimum possible initial rank.

The manuscript, authorship disclosure, and source notices are preserved. Their descriptions of the earlier source verification do not certify this port. The old hash manifests and original verifier scripts were removed. `source-sha256.json` is a current integrity inventory only. The retained supplement record describes an earlier bounded arithmetic run. It is not a current proof check and does not replace the universal statements.

No build, dependency download, Comparator check, or full preflight was run during this preparation. Before intake, run the pinned official full Palomar preflight on the exact published commit. Check the complete Solution, the independent Challenge comparison, every required kernel outcome, and the actual transitive axioms. Formal verification does not certify historical priority or the meaning of the source's undefined term “pseudo-polynomial.”
