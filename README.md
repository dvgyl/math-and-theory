# The exact last-gradient bound for constant-step gradient descent in the strongly convex case

A local source replay compiled all 20 proof modules and Solution with Lean 4.35.0
and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The independent
Challenge also compiled with its two deliberate theorem holes. The three public
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The full Palomar preflight and Comparator check are still required. See
[the local replay summary](verification/local-replay-summary.json).

The selected upper bound uses actual functions and gradients on every complete
real inner-product space. It includes every natural horizon, curvature parameter
0 ≤ μ ≤ L with L > 0, and normalized step 0 ≤ h ≤ 2. The starting distance is
the distance to an actual global minimizer. The one-dimensional attainment
theorem has L = R = 1. The manuscript gives the conventional rescaling proof
for L > 0 and R > 0.

`Challenge.lean` gives the independent statements and exact definitions.
It imports only Mathlib. Its two deliberate theorem holes are separate from
`Solution.lean`, which imports the complete proof. `comparator/strong-gradient.json` lists the
two selected declarations. `formalization.yaml` records their scope and credit.
The proof sources remain in `lean/`. The root Lake configuration uses that path.

The manuscript files are preserved from the recorded source commit. Their
Lean 4.19.0 verification discussion describes the earlier source version.
It does not certify this candidate. Earlier compiler logs, source hashes, and
release manifests are excluded. See `VERIFICATION.md` for the current status.

Read [manuscript.pdf](manuscript.pdf), [manuscript.tex](manuscript.tex),
[PROOF_MAP.md](PROOF_MAP.md), and [AUTHORSHIP.md](AUTHORSHIP.md).
The original package uses [Apache-2.0](LICENSE). Adapted MIT-licensed source
retains its notices in [lean/THIRD_PARTY_LICENSE](lean/THIRD_PARTY_LICENSE).

Taylor, Hendrickx, and Glineur supplied the formula and sharp examples.
Chikhi and Jones supplied certificate antecedents. Jones established the
complete smooth-convex curve. The bounded literature comparison does not
certify worldwide priority.

This work is fully autonomous agentic research. Automated systems produced
the research, proofs, formalization, and manuscript preparation. Dev D. Goyal
is responsible for publication. No expert validation or peer review is claimed.
