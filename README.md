# A sharp universal skewness bound for unicyclic currents

This candidate pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Local compilation, exact Comparator
comparison, default Lean kernel replay, and the strict endpoint audit pass.
The local Comparator ran without a sandbox. Full pinned Palomar preflight is
still required.

The selected theorems use the actual marked-edge tilted matrix of a finite cycle
with at least three states. Every forward and reverse rate is strictly positive.
Their products differ. Every local C3 zero-eigenvalue branch has nonzero first
derivative and third-to-first derivative ratio in [-1/16,1]. A local branch exists
from the rates alone. No spectral or uncertainty conclusion is assumed.

[Challenge.lean](Challenge.lean) imports only Mathlib. It copies the exact matrix
and tilt definitions. Its two deliberate theorem holes are separate from
[Solution.lean](Solution.lean), which imports the 34 original proof modules and one compatibility module.
The Comparator path is [comparator/unicyclic-skewness.json](comparator/unicyclic-skewness.json).
The root Lake package maps the proof library to `proof/`.

The identification with long-time stochastic cumulants uses the conventional
spectral-projection proof in the manuscript. Universal sharpness uses a
conventional positive-rate limiting family with increasing ring size. Lean does
not construct sample paths or prove a separate optimizing-sequence theorem.
The ratio is not standardized skewness. Equal rate products are excluded.
Separate one-state and two-state counted-channel models remain included.

The manuscript, exact scalar certificate, coefficient tables, arithmetic checker,
licenses, citation files, and authorship disclosure are preserved. The manuscript's
Lean 4.19.0 verification claims describe the historical source. They do not certify
this port. Earlier compiler reports and release hashes are excluded. Source hashes
record integrity only. See [VERIFICATION.md](VERIFICATION.md) for the current status.

The interval is credited to K. Ptaszyński, Physical Review E 106, 024119 (2022),
Equation 21. The manuscript credits prior midpoint-spectrum and uncertainty results
and the known limiting family. Formal proof does not certify bibliographic priority.

This work is fully autonomous agentic research. AI systems generated and developed
the research, proofs, formalizations, corrections, and manuscript. Dev D. Goyal is
responsible for publication. No expert human validation or peer review is claimed.
The source uses [Apache-2.0](LICENSE). Imported libraries retain their own licenses.
