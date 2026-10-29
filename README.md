# The three-state root-fidelity entropy bound

This candidate pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Local compilation, exact Comparator
comparison, and the default Lean kernel check pass. The local Comparator ran
without a sandbox. Full pinned Palomar preflight is still required.

The statement covers three positive semidefinite trace-one complex matrices in
any finite dimension. The three nonnegative weights sum to one. Singular states
and zero weights are included. The weighted root-fidelity matrix bounds the
ensemble Holevo quantity through its entropy. Root fidelity is not squared fidelity.

[Challenge.lean](Challenge.lean) imports only Mathlib. It contains the exact
spectral entropy, nuclear norm, weighted root, ensemble average, and root-fidelity
matrix definitions. Its two deliberate theorem holes are the structural positivity
result and the final entropy inequality. The positivity result supplies the
Hermitian proof needed by the entropy term. [Solution.lean](Solution.lean)
imports the complete proof. [formalization.yaml](formalization.yaml) records scope.

The 42 prior QICLean modules are split at their original module boundaries into
ordered files in `QICFoundation/`. Each original source block, legal notice, and
proof body is retained byte-for-byte. `QICFoundation.lean` imports the final part.
The updated `QICFoundation.sources.json` gives current source maps and retains
upstream source identities. `theorem-map.json` describes mathematical scope.
See [VERIFICATION.md](VERIFICATION.md) for the source-bound local check.

The [manuscript PDF](manuscript.pdf) and [TeX source](manuscript.tex) are preserved
from the earlier source. Their Lean 4.35.0-rc3 verification discussion describes
that historical version. Earlier compiler logs, verification reports, and release
hashes are excluded. `source-sha256.json` records integrity only.

The original inequality is credited to Fannes, de Melo, Roga, and Życzkowski.
The proof credits the Li–Zhang construction and prior quantum relative entropy
results. QICLean is prior work at commit
`acda92aa70e69b37507e422bceb5414036859fe6`. Preserve [LICENSE.QICLean](LICENSE.QICLean)
and every original copyright notice. Bundling this source is not a research
contribution. Priority is not certified by the available literature comparison.

This is fully autonomous agentic AI research. AI systems developed the mathematical
argument, formal proofs, and manuscript. Dev D. Goyal is responsible for publication.
No expert validation or peer review is claimed. The original package uses
[Apache-2.0](LICENSE). Use the retained citation files to cite the preprint.
