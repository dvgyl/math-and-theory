# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents produced the research, the exact certificates, the Lean formalization and the earlier reports in sessions whose records do not name the model or system used. Three uploaded packages contributed: a convergence dossier for `0 < tau <= 7/4`, an interval package for `[3/2, 7/4]` with general linear constraints, and the near-sharp package with the longer-memory certificates and the polytope orbit. The first two are superseded; their Lean modules are included here unchanged where the final proof uses them.

Opus 5.5 by Anthropic used with Claude Code assessed and consolidated the three packages. It coordinated independent AI referee checks, including new exact-arithmetic rechecks of the cycle and interval certificates. It ran the fresh Lean replay recorded in [verification/](verification/), added the comparison with Gao et al. (2022) and the scope notes, rewrote the manuscript, and integrated the package into this repository. AI checks are not human peer review.

The methodology of interpolation inequalities and computer-searched Lyapunov certificates is prior art and is credited in the manuscript. The literature comparison is bounded by the sources cited there and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
