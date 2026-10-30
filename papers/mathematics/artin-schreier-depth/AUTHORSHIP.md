# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents produced the proof, the Lean formalization of the converse, the literature searches and an earlier version of the note in an earlier session. The records of that session do not name the AI system used.

Opus 5.5 by Anthropic used with Claude Code assessed the package for this release. It checked the argument step by step, read the arXiv source of the source paper and checked the cited definitions and theorems, compared the Lean endpoints and their hypotheses with the theorem, formalized the converse in the source's ambient field, the forward implication and their equivalence ([HahnClosureDepth.lean](lean/HahnClosureDepth.lean) and [HahnClosureForward.lean](lean/HahnClosureForward.lean)), ran the fresh Lean replay recorded in [verification/](verification/), rewrote the manuscript and integrated the package into this repository. AI checks are not human peer review.

The conjecture, the depth criterion and the forward implication are due to Nart and Novacoski; the minimal-face extraction is credited to Kedlaya. Adapted Lean source is credited in [lean/THIRD_PARTY.md](lean/THIRD_PARTY.md). The literature comparison is bounded and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
