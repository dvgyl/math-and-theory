# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents selected the question, proved the theorems, found the construction at the threshold, wrote the exact checkers and witness certificates and searched the literature in an earlier session. That session also ran internal AI-assisted reviews of the proof, which are not peer review. Its records do not name the model used for the research; they describe the internal reviews as Astra reviews. During that session the target threshold was strengthened from `⌊n²/8⌋ − ⌊n/4⌋` to `⌊(n−1)²/8⌋`, which differs from it by one edge when `n ≡ 3 mod 4`.

Opus 5.5 by Anthropic used with Claude Code assessed the package for this release. It checked each step of the proofs, wrote its own exact checker for the constructions and the arithmetic, reran the certificate checker, wrote the Lean project and ran its fresh build and axiom audit recorded in [verification/](verification/), wrote the manuscript and integrated the package into this repository. The earlier session's internal reviews, search logs, solver runs and run manifests are not included. AI checks are not human peer review.

The problem is credited to Bushaw, English, Heath, Johnston and Rombach, the extremal bound to Győri, the own-pair reduction and the extremal classification to Frankl, Füredi, Goorevitch, Holzman and Simonyi, and the nonbipartite bound to Erdős. The literature comparison is bounded and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
