# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents produced the construction, its proof, the Lean formalization, the exact certificate, the literature searches and an earlier version of the note in an earlier session. The records of that session state that two of its novelty reviews used GPT-6.1 Terra and GPT-6.1 Sol; they do not name the system used for the construction and the formalization.

Opus 5.5 by Anthropic used with Claude Code assessed the package for this release. It checked the argument line by line, read Conjecture 1 of Vandaele, Gillis, Glineur and Tuyttens and the main statements of Chauhan and Choudhury, compared the Lean definitions of nonnegativity, factorization, nonnegative rank and the conjecture with the manuscript, ran the fresh Lean replay recorded in [verification/](verification/), reran the exact certificate, wrote the independent check [check_factorization.py](certificate/check_factorization.py), wrote the manuscript in LaTeX and integrated the package into this repository. The earlier session's internal reviews, search logs and registration notes are not included. AI checks are not human peer review.

The conjecture and the seed matrix are credited to Vandaele, Gillis, Glineur and Tuyttens, the seed also to Bocci, Carlini and Rapallo, and direct-sum additivity of nonnegative rank to Qi, Comon and Lim. The literature comparison is bounded and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
