# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents produced the proof, the Lean formalization and an earlier version of the note in an earlier session. The records of that session state that the note was prepared with ChatGPT; the model version is not recorded.

Opus 5.5 by Anthropic used with Claude Code assessed the package and coordinated an independent AI referee check: it re-derived the main chain of estimates, compared the theorem with Ivanisvili's manuscript and with the Lean statements, recomputed exact sign-vector counts for several hundred coefficient vectors and found no violation, and ran the exact rational constant checks. Opus 5.5 ran the fresh Lean replays recorded in [verification/](verification/), revised the manuscript (conditional wording for the full conjecture, credit to the strategy and lemmas of Ivanisvili's manuscript, and removal of claims resting on files not included here) and integrated the package into this repository. AI checks are not human peer review.

Three support modules are adapted from [CausalSmith](https://github.com/Jiyuan-Tan/CausalSmith) under the Apache-2.0 license; [third_party/causalsmith](third_party/causalsmith/) retains the license, notice, original files and a description of the changes. Prawitz smoothing and the prior results of Keller–Klein, Ivanisvili and others are credited in the manuscript. The literature comparison is bounded and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
