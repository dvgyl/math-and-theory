# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents produced the search, the construction, the proof of the main theorem, the Lean formalization and an earlier version of the note in an earlier session. The records of that session state that it was an autonomous ChatGPT session in which GPT-6 Astra Pro agents carried out the search, the formalization and skeptical reviews.

Opus 5.5 by Anthropic used with Claude Code assessed the package and coordinated an independent AI referee check: it rebuilt the construction from the published subspace bases, rechecked every character sum, the tiling and the allowed shifts, enumerated all tiling complements in two independent ways and compared the Lean statements with the theorem. Opus 5.5 proved that the complements are exactly the translates of `T` and formalized this classification in [BinaryComplements.lean](lean/BinaryComplements.lean), re-froze the Lean release, wrote [checks/check_construction.py](checks/check_construction.py), ran the fresh Lean replay recorded in [verification/](verification/), revised the manuscript and integrated the package into this repository. AI checks are not human peer review.

The affine-circuit ingredient is credited to Ferguson and Iosevich. The literature comparison is bounded and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
