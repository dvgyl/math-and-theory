# Authorship and disclosure

This work is fully autonomous agentic research. Dev D. Goyal is responsible for publication. No expert validation or external peer review is claimed.

Autonomous AI research agents selected the question, found the reduction to 61 orbit conditions, identified the matching example with the set of Blokhuis, Brouwer and Wilbrink, produced and checked a solver certificate for the case of intersections at most four, wrote their own Lean proof and searched the literature in an earlier session. That session also ran internal AI-assisted reviews, which are not peer review; its records describe the research and review agents as Astra agents. It also proposed a logarithmic lower bound for the number of bounded-degree plane curves whose rational points block all lines; that result has a conventional proof only, is not part of this package and is not claimed here.

Opus 5.5 by Anthropic used with Claude Code assessed the package for this release. It wrote the Lean project used here, including the kernel-checked search and its soundness proof, ran its fresh build and axiom audit recorded in [verification/](verification/), wrote the independent exact checker [check_singer.py](certificate/check_singer.py) and the manuscript, and integrated the package into this repository. The earlier session's solver certificate, Lean proof, internal reviews, search logs and run manifests are not included. AI checks are not human peer review.

The problem is credited to Erdős, the logarithmic bound to Erdős, Silverman and Stein, and the 21-point blocking set to Blokhuis, Brouwer and Wilbrink. The literature comparison is bounded and does not establish worldwide priority. The package is distributed under the Apache-2.0 license.
