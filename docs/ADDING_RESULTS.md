# Adding a result

1. Choose `papers/<subject>/<family>/`, where the subject is `mathematics`,
   `theoretical-computer-science` or `physics`. Put a companion result inside its
   existing family. For a new companion identifier, add its family/subdirectory
   alias to `GROUPS` in `verification/repository_layout.py`, as for Motzkin.
   Keep the manuscript PDF, TeX source, citation, disclosure,
   license and reproduction instructions together. Each family needs a README.
2. Add the manuscript to `catalogue.json` with its discipline, area, contribution,
   exact formal scope and source references. The catalogue determines the
   canonical family route. A standalone entry names that same directory as its
   formalization root. Shared-library entries name their Comparator configuration.
3. For a new standalone proof package, pin Lean and every dependency, supply an
   executable strict verifier and record the actual replay and axiom scope.
   Add its exact proof roots and immutable file inventory to
   `verification/curated-packages.json`. The common verifier derives package
   membership from the catalogue; no second identifier allowlist is required.
4. Add its verification command to the appropriate CI matrix. Keep hosted builds
   in temporary work copies so they do not alter the published evidence. Include
   all required modules and reject proof holes or unapproved axioms.
5. Add the result to the subject index, CONTENTS and overview. Highlight it in the
   README only if its significance and verified scope justify that selection.
   Keep conventional proofs, incomplete formalizations and unresolved source
   comparisons explicit. Update `UNFINISHED.md` when needed.
6. Rebuild changed manuscripts and check their extracted text against the source.
   Freeze each package inventory, update `publication-files.json`, then run
   `python3 verification/update_hashes.py`. Run the commands in
   `verification/README.md`, the relevant fresh proof replay and an independent
   review before publication. Never update a replay record to imply an unrun
   check; distinguish metadata changes from new mathematical verification.

`lean/` contains the shared formal library and its statement comparisons.
`verification/` contains collection-wide tools, tests and check records only.
Do not create arrival-based folders or put papers under verification tooling.
Private inputs, conversations, internal audits and build caches do not belong
in the published tree.

A minimal standalone catalogue entry has this shape (replace all example values
and provide the actual reviewed contribution and scope):

```json
{
  "id": "example-result",
  "discipline": "Mathematics",
  "area": "Matrix theory",
  "title": "Precise manuscript title",
  "kind": "Theorem",
  "summary": "Exact result, hypotheses, and boundaries.",
  "source": "Credited prior work and comparison scope.",
  "source_url": "https://example.org/paper",
  "paper": "papers/mathematics/example-result/manuscript.pdf",
  "formalization": {
    "kind": "standalone",
    "root": "papers/mathematics/example-result"
  }
}
```
