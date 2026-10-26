# Manuscript and material revision

This record covers the editorial revision of all seven papers and their current explanatory material on 26 October 2026. The baseline is commit `1fe8b6cb3ee3c9bb54258c37d61964c84309d475`.

The six shorter manuscripts now use direct explanations of the results, definitions, and proof steps. The 100-page Gyires manuscript retains the text and PDF checked in the preceding editorial review. The catalogue, overview, formal guides, verification guides, and supporting notes use the same scope. Historical source texts, legal notices, bibliographies, and old verification logs retain their recorded content.

## Mathematical content

The revision preserves every numbered theorem, lemma, proposition, and corollary body in the seven manuscripts. It preserves all displayed formulas, citations, and labels. Two inline expressions were repeated to clarify their surrounding text. They are `D` in the best-of-n inverse-curve argument and `M=1` in the diagonal-concavity abstract.

The best-of-n scope paragraph now identifies the two responses involved in a tie. They are the selected response and an independent reference draw. The definition and proof already used this comparison. No theorem changed.

All 221 Lean source files are unchanged. The toolchain, dependency manifest, and Comparator configurations are unchanged. Four Python files have revised descriptions or example commands. Their executable syntax trees are unchanged.

## Documents and records

All seven papers and the overview compile with Tectonic 0.17.0 without layout or reference warnings. All 132 pages were rendered and inspected. The new Gyires build has the same page content streams and extracted text as the retained PDF. The checked PDF is therefore preserved.

The [check record](collection-editorial/checks.json) gives the source hashes, PDF hashes, page counts, statement comparisons, and formal input comparison. The [review record](collection-editorial/review.md) gives the two independent AI review passes. The [source manifest](records/source-hashes.json) identifies current file contents.

The [earlier verification summary](summary.md) and [mathematical review](review.md) are historical records. Their checks retain their stated revisions and scope. A full Palomar report applies only to the source commit named in that report. The [Palomar guide](palomar.md) explains how to check that match.

## Submission scope

Seven manuscripts are prepared as preprints. Five retain the standalone archival recommendation. They are q-permanent, best-of-n, Hofstadter iteration, diagonal concavity, and Gyires. The explicit request to archive Gyires supplements its catalogue assessment. DomiRank and alternating Motzkin remain additional candidates.

The Palomar fields cover the 21 selected statements in seven configurations. The Gyires configuration covers the principal order-five statements only. The broader Gyires proofs have incomplete Lean verification. Neither the unrestricted Gyires conjecture nor every auxiliary target is proved.

No Zenodo deposit, DOI, or Palomar registration is created by this revision. No journal or conference format has been selected. These papers have not received independent human expert peer review.
