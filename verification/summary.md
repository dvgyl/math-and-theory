# Verification summary

The formal catalogue has seven result families, seven papers, and 21 selected statement comparisons. The [later Gyires research notes](../research-notes/gyires-extensions/README.md) have a separate certificate and review record. The formal checks below do not certify those two extensions. This record is dated 26 October 2026. Public logs replace local absolute paths with neutral labels and remove trailing whitespace. Their outcomes are unchanged. The checks concern mathematical statements and proof dependencies. They do not establish historical priority or human expert approval.

## Formal verification

The complete command `lake build MathAndTheory Solutions` passed with 2883 jobs. [Build log](records/native-final-build.log).

The command `lake env lean Audit.lean` passed for 8878 declarations, including 8096 proposition-valued declarations. [Axiom and type log](records/native-final-axiom-audit.log). These counts include generated supporting proofs. They are not counts of independent research results. Every audited declaration has only permitted transitive axioms: `propext`, `Classical.choice`, and `Quot.sound`. The audit imports the substantive library and all Solution modules. It excludes the independent Challenge holes.

The [Comparator record](records/comparators.json) lists all 21 selected statements and completed kernel outcomes. All seven configurations passed Lean, NanoDa, and con-ron. The runner and Linux requirements are in the [guide](README.md).

The [Gyires family record](gyires-circulant-five/formal-checks.json) also gives the fresh original-source build and its separate axiom audit. These historical-source checks do not substitute for the collection checks.

## Computation and documents

All seven independent computation programs and the separate best-of-n extension program passed. Each family guide gives its inputs, exact tested ranges, versions, output, and limits. The Gyires program reconstructed all 120 orderings and 120,120 coefficient positions. These finite checks supplement the general proofs.

All seven manuscripts and the overview compiled with Tectonic 0.17.0. The final compiler outputs contain no warnings, unresolved citations, or undefined references. Every final PDF page was rendered and inspected. The overview was rebuilt and all four pages were inspected again for the Gyires inclusion correction. No clipped text, overlap, or missing glyph was found. The [PDF record](records/pdfs.json) gives page counts and final PDF hashes. Compiler records are in [records](records/).

The official source checker, template metadata validator, pinned full v0.4 schema validator, and repository integrity checker passed. The repository checker covers module separation, prohibited proof mechanisms, artifact presence, catalogue membership, author spelling, and local links. The guide gives exact commands.

## Versions and review

The [source hash record](records/source-hashes.json) identifies the checked mathematical sources and proof inputs. Run `python3 verification/verify_hashes.py` to compare them.

[Software versions and immutable dependency references](records/versions.json) identify the verification environment. The Lean toolchain supplies all three proof checkers. The Python packages are pinned in [requirements.txt](requirements.txt).

GPT-6.1 Sol completed two mathematical and editorial review passes. The identified source, exposition, disclosure, and verification-record corrections were checked and applied. The referee inspected the final local records and approved publication with no blocking criticism. The [review report](review.md) gives the actual scope and limits. The official full-profile workflow and final public-clone audit are separate post-publication checks. Their commit-specific outcomes belong in the private delivery report.

No Zenodo deposit, Palomar submission, GitHub release, or tag is part of these checks.
