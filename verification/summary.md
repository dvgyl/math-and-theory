# Verification results

The collection has thirteen result families. The shared Lean 4.35.0 library covers seven families and 29 selected Comparator statements. Its build and axiom audit below passed on 27 October 2026. The six standalone study packages have separate verification records. The principal order-five and order-six Gyires claims, the all-order permutation-polynomial and four-block theorems, and the exceptional-vector theorem have Lean proofs. General Cauchy–Schwarz, permutation, dimension-constant, and direct-sum results also have Lean proofs. A further Lean theorem derives the circulant matrix inequality from explicit polynomial coefficient hypotheses. The separate order-six package proves all required coefficient hypotheses in that order. The [formal guide](../lean/docs/gyires-circulant-five.md) gives their exact scope. The principal order-seven and finite rank-two theorems remain incomplete in Lean.

## Shared Lean 4.35.0 library

The command `lake build MathAndTheory Solutions Challenges` passed with 2921 jobs. See the [build log](records/native-final-build.log).

The command `lake env lean Audit.lean` passed for 9196 declarations, including 8374 proposition-valued declarations. See the [axiom and type log](records/native-final-axiom-audit.log). These counts include generated supporting proofs. They do not count independent research results.

Every audited declaration uses only the permitted transitive axioms: `propext`, `Classical.choice`, and `Quot.sound`. The audit imports the substantive library and all Solution modules. It excludes the independent Challenge proof placeholders.

The [Comparator record](records/comparators.json) gives all 29 selected statement comparisons checked on 27 October 2026. All seven configurations passed Lean, NanoDa, and con-ron in [workflow 40452059102](https://github.com/dvgyl/math-and-theory/actions/runs/40452059102). The checked source commit is `34d14a9486ca951d6f4df5e736499fb4d5cf7687`. The record includes source hashes, artifact hashes, and checker hashes. It covers the four-block and exceptional-vector statements. This is a mechanical verification run, not a registry approval or peer review.

## Standalone Lean 4.19.0 packages

The [decision-tree covariance package](additional-proofs/readk-covariance/README.md) and [thermal kurtosis package](additional-proofs/thermal-kurtosis-counterexample/README.md) use Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Their source compilation, reproduction wrappers, and exact arithmetic checks passed on macOS ARM64 on 27 October 2026. Their verifier tests also passed.

The decision-tree record covers ten Lean source files and 29 exact axiom reports. These reports are separate from the shared library's 29 Comparator declarations. See its [source-check record](additional-proofs/readk-covariance/verification/source-checks.json), [axiom reports](additional-proofs/readk-covariance/verification/axioms.txt), and [verification scope](additional-proofs/readk-covariance/verification/report.md).

The thermal record covers its complete Lean source file and the two axiom reports printed by that source. See its [source-check record](additional-proofs/thermal-kurtosis-counterexample/source-checks.json), [compiler output](additional-proofs/thermal-kurtosis-counterexample/verification.log), and [verification scope](additional-proofs/thermal-kurtosis-counterexample/VERIFICATION.md). Both packages use only the permitted foundational axioms.

Both standalone packages passed fresh Linux checks in [workflow 40457472586](https://github.com/dvgyl/math-and-theory/actions/runs/40457472586). The checked source commit is `eac07aa986dbe577b7dc7a02661626a20bbda7ba`. The [Linux record](records/standalone-linux.json) gives all eleven proof-source hashes, the 31 requested axiom reports, wrapper hashes, and job links. Each package passed exact arithmetic and three verifier test methods. Source checks passed before and after each wrapper. Read-k dependency checks also passed before and after its wrapper. The thermal wrapper checked its Mathlib revision, tracked file state, and Lean version before compilation. All five workflow jobs passed, including the shared library, source integrity, and ten manuscript builds.

The decision-tree package proves covariance bounds and finite witnesses. It contains no Fourier-entropy theorem. The thermal package proves finite spectral statements. It does not formalize the stochastic long-time identification theorem. Neither package is covered by the shared-library Comparator run above. The package records retain the macOS checks; the separate Linux record gives the later run.

## Exact certificates

The full Gyires certificate run passed all 25 tasks. The orders-six and seven checks cover 180 chambers and 5,022,480 coefficient positions. The permutation-polynomial finite range covers orders 3–47, with 135 chambers and 224,550 coefficient positions. The rank-two certificate covers orders 2–15, with 33,607 profile intervals and 3,524,206 coefficient positions. The independent rational rank-two construction covers orders 2–6. An additional exact transfer run covers orders 3–93, with 273 chambers and 1,674,309 coefficient positions. It supplies the finite ranges for both alternative spectral bounds in the appendix.

The cubic deletion programs check all 120 primary chambers and all 720 sorting orders in the full independent construction. The order-five program checks all 120 weight orderings and 120,120 coefficient positions. The [certificate guide](../research-notes/gyires-complete-support/README.md) gives commands, mathematical roles, and coverage limits.

The programs return a nonzero exit code when a mathematical check fails or expected coverage is incomplete. Sampled reports cannot serve as exhaustive certificates. Programs that use assertions reject optimized Python execution. The failure tests also cover corrupt reports and invalid ranges.

These computations supplement the ordinary proofs. They do not provide Lean proofs of the matrix reductions or arbitrary-order statements.

## Files and documents

The [publication manifest](../publication-files.json) lists the public files. The [source hash record](records/source-hashes.json) identifies their exact contents. Run `python3 verification/verify_hashes.py` to compare them.

The [PDF record](records/pdfs.json) gives manuscript page counts and hashes. The [verification guide](README.md) gives commands for manuscript builds, source checks, metadata checks, and archive construction. Automatic checks run on pushes and pull requests. The full Palomar mechanical preflight remains manual.

The [software record](records/versions.json) identifies the Lean, Mathlib, and checking tools. The Python packages are pinned in [requirements.txt](requirements.txt). A check establishes only its stated scope. It does not establish novelty or peer review.

## Standalone study proofs

Six study packages use their own pinned Lean environments. Four packages cover the sharp Fourier bound, Galvin–Zhang domination counts, universal embezzlement, and asymmetric Tutte inequalities. Each package includes the manuscript, source files, license, citation, and source verification record. The source integrity checks compare published bytes and report coverage. Compiled objects are not included. Rebuild the package to reconstruct them.

Automatic jobs build each study and check every requested audit report. These jobs are separate from the shared Comparator selection. The order-six and permutation-polynomial Gyires packages have automatic source checks; their full source builds can be run with the manual workflow.
