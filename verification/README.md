# Verification guide

The catalogue contains thirteen result families and thirteen manuscripts. Seven families use the shared Lean 4.35.0 library, which has 29 selected Comparator statements. Six families use standalone packages pinned to Lean 4.19.0 or 4.32.1. The [Gyires preprint](../preprints/gyires-circulant-five/paper.pdf) contains the verified order-five, order-six, permutation-polynomial, four-block, and exceptional-vector results. Its other principal matrix and polynomial arguments have a [separate ordinary-proof and certificate record](../research-notes/gyires-complete-support/README.md). The principal order-seven and finite rank-two results remain incomplete in Lean. Each family guide gives its mathematical scope and test limits. The central record gives the completed checks and their scope.

## Reproduce the shared-library checks

Install the toolchain named in `lean/lean-toolchain`. The project uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. From the repository root, run:

```sh
python3 lean/scripts/check-lean-sources.py
ruby lean/scripts/validate-formalization.rb lean/formalization.yaml
python3 verification/validate_metadata.py
cd lean
lake exe cache get
lake build MathAndTheory Solutions Challenges
lake env lean Audit.lean
```

The source scan checks the module headers and file limits. The whole-library audit checks the transitive axioms of every loaded declaration in the substantive project and selected Solution namespaces. It follows all proof dependencies, including private helpers. Its type ascriptions and the selected Solution declarations check the principal types. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Comparator and independent kernels

Use Linux with Bubblewrap and the pinned Lean toolchain. From `lean/`, run each configuration:

```sh
ulimit -n 65536
for config in comparator/*.json; do
  bash scripts/verify-comparator.sh "$config"
done
```

The runner follows PalomarTemplate commit `2891de4c48955af824969a263d31b25e7a9a1406`. It adds the toolchain's bundled NanoDa and con-ron executables to a temporary configuration. This is the pinned template's local kernel registration. The submitted JSON files contain no `external_kernels` field or kernel exemption. The runner then invokes Comparator, which also uses Lean's kernel.

The file limit must permit Mathlib and the proof modules to load. A limit of 65,536 was used for the largest imports.

The Linux environment must permit Bubblewrap to create namespaces. The local checkers come from the pinned Lean toolchain. The [full Palomar workflow](palomar.md) also checks protected Challenge provenance and uses an authenticated con-ron update.

## Standalone Lean 4.19.0 packages

The two standalone packages use Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Follow each package's instructions in a separate working copy. Build output must not modify the committed package or its recorded evidence.

| Package | Proof and reproduction | Recorded verification | Formal limit |
|---|---|---|---|
| Decision-tree covariance | [README](additional-proofs/readk-covariance/README.md) | [Source checks](additional-proofs/readk-covariance/verification/source-checks.json) and [scope](additional-proofs/readk-covariance/verification/report.md) | No Fourier-entropy theorem. |
| Thermal current kurtosis | [README](additional-proofs/thermal-kurtosis-counterexample/README.md) | [Source checks](additional-proofs/thermal-kurtosis-counterexample/source-checks.json) and [scope](additional-proofs/thermal-kurtosis-counterexample/VERIFICATION.md) | No stochastic long-time identification theorem. |

The decision-tree package has ten Lean source files and 29 axiom reports. These are separate from the shared library's 29 Comparator declarations. The thermal package has one Lean proof file and two source-declared axiom reports. Both packages permit only `propext`, `Classical.choice`, and `Quot.sound`. Their stored source compilation and wrapper checks passed on macOS ARM64. Both packages also passed fresh Linux compilation, axiom checks, exact arithmetic, and verifier tests on 27 October 2026. The separate [Linux record](records/standalone-linux.json) identifies the checked commit and proof hashes. These are mechanical checks, with no external registry approval.

Run the standalone package and evidence checks from the repository root:

```sh
python3 verification/check_embedded_packages.py --arithmetic
```

This command checks package hashes, stored source evidence, axiom-report coverage, and exact arithmetic. It does not run Lean.

## Independent computations

Use Python 3 with the exact package versions in [requirements.txt](requirements.txt):

```sh
python3 -m venv .venv
.venv/bin/pip install -r verification/requirements.txt
.venv/bin/python verification/q-permanent/scripts/verify.py
.venv/bin/python verification/domirank-entropy/scripts/verify.py
.venv/bin/python verification/diagonal-concavity/scripts/verify.py
.venv/bin/python verification/hofstadter-iteration/scripts/verify.py
.venv/bin/python verification/alternating-motzkin/scripts/verify.py
.venv/bin/python verification/best-of-n/scripts/verify.py
.venv/bin/python verification/best-of-n/scripts/extension.py
.venv/bin/python verification/gyires-circulant-five/check_coefficients.py
```

These programs reconstruct finite examples or certificates. The family guides state their exact ranges. Floating-point values are diagnostics. Exact coefficient checks do not prove that a certificate covers a claimed matrix class; the formal proof must establish that link.

## Manuscripts and navigation

For the seven manuscripts under `preprints/`, run `tectonic paper.tex` from the paper directory. The standalone sources are `additional-proofs/readk-covariance/docs/manuscript.tex` and `additional-proofs/thermal-kurtosis-counterexample/report.tex`, relative to this guide. Compile them in working copies with Tectonic. Compile the overview at the repository root with `tectonic overview.tex`. Tectonic runs the required bibliography passes. The recorded checks also inspect warnings, extract text, and render every PDF page for visual review.

Run `python3 verification/check_manuscripts.py` to rebuild the overview and all nine catalogue manuscripts in temporary directories. It checks TeX warnings and compares extracted text with the committed PDFs.

Run `python3 verification/check_repository.py` to check local navigation, required artifacts, author spelling, prohibited proof mechanisms, and the catalogue entries, shared-library Comparator configurations, and standalone package paths.

## Automatic checks

The [automatic workflow](../.github/workflows/checks.yml) runs on pushes and pull requests. It checks source requirements, file hashes, metadata, certificate report coverage, checker failure handling, all nine manuscript builds, the overview, and the formal proof packages. It compares text from rebuilt PDFs with the committed PDFs. This comparison can detect stale text. It does not replace visual inspection.

The shared-library job builds `MathAndTheory`, `Solutions`, and the separate `Challenges` specifications. It then runs `Audit.lean` on the proved library. The Challenge proof placeholders are excluded from that audit. Two separate Linux jobs check the standalone packages with their pinned Lean 4.19.0 dependencies. They use temporary working copies and preserve the committed macOS evidence. The full [Palomar mechanical preflight](../.github/workflows/palomar-preflight.yml) remains manual and covers the shared library. The workflow configuration states which checks run; a successful result requires a completed workflow run.

## Records and limits

The [publication manifest](../publication-files.json) lists every public file. The [source manifest](records/source-hashes.json) records the SHA-256 hash of each file except itself. Run `python3 verification/verify_hashes.py` to compare them. The [software versions](records/versions.json) identify the recorded environment. A check establishes only its stated scope. It does not establish novelty or human peer review.

## Build archival packages

After an intended source change, update the explicit publication file list if needed. Inspect the listed files before recording their hashes:

```sh
python3 verification/update_hashes.py
python3 verification/verify_hashes.py
```

The hash update does not establish mathematical correctness. Run the checks required by the changed sources.

Run the following command after all verification checks pass. Use an output directory outside the source repository.

```sh
python3 verification/build_archives.py --output ../archival-packages
```

The builder includes only files in the explicit publication manifest. It rejects missing files, unlisted files, changed hashes, and symbolic links. It checks every ZIP member against its source bytes. The builder produces nine manuscript PDFs, nine full-collection ZIP files, and `packages.json`. Each ZIP includes both standalone packages as well as the manuscripts, shared formal library, exact checking programs, licenses, and verification scope.

[Return to the catalogue](../CONTENTS.md).

## Standalone study proofs

Six study packages use their own pinned Lean environments. Four packages cover the sharp Fourier bound, Galvin–Zhang domination counts, universal embezzlement, and asymmetric Tutte inequalities. Each package includes the manuscript, source files, license, citation, and source verification record. The source integrity checks compare published bytes and report coverage. Compiled objects are not included. Rebuild the package to reconstruct them.

Automatic jobs build each study and check every requested audit report. These jobs are separate from the shared Comparator selection. The order-six and permutation-polynomial Gyires packages have automatic source checks; their full source builds can be run with the manual workflow.
