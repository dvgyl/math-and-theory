# Verification guide

The catalogue contains seven result families, seven manuscripts, and 21 selected Comparator statements. The [continuous Gyires preprint](../preprints/gyires-circulant-five/paper.pdf) combines the verified order-five result with the completed broader arguments. Those additions have a [separate ordinary-proof and certificate record](../research-notes/gyires-complete-support/README.md). They have no completed Lean verification or selected Comparator statement. Each family guide gives its mathematical scope and test limits. The central record gives the completed checks and their scope.

## Reproduce the formal checks

Install the toolchain named in `lean/lean-toolchain`. The project uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. From the repository root, run:

```sh
python3 lean/scripts/check-lean-sources.py
ruby lean/scripts/validate-formalization.rb lean/formalization.yaml
python3 verification/validate_metadata.py
cd lean
lake exe cache get
lake build MathAndTheory Solutions
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

The local verification VM permits Bubblewrap under its root account. No kernel security setting was disabled. Other installations can run the same command as an ordinary user when unprivileged namespaces are available. The local kernel executables come from the pinned toolchain. The [current full Palomar workflow](palomar.md) also checks protected Challenge provenance and uses an authenticated con-ron update. A local Comparator pass does not certify that workflow.

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

Each manuscript can be compiled from its directory with `tectonic paper.tex`. Compile the overview at the repository root with `tectonic overview.tex`. Tectonic runs the required bibliography passes. The recorded checks also inspect warnings, extract text, and render every PDF page for visual review.

Run `python3 verification/check_repository.py` to check local navigation, required artifacts, author spelling, prohibited proof mechanisms, and the correspondence between the catalogue and Comparator configurations.

## Records and limits

The [verification summary](summary.md) records the commands, software versions, source hashes, and results. The [two-pass GPT-6.1 Sol review](review.md) passed after correction of the identified issues and inspection of the final local records. AI review is not human expert peer review. No test result establishes historical priority. The family guides record the bounded prior-work evidence.

[Return to the catalogue](../CONTENTS.md).
