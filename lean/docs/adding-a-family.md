# Add a formally verified result family

A family is one coherent group of results. A manuscript must state the verification status of any broader results separately. The collection catalogue has one family list. Each entry identifies either a shared-library formalization (`comparator`) or a standalone package (`standalone`).

## Prepare the mathematics

1. Choose a stable family identifier.
2. Read the original source. State its hypotheses and conclusions exactly.
3. Check prior work, equivalent statements, and stronger known theorems. Record the supporting sources and limits of the comparison.
4. Complete the mathematical proof and its Lean formalization. Prove each required link between the source definitions and the formal definitions.
5. Prepare a self-contained manuscript, citations, and independent checking programs. State any result that remains outside the formalization.

## Use the shared library

Add modules under `MathAndTheory/Mathematics`, `MathAndTheory/TheoreticalCS`, or `MathAndTheory/MathematicalPhysics`. Use the shared pinned Lean 4.35.0 Lake project.

Add an independent Challenge and a matching Solution. Keep the Challenge below 300 lines where practical. Add one Comparator configuration for the family. Update the shared formalization metadata and axiom audit. Set the catalogue entry's formalization kind to `comparator`.

Run source validation, the library build, the axiom audit, Comparator, and the independent kernel checks. Challenge proof placeholders remain outside the proved library and its axiom audit.

## Preserve a standalone package

Use a standalone package when an established formalization requires a separate pinned environment. Place it under `verification/additional-proofs/<family-id>/`. Preserve its source files, relative paths, dependency pins, verification records, and complete file manifest. Set the catalogue entry's formalization kind to `standalone`.

Keep the manuscript and citation files in the package. Link to them from the collection; do not make duplicate copies under `preprints/`. The catalogue must identify the package root, manifest, and manuscript. The package manifest records its toolchain, Mathlib revision, file hashes, and formal scope.

Check exact manifest coverage, source evidence, theorem-report coverage, permitted axioms, and independent arithmetic. Test that incorrect mathematics or incomplete evidence produces failure. Add a separate automatic proof job that reproduces the package with its pinned dependencies. Run builds in temporary working copies. Do not replace committed verification records with generated output.

A successful standalone check does not add the family to the shared Comparator selection. A port to another Lean release requires its own source, proof, and scope checks.

## Complete collection checks

Update the catalogue, overview, navigation, publication file list, and integrity records. Build the overview and every catalogue manuscript. Check links, exact file coverage, archive contents, and checker failure handling. Inspect all changed PDF pages. Compare the manuscript statements and formulas with the verified sources.

Obtain independent mathematical and editorial review. Resolve each blocking issue and repeat affected checks before publication. Report only completed checks for the relevant source revision and environment. Mechanical verification is not external registry approval or peer review.

A known theorem can support a new result if it receives correct attribution. Do not present an incomplete argument as a proved result. Correct or withdraw false claims. Publication files should contain mathematical statements, sources, and reproducible evidence.
