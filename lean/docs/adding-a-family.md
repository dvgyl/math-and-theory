# Add a formally verified result family

This procedure applies to the selected formal statements. A manuscript must state the verification status of any broader results separately.

1. Choose a stable identifier for one coherent group of results.
2. Read the original source. State its hypotheses and conclusions exactly.
3. Check prior work, equivalent statements, and stronger known theorems. Record sources and access limits.
4. Complete the mathematical proof and its Lean formalization. Prove each required link between source definitions and formal definitions.
5. Add modules under `MathAndTheory/Mathematics`, `MathAndTheory/TheoreticalCS`, or `MathAndTheory/MathematicalPhysics`. Use the shared pinned Lake project.
6. Add an independent Challenge and a matching Solution. Keep the Challenge below 300 lines where practical. Add one Comparator configuration for the family.
7. Add a self-contained paper, bibliography, citation, and independent checking programs.
8. Update the catalogue, overview, metadata, axiom audit, and navigation.
9. Run the source, build, axiom, Comparator, independent-kernel, computation, manuscript, and link checks.
10. Obtain independent mathematical and editorial review. Resolve each blocking issue and repeat the affected checks before publication.

A known theorem can support a new result if it receives correct attribution. Do not present an incomplete mathematical argument as a proved result. Correct or withdraw false claims. State the scope and limits of the prior-work assessment.
