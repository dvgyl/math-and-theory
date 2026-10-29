# An unbounded obstruction to projection AM–GM in Loewner order

This work is fully autonomous agentic research. Artificial intelligence systems generated the research, proofs, formalization, and manuscript. I, Dev D. Goyal, am responsible for publication. No expert validation or peer review is claimed.

I give three rational rank-one orthogonal projections in dimension three for which the average of the six ordered products exceeds the cube of their arithmetic mean in one direction. I also give a family that rules out every finite real multiplier of that cube. The mean is positive definite. Its condition number grows without bound along this family.

The result concerns the explicit unrestricted matrix comparison in [the paper](paper.pdf). It does not establish a counterexample to a coordinate-descent convergence rate or to the additional nonsingular block class in that application. I make no unconditional priority claim.

## Files and proof coverage

- [paper.pdf](paper.pdf) and [paper.tex](paper.tex): complete conventional proofs, source context, and limits.
- [Counterexample.lean](ProjectionAMGM/Counterexample.lean): actual real matrices, projection identities, and the negative quadratic form `-8/243`.
- [Family.lean](ProjectionAMGM/Family.lean): actual matrix family and failure for every real constant `C`.
- [Audit.lean](Audit.lean): endpoint types and transitive axiom reports.
- [verify_exact.py](verify_exact.py): supplementary exact rational calculation for the finite witness. It does not prove the universal theorem.

The principal Lean declarations are `ProjectionCounterexample.three_projection_counterexample` and `ProjectionFamily.no_finite_loewner_constant`. Both conclude failure of Mathlib's `Matrix.PosSemidef` predicate for the stated matrix difference. The definitions average all six permutation products.

The rank-one property, positive-definite mean, rational choices for every real `C`, and minimal number of factors have complete conventional proofs in the paper. These additional properties are not included in the Lean endpoint statements. The two-factor identity is standard background, credited to Recht and Ré.

## Reproduction

The pinned environment is Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Install Lean through elan, then run:

```sh
lake update
lake exe cache get
sh verify.sh
```

The verifier checks Lean 4.19.0, all nine locked dependency revisions, and the absence of tracked changes in those dependencies. It builds the two substantive matrix sources sequentially with trust level zero and warnings as errors, then checks Audit.lean. It requires each named axiom report exactly once and compares the full dependency source and object fingerprints before and after the build. The import-only aggregate file is not a separate proof check. The only permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. Each Lean process has a 900-second time limit and an 8 GiB address-space limit. The verifier requires a Unix-like system with Python's `resource` module.

Run `python3 verify.py --self-test` to check that missing, wrong, repeated, and unsafe axiom reports fail. The exact Python check also runs under `python3 -O`. A failed identity raises an exception and returns a nonzero exit status.

Build the manuscript with pdfLaTeX:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

## Citation and license

[CITATION.cff](CITATION.cff) describes the software and preferred article citation. [CITATION.bib](CITATION.bib) contains a BibTeX citation. The source and paper use the [Apache-2.0 license](LICENSE). Lean and Mathlib retain their own licenses. The paper credits Sun, Luo, and Ye for the motivating projection comparison and distinguishes the norm inequalities studied by Recht and Ré, Lai and Lim, and De Sa.
