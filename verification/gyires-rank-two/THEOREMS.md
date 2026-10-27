# Theorem map

The final statement is `MathAndTheory.Gyires.RankTwo.rank_two_complete` in [RangeComplete.lean](src/RangeComplete.lean). It assumes 2 ≤ n ≤ 5, doubly stochastic membership, and matrix rank at most two. It proves both Gram contractions, the A² contraction, the nonnegative Gyires margin, the normalized left Gram bound, the combined inequality, and its equality criterion. [RangeAudit.lean](src/RangeAudit.lean) expands the matrix statements and prints the final axiom report.

| Step | Source | Statement |
| --- | --- | --- |
| Actual rank-two representation | `StochasticRepresentation.lean` | The matrix is uniform, or it has the parameter form with 0<t<n. |
| Exact permanent expansion | `PermanentExpansion.lean`, `CenteredGram.lean`, `NormalizedPermanent.lean` | The formulas refer to the actual matrix permanent and Gram products. |
| Convex reduction | `ConvexLawMaximizer.lean`, `LawDeficitConnection.lean`, `ProfileReduction.lean` | Equal-interior parameter profiles suffice. |
| Complete profile coverage | `ProfileCoverage.lean`, `CertificateCoverage.lean` | Every admissible profile and overlap interval is included. |
| Polynomial evaluation | `ProfileRatios.lean`, `ProfileCertificateBound.lean` | The integer sign check implies the actual centered-matrix contraction. |
| Matrix join | `RankTwoContraction.lean`, `RankTwoConsequences.lean` | The finite checks imply the actual-rank matrix bounds. |
| Equality | `StrictGram.lean`, `RankTwoConsequences.lean` | A nonuniform matrix gives a strict permanent lower bound. |

The general-order join retains a finite-check hypothesis. The final theorem discharges that hypothesis for every order in the stated range. No larger range follows from this package.
