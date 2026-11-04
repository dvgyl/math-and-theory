# Manuscript-to-Lean correspondence

This map concerns the full theorem in the manuscript (`../manuscript.tex`), not a finite numerical surrogate. All declaration names below are in the `MatCKronecker` namespace. The aggregate `MatCKronecker.lean` imports the complete dependency chain.

## Central statement

`exists_rational_counterexample_with_gap (k : ℕ)` produces

```lean
∃ C : Matrix (Fin (k + 11)) (Fin (k + 11)) ℝ,
  EntryNonneg C ∧ RationalEntries C ∧
  C.rank = k + 10 ∧ nnrank C = k + 11 ∧
  nnrank (C ⊗ₖ C) ≤ (k + 10) ^ 2 + 9 ∧
  nnrank (C ⊗ₖ C) + k < nnrank C * C.rank
```

No matrix rank, seed property, or factorization is an external hypothesis. The sole parameter is an arbitrary natural number, including zero. All constants and subsidiary rank statements are derived in the package. `counterexample_eleven` is the \(k=0\) specialization. `vandaele_gillis_glineur_tuyttens_conjecture_false` negates the source statement over every pair of finite rectangular dimensions and every entrywise nonnegative real matrix.

## Definitions and semantic checks

| Mathematical object | Lean definition or theorem | Meaning and edge cases |
|---|---|---|
| Entrywise nonnegative \(M\) | `EntryNonneg M` | Literally `∀ i j, 0 ≤ M i j`; no scoped positive-semidefinite matrix order. |
| Width-\(d\) nonnegative factorization | `HasNMF M d` | Existential real \(U,V\), inner index `Fin d`, both entrywise nonnegative, exact product equality. |
| \(r_+(M)\) | `nnrank M` | `Nat.find` of the actual factorization-width set. `exists_hasNMF` proves nonemptiness for every finite nonnegative matrix; `hasNMF_nnrank` proves attainment. The default zero on matrices with no factorization never enters the witness proof. |
| Minimum-width characterization | `nnrank_le_iff hM d` | `nnrank M ≤ d ↔ HasNMF M d`; includes padding and \(d=0\). |
| Ordinary real rank | `Matrix.rank` | Mathlib's dimension-based matrix rank, with `HasNMF.rank_le` and `rank_le_nnrank`. |
| Rational entries | `RationalEntries M` | `∀ i j, ∃ q : ℚ, (q : ℝ) = M i j`. Factorization rank is still minimized over all real factors. |
| Block witness | `witnessMatrix t` | Exact `fromBlocks seed 0 0 (smallBlock t)` with row/column index `Fin 4 ⊕ Option (Fin t)`. |
| Standard finite dimension | `finiteWitness k`, `witnessIndexEquiv k` | Reindexes \(t=k+6\) to `Fin (k+11)`; the transport preserves ranks and Kronecker factorizations. Its enumerating equivalence is noncanonical, which does not alter the asserted invariants. |

## Complete proof map

| Manuscript step | Source module | Declarations / precise role |
|---|---|---|
| Nonnegative rank as a true minimum; ordinary-rank lower bound | `NonnegativeRank.lean` | `exists_hasNMF`, `nnrank_le_of_hasNMF`, `hasNMF_nnrank`, `HasNMF.mono`, `nnrank_le_iff`, `rank_le_nnrank`. |
| Additivity on block diagonals | `BlockSum.lean` | `HasNMF.blockDiag_lower` splits arbitrary real nonnegative factors using cross-block zeros; `nnrank_fromBlocks` proves equality. |
| Ordinary-rank block additivity | `BlockRank.lean` | `rank_fromBlocks` proves the standard image/rank identity, with finite rectangular index types. |
| Product, sum and scalar factor constructions | `BasicFactorizations.lean` | `HasNMF.kronecker`, `HasNMF.add`, `HasNMF.smul`; all are actual factor matrices. |
| Four-block tensor-square decomposition | `BlockKronecker.lean` | `blockProductEquiv`, `blockDiag_kronecker_reindex`, `HasNMF.blockDiag_kronecker`, `HasNMF.kronecker_swap`; explicit equivalences, no presumed block identity. |
| Full rank of \(J_s+\epsilon I_s\) | `PositiveIdentity.lean` | `nearOneInverse`, `nearOneInverse_mul`, `rank_nearOne`, `nnrank_nearOne`; \(\epsilon>0\), arbitrary finite size including empty index types. |
| Exact \(A,U,V,R,T\) and ordinary rank 3 | `Seed.lean` | `seed_nonnegative_factorization`, `seed_rank_factorization`, `seedMinor_det`, `seed_rank`; determinant is exactly 4608. |
| Nonnegative rank of seed equals 4 | `SeedNonnegativeRank.lean` | `seed_not_hasNMF_three` is a pigeonhole obstruction to every real width-three factorization. Padding excludes all smaller widths; `seed_nnrank` combines both bounds. |
| Simplex identity | `SimplexFactorization.lean` | `simplex_factorization`: literal multiplication with an arbitrary finite intermediate type and nonzero \(\eta\). The specialized 18-coordinate lemmas are also compiled and audited, although the final family uses the uniform module. |
| Uniform factor nonnegativity | `SimplexUniform.lean` | `simplexLeft_nonneg_uniform`, `simplexRight_nonneg_uniform`: \(q>0\), entries bounded by 17 and 1, baseline at least 1/36 and 1/10, exact \(\eta=1/(840q)\), \(\epsilon=1/(33600q(q+1))\). The formal theorem requires nonnegativity; the manuscript's stronger elementary strict lower estimates are not needed by the central theorem. |
| \(WZ=I-J/(t+1)\), Kronecker rank factors | `CrossData.lean` | `contrast_factorization`, `cross_rank_factorization`, entry absolute bounds; `crossEpsilon`, `crossEta` and their positivity for \(t>0\). |
| Mixed width \(3t+4\) | `CrossFactors.lean` | `correctedTerm_hasNMF` gives width \(3t+1\), `other_hasNMF` gives the other three terms, `cross_factorization_identity` and `cross_hasNMF` establish the exact product for every \(t>0\). |
| Witness ranks and square bound | `Counterexample.lean` | `witness_rank`, `witness_nnrank`, `witness_square_hasNMF`, `witness_square_nnrank_le`; all for \(t>0\). |
| Rationality and all-\(k\) strict violation | `Counterexample.lean` | `witness_rational`, `exists_rational_counterexample_with_gap`, `counterexample_eleven`, `vandaele_gillis_glineur_tuyttens_conjecture_false`. |

## Index and certificate correspondence

The executable certificate uses coordinates \(0,\ldots,5,*\) for the seven-dimensional block. They correspond to Lean's `some i` and `none` in `Option (Fin 6)`. Pair indices are stored as \(11i+j\). The full matrix in that standard block order is the same explicit \(C_6\) as `witnessMatrix 6`, after this named index identification. The theorem's `finiteWitness 0` uses `Fintype.equivFinOfCardEq`, so the compiled existence witness may enumerate the same finite set in another order; the Lean proof explicitly carries the rank and factorization assertions through that equivalence. No numerical matrix is silently substituted for a different symbolic witness.

The Python certificate verifies \(L R=C_6\otimes C_6\) for all 14,641 entries. It does not determine the exact square nonnegative rank. The proof of \(r_+(C_6)=11\) over all real factorizations is the seed obstruction plus block additivity and full rank of \(B_6\), all proved in Lean. The rational generator is an additional check of the explicit fixed witness and its factors.

## Verification boundary

The pinned compiler and dependency hashes are in `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and `VERIFICATION.json`. The final pipeline requires all fourteen local modules (thirteen source modules and their aggregate) to occur as freshly built, then prints the types and transitive axiom closures of all 130 authored declarations, including all 96 theorems. Its parser checks the declaration list against the source list and verifies import reachability. The complete build and audit logs, rather than this prose description, are the execution evidence.

Standard foundational dependencies `propext`, `Classical.choice` and `Quot.sound` are allowed. No `sorry`, `admit`, custom axiom, `native_decide`, or hidden mathematical hypothesis is permitted. Lean verification establishes the stated mathematics relative to these foundations and the pinned compiler; it does not establish historical priority.
