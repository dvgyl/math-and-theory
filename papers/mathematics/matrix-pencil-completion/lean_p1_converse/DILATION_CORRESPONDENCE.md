# Exact correspondence for the complete dilation theorem

This document specifies the correspondence between the manuscript `../manuscript.pdf` and the complete formal statement in `MatCP1Converse/DilationTheorem.lean`. Successful verification is recorded separately in `VERIFICATION.json`, `verification/build.log`, and `verification/axioms.log`. Neither this correspondence nor kernel correctness establishes novelty.

## The statement being formalized

For every infinite field F, every two same-size rectangular affine pencils A,B, every nonnegative integer k, and every distinct pair c,d in F,

    delta(A,B) <= k  iff  K_cd(A) is a constant full-rank compression
                          of K_cd(B) direct_sum (t-d) I_k.

The explicit block pencil is

    K_cd(A)(t) = [[A(t), 0, I_m],
                 [0,    0, (c-t) I_m],
                 [I_n, (d-t) I_n, 0]].

There are no hidden spectral, regularity, rank, chart, decomposition, factorization or nonempty-index hypotheses. The row and column index types are arbitrary finite types; `Fin k` supplies the added coordinates. Decidable equality is used for matrix identities and sums, and adds no mathematical restriction on finite types.

## Definitions are literal

| Mathematical object | Exact formal meaning |
|---|---|
| Affine pencil A0+tA1 | `Pencil F m n` is the pair `Matrix m n F × Matrix m n F`. |
| Normal rank | `Pencil.normalRank A` is `A.generic.rank`, where `generic` is `A0.map RatFunc.C + RatFunc.X • A1.map RatFunc.C`. The field is `RatFunc F`. |
| Constant strict equivalence | `Pencil.StrictEquivalent A B` quantifies constant matrices P,Pi,Q,Qi, all four two-sided inverse identities, and the simultaneous two-coefficient identity `transform P Q B = A`. |
| Minimum over both classes | `Pencil.BoundedDistance A B k` quantifies both A′ and B′ with those strict-equivalence witnesses and the actual normal-rank inequality. `orbitDistance` is `Nat.find` of the nonempty set of such bounds. `orbitDistance_le_iff` proves the exact minimum/bound equivalence. |
| Dilation | `matrixDilationConstant` and `matrixDilationLinear` are literal nested `Matrix.fromBlocks` expressions. `matrixDilationFamily` uses `false` for the constant coefficient and `true` for the linear coefficient. `Pencil.dilate` is their native coefficient pair. |
| Completion | `MatCP1.MatrixJointCompression` quantifies one P and one Q, surjectivity of `P.mulVec`, injectivity of `Q.mulVec`, and the product equality for every coefficient index. It does not quantify different P,Q at different parameter values. |
| Prescribed scalar summand | Its false coefficient is `-d • 1`, its true coefficient is `1`, hence exactly `(t-d) I_k`. |

The public endpoint `dilation_rank_distance_iff` exposes P and Q and the two individual coefficient equations instead of leaving the compression relation opaque. Its sizes are P:(2m+n)-by-(2m+n+k) and Q:(2n+m+k)-by-(2n+m). This is the literal row/column-completion relation in the manuscript.

## No difficult assertion is supplied as an extra hypothesis

| Manuscript step | Implemented endpoints and actual inputs |
|---|---|
| Common-summand cancellation | Sibling project `../lean_p1`: `matrixJointCompression_common_summand_iff` and `matrix_common_summand_cancellation`, arbitrary families and rectangular common block. The kernel/linking-family construction is proved. |
| Generic specialization | `Pencil.exists_rank_evaluation_eq`, from polynomial certificates obtained from the true rational rank-size factorization and identity compression. No favorable-point premise. |
| Rectangular normalization | `exists_rectangular_rank_normalization`, from actual rank and full-rank factors, with explicit inverse matrices. |
| Exact mixed-factor decomposition | `Pencil.exists_rank_mixed_factorization`, with only the arbitrary pencil and infinite field as inputs; returns a+b=normal rank and both coefficient identities. `normalized_pencil_all_moments` derives every vanishing moment from normal rank, and `normalized_pencil_mixed_factorization` constructs the reachable space. |
| Literal forward embedding | `matrix_dilation_compression_of_factorized_difference`; subsequent modules construct the two-step same-anchor compression and padding. |
| Universal anchor interchange | `dilation_anchor_swap_coefficients` and the matrix wrapper, with explicit mutually inverse constant maps. No spectral hypothesis. |
| Transport of representatives | `Pencil.strictEquivalent_dilate` and `Pencil.dilate_family_strictEquivalence`, using the displayed three-block constant multipliers. |
| Full forward implication | `matrix_dilation_completion_forward`, from actual `orbitDistance ≤ card x`, constructing all factors and representative transports internally. It does not require distinct anchors. |
| Fixed-factor extraction | `matrix_subpencil_extract_fixed_factor`, from the original constant compression matrices and evaluated-rank equality. It constructs the actual completion, border normalization, graph, inverse Schur block, correction, and equivalence. |
| Intrinsic complement contraction | `complement_common_coefficient_contraction_general` and `complement_orbitDistance_contraction`, from actual ranks, joint kernel/image conditions, and transparent data defining the actual complements. Common charts and factorization invariance are proved internally. |
| Dilation recovery | `matrix_dilation_complement_presentation`, `matrix_dilation_rank_at_d`, `matrix_dilation_rank_at_c`, and the joint injectivity/surjectivity lemmas. All hypotheses needed by the intrinsic contraction are derived from the literal dilation, not imported into the final theorem. |
| Actual parameter invariance | `normalRank_coefficientChange` and `orbitDistance_coefficientChange`, including the rational-function homomorphism and inverse coefficient transformation. |
| Full converse | `matrix_dilation_completion_converse`, with only original A0,A1,B0,B1, distinct anchors, and the literal compression as inputs. No complement-presentation premise remains. |
| Biconditional | `matrix_dilation_completion_iff`, its `Fin k` specialization `matrix_dilation_completion_iff_nat`, and the completely exposed `dilation_rank_distance_iff`. |

`ComplementPresentation` is a transparent record defining the construction: actual rank factorizations, injective/surjective maps, exact kernel/range equalities, and exact coefficient equations. It contains neither a contraction theorem nor an assumed correspondence with the original pencil. `RawDilationConverse.lean` constructs it explicitly for both pencils using `ForwardDilationRecoveryMatrix.lean` and constant ambient transport. This is why a supporting lemma with construction data as inputs does not weaken the final theorem.

## Edge-case and interpretation checks

All source, target, rank-factor, kernel and quotient spaces can be zero-dimensional. The actual final signature has no `Nonempty` hypothesis on matrix index types, no positive-rank assumption, and no positivity assumption on k. It works in every characteristic, including two. The only anchor hypothesis in the biconditional is `c ≠ d`. No norm, approximation, numerical tolerance, randomized certificate, selected numerical rank, or asymptotic quantifier appears.

Both representative matrices and all completion/equivalence witnesses lie in F. Rational-function matrices occur only in rank calculations. Constant matrix transport is proved separately; a rational left/right inverse is never accepted as a strict-equivalence witness. The scalar homogeneous factor in a parameter change is handled as a nonzero element of F(t), and the map on the rational-function field is constructed from transcendence.

The forward proof chooses representatives from the actual minimum and then transports the compression to the original A,B. The converse concludes the actual minimum after using two arbitrary prescribed complement coordinates. Thus neither side is limited to a favorable fixed representative.

## Boundary with the published barred formulation

The primary formal theorem is the explicit dilation equivalence above. The ordinary manuscript derives the source's Conjecture 1 using the previously published strong-block-minimal-bases eigenstructure identification and the formally proved cancellation theorem. This project does **not** formalize Kronecker classification, homogeneous elementary divisors, the bar/minimal-index definition, or the cited block-minimal-bases eigenstructure theorem. No claim that the exact barred statement has been checked by Lean is made.

The distinction is substantive. The raw theorem allows spectral anchors, for which the naive split into bar A and simple scalar blocks can fail. The formal proof bypasses that split through explicit kernel/quotient recovery. This document records a complete matrix theorem with its real hypotheses, rather than introducing an unproved bar correspondence as an assumption and presenting the conditional result as the original conjecture.

## Verification discipline

The project pins Lean `leanprover/lean4:v4.35.0-rc3`, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`, and mathlib commit `0db6cb99b412983de54b59ecc1b0b2747542cda3`. `verify.sh` cleans the local package outputs, rebuilds every exported local module, prints the exact central statements and definitions, audits every exported theorem, rejects proof placeholders or custom proof shortcuts, and generates a hash manifest only after success. It preserves dependency caches, which does not substitute for rebuilding this package's sources.

The permitted foundational dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`; the audit rejects any additional axiom dependency. No `sorry`, `admit`, custom `axiom`, or `native_decide` is permitted in the proof sources. Raising an elaboration heartbeat budget changes resource limits only, not the theorem, kernel or trust assumptions.

The final aggregate verification record is authoritative about successful commands, times, theorem counts and source hashes. Scoped logs are retained as provenance, not substituted for the aggregate result. Novelty remains a separate unresolved assessment; see the manuscript's section on prior work and limits.
