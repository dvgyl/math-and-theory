# Complete matrix-pencil dilation equivalence

This project formalizes the full explicit matrix theorem

\[
\delta(A,B)\le k
\quad\Longleftrightarrow\quad
K_{c,d}(A)\preceq K_{c,d}(B)\oplus(t-d)I_k
\]

for arbitrary same-size rectangular affine pencils over every infinite field, arbitrary nonnegative k, and distinct anchors c,d. The anchors may be spectral points. Every matrix dimension may be zero. Normal rank is the actual rank over `RatFunc F`; the distance is the actual minimum over both constant strict-equivalence classes; completion uses one constant full-row matrix and one constant full-column matrix for both coefficients.

Start with `MatCP1Converse/DilationTheorem.lean`, whose endpoint `MatCP1Converse.dilation_rank_distance_iff` exposes both completion matrices and both coefficient equations. The complete ordinary proof is in `../manuscript.pdf`. `DILATION_CORRESPONDENCE.md` checks every definition, quantifier, structural bridge, and edge case. The final actual build and axiom results are recorded in `VERIFICATION.json` and `verification/`.

The formal theorem is the explicit dilation statement. The manuscript's corollary in the original conjecture's barred/minimal-index notation uses a cited eigenstructure theorem that is not formalized here. Novelty remains **unresolved**, including three material missing full-text comparisons. No priority or qualifying-breakthrough claim follows from formal correctness.

The project includes the supporting components documented below and depends on the separately verified common-summand cancellation package at `../lean_p1`. Both directories are needed to reproduce the proof.

## Complete fixed-factor extraction endpoint

Let `F` be an infinite field, let `A(t)=A0+t A1` and `B(t)=B0+t B1` be same-size rectangular matrix pencils, and fix any `d : F`. Suppose fixed full-row and full-column matrices `P,Q` satisfy the two actual coefficient equations

\[
P\begin{pmatrix}B_0&0\\0&-dI_x\end{pmatrix}Q=A_0,
\qquad
P\begin{pmatrix}B_1&0\\0&I_x\end{pmatrix}Q=A_1,
\]

and suppose

\[
\operatorname{rank}_F(A_0+dA_1)=\operatorname{rank}_F(B_0+dB_1).
\]

The endpoint `MatCP1Converse.matrix_subpencil_extract_fixed_factor` produces a **constant** matrix `E` with `rank E ≤ x` and constant matrices `p,q` with explicit two-sided inverses, satisfying

\[
A_0+dE=pB_0q,\qquad A_1-E=pB_1q.
\]

It also states the full pencil identity for every parameter:

\[
A(t)-(t-d)E=pB(t)q\qquad\text{for all }t\in F.
\]

This starts from the original simultaneous-compression premise. The proof constructs the actual completion and its ambient constant equivalences, normalizes the evaluated border using the rank equality, derives the derivative-map rank bound, chooses the invertible border graph, applies constant Schur shears, and cancels the common scalar summand. These steps are proved inside the formalization. No derivative-rank estimate, favorable minor, normalized completion, or cancellation conclusion is assumed by this endpoint.

`matrix_completion_extract_fixed_factor` supplies the literal-matrix version when an actual strictly equivalent block completion and explicit inverse witnesses are already given. `completion_extract_fixed_factor` and `subpencil_extract_fixed_factor` state the corresponding finite-dimensional linear-map versions. Both coefficient identities are recorded, so the result does not rely on checking finitely many parameter evaluations. All finite row, column, and border index types may be empty, including `x=0`; every characteristic allowed by the infinite-field hypothesis is included.

## Complete static-compression endpoint

Let `F` be any field. Let `A0,A1` be `n × n` matrices, `X0,X1` be full-column `n × m` matrices, and `Y0,Y1` be full-row `p × n` matrices. For each `i`, choose a full-row matrix `Qi` and a full-column matrix `Ki` satisfying

\[
\ker Q_i=\operatorname{im}X_i,\qquad \operatorname{im}K_i=\ker Y_i.
\]

Set

\[
P_i(z)=Q_i(A_i+zI)K_i,
\qquad
\Delta=\begin{pmatrix}A_1-A_0&X_1-X_0\\Y_1-Y_0&0\end{pmatrix}.
\]

The endpoint `MatCP1Converse.static_compression_strict_equivalence_bound` constructs **constant invertible matrices** `L,R`, with explicit two-sided inverses, such that

\[
\operatorname{rank}_{F(z)}\bigl(LP_1(z)R-P_0(z)\bigr)
\leq\operatorname{rank}_F\Delta.
\]

The first representative `P0` stays fixed, and `Q1,K1` may be any prescribed valid quotient/kernel bases. The proof constructs the necessary ambient extensions; it does not assume the hard extension lemma, a factor-space decomposition, or the desired rank estimate.

The theorem uses actual `Matrix` expressions and `Pencil.normalRank`, defined as the rank of the corresponding matrix over `RatFunc F`. It therefore concerns normal rank at the transcendental parameter, rather than rank at selected numerical evaluations. All finite matrix index types may be empty. This theorem and the ambient extension lemmas work in every characteristic and even over finite fields. The simultaneous graph-chart, border-graph, and cancellation results explicitly assume an infinite field.

## Why the static estimate holds

The extension theorems produce constant invertible `S,T` and constant `D,W` with

\[
SX_0=X_1,\quad Y_1T=Y_0,\quad
S-I=(X_1-X_0)D,\quad T-I=W(Y_1-Y_0).
\]

They give the exact rectangular factorization

\[
(A_1+zI)T-S(A_0+zI)
=\begin{bmatrix}I&(A_1+zI)W\end{bmatrix}
\Delta
\begin{bmatrix}I\\-D(A_0+zI)\end{bmatrix}.
\]

Multiplying by `Q0 S⁻¹` and `K0` bounds the normal rank by the rank of the constant bordered matrix. The new matrices `Q0 S⁻¹` and `T K0` are proved to have the required full ranks and exact kernel/image. Finally, exact changes between quotient bases with the same kernel and kernel bases with the same image relate them to the prescribed `Q1,K1`. Thus the final equivalence matrices are constant, although the auxiliary rectangular matrices used only to establish the rank bound depend on `z`.

This direct factorization replaces the three-part factor-space decomposition in the earlier ordinary static-compression argument. Its formal proof is `static_displacement_factorization` in `StaticFactor.lean`.

## Other fully proved components

- `exists_nearby_automorphism`: if two embeddings into a finite-dimensional space agree modulo a subspace `U`, an ambient automorphism takes one to the other and induces the identity modulo `U`.
- `exists_nearby_surjection_factor`: if two surjections agree on `ker R`, an intertwining ambient automorphism has displacement factoring through the exact map `R`.
- `exists_embedding_matrix_extension` and `exists_surjection_matrix_extension`: literal matrix versions with two-sided inverse witnesses and factored displacement.
- `principalPivot_sub_factorization` and `principalPivot_sub_rank`: the actual block identity and exact rank preservation for differences under the specified principal-pivot transform.
- `pivot_compression_strict_equivalence_bound`: the actual normal-rank contraction in a common invertible pivot chart, for arbitrary prescribed valid quotient/kernel bases, with constant invertible left/right witnesses. It constructs the transformed full-rank maps internally and combines the static theorem with the principal-pivot rank identity.
- `exists_invertible_graph`, `exists_common_invertible_graph`, and `exists_common_invertible_cograph`: the relevant one-map and common two-map graph-chart choices, with all rank and field hypotheses explicit.
- `exists_full_rank_factorization` and `exists_common_rank_chart`: factorization through a space of the actual rank, with an injective and a surjective factor, followed by a common invertible chart for two maps whose ranks equal the chart dimension. The chart theorem assumes actual rank equalities and derives the factors and common chart.
- `exists_invertible_border_graph`: if a block map has rank at least the dimension of its added coordinates, actual source and target graph maps make its compressed border block invertible.
- `strict_common_summand_cancellation` and `familyStrictEquivalence_common_summand_iff`: actual constant strict-equivalence cancellation for arbitrary equal-size matrix families, with explicit inverse witnesses. These use the verified compression cancellation and finite-dimensional square full-rank equivalences; no Kronecker canonical form or uniqueness hypothesis is invoked.
- `linear_strict_common_summand_cancellation`: the same cancellation conclusion for arbitrary families of linear maps between finite-dimensional spaces, returning actual linear equivalences on the original source and target. This is the interface used by the completion extraction's linear-map Schur split.
- `jointCompression_exists_strict_completion`: a genuine full-row/full-column compression of an arbitrary family is realized as the actual upper-left corner of a strictly equivalent completion, with common constant ambient equivalences for the entire family. It derives the completion from the compression maps over any field.

The correspondence between the manuscript and the formal statements is in `DILATION_CORRESPONDENCE.md`.

## Reproducibility and audit

Pinned Lean: `leanprover/lean4:v4.35.0-rc3`.

Pinned mathlib: `0db6cb99b412983de54b59ecc1b0b2747542cda3`.

The complete transitive revisions are in `lake-manifest.json`, including the local path dependency `../lean_p1`. Retain both sibling project directories. Initialize their dependencies from their manifests with `lake build`, then run:

```sh
bash verify.sh
```

Set `MAT_C_LAKE` if Lake is not on `PATH`. The script checks the actual mathlib revision and the shared toolchain, cleans only `mat_c_p1_converse`, rebuilds every exported project module, prints the exact main theorem statements, and audits the endpoint dependencies. It preserves the separately verified cancellation project and dependency build caches.

The complete verification records are `verification/environment.log`, `verification/build.log`, and `verification/axioms.log`. The script audits every theorem declared in an exported project source module and checks that every module is rebuilt. The foundational dependencies are explicitly printed and are confined to `propext`, `Classical.choice`, and `Quot.sound`. There are no project axiom declarations, proof placeholders, or `native_decide` proof dependencies.

After those checks succeed, `make_verification_record.py` writes `VERIFICATION.json`, including the exact scope, pinned versions, rebuilt module list, printed actual statements, each theorem's axiom dependencies, and SHA-256 hashes of all project Lean sources, configurations, scripts, documentation, and verification logs. It also records hashes for the separately verified local cancellation dependency. No unused or unexported project source module is silently included in the successful record.
