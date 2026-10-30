# Common-summand cancellation for simultaneous matrix compression

This Lean project formalizes the actual cancellation theorem for an arbitrary family of rectangular matrices over an infinite field. It does not formalize or resolve the full Dodig–Stošić pencil perturbation conjecture. The relationship to that conjecture is recorded in the surrounding research manuscript. Formal correctness establishes neither novelty nor priority; the accompanying novelty review remains unresolved.

## Exact matrix theorem

Let `F` be any infinite field and let `I` be any index type, without a finiteness assumption. Let `m`, `n`, `p`, `q`, `u`, and `v` be finite index types, each allowed to be empty. Consider arbitrary families

\[
A_i\in F^{m\times n},\qquad B_i\in F^{p\times q},\qquad S_i\in F^{u\times v}.
\]

If fixed matrices

\[
P\in F^{(m+u)\times(p+u)},\qquad Q\in F^{(q+v)\times(n+v)}
\]

have full row rank and full column rank, respectively, and satisfy

\[
P\begin{pmatrix}B_i&0\\0&S_i\end{pmatrix}Q
=\begin{pmatrix}A_i&0\\0&S_i\end{pmatrix}\qquad(i\in I),
\]

then there are fixed matrices `P' : Matrix m p F` and `Q' : Matrix q n F`, of full row and full column rank respectively, satisfying `P' * B i * Q' = A i` for every `i`.

The main theorem is `MatCP1.matrix_common_summand_cancellation` in `MatCP1/MatrixCancellation.lean`. Its signature exposes the original `P`, `Q`, every rank and coefficient hypothesis, and the existential conclusion. Full row rank is represented by surjectivity of multiplication by a column vector; full column rank is represented by injectivity. These are the exact equivalent full-rank conditions over a field, including zero rows or zero columns.

`MatCP1.matrixJointCompression_common_summand_iff` also proves the equivalence: compression holds after adding a common rectangular summand if and only if it holds before adding it. The forward implication is the substantive cancellation argument; the reverse implication uses direct sums of the compression matrices with identity maps.

No hypothesis restricts the characteristic, the cardinality of `I`, or the row/column sizes beyond their explicit finiteness. In particular, `S` need not be square, regular, invertible, or a pencil.

## Reproduce verification

Pinned Lean: `leanprover/lean4:v4.35.0-rc3`.

Pinned mathlib: `0db6cb99b412983de54b59ecc1b0b2747542cda3`.

`lake-manifest.json` pins the transitive package revisions. With the pinned toolchain installed, initialize the dependencies and their cache, then run the verification script:

```sh
lake exe cache get
bash verify.sh
```

If Lake is not on `PATH`, set `MAT_C_LAKE` to its executable path. The verification script checks the actual mathlib checkout, deletes only this project's generated build directory, rebuilds every project proof file, prints the exact endpoint statements, and audits their axiom dependencies. It leaves the dependency cache intact.

Verification artifacts are `verification/environment.log`, `verification/build.log`, and `verification/axioms.log`. The allowed foundational dependencies reported for the endpoints are `propext`, `Classical.choice`, and `Quot.sound`; there are no project axioms, unproved placeholders, or native-decide proof dependencies. `AxiomAudit.lean` is the reproducible audit source.

## Proof structure

The proof first establishes that a linearly varying map is generically injective or surjective when it has the relevant rank at one parameter. This follows from a nonzero determinant polynomial after composing with a linear retraction or section. Only finitely many parameters are excluded.

A stable compression determines a two-vertex simultaneous subquotient diagram. At each vertex, let `(r,q)` be its injective map into the `B ⊕ S` side and `(p,s)` its surjective map onto the `A ⊕ S` side. The maps

\[
h_z=q+z(s-q)
\]

intertwine the entire `S` family. At `z=0`, `(r,h_z)` is injective. At `z=1`, `(p,h_z)` is surjective. A single scalar outside the union of the four finite exceptional sets gives the required two ranks at both vertices. Infinite `F` is used only to select this scalar.

The common kernels of these two intertwining maps form a simultaneous subrepresentation. They inject into `B` through `r` and surject onto `A` through `p`. Choosing a linear section of the source quotient and a linear retraction of the target inclusion produces the actual fixed compression maps. The final files convert between linear maps and literal `Matrix.fromBlocks` matrices by the standard sum-coordinate/product-coordinate equivalence.

See `CORRESPONDENCE.md` for the theorem-by-theorem match to the mathematical argument and the boundaries of the formalization.
