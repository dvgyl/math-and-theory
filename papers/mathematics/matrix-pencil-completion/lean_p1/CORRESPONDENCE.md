# Mathematical statement and Lean correspondence

The formal endpoint is common-summand cancellation for arbitrary simultaneous rectangular matrix families over infinite fields. The endpoint is not a generic-rank lemma, a single-matrix specialization, or a numerical check. The complete endpoint is printed by `AxiomAudit.lean` and recorded in `verification/axioms.log`.

| Mathematical step | Lean declaration | Exact content |
| --- | --- | --- |
| Fixed simultaneous compression | `JointCompression`, `MatrixJointCompression` | One common `P` and one common `Q` for all family members; `P` surjective, `Q` injective; every coefficient identity. |
| Generic full rank | `eventually_bijective_affine`, `eventually_injective_affine`, `eventually_surjective_affine` | The bad parameters of an affine family are contained in a finite set, provided one parameter has the claimed rank. |
| Simultaneous interpolation | `eventually_common_kernel_ranks` | Both ranks hold generically for the same `h_z = q + z • (s - q)`. |
| Common-kernel subrepresentation | `jointCompression_of_common_kernel` | The kernels inherit every family map; their restrictions inject into `B` and surject onto `A`. |
| Produce actual constant matrices | `jointCompression_of_subquotient` | A source section and target retraction yield explicit existential compression maps, with full rank and all coefficient identities. |
| Cancel the two-vertex diagram | `jointCompression_of_common_summand_diagram` | One scalar works at both vertices and for an arbitrary, potentially infinite family. |
| Apply to actual stable compression | `jointCompression_cancel_common_summand` | The linking representation is `T_i = (B_i.prodMap S_i).comp Q`, with source `VA × XS` and target `WB × YS`. |
| Reverse direction | `JointCompression.prodMap` | Extend the given compression maps by identity on the common summand. |
| Linear-map iff | `jointCompression_common_summand_iff` | Stable simultaneous compression is equivalent to unstabilized simultaneous compression. |
| Matrix-coordinate correspondence | `matrixJointCompression_iff_linear`, `block_mulVecLin_conj`, `prod_mulVecLin_conj`, `matrixJointCompression_blocks_iff_linear` | Literal matrix multiplication and literal `Matrix.fromBlocks` are equivalent to their linear-map versions. |
| Actual matrix iff | `matrixJointCompression_common_summand_iff` | The full matrix-family equivalence. |
| Fully exposed main endpoint | `matrix_common_summand_cancellation` | The exact matrices, ranks, universal coefficient equations, and existential unstabilized conclusion appear in its signature. |

## Quantifiers and edge cases

- `F` is an arbitrary field with `Infinite F`; no `CharZero` assumption occurs.
- `I` is an arbitrary type. Neither `Finite I` nor `Fintype I` is assumed.
- All six matrix row/column index types have `Fintype` instances. No nonemptiness assumption occurs, so every zero-dimensional case is included.
- The common summand has independent source and target types `v` and `u`; rectangular and singular summands are allowed.
- All matrices are arbitrary; the formalization assumes no canonical form, spectrum, polynomial pencil structure, or numerical genericity.
- The stable compression maps `P` and `Q` are fixed before the universal quantifier over family members. The resulting `P'` and `Q'` are also fixed before that quantifier.
- The generic parameter is chosen once. Intertwining of its kernel with each family member follows algebraically, so the proof does not intersect infinitely many rank-open sets.

## Stable-compression specialization

With the stable `P : WB × YS → WA × YS` and `Q : VA × XS → VB × XS`, the formal proof uses:

| Map | Source vertex | Target vertex |
| --- | --- | --- |
| `r` | `fst ∘ Q` | `fst` |
| `q` | `snd ∘ Q` | `snd` |
| `p` | `fst` | `fst ∘ P` |
| `s` | `snd` | `snd ∘ P` |

The stable identity is exactly what proves the `p` and `s` intertwining identities. The `r` and `q` identities follow directly from the block map. No unproved representation-theoretic cancellation result is invoked.

## Scope boundary

This project proves the supporting cancellation theorem. It does not prove the Kronecker canonical form reductions in the surrounding manuscript, and it does not prove the reverse implication of the full pencil perturbation conjecture. It makes no novelty claim. Those mathematical and priority questions are separate from kernel verification.

## Trust boundary

Every project theorem is proved in Lean against the pinned mathlib revision. There are no project axiom declarations, `sorry`, `admit`, or `native_decide` uses. Standard Lean/mathlib foundational axioms are explicitly enumerated in `verification/axioms.log`. The fresh build reuses the pinned dependency cache but deletes and recompiles all generated proof objects of this project. The dependency source revision and toolchain version are recorded in `verification/environment.log`.
