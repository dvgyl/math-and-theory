# Extended q-permanent monotonicity

[Paper](../../preprints/q-permanent/paper.pdf) · [Computation](../../verification/q-permanent/README.md) · [Central verification](../../verification/README.md)

The result concerns real symmetric positive-definite matrices and parameters above one. It does not settle the real-symmetric Bapat–Lal assertion on `[-1,1]`.

## Source and definition fidelity

Da Fonseca's [2010 paper](https://doi.org/10.1016/j.laa.2009.10.036), Section 2, adopts the real positive-definite convention and states Conjecture 1. It uses a left endpoint at or below −1. The [2018 restatement](https://arxiv.org/abs/1804.02231v1), Conjecture 2, uses a left endpoint below −1. A decrease from 14 to 15 contradicts both versions.

The Challenge defines the inversion count and the sum over all permutations directly. It includes the explicit matrix. The isolated identity coordinates remain in the coordinate order when inversions are counted. The proof establishes their contribution; it does not delete them. Mathlib's positive-definite predicate supplies the matrix hypothesis.

## Principal correspondence

All substantive declarations below use namespace `MathAndTheory.QPermanent`.

| Paper content | Declaration |
|---|---|
| Explicit positive-definite witness | `counterexample_posDef` |
| Complete polynomial | `counterexample_polynomial` |
| Exact values at 14 and 15 | `counterexample_q14`, `counterexample_q15` |
| Source conjecture is false | `not_daFonseca_extended_conjecture` |
| Sparse-family identity | `qPermanent_family_formula` |
| Negative derivative at each real parameter above one | `exists_posDef_negative_qPermanent_derivative_ge_five` |
| Dense correlation examples | `exists_dense_correlation_negative_qPermanent_derivative` |
| Integer-entry examples | `exists_integer_posDef_negative_qPermanent_derivative` |

[Challenge](../Challenges/QPermanent.lean) and [Solution](../Solutions/QPermanent.lean) select five statements in namespace `QPermanentProblem`. The [configuration](../comparator/q-permanent.json) compares their exact types. Its matrix sum is definitionally equal to the library definition.

## Prior work

[Mitchell, 2020](https://files.ele-math.com/articles/oam-14-56.pdf) discusses positive semidefinite rank-one examples at negative parameters. That setting does not give the positive-definite examples above one proved here. [De Sá, 2015](https://www.mat.uc.pt/preprints/ps/p1519.pdf) identifies flawed tree expansion formulas. This proof uses a direct permutation enumeration and does not use those formulas.

[Kenta Kitamura's public formalization](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b) gives an order-144 complex Hermitian disproof on the Bapat–Lal parameter interval. Its real-symmetric case remains separate. The public MI-19 examples concern a subset-preserving permutation inequality on `[0,1]`; they do not establish the present monotonicity failure above one.

No claim of first priority is made.

The witness dimension is not claimed to be minimal. The integer-entry and correlation conclusions are separate. No integer correlation matrix is asserted. This preprint has not been peer reviewed.
