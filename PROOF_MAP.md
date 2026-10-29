# Mathematical claims and verification boundary

This map describes the original mathematical source. The current module-system port is uncompiled. Earlier verification records do not certify this candidate. The active Lake project is at the package root.

The recurrence coefficient field is complex numbers. The index set is `n ≥ 0`, and recurrences may initially hold on a tail. Rank zero and characteristic polynomial one are assigned to an eventually zero sequence. The constructed sequences are everywhere positive. Their minimal characteristic polynomials are monic integer polynomials with nonzero constant terms, and their recurrences hold for every index. Their minimal orders over Q, R, and C therefore agree.

The termwise zeroth power of either constructed sequence is the constant sequence one, with rank one and characteristic polynomial `T−1`. The main rank-13 formula is stated for positive powers. The companion family also includes power zero.

| Claim | Complete conventional proof |
|---|---|
| Rank and minimal polynomial of an exponential-polynomial sequence | Lemma 2, Section 2: shift operators and eventual independence |
| Positive rank-13 sequence | Theorem 1, equation (1), and its distinct-base expansion in Section 3 |
| Every power's complete minimal characteristic polynomial | Theorem 1 and Section 3: exact layer expansion, coefficient identities, and nonzero next-degree coefficients |
| Exactly one multiplicity loss at each exceptional position | Section 3.3: the square condition, modulo-three endpoint exclusion, and positive sixth-degree coefficient |
| Exact cubic-minus-square-count rank | Section 4: full multiplicity sum and parity-restricted square layers |
| Failure of eventual quasipolynomiality | Section 4: square-root correction on every residue class |
| Infinitely many power-rank sequences at each rank at least three | Theorem 4, Section 5: canonical monomial representatives and positive coefficients |
| Every companion power's minimal polynomial | Section 5, the displayed polynomial `χ_(r,d,M)`: product over distinct canonical bases |

The rank-13 example has four repeated characteristic roots. It is not a simple-root-only example. The family in Theorem 4 has distinct positive integer characteristic roots and uses no coefficient cancellation. Its Hilbert series is a standard principal-relation calculation.

The [formalization package](formalization/README.md) supplies proofs of the rank-thirteen main theorem, the companion-family theorem, and the exponential-polynomial rank principle. Its 35 source modules include an audit that requests 25 transitive axiom reports. It proves the exact main floor formula, both constructions' integral minimal polynomials, equal rational/real/complex eventual ranks, forward recurrences from index zero, and zeroth-power boundaries. The companion result includes every r >= 3, d >= 2, and M >= 0, the required odd-prime existence, and infinitely many distinct power-rank sequences at each r. [The formal statement map](formalization/THEOREMS.md) identifies each declaration. The companion generating function, eventual polynomial degree and leading coefficient, and rank-three examples retain their conventional proofs and are outside the formal package.

The Python programs retain the original arithmetic bodies and add an explicit rejection of optimized Python. A focused startup test checks that guard without running the arithmetic enumeration. The programs are finite corroborating checks. The included recorded run covers powers through 14 for the full coefficient expansion, and powers through three for direct modular recurrence comparison. It does not replace the universal proofs, establish external source correspondence, or certify novelty. The author-hosted primary text has now been checked separately: the companion contradicts its unnumbered fixed-rank finiteness conjecture as written, while the main nonquasipolynomial result is kept distinct from its undefined “pseudo-polynomial” terminology.
