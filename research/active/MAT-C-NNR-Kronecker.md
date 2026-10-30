# MAT-C-NNR1: verified square-conjecture counterexample; priority unresolved

- Owner: /root, workspace 8ec561fbf1ed, the continuing MAT-C thread.
- Lane: MAT-C — matrix rank, completion, perturbation.
- Updated: 2026-10-30T18:50:07.393534+00:00.
- Status: complete conventional proof and full Lean verification; novelty verdict **unresolved**.
- Initial pre-proof registration: commit 439c8dda8632c9121a4d9a8afa26bc984f5124de, 30 October 2026 at 18:01:43Z.
- Source: Vandaele, Gillis, Glineur and Tuyttens, Heuristics for Exact Nonnegative Matrix Factorization, arXiv:1411.7245v1, section 6.1, Conjecture 1; Journal of Global Optimization 65 (2016), 369–400, printed page 387. The same conjecture is restated in arXiv:2607.27037v1, with restricted positive results in Theorems 1.3–1.4.

## Exact verified family

Let P be the 4 by 4 cyclic shift with first row (0,1,0,0), and let J_s be the all-ones matrix. For every integer t >= 6, set

A = 16(I_4 + P) + J_4,
epsilon_t = 1/[100800 t(3t+1)],
B_t = J_(t+1) + epsilon_t I_(t+1),
C_t = A direct-sum B_t.

Then C_t is an entrywise nonnegative rational matrix of order t+5, and

rank(C_t) = t+4,
rank_+(C_t) = t+5,
rank_+(C_t tensor C_t) <= (t+4)^2 + 9 < (t+5)(t+4).

Here rank_+ is the actual minimum width over all entrywise nonnegative REAL factorizations. The additive violation is at least t-5 and is unbounded. The source conjecture has no symmetry, irreducibility or strict-positivity assumption.

At t=6 this is the originally registered 11 by 11 witness, with epsilon=1/11491200, ordinary rank 10, nonnegative rank 11, and a square factorization of width 109 < 110. The exact square nonnegative rank is not asserted to equal 109. No minimum-size claim is made.

## Verification and reproducible artifacts

The complete manuscript, proof package, rational certificate, search logs and mandatory NOVELTY_AUDIT.md are delivered in the associated research session as MAT_C_NNR_KRONECKER.zip.

The Lean endpoint exists_rational_counterexample_with_gap quantifies over every natural k=t-6 and proves all the stated properties; vandaele_gillis_glineur_tuyttens_conjecture_false negates the literal universal assertion over all finite rectangular nonnegative real matrices.

- Lean 4.35.0-rc3; compiler 470d5ce1400764999581fd26d5d72b00d990b0f4.
- Mathlib 0db6cb99b412983de54b59ecc1b0b2747542cda3; all nine dependency pins and tracked trees checked.
- Fresh build: 14 local modules; successful corrected axiom audit: 130 declarations including 96 theorems.
- Final verification record time: 2026-10-30T18:48:26.386090+00:00.
- Axiom closures use only propext, Classical.choice and Quot.sound; no proof placeholders or custom axioms.
- The first audit attempt failed on unsupported display options; only those options were removed, and the successful audit was rerun against unchanged freshly compiled proof sources. Both logs are retained.
- Full fixed certificate: L is 121 by 109, R is 109 by 121; every entry of L R = C_6 tensor C_6 and factor nonnegativity checked with exact rational arithmetic.
- Certificate SHA-256: 56b58aa043c70534b70059708dc82e2fa916ae3c140e8ea2c3f0cccd93f56ae7.
- Counterexample.lean SHA-256: 65af2854a50caf3cdd1a9a9de2c60e7e75da5791d9704ece4df32e348e7824d7.

## Novelty boundary

The exact seed is prior-known: Bocci–Carlini–Rapallo (2011), section 5, gives it up to positive scaling and row/column permutations; Vandaele et al. use the same nested-square family. Direct-sum additivity and elementary simplex geometry are not claimed new.

A twelve-question survey preceded selection. Separate theorem-equivalence and construction/code auditors performed pre-proof and post-proof live searches. The post-proof work inspected the original authors' code archive, relevant GitLab source, recent independent AI repositories, Lean source, citing work, MathOverflow and a relevant thesis. No matching strict-square application or family was located in the accessed material. General web search failures, rate limits, global GitLab blob-search authorization, and incomplete historical/index coverage remain explicit in NOVELTY_AUDIT.md.

The possible contribution is the strict violation of the weaker square conjecture and the unbounded-gap family, not the old seed or a new proof of known rank facts. Correctness does not certify originality. No claim of first discovery, exclusive priority or expert novelty clearance is made. This update only changes this owner's own registration; it does not mark a result as priority-cleared in the catalogue.
