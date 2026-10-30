# Active research problems

This ledger records current research assignments. An entry is not a theorem, an originality claim, or a guarantee that unrecorded parallel work does not exist. Preserve other owners' entries when updating.

## ALG-B — commutative algebra and invariant theory

- Owner: ChatGPT research session d885390e0e47, primary agent /root.
- Registered in the local shared runtime on 2026-10-30 before substantial proof work; repository registration on 2026-10-30 after write access was verified.
- Status: B10 ordinary proof independently reviewed; full Lean formalization remains incomplete. B06 is formally verified but not accepted under the exceptional-significance threshold. No qualifying discovery or priority claimed.
- Exact B06 statement: for f = x_0^4 + x_1^4 + x_2^4 + x_3^4 + x_4^4 over Q, every reduction modulo a prime p >= 11 is Frobenius split; for every invertible linear substitution over C and every monomial order, the initial ideal of the transformed principal ideal (f) is not squarefree.
- Source: De Stefani–Ma–Varbaro, Herzog ideals and F-singularities, https://arxiv.org/abs/2601.06476v2 (2026-08-11), Question 1.2 and the quartic case immediately before Remark 3.4. The general degree >= 5 counterexamples in that version are prior work.
- Scope: graded linear coordinate changes; no assertion for arbitrary nonlinear polynomial automorphisms.
- Prior method: classical partial-derivative / catalecticant bounds and leading-monomial independence. Any possible contribution is the quartic application, not those bounds.
- B06 verification update, 2026-10-30: the full quotient/GL5/all-monomial-orders theorem compiled, passed a fresh own-module build, and has only propext, Classical.choice and Quot.sound in its axiom closure. Two independent post-proof audits retain method overlap and unconfirmed exact-application priority; exceptional significance is not established.

### Earlier candidates in this session

- HNN symbolic asymptotic regularity, https://arxiv.org/abs/2501.07710v3 Conjectures 1.4/9.3: paused, uniform arbitrary-k bound unproved. Do not treat finite computations as a solution.
- Infinite 2x2 determinantal Artin–Rees in characteristic two, https://doi.org/10.1112/plms.70112 Remark 3.9: originality blocked by overlapping consequences of Ganapathy's current cycle-kernel assertion. An elementary proof was developed, but no new resolution or full Lean theorem is claimed.

### B10 current candidate — registered 2026-10-30

- Owner: same ALG-B session, /root; proof development /root/renewed_bottlenecks, independent proof adversary /root/artin_rees_proof, independent construction audit /root/novelty_constructions.
- Exact proposed theorem: for every ring of integers A of a number field and every finite subgroup G of GL_2(A), acting A-linearly on A[X,Y], the invariant ring A[X,Y]^G is Cohen–Macaulay.
- Source: Tony J. Puthenpurakal, The Cohen-Macaulay property of invariant rings over ring of integers of a global field, https://arxiv.org/abs/2402.08962v1, Conjecture 1.7 (2024-02-14). Strongest inspected predecessor: Part II https://arxiv.org/abs/2504.04746v1, Theorem 1.5 and Section 6, proves all sufficiently large BINARY Veronese subrings Cohen–Macaulay and the full ring generalized Cohen–Macaulay. Its journal DOI is 10.1007/s00031-025-09938-8, published 2025-11-18; full journal body remains inaccessible.
- Status update, 2026-10-30: a complete ordinary geometric proof candidate via Proj over a DVR, geometric integrality of the special fiber, reflexivity of ALL weighted twists, and all-degree cohomological torsion-freeness survived an independent mathematical review (no fatal gap found). Two separate novelty audits and a post-ordinary-proof search found no exact predecessor in the inspected sources, but priority and exceptional significance remain unresolved. Full Lean formalization is absent; the B06 formalization does not verify B10. This is an unresolved research handoff, not a claimed discovery. Local registration preceded the proof attempt.
- B10-DVR scope candidate registered 2026-10-30 12:38:16 UTC: for every discrete valuation ring O and every finite subgroup G of GL_2(O), the fixed ring O[X,Y]^G is Cohen–Macaulay; consequently the same conclusion for every Noetherian Dedekind domain A. Source/motivation: the B10 conjecture above and the proposed relative-Proj argument. This exact extension is under independent scope/equivalence audit before any separate substantial proof or formalization attempt. It is exploratory, not a proved or original result; no full Lean theorem exists.
- B10-DVR status update, 2026-10-30: the second independent internal mathematical review found no fatal gap and supports the same ordinary argument for every DVR and every Noetherian Dedekind domain, with the action linear on the two degree-one variables. It also gives direct Cohen–Macaulayness at every prime through finite locally free punctured charts. Two fresh novelty passes after the 12:44:16 UTC ordinary-scope cutoff found no exact predecessor in the inspected sources but confirmed substantial prior method overlap. Full Lean formalization and kernel audit are absent; journal/thesis coverage gaps, priority and exceptional significance remain unresolved. Status: reproducible research handoff, not a qualifying discovery.

## NT-C — algebraic number theory and local/global arithmetic

- Owner: ChatGPT research session 209b5caa3575, primary agent /root.
- Registered 2026-10-30 during the second research run, after reading this ledger, CONTENTS.md, catalogue.json and UNFINISHED.md at a847dc2c94d6bf350077d6d32de42973a1568be2.
- Status: seventeen new questions surveyed before selection. NT-C-DISC has a complete conventional proof but was set aside after adverse significance/overlap review. NT-C-PYTH is registered below before substantial proof work. No qualifying discovery is claimed.
- Scope: algebraic number theory and local/global arithmetic. Excludes ALG-B's binary integral invariant-ring question and all other existing completed or active results.
- Prior local result excluded from this search: for every algebraic totally real field K and positive-definite integral quadratic O_K-submodule L of finite-dimensional span, represented positive integer-unit squareclasses number at most dim_K(span_K L), without a classical or finite-generation hypothesis. Source: Daans–Kala–Man–Widmer–Yatsyna, https://arxiv.org/html/2409.11082v2, Theorem 3.2 and Question 3.4. Full embedded-module Lean theorem verified locally on 2026-10-30; historical novelty unresolved, no discovery/priority claim. This note coordinates scope; it does not publish or certify that result.
- Prior secondary candidate also excluded: Srimathy https://arxiv.org/html/2510.03603v2 Question 8.3, pseudo-perfect extensions and mod-p Milnor K2. Not a qualifying result and not fully formalized.
- No guarantee is made about unrecorded parallel sessions. Existing owners' entries are preserved.

### NT-C-DISC — registered 2026-10-30 before substantial proof

- Exact proposed theorem: for any number field K and finite extensions L1,L2 linearly disjoint over K in a common algebraic closure, equality O_(L1L2)=O_(L1)O_(L2) forces the relative discriminant ideals d(L1/K) and d(L2/K) to be coprime. Equivalently no nonzero prime of O_K ramifies in both extensions. The reverse implication is classical.
- Source: Sudesh Kaur Khanduja, Corrigendum to The discriminant of compositum of algebraic number fields, IJNT20(4)(2024)1191–1194, https://doi.org/10.1142/S1793042124500489, Theorem1.A and following paragraph, publisher first-page preview inspected. The 2019 proof is withdrawn; an exact 2018 valuation-ring claim still requires reconciliation. Full corrigendum beyond the preview has not yet been accessed.
- Initial proposed construction: square-zero elements in the two ramified reductions yield an integral element ab/pi outside their tensor order. This is only a proof outline and may reproduce a classical normality criterion.
- Owner: same NT-C session. Independent earlier-theorem audit: /root/discover_norms; independent code/construction audit: /root/discover_local; proof work: /root/discover_global and root.
- Status update, 2026-10-30: a complete conventional proof of the full relative number-field statement was independently checked. No Lean formalization was attempted. Earlier general tensor embedding-dimension results (Bouchiba–Kabbaj, arXiv:1701.05365, Theorem 5.1) give a short implication; Moody's 2017 draft also discloses a close differential-support construction, with scope problems. The 2020 and 2024 full corrigenda remain inaccessible. Historical verdict: overlapping/unresolved. This target was set aside because exceptional significance was not established; no qualifying discovery or priority claimed.

### NT-C-PYTH — registered 2026-10-30 before substantial proof

- Exact proposed theorem: for every infinite-degree totally real multiquadratic algebraic extension K of Q, the Pythagoras number of its full ring of algebraic integers O_K is infinite. Equivalently, for every natural m >= 1 there are x_0,...,x_m in O_K such that their sum of squares is not the sum of m squares in O_K. No finite-generation hypothesis on K and no restriction to prime radicands is intended.
- Source: Nicolas Daans, Stevan Gajović, Siu Hang Man and Pavlo Yatsyna, Pythagoras numbers for infinite algebraic fields, https://arxiv.org/html/2502.11222v2 (2026-02-26), introduction and Section 4; journal DOI https://doi.org/10.1007/s13163-026-00562-y. Theorem 1.1 and Remark 3.3 give important special cases; Remark 3.4 explains the obstruction from overlapping composite radicands.
- Owner: same NT-C session. Proof exploration: /root/discover_global and root; independent theorem-equivalence audit: /root/discover_norms; independent construction/code audit: /root/discover_local.
- Status: pre-proof live literature refresh in progress; no proof, no originality or priority claim. General arithmetic target retained at the user's exceptional-significance threshold.

- NT-C-PYTH scope refinement registered 2026-10-30: let F=Q(sqrt(n): n positive integer). Proposed substantial special case: every intermediate K with [F:K] finite satisfies P(O_K)=infinity. Stronger proposed criterion: if K is any subfield of F and a fixed positive squarefree q satisfies sqrt(qp) in K for infinitely many primes p congruent to1 modulo4, then P(O_K)=infinity. This includes the overlapping-prime field singled out in Remark3.4, but does not settle the full conjecture. A minimal-trace character-coefficient construction is under independent proof, novelty and significance review. No full Lean theorem or qualifying result is claimed.
