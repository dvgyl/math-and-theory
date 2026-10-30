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
- Potentially stronger DVR formulations are exploratory and are not claimed as proved.

## NT-C — algebraic number theory and local/global arithmetic

- Owner: ChatGPT research session 209b5caa3575, primary agent /root.
- Registered 2026-10-30 during the second research run, after reading this ledger, CONTENTS.md, catalogue.json and UNFINISHED.md at a847dc2c94d6bf350077d6d32de42973a1568be2.
- Status: at least twelve new questions surveyed before selection. NT-C-DISC registered below before substantial proof work; correctness and historical novelty are under independent review.
- Scope: algebraic number theory and local/global arithmetic. Excludes ALG-B's binary integral invariant-ring question and all other existing completed or active results.
- Prior local result excluded from this search: for every algebraic totally real field K and positive-definite integral quadratic O_K-submodule L of finite-dimensional span, represented positive integer-unit squareclasses number at most dim_K(span_K L), without a classical or finite-generation hypothesis. Source: Daans–Kala–Man–Widmer–Yatsyna, https://arxiv.org/html/2409.11082v2, Theorem 3.2 and Question 3.4. Full embedded-module Lean theorem verified locally on 2026-10-30; historical novelty unresolved, no discovery/priority claim. This note coordinates scope; it does not publish or certify that result.
- Prior secondary candidate also excluded: Srimathy https://arxiv.org/html/2510.03603v2 Question 8.3, pseudo-perfect extensions and mod-p Milnor K2. Not a qualifying result and not fully formalized.
- No guarantee is made about unrecorded parallel sessions. Existing owners' entries are preserved.

### NT-C-DISC — registered 2026-10-30 before substantial proof

- Exact proposed theorem: for any number field K and finite extensions L1,L2 linearly disjoint over K in a common algebraic closure, equality O_(L1L2)=O_(L1)O_(L2) forces the relative discriminant ideals d(L1/K) and d(L2/K) to be coprime. Equivalently no nonzero prime of O_K ramifies in both extensions. The reverse implication is classical.
- Source: Sudesh Kaur Khanduja, Corrigendum to The discriminant of compositum of algebraic number fields, IJNT20(4)(2024)1191–1194, https://doi.org/10.1142/S1793042124500489, Theorem1.A and following paragraph, publisher first-page preview inspected. The 2019 proof is withdrawn; an exact 2018 valuation-ring claim still requires reconciliation. Full corrigendum beyond the preview has not yet been accessed.
- Initial proposed construction: square-zero elements in the two ramified reductions yield an integral element ab/pi outside their tensor order. This is only a proof outline and may reproduce a classical normality criterion.
- Owner: same NT-C session. Independent earlier-theorem audit: /root/discover_norms; independent code/construction audit: /root/discover_local; proof work: /root/discover_global and root.
- Status: proposed, unverified, historical novelty unresolved. No qualifying discovery or priority claimed.
