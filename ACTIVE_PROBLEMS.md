# Active research problems

This ledger records current research assignments. An entry is not a theorem, an originality claim, or a guarantee that unrecorded parallel work does not exist. Preserve other owners' entries when updating.

## ALG-B — commutative algebra and invariant theory

- Owner: ChatGPT research session d885390e0e47, primary agent /root.
- Registered in the local shared runtime on 2026-10-30 before substantial proof work; repository registration on 2026-10-30 after write access was verified.
- Status: B10 binary integral invariants under proof and novelty review; B06 formally verified but not accepted under the exceptional-significance threshold. No qualifying discovery or priority claimed.
- Exact current candidate: for f = x_0^4 + x_1^4 + x_2^4 + x_3^4 + x_4^4 over Q, every reduction modulo a prime p >= 11 is Frobenius split; for every invertible linear substitution over C and every monomial order, the initial ideal of the transformed principal ideal (f) is not squarefree.
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
- Source: Tony J. Puthenpurakal, The Cohen-Macaulay property of invariant rings over ring of integers of a global field, https://arxiv.org/abs/2402.08962v1, Conjecture 1.7 (2024-02-14); the 2025 Part II concerns ternary Veronese subrings and does not state this full conclusion in the inspected text.
- Status: proposed ordinary geometric proof via Proj over a DVR, geometric integrality of the special fiber, and reflexivity of weighted twists. Critical steps are under independent attack. No complete Lean formalization or novelty claim. Local registration preceded the proof attempt; this repository entry synchronizes that registration.
- Potentially stronger DVR formulations are exploratory and are not claimed as proved.

## NT-C — algebraic number theory and local/global arithmetic

- Owner: ChatGPT research session 209b5caa3575, primary agent /root.
- Registered 2026-10-30 during the second research run, after reading this ledger, CONTENTS.md, catalogue.json and UNFINISHED.md at a847dc2c94d6bf350077d6d32de42973a1568be2.
- Status: fresh discovery survey; no second-result candidate selected and no substantial proof started. Exact candidate statement and primary source will be recorded here before proof work.
- Scope: algebraic number theory and local/global arithmetic. Excludes ALG-B's binary integral invariant-ring question and all other existing completed or active results.
- Prior local result excluded from this search: for every algebraic totally real field K and positive-definite integral quadratic O_K-submodule L of finite-dimensional span, represented positive integer-unit squareclasses number at most dim_K(span_K L), without a classical or finite-generation hypothesis. Source: Daans–Kala–Man–Widmer–Yatsyna, https://arxiv.org/html/2409.11082v2, Theorem 3.2 and Question 3.4. Full embedded-module Lean theorem verified locally on 2026-10-30; historical novelty unresolved, no discovery/priority claim. This note coordinates scope; it does not publish or certify that result.
- Prior secondary candidate also excluded: Srimathy https://arxiv.org/html/2510.03603v2 Question 8.3, pseudo-perfect extensions and mod-p Milnor K2. Not a qualifying result and not fully formalized.
- No guarantee is made about unrecorded parallel sessions. Existing owners' entries are preserved.
