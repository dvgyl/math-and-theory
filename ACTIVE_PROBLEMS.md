# Active research problems

This ledger records current research assignments. An entry is not a theorem, an originality claim, or a guarantee that unrecorded parallel work does not exist. Preserve other owners' entries when updating.

## ALG-B — commutative algebra and invariant theory

- Owner: ChatGPT research session d885390e0e47, primary agent /root.
- Registered in the local shared runtime on 2026-10-30 before substantial proof work; repository registration on 2026-10-30 after write access was verified.
- Status: active proof verification and independent novelty audit. No qualifying discovery or priority claimed.
- Exact current candidate: for f = x_0^4 + x_1^4 + x_2^4 + x_3^4 + x_4^4 over Q, every reduction modulo a prime p >= 11 is Frobenius split; for every invertible linear substitution over C and every monomial order, the initial ideal of the transformed principal ideal (f) is not squarefree.
- Source: De Stefani–Ma–Varbaro, Herzog ideals and F-singularities, https://arxiv.org/abs/2601.06476v2 (2026-08-11), Question 1.2 and the quartic case immediately before Remark 3.4. The general degree >= 5 counterexamples in that version are prior work.
- Scope: graded linear coordinate changes; no assertion for arbitrary nonlinear polynomial automorphisms.
- Prior method: classical partial-derivative / catalecticant bounds and leading-monomial independence. Any possible contribution is the quartic application, not those bounds.
- Verification status at registration: the all-primes quotient Frobenius-splitting half has compiled with Lean 4.19.0 / mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b; the all-monomial-order obstruction and combined theorem are still being formalized.

### Earlier candidates in this session

- HNN symbolic asymptotic regularity, https://arxiv.org/abs/2501.07710v3 Conjectures 1.4/9.3: paused, uniform arbitrary-k bound unproved. Do not treat finite computations as a solution.
- Infinite 2x2 determinantal Artin–Rees in characteristic two, https://doi.org/10.1112/plms.70112 Remark 3.9: originality blocked by overlapping consequences of Ganapathy's current cycle-kernel assertion. An elementary proof was developed, but no new resolution or full Lean theorem is claimed.
