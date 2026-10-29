# Nonquasipolynomial power ranks

I prove the rank-thirteen main theorem and the companion family at every initial rank r >= 3. The main positive integer sequence is

    s(n) = 1 + 2^n + 3^n(1-2^n)^2 + n9^n(1+2^n)^3.

The recurrence rank is the least order of a monic complex recurrence with nonzero constant coefficient that holds at every sufficiently large index. The proof determines the minimal characteristic polynomial of every termwise power. It includes every repeated root and every coefficient cancellation. The minimal polynomials have integer coefficients, and their recurrences hold from index zero. Rational, real, and complex recurrence ranks agree.

For every positive M, the rank is P(M)-2Q(M), where

    P(M) = (M+1)(2M+1)(7M+6)/6,
    Q(M) = #{q in N : M < q^2 < 3M, q has parity opposite to M}.

The proof includes the exact floor formula for Q, the error bound

    |P(M)-rank(s^M)-(sqrt(3)-1)sqrt(M)| <= 2,

and failure of eventual quasipolynomiality even with real coefficients in the constituent polynomials. The zeroth power has characteristic polynomial T-1 and rank one.

For each r >= 3, the companion family has the literal form

    u(n) = 1 + 2^n + 2^(dn) + sum_i p_i^n,

where d >= 2 and the p_i are r-3 distinct odd primes. Its rank is r. Every termwise power has a minimal characteristic polynomial with simple positive integer roots. Its rank is

    choose(M+r-1,r-1) - (0 if M<d else choose(M-d+r-1,r-1)).

The package proves this formula for every M >= 0, the full minimal polynomial, integral recurrences from index zero, and equal recurrence ranks over rational, real, and complex coefficients. It constructs enough distinct odd primes for every r. Varying d gives infinitely many distinct power-rank profiles at each r.

The companion generating function, eventual polynomial degree and leading coefficient, and simplified rank-three examples retain their conventional proofs in the manuscript. They are outside the formal package. Formal verification does not establish historical novelty or interpret the undefined term “pseudo-polynomial” in the cited preprint.

## Reproduce

Install Python 3.11 or later and the Lean toolchain manager `elan`. Run these commands in this directory:

```sh
python3 check_package.py
lake exe cache get
python3 verify.py
```

The package pins Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The verifier builds all 35 source modules in a fresh directory. It uses `--trust=0`, rejects warnings and stale project outputs, and checks 25 final transitive axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Missing coverage or any failure returns a nonzero exit status. The verification result reports completion only after all checks pass.

Use `python3 verify.py --max-seconds 600` for a bounded work period. Use `python3 verify.py --resume` to continue after the saved source, dependency, compiler, object, and log hashes have been checked. Run `python3 -B test_verify.py` to test failure handling without starting Lean.

[THEOREMS.md](THEOREMS.md) maps the statements to their source modules. [sources.json](sources.json) records the complete source closure and hashes. [NOTICE](NOTICE) gives source credit. [LICENSE](LICENSE) contains the Apache License 2.0.

## Authorship

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex produced formal proofs and verification software for this package. I am responsible for publication.
