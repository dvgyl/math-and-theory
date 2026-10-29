# Bounded-forcing recurrence inequalities

I prove a uniform inequality for arbitrary real sequences a and e. Assume

    a(12) > 1800,
    L(12) < a(13)/a(12) < U(12),
    (m+2)a(m) = m(2a(m-1)+3a(m-2)) + e(m),  m >= 14,
    |e(m)| <= 2,  m >= 14,

where

    L(n) = 3 - 9/(2(n+3)) + 9/(16(n+3)^2),
    U(n) = L(n) + 2/(n+3)^3.

For every integer n >= 12, the package proves

    a(n) > 8(n+3)^2,
    L(n) < a(n+1)/a(n) < U(n),
    a(n)a(n+2)^3 - a(n+1)^3a(n+3) > 800a(n)^4/(n+3)^3 > 0.

The errors can vary independently at every allowed index. The theorem imposes no sign pattern, integrality, or rationality condition on a or e. It requires no recurrence or error bound before index 14. The constant 800 is sufficient; no optimality is claimed.

The package also proves the scaled result. For every real B >= 0, replace the error bound by B and the size seed by a(12) > 900B. The growth bound becomes a(n) > 4B(n+3)^2. The quotient interval and quartic inequality stay the same. This includes B = 0, when the growth statement is positivity.

This is the robust-forcing theorem within the alternating-Motzkin result family. It does not formalize the full parameter family, the exact threshold tables, or the root-transfer results from the accompanying manuscript. It does not establish historical novelty.

## Reproduce

Use Linux, Python 3.11 or later, and the Lean toolchain manager `elan`. Run these commands in this directory:

```sh
python3 check_package.py
lake exe cache get
python3 verify.py
```

The package pins Lean 4.19.0 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The verifier builds all ten modules in a fresh directory. It uses `--trust=0`, one worker, a six-GiB process memory limit, warning-as-error and bounded compiler time. It rejects stale project objects and checks all 53 final transitive axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Incomplete coverage and every failed check return nonzero status.

Use `python3 verify.py --max-seconds 300` for a bounded work period. Use `python3 verify.py --resume` to continue after saved package, dependency, compiler, source, object and log hashes have been checked. Run `python3 -B test_verify.py` to test failure handling without starting Lean.

[THEOREMS.md](THEOREMS.md) maps the statements to their source modules. [sources.json](sources.json) lists the complete source closure and hashes. [NOTICE](NOTICE) gives source credit. [LICENSE](LICENSE) contains the Apache License 2.0.

## Authorship

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex produced formal proofs and verification software for this package. I am responsible for publication.
