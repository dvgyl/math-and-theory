# Square-flower and book domination roots

I prove the sharp largest-root law for the actual graph formed by n squares sharing one vertex. For every n≥1 its largest root modulus satisfies

    R_n < 2 + sqrt(4n/W(4n)).

The positive real Lambert function W is defined by W(s) exp(W(s))=s and W(s)>0. The proof also gives

    4n/R_n² - log(4n) + log(log(4n)) → 0,
    R_n/(2sqrt(n/log n)) → 1.

The source closure proves the conclusions of all numbered results in the accompanying manuscript. It defines both finite simple graphs and their domination polynomials as sums over actual dominating vertex subsets. The polynomial formulas are proved from those definitions.

For square flowers, the package proves degree 3n+1, origin multiplicity n+1, exactly 2n nonzero complex roots with multiplicity, the complete finite root set, and its maximum modulus. It proves the full real-root classification, multiplicity-one simplicity of every nonzero real root, strict motion through even orders, endpoint limits, and the log(phi)/n and log(2)/n expansions with O(n^-2) errors, where phi=(1+sqrt(5))/2.

For books, it proves the formula for every n≥1, the separate n=0 single-edge formula, origin multiplicity two for n≥1, and the n=1 only-zero real-root exception. For even n≥2, one nonzero real root lies in (-3,-2) and one in (-1/2,0). For odd n≥3, exactly two distinct nonzero real roots lie in (-1/2,0). Each nonzero real root has multiplicity one in both the real and complex polynomial. The real root multiset has cardinality four for every n≥2.

Formal verification does not establish historical novelty or settle source correspondence. The package does not classify every complex root or assert simplicity of every complex root.

## Reproduce

Install Python 3.11 or later and the Lean toolchain manager `elan`. Run in this directory:

```sh
python3 check_package.py
lake exe cache get
python3 verify.py
```

The package pins Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The verifier builds all 70 source modules in a fresh directory. It uses one Lean process, `--trust=0`, warnings as errors, a 6 GiB memory limit, and a 180-second limit per module. It rejects stale project objects and checks 258 explicit statement types and final transitive axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. A failed or incomplete check returns a nonzero status.

Use `python3 verify.py --max-seconds 600` for a bounded work period. Use `python3 verify.py --resume` to continue after the saved source, dependency, compiler, object, and log hashes have been checked. Run `python3 -B test_verify.py` to test failure handling without starting Lean.

[THEOREMS.md](THEOREMS.md) maps the conclusions. [sources.json](sources.json) records the source closure and hashes. [NOTICE](NOTICE) gives source credit. [LICENSE](LICENSE) contains the Apache License 2.0.

## Authorship

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex contributed formal proofs and verification software. I am responsible for publication.
