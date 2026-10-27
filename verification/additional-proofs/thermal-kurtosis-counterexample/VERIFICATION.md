# Verification scope and reproduction

The source compilation recorded in `source-checks.json` passed under Lean 4.19.0 with Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The record identifies the checked source by its SHA-256 hash. Compiler output is in `verification.log`.

## Formal result

`ThermalCounterexample.thermal_kurtosis_counterexample` has no hypotheses. It proves the stated rate conditions, local detailed balance, existence of a smooth dominant spectral branch, and the exact negative ratio. `ThermalCounterexample.scgf_strictly_dominant` states strict dominance over every distinct eigenvalue.

The source prints two transitive axiom reports. Their dependencies are contained in the standard set `propext`, `Classical.choice`, and `Quot.sound`. The source contains no admitted proofs, added axiom declarations, or native decision oracle.

The formalization uses the standard complex eigenvalue predicate and iterated real derivatives. It does not replace the spectrum or derivatives with assumed coefficient identities. It does not construct a trajectory probability space or formalize the long-time stochastic cumulant-generating-function theorem.

## Exact arithmetic

`model_check.py` uses Python's standard library and exact rational arithmetic. It checks the Laurent-polynomial determinant and independently differentiates the tilted eigenvector equation. Both calculations give the four cumulants stated in the manuscript. `model_check_output.json` records the output.

`test_verifiers.py` has three test methods with multiple adversarial cases. It checks valid evidence and failures in mathematical expectations, toolchain versions, or source integrity. Invalid evidence must produce a nonzero exit status, including under optimized Python.

## Reproduce

Follow `README.md` to obtain the pinned Mathlib checkout. Its Git revision must match the stated commit, and its tracked files must be unchanged. Run the wrapper with the path to that checkout. Then run the verifier tests from this package directory:

```bash
bash verify.sh /absolute/path/to/mathlib4
python3 test_verifiers.py
```

The wrapper also passed on macOS ARM64. It checked the dependency Git revision, unchanged tracked files, and compiler version, then compiled the source and ran the exact arithmetic checker. The source evidence records the successful commands.

The proof is for the specified finite spectral model. It does not establish literature priority or empirical validity.
