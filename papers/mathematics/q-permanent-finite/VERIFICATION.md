# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the environment of the original development; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), a C++17 compiler and Python 3, then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/q-permanent-finite-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds `QPermanentResearch` and `QPermanentResearch.AxiomAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and runs the certificate checks below. `QPermanentResearch.AxiomAudit` enumerates every declaration whose defining module is one of the 32 project modules, including private and generated ones. Lean 4.19's code generator also stores auxiliary declarations (`_cstage1`, `_cstage2`, `_spec_k`, `_elambda_k`, `_closed_k`, `_boxed`) that may refer to its placeholder `lcProof`; the audit records them separately, allows them only those placeholders and other such auxiliaries, and requires every other declaration to be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. The checker also rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `Lean.ofReduceBool` and `axiom` in the sources and confirms that every named source declaration was audited.

`qPermanent` is the permutation sum with weight `q ^ inversionCount σ`, for a matrix indexed by `Fin n` in its given order; `qPermanentDerivative` is its derivative (`deriv_qPermanent`). `productFischerNorm` and `wedgeFischerNorm` are the factorial-weighted coefficient sums of the actual product and wedge polynomials. [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps the manuscript to the declarations. The concrete conclusions in [Witness896.lean](lean/QPermanentResearch/Witness896.lean) take the finite integer comparison as an explicit hypothesis; Lean does not evaluate it.

## Exact certificate

[certificate/verify_certificate.py](certificate/verify_certificate.py) uses only the Python standard library. Without options it checks the orbit-file hash and the row expansion, the coordinate cap, the two rank minors, the comparison `1000U > 1001·C(896,2)·per(B)` on the frozen integers, the residue record [crt_residues.json](certificate/crt_residues.json) (every modulus prime, their product above the a priori bound `C(n,2)·n!·Π B_ii`, and the Chinese-remainder reconstruction of `per(B)`, `U` and `T` equal to the frozen integers), the regularization parameters and the order-1024 alternative:

```sh
python3 certificate/verify_certificate.py
python3 certificate/verify_certificate.py --recompute --primes 4
python3 certificate/verify_certificate.py --recompute --primes all
```

`--recompute` compiles, in a temporary directory, the GMP program [exact_orbits.cpp](certificate/exact_orbits.cpp) and runs it on both witnesses, comparing every reported integer with the frozen reports, and the independent program [row_residues.cpp](certificate/row_residues.cpp) on the given number of recorded primes. The GMP program uses the bundled ABI binding [gmp_integer.hpp](certificate/gmp_integer.hpp) for 64-bit Linux, because GMP development headers are not assumed; it links `/lib/x86_64-linux-gnu/libgmp.so.10`. On one core the GMP run takes about a minute per witness and the residue program about five seconds per prime; `--primes all` repeats the whole record of 500 primes.

`row_residues.cpp` works from the actual row order only. It applies `f' = fℓ`, `S'_a = S_aℓ + v_a f` and `G'_{ab} = G_{ab}ℓ + v_b S_a − v_a S_b` for each new row form `ℓ = v·z`, and reports, modulo each prime, the Fischer norm of `f` and of each exponent-parity class of the three components of `G`. It does not use the four-row symmetry or the compressed recurrence of the manuscript, so it checks that derivation as well as the arithmetic.

## Scope

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit and a short certificate recomputation on every push. The explicit regularization and the asymptotic, spectral, random-order and coherent-ordering theorems are not formalized. Formal verification and exact computation do not establish novelty or priority.
