# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the environment of the original development. [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and Python 3 with the packages in [checks/requirements.txt](checks/requirements.txt). Then, from this directory, in a fresh copy of the package, run:

```sh
bash scripts/verify.sh /tmp/one-sided-f3-verification
```

The script downloads the Mathlib cache and refuses to run if the project already has build output. It builds the library `OneSidedF3`, whose roots are all 43 source modules and the audit module [AxiomAudit.lean](lean/AxiomAudit.lean). It then checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and runs the checks below.

`AxiomAudit` enumerates every declaration whose defining module is one of the 41 modules that define declarations (`FilteredF3` and `ExpandedF3` only import), including private and generated ones, and collects its transitive axioms with Lean's own collector. Lean 4.19's code generator also stores auxiliary declarations (`_cstage1`, `_cstage2`, `_spec_k`, `_elambda_k`, `_closed_k`, `_boxed`) that may refer to its placeholder `lcProof`. The audit records these separately and allows them only that placeholder and other such auxiliaries. Every other declaration must be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. The checker also rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool` and `axiom` in the sources. It confirms that every source module is a library root and that every named source declaration was audited.

### What the main theorem says

```lean
theorem FilteredF3.equation10_both_closed_forms (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsLUB (quantumF3AliceGLValues M) (Real.sqrt (quantumAliceExactValue M hM)) ∧
    IsLUB (quantumF3BobGLValues M) (Real.sqrt (quantumBobExactValue M hM))
```

- `Milne.CMatrix` is `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`, and `Milne.Density M` means `M.PosSemidef ∧ trace M = 1`. No rank hypothesis is made.
- `quantumF3AliceGLValues M` is the set of `Real.sqrt (correlationSq N)`, where `N = p⁻¹ • (onAlice F * M * onAlice Fᴴ)`, over complex `2×2` matrices `F` with `F.det ≠ 0` and success trace `p > 0`. Here `onAlice F` is `F ⊗ I`, and `correlationSq` is `Σᵢⱼ (Re tr(N (σᵢ ⊗ σⱼ)))²` with the standard Pauli matrices. The Bob set uses `I ⊗ F`.
- `quantumBobExactValue M hM` is `blochSq (partialA M)` if Bob's marginal is singular. Otherwise it is the spectral value of the canonical quadratic of the whitened state `canonicalize M hM`: the secular value at `max 0 ν`, where `ν` is the greatest real root of the explicit secular polynomial in mathlib's eigenvalues of a real symmetric `3×3` matrix. The existence of `ν` is proved. `quantumAliceExactValue` is the Bob value of the party-swapped matrix.

The right side contains no optimization over filters and no hypothesized optimizer or multiplier. It is the whitened-state form of the manuscript's formula. The rational Bloch-coordinate expressions for the ellipsoid data `(c, Q)` and the six-invariant rule are proved in the manuscript and checked by exact arithmetic, but they are not separate Lean theorems. The identification of `‖T‖_F` with the optimized steering value (Equation 3 of the source) is cited.

Beyond the main theorem, Lean proves the exact gap identity, root and optimizer existence for diagonal quadratics, the transfer to arbitrary real symmetric matrices, the singular-safe companion determinant, all maximizers, the extremizing filters and the invertible-attainment criterion. It also proves the rational violating-branch criterion in canonical coordinates and scalar lemmas used by the extensions. The success-probability frontier, the highest-success rule, continuity, the pure-state frontier, the conditional-purity bound and its equality family, the cluster interval, the separability corollary and the Galois obstruction are conventional proofs.

The 22 modules in [lean/QuantumPrior](lean/QuantumPrior/) are an attributed library adapted from the author's earlier steering-ellipsoid formalization. [PROVENANCE.json](lean/QuantumPrior/PROVENANCE.json) records their hashes and their relation to the [steering-bounds](../steering-bounds/) package.

## Checks

`python3 checks/run_checks.py --independent` copies [checks/](checks/) to a temporary directory. There it runs each program with `python3 -I`, adding only the program's own directory to the import path:

| Program | Kind | What it checks |
|---|---|---|
| `verify_galois_certificate.py` | exact, standard library | the integer sextic of the S₆ example, its factorizations modulo 17, 59 and 487, squarefreeness and irreducibility, and rational enclosures of the root and value |
| `verify_companion_exact.py` | exact (SymPy) | the companion determinant in dimensions 1–4 including singular shifts, the six-invariant compression and the singular derivative rule |
| `verify_exact_rational.py` | exact (SymPy) | 23 rational states, both parties and all pole orders 0–3, with exact branch selection by Sturm counts |
| `verify.py` | Float64 | 800 one-sided instances of ranks 1–4: fractional identity, whitening, ellipsoid shape, gap identity, recovered filters |
| `independent_check.py` | Float64 | a separate density-matrix implementation, 514 one-sided instances, 64 compared with constrained optimization |
| `extension_checks.py` | Float64 and exact fractions | probability-budget frontiers, optimal families and pure-state frontiers |
| `conditional_checks.py` | Float64 and SymPy | the conditional-purity bound, its equality families and collapsing states |
| `independent_bruteforce.py` | Float64 | written for this release: multistart search over all complex 2×2 filters directly on 4×4 states, 24 states of ranks 1–4, against a fresh implementation of the formula |

The recorded reports are the `*_results.json` files in [checks/](checks/). Floating-point checks detect errors; they are not proofs. The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit and the standard-library Galois certificate on every push. Formal verification does not establish novelty or priority.
