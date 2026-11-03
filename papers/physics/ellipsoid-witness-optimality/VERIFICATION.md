# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the environment of the original development; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and Python 3, then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/ellipsoid-witness-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, runs `lake build Main ProjectAxiomAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py), prints the 44 selected closures of [AxiomAudit.lean](lean/AxiomAudit.lean) and runs the exact checks below in a virtual environment.

[ProjectAxiomAudit.lean](lean/ProjectAxiomAudit.lean) enumerates every declaration whose defining module is one of the nine content modules (`EllipsoidCounterexample`, `SameChirality`, `ParametricFamily`, `ClassCComparison`, `NormalFormCertificates`, `MirrorComparison`, `GeometryCertificates`, `ProductVector`, `OptimalityReduction`), including private and generated ones, and collects its axioms with the utility behind `#print axioms`. Lean 4.19's code generator also stores auxiliary declarations (`_cstage1`, `_cstage2`, `_spec_k`, `_elambda_k`, `_closed_k`, `_boxed`) that may refer to its placeholder `lcProof`; the audit records them separately, allows them only those placeholders and other such auxiliaries, and requires every other declaration to be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. The checker also rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `Lean.ofReduceBool` and `axiom` in the sources, confirms that `Main.lean` only imports the nine modules and that every named source declaration was audited. The audit module and the checker were added for this release; the nine content modules, `Main.lean` and `AxiomAudit.lean` are the original sources, unchanged.

The definitions are faithful to the physics: `M4` is `Matrix (Fin 4) (Fin 4) ℂ` in the order `00, 01, 10, 11`; `State` is Hermitian, positive semidefinite for every complex vector and of trace one; `Witness` is Hermitian, trace one, nonnegative on every complex product vector and negative on some vector; `Finer V W` quantifies over all complex density matrices; `ClassD` requires both the operator and its partial transpose to be witnesses with negative determinants. [THEOREM_INDEX.md](THEOREM_INDEX.md) gives every definition and the declaration of each claim, and [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) separates unconditional, conditional and unformalized statements. In particular, `quantum_classification_given_structural_inputs` is conditional, and the theorems `counterexample` and `infinite_ClassD_counterexamples` state nonoptimality in the set of canonical witnesses inside the target, while `not_optimal_in_any_containing_set` and `parametric_not_optimal_in_any_containing_set` remove that restriction.

## Exact and numerical checks

[verification/requirements.txt](verification/requirements.txt) pins SymPy. From this directory:

```sh
python3 scripts/run_exact_checks.py
```

The runner copies [verification/](verification/) to a temporary directory and runs the four exact scripts there: [class_d_verify.py](verification/class_d_verify.py) (55 checks: spectra, determinants and refinement identities of the family, the rational counterexamples with their containment LMIs, the normal-form residual spectra and the rank-two transpose absorption), [new_results_verify.py](verification/new_results_verify.py) (104 checks: the sharp mirror interval, the universal separator, the robustness radius, the dual certificates of the convex program, the Class C examples, the volume-reversal family and the cross-orbit incomparable pair), [exact_sdp_certificates.py](verification/exact_sdp_certificates.py) (five primal–dual optima and two containment certificates, positivity by all principal minors) and [verify_mirror_formulas.py](verification/verify_mirror_formulas.py) (the four mirror and interior identities). It requires every check to pass and every regenerated report to equal the committed file byte for byte.

The numerical demonstration [solve_refinement.py](verification/solve_refinement.py) needs NumPy and CVXPY; `python3 verification/solve_refinement.py --output sdp.json` reproduces [sdp_examples.json](verification/sdp_examples.json) to solver tolerance. Its residuals and duality gaps are diagnostics, not proofs. [make_figures.py](verification/make_figures.py) needs Matplotlib and redraws the [figures](figures/) from exact formulas.

## Scope

The fresh replay for this release is recorded in [verification/replay/](verification/replay/). The CI workflow repeats the Lean build, the audit and the exact checks on every push. The general classification, the S-lemma converse and the structural inputs of the conditional assembly theorem are not formalized. Formal verification and exact computation do not establish novelty or priority.
