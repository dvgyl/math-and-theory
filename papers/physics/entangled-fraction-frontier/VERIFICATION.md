# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.32.0` and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, the environment of the original development. [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and Python 3 with the packages in [analysis/requirements.txt](analysis/requirements.txt). Then, from this directory, in a fresh copy of the package, run:

```sh
bash scripts/verify.sh /tmp/entangled-fraction-frontier-verification
```

The script downloads the Mathlib cache and refuses to run if the project already has build output. It builds the library `MilneResearch`, whose roots are the six source modules, and the audit module [ProjectAxiomAudit.lean](lean/ProjectAxiomAudit.lean). It then checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and runs the checks below.

`ProjectAxiomAudit` enumerates every declaration whose defining module is one of the six modules, including private and generated ones, and collects its transitive axioms with Lean's own collector. Every declaration must be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. Under Lean 4.32 no code-generation auxiliaries are stored, so none is excluded. The checker also rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool` and `axiom` in the sources, and confirms that every named source declaration was audited.

The upload's own Lake configuration listed only three of the six modules as library roots. Lake 4.32 then rejects the imports of `MarginalRank` and `NilpotentTensor` ("unknown module prefix"), so its documented `lake build` fails. The committed [lakefile.toml](lean/lakefile.toml) lists all six modules; the sources are unchanged.

### What the main statements say

```lean
theorem MilneNew.Qubit.fef_frontier_standard (ρ : Joint) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (hb : vlen (blochB ρ) < 1) :
    fef ρ ≤ (Real.sqrt (1+vlen (blochB ρ)) +
      Real.sqrt (1-vlen (centre ρ)) * Real.sqrt (1-vlen (blochB ρ)))^2/4

theorem MilneNew.Qubit.frontier_sharp (c b : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∃ ρ : Joint, ρ.PosSemidef ∧ trace ρ = 1 ∧
      vlen (centre ρ) = c ∧ vlen (blochB ρ) = b ∧ fef ρ = frontierStandard c b

theorem MilneNew.Qubit.quantum_stability_coefficient_optimal_closed (c K : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hK : ∀ ρ : Joint, ρ.PosSemidef → trace ρ = 1 → vlen (centre ρ) = c →
      ((2-c)*vlen (blochB ρ)-c)^2 ≤ K * (1-c/2-fef ρ)) :
    MilneRefinement.stabilityConstant c ≤ K
```

- `Joint` is `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`; no rank, reality or canonicality hypothesis is made.
- `fef`, `centre`, `blochB` and `vlen` are the definitions of the Omega module: `fef ρ` is the real supremum of `Re ⟨e|ρ|e⟩` over unit vectors `e` whose two reduced states are `𝟙/2`; `blochB ρ j = Re tr(ρ(𝟙⊗σ_j))` with the standard Pauli matrices; `centre ρ` is `(a − Tb)/(1 − |b|²)`, or `a` when `|b| = 1`; `vlen` is the Euclidean length.
- `frontierStandard c b` is `(√(1+b) + √(1−c)·√(1−b))²/4`, and `MilneRefinement.stabilityConstant c` is `4(1+√(1−c))²`.

`MilneExpanded.quantum_overlap_bound` proves the prescribed-Schmidt bound for every positive semidefinite complex matrix on `ℂ^d ⊗ ℂ^d` and every vector, with the ordered marginal eigenvalues and Schmidt coefficients computed from the inputs. `MilneNew.Qubit.fef_singular_frontier` proves `fef ρ ≤ (1 + vlen (centre ρ))/4` when `|b| = 1`. The stability upper bound, the fixed-marginal reduction, optimizer complementarity (`OptimizerComplementarity.lean`), the marginal-rank inequality and the every-optimizer rank ceilings (`MarginalRank.lean`, `RectangularOptimizerRank.lean`), the qutrit pencil identities (`NilpotentTensor.lean`) and the density-matrix properties of the qutrit counterexample (`NilpotentState.lean`) are further Lean theorems. Appendix B of the manuscript lists the formal coverage section by section.

**Not formalized:** the local-unitary equality classifications, the general-dimension filtered canonical-spectrum bound (a written corollary of the formal prescribed-Schmidt bound), the saturation normal form and its Schmidt-number, partial-transpose, distillability, G-concurrence and quasidistillation consequences, low-rank optimizer existence, sharpness of the rank ceilings, the unique core and optimizer faces, compactness and SDP duality arguments, the quartic and the purity envelope as statements about states (Bravyi's theorem is used, not formalized), the physical reading of the filter frontier, the tensor laws, the negativity theorems and the asymptotic capacity formula.

**Third-party code.** The sections `LocalPrerequisites` and `Replay` of `AllProofs.lean` are the Omega Institute's proof of the known bound (commit `609e95e`, Apache License 2.0). `Replay` is the target file with its imports removed and three `#print axioms` commands appended; a comparison with the source at that commit (SHA-256 `12103d83…e3ab1d`) shows no other difference. See [lean/THIRD_PARTY_NOTICE.md](lean/THIRD_PARTY_NOTICE.md).

## Checks

`python3 -I scripts/run_checks.py` copies [analysis/](analysis/) and the independent checker to a temporary directory and runs each program there with `python3 -I`. Each checker exits with a nonzero status if one of its assertions fails.

| Programs | Kind | What they check |
|---|---|---|
| `verify_results.py`, `highdim_canonical_checks.py` | Float64, seeded | 20,000 two-qubit states of ranks 1–4 against the frontier, two independent FEF formulas, 3,006 sharp-family states, general-dimension bounds and attainers for `d = 2, …, 6`; the filtered canonical-spectrum bound in 40 cases with `d = 3, 4` |
| `symbolic_checks.py`, `geometry_checks.py`, `exact_expanded_certificates.py` | exact (SymPy) | trace, marginals, centre, correlations, characteristic polynomial and Bell overlap of the frontier states; the signed quartic; 40 expanded certificates |
| `check_expanded_results.py`, `verify_purity_envelope.py`, `dual_stability_checks.py` | Float64 and exact | the centre–purity envelope (40,000 canonical states, 180 constrained optimizations), duals, stability and filter-success cases |
| `core_uniqueness_checks.py`, `all_optimizer_rank_checks.py`, `low_rank_optimizer_checks.py`, `capacity_checks.py` | exact (SymPy) | the unique-core example, 55 rank cases, 45 low-rank cases, rectangular capacity primal–dual pairs |
| `saturation_checks.py`, `saturation_inertia_checks.py` | exact and Float64 | saturation fixtures, partial-transpose inertia and filters |
| `check_sdp_reduction.py`, `check_negativity.py` | SDP solver | full against reduced fixed-marginal optimization (16 instances); negativity transport against the quantum residual SDP |
| `tensor_entanglement_checks.py`, `collective_capacity_checks.py` | exact and Float64 | the qutrit counterexample and its nine-term ensemble, triangular determinant identities, finite-copy capacities and Chernoff certificates |
| `scripts/independent_check.py` | exact and Float64 | written separately from the checkers above: the frontier, deficit identity, saturators and stability constant on random states; the counterexample with SymPy; the capacity fixture against an SDP; the prescribed-Schmidt bound and the spectral cap in dimensions three and four, with attainment by the coherent-minimum state |

The recorded outputs are the `*.json` files in [analysis/](analysis/). The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build and the axiom audit on every push. Formal verification does not establish novelty or priority.
