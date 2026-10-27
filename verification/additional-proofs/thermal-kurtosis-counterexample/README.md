# Three-state thermal spectral kurtosis counterexample

Dev D. Goyal · [ORCID 0009-0009-9132-744X](https://orcid.org/0009-0009-9132-744X)

The complete result, proof, assumptions, and formal scope are in [the manuscript](report.pdf). The machine-checkable source is the single file `ThermalKurtosis.lean`.

## Result

The two-temperature rate model with row generator

```text
Q = [[-11, 10, 1], [20, -52, 32], [32, 1, -33]]
E = [0, 2, 1]
betaHot = log(2)/2
betaCold = 5*log(2)
```

has exact cold-heat spectral cumulant ratio

```text
C4/C2 = -3470947982622836/176627429595846691 < 0.
```

The hot bath acts on 0 <-> 1. The cold bath acts on 1 <-> 2 and 2 <-> 0. Every supported bath channel satisfies local detailed balance, and every total off-diagonal rate is positive.

The result refutes Eq. (19) of K. Ptaszyński, *Bounds on skewness and kurtosis of steady-state currents*, Physical Review E 106, 024119 (2022), in the tilted-generator spectral formulation specified in that paper. The [related-work summary](RELATED_WORK.md) compares this result with the cited models and cumulant bounds.

## Exact formal scope

The Lean source checks the finite matrices, complex eigenvalues, a four-times continuously differentiable local dominant real eigenvalue branch, and iterated real derivatives. It does not construct a sample-path probability space or prove the standard long-time probability-limit identification of the spectral function. It makes no empirical validation claim. The manuscript explains why this is the same finite spectral formulation of the proposed inequality.

The main theorem, which has no hypotheses, is:

```lean
ThermalCounterexample.thermal_kurtosis_counterexample
```

Strict dominance over every distinct eigenvalue is separately stated as:

```lean
ThermalCounterexample.scgf_strictly_dominant
```

The source has no admitted proofs, extra axiom declarations, or native-computation proof shortcuts. Its final commands print the foundational dependencies of the main theorem and the negative-ratio theorem. The expected dependencies are `propext`, `Classical.choice`, and `Quot.sound`, the standard Lean/Mathlib foundations.

## Reproduce the Lean check

Required versions:

- Lean **4.19.0**, official toolchain `leanprover/lean4:v4.19.0`.
- Mathlib commit **c44e0c8ee63ca166450922a373c7409c5d26b00b**, official tag `v4.19.0`.
- Python 3.9 or later for the optional independent arithmetic checker.

Install the official [elan toolchain manager](https://github.com/leanprover/elan) if Lean is not already installed. Then run:

```bash
git clone --depth 1 --branch v4.19.0 https://github.com/leanprover-community/mathlib4.git mathlib4
git -C mathlib4 rev-parse HEAD
```

The printed revision must equal the exact commit above. Mathlib's `lean-toolchain` file selects Lean 4.19.0.

From the Mathlib checkout, download the official cache for the proof's imports. This list avoids downloading unrelated parts of the library:

```bash
cd mathlib4
lake exe cache get \
  Mathlib/Analysis/SpecialFunctions/Log/Basic.lean \
  Mathlib/LinearAlgebra/Matrix/Adjugate.lean \
  Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean \
  Mathlib/LinearAlgebra/Eigenspace/Basic.lean \
  Mathlib/Analysis/Complex/Basic.lean \
  Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean \
  Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean \
  Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean \
  Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean \
  Mathlib/Analysis/Calculus/Deriv/Pow.lean \
  Mathlib/Tactic/Convert.lean \
  Mathlib/Tactic/FieldSimp.lean \
  Mathlib/Tactic/FinCases.lean \
  Mathlib/Tactic/FunProp.lean \
  Mathlib/Tactic/FunProp/ContDiff.lean \
  Mathlib/Tactic/Linarith.lean \
  Mathlib/Tactic/LinearCombination.lean \
  Mathlib/Tactic/NormNum.lean \
  Mathlib/Tactic/Push.lean \
  Mathlib/Tactic/Ring.lean
```

Check the entire proof with:

```bash
lake env lean /absolute/path/to/ThermalKurtosis.lean
```

Alternatively, check the toolchain, proof, and independent arithmetic together:

```bash
bash /absolute/path/to/verify.sh "$PWD"
```

Successful proof checking exits with status 0 and prints the two axiom-dependency lists. Warnings about tactic style, if present, are not proof admissions. The supplied `verification.log` records source compilation. `source-checks.json` records the source hash, toolchain, command, and exit status. The source file is sufficient; no prebuilt project-specific `.olean` file is needed or supplied.

## Independent arithmetic check

Run these commands from this package directory:

```bash
python3 model_check.py
python3 test_verifiers.py
```

This uses only the Python standard library. It checks exact fractions, a Laurent-polynomial determinant, and an independent recurrence obtained by differentiating the directly tilted eigenvector equation. It prints JSON; the recorded output is in `model_check_output.json`. It supplements Lean's analytic and spectral proof. The verifier regression suite checks valid inputs and mathematical, version, or source-integrity failures. Its three test methods contain multiple adversarial cases. Invalid evidence produces a nonzero exit status, including under optimized Python.

## Contents

- `ThermalKurtosis.lean`: the complete Lean proof.
- `report.pdf`: the research report and full ordinary proof.
- `report.tex`: editable typesetting source for the report.
- `README.md`: these instructions and exact formal scope.
- `verify.sh`: verification wrapper.
- `verification.log`: actual full-source Lean output.
- `model_check.py` and `model_check_output.json`: independent exact checker and output.
- `RELATED_WORK.md`: comparison with cited models and cumulant bounds.
- `VERIFICATION.md`: verification evidence and its scope.
- `source-checks.json`: source compilation record.
- `test_verifiers.py`: verifier regression tests.
- `CITATION.cff` and `CITATION.bib`: manuscript citation metadata.
- `manifest.json`: versions, verification status, and SHA-256 hashes.

To typeset the manuscript, run `tectonic report.tex`. Alternatively, run `pdflatex report.tex` twice with a TeX Live installation that includes AMS packages, Latin Modern, microtype, hyperref, fancyhdr, and enumitem.

## Boundaries of the claim

The witness does not settle the separate skewness conjecture, establish a minimal number of states, optimize a lower bound, or prove robustness to adding bath channels. The formalization does not include the long-time stochastic identification theorem or empirical validation. This package uses Lean 4.19.0; no compatibility with another Lean release is asserted. Negative fourth cumulants for arbitrary driven Markov currents and thermal three-level models themselves are prior art; the claimed contribution is this exact admissible thermal counterexample.

## Research and publication

This work is fully autonomous agentic research generated by AI systems. AI agents produced the mathematical arguments, formal proofs, computations, and manuscript. Dev D. Goyal is responsible for publication.

## Package integrity and license

[manifest.json](manifest.json) lists the SHA-256 hash of every release file except itself. The package uses the [Apache License 2.0](LICENSE).
