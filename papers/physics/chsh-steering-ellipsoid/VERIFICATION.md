# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), Python 3 with NumPy and SymPy ([requirements](scripts/requirements.txt)), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/chsh-steering-ellipsoid-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds the fifteen modules (warnings are errors) and `ProjectAxiomAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and runs the exact and quick numerical checks. `ProjectAxiomAudit` enumerates every declaration whose defining module is one of the fifteen project modules, including private and generated ones, and collects its axioms with `Lean.collectAxioms`. Lean 4.19's code generator stores auxiliary declarations (`_cstage1`, `_cstage2`, `_spec_k`, `_elambda_k`, `_closed_k`, `_boxed`) that may refer to its placeholder `lcProof`; the audit records them separately, allows them only such placeholders, and requires every other declaration to be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. The checker also rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `Lean.ofReduceBool` and `axiom` in the sources and confirms that every named source declaration was audited.

### Definitions and principal statements

- `CHSHPhysical.Density A`: `A` is Hermitian, has trace one and `0 ≤ Re(w* A w)` for every `w : Fin 4 → ℂ`.
- `CHSHPhysical.pauli`, `CHSHPhysical.tensor`: the standard Pauli matrices and the Kronecker product in the basis |00⟩, |01⟩, |10⟩, |11⟩, Alice first.
- `CertifiedCHSH.bell u u' v v'` is `spin u ⊗ spin (v + v') + spin u' ⊗ spin (v − v')`; `CertifiedCHSH.beta ρ` is the real supremum of `√(normSq (tr (ρ · bell u u' v v')))` over real unit vectors. No floor at 2 and no Horodecki formula.
- `CertifiedCHSH.physical_joint_chsh_attainment c r`: for `0 ≤ c ≤ 1` and `r² < 1`, with `a = √((1−c)(1−r²))`, `d = √(c(1−r²))`, the matrix `CHSHPhysical.state a d r` is a density matrix, `CHSHPhysical.centre a r = (0,0,c)`, Bob's length squared is `r²`, and `beta = 2√(1 + (1−2c)(1−r²))`. The centre is the formula `(a − T b)/(1 − |b|²)` applied to the vectors `alice`, `bob`, `T`, which `CHSHPhysical.alice_readout`, `bob_readout` and `correlation_readout` prove are the Pauli expectations of the matrix.
- `CHSHAxialWitness.beta_exact`, `BoundarySharpness.beta_exact`: the exact suprema for the axial witness and the sharpness family.
- `AxialCertificates.axial_exact_maximum`: the scalar maximum of the pairwise root sums of the axial Gram matrix over `−r ≤ z ≤ r`, equal to the envelope of the manuscript, with an attaining `z`.

The connection of `axial_exact_maximum` to arbitrary states with a given axial ellipsoid uses the filter-to-Gram correspondence and the Horodecki theorem, which are proved conventionally, not in Lean.

## Exact and numerical checks

```sh
python3 -I scripts/check_exact.py
python3 -I scripts/check_numeric.py          # full run, about 10 minutes
python3 -I scripts/check_numeric.py --quick  # about 3 minutes
```

[check_exact.py](scripts/check_exact.py) uses SymPy to check 46 identities exactly: the attaining family symbolically in `c` and `r`, the equality-proof block identities and their agreement with the Gram formula, the Gram formula on an explicitly filtered state, every identity of the axial proof, the axial witness, the sharpness family, the printed-direction countercertificate and the remaining explicit examples. [check_numeric.py](scripts/check_numeric.py) runs seeded NumPy searches for counterexamples; it computes CHSH from Pauli traces and whitening at the density-matrix level, and cross-checks the Horodecki value against direct Bell operators.

## Scope

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit and the exact checks on every push. Formal verification and exact computation do not establish novelty or priority.
