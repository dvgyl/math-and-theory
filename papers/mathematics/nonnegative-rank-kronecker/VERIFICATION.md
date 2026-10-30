# Verification

## Exact certificate

The order-11 witness is checked by two standard-library Python programs in exact rational arithmetic. From this directory:

```sh
python3 certificate/exact_certificate.py --verify-only certificate/C11_NMF109.json
python3 certificate/check_factorization.py certificate/C11_NMF109.json
```

The first reloads the stored matrices and checks the signs, the identity `L R = C_6 ⊗ C_6` in all 14,641 entries, the seed identities and the ordinary ranks; `python3 certificate/exact_certificate.py --output-dir DIR` regenerates the certificate from the construction. The second rebuilds `C_6` from its definition, compares it with the stored copy, checks the signs of both factors and every entry of `L R`, and computes `rank A = 3` and `rank C_6 = 10` by rational elimination. These checks give the upper bound 109 for the fixed witness; the lower bound `rank₊ C_6 = 11` over all real factorizations is proved in Lean.

## Lean

The project in [lean/](lean/) pins Lean `v4.35.0-rc3` (commit `470d5ce14007`) and Mathlib `0db6cb99b412983de54b59ecc1b0b2747542cda3`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then in `lean/`:

```sh
lake exe cache get
bash verify.sh
```

`verify.sh` checks the Mathlib revision, regenerates `AxiomAudit.lean`, removes this project's build output, rebuilds all 14 modules with Lake's local artifact cache disabled, prints the type and axiom dependencies of all 130 declarations defined in the project, and writes `VERIFICATION.json`. That last step fails if a module was not rebuilt, a declaration is missing from the audit, a source contains `sorry`, `admit`, `axiom` or `native_decide`, or any declaration depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.

`EntryNonneg M` is entrywise nonnegativity, `HasNMF M d` is the existence of a real nonnegative factorization with inner dimension `d`, and `nnrank M` is the least such `d`; `nnrank_le_iff` identifies the minimum with factorization existence. Rank is Mathlib's `Matrix.rank` over `ℝ` and `⊗ₖ` is Mathlib's Kronecker product. [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps every step of the proof to its declarations.

The fresh replay for this release is recorded in [verification/](verification/) and [lean/verification/](lean/verification/). The CI workflow repeats it on every push. Formal verification does not establish novelty or priority.
