# Verification of the order-five Gyires result

The library proves the order-five circulant theorem only. It has ten principal declarations. The manuscript also maps its supporting statements to Lean declarations.

## Current checks

- The unmodified original source built on Lean 4.35.0 with Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The build completed with 2689 jobs. Only the ten intended Challenge declarations produced placeholder warnings.
- The original source axiom audit passed for all 94 listed statements and all 8035 library/Solution declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occurred. See `original-axiom-check.log`.
- The earlier Gyires migration snapshot source scan passed for its 172 Lean files. This is a family count, not the file count of the complete collection. It found ten Challenge placeholders and no other proof bypass token. See `source-scan.log`.
- The exact integer checker passed all 120 orderings. It checked 120,120 coefficient positions: 119,520 positive and 600 zero. It verified the sharp constant 484 and the witness `(1,1,0,0,0)`. See `coefficient-check.log` and `coefficient-results.json`.
- The manuscript compiled with the desktop LaTeX compiler and Tectonic. All 12 rendered pages were inspected. No clipping or missing mathematical glyphs was found. The final source must be recompiled after any later review edit.

The migrated collection build passed with 2686 jobs. The family axiom audit passed for all 94 listed statements and all 8035 declarations. It found only `propext`, `Classical.choice`, and `Quot.sound`. See `build.log`, `axiom-audit.log`, and `axiom-check.log`. The current collection Comparator passed all ten selected statements with Lean, NanoDa, and con-ron. See the [current Comparator log](../records/comparator-gyires-circulant-five.log). The original repository's old reports do not substitute for these checks.

## Reproduction

From `lean/`, run:

```sh
lake build +MathAndTheory.Mathematics.GyiresCirculant5.Main +Challenges.GyiresCirculant5 +Solutions.GyiresCirculant5
lake env lean -j1 ../verification/gyires-circulant-five/AxiomAudit.lean > ../verification/gyires-circulant-five/axiom-audit.log
python3 ../verification/gyires-circulant-five/check_axioms.py ../verification/gyires-circulant-five/axiom-audit.log
```

From the repository root, run:

```sh
python3 verification/gyires-circulant-five/scan_sources.py
python3 verification/gyires-circulant-five/check_coefficients.py --output verification/gyires-circulant-five/coefficient-results.json
```

The Python checker uses only the standard library. It reconstructs permanents from their permutation definition. It does not read Lean files or coefficient tables. Forward and inverse binomial transforms check the change to sorted gaps. Its finite coefficient calculation supplements the formal proof. It does not assert a Lean kernel result.

The original `historical_independent_checks.gp` is preserved for reproduction of the earlier PARI/GP checks. The current audit did not rerun that entire historical program.

`source-map.json` records the original and migrated source hashes. The migration changes only module paths, namespaces, and source notices. The original mathematical proof scripts are retained.

## Scope and review limits

The Challenge uses Mathlib's matrix, permanent, circulant, and doubly stochastic definitions. The opposite convention for circulant indices is handled by an explicit transpose theorem. The development covers nonnegative circulant matrices of exactly order five.

The coefficient counts and minimum-coefficient statistics are exact computational results. The principal inequalities, equality cases, and sharp margin are Lean theorems. The formal proof uses `ring` and `positivity`; it does not use `native_decide`.

The manuscript preserves the historical AI contribution record. The original reviewer wrote some files that it checked. No independent human expert or journal review is claimed. The collection's separate [GPT-6.1 Sol review](../review.md) passed after two review passes and inspection of the completed local checks.
