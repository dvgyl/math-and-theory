# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the environment of the [earlier package](../keller-klein/), whose 62 modules it imports; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. The upload was developed in this environment and is kept in it rather than ported to the repository's Lean 4.35.0 library. Install [Elan](https://github.com/leanprover/elan), then, in a fresh copy of the package, from `lean/`:

```sh
lake exe cache get
python3 verify.py --lean "$(lean --print-prefix)/bin/lean" --mathlib .lake/packages/mathlib --trust 0 --output /tmp/keller-klein-sharp-stability-verification
```

The verifier checks the dependency commits and clean worktrees, rejects `sorry`, `admit`, added axioms, `unsafe`, `opaque`, `native_decide`, `implemented_by`, `extern` and changes to kernel checking in all local sources, copies all 89 modules into a fresh directory and compiles them in dependency order with `-DautoImplicit=false -Ddebug.skipKernelTC=false`. It requires every `#print axioms` command of the new groups to produce an audit and every audited declaration, 144 distinct ones in all, to depend only on `propext`, `Classical.choice` and `Quot.sound`, and it writes `build.log`, `axioms.txt` and `certificate.json` to the output directory. `--trust 0` rechecks imported compiled objects as well; the default `--trust 1`, used in CI, kernel-checks every new declaration and trusts compiled imports.

| Directory | Modules | Content |
|---|---|---|
| [KellerKlein/](lean/KellerKlein/) | 62 | The earlier small-coefficient package, byte for byte, including three ports from CausalSmith ([provenance](third_party/causalsmith/UPSTREAM.txt)). |
| [support-gap/](lean/support-gap/) | 9 | Modules of the unpublished preceding package imported by the new development: the actual `supportGap` of a finite real vector (minimum of `|Σ bᵢεᵢ|` over the Boolean cube), its exact all-cap optimum `capGapFormula`, attainment and optimizer classification. 46 audits. |
| [stability/](lean/stability/) | 15 | The new deterministic development. 67 audits. |
| [attainment/](lean/attainment/) | 1 | The two-residual attaining family. 2 audits. |
| [bridge/](lean/bridge/) | 2 | The conditional probability bridge. 15 audits. |

Central declarations, all for actual coefficient vectors `Fin N → ℝ` with arbitrary signs and their actual `supportGap`:

- `Breakthrough.GlobalGapRigidity.signed_supportGap_inverse` and `..._equality_iff`: under `|bᵢ| ≤ a ≤ 1`, `Σ bᵢ² = 1` and `a < 2·supportGap b`, the derived core `gapCore` has odd size, the squared distance to the flat vector on it is at most `2 − 2√(1 − (a − g)²)`, and equality holds exactly when every core coefficient is `a`, at most one tail coefficient is nonzero and the tail sum is `a − g`.
- `Breakthrough.ActualGlobalGapStability.signed_supportGap_phase_stability` and `all_caps_supportGap_stability`: in the odd band derived from the cap by `oddBandIndex`, if `supportGap b > max(a/2, 1/√(n+4))`, there is a nonnegative normalized vector `v` with entries at most `a`, saturated or `(n+2)`-flat, at Euclidean distance at most `√(2+√2)·(capGapFormula n a − supportGap b)` from `|b|` padded by one zero, with `supportGap v = capGapFormula n a` at a tie or below the phase separation.
- `Breakthrough.ExactSaturatedModulus.actual_saturated_modulus`, `actual_saturated_modulus_equality_iff` and `Breakthrough.ActualSaturatedModulus.all_caps_exact_saturated_modulus`: the bound `F_r(e)` and its equality equivalence.
- `Breakthrough.ExactModulusAttainment.actual_exact_modulus_family`: explicit attaining vectors for every odd core and every `0 ≤ e ≤ (√2 − 1)r` with the high-gap condition.
- `Breakthrough.FixedFlatTradeoff.signed_supportGap_fixed_flat`: both fixed-flat inequalities. The equality shape of the trade-off is a written proof only.
- `Breakthrough.SharpStabilityExamples.actual_sharp_stability_witness` and `concrete_sharp_parameters`, and the examples in `GapRigidityExamples`: the optimal-constant witness `(a, t, t)` with feasible rational parameters, the saturated equality family and the even-core vector `(2, 1, 1, 1)/√7`.
- `Breakthrough.FourShiftEnvelope.actual_four_shift_envelope` (conditional): for the actual finite Rademacher law, the four-shift mixture, open and closed tail identities, residual normalization and cap, and the scalar envelope bound on the lower discrepancy. The Gaussian comparisons, the Hollom–Portier profile, the exponential estimate, the above-one tail estimate and additional open-tail bounds enter as named hypotheses. This is not a Lean proof of any probability cap optimum.

The fresh replay is recorded in [verification/](verification/); the CI workflow repeats the verifier on every push. The upload's own chained verifiers, which also replay all 49 modules of the preceding package, were rerun from fresh output as well; [verification/README.md](verification/README.md) summarizes that run.

## Certificates

The programs in [certificates/](certificates/) check the scalar inequalities of the probability proofs. Run them on a copy, since each writes its report beside itself.

```sh
python3 certificates/check_two_core_upper.py
python3 certificates/check_four_core_upper.py
python3 -m venv /tmp/flint && /tmp/flint/bin/pip install -r certificates/requirements.txt
/tmp/flint/bin/python certificates/verify_lower_exact_gap_arb.py 128
/tmp/flint/bin/python certificates/verify_lower_five_flat_arb.py B 128
/tmp/flint/bin/python certificates/verify_lower_five_flat_arb.py C 128
```

The first two use only exact rational arithmetic and the standard library. The interval verifiers read the `xz`-compressed bisection paths of the three partitions (13,666, 14,303 and 3 leaves), check exactly that they form complete dyadic prefix trees of total volume one, reconstruct every box with rational arithmetic, and require a strictly positive Arb enclosure of the margin of the four-shift envelope on every leaf with python-flint 0.9.0. Floating values in the partition files are never used. Compared with the upload, the verifiers differ only in reading the compressed partitions; the reports record the SHA-256 of the decompressed partitions, which equals that of the uploaded files. Each run takes about ten seconds.

The included reports are the 128-bit runs, with every leaf margin; the smallest margins are about `1.2·10⁻⁶`, `2.4·10⁻⁶` and `1.5·10⁻³`. The 192-bit runs (argument `192`) also pass on every leaf. They use the same partitions and the same Arb backend and differ only in working precision, so their reports are not included. The certificates prove the stated scalar inequalities only; the reductions to them, and the Keller–Klein, Hollom–Portier and Tomaszewski inputs, are outside them and outside Lean.

Formal verification and certificate checks do not establish novelty or priority.
