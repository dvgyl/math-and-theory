# Formal verification

The completed check proves the actual finite-matrix derivative interval and local branch existence. [FORMALIZATION.md](FORMALIZATION.md) maps the claims to exact declarations and states the conventional stochastic and sharpness boundaries.

The project pins Lean **4.19.0**, compiler commit `6caaee842e94`, and mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**. The complete Lake lock is in `proof/`. The verifier uses Python 3 and a Unix host for its process memory limit; the independent algebra check additionally uses SymPy 1.14.0.

After installing the pinned dependencies and their ordinary cache, run from the package root:

```sh
python3 verify.py --mathlib /path/to/mathlib4 \
  --lean-bin /path/to/lean-4.19.0-linux/bin --output verification-replay
python3 check_certificate.py
```

Choose a new output directory for each run. The verifier does not install software or access the network. If an incomplete dependency cache lacks an imported module, obtain its official cache or build that official module from the exact pinned source before replay.

The verifier assembles all 34 local modules from source into one Lean process. Its import path contains no task proof objects. It checks with `--trust=0`, one worker, and warnings as errors. The process has an 8 GiB address-space limit and a 600-second timeout. The check prints the public theorem contracts and the actual generator, tilt, and ratio definitions. It fingerprints the external dependency sources and objects before and after, and checks the local source hashes again after compilation.

The completed check returned exit code zero in 135.169 seconds, with zero compiler warnings or errors. All 83 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The 3,535 external dependency bindings and all local source hashes remained unchanged. See the [full manifest](verification/verification.json), [compiler output and theorem types](verification/UnicyclicAll.log), and [assembled source](verification/UnicyclicAll.lean.txt). No compiled project objects are distributed.

The verifier returns a nonzero status for a failed compilation, an unreported principal axiom check, a disallowed axiom, changed dependencies or sources, or incomplete local-module coverage. It rejects local `sorry`, `admit`, added axioms, `native_decide`, `unsafe`, `implemented_by`, `ofReduceBool`, `ofReduceNat`, and a skipped-kernel-check setting. A preflight failure resets the manifest to `all_passed=false`.

The independent exact algebra check expands all three integer certificates and the scalar reduction identities. It checks continuous interval coverage, not selected ring sizes. It rejects optimized Python so that assertions cannot disappear under `python -O`. The manuscript includes all 45 certificate coefficients and all three scales.

The formal proof does not establish bibliographic priority or expert validation. The long-time stochastic identification and the limiting sharpness family are conventional proofs in the manuscript, rather than Lean sample-path or optimizing-sequence theorems.
