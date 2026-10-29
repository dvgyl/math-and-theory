# Formal verification

The checked statements are the actual-function upper bound, its radius corollary, and normalized actual-function attainment. [PROOF_MAP.md](PROOF_MAP.md) states the full hypotheses and the written rescaling limit.

The project pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It uses Python 3.10 or newer and a Unix host for the fresh verifier's process memory limit.

From `lean/`, install the pinned dependencies and obtain their ordinary cache:

```sh
lake update
lake exe cache get
```

Then rebuild every local module from source into a new directory:

```sh
python3 verify.py --lean "$(elan which lean)" \
  --mathlib .lake/packages/mathlib --entry THGStrong \
  --audit-theorem THGStrong.Sharpness.attain_rate \
  --timeout 300 --output ../verification-replay
```

Choose a new output directory for each run. The verifier does not install software or access the network. The preceding Lake commands do require network access. If a partial dependency cache lacks an imported module, build that official pinned Mathlib module before replay.

A successful replay requires exit code zero and `status: verified` in the new `verification.json`. The verifier clears inherited Lean search paths, copies only source files, rebuilds all 20 local modules in dependency order, and invokes Lean with `--trust=0`, one compiler thread, and warnings as errors. Each process has a 12 GiB address-space limit and the stated time limit. It separately prints the exact rate definition, actual-attainment contract, public theorem types, and transitive axioms. It fingerprints 2,319 source-resolvable external modules in the recorded run and checks that the external source/object fingerprints, local sources, and verifier remain unchanged.

The completed source-only replay accepted all 20 modules and the final audit with no compiler warnings. Each of the three public declarations depends only on `propext`, `Classical.choice`, and `Quot.sound`. See the portable [verification summary](verification/summary.json) and [theorem audit](verification/theorem-audit.txt). This is formal proof evidence; it does not establish bibliographic priority or expert validation.

No supplied project object is included or reused. The public proof package contains no project `.olean` files. The verifier rejects `sorry`, `admit`, added axioms, `native_decide`, `unsafe`, `implemented_by`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and a skipped-kernel-check setting in local proof source.

The general-L upper bound is formalized. The attainment theorem is normalized to L = R = 1; the manuscript proves rescaling for arbitrary L > 0 and R > 0.
