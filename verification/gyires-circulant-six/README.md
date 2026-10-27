# Order-six circulant certificates

I provide the formal sources and build instructions for the order-six circulant theorem here.

These sources prove the stated permanent inequalities for every nonnegative real weight vector of length six. The matrix entry in row `i` and column `j` is `w (j - i)`, with indices modulo six.

Install Lean through elan and use Python 3.11 or later. The verification script supports Linux and macOS. It uses the pinned Lean version in `lean-toolchain`.

From this directory, download the pinned package cache:

```sh
lake exe cache get
```

Then run the full verification:

```sh
python3 verify.py
```

The script checks every source hash. A fresh run rebuilds all 3,091 local modules. External package revisions must match the manifest. Each compiler uses one thread and a 4 GiB Lean allocation limit. The process-group memory limit is 5 GiB. A module stops after ten minutes.

The script removes inherited library search paths. It accepts only the pinned package and toolchain paths. Resumed records must match this path policy and the verifier hash.

The build directory can contain only outputs for the listed modules. The script rejects unlisted files and symbolic links. It checks the hashes of the Lean objects and intermediate-code files before reuse.

The default is one compiler. On a computer with sufficient memory, use `python3 verify.py --jobs 2`. The full run can take several hours. Allow space for the source files, package cache, and compiled objects.

To continue an interrupted run, use `python3 verify.py --resume`. The script checks source, object, dependency, compiler, and log hashes before it reuses a record.

The final result is `.verification/result.json`. Success requires `complete: true` and a zero exit code. Per-module records and compiler output are in `.verification/logs/`.

The source manifest has only relative paths. Its root is `SixTheoremChecks`. That module checks the matrix statements and reports the axioms of the main theorems. The expected axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.
