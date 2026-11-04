# Reproduction and verification

This document distinguishes three activities: rebuilding the Lean proofs, independently checking finite rational certificates, and replaying the original research package. None of the Python results is used as an axiom or premise of a Lean theorem.

## 1. Pinned inputs

| Input | Pin |
|---|---|
| Original repository | `https://github.com/dvgyl/math-and-theory` |
| Original commit | `650a9782de75ab7f9eb16c2bcaf22c9b5e8b4d09` |
| Original package | `papers/mathematics/nonnegative-rank-kronecker` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc3` |
| Lean compiler commit | `470d5ce1400764999581fd26d5d72b00d990b0f4` |
| Mathlib commit | `0db6cb99b412983de54b59ecc1b0b2747542cda3` |
| Other Lean dependencies | Exact revisions in `lean/lake-manifest.json` |

The copied upstream Lean files are listed with hashes in `lean/verification/upstream-sources.json`. The verification script rejects modifications to those copies. The extension's own files reside in a separate directory.

## 2. Clean Lean setup

Use a normal Linux, macOS, or other Lean-supported environment with Git, Bash, Python 3, and `elan` available. The Python code uses the standard library; no numerical or optimization package is required. Install `elan` using the [Lean installation instructions](https://lean-lang.org/install/), then work in a fresh copy of this extension.

From `positive-core-extension/lean`:

```bash
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake update
lake exe cache get
bash verify.sh
```

The checked-in toolchain file selects the required compiler. `lake update` materializes dependencies; the fixed Mathlib revision and manifest determine their versions. `lake exe cache get` retrieves pinned dependency artifacts. The environment check verifies the actual Git revision of every dependency before accepting a build.

The verification script deletes **this project's** `.lake/build` before compiling every exported original and extension module. It disables reuse of project build artifacts. Mathlib and other dependency caches are retained. Thus the audit is a fresh build of all authored source, rather than a claim that Mathlib and Lean themselves were rebuilt from source.

Do not run `verify.sh` concurrently with another build of the same project: deletion of the project build directory is intentional. It does not remove source files or dependency checkouts. `POSITIVE_CORE_LAKE` can specify the path to the Lake executable if `lake` is not on the command path.

### What the script records

`lean/verify.sh`:

1. Records the compiler and Lake versions and checks the dependency revisions and upstream hashes.
2. Regenerates `AxiomAudit.lean` by enumerating every authored definition, theorem, lemma, and abbreviation.
3. Deletes `.lake/build` and builds both `MatCKronecker` and `PositiveCore` with project artifact-cache reuse disabled.
4. Prints the types and transitive axiom dependencies of every enumerated declaration.
5. Checks that all source modules are exported and freshly built, that every declaration was audited, and that the logs show successful completion.
6. Writes `lean/VERIFICATION.json`, including source and log hashes.

The audit rejects `sorry`, `admit`, custom `axiom` declarations, `native_decide`, `sorryAx`, and `Lean.ofReduceBool`. The permitted foundational dependencies are exactly Lean's usual `propext`, `Classical.choice`, and `Quot.sound`. Noncomputable definitions using ordinary classical mathematics are included in that audit.

**Final release record:** passed, with build and audit exit codes zero. `lean/VERIFICATION.json` records 30 freshly built authored modules and 267 audited declarations, including 206 theorems and lemmas. The original library accounts for 14 modules, 130 declarations, and 96 theorems and lemmas; the extension contributes 15 mathematical modules plus its aggregate, 137 declarations, and 110 theorems and lemmas. Every transitive proof closure is restricted to the three permitted standard foundations. The complete environment, build, and declaration-audit logs are retained in `lean/verification/`.

### Optional executable-path compatibility

The hosted Linux environment used for this work required a small optional compatibility shim because its process namespace exposed an executable path inconsistently. The shim rewrites that executable-path lookup to `/proc/self/exe`. Its source, when included, is `lean/verification/lean_app_path_compat.c`.

The shim does not change Lean's parser, elaborator, evaluator, proof terms, or kernel. A normal installation should use the commands above without it. The recorded run used the shim, as explicitly recorded by `executable_path_compatibility_shim_used` in `lean/VERIFICATION.json`. It is not a mathematical assumption or a required dependency of the project.

## 3. Exact activation certificates

The saved certificates use the circulant seed with first row `(29,29,11,11)/20` and `B_s=J_s+εI_s`.

| Certificate | `s` | Exact `ε` | Left/right dimensions | Product's exact nonnegative rank |
|---|---:|---:|---|---:|
| `activation_s2.json` | 2 | `1/238032` | `8×6`, `6×8` | 6 |
| `activation_s3.json` | 3 | `1/1904256` | `12×9`, `9×12` | 9 |
| `activation_s5.json` | 5 | `1/15234048` | `20×15`, `15×20` | 15 |

Run from `positive-core-extension`:

```bash
python3 computations/check_certificate.py \
  certificates/activation_s2.json \
  certificates/activation_s3.json \
  certificates/activation_s5.json
```

`check_certificate.py` is independent of the generator: it does not import `generate.py`. It parses canonical rational strings with `fractions.Fraction`, reconstructs the seed and auxiliary matrix from their definitions, checks every entry of `LR=A⊗B`, checks positive entry bounds, and computes ordinary ranks by exact Gaussian elimination. Equality between the factor width and the ordinary rank proves the exact nonnegative rank of each target matrix. There is no floating-point tolerance or optimization solver.

The three saved targets require 64, 144, and 400 product-entry checks respectively. `verification/independent-certificates.json` records the results, certificate hashes, and pivot columns.

The checker explicitly reports that it has **not** established the new seed's nonnegative-rank-four lower bound. That separate claim is a consequence of the classical nested-squares theorem cited in the manuscript. It is not needed to certify the target product's exact rank.

### Regenerate independently reproducible data

```bash
python3 computations/generate.py --s 2 3 5 --write verification/regenerated
python3 computations/check_certificate.py \
  verification/regenerated/activation_s2.json \
  verification/regenerated/activation_s3.json \
  verification/regenerated/activation_s5.json
cmp certificates/activation_s2.json verification/regenerated/activation_s2.json
cmp certificates/activation_s3.json verification/regenerated/activation_s3.json
cmp certificates/activation_s5.json verification/regenerated/activation_s5.json
```

The generator accepts other integer values `s≥2`. Its formula uses `q=3(s−1)`, `η=1/(58q)`, and `ε=1/(8816q³)`. Successful execution at additional sizes is a finite arithmetic check. The manuscript provides the proof for all sizes; the general explicit all-`s` formula is not fully instantiated in Lean.

The Lean module `PositiveCore.Activation` proves more than the single saved `s=2` endpoint: it proves the exact product rank throughout the real interval `0<ε≤1/238032`, by proving the symbolic factorization and entry inequalities in Lean.

## 4. Cone-separation certificate

```bash
python3 computations/cone_certificate.py --check certificates/cone_obstruction.json
```

This integer calculation checks the sixteen pairings of the four adjacent-pair generators of the intrinsic cone and the separating score of the original `17/1` seed. It records mass `144`, score `128`, and the strict violation `128>144/2`.

The finite certificate is an inspectable supplement. The general scalar cone inequality, its factorization consequence, and the tensor obstruction are established by the Lean development; the Python calculation is not a replacement for those proofs.

## 5. Original package reproduction

A byte-preserved original package is included in `upstream/original-package/`, with every file hashed in `upstream/PROVENANCE.json`. Its Python checks can be run there without another download. Alternatively, clone the repository and check out the pinned commit, then use its own verification instructions and scripts. For example, from an enclosing working directory:

```bash
git clone https://github.com/dvgyl/math-and-theory.git original-repository
git -C original-repository checkout 650a9782de75ab7f9eb16c2bcaf22c9b5e8b4d09
cd original-repository/papers/mathematics/nonnegative-rank-kronecker
python3 certificate/exact_certificate.py --verify-only certificate/C11_NMF109.json
python3 certificate/check_factorization.py
```

If a script's command-line interface changes in another revision, use the checked-out revision's own `--help` and `VERIFICATION.md`; the commit above is the reference input.

The recorded replay includes:

- Exact parsing of 26,499 rational entries in the order-11 certificate, its seven matrix equalities, and the width-109 square factorization.
- A separate direct product check of all 14,641 entries in the `121×121` square, with ordinary ranks `rank A₀=3` and `rank C₆=10`.
- A fresh original Lean replay, preserved in `verification/original-lean-replay/`.

The corresponding records are `verification/original-generator-check.json` and `verification/original-independent-check.json`. The original square's exact nonnegative rank remains unspecified: the certificate proves an upper bound of 109, not an equality.

## 6. Scope of formal verification

The fully formal headline lower bound uses the exact minimum over **all** nonnegative factorizations, not a minimum over supplied numerical examples. The original mixed-block equality and the real `s=2` activation interval are also formal endpoints. [FORMAL_CORRESPONDENCE.md](FORMAL_CORRESPONDENCE.md) gives their exact declarations and hypotheses.

The following mathematical material remains outside the complete Lean formalization:

- The full uniform neighborhood theorem that uses a Schur-complement chart and allows perturbation rank to change.
- The general local Kronecker saturation formula obtained from that neighborhood theorem or from published local-openness results.
- The all-size explicit activation construction and its quantitative bound as a single universally quantified Lean theorem.
- The new `9/20` seed's nonnegative-rank-four lower bound from classical nested-square geometry.
- Literature priority and journal significance.

These items have mathematical proofs or source attribution in the manuscript as indicated there. They must not be described as consequences of a kernel check merely because nearby supporting lemmas or particular instances are formalized.

## 7. Combined reproduction command

After installing the Lean dependencies, this command reruns all exact certificates,
checks byte-identical regeneration and upstream preservation, and performs a clean
Lean rebuild and audit:

```bash
python3 verify_all.py --lean --output verification/reproduction.json
```

Omit `--lean` to run the arithmetic and source/log hash checks only. In that mode,
the output explicitly says that the stored Lean record was checked without a new
kernel run. The release report in `verification/reproduction.json` was produced
after the separately recorded clean Lean build.
