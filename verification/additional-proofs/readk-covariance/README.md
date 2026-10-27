# Logarithmic covariance bounds for Boolean decision trees

I publish the manuscript and Lean proof of the decision-tree covariance bounds here. My [ORCID is 0009-0009-9132-744X](https://orcid.org/0009-0009-9132-744X).

Manuscript and Lean 4 formalization, 27 October 2026. Read the complete proof in [the manuscript](docs/manuscript.pdf).

## Mathematical results

For a finite Boolean decision tree with no repeated coordinate on a root-to-leaf path, let `k_i` be the total number of query nodes labelled `i`, and let `I_i(f)` be uniform bit-flip influence. The principal theorem proves

\[
\sum_v 2^{-d(v)}\,|\operatorname{Cov}(f_{v,0},f_{v,1})|
\leq \sum_i I_i(f)\log_2\max(1,k_i).
\]

In particular, a read-`k` tree has signed and absolute tree covariance at most `log₂(k) I(f)` for `k ≥ 1`. The known dummy-prefix family attains equality for every `k = 2^d`.

The proposed replacement of total influence by variance with coefficient one is false. The package gives a four-variable read-3 counterexample with covariance `5/4` and variance `3/4`, and a nine-variable example with every query relevant, covariance `4863/4096`, and variance `3007/4096`.

The manuscript gives the full proofs, assumptions, comparison with the earlier results of Wan–Wright–Wu and Shalev, attribution of the proposed logarithmic potential, and limitations. The [related-work summary](docs/related-work.md) compares the cited results. The formalization contains no Fourier-entropy theorem.

## Pinned dependencies

- Lean: `leanprover/lean4:v4.19.0`.
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b` (the `v4.19.0` release).
- The included `lake-manifest.json` pins transitive Lake packages.
- Python 3 is needed only for the independent finite arithmetic check and audit-output validation.

The project uses the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`. It adds no research axioms. The axiom audit checks the transitive dependencies of the public result theorems. The proofs use kernel-checked tactics and ordinary finite `decide`, without native evaluation as a proof oracle.

## Reproduce

Install Lean's standard `elan` toolchain manager if it is not already available. In the extracted project directory, run:

```bash
lake exe cache get
bash verify.sh
python3 scripts/test_verifiers.py
```

Keep the supplied `lake-manifest.json`. The `lean-toolchain` file selects the pinned compiler. `lake exe cache get` downloads the official compiled mathlib dependencies; it is a convenience, not a substitute for compiling this project's proofs. To rebuild dependencies from source, omit that command. The final `verify.sh` command compiles the project, prints the theorem axiom dependencies, checks the source policy, and runs the independent exact-rational enumeration. Every command must exit with status zero. The verifier tests check valid results and reject missing, malformed, or invalid evidence.

The checked project sources, axiom reports, and exact finite-check output are included. [Verification scope](verification/report.md) explains the recorded checks. No compiled research proof objects are supplied: the verification instructions rebuild them from source.

## Source map

| File | Content |
| --- | --- |
| `Research/Cube.lean` | Uniform Boolean-cube expectation, covariance, influence, restriction identities, and the min-influence covariance estimate. |
| `Research/LogPotential.lean` | Base-two logarithmic weights and the scalar merge inequality, including zero-count cases. |
| `Research/DecisionTree.lean` | Tree syntax, evaluation, global query counts, path regularity, and the signed covariance bound. |
| `Research/Absolute.lean` | Output complementation, absolute covariance estimate, and the stronger absolute tree theorem. |
| `Research/Sharpness.lean` | The known equality family for every nonnegative depth. |
| `Research/Counterexample.lean` | The four-variable witness and an existential refutation of the variance refinement. |
| `Research/AbsoluteCounterexample.lean` | Absolute covariance of the four-variable witness. |
| `Research/Nonredundant.lean` | The nine-variable witness, exact counts and moments, local query relevance, and strict violation. |
| `Audit.lean` | Public theorem signatures and transitive axiom reports. |
| `scripts/finite_checks.py` | Independent standard-library Python enumeration with exact fractions. |
| `docs/manuscript.pdf` and `.tex` | Complete mathematical manuscript and typesetting source. |
| `docs/related-work.md` | Cited prior results and the differences in their assumptions and conclusions. |
| `scripts/test_verifiers.py` | Regression checks for mathematical failures and incomplete verification evidence. |
| `verification/` | Actual compilation, axiom, and arithmetic verification output. |

## Scope of the verification

`Bool` encodes the two output signs by `false ↦ -1` and `true ↦ +1`. Expectations range over the full finite uniform cube. The `Regular` predicate means that no variable appears twice on a single root-to-leaf path; repeated occurrences in separate branches are permitted. Read multiplicity counts all query nodes in the entire tree. `Nonredundant.Relevant` requires the two child functions at each node to be unequal.

The formalization proves statements for this finite model. It does not prove a universal Fourier entropy–influence bound or the optimal asymptotic variance bound. It does not establish literature priority. This standalone project uses Lean 4.19.0. No compatibility with another Lean release is asserted.

## Research and publication

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.

The logarithmic potential is due to Shalev. The equality construction is due to Wan, Wright, and Wu. The manuscript gives the full citations.

## Build the manuscript

From the project root, use Pandoc and Tectonic:

```bash
pandoc docs/manuscript.md --from=markdown+tex_math_single_backslash --standalone --number-sections --to=latex --output=docs/manuscript.tex
tectonic docs/manuscript.tex --outdir docs
```

Use `CITATION.cff` or `CITATION.bib` to cite the manuscript.

## Package integrity and license

[manifest.json](manifest.json) lists the SHA-256 hash of every release file except itself. The package uses the [Apache License 2.0](LICENSE).

`SOURCE_SHA256SUMS` covers source and build-control files only. Use `manifest.json` for the complete package file list.
