# Lean formalizations

I keep the shared formal library for seven of the thirteen result families in this Lake project. It has 29 selected Comparator statements. Lean is pinned to version 4.35.0. Mathlib and every transitive package are pinned in `lake-manifest.json`.

The `MathAndTheory` library contains the substantive proofs. `Challenges` contains independent source statements with deliberate proof holes. `Solutions` proves the same statement types. The proved library does not import `Challenges`.

The [verification guide](../verification/README.md) gives build, axiom-audit, Comparator, independent-kernel, and source-validation commands. The [v0.4 metadata](formalization.yaml) records proof provenance, scope, source differences, and automation.

| Family | Statement and prior-work guide | Comparator configuration |
|---|---|---|
| q-permanent | [Guide](docs/q-permanent.md) | [Configuration](comparator/q-permanent.json) |
| gyires-circulant-five | [Guide](docs/gyires-circulant-five.md) | [Configuration](comparator/gyires-circulant-five.json) |
| domirank-entropy | [Guide](docs/domirank-entropy.md) | [Configuration](comparator/domirank-entropy.json) |
| diagonal-concavity | [Guide](docs/diagonal-concavity.md) | [Configuration](comparator/diagonal-concavity.json) |
| alternating-motzkin | [Guide](docs/alternating-motzkin.md) | [Configuration](comparator/alternating-motzkin.json) |
| hofstadter-iteration | [Guide](docs/hofstadter-iteration.md) | [Configuration](comparator/hofstadter-iteration.json) |
| best-of-n | [Guide](docs/best-of-n.md) | [Configuration](comparator/best-of-n.json) |

## Standalone packages

I keep the other six families in separate proof environments. Five use Lean 4.19.0 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Asymmetric Tutte uses Lean 4.32.1 and its own pinned Mathlib revision. They are not imported by this Lake project and are not included in its Comparator selection.

| Family | Manuscript | Proof environment and scope |
|---|---|---|
| Decision-tree covariance | [PDF](../verification/additional-proofs/readk-covariance/docs/manuscript.pdf) | [Package guide](../verification/additional-proofs/readk-covariance/README.md). Covariance inequalities and finite witnesses; no Fourier-entropy theorem. |
| Thermal current kurtosis | [PDF](../verification/additional-proofs/thermal-kurtosis-counterexample/report.pdf) | [Package guide](../verification/additional-proofs/thermal-kurtosis-counterexample/README.md). Finite spectral statements; no stochastic long-time identification theorem. |

I also include standalone packages for [Sharp Eighth](../verification/additional-proofs/sharp-eighth/README.md), [Galvin–Zhang](../verification/additional-proofs/galvin-zhang/README.md), [universal embezzlement](../verification/additional-proofs/universal-embezzlement/README.md), and [asymmetric Tutte](../verification/additional-proofs/asymmetric-tutte/README.md). Each guide gives the exact theorem scope and build commands.

I keep the additional Gyires [order-six](../verification/gyires-circulant-six/README.md) and [permutation-polynomial](../verification/gyires-permutation-polynomial/README.md) proofs in separate packages. [UNFINISHED.md](../UNFINISHED.md) lists the remaining formal-proof gaps.

The decision-tree package's 29 axiom reports are a separate count from this library's 29 Comparator declarations. The package guides identify their exact toolchains, source hashes, and reproduction commands.

The source and axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`. A successful build does not by itself establish source fidelity, originality, or editorial suitability for Palomar. The [family addition procedure](docs/adding-a-family.md) gives the required sequence for later work.

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.
