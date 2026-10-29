# Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity

I present a construction for universal entanglement embezzlement.

A target-independent catalyst with local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector on m entries.

The proof constructs local basis permutations and establishes their finite complex Hilbert-space interpretation. Arbitrary changes to an external Schmidt basis are not separately formalized.

A Schmidt probability vector is a finite list of nonnegative values with sum one. Its square roots are the target state amplitudes. Here `m` is the number of entries, including zero values. For every integer `L ≥ 1`, the same catalyst works for every such vector. The catalyst depends only on `L`. The local permutation can depend on the target.

Root fidelity `F` is the norm of the complex inner product of the two unit states. Root infidelity is `1 - F`. With catalyst local dimension `n = 2^(4L)`, the error bound is `125m/L² = 2000m/(log₂ n)²`. This gives convergence uniformly over probability vectors for each fixed `m`. Each party's combined target and catalyst register has dimension `mn`.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).

## Palomar statement

[Challenge.lean](Challenge.lean) states the local-permutation theorem and its logarithmic form. It includes the independent definitions and two deliberate theorem holes. [Solution.lean](Solution.lean) imports the complete proof source. [formalization.yaml](formalization.yaml) records the scope, source attribution, and preparation status.

This package is an uncompiled submission preparation. It preserves the manuscript from the pinned source commit. The manuscript describes the original Lean 4.19.0 environment. The submission source uses the dependency pins below and requires a fresh full preflight.

## Reproduce the proof

Use the pinned Lean 4.35.0 toolchain and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Install Git and the Lean toolchain manager `elan`. Start with a fresh copy of this directory.

```sh
lake exe cache get
lake build UniversalEmbezzlement Solution
lake env lean -DwarningAsError=true Audit.lean
```

The audit prints the transitive axioms of the selected statements. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. A successful check must contain every requested report and no additional axiom. Compiler errors and warnings require a failed check.

## License and publication

The original code and manuscript use [Apache-2.0](LICENSE). [NOTICE](NOTICE) identifies external dependencies. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite this preprint.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. This preprint has not been peer reviewed.

The source files have been ported to Lean's module system. Earlier compiler logs and hashes do not certify these changed source bytes and are not included. [source-sha256.json](source-sha256.json) identifies the current files. It is an integrity inventory, not a compiler record. Compiled object files are not included.

Run the pinned full Palomar preflight on the exact submission commit before intake. [VERIFICATION.md](VERIFICATION.md) states the full quantified scope and its limits.
