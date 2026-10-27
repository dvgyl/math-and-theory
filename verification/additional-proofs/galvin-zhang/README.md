# Ultra-log-concavity of domination sequences of powers of paths and cycles

I present the proof of Conjecture 1.8 of Galvin and Zhang.

A dominating set covers each graph vertex through membership or adjacency. Let dₖ count the dominating sets of size k in a graph with n vertices. This package proves that dₖ / binom(n,k) is log-concave for every power of a finite path or cycle. It establishes Conjecture 1.8 of Galvin and Zhang.

The manuscript states the theorem for all n ≥ 0 and all powers ℓ ≥ 1. The Lean theorem also includes ℓ = 0. Its counts are cardinalities of actual dominating vertex subsets. The proof establishes their correspondence with bounded gap sequences. It has no finite order cutoff or positive-count assumption.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Theorem map and verification scope](VERIFICATION.md).
- [Related work](RELATED_WORK.md).

## Reproduce the proof

Install Git and [elan](https://lean-lang.org/install/). Extract the source package into a new directory. It contains no compiled project files. Use the pinned Lean 4.19.0 toolchain and the dependency revisions in `lake-manifest.json`.

Run these commands from the package directory:

```sh
lake exe cache get
lake build
lake env lean -j1 -DwarningAsError=true Audit.lean
```

To check the package hashes from the full repository, run `python3 verification/check_embedded_packages.py` from the repository root. The manifest uses JSON, not the line format required by `shasum -c`.

The cache command downloads compiled dependency files. The build command compiles the project sources and the audit. Warnings cause failure. The audit prints four theorem types and four axiom reports. Each report must use only `propext`, `Classical.choice`, and `Quot.sound`.

For a new check, extract the source package again into a new directory. Do not copy project build files from an earlier run. The package fixes its dependency commits. Do not run `lake update` to move them to other revisions.

## Citation and license

Dev D. Goyal. *Ultra-log-concavity of domination sequences of powers of paths and cycles*. Preprint, 2026. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib).

The code and documents use the Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE). This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.

The source verification record gives the hashes from the completed source build. Compiled object files are not included. Integrity checks compare the published source bytes. Run the Lean commands to reconstruct the objects and check the theorems.
