# A quartic entropy deficit for random rankings

I present the mathematical result and its formal proof below.

A distribution on rankings of n labels has entropy at most (1 − ε⁴/144) log(n!) if every pairwise comparison has probability at distance at least ε > 0 from 1/2.

The proof includes all finite sizes and actual position-valued permutations. It assumes neither independent comparisons nor transitive preferred directions.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).

## Reproduce the proof

Use the pinned Lean 4.19.0 toolchain and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Install Git and the Lean toolchain manager `elan`. Start with a fresh copy of this directory.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true PermEntropy/Verification.lean
```

The audit prints the transitive axioms of the selected statements. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. A successful check must contain every requested report and no additional axiom. Compiler errors and warnings require a failed check.

## License and publication

The original code and manuscript use [Apache-2.0](LICENSE). [NOTICE](NOTICE) identifies external dependencies. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite this preprint.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. This preprint has not been peer reviewed.

The source verification record gives the hashes from the completed build of all 20 source modules. The verification module checks five endpoint types and the transitive axioms of all 238 project theorem declarations, including 17 private helpers. Compiled object files are not included. Integrity checks compare the published source bytes. Run the Lean commands to reconstruct the objects and check the theorems.
