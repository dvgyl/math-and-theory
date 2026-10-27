# The exact asymmetric Merino–Welsh region for finite matroids

I present a theorem that characterizes all nonnegative pairs (x,y) for which T_M(x,0) T_M(0,y) ≥ T_M(1,1)² holds for every finite matroid without loops or coloops.

The statement uses actual Mathlib matroids and the literal subset rank sum. It includes empty ground sets and finite ground sets in arbitrary ambient types.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).

## Reproduce the proof

Use the pinned Lean 4.32.1 toolchain and Mathlib revision `520045ab14e26149ee970e2e617ca04b09bde5d6`. Install Git and the Lean toolchain manager `elan`. Start with a fresh copy of this directory.

```sh
lake exe cache get
lake build
lake env lean --error=warning Audit.lean
```

The audit prints the transitive axioms of the selected statements. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. A successful check must contain every requested report and no additional axiom. Compiler errors and warnings require a failed check.

## License and publication

The original code and manuscript use [Apache-2.0](LICENSE). [NOTICE](NOTICE) identifies external dependencies. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite this preprint.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. This preprint has not been peer reviewed.

The source verification record gives the hashes from the completed source build. Compiled object files are not included. Integrity checks compare the published source bytes. Run the Lean commands to reconstruct the objects and check the theorems.
