# The sharp level-one Fourier weight at density one eighth

I present the sharp level-one Fourier bound at density one eighth.

For every Boolean indicator of mean 1/8 on a finite uniform cube, the level-one Fourier weight is at most 3/64. A codimension-three subcube attains the bound in every dimension at least three.

The formal proof includes arbitrary dimensions, the exact moment identities, the Hamming-distance bound, and sharpness witnesses.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).

## Priority and subsequent correspondence

On 30 October 2026, Professor Lei Yu informed me that Yijia Fang and Hao Huang had already proved the same density-1/8 Fourier-weight bound. He told me that their manuscript had been shared privately approximately one month earlier; it was submitted to arXiv on 29 October 2026 as [*Average pairwise Hamming distance of a subset in a hypercube*](https://arxiv.org/abs/2610.40486). Their result also characterizes the equality cases. I was previously unaware of their work, and my agents' original novelty searches had not found it.

I confirmed the public arXiv record, whose summary states the same bound in its average-distance form together with the equality cases. The private circulation date is as Professor Yu reported it; I have not seen that version, and I have not compared the two proofs. I acknowledge Fang and Huang's earlier work, I make no originality or priority claim for this bound, and I have withdrawn the statements in the manuscript that presented the bound as its contribution. The proof here, its exact certificates and the Lean formalization are unchanged. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#sharp-level-one-fourier-weight-at-density-one-eighth) gives the details.

## Reproduce the proof

Use the pinned Lean 4.19.0 toolchain and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Install Git and the Lean toolchain manager `elan`. Start with a fresh copy of this directory.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

The audit prints the transitive axioms of the selected statements. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. A successful check must contain every requested report and no additional axiom. Compiler errors and warnings require a failed check.

## Exact certificate checks

Run `python3 verify_certificate.py` for the exact rational coefficient checks. This checker uses only the Python standard library.

## License and publication

The original code and manuscript use [Apache-2.0](LICENSE). [NOTICE](NOTICE) identifies external dependencies. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite this preprint.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. This preprint has not been peer reviewed.

The source verification record gives the hashes from the completed source build. Compiled object files are not included. Integrity checks compare the published source bytes. Run the Lean commands to reconstruct the objects and check the theorems.
