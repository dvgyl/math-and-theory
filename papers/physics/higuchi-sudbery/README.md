# A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound

I present the mathematical result and its formal proof below.

The average von Neumann entropy of the three two-qubit marginals of a pure four-qubit state is at most log(2) + log(3)/2. The Higuchi–Sudbery state attains this bound.

The proof uses all sixteen complex amplitudes, actual reduced-matrix eigenvalues, an exact sum-of-squares identity, and an explicit maximizing state.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).

## Priority and subsequent correspondence

On 30 October 2026, following my correspondence with Dr. Jef Pauwels, he informed me that the Omega Institute had recently announced a similar result. I was previously unaware of this work, and my agents' original novelty searches had not found it. Upon investigating, I found that the Omega Institute had registered the problem on 5 October 2026 and publicly committed a claimed Lean proof on 7 October 2026 ([public record](https://github.com/the-omega-institute/trureturing/issues/13454)), before I published this result on 27 October 2026. A subsequent comparison showed that our 272-term sum-of-squares certificates are algebraically equivalent.

I acknowledge the Omega Institute's earlier public work and the substantial overlap between our results, and I make no originality or priority claim for this result. I have not independently checked their Lean proof. The proof here, its Lean formalization and the verification records are unchanged. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#higuchisudbery-four-qubit-entropy-bound) gives the details.

## Reproduce the proof

Use the pinned Lean 4.35.0 toolchain and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Install Git and the Lean toolchain manager `elan`. Start with a fresh copy of this directory.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true HS/Audit.lean
```

The audit prints the transitive axioms of the selected statements. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. A successful check must contain every requested report and no additional axiom. Compiler errors and warnings require a failed check.

## Exact certificate checks

Run `python3 tools/audit_sos.py` for the exact integer sum-of-squares identity. This checker uses only the Python standard library. Its report gives the complete coefficient comparison counts.

## License and publication

The original code and manuscript use [Apache-2.0](LICENSE). [NOTICE](NOTICE) identifies external dependencies. Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite this preprint.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. This preprint has not been peer reviewed.

The [source verification record](verification/source-checks.json) gives the checked hashes and compiler logs for all 50 source modules. The audit checks eleven selected axiom reports. [VERIFICATION.md](VERIFICATION.md) states the theorem scope and its limits. Compiled object files are not included. Integrity checks compare the published source bytes. Run the Lean commands to reconstruct the objects and check the theorems.
