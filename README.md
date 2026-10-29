# A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound

I present the mathematical result and its formal proof below.

The average von Neumann entropy of the three two-qubit marginals of a pure four-qubit state is at most log(2) + log(3)/2. The Higuchi–Sudbery state attains this bound.

The proof uses all sixteen complex amplitudes, actual reduced-matrix eigenvalues, an exact sum-of-squares identity, and an explicit maximizing state.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).

## Palomar statement

I submit the unrestricted upper bound and its exact global maximum. [Challenge.lean](Challenge.lean) gives the independent statement and definitions. [Solution.lean](Solution.lean) imports the complete proof. [formalization.yaml](formalization.yaml) records the scope and source attribution. The deliberate Challenge holes are excluded from the proved library.

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

This branch contains the complete proof sources and an independent Palomar statement.
The source files have been ported to Lean's module system. The earlier compiler logs
and hashes do not certify these changed source bytes and are not included here.
Run the pinned full Palomar preflight on this exact commit before submission.
[VERIFICATION.md](VERIFICATION.md) states the theorem scope and its limits.
Compiled object files are not included.
