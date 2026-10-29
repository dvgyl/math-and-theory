# The exact asymmetric Merino–Welsh region for finite matroids

The theorem characterizes every nonnegative pair `(x, y)` for which
`T_M(1,1)^2 ≤ T_M(x,0) * T_M(0,y)` holds for every finite matroid without
loops or coloops. The definitions use actual Mathlib matroids and the subset
rank sum. The ground set can be empty. It can be a proper subset of an
infinite ambient type. Both infinite families in `AsymmetricTutte.Region`
are part of the statement.

The complete original proof development, manuscript source, and manuscript PDF
are included. The manuscript records the original research version.
The active package configuration uses Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

- [Manuscript](manuscript.pdf).
- [Editable manuscript](manuscript.tex).
- [Citation](CITATION.cff).
- [Verification scope](VERIFICATION.md).

`Challenge.lean` imports only Mathlib. It states the full equivalence and has
one deliberate proof placeholder. `Solution.lean` imports the complete proof.
`comparator/asymmetric-tutte.json` selects `AsymmetricTutte.universal_iff_region`.

The proof imports Mingchang Liu's substantive Tutte-threshold library at commit
`636352f0fef47b19d7d5de364858ccee2317fd66`. This dependency supplies the
rank-sum API, its bridge to Mathlib matroids, and supporting proofs. These are
prior work. The source is not included. Its Lean sources have no redistribution
license. See [NOTICE](NOTICE). The root Mathlib pin replaces the dependency's
original Mathlib 4.32.1 pin. Compatibility requires a fresh full check.

The module port and the new Challenge have not been compiled with these pins.
Historical compiler records do not certify these files. The full Palomar
preflight must check the exact commit, build the complete Solution, compare
Challenge and Solution, and inspect their axiom dependencies before intake.
No verification certificate is supplied.

The original code and manuscript use [Apache-2.0](LICENSE).
Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite the preprint.

This work is fully autonomous agentic research. The initial research and proofs
were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra
in Codex autonomously produced the formalizations and corrections. I checked
the proofs to the best of my mathematical abilities. This check is not expert
validation or peer review. I am responsible for publication. This preprint has
not been peer reviewed.
