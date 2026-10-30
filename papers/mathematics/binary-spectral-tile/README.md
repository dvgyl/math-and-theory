# A 64-point spectral tile in F₂⁹ with no periodic complement

**Fully autonomous agentic research.** Autonomous AI research agents produced the construction, the proof, the Lean formalization and an earlier note; Opus 5.5 by Anthropic used with Claude Code rechecked them, proved and formalized that the tiling complement is unique up to translation, and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Write `F₂⁹ = F₂⁶ × F₂³` and let `C = {0, e₁, …, e₆, e₁+⋯+e₆} ⊂ F₂⁶`. For eight explicit three-dimensional subspaces `K₀, …, K₇` of `F₂⁶`, the 64-point set

```text
E = ⋃ᵢ Kᵢ × {i}
```

is spectral with spectrum `C × F₂³`, tiles `F₂⁹` with the complement `T = C × {0}`, and is aperiodic. Every tiling complement of `E` is aperiodic, so no linear subspace complements `E` and `F₂⁹` fails the periodic tiling property of Fan and Zhang. In fact the complements of `E` are exactly the 512 translates of `T`: the allowed shifts form the line graph of `K₈` on `C`, and a complement corresponds to a star.

This answers negatively the stronger subspace-complement part of Question 8.1 of Ferguson and Iosevich (arXiv:2610.36417, 26 October 2026) and, through their stated equivalence, their Question 8.2. It does not settle whether every spectral 64-point subset of `F₂⁹` tiles. Accepting their dimension-eight theorem, nine is the least binary dimension in which the periodic tiling property fails.

## Priority and subsequent correspondence

On 30 October 2026, following my correspondence with Dr. Samuel Ferguson, he informed me that he and his coauthor Professor Joshua Iosevich had already become aware of counterexamples to the stronger statement shortly after submitting their recent arXiv paper. These findings were previously unknown to me, and my agents' original novelty searches had not found them.

I acknowledge their prior awareness of counterexamples to the stronger subspace-complement statement. I have not seen their examples, and it has not been established whether they are equivalent to my 64-point construction. Later the same day, Dr. Ferguson shared an AI-generated comparison suggesting that my construction is not affinely equivalent to his displayed example or to any of 210 constructions he had saved, despite substantial structural overlap, and that the constructions share common classifications of their tiling complements and spectra. These are provisional AI-generated findings. I have not independently verified them, and I do not treat them as established mathematical conclusions. I continue to acknowledge Ferguson and Iosevich's earlier counterexamples.

The construction, the classification of its 512 complements and the Lean formalization are unchanged. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#binary-spectral-tile-in-dimension-nine) gives the details.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 16 modules, with the central statements in [BinaryMain.lean](lean/BinaryMain.lean) and the classification of complements in [BinaryComplements.lean](lean/BinaryComplements.lean), the module list in [modules.json](lean/modules.json), the generated audit in [AxiomAudit.lean](lean/AxiomAudit.lean) and the frozen source hashes in [release-freeze.json](lean/release-freeze.json).
- [Exact checks](checks/check_construction.py) with the [construction data](checks/construction.json), and a [priority screen](discovery/) of the public Ferguson–Iosevich examples.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
