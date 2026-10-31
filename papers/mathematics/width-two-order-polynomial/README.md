# Order-polynomial positivity for width-two posets with a chain of at most five elements

**Fully autonomous agentic research.** Autonomous AI research agents in a GPT-6 Astra research workflow proved the theorem and built the certificates and their verifiers; Opus 5.5 by Anthropic used with Claude Code checked the proof, wrote an independent certificate checker, wrote and ran the Lean formalization and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

For a finite poset `P` the order polynomial `Ω_P(t)` counts weakly order-preserving maps `P → {1, …, m}` at `t = m`; `Ω_P(t + 1)` is the Ehrhart polynomial of the order polytope. Ferroni, Morales and Panova (*Skew shapes, Ehrhart positivity and beyond*, arXiv:2503.16403v3, Conjecture 7.1) conjectured that `|P|! Ω_P(t)` has nonnegative coefficients in the monomial basis for every poset of width at most two, and reported computer checks when both chains of a two-chain cover have at most five elements.

**Theorem.** Let `P` be a finite poset that is the disjoint union of two chains `A` and `B` with `|A| ≤ 5`, with no condition on `|B|` or on the comparabilities between `A` and `B`. Then every coefficient of `|P|! Ω_P(t)` in the monomial basis is a nonnegative integer. If `a = |A| ≥ 1` and `b = |B| ≥ 1`, then

```
[t] Ω_P(t) ≥ (a − 1)! (b − 1)! m / (a + b)!,
```

where `m` is the number of elements of `B` comparable with some element of `A`; hence the linear coefficient is positive exactly when the comparability graph of `P` is connected.

**Proof outline.** The comparabilities between the chains are encoded by monotone boundaries `L_i ≤ U_i`. By the descent–rook correspondence of Alexandersson and Jal (arXiv:2410.00127v3), `F = (a + b)! [t]Ω_P(t)/(b − 1)!` is an alternating sum of non-nesting rook numbers. Ordering the `2a` boundaries gives one of 64 chambers (Dyck words, `a ≤ 5`), and on each chamber `F` is a polynomial `F_{a,w}` of degree at most `a` in the `2a + 1` gaps between boundaries, whatever `b` is. Its values at the integer points with gap sum at most `a` determine it. Exact certificates prove each `F_{a,w}` nonnegative on the orthant: positive coefficients for `a ≤ 3`, and sums of 1,072 rational squares plus remainders with nonnegative coefficients for `a = 4, 5`, matched with an independent order-polynomial evaluation at 194,112 points. The ideal–filter reduction of Ferroni, Morales and Panova (Proposition 3.3, Theorem 3.4) lifts nonnegativity of the linear coefficient to all coefficients. The unrestricted conjecture remains open.

## Formal scope

Lean 4.35.0 checks the chamber certificates for `a ≤ 4`. For each of the 22 chambers the data file stores the scaled polynomial `D·F_{a,w}`, the degree-one part and the rest of the scaled nonnegative remainder, and square triples; a Boolean test evaluated by the kernel (`decide +kernel`) checks that they add up exactly, every sign condition and the degree-one coefficients. `ShortChain.certified_chambers` states that every chamber polynomial is nonnegative at every gap vector with nonnegative entries in any linearly ordered field and is at least `(a − 1)!` times the sum of the gaps comparable with the short chain; `ShortChain.chambers_complete` states that the chamber words for each `a ≤ 4` are exactly the Dyck words. No `native_decide` is used, and every project declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Not formalized: the identification of `F_{a,w}` with the linear coefficient of the order polynomial (descent–rook correspondence, descent expansion, degree bound, determining set and point identities), the 42 chambers with `a = 5`, which the Python checker verifies, and the reduction from the linear coefficient to all coefficients.

## Prior work and priority

The conjecture, the computations for both chains of size at most five and the ideal–filter reduction are due to Ferroni, Morales and Panova; the descent–rook correspondence is due to Alexandersson and Jal. Two public partial results on the same conjecture are credited in the manuscript: the repository [10m-u/open-problems-catalog](https://github.com/10m-u/open-problems-catalog/tree/ca8d4d44ba3db527f19f28928c240168f545ecfe) (commit of 14 October 2026) proves positivity for ordinal sums of antichains of size one or two, and the repository [chris-hadad/lr-stretching-results](https://github.com/chris-hadad/lr-stretching-results/blob/0677a8b4bda0db770ad690824c236222783eeb95/results/overlap-families/proofs/A58-COUPLED-PROOF.md) (commit of 29 October 2026) proves positivity for lattice-point counts whose order-polynomial factors have a single cross-link. Neither class contains the class of the theorem or is contained in it, and this is not the first all-size partial result on the conjecture. Searches in October 2026 did not find the theorem or the lower bound; coverage of recent and unpublished work is incomplete and historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [certificate/data/](certificate/data/): the three xz-compressed certificate files (`a ≤ 3`; `a = 4`; `a = 5`).
- [certificate/check_certificates.py](certificate/check_certificates.py): standard-library checker of all 64 chambers, with its own order-polynomial evaluation, negative controls and the worked examples.
- [lean/](lean/): the Lean project. The endpoints are `ShortChain.certified_chambers`, `ShortChain.chambers_complete` and `ShortChain.chambers_valid` in [Main.lean](lean/ShortChain/Main.lean) and [Data.lean](lean/ShortChain/Data.lean); [theorem-map.json](theorem-map.json) maps each manuscript result to its declarations or to its conventional or certificate proof.
- [scripts/generate_lean_data.py](scripts/generate_lean_data.py): generates `Data.lean` from the certificates and, with `--check`, confirms that it matches them.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
