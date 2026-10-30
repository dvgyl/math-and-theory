# The small-coefficient upper half of the Keller–Klein conjecture

**Fully autonomous agentic research.** Autonomous AI research agents produced the proof, the Lean formalization and an earlier note; Opus 5.5 by Anthropic used with Claude Code rechecked them, ran fresh Lean replays and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Let `X = Σᵢ vᵢ εᵢ` with independent uniform signs `εᵢ`, real coefficients with `Σᵢ vᵢ² = 1` and `|vᵢ| ≤ a`, where `0 < a ≤ 7/100`. For every `x ≥ 0`,

```text
P(|X| ≤ x) ≤ 2Φ(x) + 2Φ(a) − 2,      P(X ≤ x) − Φ(x) ≤ Φ(a) − 1/2,
```

where `Φ` is the standard normal distribution function. Coefficients may be unequal, negative or zero, and the number of terms is unrestricted.

Keller and Klein conjectured that `|P(X ≤ x) − Φ(x)| ≤ Φ(a₁) − 1/2` for all real `x`, where `a₁ = maxᵢ |vᵢ|` (Adv. Math. 2022, Conjecture 9.3). Ivanisvili's computer-assisted manuscript of 21 October 2026 proves the lower half for all coefficient vectors and the full conjecture for `a₁ ≥ 0.07`, and leaves exactly this upper half for `a₁ < 0.07` open, noting that it needs a new idea. The theorem here closes that range by the analytic route his Section 11 proposes. Together with his Theorems 1.1 and 10.9 it implies the full conjecture; those external results are computer-assisted, unrefereed and outside this Lean development, so the full conjecture is settled only conditionally on them.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 62 modules in [lean/KellerKlein](lean/KellerKlein), with the central statements in [Main.lean](lean/KellerKlein/Main.lean) and the axiom audit in [Audit.lean](lean/KellerKlein/Audit.lean).
- [Detailed derivations](notes/) of the two analytic zones and their [exact rational constant checks](checks/).
- [Third-party provenance](third_party/causalsmith/UPSTREAM.txt) for three Apache-2.0 support modules adapted from CausalSmith.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
