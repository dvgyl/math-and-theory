# Critical hard-core influence bounds via nonbacktracking collisions

**Fully autonomous agentic research.** Autonomous AI research agents produced the proof, the Lean formalization and an earlier note; Opus 5.5 by Anthropic used with Claude Code rechecked them and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Fix `Δ ≥ 3` and `d = Δ − 1`. For every finite simple graph on `n` vertices with maximum degree at most `Δ`, every hard-core activity `0 < λ ≤ λ_c(Δ) = d^d/(d−1)^(d+1)`, every feasible pinning and every source with a nondegenerate pinned marginal, the absolute row sum of the influence matrix is at most

```text
1 + 12 Δ d [λ/(1+λ)] r ⌈log_d r⌉,   r = ⌊√(2Δn)⌋ + 1,
```

an `O_Δ(√n log n)` ℓ∞-spectral-independence bound at the uniqueness threshold. The influence matrix uses the actual conditional hard-core law, with diagonal one.

The proof combines exact vertex-deletion identities, a known local squared-message contraction, a self-avoiding-walk transfer in the style of Sinclair, Srivastava, Štefankovič and Yin, and a finite form of the nonbacktracking collision argument of Bencs et al. It recovers, up to a logarithm, the `O(√n)` bound stated by Chen and Jiang in 2025 and withdrawn in January 2026. The constant is large: the bound improves on the trivial bound `n` only for `n ≥ 3.4·10⁶` when `Δ = 3`. A mixing-time consequence for Glauber dynamics follows from a published proposition that is not formalized here.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 32 modules in [lean/CriticalHardcore](lean/CriticalHardcore), with the central statements in [Main.lean](lean/CriticalHardcore/Main.lean) and the axiom audit in [Audit.lean](lean/CriticalHardcore/Audit.lean).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
