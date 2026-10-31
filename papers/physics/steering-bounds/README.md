# Exact three-setting correlation bounds at fixed steering centre

This work is fully autonomous agentic research. Automated systems produced the mathematical arguments and formal proofs. Codex contributed mathematical checks, verification software, and manuscript preparation. I am responsible for publication. No expert validation or peer review is claimed.

Dev D. Goyal · 29 October 2026

I determine the exact upper envelope of the optimized CJWR three-setting correlation value for all two-qubit density matrices at fixed steering-ellipsoid centre length. I include complete proofs, explicit witness states, the singular marginal boundary, and Lean matrix formalizations. The [paper](paper/steering_bounds.pdf) gives the argument; [PROOF_MAP.md](PROOF_MAP.md) maps its claims to Lean.

For the Pauli correlation matrix \(T\), put \(F_3=\|T\|_{\mathrm F}\). For centre length \(c\in[0,1]\), the exact least upper bound of \(F_3^2\) is

\[
G(c)=\begin{cases}
1+\dfrac{(2-3c)^2}{2-2c-c^2},&0\le c\le2/3,\\
1,&2/3<c\le1.
\end{cases}
\]

The bound is attained for \(c<2/3\). For \(2/3\le c<1\), it is approached but never attained. A pure product state attains it at \(c=1\). A state with \(F_3>1\) exists at a given centre length exactly when \(c<2/3\). This threshold concerns the specified three-setting expression; it does not characterize all steerable states.

I also prove that the maximum fully entangled fraction at fixed centre length is \(1-c/2\). This is a short consequence of a known canonical spectral bound. Canonical filtering and the maximally obese witness family are credited prior ingredients. The paper cites Milne et al. (2014), Ducuara et al. (2024), Bravyi (2004), and Costa and Angelo (2016).

The formal objects are positive semidefinite complex matrices of size four with trace one. The partial traces, positive canonical filter, Pauli observables, actual witness matrices, least upper bound, and fully entangled fraction are explicit. The physical interpretation of the canonical centre and the measurement optimization for the CJWR expression use the cited external correspondences.

## Earlier public work

On 31 October 2026, a check of public problem records found that the Omega Institute's public repository [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing) records a claimed Lean proof of my companion bound f(ρ) ≤ 1 − c/2, which is Conjecture 2 of Milne, Jennings, Jevtic and Rudolph, committed on 8 October 2026 at 12:27 UTC (issue #14206), and a proof of their Conjecture 1 on the CHSH value at fixed centre, committed on 14 October 2026 (issue #16558). My first commit is dated 29 October 2026. The CHSH bound concerns a different quantity from my three-setting theorem, which appears in neither record. I acknowledge the earlier public record and make no priority claim for the fully-entangled-fraction bound. The proof, Lean formalization and verification record here are unchanged. The [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds) gives the dates and sources; a commit date does not by itself establish when it became public.

## Reproduction

The project pins Lean 4.19.0 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All dependency revisions are in `dependency-pins.json` and `lake-manifest.json`.

```bash
python3 scripts/verify.py --fetch-cache --serial
```

The script requires Python 3.9 or later, Git, and Lean/Lake. It checks dependency revisions, rebuilds all 18 task-owned modules, treats warnings as errors, uses compiler trust level zero, and audits all 23 principal declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed as axioms. Each build command has a 900-second limit. Mathlib caches accelerate the build; no supplied task-owned compiled objects are required.

The matrix theorem replay uses pinned official dependency artifacts. This establishes the checked Lean propositions, not novelty or experimental validation. Verification evidence is in `verification/`; a fresh network-backed Lake dependency build is a distinct reproduction route.

To rebuild the manuscript, run `pdflatex -interaction=nonstopmode -halt-on-error steering_bounds.tex` twice from `paper/`. The optional figure script requires NumPy and Matplotlib and plots only the analytic formulas.

The materials use the [Apache License, Version 2.0](LICENSE).
