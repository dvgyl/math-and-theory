# A positive constant-recursive sequence with nonquasipolynomial power ranks

This submission package requires the official full Palomar preflight. It contains the complete proof source, the independent Challenge, and the original manuscript. The module-system port requires a fresh full Palomar preflight.

The main positive integer sequence is

`s(n) = 1 + 2^n + 3^n(1 - 2^n)^2 + n9^n(1 + 2^n)^3`.

A constant-coefficient recurrence expresses each later term as a fixed linear combination of earlier terms. Here recurrence rank is the least order of an admissible complex recurrence that holds after some index. Its polynomial is monic and has nonzero constant coefficient. The sequence has rank 13.

The power with exponent `M` means the sequence `s(n)^M`. The main theorem gives its complete minimal characteristic polynomial and exact rank for every natural `M`, including zero. The rank is a cubic expression minus twice a parity-restricted square count. The square-root correction has error at most two for `M ≥ 1`. The power ranks are not eventually quasipolynomial. This means that no finite list of real polynomials gives their values by residue class after a common threshold.

The companion family is `1 + 2^n + 2^(dn) + ∑ p_i^n`. It uses `r - 3` distinct odd primes and every integer `d ≥ 2`. The selected statements give the exact rank of every power and infinitely many different power-rank profiles at each fixed initial rank `r ≥ 3`.

[Challenge.lean](Challenge.lean) contains the independent recurrence and sequence definitions. It has three deliberate theorem holes. [Solution.lean](Solution.lean) imports the complete main and companion proof package. [comparator/power-rank.json](comparator/power-rank.json) selects the three existing statements. [formalization.yaml](formalization.yaml) records their exact scope and attribution.

Use the pinned Lean 4.35.0 toolchain and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. From this directory, the proof build commands are:

```sh
lake exe cache get
lake build PowerRankComplete Solution
lake env lean --trust=0 -DwarningAsError=true formalization/src/CompleteAudit.lean
```

Private local checks do not replace the official full preflight. The official full preflight must check the exact published submission commit before intake. The audit requests 25 axiom reports. The expected permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Read [manuscript.pdf](manuscript.pdf), [manuscript.tex](manuscript.tex), [PROOF_MAP.md](PROOF_MAP.md), and [formalization/THEOREMS.md](formalization/THEOREMS.md) for the mathematical argument and source map. The companion generating function, eventual polynomial degree and leading coefficient, and simplified rank-three examples have conventional manuscript proofs. They are outside the selected formal claim.

[VERIFICATION.md](VERIFICATION.md) gives the current verification boundary. The earlier release manifests, source hashes, and verifier scripts are excluded. [source-sha256.json](source-sha256.json) identifies current file bytes only. The retained supplement scripts and recorded bounded arithmetic results do not replace the universal proofs. They have not been run during this preparation.

[AUTHORSHIP.md](AUTHORSHIP.md) preserves the contribution disclosure. [formalization/NOTICE](formalization/NOTICE) records source credit. The exponential-polynomial rank principle, coefficient duality and Krawtchouk recurrence, and principal-relation Hilbert-function mechanism are standard supporting mathematics. Rowland and Sistos Barrón receive credit for the related study of powers of constant-recursive sequences. Historical priority and precise source correspondence remain provisional. The nonquasipolynomial conclusion is not identified with the source's undefined term “pseudo-polynomial.”

The original package uses [Apache-2.0](LICENSE). Use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib) to cite the manuscript.

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex produced formal proofs and verification software for the accompanying package. I am responsible for publication.
