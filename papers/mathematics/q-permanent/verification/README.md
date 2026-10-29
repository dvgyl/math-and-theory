# Independent q-permanent checks

I include exact computational checks for the q-permanent counterexamples here.

Run from the repository root after installing [the pinned packages](../../../../verification/requirements.txt):

```sh
python3 papers/mathematics/q-permanent/verification/scripts/verify.py
```

The program enumerates all 120 permutations of the displayed order-five matrix. It reconstructs every nonzero term, inversion count, polynomial coefficient, the values at 14 and 15, and the derivative at 15. An exact rational LDL factorization checks positive definiteness.

It also enumerates the full sparse-family permutation sums for dimensions four through eight. Exact rational calculations check the sufficient growth condition and negative derivative at `101/100`, `11/10`, `3/2`, `2`, and `15`. The chosen dimensions are 929, 73, 16, 10, and 5. The large-dimensional checks use the proved family formula; they do not enumerate all permutations in those dimensions.

These finite checks do not prove the all-real-parameter theorem. The mathematical proof and Lean formalization establish that quantifier. [Logs](logs) record the independent run. The [central guide](../../../../verification/README.md) records formal and independent-kernel checks. [Statement fidelity](../../../../lean/docs/mathematics/q-permanent.md) explains the original conjecture and the exact scope.

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.
