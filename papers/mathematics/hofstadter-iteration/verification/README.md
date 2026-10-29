# Verify the Hofstadter iteration family

I provide exact finite checks and the universal Lean proof here.

The independent program uses exact integers to compute the recursive functions. The Lean proof establishes the uniform result for every `k≥4`. Read the [paper](../paper.pdf) and [theorem map](../../../../lean/docs/mathematics/hofstadter-iteration.md) for the precise statements.

## Reproduce the computation

From the repository root, run:

```sh
python3 papers/mathematics/hofstadter-iteration/verification/scripts/verify.py
```

The program uses only the Python standard library. It writes JSON to standard output and raises an assertion failure if a check fails.

For each parameter `k`, it starts with `F_k(0)=0`. To compute the next entry at index `n`, it starts at `n−1`, applies the existing table lookup `k` times, and stores `n` minus that result. Thus the computation uses the defining recurrence. It does not read the formal proof's finite tables.

The exact finite checks give:

| Input | `F_4^9` | `F_5^10` |
| --- | ---: | ---: |
| 132 | 8 | 7 |
| 36 | 2 | 3 |

The program also checks 29 parameter values: every `k` from 4 through 30, plus 50 and 100. It constructs both inverse orbits with `L_k(n)=n+F_k^(k−1)(n)`. It checks that their difference is `k−3`, then evaluates the forward iterates at the resulting witness. At `k=100`, the inverse values are 202,915 and 203,012, and the forward values are 104 and 103.

These computations use exact integers. They check finitely many cases and do not prove the universal parameter claim.

## Reproduce the formal checks

Install the toolchain in `lean/lean-toolchain` and obtain the pinned project dependencies. From the repository root, run:

```sh
cd lean
lake build MathAndTheory.Mathematics.Hofstadter.Family Solutions.Mathematics.Hofstadter.Main
lake env lean Solutions/Mathematics/Hofstadter/Main.lean
```

The three proof modules use `Std`. The recursive definition is infinite and independent of the finite tables. `validTable_correct` proves that a table satisfying the recurrence agrees with that function on its index range. Kernel-reduced `decide` checks the two finite tables. The family proof derives the inverse relation and exact orbit gap without an assumed recurrence property.

The selected Solution theorem is `HofstadterChallenge.result`. Its axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`. The Challenge defines the functions and states the same theorem without importing the substantive proof. Its permitted target hole is excluded from the proved library.

In an environment with `bwrap` and the kernels bundled with Lean 4.35.0, run this command from `lean/`:

```sh
bash scripts/verify-comparator.sh comparator/mathematics/hofstadter-iteration.json
```

Comparator replay for this selected statement has passed through Lean, NanoDa, and con-ron. See the [central verification record](../../../../verification/README.md) for the recorded run. This result checks the statement and proof term. It does not establish novelty or peer review.

## Limits

The infinite family varies `k`. The theorem does not claim infinitely many violating inputs for each fixed `k`. The finite incomparability result concerns the particular functions `F_4^9` and `F_5^10`. No classification of all iteration indices is claimed.

The [prior-work record](../README.md) explains the source comparison and the limits of the search. This paper has not been peer reviewed.

See the [authorship and autonomous AI disclosure](../../../../AUTHORSHIP.md).
