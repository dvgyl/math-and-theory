# Alternating Motzkin sums in Lean

The principal theorem proves strict log-concavity of the real roots of the source finite sums from index five. It also proves that five is the smallest possible tail start. The [paper](../../preprints/alternating-motzkin/paper.pdf) gives the mathematical proof. The [verification guide](../../verification/alternating-motzkin/README.md) gives reproduction commands.

The source is [Zhao, INTEGERS 26 (2026), A55](https://math.colgate.edu/~integers/aa55/aa55.pdf), equations (1) and (2), and Conjecture 1. [Definitions.lean](../MathAndTheory/Mathematics/Motzkin/Definitions.lean) defines `MathAndTheory.Motzkin.Challenge.IsMotzkin` by

```text
a 0 = 1, a 1 = 1,
(n+3) * a (n+1) = (2*n+3) * a n + 3*n * a (n-1)  for n ≥ 1.
```

Here `a : ℕ → ℚ`. The same module defines

```text
alternatingSum a n = ∑ j ∈ Finset.range (n+1), (-1 : ℚ)^(n-j) * a j
nthRoot a n = (alternatingSum a n : ℝ) ^ (1 / (n : ℝ)).
```

The exponent in `nthRoot` uses real division and real power. It is not natural-number division. The inequalities concern positive sums at indices at least two. The formal function is total at index zero, but the positive-root claim does not use that index.

[Source.lean](../MathAndTheory/Mathematics/Motzkin/Source.lean) is the source correspondence module, `MathAndTheory.Mathematics.Motzkin.Source`. Its namespace is `MathAndTheory.Motzkin.Source`. The following names are relative to `MathAndTheory.Motzkin`.

| Claim | Declaration |
| --- | --- |
| The implemented sequence satisfies the source recurrence | `Source.motzkin_isMotzkin` |
| The source recurrence determines that sequence uniquely | `Source.eq_motzkin_of_isMotzkin` |
| The finite sum equals the recursive alternating sequence | `Source.alternatingSum_eq_alternating` |
| The correspondence holds for every sequence satisfying the source recurrence | `Source.alternatingSum_eq_of_isMotzkin` |
| The source root equals the implemented real root | `Source.nthRoot_eq_root` |
| Strict root log-concavity on the tail starting at five | `Source.finite_sum_roots_strict_log_concave` |
| Zhao's stated tail-nine conjecture | `Source.zhao_conjecture_one` |
| Strict reverse inequality at center five | `Source.finite_sum_roots_sharp_failure` |
| Every tail starting at most four fails log-concavity | `Source.finite_sum_tail_start_optimal` |
| Existence and all three main conclusions | `Source.solution` |

`Source.solution` proves `MathAndTheory.Motzkin.Challenge.Problem`. The existence clause prevents the recurrence condition from being empty. The uniqueness and finite-sum proofs establish the connection to the source statement. The formalization uses the source recurrence characterization. It does not prove a general correspondence with lattice paths.

[Analysis.lean](../MathAndTheory/Mathematics/Motzkin/Analysis.lean) defines the recursive sequences and proves the analytic estimates. Its principal declarations are `ratio_bounds_at`, `T_pos`, `interlacing_at`, `M_size`, `T_size`, `gap_pos`, and `root_inequality_infinite`. The infinite proof covers centers at least 31. [Finite.lean](../MathAndTheory/Mathematics/Motzkin/Finite.lean) proves the remaining centers 6 through 30 with exact arithmetic. It then proves `roots_strict_log_concave` and `roots_sharp_failure` for real powers. Some internal declarations use the left index of a triple. Their center is one greater than that index.

The Comparator statement is separate from the source implementation. [Challenges/Motzkin.lean](../Challenges/Motzkin.lean) imports only Mathlib and independently defines the predicates in `MathAndTheory.Motzkin.Palomar`. Its single `sorry` marks the theorem to be proved. [Solutions/Motzkin.lean](../Solutions/Motzkin.lean) defines the same predicates and proves `MathAndTheory.Motzkin.Palomar.source_defined_result` from `Source.solution`. It does not import the Challenge. The two wrappers belong to separate checking environments because they use the same declaration names.

The [Comparator configuration](../comparator/alternating-motzkin.json) permits only `propext`, `Classical.choice`, and `Quot.sound`. Earlier native builds and source-theorem axiom checks succeeded. Those checks do not establish a final Comparator pass, final referee approval, or a fresh-clone pass for the integrated repository. The original claim that the roots increase to three is outside this formal theorem.
