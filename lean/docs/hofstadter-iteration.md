# Hofstadter iteration formalization

This family proves a late-iterate counterexample for every parameter `k≥4`. It also proves exact finite witnesses that establish incomparability of `F_4^9` and `F_5^10`.

Read the [paper](../../preprints/hofstadter-iteration/paper.pdf), [source and prior-work guide](../../preprints/hofstadter-iteration/README.md), or [verification guide](../../verification/hofstadter-iteration/README.md).

## Modules and namespaces

| File | Namespace | Role |
| --- | --- | --- |
| [Counterexample.lean](../MathAndTheory/Mathematics/Hofstadter/Counterexample.lean) | `MathAndTheory.Hofstadter` | Recursive functions, table certification, and exact witnesses |
| [Foundation.lean](../MathAndTheory/Mathematics/Hofstadter/Foundation.lean) | `MathAndTheory.Hofstadter` | Monotonicity, inverse map, and iterate equivalence |
| [Family.lean](../MathAndTheory/Mathematics/Hofstadter/Family.lean) | `MathAndTheory.Hofstadter.Family` | Inverse-orbit recurrence and the uniform counterexample family |

These modules require `Std`, not Mathlib. The independent [Challenge](../Challenges/Hofstadter.lean) defines the recursive functions without importing the solution. Its target is `HofstadterChallenge.result`. The matching [Solution](../Solutions/Hofstadter.lean) proves that for every `k≥4` there is an input with

`iter (F (k+1)) (2k+2) n < iter (F k) (2k+1) n`.

The [Comparator configuration](../comparator/hofstadter-iteration.json) selects this target.

## Source correspondence

The recurrence in [Letouzey, Li, and Steiner, section 7](https://arxiv.org/html/2410.00529v2) is `F_k(0)=0` and `F_k(n+1)=n+1−F_k^k(n)`. Superscripts mean repeated composition. The source conjecture concerns `j>2k`.

The definition `iter` is repeated composition. `boundedF` defines the infinite function by well-founded recursion. It carries the bound `F_k(n)≤n` needed for recursive calls. `F_succ` proves the source recurrence for this function. The infinite function is not defined by a finite table.

`ValidTable` states the recurrence at every index of a finite table. `validTable_correct` proves that any such table agrees with the infinite function on its range. The two supplied tables pass kernel-reduced `decide`. This connects each finite computed value to the actual recursively defined function.

## Theorem map

Names from `Counterexample.lean` and `Foundation.lean` have prefix `MathAndTheory.Hofstadter`. Names from `Family.lean` have prefix `MathAndTheory.Hofstadter.Family`. In the table, the Family module starts with the row for initial function values.

| Claim | Declaration |
| --- | --- |
| Infinite function and recurrence | `boundedF`, `F`, `F_le`, `F_zero`, `F_succ` |
| Finite table correspondence | `ValidTable`, `validTable_correct`, `table4_correct`, `table5_correct` |
| Values at 132 | `counterexample_left`, `counterexample_right` |
| Values at 36 | `reverse_witness_left`, `reverse_witness_right` |
| Finite incomparability and conjecture disproof | `pointwise_incomparable`, `lateIterateOrderConjecture_false` |
| Function and iterate monotonicity | `F_step`, `F_mono`, `iter_F_mono`, `iter_F_step` |
| Inverse map | `L`, `F_L`, `F_L_succ` |
| Inverse equivalences | `F_galois`, `iter_galois`, `iter_F_iter_L` |
| Initial function values | `F_initial`, `F_boundary`, `iter_F_initial`, `iter_F_boundary` |
| Inverse-orbit recurrence | `L_orbit_recurrence` |
| Shared initial orbit | `left_initial_step`, `right_initial_step`, `initial_orbits_equal` |
| Exact gap `k−3` | `recurrence_gap`, `inverse_iterate_gap` |
| Explicit input and strict violation | `familyWitness`, `general_counterexample` |
| Uniform existential theorem | `infinitely_many_parameter_counterexamples` |

The inverse relation is `F_k^r(n)≤m` if and only if `n≤L_k^r(m)`. The proof derives it from the recurrence. The family theorem then proves

`L_(k+1)^(2k+2)(k+3)=L_k^(2k+1)(k+3)+(k−3)`.

For `k≥4`, the positive gap supplies the desired input at `j=2k+1`. No inverse formula or recurrence property is assumed as an axiom.

## Formal scope and prior results

The inverse relations and earlier order comparisons are known ingredients. The new claim is the late-iterate failure and its parameter family. The inspected same-day HAL preprint and Rocq source concern distinct index ranges; the [paper guide](../../preprints/hofstadter-iteration/README.md) records the comparison and its limits.

The modules and Solution compile under Lean 4.35.0. The uniform theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. Comparator replay has passed through Lean, NanoDa, and con-ron for the selected Challenge/Solution statement. This is a statement and kernel check, not a claim of expert review or novelty. See the [central verification record](../../verification/README.md) for the recorded run and review status.

The uniform theorem gives one input for every `k≥4`. It does not give infinitely many violating inputs for each fixed `k`.
