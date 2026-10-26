# Verify the best-of-n family

This guide separates exact finite computations from the universal Lean proof. Read the [paper](../../preprints/best-of-n/paper.pdf) and [theorem map](../../lean/docs/best-of-n.md) for the claims and their formal statements.

## Reproduce the computations

From the repository root, run:

```sh
python3 verification/best-of-n/scripts/verify.py
python3 verification/best-of-n/scripts/extension.py
```

Both programs use only the Python standard library. They write JSON to standard output and exit unsuccessfully if an assertion fails. They do not change the repository. Redirect standard output to a file if a persistent run record is needed.

`verify.py` independently enumerates all sixteen pairs of draws from `(2/5,1/5,1/5,1/5)`. It computes the selected law and half-credit win rate with exact rational arithmetic. It encloses each logarithm with a finite series and a rigorous geometric remainder. The resulting certified interval is

`0.002375504921683 < ell(W)−D < 0.002375504921686`.

The stronger finite bound `1/500` passes this independent rational check. The main Lean theorem uses the separately proved bound `1/2445`.

`extension.py` checks the new construction `a=min(δ,1/(8(n+1)))`, `T=a^n/(48(n+1))`, `m=floor((1−a)/T)+1`, and `h=(1−a)/m`. It verifies the exact probability cap and normalization of the reference law.

For a specified response, each draw belongs to one of three groups: lower reward, equal reward, or higher reward. The script enumerates the `3^n` ordered group tuples. It sums their exact product masses when the specified response is the maximum. It then compares this independent sum with the cumulative-probability formula.

| Budget and cap | Reference responses | Selected responses checked |
| --- | ---: | ---: |
| `n=2`, `δ=1/2` | 79,490 | All 79,490 |
| `n=2`, `δ=1/100` | 1,425,602 | All 1,425,602 |
| `n=3`, `δ=1/2` | 6,094,850 | 27 |
| `n=4`, `δ=1/10` | 599,040,002 | 27 |
| `n=5`, `δ=1/100` | 2,851,200,000,002 | 27 |

For both budget-two distributions, selected normalization and the win rate are checked exactly. Floating-point divergence calculations give positive gaps of about `0.0003081992` and `0.00001893972`. These numerical values are diagnostics. The script uses exact group aggregation; it does not enumerate every raw response tuple. For budgets three through five, it checks the specified response samples only.

## Reproduce the formal checks

Install the toolchain in `lean/lean-toolchain` and obtain the pinned dependencies. From the repository root, run:

```sh
cd lean
lake exe cache get
lake build MathAndTheory.TheoreticalCS.BestOfN.Extension Solutions.BestOfN
lake env lean Solutions/BestOfN.lean
```

The last command prints the axiom lists for both selected Solution theorems. The permitted list is `propext`, `Classical.choice`, and `Quot.sound`. The proof modules and Solution have no proof holes. The independent Challenge has the permitted target holes and is not part of the proved library.

In an environment with `bwrap` and the kernels bundled with Lean 4.35.0, run the statement comparison and independent kernel replay from `lean/`:

```sh
bash scripts/verify-comparator.sh comparator/best-of-n.json
```

The [Comparator configuration](../../lean/comparator/best-of-n.json) selects both the finite disproof and the every-budget theorem. The [central verification record](../README.md) states the recorded Comparator and review status. Compilation and standard axiom lists alone are not a Comparator result.

## Limits

The finite programs test the cases stated above. The Lean theorem proves the universal claim for every `n≥2` and `δ>0`. Neither a finite computation nor a successful kernel check establishes historical priority, a sharp replacement curve, or expert peer review. This paper has NOT been peer reviewed.
