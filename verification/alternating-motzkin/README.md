# Verification of alternating Motzkin sums

I include an infinite Lean proof and separate finite arithmetic checks for this family. See the [paper](../../preprints/alternating-motzkin/paper.pdf) and [declaration map](../../lean/docs/alternating-motzkin.md). A finite check cannot establish the infinite theorem.

Run the independent check from the repository root with Python 3:

```sh
python3 verification/alternating-motzkin/scripts/verify.py
```

The program uses only the Python standard library. The program rejects Python optimization because its mathematical checks use `assert`. It prints a JSON report with the Python version and `status: PASS` when every comparison succeeds. A failed assertion exits with an error.

The program first counts paths with height changes −1, 0, and 1. The paths start and end at height zero and never have negative height. It then computes each alternating sum directly from its finite-sum definition. It does not generate the sums from the recursive alternating-sequence implementation in Lean.

| Check | Exact finite range |
| --- | --- |
| Path counts and alternating sums | Indices 0 through 300 |
| Agreement with the retained OEIS values | Indices 0 through 300 |
| Motzkin recurrence | Recurrence indices 1 through 299 |
| Strict integer-power inequality for the roots | Centers 6 through 100 |
| Strict reverse inequality | Center 5 |

The retained [data file](scripts/oeis-b187306.txt) contains indices 0 through 300 from the [OEIS A187306 data table](https://oeis.org/A187306/b187306.txt), retrieved on 26 October 2026. The source and retained range are stated in the file. The root comparisons use exact integers:

$$
T_n^{2(n^2-1)}>T_{n-1}^{n(n+1)}T_{n+1}^{n(n-1)}.
$$

At center five the program checks `T[5]**48 < T[4]**30 * T[6]**20`. No floating-point root or logarithm is used. These checks do not prove the recurrence or the path interpretation at every index. Lean proves the infinite root result from the source recurrence and finite sum.

The Lake project pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. With that toolchain installed and the pinned dependencies available, run the following commands from the repository root:

```sh
cd lean
lake build MathAndTheory.Mathematics.Motzkin.Source
lake env lean Challenges/Motzkin.lean
lake env lean Solutions/Motzkin.lean
```

The Challenge check is expected to report its one intentional `sorry`. The Solution must compile without a proof hole. Do not import both wrapper modules into one Lean environment. They independently declare the same names for statement comparison.

To inspect the principal theorem's axioms from the `lean` directory, run:

```sh
lake env lean --stdin <<'LEAN'
import MathAndTheory.Mathematics.Motzkin.Source
#print axioms MathAndTheory.Motzkin.Source.solution
#print axioms MathAndTheory.Motzkin.Source.finite_sum_roots_strict_log_concave
#print axioms MathAndTheory.Motzkin.Source.finite_sum_roots_sharp_failure
LEAN
```

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. An axiom report checks logical dependencies. It does not, by itself, check correspondence with the published problem; that correspondence is explained in the declaration map.

The repository's Comparator command uses the independent Challenge and Solution. It also requests the bundled NanoDa and con-ron kernel checks. Run it from `lean` on a supported Linux environment with `bwrap` and the required toolchain executables:

```sh
./scripts/verify-comparator.sh comparator/alternating-motzkin.json
```

A successful native Lean build does not replace this command. The [central verification record](../summary.md) gives the recorded build, axiom, Comparator, and finite-computation results.

For the paper, run Tectonic from the repository root:

```sh
tectonic preprints/alternating-motzkin/paper.tex
```

Inspect the resulting PDF after compilation. Compilation alone does not check page layout, mathematical correctness, or bibliographic accuracy.

The [preprint guide](../../preprints/alternating-motzkin/README.md) gives the related results and source comparisons. I make no priority claim.

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.
