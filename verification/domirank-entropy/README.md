# Independent DomiRank checks

Run from the repository root after installing [the pinned packages](../requirements.txt):

```sh
python3 verification/domirank-entropy/scripts/verify.py
```

The program constructs the graph from its edge rules. It checks all 32 edges, connectivity, and every degree. Exact matrix calculations verify a rational LDL factorization of `15I+4A` and the five-class quotient formula. Exact rational root isolation proves that all relevant numerator and denominator polynomials have no root on the closed comparison interval. Their left-endpoint signs then establish interval positivity.

The program independently inverts the full 14 by 14 matrices at both endpoints. It computes the oriented-edge covariance. Finite rational logarithm bounds reproduce all ten endpoint probability enclosures and prove an entropy gap greater than `1/10000`. An 80-decimal calculation illustrates the gap; it is not used as the sign proof.

[Logs](logs/) record the run. The [central guide](../README.md) records formal and independent-kernel checks. [Statement fidelity](../../lean/docs/domirank-entropy.md) explains the source normalization and spectral condition. These checks concern the exact graph and mathematical model, not empirical network performance.
