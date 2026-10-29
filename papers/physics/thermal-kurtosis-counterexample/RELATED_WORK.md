# Related work on thermal current cumulants

The result concerns the fourth-to-second spectral heat-cumulant ratio of a finite classical thermal Markov model. It supplies an exact counterexample to Eq. (19) of [Ptaszyński, *Bounds on skewness and kurtosis of steady-state currents*](https://doi.org/10.1103/PhysRevE.106.024119), 2022. The model follows the finite tilted-generator formulation in Eqs. (63)–(70). The row-generator convention used here is the transpose of the paper's column-generator convention. The eigenvalues are unchanged by transposition.

## Established models and methods

[Segal, *Current fluctuations in quantum absorption refrigerators*](https://doi.org/10.1103/PhysRevE.97.052145), 2018, studies three-level thermal systems with selective bath couplings. The paper derives a tilted generator and a cubic characteristic equation, then calculates mean current and noise. The present model uses that established thermal-triangle framework. Its two lower transitions share one cold temperature, and both cold heat transfers are counted.

[Gerry and Segal, *Random walks on modular chains: Detecting structure through statistics*](https://doi.org/10.1103/PhysRevE.108.024135), 2023, exhibit negative fourth cumulants in biased classical chains. Their uniform directional bias does not itself give the static-energy, bath-resolved thermal realization required by Eq. (19). Ptaszyński's target paper also allows negative fourth cumulants in general unicyclic networks. The distinction here is the explicit realization with two positive-temperature baths and local detailed balance.

## Related cumulant bounds

[Holubec and Novotný, *Effects of noise-induced coherence on the fluctuations of current in quantum absorption refrigerators*](https://doi.org/10.1063/1.5096275), 2019, study fourth current cumulants in classical and coherent regimes of a refrigerator model. Their fourth-to-second-squared normalization has the same sign as the fourth cumulant when the second cumulant is positive.

[Saryal, Friedman, Segal, and Agarwalla, *Thermodynamic uncertainty relation in thermal transport*](https://doi.org/10.1103/PhysRevE.100.042101), 2019, study thermal transport, including quantum and non-Markovian settings. Negative cumulants in those settings do not by themselves settle the proposed classical thermal Markov inequality.

[Ptaszyński and Esposito, *Critical heat current fluctuations in Curie-Weiss model in and out of equilibrium*](https://doi.org/10.1103/PhysRevE.111.034125), 2025, study heat-current fluctuations near phase transitions, including equilibrium fourth cumulants. The present counterexample is out of equilibrium.

[Salazar, *Thermodynamic Skewness Relation From Detailed Fluctuation Theorem*](https://doi.org/10.1103/PhysRevE.106.L042101), 2022, concerns entropy-production skewness. [Delvenne and Van Brandt, *Moments of Entropy Production in Dissipative Devices*](https://doi.org/10.1103/jqsx-ycjv), 2025, gives entropy-production moment bounds under its stated assumptions. These are distinct from the fourth spectral heat cumulant here. Their hypotheses cannot be transferred to general multistate current dynamics without proof.

## Scope of the counterexample

The bath rates are nonnegative. Unsupported bath channels are absent in both directions. Every total off-diagonal rate is positive. The model has fixed energies and temperatures, with no mechanical or chemical driving.

The fourth spectral cumulant is negative, while the third is positive. Thus the witness refutes the stated thermal kurtosis proposal in its spectral formulation. It does not refute the separate two-bath skewness conjecture. It proves no minimal-state result, optimal negative bound, or robustness to added bath channels.

Lean verifies the finite matrices, local detailed balance, complex spectrum, smooth dominant branch, and derivatives. It does not formalize the stochastic long-time theorem that identifies the branch with a cumulant generating function. The result makes no empirical validation or priority claim.
