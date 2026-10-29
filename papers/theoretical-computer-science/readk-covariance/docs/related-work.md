# Related work on decision-tree covariance

The manuscript concerns covariance in finite Boolean decision trees under uniform independent bits. A read number counts query nodes in the entire tree. No coordinate repeats along a root-to-leaf path.

## Direct covariance results

[Wan, Wright, and Wu, *Decision Trees, Protocols, and the Fourier Entropy-Influence Conjecture*](https://doi.org/10.1145/2554797.2554806), ITCS 2014, introduced the signed tree covariance used here. Their Section 2.1 uses the same path convention and global node count. Their Lemma 1.8, also stated as Lemma 2.7, gives

\[
\mathcal C(T)\leq(k-1)\operatorname{Var}(f).
\]

Section 2.4 proposes the coefficient-one logarithmic variance replacement. The same section gives the dummy-prefix equality construction. Their definitions permit identical child functions and do not require a tree of minimum size. Thus the four-variable witness addresses their stated class of representations. It does not deny that the same function can have a different representation with lower covariance. [Author full text](https://people.eecs.berkeley.edu/~jswright/papers/readk.pdf).

[Shalev, *On the Fourier Entropy Influence Conjecture for Extremal Classes*, version 2](https://arxiv.org/abs/1806.03646v2), Section 6.2, Theorem 31, proves

\[
\mathcal C(T)\leq2\sqrt{k}\,I(f).
\]

That section proposes the logarithmic Fourier weight whose weighted sum is the potential in the present theorem. The potential is prior work. The present proof bounds absolute child covariance by a sum of minimum coordinate influences, then applies a logarithmic induction on the tree. It also gives two counterexamples to the stronger logarithmic variance proposal.

## Fourier entropy and other representation parameters

[Arunachalam, Chakraborty, Koucký, Saurabh, and de Wolf, *Improved Bounds on Fourier Entropy and Min-entropy*](https://doi.org/10.1145/3470860), 2021, give logarithmic read-number bounds for Fourier min-entropy of DNF formulas. Their read number counts terms that contain a variable. It differs from the query-node count here.

[Shmalo, *Fourier entropy of threshold functions and their compositions*, version 1](https://arxiv.org/html/2610.16069v1), Theorem 5.1, bounds Fourier entropy for unions and intersections of structured gates. Its read parameter counts relevant constituent gates. The conversion of accepting tree paths to DNF terms can increase this parameter without bound, even for a read-once tree.

Shmalo's Proposition 8.6 gives general selector identities with shared data. It does not require balanced data functions or disjoint Fourier supports. Corollaries 8.7 and 8.8 impose further hypotheses, including orthogonality conditions between neighboring branches. Arbitrary tree children need not satisfy those conditions. The general identities alone do not establish the covariance bound in the present manuscript.

[González, MacManus, and Pereyra, *Further evidence towards the Fourier Entropy-Influence conjecture*, version 2](https://arxiv.org/html/2606.00246v2), use a restriction inequality to treat further function classes. [Han, *A New Bound for the Fourier-Entropy-Influence Conjecture*](https://doi.org/10.1007/s00493-024-00133-z), 2025, bounds entropy using total influence and coordinate influences with reciprocal-logarithm weights. [Kelman, Kindler, Lifshitz, Minzer, and Safra, *Towards a Proof of the Fourier–Entropy Conjecture?*](https://arxiv.org/abs/1911.10579), study spectral concentration and low-degree entropy. These are distinct from a covariance bound in terms of query multiplicities of a given tree.

## Scope

The known dummy-prefix construction proves sharpness of the covariance estimate for powers of two. Its dictator output has zero Fourier entropy, so it gives no Fourier-entropy sharpness result. The present Lean project contains no Fourier transform, entropy, or coding theorem. The comparison above identifies differences between the cited statements; it is not a guarantee of priority.
