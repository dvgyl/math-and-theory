# Third-party source attribution

The modules `QPermanentResearch/PairMinorIdentity.lean` and `QPermanentResearch/Complement.lean`, and portions of the color-fiber and pair-grouping arguments in `QPermanentResearch/Fischer.lean` and `QPermanentResearch/WedgeNorm.lean`, are adapted or generalized from Kenta Kitamura's q-permanent proof package [KitaKen1/bapat-lal-q-permanent-lean](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b), pinned revision `4200da4fc1a132d69c23fb877795b5b72089544b`.

That package is licensed under the Apache License 2.0. Its license is included unchanged as [LICENSE-Kitamura](LICENSE-Kitamura). The changes in this project include real-valued and arbitrary-rank generalizations, a rank-three exterior norm identity, multivariate polynomial bridges and recurrences, and reductions to positive-definite rational matrices with rational parameters. Each adapted file states its origin in its header comment.

The definitions `inversionCount` and `qPermanent` in `QPermanentResearch/Basic.lean` restate those of this repository's shared q-permanent library.

Mathlib is an external dependency pinned by `lake-manifest.json`; it is not bundled.
