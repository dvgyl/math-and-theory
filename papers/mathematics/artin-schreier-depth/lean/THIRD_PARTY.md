# Attribution and dependency boundary

The project imports mathlib at the exact revision in `lake-manifest.json`. Dependency sources and binaries are not bundled with this package. The following adapted formal proof sources are credited separately from the mathematical novelty question.

## 1. Tau Ceti: additive splitting-field construction

The splitting-field proof pattern in `AdditiveGalois.lean` was adapted from:

[The Tau Ceti contributors, `TauCeti/FieldTheory/ArtinSchreier/Additive.lean`, commit `343f4606bc2693cfa7e778296dd0fe4dbb041a39`](https://github.com/TauCetiProject/TauCeti/blob/343f4606bc2693cfa7e778296dd0fe4dbb041a39/TauCeti/FieldTheory/ArtinSchreier/Additive.lean).

Original notice:

```text
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
```

The present development changes that pattern substantially for a finite linearized coefficient family, an algebraically closed constant field, the pinned older mathlib API and a perfect-base variant. Its source header records the adaptation. The polynomial/Ore/translation development was written against Lean 4.19 mathlib. These are formalizations of known algebraic facts, with no mathematical novelty claim.

The upstream Apache-2.0 license is reproduced in `third_party/LICENSE-APACHE-2.0.txt`, fetched at the pinned Tau Ceti commit. An upstream NOTICE-file request returned 404 on 2026-10-30.

## 2. TrustworthyKedlaya: Hahn Frobenius and AS-root coefficients

The following sources were inspected and adapted at exact commit **`f97be4372713e25a21603dec26706d8bb0cd9d24`** of [YijunYuan/TrustworthyKedlaya](https://github.com/YijunYuan/TrustworthyKedlaya):

- [Kedlaya/Frobenius.lean](https://github.com/YijunYuan/TrustworthyKedlaya/blob/f97be4372713e25a21603dec26706d8bb0cd9d24/TrustworthyKedlaya/Kedlaya/Frobenius.lean) → `HahnFrobenius.lean`.
- [Kedlaya/ArtinSchreierNeg.lean](https://github.com/YijunYuan/TrustworthyKedlaya/blob/f97be4372713e25a21603dec26706d8bb0cd9d24/TrustworthyKedlaya/Kedlaya/ArtinSchreierNeg.lean) → the inverse-Frobenius coefficient construction and elementary `finsum` splitting pattern in `HahnASRoot.lean`.

The retained source notices read:

```text
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
```

The local changes, made 2026-10-30, include Lean 4.19/mathlib API compatibility, namespace changes, iterated Frobenius and truncation lemmas. The local AS-root module supplies general summability and real support-closure arguments for arbitrary rational Hahn supports over perfect coefficient fields. Its header distinguishes these local additions from the reused coefficient construction. This description records formal theorem scope and code provenance; the classical AS root formula and Frobenius identity are not claimed as new mathematics.

## 3. TrustworthyKedlaya: additive Hilbert 90 and AS generators

The proof of `exists_artinSchreier_generator_of_prime_degree` in `OkutsuDepth.lean` adapts the trace-one, weighted-sum additive-Hilbert-90 construction from:

[Yijun Yuan, `Kedlaya/ArtinSchreierGalois.lean`, `TrustworthyKedlaya.exists_artinSchreier_generator`, at the same pinned commit](https://github.com/YijunYuan/TrustworthyKedlaya/blob/f97be4372713e25a21603dec26706d8bb0cd9d24/TrustworthyKedlaya/Kedlaya/ArtinSchreierGalois.lean).

Original notice retained in the local source attribution:

```text
Copyright (c) 2026 Yijun Yuan.
Released under Apache 2.0.
```

The source commit is dated **2026-09-07 06:55:59 UTC**, as recorded by the commit API when the source was inspected. The local adaptation targets the pinned Lean 4.19 APIs and proves the actual field-generation statement for a degree-p Galois extension in characteristic p. The subsequent finite elementary abelian character/compositum argument uses this standard AS correspondence. Reuse of the Hilbert-90 proof construction is resolved as prior-known work, not independent priority.

## 4. License and verification scope

The retained Apache-2.0 notices above identify the adapted sources and copyright holders. The Apache-2.0 license text is bundled at `third_party/LICENSE-APACHE-2.0.txt`; local modifications are identified in the source headers and this file. No ownership of upstream work is claimed.

Local verification reuses pinned dependency binaries. It does not assert that those binaries, either complete upstream repository, or all transitive dependency code were independently rebuilt or authenticated. Attribution and successful formal checking are also separate from originality: the novelty assessment is stated in the manuscript and is not inferred from a new port or formal proof of standard mathematics.
