# Attribution and dependency boundary — modern combined project

The project imports mathlib at the exact revision in `lake-manifest.json`. The 54-file NYLL import closure is bundled from source as described below. Mathlib and its transitive dependency sources and binaries are not bundled. The following adapted formal proof sources are credited separately from the mathematical novelty question.

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

The source commit is dated **2026-09-07 06:55:59 UTC**, as recorded by the inspected commit API in `audits/finish_depth.md`. The local adaptation targets the pinned Lean 4.19 APIs and proves the actual field-generation statement for a degree-p Galois extension in characteristic p. The subsequent finite elementary abelian character/compositum argument uses this standard AS correspondence. Reuse of the Hilbert-90 proof construction is resolved as prior-known work, not independent priority.

## 4. License and verification scope

The retained Apache-2.0 notices above identify the adapted sources and copyright holders. The Apache-2.0 license text is bundled at `third_party/LICENSE-APACHE-2.0.txt`; local modifications are identified in the source headers and this file. No ownership of upstream work is claimed.

Local verification reuses pinned dependency binaries. It does not assert that those binaries, either complete upstream repository, or all transitive dependency code were independently rebuilt or authenticated. Attribution and successful formal checking are also separate from originality: the project novelty verdict is recorded in `NOVELTY_AUDIT.md`, not inferred from a new port or formal proof of standard mathematics.


## 5. Same-project finite AS-tower helper

`TowerForwardFinite.lean` adapts the actual `finiteDimensional_asTower` theorem from the same project's already published continuation, `dvgyl/math-and-theory`, commit `d43158abbe80c4899814061d1f3665cf12992452` (2026-10-30 19:48:54 UTC), file `papers/mathematics/artin-schreier-depth/lean/HahnClosureForward.lean`. The exact body and statement match after the disclosed local rename; the comparison hash is recorded in `audits/complete_forward_reuse.json`. The source project credits autonomous agents and subsequent review/extension with Opus 5.5. This is explicitly reused prior formal work, under its Apache-2.0 license; the license text is retained in `third_party/LICENSE-APACHE-2.0.txt`.

The related tower-embedding method was separately compared against Yijun Yuan's `TrustworthyKedlaya/Kedlaya/TowerEmbedding.lean` at commit `f97be4372713e25a21603dec26706d8bb0cd9d24`. It already uses AS splitting, mapped minimal-polynomial divisibility and inductive lifting. The present code was drafted before that direct follow-up read and was not copied from that file, but its mathematical construction is prior-known. See `audits/complete_forward_embedding_provenance.json` and `audits/continue_construction_audit.md`.

## 6. NYLL: henselian valuation existence and uniqueness

The modern combined project vendors the 54 Lean modules in the import closure of the two used henselian results from [n-yamaguchi-0729/NYLL](https://github.com/n-yamaguchi-0729/NYLL), pinned at **`8c1b16d10afaca09e0dc72753c6575e230d31a55`**, commit time **2026-10-19 18:19:32 UTC**. The source's author attribution is **Naganori Yamaguchi (assisted by OpenAI Codex)**. Original source notices are retained. The fetched Apache-2.0 license is supplied as `vendor/NYLL_LICENSE`, with original Git blob `8dada3edaf50dbc082c9a125058f25def75e625a`.

The source closure includes the ordinary simple-root-to-factorization bridge, the actual finite norm absolute value, and uniqueness of extending valuation rings. These are substantial earlier formal results, not assumptions introduced by this project and not claimed as new contributions. `HenselianStandardBridge.lean` applies them to rational-valued valuations, proves the value-one normalization and gluing interface through its local helper modules, and then specializes to the exact Hahn valuation ring.

Original Git blob hashes were checked for all 54 files. In `NormFormula.lean`, the broad `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core` import is replaced by the two direct mathlib imports `Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed` and `Mathlib.RingTheory.Valuation.Extension`; a dated modification notice is added there. The failed first check identified those two necessary transitive dependencies, and its log is retained. No theorem in that source is weakened. The exact original/local SHA-256 values and the full patch are retained in `vendor/source_manifest.json` and `vendor/NormFormula.patch`. No other vendor modification is authorized by this provenance record without an explicit update.

## 7. Modern port and build boundary

The final combined project uses Lean **4.35.0-rc2**, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`, and mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Earlier 4.19 source attributions above identify the original local adaptations; the modern tree additionally ports changed library names, polynomial splitting APIs, Hahn support lemmas and order-class interfaces. These compatibility changes make no new mathematical claim.

The final verifier is designed to freshly compile every root production source and every vendored NYLL source, then audit every declaration by its defining module. Pinned mathlib and ordinary dependency binaries are reused. Actual completion, exact declaration counts and failure logs are supplied by the machine-generated verification report; this attribution file alone is not a successful-build claim.

## 8. Existing polynomial and power-series Gauss constructions

The final construction audit directly inspected `Polynomial.gaussNorm_mul` in [mathlib's polynomial Gauss file at the project's pinned revision](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Polynomial/GaussNorm.lean). This file credits Fabrizio Barroero, copyright 2025, under Apache-2.0. The file and basic norm were introduced in [commit 9ac601a066a9064f73d08f00b206a1a7515958b8](https://github.com/leanprover-community/mathlib4/commit/9ac601a066a9064f73d08f00b206a1a7515958b8), dated 4 June 2025, 07:53:02 UTC. The multiplicativity theorem and dominant-coefficient proof were added later, in [commit 308bf9018af623dbb38d98a1ca12ff270b27f1d2](https://github.com/leanprover-community/mathlib4/commit/308bf9018af623dbb38d98a1ca12ff270b27f1d2), dated 19 March 2026, 16:26:12 UTC. The root directly inspected both actual diffs, resolving the distinction between file and theorem introduction. The local `MLVGauss` rational additive development is integration/formalization work, not a newly discovered multiplicativity construction.

The audit also read [Tau Ceti's power-series Gauss source](https://github.com/TauCetiProject/TauCeti/blob/d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad/TauCeti/RingTheory/PowerSeries/GaussNorm.lean), which explicitly attributes its dominant-coefficient method to mathlib. These sources were identified during the post-proof comparison; this paragraph records construction overlap, not a claim that their source was directly copied into `MLVGauss`. Any earlier missing-capability statement based on the Lean 4.19 snapshot is restricted to that snapshot. The modern pinned mathlib contains the polynomial theorem.
