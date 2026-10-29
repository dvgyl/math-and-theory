# Formal source provenance

The publication copy preserves all non-comment Lean bytes, including imports,
definitions, theorem statements, and proofs, from the previously checked source.
The pinned configurations are unchanged. No new Lean compiler run is claimed
for this editorial packaging. The prior successful build and axiom audit
precede any comment-only source-context repair described below.

Only comments that asserted unverified external-source identity were repaired. The current manuscript defines its theorem independently and makes the external-source comparison conditional.

| File | Previously checked SHA-256 | Publication SHA-256 |
|---|---|---|
| `formalization/CertificateAnalysis.lean` | `ced2bd9ecd77f9d8eb93e9d8e1b57f38a037733c7437e318172d8e282c2f7bac` | `2f03be385f8a7f8245d0cc3a9682c0d2c0dc09bebd57f0af08c52be1ef966638` |
| `formalization/Conjecture.lean` | `25a2d04bb47e8040d47b03df45be8d81d703be4b6398850e7932f1b05d911db8` | `a2fb3d02f3bc45d6c0a1275efb37110a52d1394dd0b861edb8a73adb37806c51` |
| `formalization/Counterexample.lean` | `30ed875d68278058a290fbf1191a0ab0804b0e25f0d82ab3304f8ab7e245cd2c` | `de4922593217eec9156aba54fcc148b0fe39f9e22fcca6fea47664dd47070f6c` |
| `formalization/GeneralResult.lean` | `95027594371b60e1ba93eac705cb9fb44150946a0abe4994957fe0b2dd4d903b` | `a46638382e58108e3e8c3ac82d6c0d7658a239a9fcddbd1f250cae245cef9335` |
| `formalization/SourceMass.lean` | `786c9acfbcdd71fb4b977f8d5a2b0efbdf561f6ea1eb97bff9851a73e953095e` | `7a305b6d9d28f0b998c1171ac519d1c8c67e0c1c348f1298feb6ddd83dafdf6c` |

An exact comparison after removal of nested block comments and line comments found identical remaining bytes in every Lean file. The comparison preserved string contents.
