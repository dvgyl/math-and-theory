# Formal source provenance

The publication copy preserves all non-comment Lean bytes, including imports,
definitions, theorem statements, and proofs, from the previously checked source.
The pinned configurations are unchanged. No new Lean compiler run is claimed
for this editorial packaging. The prior successful build and axiom audit
precede any comment-only source-context repair described below.

Only comments that asserted unverified external-source identity were repaired. The current manuscript defines its theorem independently and makes the external-source comparison conditional.

| File | Previously checked SHA-256 | Publication SHA-256 |
|---|---|---|
| `formalization/OrderedAllocationReduction.lean` | `98fbc8b20c1eb589cb1ceae39196ad2f3d52e84e4f93a3d9f877b43b8ff3f6c2` | `16e400f22d5157d16118f42da413e4d30bd17fdaf50c94d61701bab2a800f665` |

An exact comparison after removal of nested block comments and line comments found identical remaining bytes in every Lean file. The comparison preserved string contents.
