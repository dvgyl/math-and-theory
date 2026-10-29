# Formal statement map

Paths below are relative to `../formalization/`; namespace prefixes are explicit. The paper uses `U_k` for the polynomial called `Counting.T k` in Lean, reserving `T` for the graph.

| Paper claim | Formal source and declaration |
|---|---|
| Ordinary dominating subsets and their cardinality weights | `LeafMode/Semantics.lean`: `LeafMode.Dominates`, `dominationPolynomial`, `coeff_dominationPolynomial` |
| Parent graph is a tree | `LeafMode/Graph.lean`: `LeafMode.graph`, `graph_isTree` |
| Added vertex has degree one; actual induced deletion | `LeafMode/Graph.lean`: `extra_degree`, `deleteLeafIso` |
| Cardinality-preserving bijection between configurations and all vertex subsets | `LeafMode/Semantics.lean`: `selectionEquiv`, `set_weight`, `dominates_iff_valid` in `LeafMode.Semantics` |
| Proposition 2, root-selected/root-absent enumeration | `LeafMode/Counting.lean`: `branchGF_true_eq`, `branchGF_false`, `branchNoU_eq`, `rootGF_eq`, `extendedGF_eq` in `LeafMode.Counting` |
| Enumeration equals the actual graph polynomial, for all n and positive k | `LeafMode/Semantics.lean`: `dominationPolynomial_root`, `dominationPolynomial_extended` |
| Graph-isomorphism invariance | `LeafMode/IsoInvariance.lean`: `LeafMode.dominationPolynomial_iso` |
| Concrete 7284/7283 vertex counts and polynomial formulas | `LeafMode/ResultCore.lean`: `tree_card`, `deleted_card`, `core_formula`, `tree_formula`, `deleted_formula` in `LeafMode.Result` |
| Correct coefficient-list arithmetic and power certification | `LeafMode/CertificateSupport.lean`: `ofList_add`, `ofList_mul`, `ofList_deriv`, `coeff_ofList`, `ode_zero`, `ode_unique`, `power_of_ode` in `LeafMode.Cert` |
| F=S^662, G=U^662, H=(1+x)^5958 | `LeafMode/FCertificate.lean`, `LeafMode/GCertificate.lean`, `LeafMode/HCertificate.lean`: `LeafMode.Cert.f_power`, `g_power`, `h_power` |
| Base-polynomial and P/Q list correspondence | `LeafMode/AlgebraCertificate.lean`: `sList_formula`, `tList_formula`; `LeafMode/Certificates.lean`: `pData_formula`, `qData_formula` |
| All weak trends, including the last coefficient against zero | `LeafMode/CertificateSupport.lean`: `trend`, `trend_sound`; `LeafMode/ShapeCertificate.lean`: `p_trend_checked`, `q_trend_checked` |
| Nonnegativity and strict/positive peaks | `LeafMode/ShapeCertificate.lean`: `p_nonneg_checked`, `q_nonneg_checked`, `p_left_checked`, `p_right_checked`, `q_left_checked`, `q_right_checked`, `p_positive_checked`, `q_positive_checked` |
| Uniqueness of inner peaks | `LeafMode/CertificateSupport.lean`: `peak_unique`; `LeafMode/Certificates.lean`: `p_unique`, `q_unique` |
| Translation under initial zero coefficients | `LeafMode/Modes.lean`: `shift_unimodal`, `shift_unique` in `LeafMode.Modes` |
| Actual graph unimodality, unique modes, all pairs excluded | `LeafMode/Result.lean`: `tree_unimodal`, `deleted_unimodal`, `tree_unique_mode`, `deleted_unique_mode`, `no_close_modes` in `LeafMode.Result` |
| Complete assembled and existential results | `LeafMode/Result.lean`: `LeafMode.Result.counterexample`, `LeafMode.Result.question_8_1` |

## Ten audited endpoints

The separate `--trust=0` audit covers exactly:

```text
LeafMode.Result.counterexample
LeafMode.Result.question_8_1
LeafMode.Result.tree_unique_mode
LeafMode.Result.deleted_unique_mode
LeafMode.coeff_dominationPolynomial
LeafMode.Cert.f_power
LeafMode.Cert.g_power
LeafMode.Cert.h_power
LeafMode.Cert.p_trend_checked
LeafMode.Cert.q_trend_checked
```

The two trend endpoints have no axiom dependencies; the other eight use only `propext`, `Classical.choice`, and `Quot.sound`. The default build and audit succeeded on 28 October 2026. All 18 scientific modules and the audit are included. The dependency lock pins the specified mathlib revision. Three style warnings remain.

## Reproduction

From `../formalization/`, after installing Lean's pinned toolchain and obtaining the pinned dependencies and compatible mathlib cache, run:

```sh
bash build.sh
```

This wrapper builds and runs the named audit with fail-closed report/axiom validation. Inspect `build.sh` and `check_axioms.py` for the exact commands and accepted report inventory. A direct diagnostic audit is `lake env lean --trust=0 Audit.lean`; printing reports alone does not enforce completeness. The checking statements describe the completed 28 October 2026 build.

The paper's Python reproducer is supplementary. It derives its coefficients rather than importing the Lean coefficient lists. Its completed exact check supports the same finite arithmetic; the Lean proof additionally verifies actual graph semantics and the assembled theorem.

`question_8_1` is a package identifier for its displayed existential theorem. It does not authenticate an external question number. The source-question and current-version comparisons remain provisional.
