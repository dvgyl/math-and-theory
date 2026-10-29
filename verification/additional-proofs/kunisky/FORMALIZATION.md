# Formal statement map

The project has sixteen Lean modules and twelve required axiom reports. All main declarations are in namespace `Kunisky`.

| Claim | Declaration |
|---|---|
| Fair-branch mass equals the sum over leaf occurrences | `Tree.mass_eq_occurrence_sum` |
| Exact three-variable witness | `FiniteCounterexample.concrete_counterexample` |
| Witness has no tautological node | `FiniteCounterexample.noTaut223` |
| Internal predicate is false | `not_conjecture44` |
| Concentration in an actual finite refutation | `exists_concentrated_refutation` |
| Full-clause formula is minimally unsatisfiable | `fullFormula_minimallyUnsatisfiable` |
| Universal upper bound on full-clause family | `full_certificate_le` |
| Arbitrarily near the supremum | `exists_certificate_near` |
| Exact supremum `n+1` for `n ≥ 3` | `full_certificate_isLUB` |
| No universal constant | `certificate_unbounded` |
| Positive mass for minimal formulas | `Tree.mass_pos_of_minimal`, `fullFormula_mass_pos` |

`Conjecture44` is an internal predicate in `Conjecture.lean`; its name is a historical label. `not_conjecture44` proves the negation of that predicate, not the authenticity or identity of a conjecture in an external publication. The functional coalesces equal clause labels before square roots. The tree class is ordinary unrestricted resolution and includes nonregular trees. These conditions are essential.

The conventional proof and source definitions agree. Literal external definitions, proof restrictions, source quantifiers and current-version correspondence remain unverified. No historical priority, optimal Komlós constant, or existential-proof-choice conclusion is certified.

Run the commands in the README. `build.sh` requires successful compilation and exactly twelve accepted transitive axiom reports, rejects missing or malformed coverage, and allows only `propext`, `Classical.choice`, and `Quot.sound`. The accepted compiler results precede the publication copy's source-context comment-only repair. All non-comment code, theorem statements, imports, proofs, and pins remain identical. No new Lean compilation is claimed for that editorial delta.
