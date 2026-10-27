# Formal verification scope

The theorem applies to every probability distribution on the complete rankings of a finite set. For every distinct pair, the probability of one order must differ from one half by at least a common positive value ε. The conclusion is

`H(P) ≤ (1 − ε⁴/144) log(n!)`.

The formal statement includes all finite sizes, including zero and one. It does not assume independent comparisons or transitive preferred directions. It includes rankings represented by lists and by position-valued permutations.

All 20 project sources compiled with pinned Lean 4.19.0 and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Compiler warnings were treated as errors. [The source record](verification/source-checks.json) binds each source to its compiler output and log. Compiled objects are not distributed.

`PermEntropy/Verification.lean` checks five endpoint types and prints their axiom reports. It also checks the transitive axioms of all 238 project theorem declarations, including 17 private helpers. The source contains 144 explicit theorem declarations. The larger kernel count includes generated declarations.

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The theorem does not depend on an added mathematical axiom, a proof placeholder, or `native_decide`.

The main endpoints are `PermEntropy.FinDist.entropy_of_pairwise_bias_all` and `PermEntropy.FinDist.entropy_of_pairwise_bias_equiv_all`. The first uses complete ranking lists. The second uses the literal comparison event `e u < e v` for position-valued permutations.

See [README.md](README.md) for reproduction commands, research attribution, and the limits of author review. A formal proof does not establish novelty or expert peer review.
