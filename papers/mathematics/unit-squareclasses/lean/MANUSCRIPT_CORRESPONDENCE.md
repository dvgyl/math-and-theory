# Manuscript-to-Lean correspondence

Prepared on 2026-10-30 UTC. This document identifies the actual quantifiers and proof components; it is not a historical novelty verdict. The replay record in [../verification/](../verification/) gives the build status and exact source hashes.

## Actual final statement

The strongest endpoint is:

`UnitSquareclass.algebraic_represented_unit_squareclasses_card_le_lattice_rank`

Its field is any characteristic-zero field `K` algebraic over the rationals. Total reality is expressed by the statement that every ring embedding `K →+* ℂ` has zero imaginary part on every element. Its ambient space `V` is a finite-dimensional `K`-vector space, and its integral module is an actual `Submodule (𝓞 K) V`. The integral action is compatible with the field action through `IsScalarTower (𝓞 K) K V`.

The form is a symmetric `LinearMap.BilinForm K V`. For every complex embedding and every nonzero vector, the real part of the embedded diagonal value is strictly positive. Every diagonal value on the integral module is integral over `ℤ`.

For **every finite index type `I`**, every family `u : I → (𝓞 K)ˣ` of actual integer-ring units, every family of actual representations in the module, and the condition

`∀ i j, i ≠ j → ∀ w : (𝓞 K)ˣ, u j ≠ w ^ 2 * u i`,

the conclusion is

`Fintype.card I ≤ Module.finrank K (Submodule.span K (L : Set V))`.

This condition is exactly pairwise distinctness modulo squares of **all** integer-ring units. The represented units are automatically totally positive by the positivity hypothesis; no assumption that all units are positive is made. The conclusion uses the field-span of the actual integral module, so an unnecessarily large ambient vector space does not weaken the bound.

The finite-family formulation is equivalent to “the set of represented unit squareclasses has size at most the rank”: if that assertion failed, one could select rank-plus-one distinct represented classes and representatives. Thus the endpoint is not a statement only about a preselected special family, linearly independent representatives, or a pre-assumed finite collection of shells.

## Assumptions that are absent

The final endpoint assumes no finite generation or freeness of the integral module, no finite degree of `K`, no supplied ordered-field structure on `K`, no classicality of the bilinear pairing, no shell finiteness, no reflection closure, no descent field, and no conclusion about a smaller-field lattice. Those properties needed during the proof are constructed or proved internally.

The manuscript initially states the result for finitely generated torsion-free lattices. Such lattices are covered by the stronger formal endpoint. The manuscript realizes a lattice as a submodule of its quadratic space; this is also how the formal statement is represented. It does not assume a free integral basis. The symmetric-bilinear presentation agrees with the usual quadratic-form presentation in characteristic zero through polarization, with `Q(x) = B(x,x)` and `2B(x,y) = Q(x+y)-Q(x)-Q(y)`.

## Proof correspondence

| Manuscript component | Lean declaration(s) | Scope and correspondence |
|---|---|---|
| A field square root of an integer unit is an integer unit | `exists_integral_unit_of_sq_eq`, `exists_integral_unit_of_ratio_sq` | Proves integrality of both the root and its inverse, then constructs an actual unit of `𝓞 K`. It does not assume that field and unit squareclasses agree. |
| Polar integrality from diagonal integrality | `two_mul_bilin_isIntegral` | Expands the polar identity. Only `B(x,x)` is assumed integral. |
| Unit reflection preserves the lattice and the quadratic value | `integralReflect_mem`, `integralReflect_norm`, `integralReflect_mem_shell` | The division by the norm is implemented using the inverse of an actual integer-ring unit. |
| Fixed-value shell finiteness over a number field | `finite_arithmetic_shell` | Derives bounded integral polar coordinates at every embedding and proves those coordinates injective on the span. Applies mathlib's actual bounded-conjugates finiteness theorem. |
| A generic functional exists | `exists_functional_ne_zero` | Constructs it by finite induction, avoiding finitely many forbidden scalar parameters. No genericity premise remains. |
| Positive minimum in each shell | `exists_positive_minimum` | Uses finiteness, negation closure, and the constructed nonvanishing functional. |
| Distinct shell representatives have nonpositive pairing | `pairing_nonpos_of_reflection_minima` | Implements the two reflection inequalities and the strict Cauchy contradiction over the actual ordered field. |
| Nonpositive pairings in a common positive halfspace imply independence | `linearIndependent_of_pairwise_nonpos` | Splits coefficients into nonnegative positive and negative parts; their supports have zero product on the diagonal. |
| The number-field theorem | `represented_unit_squareclasses_card_le_finrank` and `totally_real_represented_unit_squareclasses_card_le_lattice_rank` | Discharges every geometric shell premise from the actual arithmetic module and units. The latter uses the standard `NumberField.IsTotallyReal` class and positivity at every real embedding. |
| Finite-data descent | `exists_numberField_containing`, `subfieldBilin`, `subfieldUnit`, `subfieldCoords`, `algebraic_represented_unit_squareclasses_card_le_finrank` | Chooses a finite subfield containing the Gram coefficients, coordinates of the chosen representations, and unit values. Constructs its form, integral module, and actual unit representatives. |
| Every embedding of the finite subfield extends | `extend_complex_embedding`, `totally_real_intermediate`, `positive_intermediate` | Uses algebraicity of the ambient field; does not assume the finite subfield already has the desired reality or positivity. |
| Distinctness survives descent | `distinct_unit_squareclasses_descend` | Applies the actual homomorphism between integer-unit groups to a hypothetical smaller-field square relation. |
| The bound uses intrinsic lattice rank | `algebraic_represented_unit_squareclasses_card_le_lattice_rank` | Restricts the form and integral module to their field-span and proves nonzero vectors remain nonzero in the ambient space. |

## Differences in proof implementation

The manuscript bounds a polar coordinate using positivity of `Q(x+e)` and `Q(x-e)`, obtaining `|σ(2B(x,e))| ≤ σ(Q(x))+σ(Q(e))`. The formal arithmetic file uses a determinant identity and a Cauchy inequality to obtain the sufficient bound `1 + 4‖φ(Q(x))‖‖φ(Q(e))‖`. Both prove the same fixed-value shell is finite; neither changes the arithmetic theorem or assumes finiteness as a substitute for that proof.

The manuscript's infinite-field descent may include a basis among the generators of the descended lattice. The formal descent only needs the finitely many represented vectors as integral generators, because the number-field theorem bounds by the dimension of an ambient finite-dimensional space. The final intrinsic-rank wrapper first restricts that ambient space to the original lattice's field-span. These choices give the same bound and additionally remove the need to assume that the original integral module is finitely generated.

The manuscript describes selection of a smallest positive functional value. The formal proof stores the resulting comparison with the absolute value of every functional value in the shell. Negation closure establishes the equivalence of these formulations.

## Edge cases

- **Rank zero:** no nonzero unit can equal the quadratic value at zero. The actual shell nonzero proof uses the unit's nonzero field image. No positive-rank hypothesis is imposed.
- **Rank one:** the same theorem applies; no rank-at-least-two lemma is used in the final argument.
- **Empty indexed family:** permitted. The geometric representative and finite-set arguments remain valid, and the conclusion is `0 ≤ rank`.
- **Repeated exact values or equal squareclasses:** excluded only by the stated pairwise distinctness condition. No hidden distinctness assumption occurs in the shell construction.
- **Nonfree integral modules:** permitted, because generators are used only in the number-field intermediate step and no integral basis is selected.
- **Nonclassical forms:** permitted, because the reflection integrality proof uses `2B`, not integrality of `B`.
- **Infinite algebraic fields:** covered by actual finite-data descent. The proof never assumes norm shells over such a field are finite.

## Verification boundary

The final build compiles the proof source using the pinned Lean compiler and pinned cached mathlib/dependency libraries. Every advertised endpoint is included in `AxiomAudit.lean`. The allowed dependencies are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no custom mathematical axiom is allowed. The verifier records exact source hashes and fails on any source change during its run.

This establishes the formal theorem with the displayed arithmetic hypotheses. It does not establish novelty, historical priority, expert acceptance, or the research significance of the result; those are separate questions.
