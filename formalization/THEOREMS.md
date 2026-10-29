# Formal statement map

This map describes source statements. The current module-system port is uncompiled. Earlier compiler records do not certify these bytes.

Main declarations are in namespace `PowerRank`. Companion declarations are in `PowerRank.Companion`.

| Mathematical statement | Source and declaration |
|---|---|
| Actual shift-polynomial recurrence action | `MixedComponents.polyAction_apply` |
| Eventual complex minimality with every root multiplicity | `RankPrinciple.minimalCharacteristic_expPoly_sum` |
| Literal positive integer sequence and rank thirteen | `MainProperties.mainInteger_pos`, `mainSequence_eq_intCast`, `mainSequence_recurrenceRank` |
| Complete expansion of every termwise power | `MainPowers.mainPowerSequence_expansion` |
| Every power's complete minimal characteristic polynomial | `MainPowers.mainPower_minimalCharacteristic` |
| Exact cubic-minus-square-count rank | `SquareCounting.mainPower_rank_cubic_squareCorrection` |
| Strict square endpoints and exact floor formula | `SquareFloor.squareCorrection_floor` |
| Uniform square-root correction with error at most two | `SquareEstimate.mainPower_sqrt_error` |
| No eventual quasipolynomial with real constituent polynomials | `Nonquasipolynomial.mainPower_not_eventuallyQuasipolynomial` |
| Integral polynomial with monic leading term and nonzero constant coefficient | `IntegralFields.integralPowerCharacteristic_map`, `integralPowerCharacteristic_monic`, `integralPowerCharacteristic_constant_ne_zero` |
| Equal rational, real, and complex eventual ranks | `IntegralFields.mainPower_rational_real_ranks` |
| Literal integer-coefficient forward recurrence from index zero | `MainTheorem.mainPower_integral_forward_recurrence` |
| Zeroth and first power polynomial boundaries | `MainTheorem.mainPower_zero_characteristic`, `mainPower_first_characteristic` |
| Assembled main theorem | `MainTheorem.main_result` |

`EventuallyQuasipolynomial` requires a positive integer period, one real polynomial for each residue, and a common threshold. Each polynomial is evaluated at the original integer argument. The proof excludes this full definition.

`recurrenceRankOver f u` restricts the recurrence coefficients to the field embedded by f into the complex numbers. The sequence and eventual-recurrence convention are the same. Injectivity preserves polynomial degrees. The integral minimal polynomial supplies a recurrence over every characteristic-zero subfield of the complex numbers.

No theorem assumes a finite computation as an infinite rank assertion. The final audit imports the complete source closure and requests 25 endpoint axiom reports.

## Companion family

| Mathematical statement | Source and declaration |
|---|---|
| Literal positive integer sequence | `CompanionExpansion.sequence_literal`, `naturalSequence_pos` |
| Unique normal representatives and exact count | `CompanionCompositions.normalComposition_card`, `CompanionBases.complexBase_injective` |
| Full positive-coefficient power expansion | `CompanionExpansion.powerSequence_expansion`, `coefficient_pos` |
| Every power's complete minimal characteristic polynomial | `CompanionFamily.power_minimalCharacteristic` |
| Exact rank for all powers and every initial rank r >= 3 | `CompanionFamily.all_r_power_rank`, `all_r_sequence_rank` |
| Monic integral minimal polynomial with nonzero constant coefficient | `CompanionFamily.integralCharacteristic_map`, `integralCharacteristic_monic`, `integralCharacteristic_constant_ne_zero` |
| Integral forward recurrence from index zero | `CompanionFamily.integral_forward_recurrence` |
| Equal rational, real, and complex eventual ranks | `CompanionFamily.power_ranks_over_subfield` |
| Zeroth-power polynomial T-1 | `CompanionFamily.zero_power_characteristic` |
| Pairwise distinct profiles as d varies | `CompanionFamily.power_rank_functions_injective` |
| Distinct odd-prime lists of every finite length | `CompanionExistence.oddPrimes_exist` |
| Infinitely many profiles at each r >= 3 | `CompanionExistence.every_rank_has_infinitely_many_profiles` |
| Assembled companion theorem | `CompanionFamily.family_result` |

The generating function, eventual polynomial degree and leading coefficient, and simplified rank-three examples are outside this formal package. The manuscript gives their conventional proofs.
