/-
Check the transitive axioms of the order-five, four-block, and exceptional-vector Gyires developments.
Run from lean/ after the library build:
  lake env lean -j1 ../verification/gyires-circulant-five/AxiomAudit.lean
The audit checks the listed statements and every declaration in this family.
-/
module

import MathAndTheory.Mathematics.GyiresCirculant5.Main
import Solutions.GyiresCirculant5
import MathAndTheory.Mathematics.Gyires.ExceptionalBoundaryChecks

-- The theorems compared with `Challenges/GyiresCirculant5.lean`
#print axioms MathAndTheory.GyiresCirculant5.gyires_ratio
#print axioms MathAndTheory.GyiresCirculant5.gyires_ratio_eq_iff
#print axioms MathAndTheory.GyiresCirculant5.gyires_denominator_pos
#print axioms MathAndTheory.GyiresCirculant5.gyires_homogeneous
#print axioms MathAndTheory.GyiresCirculant5.gyires_homogeneous_eq_iff
#print axioms MathAndTheory.GyiresCirculant5.strong_inequality
#print axioms MathAndTheory.GyiresCirculant5.strong_inequality_eq_iff
#print axioms MathAndTheory.GyiresCirculant5.strong_margin
#print axioms MathAndTheory.GyiresCirculant5.strong_margin_attained
#print axioms MathAndTheory.GyiresCirculant5.strong_margin_sharp

#print axioms MathAndTheory.GyiresExceptional.strong
#print axioms MathAndTheory.GyiresExceptional.gram_eq_iff
#print axioms MathAndTheory.GyiresExceptional.gyires
#print axioms MathAndTheory.GyiresExceptional.gyires_eq_iff
#print axioms MathAndTheory.GyiresFourBlock.contractions
#print axioms MathAndTheory.GyiresFourBlock.margin
#print axioms MathAndTheory.GyiresFourBlock.gyires
#print axioms MathAndTheory.GyiresFourBlock.gyires_eq_iff
#print axioms MathAndTheory.Gyires.Bernoulli.probability_central_likelihood
#print axioms MathAndTheory.Gyires.Bernoulli.one_le_central_likelihood
#print axioms MathAndTheory.Gyires.Bernoulli.likelihood_norm_le_central
#print axioms MathAndTheory.Gyires.Bernoulli.central_likelihood_eq_one_iff
#print axioms MathAndTheory.Gyires.Bernoulli.likelihood_norm_eq_of_deterministic
#print axioms MathAndTheory.Gyires.Bernoulli.column_class_bounds

-- Section 2 of the paper: products, the permanent polynomial, the Gram comparison
#print axioms MathAndTheory.GyiresCirculant5.circ_mul_transpose
#print axioms MathAndTheory.GyiresCirculant5.transpose_mul_circ
#print axioms MathAndTheory.GyiresCirculant5.circ_mul_self
#print axioms MathAndTheory.GyiresCirculant5.permanent_succ
#print axioms MathAndTheory.GyiresCirculant5.permanent_circ
#print axioms MathAndTheory.GyiresCirculant5.PermanentGram.permanent_mul_transpose
#print axioms MathAndTheory.GyiresCirculant5.PermanentGram.permanent_gram_add_ge
#print axioms MathAndTheory.GyiresCirculant5.conv_permanent_le_gram

-- Section 4: affine symmetry and the chambers
#print axioms MathAndTheory.GyiresCirculant5.P5_affine
#print axioms MathAndTheory.GyiresCirculant5.gram_affine
#print axioms MathAndTheory.GyiresCirculant5.conv_affine
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_affine
#print axioms MathAndTheory.GyiresCirculant5.gyiresDefect_affine
#print axioms MathAndTheory.GyiresCirculant5.affine_bijective
#print axioms MathAndTheory.GyiresCirculant5.order_affine_cover
#print axioms MathAndTheory.GyiresCirculant5.order_affine_cover_unique
#print axioms MathAndTheory.GyiresCirculant5.exists_canonical_chamber
#print axioms MathAndTheory.GyiresCirculant5.canonical_chamber_of_monotone
#print axioms MathAndTheory.GyiresCirculant5.sortedGaps_nonneg
#print axioms MathAndTheory.GyiresCirculant5.nonneg_of_canonical_chambers
#print axioms MathAndTheory.GyiresCirculant5.constant_of_zero_of_canonical_chambers

-- Section 4: the chamber certificate
#print axioms MathAndTheory.GyiresCirculant5.P5_add_constant
#print axioms MathAndTheory.GyiresCirculant5.gram_add_constant
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_add_constant
#print axioms MathAndTheory.GyiresCirculant5.chamberPoly0_eval
#print axioms MathAndTheory.GyiresCirculant5.chamberPoly1_eval
#print axioms MathAndTheory.GyiresCirculant5.chamberPoly2_eval
#print axioms MathAndTheory.GyiresCirculant5.chamberPoly3_eval
#print axioms MathAndTheory.GyiresCirculant5.chamberPoly4_eval
#print axioms MathAndTheory.GyiresCirculant5.chamberPoly5_eval
#print axioms MathAndTheory.GyiresCirculant5.strong_chamber_0
#print axioms MathAndTheory.GyiresCirculant5.strong_chamber_1
#print axioms MathAndTheory.GyiresCirculant5.strong_chamber_2
#print axioms MathAndTheory.GyiresCirculant5.strong_chamber_3
#print axioms MathAndTheory.GyiresCirculant5.strong_chamber_4
#print axioms MathAndTheory.GyiresCirculant5.strong_chamber_5
#print axioms MathAndTheory.GyiresCirculant5.strong_chambers
#print axioms MathAndTheory.GyiresCirculant5.gyires_chambers

-- Sections 3 and 4: the main theorems in the library's notation
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_nonneg
#print axioms MathAndTheory.GyiresCirculant5.gyiresDefect_nonneg
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_eq_zero_iff
#print axioms MathAndTheory.GyiresCirculant5.gyiresDefect_eq_zero_iff
#print axioms MathAndTheory.GyiresCirculant5.strong_matrix_inequality
#print axioms MathAndTheory.GyiresCirculant5.gyires_matrix_inequality
#print axioms MathAndTheory.GyiresCirculant5.strong_matrix_equality_iff
#print axioms MathAndTheory.GyiresCirculant5.gyires_matrix_equality_iff
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_margin
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_margin_attained
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_margin_sharp
#print axioms MathAndTheory.GyiresCirculant5.normalized_equality_weights
#print axioms MathAndTheory.GyiresCirculant5.circ_nonneg
#print axioms MathAndTheory.GyiresCirculant5.circ_row_sum
#print axioms MathAndTheory.GyiresCirculant5.circ_column_sum
#print axioms MathAndTheory.GyiresCirculant5.positiveDenominator
#print axioms MathAndTheory.GyiresCirculant5.normalizedGyiresRatio
#print axioms MathAndTheory.GyiresCirculant5.normalizedGyiresRatio_eq_iff

-- Translation to Mathlib's `Matrix.circulant`
#print axioms MathAndTheory.GyiresCirculant5.circulant_eq_transpose_circ
#print axioms MathAndTheory.GyiresCirculant5.permanent_circulant
#print axioms MathAndTheory.GyiresCirculant5.permanent_circulant_mul_transpose
#print axioms MathAndTheory.GyiresCirculant5.permanent_transpose_mul_circulant
#print axioms MathAndTheory.GyiresCirculant5.permanent_circulant_mul_self
#print axioms MathAndTheory.GyiresCirculant5.gyiresDenominator_circulant
#print axioms MathAndTheory.GyiresCirculant5.weights_nonneg_of_entries
#print axioms MathAndTheory.GyiresCirculant5.weights_of_doublyStochastic
#print axioms MathAndTheory.GyiresCirculant5.circulant_eq_const_iff

-- Section 4 and the Discussion: the two-point example and the sharpness of 484
#print axioms MathAndTheory.GyiresCirculant5.P5_twoSupport
#print axioms MathAndTheory.GyiresCirculant5.P5_gram_twoSupport
#print axioms MathAndTheory.GyiresCirculant5.P5_conv_twoSupport
#print axioms MathAndTheory.GyiresCirculant5.strongDefect_twoSupport
#print axioms MathAndTheory.GyiresCirculant5.gyiresDefect_twoSupport
#print axioms MathAndTheory.GyiresCirculant5.gyiresDenominator_twoSupport
#print axioms MathAndTheory.GyiresCirculant5.twoSupport_half_nonneg
#print axioms MathAndTheory.GyiresCirculant5.twoSupport_half_sum
#print axioms MathAndTheory.GyiresCirculant5.permanent_twoSupport_half
#print axioms MathAndTheory.GyiresCirculant5.permanent_gram_twoSupport_half
#print axioms MathAndTheory.GyiresCirculant5.permanent_square_twoSupport_half
#print axioms MathAndTheory.GyiresCirculant5.normalizedGyiresRatio_twoSupport_half
#print axioms MathAndTheory.GyiresCirculant5.gap_coefficient_optimal

-- Remarks of the paper (Sections 1 and 6)
#print axioms MathAndTheory.GyiresCirculant5.gyires_of_strong
#print axioms MathAndTheory.GyiresCirculant5.permanent_fin_two
#print axioms MathAndTheory.GyiresCirculant5.gyires_two
#print axioms MathAndTheory.GyiresCirculant5.circulant_mem_doublyStochastic_iff
#print axioms MathAndTheory.GyiresCirculant5.cyclicShift_pow
#print axioms MathAndTheory.GyiresCirculant5.circulant_eq_sum_pow

-- Every declaration of the library and of the Solution. Under the module system an importing
-- file sees an imported theorem without its proof (as an opaque constant), so the scan does not
-- filter by kind: `collectAxioms` reads the axiom list that Lean computed from the full proof when
-- the declaring module was compiled, and a genuine `axiom` declaration would list itself.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut used : NameSet := {}
  let mut bad : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[idx.toNat]!
    unless (`MathAndTheory.Mathematics.GyiresCirculant5).isPrefixOf module ||
      (`MathAndTheory.Mathematics.Gyires).isPrefixOf module ||
      module == `Solutions.GyiresCirculant5 || module == `Solutions.GyiresFourBlock ||
      module == `Solutions.GyiresExceptional do continue
    declarations := declarations + 1
    let axioms ← liftCoreM <| collectAxioms name
    for a in axioms do used := used.insert a
    if axioms.any (fun a => !standard.contains a) then
      bad := bad.push (name, axioms)
  logInfo m!"declaration scan: {declarations} declarations in the Gyires collection modules"
  logInfo m!"declaration scan: axioms used: {used.toList}"
  logInfo m!"declaration scan: declarations with non-standard axioms: {bad.size}"
  for (n, axioms) in bad do
    logInfo m!"NON-STANDARD AXIOMS: {n} {axioms}"
  if declarations == 0 then
    throwError "No Gyires declaration was loaded for the audit"
  unless bad.isEmpty do
    throwError "The Gyires audit found non-standard axioms"
