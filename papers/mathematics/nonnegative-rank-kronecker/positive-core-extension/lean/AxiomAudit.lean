module

import MatCKronecker
import PositiveCore

-- Actual definitions of the factorization relation and entrywise predicates.
#print MatCKronecker.EntryNonneg
#print MatCKronecker.HasNMF
#print MatCKronecker.RationalEntries

-- theorem
#check @MatCKronecker.factor_term_le
#print axioms MatCKronecker.factor_term_le

-- theorem
#check @MatCKronecker.EntryNonneg.transpose
#print axioms MatCKronecker.EntryNonneg.transpose

-- theorem
#check @MatCKronecker.HasNMF.transpose
#print axioms MatCKronecker.HasNMF.transpose

-- theorem
#check @MatCKronecker.nnrank_transpose
#print axioms MatCKronecker.nnrank_transpose

-- theorem
#check @MatCKronecker.EntryNonneg.kronecker
#print axioms MatCKronecker.EntryNonneg.kronecker

-- theorem
#check @MatCKronecker.HasNMF.kronecker
#print axioms MatCKronecker.HasNMF.kronecker

-- theorem
#check @MatCKronecker.nnrank_kronecker_le
#print axioms MatCKronecker.nnrank_kronecker_le

-- theorem
#check @MatCKronecker.HasNMF.add
#print axioms MatCKronecker.HasNMF.add

-- theorem
#check @MatCKronecker.EntryNonneg.smul
#print axioms MatCKronecker.EntryNonneg.smul

-- theorem
#check @MatCKronecker.HasNMF.smul
#print axioms MatCKronecker.HasNMF.smul

-- def
#check @MatCKronecker.blockProductEquiv
#print axioms MatCKronecker.blockProductEquiv

-- theorem
#check @MatCKronecker.blockDiag_kronecker_reindex
#print axioms MatCKronecker.blockDiag_kronecker_reindex

-- theorem
#check @MatCKronecker.HasNMF.blockDiag_kronecker
#print axioms MatCKronecker.HasNMF.blockDiag_kronecker

-- theorem
#check @MatCKronecker.HasNMF.kronecker_swap
#print axioms MatCKronecker.HasNMF.kronecker_swap

-- theorem
#check @MatCKronecker.rank_fromBlocks
#print axioms MatCKronecker.rank_fromBlocks

-- theorem
#check @MatCKronecker.EntryNonneg.fromBlocks
#print axioms MatCKronecker.EntryNonneg.fromBlocks

-- theorem
#check @MatCKronecker.EntryNonneg.blockDiag
#print axioms MatCKronecker.EntryNonneg.blockDiag

-- theorem
#check @MatCKronecker.HasNMF.blockDiag
#print axioms MatCKronecker.HasNMF.blockDiag

-- theorem
#check @MatCKronecker.HasNMF.blockDiag_lower
#print axioms MatCKronecker.HasNMF.blockDiag_lower

-- theorem
#check @MatCKronecker.nnrank_fromBlocks
#print axioms MatCKronecker.nnrank_fromBlocks

-- def
#check @MatCKronecker.witnessMatrix
#print axioms MatCKronecker.witnessMatrix

-- theorem
#check @MatCKronecker.smallBlock_nonneg
#print axioms MatCKronecker.smallBlock_nonneg

-- theorem
#check @MatCKronecker.witness_nonneg
#print axioms MatCKronecker.witness_nonneg

-- theorem
#check @MatCKronecker.witness_rank
#print axioms MatCKronecker.witness_rank

-- theorem
#check @MatCKronecker.witness_nnrank
#print axioms MatCKronecker.witness_nnrank

-- theorem
#check @MatCKronecker.smallBlock_hasNMF
#print axioms MatCKronecker.smallBlock_hasNMF

-- theorem
#check @MatCKronecker.witness_square_hasNMF
#print axioms MatCKronecker.witness_square_hasNMF

-- theorem
#check @MatCKronecker.witness_square_nnrank_le
#print axioms MatCKronecker.witness_square_nnrank_le

-- theorem
#check @MatCKronecker.witness_unbounded_gap
#print axioms MatCKronecker.witness_unbounded_gap

-- def
#check @MatCKronecker.RationalEntries
#print axioms MatCKronecker.RationalEntries

-- theorem
#check @MatCKronecker.seed_rational
#print axioms MatCKronecker.seed_rational

-- theorem
#check @MatCKronecker.crossEpsilon_rational
#print axioms MatCKronecker.crossEpsilon_rational

-- theorem
#check @MatCKronecker.smallBlock_rational
#print axioms MatCKronecker.smallBlock_rational

-- theorem
#check @MatCKronecker.witness_rational
#print axioms MatCKronecker.witness_rational

-- def
#check @MatCKronecker.witnessIndexEquiv
#print axioms MatCKronecker.witnessIndexEquiv

-- def
#check @MatCKronecker.finiteWitness
#print axioms MatCKronecker.finiteWitness

-- theorem
#check @MatCKronecker.exists_rational_counterexample_with_gap
#print axioms MatCKronecker.exists_rational_counterexample_with_gap

-- theorem
#check @MatCKronecker.counterexample_eleven
#print axioms MatCKronecker.counterexample_eleven

-- theorem
#check @MatCKronecker.vandaele_gillis_glineur_tuyttens_conjecture_false
#print axioms MatCKronecker.vandaele_gillis_glineur_tuyttens_conjecture_false

-- def
#check @MatCKronecker.contrastLeft
#print axioms MatCKronecker.contrastLeft

-- def
#check @MatCKronecker.contrastRight
#print axioms MatCKronecker.contrastRight

-- def
#check @MatCKronecker.centeredIdentity
#print axioms MatCKronecker.centeredIdentity

-- theorem
#check @MatCKronecker.contrastLeft_abs_le
#print axioms MatCKronecker.contrastLeft_abs_le

-- theorem
#check @MatCKronecker.contrastRight_abs_le
#print axioms MatCKronecker.contrastRight_abs_le

-- theorem
#check @MatCKronecker.contrast_factorization
#print axioms MatCKronecker.contrast_factorization

-- def
#check @MatCKronecker.crossRankLeft
#print axioms MatCKronecker.crossRankLeft

-- def
#check @MatCKronecker.crossRankRight
#print axioms MatCKronecker.crossRankRight

-- theorem
#check @MatCKronecker.cross_rank_factorization
#print axioms MatCKronecker.cross_rank_factorization

-- theorem
#check @MatCKronecker.crossRankLeft_abs_le
#print axioms MatCKronecker.crossRankLeft_abs_le

-- theorem
#check @MatCKronecker.crossRankRight_abs_le
#print axioms MatCKronecker.crossRankRight_abs_le

-- def
#check @MatCKronecker.crossEpsilon
#print axioms MatCKronecker.crossEpsilon

-- def
#check @MatCKronecker.crossEta
#print axioms MatCKronecker.crossEta

-- theorem
#check @MatCKronecker.crossEpsilon_pos
#print axioms MatCKronecker.crossEpsilon_pos

-- theorem
#check @MatCKronecker.crossEta_pos
#print axioms MatCKronecker.crossEta_pos

-- def
#check @MatCKronecker.smallBlock
#print axioms MatCKronecker.smallBlock

-- def
#check @MatCKronecker.baselineScale
#print axioms MatCKronecker.baselineScale

-- def
#check @MatCKronecker.crossU
#print axioms MatCKronecker.crossU

-- def
#check @MatCKronecker.crossV
#print axioms MatCKronecker.crossV

-- def
#check @MatCKronecker.otherLeft
#print axioms MatCKronecker.otherLeft

-- def
#check @MatCKronecker.otherRight
#print axioms MatCKronecker.otherRight

-- def
#check @MatCKronecker.correctedTerm
#print axioms MatCKronecker.correctedTerm

-- theorem
#check @MatCKronecker.baselineScale_ge_one
#print axioms MatCKronecker.baselineScale_ge_one

-- theorem
#check @MatCKronecker.crossU_lower
#print axioms MatCKronecker.crossU_lower

-- theorem
#check @MatCKronecker.crossV_lower
#print axioms MatCKronecker.crossV_lower

-- theorem
#check @MatCKronecker.correctedTerm_hasNMF
#print axioms MatCKronecker.correctedTerm_hasNMF

-- theorem
#check @MatCKronecker.other_hasNMF
#print axioms MatCKronecker.other_hasNMF

-- theorem
#check @MatCKronecker.other_plus_main
#print axioms MatCKronecker.other_plus_main

-- theorem
#check @MatCKronecker.cross_factorization_identity
#print axioms MatCKronecker.cross_factorization_identity

-- theorem
#check @MatCKronecker.cross_hasNMF
#print axioms MatCKronecker.cross_hasNMF

-- def
#check @MatCKronecker.EntryNonneg
#print axioms MatCKronecker.EntryNonneg

-- def
#check @MatCKronecker.HasNMF
#print axioms MatCKronecker.HasNMF

-- def
#check @MatCKronecker.nnrank
#print axioms MatCKronecker.nnrank

-- theorem
#check @MatCKronecker.hasNMF_of_factorization
#print axioms MatCKronecker.hasNMF_of_factorization

-- theorem
#check @MatCKronecker.HasNMF.nonneg
#print axioms MatCKronecker.HasNMF.nonneg

-- theorem
#check @MatCKronecker.exists_hasNMF
#print axioms MatCKronecker.exists_hasNMF

-- theorem
#check @MatCKronecker.nnrank_le_of_hasNMF
#print axioms MatCKronecker.nnrank_le_of_hasNMF

-- theorem
#check @MatCKronecker.hasNMF_nnrank
#print axioms MatCKronecker.hasNMF_nnrank

-- theorem
#check @MatCKronecker.HasNMF.rank_le
#print axioms MatCKronecker.HasNMF.rank_le

-- theorem
#check @MatCKronecker.rank_le_nnrank
#print axioms MatCKronecker.rank_le_nnrank

-- theorem
#check @MatCKronecker.nnrank_le_card_width
#print axioms MatCKronecker.nnrank_le_card_width

-- theorem
#check @MatCKronecker.HasNMF.mono
#print axioms MatCKronecker.HasNMF.mono

-- theorem
#check @MatCKronecker.nnrank_le_iff
#print axioms MatCKronecker.nnrank_le_iff

-- theorem
#check @MatCKronecker.hasNMF_zero
#print axioms MatCKronecker.hasNMF_zero

-- theorem
#check @MatCKronecker.nnrank_zero
#print axioms MatCKronecker.nnrank_zero

-- theorem
#check @MatCKronecker.HasNMF.submatrix
#print axioms MatCKronecker.HasNMF.submatrix

-- theorem
#check @MatCKronecker.hasNMF_submatrix_equiv_iff
#print axioms MatCKronecker.hasNMF_submatrix_equiv_iff

-- theorem
#check @MatCKronecker.nnrank_submatrix_equiv
#print axioms MatCKronecker.nnrank_submatrix_equiv

-- def
#check @MatCKronecker.onesMatrix
#print axioms MatCKronecker.onesMatrix

-- def
#check @MatCKronecker.nearOne
#print axioms MatCKronecker.nearOne

-- theorem
#check @MatCKronecker.nearOne_eq
#print axioms MatCKronecker.nearOne_eq

-- theorem
#check @MatCKronecker.nearOne_nonneg
#print axioms MatCKronecker.nearOne_nonneg

-- theorem
#check @MatCKronecker.onesMatrix_mul
#print axioms MatCKronecker.onesMatrix_mul

-- def
#check @MatCKronecker.nearOneInverse
#print axioms MatCKronecker.nearOneInverse

-- theorem
#check @MatCKronecker.nearOneInverse_mul
#print axioms MatCKronecker.nearOneInverse_mul

-- theorem
#check @MatCKronecker.rank_nearOne
#print axioms MatCKronecker.rank_nearOne

-- theorem
#check @MatCKronecker.nnrank_nearOne
#print axioms MatCKronecker.nnrank_nearOne

-- def
#check @MatCKronecker.seed
#print axioms MatCKronecker.seed

-- def
#check @MatCKronecker.seedLeft
#print axioms MatCKronecker.seedLeft

-- def
#check @MatCKronecker.seedRight
#print axioms MatCKronecker.seedRight

-- def
#check @MatCKronecker.seedRankLeft
#print axioms MatCKronecker.seedRankLeft

-- def
#check @MatCKronecker.seedRankRight
#print axioms MatCKronecker.seedRankRight

-- theorem
#check @MatCKronecker.seed_positive
#print axioms MatCKronecker.seed_positive

-- theorem
#check @MatCKronecker.seedLeft_lower
#print axioms MatCKronecker.seedLeft_lower

-- theorem
#check @MatCKronecker.seedRight_lower
#print axioms MatCKronecker.seedRight_lower

-- theorem
#check @MatCKronecker.seed_nonnegative_factorization
#print axioms MatCKronecker.seed_nonnegative_factorization

-- theorem
#check @MatCKronecker.seed_rank_factorization
#print axioms MatCKronecker.seed_rank_factorization

-- theorem
#check @MatCKronecker.seedRankLeft_abs_le
#print axioms MatCKronecker.seedRankLeft_abs_le

-- theorem
#check @MatCKronecker.seedRankRight_abs_le
#print axioms MatCKronecker.seedRankRight_abs_le

-- theorem
#check @MatCKronecker.seed_diagonal
#print axioms MatCKronecker.seed_diagonal

-- theorem
#check @MatCKronecker.seed_cross_product
#print axioms MatCKronecker.seed_cross_product

-- def
#check @MatCKronecker.seedMinor
#print axioms MatCKronecker.seedMinor

-- theorem
#check @MatCKronecker.seedMinor_det
#print axioms MatCKronecker.seedMinor_det

-- theorem
#check @MatCKronecker.seed_rank
#print axioms MatCKronecker.seed_rank

-- theorem
#check @MatCKronecker.seed_nonneg
#print axioms MatCKronecker.seed_nonneg

-- theorem
#check @MatCKronecker.seed_hasNMF_four
#print axioms MatCKronecker.seed_hasNMF_four

-- theorem
#check @MatCKronecker.seed_not_hasNMF_three
#print axioms MatCKronecker.seed_not_hasNMF_three

-- theorem
#check @MatCKronecker.seed_nnrank
#print axioms MatCKronecker.seed_nnrank

-- def
#check @MatCKronecker.simplexLeft
#print axioms MatCKronecker.simplexLeft

-- def
#check @MatCKronecker.simplexRight
#print axioms MatCKronecker.simplexRight

-- theorem
#check @MatCKronecker.simplexRight_sum
#print axioms MatCKronecker.simplexRight_sum

-- theorem
#check @MatCKronecker.simplexRight_sub_none
#print axioms MatCKronecker.simplexRight_sub_none

-- def
#check @MatCKronecker.simplexRowDifferences
#print axioms MatCKronecker.simplexRowDifferences

-- theorem
#check @MatCKronecker.simplexLeft_mul
#print axioms MatCKronecker.simplexLeft_mul

-- theorem
#check @MatCKronecker.simplex_factorization
#print axioms MatCKronecker.simplex_factorization

-- theorem
#check @MatCKronecker.abs_sum_eighteen_le
#print axioms MatCKronecker.abs_sum_eighteen_le

-- theorem
#check @MatCKronecker.simplexLeft_nonneg_eighteen
#print axioms MatCKronecker.simplexLeft_nonneg_eighteen

-- theorem
#check @MatCKronecker.simplexRight_nonneg_eighteen
#print axioms MatCKronecker.simplexRight_nonneg_eighteen

-- theorem
#check @MatCKronecker.simplex_abs_sum_le_card_mul
#print axioms MatCKronecker.simplex_abs_sum_le_card_mul

-- theorem
#check @MatCKronecker.simplexLeft_nonneg_uniform
#print axioms MatCKronecker.simplexLeft_nonneg_uniform

-- theorem
#check @MatCKronecker.simplexRight_nonneg_uniform
#print axioms MatCKronecker.simplexRight_nonneg_uniform

-- theorem
#check @PositiveCore.simplexLeft_nonneg_iff
#print axioms PositiveCore.simplexLeft_nonneg_iff

-- theorem
#check @PositiveCore.simplexRight_nonneg_iff
#print axioms PositiveCore.simplexRight_nonneg_iff

-- theorem
#check @PositiveCore.absorption_of_coordinates
#print axioms PositiveCore.absorption_of_coordinates

-- theorem
#check @PositiveCore.simplexLeft_nonneg_bounded
#print axioms PositiveCore.simplexLeft_nonneg_bounded

-- theorem
#check @PositiveCore.simplexRight_nonneg_bounded
#print axioms PositiveCore.simplexRight_nonneg_bounded

-- theorem
#check @PositiveCore.absorption_bounded
#print axioms PositiveCore.absorption_bounded

-- theorem
#check @PositiveCore.positive_core_absorption
#print axioms PositiveCore.positive_core_absorption

-- def
#check @PositiveCore.Activation.seed
#print axioms PositiveCore.Activation.seed

-- def
#check @PositiveCore.Activation.auxiliary
#print axioms PositiveCore.Activation.auxiliary

-- def
#check @PositiveCore.Activation.leftEven
#print axioms PositiveCore.Activation.leftEven

-- def
#check @PositiveCore.Activation.leftOdd
#print axioms PositiveCore.Activation.leftOdd

-- def
#check @PositiveCore.Activation.rightConstant
#print axioms PositiveCore.Activation.rightConstant

-- def
#check @PositiveCore.Activation.rightEvenSlope
#print axioms PositiveCore.Activation.rightEvenSlope

-- def
#check @PositiveCore.Activation.rightOddSlope
#print axioms PositiveCore.Activation.rightOddSlope

-- def
#check @PositiveCore.Activation.left
#print axioms PositiveCore.Activation.left

-- def
#check @PositiveCore.Activation.right
#print axioms PositiveCore.Activation.right

-- theorem
#check @PositiveCore.Activation.product_identity
#print axioms PositiveCore.Activation.product_identity

-- theorem
#check @PositiveCore.Activation.left_positive
#print axioms PositiveCore.Activation.left_positive

-- theorem
#check @PositiveCore.Activation.right_positive
#print axioms PositiveCore.Activation.right_positive

-- theorem
#check @PositiveCore.Activation.hasNMF_six
#print axioms PositiveCore.Activation.hasNMF_six

-- def
#check @PositiveCore.Activation.seedMinor
#print axioms PositiveCore.Activation.seedMinor

-- theorem
#check @PositiveCore.Activation.seedMinor_det
#print axioms PositiveCore.Activation.seedMinor_det

-- theorem
#check @PositiveCore.Activation.auxiliary_det
#print axioms PositiveCore.Activation.auxiliary_det

-- def
#check @PositiveCore.Activation.seedRankLeft
#print axioms PositiveCore.Activation.seedRankLeft

-- def
#check @PositiveCore.Activation.seedRankRight
#print axioms PositiveCore.Activation.seedRankRight

-- theorem
#check @PositiveCore.Activation.seed_rank_factorization
#print axioms PositiveCore.Activation.seed_rank_factorization

-- theorem
#check @PositiveCore.Activation.seed_rank
#print axioms PositiveCore.Activation.seed_rank

-- theorem
#check @PositiveCore.Activation.auxiliary_rank
#print axioms PositiveCore.Activation.auxiliary_rank

-- theorem
#check @PositiveCore.Activation.product_rank_lower
#print axioms PositiveCore.Activation.product_rank_lower

-- theorem
#check @PositiveCore.Activation.product_nnrank
#print axioms PositiveCore.Activation.product_nnrank

-- theorem
#check @PositiveCore.Activation.product_rank
#print axioms PositiveCore.Activation.product_rank

-- theorem
#check @PositiveCore.exists_bounded_rank_factorization
#print axioms PositiveCore.exists_bounded_rank_factorization

-- def
#check @PositiveCore.capacityMap
#print axioms PositiveCore.capacityMap

-- theorem
#check @PositiveCore.finrank_comap_subtype
#print axioms PositiveCore.finrank_comap_subtype

-- theorem
#check @PositiveCore.capacity_dimension
#print axioms PositiveCore.capacity_dimension

-- theorem
#check @PositiveCore.exists_nullspace_frame_iff_dimension
#print axioms PositiveCore.exists_nullspace_frame_iff_dimension

-- theorem
#check @PositiveCore.exists_nullspace_frame_iff
#print axioms PositiveCore.exists_nullspace_frame_iff

-- theorem
#check @PositiveCore.exists_matrix_nullspace_frame_iff
#print axioms PositiveCore.exists_matrix_nullspace_frame_iff

-- theorem
#check @PositiveCore.rank_kronecker_row_slice_le
#print axioms PositiveCore.rank_kronecker_row_slice_le

-- theorem
#check @PositiveCore.rank_kronecker_col_slice_le
#print axioms PositiveCore.rank_kronecker_col_slice_le

-- theorem
#check @PositiveCore.rank_kronecker_row_slice
#print axioms PositiveCore.rank_kronecker_row_slice

-- theorem
#check @PositiveCore.rank_kronecker_col_slice
#print axioms PositiveCore.rank_kronecker_col_slice

-- theorem
#check @PositiveCore.kronecker_factor_compression
#print axioms PositiveCore.kronecker_factor_compression

-- theorem
#check @PositiveCore.balanced_factorization_of_kronecker_rank_saturation
#print axioms PositiveCore.balanced_factorization_of_kronecker_rank_saturation

-- theorem
#check @PositiveCore.hasNMF_kronecker_compression
#print axioms PositiveCore.hasNMF_kronecker_compression

-- def
#check @PositiveCore.ConeObstruction.twist
#print axioms PositiveCore.ConeObstruction.twist

-- def
#check @PositiveCore.ConeObstruction.nested
#print axioms PositiveCore.ConeObstruction.nested

-- def
#check @PositiveCore.ConeObstruction.score
#print axioms PositiveCore.ConeObstruction.score

-- def
#check @PositiveCore.ConeObstruction.mass
#print axioms PositiveCore.ConeObstruction.mass

-- theorem
#check @PositiveCore.ConeObstruction.difference_mul_le
#print axioms PositiveCore.ConeObstruction.difference_mul_le

-- theorem
#check @PositiveCore.ConeObstruction.cone_pairing_bound
#print axioms PositiveCore.ConeObstruction.cone_pairing_bound

-- theorem
#check @PositiveCore.ConeObstruction.score_mul
#print axioms PositiveCore.ConeObstruction.score_mul

-- theorem
#check @PositiveCore.ConeObstruction.mass_mul
#print axioms PositiveCore.ConeObstruction.mass_mul

-- theorem
#check @PositiveCore.ConeObstruction.factorization_score_bound
#print axioms PositiveCore.ConeObstruction.factorization_score_bound

-- theorem
#check @PositiveCore.ConeObstruction.score_nested
#print axioms PositiveCore.ConeObstruction.score_nested

-- theorem
#check @PositiveCore.ConeObstruction.mass_nested
#print axioms PositiveCore.ConeObstruction.mass_nested

-- theorem
#check @PositiveCore.ConeObstruction.parameter_le_half
#print axioms PositiveCore.ConeObstruction.parameter_le_half

-- theorem
#check @PositiveCore.finite_positive_margin
#print axioms PositiveCore.finite_positive_margin

-- theorem
#check @PositiveCore.positive_affine_interval
#print axioms PositiveCore.positive_affine_interval

-- theorem
#check @PositiveCore.nullspace_directional_interval
#print axioms PositiveCore.nullspace_directional_interval

-- theorem
#check @PositiveCore.directional_absorption_of_rank
#print axioms PositiveCore.directional_absorption_of_rank

-- theorem
#check @PositiveCore.directional_nnrank_le_of_rank
#print axioms PositiveCore.directional_nnrank_le_of_rank

-- theorem
#check @PositiveCore.directional_absorption_factor_rank_bound
#print axioms PositiveCore.directional_absorption_factor_rank_bound

-- def
#check @PositiveCore.duplicateD
#print axioms PositiveCore.duplicateD

-- def
#check @PositiveCore.duplicateE
#print axioms PositiveCore.duplicateE

-- theorem
#check @PositiveCore.duplicateD_mul_duplicateE
#print axioms PositiveCore.duplicateD_mul_duplicateE

-- def
#check @PositiveCore.duplicateLeft
#print axioms PositiveCore.duplicateLeft

-- def
#check @PositiveCore.duplicateRight
#print axioms PositiveCore.duplicateRight

-- theorem
#check @PositiveCore.duplicateLeft_inl
#print axioms PositiveCore.duplicateLeft_inl

-- theorem
#check @PositiveCore.duplicateLeft_inr
#print axioms PositiveCore.duplicateLeft_inr

-- theorem
#check @PositiveCore.duplicateRight_inl
#print axioms PositiveCore.duplicateRight_inl

-- theorem
#check @PositiveCore.duplicateRight_inr
#print axioms PositiveCore.duplicateRight_inr

-- theorem
#check @PositiveCore.duplicateLeft_pos
#print axioms PositiveCore.duplicateLeft_pos

-- theorem
#check @PositiveCore.duplicateRight_pos
#print axioms PositiveCore.duplicateRight_pos

-- theorem
#check @PositiveCore.duplicate_product
#print axioms PositiveCore.duplicate_product

-- theorem
#check @PositiveCore.duplicateLeft_rank
#print axioms PositiveCore.duplicateLeft_rank

-- theorem
#check @PositiveCore.duplicateRight_rank
#print axioms PositiveCore.duplicateRight_rank

-- theorem
#check @PositiveCore.exists_positive_duplication
#print axioms PositiveCore.exists_positive_duplication

-- theorem
#check @PositiveCore.exists_rank_factorization
#print axioms PositiveCore.exists_rank_factorization

-- theorem
#check @PositiveCore.rank_kronecker
#print axioms PositiveCore.rank_kronecker

-- theorem
#check @PositiveCore.nullspace_absorption_identity
#print axioms PositiveCore.nullspace_absorption_identity

-- theorem
#check @PositiveCore.nullspace_absorption
#print axioms PositiveCore.nullspace_absorption

-- theorem
#check @PositiveCore.nullspace_scaled_absorption_identity
#print axioms PositiveCore.nullspace_scaled_absorption_identity

-- theorem
#check @PositiveCore.abs_mul_entry_le
#print axioms PositiveCore.abs_mul_entry_le

-- theorem
#check @PositiveCore.nullspace_absorption_bounded
#print axioms PositiveCore.nullspace_absorption_bounded

-- theorem
#check @PositiveCore.nullspace_nnrank_le
#print axioms PositiveCore.nullspace_nnrank_le

-- theorem
#check @PositiveCore.original_seed_tensor_rank
#print axioms PositiveCore.original_seed_tensor_rank

-- theorem
#check @PositiveCore.original_mixed_rank
#print axioms PositiveCore.original_mixed_rank

-- theorem
#check @PositiveCore.ProfileExamples.left_annihilator_of_equal_rank
#print axioms PositiveCore.ProfileExamples.left_annihilator_of_equal_rank

-- theorem
#check @PositiveCore.ProfileExamples.right_annihilator_of_equal_rank
#print axioms PositiveCore.ProfileExamples.right_annihilator_of_equal_rank

-- def
#check @PositiveCore.ProfileExamples.balanceRow
#print axioms PositiveCore.ProfileExamples.balanceRow

-- theorem
#check @PositiveCore.ProfileExamples.intrinsic_column_balance
#print axioms PositiveCore.ProfileExamples.intrinsic_column_balance

-- theorem
#check @PositiveCore.ProfileExamples.intrinsic_row_balance
#print axioms PositiveCore.ProfileExamples.intrinsic_row_balance

-- theorem
#check @PositiveCore.ProfileExamples.score_bound_of_equal_factor_ranks
#print axioms PositiveCore.ProfileExamples.score_bound_of_equal_factor_ranks

-- theorem
#check @PositiveCore.ProfileExamples.nested_nonneg
#print axioms PositiveCore.ProfileExamples.nested_nonneg

-- theorem
#check @PositiveCore.ProfileExamples.nested_balanced_parameter_le_half
#print axioms PositiveCore.ProfileExamples.nested_balanced_parameter_le_half

-- def
#check @PositiveCore.ProfileExamples.lowerLeft
#print axioms PositiveCore.ProfileExamples.lowerLeft

-- def
#check @PositiveCore.ProfileExamples.lowerRight
#print axioms PositiveCore.ProfileExamples.lowerRight

-- theorem
#check @PositiveCore.ProfileExamples.lower_factorization
#print axioms PositiveCore.ProfileExamples.lower_factorization

-- theorem
#check @PositiveCore.ProfileExamples.rank_le_three_of_last_column
#print axioms PositiveCore.ProfileExamples.rank_le_three_of_last_column

-- theorem
#check @PositiveCore.ProfileExamples.lower_factor_rank_bound
#print axioms PositiveCore.ProfileExamples.lower_factor_rank_bound

-- theorem
#check @PositiveCore.ProfileExamples.nested_profile_low
#print axioms PositiveCore.ProfileExamples.nested_profile_low

-- theorem
#check @PositiveCore.ProfileExamples.nested_profile_high
#print axioms PositiveCore.ProfileExamples.nested_profile_high

-- theorem
#check @PositiveCore.ProfileExamples.nested_defect_low
#print axioms PositiveCore.ProfileExamples.nested_defect_low

-- theorem
#check @PositiveCore.ProfileExamples.nested_defect_high
#print axioms PositiveCore.ProfileExamples.nested_defect_high

-- theorem
#check @PositiveCore.ProfileExamples.original_seed_profile
#print axioms PositiveCore.ProfileExamples.original_seed_profile

-- theorem
#check @PositiveCore.ProfileExamples.original_seed_defect
#print axioms PositiveCore.ProfileExamples.original_seed_defect

-- def
#check @PositiveCore.HasFactorRankBound
#print axioms PositiveCore.HasFactorRankBound

-- def
#check @PositiveCore.factorRankProfile
#print axioms PositiveCore.factorRankProfile

-- def
#check @PositiveCore.factorRankDefect
#print axioms PositiveCore.factorRankDefect

-- theorem
#check @PositiveCore.exists_hasFactorRankBound
#print axioms PositiveCore.exists_hasFactorRankBound

-- theorem
#check @PositiveCore.factorRankProfile_le_of_bound
#print axioms PositiveCore.factorRankProfile_le_of_bound

-- theorem
#check @PositiveCore.hasFactorRankBound_profile
#print axioms PositiveCore.hasFactorRankBound_profile

-- theorem
#check @PositiveCore.exists_factorization_max_rank_eq_profile
#print axioms PositiveCore.exists_factorization_max_rank_eq_profile

-- theorem
#check @PositiveCore.rank_le_factorRankProfile
#print axioms PositiveCore.rank_le_factorRankProfile

-- theorem
#check @PositiveCore.factorRankProfile_le_nnrank
#print axioms PositiveCore.factorRankProfile_le_nnrank

-- theorem
#check @PositiveCore.factorRankDefect_eq_zero_iff
#print axioms PositiveCore.factorRankDefect_eq_zero_iff

-- theorem
#check @PositiveCore.factorRankProfile_add_product_rank_le_of_hasNMF
#print axioms PositiveCore.factorRankProfile_add_product_rank_le_of_hasNMF

-- theorem
#check @PositiveCore.exists_positive_entry_of_nonzero
#print axioms PositiveCore.exists_positive_entry_of_nonzero

-- theorem
#check @PositiveCore.factorRankProfile_add_product_rank_le_nnrank
#print axioms PositiveCore.factorRankProfile_add_product_rank_le_nnrank

-- theorem
#check @PositiveCore.kronecker_swap_ranks
#print axioms PositiveCore.kronecker_swap_ranks

-- theorem
#check @PositiveCore.factorRankProfile_add_product_rank_le_nnrank_right
#print axioms PositiveCore.factorRankProfile_add_product_rank_le_nnrank_right

-- theorem
#check @PositiveCore.rank_add_max_factorRankDefect_le_nnrank_kronecker
#print axioms PositiveCore.rank_add_max_factorRankDefect_le_nnrank_kronecker

-- theorem
#check @PositiveCore.rank_mul_add_max_factorRankDefect_le_nnrank_kronecker
#print axioms PositiveCore.rank_mul_add_max_factorRankDefect_le_nnrank_kronecker

-- theorem
#check @PositiveCore.exists_right_inverse_of_full_row_rank
#print axioms PositiveCore.exists_right_inverse_of_full_row_rank

-- theorem
#check @PositiveCore.exists_left_inverse_of_full_column_rank
#print axioms PositiveCore.exists_left_inverse_of_full_column_rank

-- theorem
#check @PositiveCore.saturated_factor_ranks
#print axioms PositiveCore.saturated_factor_ranks

-- theorem
#check @PositiveCore.left_annihilator_transfer
#print axioms PositiveCore.left_annihilator_transfer

-- theorem
#check @PositiveCore.right_annihilator_transfer
#print axioms PositiveCore.right_annihilator_transfer

-- theorem
#check @PositiveCore.four_row_relation_transfer
#print axioms PositiveCore.four_row_relation_transfer

-- theorem
#check @PositiveCore.four_column_relation_transfer
#print axioms PositiveCore.four_column_relation_transfer

-- theorem
#check @PositiveCore.tensor_obstruction_of_score
#print axioms PositiveCore.tensor_obstruction_of_score

-- theorem
#check @PositiveCore.nested_rank
#print axioms PositiveCore.nested_rank

-- theorem
#check @PositiveCore.nested_tensor_obstruction
#print axioms PositiveCore.nested_tensor_obstruction

-- theorem
#check @PositiveCore.original_seed_tensor_obstruction
#print axioms PositiveCore.original_seed_tensor_obstruction

-- theorem
#check @PositiveCore.original_mixed_nnrank_exact
#print axioms PositiveCore.original_mixed_nnrank_exact

-- theorem
#check @PositiveCore.original_mixed_nnrank_exact_reverse
#print axioms PositiveCore.original_mixed_nnrank_exact_reverse
