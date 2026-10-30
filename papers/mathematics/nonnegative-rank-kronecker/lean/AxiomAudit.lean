module

import MatCKronecker

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
