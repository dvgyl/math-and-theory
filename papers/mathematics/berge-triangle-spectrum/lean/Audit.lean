import BergeTriangle

/-! Axiom audit of the principal declarations.  Run with `lake env lean Audit.lean`. -/

-- Paired products
#print axioms BergeTriangle.PairSystem.free
#print axioms BergeTriangle.PairSystem.saturated
#print axioms BergeTriangle.PairSystem.card_edges
#print axioms BergeTriangle.PairSystem.two_mul_card_pairs_add_card_base
#print axioms BergeTriangle.PairedProduct.saturated
#print axioms BergeTriangle.PairedProduct.isProductSize
#print axioms BergeTriangle.finProduct_card_edges
#print axioms BergeTriangle.inSaturationSpectrum_of_isProductSize
#print axioms BergeTriangle.IsSaturated.eq_of_subset

-- The construction J(p,q) and the threshold system (Theorem 3, lower bound)
#print axioms BergeTriangle.mem_sharpSystem_iff
#print axioms BergeTriangle.sharpSystem_free
#print axioms BergeTriangle.sharpSystem_saturated
#print axioms BergeTriangle.card_sharpSystem
#print axioms BergeTriangle.sharpSystem_not_product
#print axioms BergeTriangle.div_four_mul_eq_L
#print axioms BergeTriangle.thresholdSystem_saturated
#print axioms BergeTriangle.thresholdSystem_not_isPairedProduct
#print axioms BergeTriangle.card_thresholdSystem
#print axioms BergeTriangle.exists_saturated_not_isPairedProduct_card_eq_L
#print axioms BergeTriangle.exists_free_card_eq_L_not_subset_product

-- Arithmetic of the window (Lₙ, Eₙ]
#print axioms BergeTriangle.mul_sub_le_E
#print axioms BergeTriangle.W_eq
#print axioms BergeTriangle.isProductSize_E_sub_iff
#print axioms BergeTriangle.card_window_productSizes_le
#print axioms BergeTriangle.window_not_productSize_count

-- Consequences of Theorem 1 (hypothesis `DenseContainment n`)
#print axioms BergeTriangle.DenseContainment.isPairedProduct
#print axioms BergeTriangle.DenseContainment.inSaturationSpectrum_iff
#print axioms BergeTriangle.DenseContainment.spectrum_inter_window
#print axioms BergeTriangle.DenseContainment.card_le_L_of_not_isPairedProduct
#print axioms BergeTriangle.DenseContainment.isGreatest_not_isPairedProduct
#print axioms BergeTriangle.DenseContainment.card_le_E
#print axioms BergeTriangle.DenseContainment.inSaturationSpectrum_E_sub_iff
#print axioms BergeTriangle.DenseContainment.window_missing_count
