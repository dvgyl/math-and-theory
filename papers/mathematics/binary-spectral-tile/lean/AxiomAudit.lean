-- Generated from modules.json by verify_release.py --freeze.
import BinaryBasic
import BinaryData
import BinaryTilingDefs
import BinarySubspacePrelude
import BinaryTilingCodes
import BinaryAperiodic
import BinaryObstruction
import BinaryCharacters
import BinaryTiling
import BinaryNoLinear
import BinaryWalsh
import BinaryPeriodicity
import BinarySpectral
import BinaryNoSubspace
import BinaryComplements
import BinaryMain

#print axioms BinaryFuglede.V
#print axioms BinaryFuglede.decode
#print axioms BinaryFuglede.decodeFin
#print axioms BinaryFuglede.decode_xor
#print axioms BinaryFuglede.decode_zero
#print axioms BinaryFuglede.decodeFin_injective
#print axioms BinaryFuglede.card_V
#print axioms BinaryFuglede.decodeFin_bijective
#print axioms BinaryFuglede.add_self
#print axioms BinaryFuglede.xorFin
#print axioms BinaryFuglede.decodeFin_xor
#print axioms BinaryFuglede.pointCode
#print axioms BinaryFuglede.freqCode
#print axioms BinaryFuglede.tileCode
#print axioms BinaryFuglede.allowedCode
#print axioms BinaryFuglede.point
#print axioms BinaryFuglede.freq
#print axioms BinaryFuglede.tileShift
#print axioms BinaryFuglede.allowedShift
#print axioms BinaryFuglede.Eset
#print axioms BinaryFuglede.Lset
#print axioms BinaryFuglede.Tset
#print axioms BinaryFuglede.Allowed
#print axioms BinaryFuglede.TilingPair
#print axioms BinaryFuglede.Periodic
#print axioms BinaryFuglede.HasPTProperty
#print axioms BinaryFuglede.code_tiling
#print axioms BinaryFuglede.sum_point_tile_bijective
#print axioms BinaryFuglede.point_injective
#print axioms BinaryFuglede.tileShift_injective
#print axioms BinaryFuglede.pointEquiv
#print axioms BinaryFuglede.tileEquiv
#print axioms BinaryFuglede.card_Eset
#print axioms BinaryFuglede.card_Tset
#print axioms BinaryFuglede.explicit_tiling
#print axioms BinaryFuglede.point_zero
#print axioms BinaryFuglede.code_nonperiodic
#print axioms BinaryFuglede.Eset_not_periodic
#print axioms BinaryFuglede.permittedCode
#print axioms BinaryFuglede.allowedCode_permitted
#print axioms BinaryFuglede.differenceWitness
#print axioms BinaryFuglede.DifferenceCovered
#print axioms BinaryFuglede.instDecidableDifferenceCovered
#print axioms BinaryFuglede.blockCode
#print axioms BinaryFuglede.code_difference_cover
#print axioms BinaryFuglede.CubeAllowed
#print axioms BinaryFuglede.instDecidableCubeAllowed
#print axioms BinaryFuglede.no_allowed_cube_codes
#print axioms BinaryFuglede.finrank_three_has_cube
#print axioms BinaryFuglede.difference_free_mem_allowed
#print axioms BinaryFuglede.permittedCode_of_decode_mem_allowed
#print axioms BinaryFuglede.no_allowed_cube
#print axioms BinaryFuglede.no_three_dimensional_difference_free
#print axioms BinaryFuglede.subspace_difference_free_of_tiling
#print axioms BinaryFuglede.no_three_dimensional_tiling
#print axioms BinaryFuglede.complement_card_eight
#print axioms BinaryFuglede.add_nonzero_of_distinct
#print axioms BinaryFuglede.complement_difference_free
#print axioms BinaryFuglede.complement_difference_allowed
#print axioms BinaryFuglede.exists_mem_outside_finset
#print axioms BinaryFuglede.not_periodic_complement
#print axioms BinaryFuglede.no_subspace_tiling_of_card
#print axioms BinaryFuglede.binaryDot
#print axioms BinaryFuglede.intCharacter
#print axioms BinaryFuglede.character
#print axioms BinaryFuglede.binaryDot_add
#print axioms BinaryFuglede.binaryDot_add_left
#print axioms BinaryFuglede.intCharacter_zero
#print axioms BinaryFuglede.intCharacter_zero_left
#print axioms BinaryFuglede.intCharacter_add
#print axioms BinaryFuglede.intCharacter_add_left
#print axioms BinaryFuglede.character_add
#print axioms BinaryFuglede.character_add_left
#print axioms BinaryFuglede.character_zero
#print axioms BinaryFuglede.character_zero_left
#print axioms BinaryFuglede.character_conj
#print axioms BinaryFuglede.character_sq
#print axioms BinaryFuglede.characterHom
#print axioms BinaryFuglede.SpectralDifference
#print axioms BinaryFuglede.instDecidableSpectralDifference
#print axioms BinaryFuglede.walshInt
#print axioms BinaryFuglede.walshBlockCode
#print axioms BinaryFuglede.walshInt_zero
#print axioms BinaryFuglede.frequency_difference
#print axioms BinaryFuglede.int_character_orthogonality
#print axioms BinaryFuglede.characterVector
#print axioms BinaryFuglede.character_gram
#print axioms BinaryFuglede.character_vectors_linearIndependent
#print axioms BinaryFuglede.enumeratedCharacterBasis
#print axioms BinaryFuglede.enumeratedCharacterBasis_apply
#print axioms BinaryFuglede.restrictToEnumeration
#print axioms BinaryFuglede.actualCharacterBasis
#print axioms BinaryFuglede.actualCharacterBasis_apply
#print axioms BinaryFuglede.freq_injective
#print axioms BinaryFuglede.freqEquiv
#print axioms BinaryFuglede.card_Lset
#print axioms BinaryFuglede.spectrumBasis
#print axioms BinaryFuglede.spectrumBasis_apply
#print axioms BinaryFuglede.actual_character_orthogonality
#print axioms BinaryFuglede.IsSpectral
#print axioms BinaryFuglede.Eset_isSpectral
#print axioms BinaryFuglede.explicit_no_periodic_complement
#print axioms BinaryFuglede.explicit_no_subspace_complement
#print axioms BinaryFuglede.binary_nine_fails_PT
#print axioms BinaryFuglede.spectral_aperiodic_tile_without_periodic_complement
#print axioms BinaryFuglede.exists_spectral_counterexample
#print axioms BinaryFuglede.StarCode
#print axioms BinaryFuglede.instDecidableStarCode
#print axioms BinaryFuglede.EdgeStar
#print axioms BinaryFuglede.instDecidableEdgeStar
#print axioms BinaryFuglede.edge_star
#print axioms BinaryFuglede.tile_code_aperiodic
#print axioms BinaryFuglede.pair_sum_cancel
#print axioms BinaryFuglede.tileShift_zero
#print axioms BinaryFuglede.permitted_of_allowedShift
#print axioms BinaryFuglede.starCode_mem
#print axioms BinaryFuglede.tilingPair_translate
#print axioms BinaryFuglede.eq_of_tilingPair_subset
#print axioms BinaryFuglede.complement_eq_translate
#print axioms BinaryFuglede.tilingPair_iff_translate
#print axioms BinaryFuglede.translate_tile_injective
#print axioms BinaryFuglede.complementEquiv
#print axioms BinaryFuglede.card_complements
