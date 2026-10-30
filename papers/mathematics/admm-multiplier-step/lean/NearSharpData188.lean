import IntegerCross
import IntegerEmbedding
import NearSharpData188Defs
import NearSharpData188_lower_lo_gram_identity_0
import NearSharpData188_lower_lo_gram_identity_6
import NearSharpData188_lower_lo_gram_identity_12
import NearSharpData188_lower_lo_gram_identity_18
import NearSharpData188_Tlo_gram_identity_0
import NearSharpData188_Tlo_gram_identity_6
import NearSharpData188_Tlo_gram_identity_12
import NearSharpData188_Tlo_gram_identity_18
import NearSharpData188_lower_hi_gram_identity_0
import NearSharpData188_lower_hi_gram_identity_6
import NearSharpData188_lower_hi_gram_identity_12
import NearSharpData188_lower_hi_gram_identity_18
import NearSharpData188_Thi_gram_identity_0
import NearSharpData188_Thi_gram_identity_6
import NearSharpData188_Thi_gram_identity_12
import NearSharpData188_Thi_gram_identity_18
import NearSharpData188_weightedFZ_identity_0
import NearSharpData188_weightedFZ_identity_6
import NearSharpData188_weightedFZ_identity_12
import NearSharpData188_weightedGZ_identity_0
import NearSharpData188_weightedGZ_identity_6
import NearSharpData188_weightedGZ_identity_12
import NearSharpData188_endpoint_fast_lo_0
import NearSharpData188_endpoint_fast_lo_6
import NearSharpData188_endpoint_fast_lo_12
import NearSharpData188_endpoint_fast_lo_18
import NearSharpData188_endpoint_fast_lo_24
import NearSharpData188_endpoint_fast_hi_0
import NearSharpData188_endpoint_fast_hi_6
import NearSharpData188_endpoint_fast_hi_12
import NearSharpData188_endpoint_fast_hi_18
import NearSharpData188_endpoint_fast_hi_24
import NearSharpData188_Simple0
import NearSharpData188_Simple1
import NearSharpData188_Simple2
import NearSharpData188_Simple3
import NearSharpData188_Simple4
import NearSharpData188_Simple5
import NearSharpData188_Simple6
import NearSharpData188_Simple7
import NearSharpData188_Simple8
import NearSharpData188_Simple9
import NearSharpData188_Simple10
import NearSharpData188_Simple11

namespace ADMMNearSharpCertificate.Data188

open scoped BigOperators
open ADMMNearSharp.StandardRows

set_option maxHeartbeats 0

theorem lower_lo_gram_identity : ∀ (i : Fin 24) (j : Fin 24), (lower_lo_Rden^2 • lower_loZ) i j = (den_lo • (lower_lo_RZ.transpose * lower_lo_RZ) + lower_lo_EZ) i j := by
  intro i j
  fin_cases i
  · exact lower_lo_gram_identity_row0 j
  · exact lower_lo_gram_identity_row1 j
  · exact lower_lo_gram_identity_row2 j
  · exact lower_lo_gram_identity_row3 j
  · exact lower_lo_gram_identity_row4 j
  · exact lower_lo_gram_identity_row5 j
  · exact lower_lo_gram_identity_row6 j
  · exact lower_lo_gram_identity_row7 j
  · exact lower_lo_gram_identity_row8 j
  · exact lower_lo_gram_identity_row9 j
  · exact lower_lo_gram_identity_row10 j
  · exact lower_lo_gram_identity_row11 j
  · exact lower_lo_gram_identity_row12 j
  · exact lower_lo_gram_identity_row13 j
  · exact lower_lo_gram_identity_row14 j
  · exact lower_lo_gram_identity_row15 j
  · exact lower_lo_gram_identity_row16 j
  · exact lower_lo_gram_identity_row17 j
  · exact lower_lo_gram_identity_row18 j
  · exact lower_lo_gram_identity_row19 j
  · exact lower_lo_gram_identity_row20 j
  · exact lower_lo_gram_identity_row21 j
  · exact lower_lo_gram_identity_row22 j
  · exact lower_lo_gram_identity_row23 j

theorem Tlo_gram_identity : ∀ (i : Fin 24) (j : Fin 24), (Tlo_Rden^2 • TloZ) i j = (den_lo • (Tlo_RZ.transpose * Tlo_RZ) + Tlo_EZ) i j := by
  intro i j
  fin_cases i
  · exact Tlo_gram_identity_row0 j
  · exact Tlo_gram_identity_row1 j
  · exact Tlo_gram_identity_row2 j
  · exact Tlo_gram_identity_row3 j
  · exact Tlo_gram_identity_row4 j
  · exact Tlo_gram_identity_row5 j
  · exact Tlo_gram_identity_row6 j
  · exact Tlo_gram_identity_row7 j
  · exact Tlo_gram_identity_row8 j
  · exact Tlo_gram_identity_row9 j
  · exact Tlo_gram_identity_row10 j
  · exact Tlo_gram_identity_row11 j
  · exact Tlo_gram_identity_row12 j
  · exact Tlo_gram_identity_row13 j
  · exact Tlo_gram_identity_row14 j
  · exact Tlo_gram_identity_row15 j
  · exact Tlo_gram_identity_row16 j
  · exact Tlo_gram_identity_row17 j
  · exact Tlo_gram_identity_row18 j
  · exact Tlo_gram_identity_row19 j
  · exact Tlo_gram_identity_row20 j
  · exact Tlo_gram_identity_row21 j
  · exact Tlo_gram_identity_row22 j
  · exact Tlo_gram_identity_row23 j

theorem lower_hi_gram_identity : ∀ (i : Fin 24) (j : Fin 24), (lower_hi_Rden^2 • lower_hiZ) i j = (den_hi • (lower_hi_RZ.transpose * lower_hi_RZ) + lower_hi_EZ) i j := by
  intro i j
  fin_cases i
  · exact lower_hi_gram_identity_row0 j
  · exact lower_hi_gram_identity_row1 j
  · exact lower_hi_gram_identity_row2 j
  · exact lower_hi_gram_identity_row3 j
  · exact lower_hi_gram_identity_row4 j
  · exact lower_hi_gram_identity_row5 j
  · exact lower_hi_gram_identity_row6 j
  · exact lower_hi_gram_identity_row7 j
  · exact lower_hi_gram_identity_row8 j
  · exact lower_hi_gram_identity_row9 j
  · exact lower_hi_gram_identity_row10 j
  · exact lower_hi_gram_identity_row11 j
  · exact lower_hi_gram_identity_row12 j
  · exact lower_hi_gram_identity_row13 j
  · exact lower_hi_gram_identity_row14 j
  · exact lower_hi_gram_identity_row15 j
  · exact lower_hi_gram_identity_row16 j
  · exact lower_hi_gram_identity_row17 j
  · exact lower_hi_gram_identity_row18 j
  · exact lower_hi_gram_identity_row19 j
  · exact lower_hi_gram_identity_row20 j
  · exact lower_hi_gram_identity_row21 j
  · exact lower_hi_gram_identity_row22 j
  · exact lower_hi_gram_identity_row23 j

theorem Thi_gram_identity : ∀ (i : Fin 24) (j : Fin 24), (Thi_Rden^2 • ThiZ) i j = (den_hi • (Thi_RZ.transpose * Thi_RZ) + Thi_EZ) i j := by
  intro i j
  fin_cases i
  · exact Thi_gram_identity_row0 j
  · exact Thi_gram_identity_row1 j
  · exact Thi_gram_identity_row2 j
  · exact Thi_gram_identity_row3 j
  · exact Thi_gram_identity_row4 j
  · exact Thi_gram_identity_row5 j
  · exact Thi_gram_identity_row6 j
  · exact Thi_gram_identity_row7 j
  · exact Thi_gram_identity_row8 j
  · exact Thi_gram_identity_row9 j
  · exact Thi_gram_identity_row10 j
  · exact Thi_gram_identity_row11 j
  · exact Thi_gram_identity_row12 j
  · exact Thi_gram_identity_row13 j
  · exact Thi_gram_identity_row14 j
  · exact Thi_gram_identity_row15 j
  · exact Thi_gram_identity_row16 j
  · exact Thi_gram_identity_row17 j
  · exact Thi_gram_identity_row18 j
  · exact Thi_gram_identity_row19 j
  · exact Thi_gram_identity_row20 j
  · exact Thi_gram_identity_row21 j
  · exact Thi_gram_identity_row22 j
  · exact Thi_gram_identity_row23 j

theorem weightedFZ_identity : ∀ (i : Fin 13) (j : Fin 26), weightedDifferences lambdaFZ xRowsZ i j = weightedFZ i j := by
  intro i j
  fin_cases i
  · exact weightedFZ_identity_row0 j
  · exact weightedFZ_identity_row1 j
  · exact weightedFZ_identity_row2 j
  · exact weightedFZ_identity_row3 j
  · exact weightedFZ_identity_row4 j
  · exact weightedFZ_identity_row5 j
  · exact weightedFZ_identity_row6 j
  · exact weightedFZ_identity_row7 j
  · exact weightedFZ_identity_row8 j
  · exact weightedFZ_identity_row9 j
  · exact weightedFZ_identity_row10 j
  · exact weightedFZ_identity_row11 j
  · exact weightedFZ_identity_row12 j

theorem weightedGZ_identity : ∀ (i : Fin 13) (j : Fin 26), weightedDifferences lambdaGZ zRowsZ i j = weightedGZ i j := by
  intro i j
  fin_cases i
  · exact weightedGZ_identity_row0 j
  · exact weightedGZ_identity_row1 j
  · exact weightedGZ_identity_row2 j
  · exact weightedGZ_identity_row3 j
  · exact weightedGZ_identity_row4 j
  · exact weightedGZ_identity_row5 j
  · exact weightedGZ_identity_row6 j
  · exact weightedGZ_identity_row7 j
  · exact weightedGZ_identity_row8 j
  · exact weightedGZ_identity_row9 j
  · exact weightedGZ_identity_row10 j
  · exact weightedGZ_identity_row11 j
  · exact weightedGZ_identity_row12 j

theorem endpoint_fast_lo : ∀ (i : Fin 26) (j : Fin 26), embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j + qFactor_lo * qsumFastZ tauNum_lo tauDen_lo i j = embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  intro i j
  fin_cases i
  · exact endpoint_fast_lo_row0 j
  · exact endpoint_fast_lo_row1 j
  · exact endpoint_fast_lo_row2 j
  · exact endpoint_fast_lo_row3 j
  · exact endpoint_fast_lo_row4 j
  · exact endpoint_fast_lo_row5 j
  · exact endpoint_fast_lo_row6 j
  · exact endpoint_fast_lo_row7 j
  · exact endpoint_fast_lo_row8 j
  · exact endpoint_fast_lo_row9 j
  · exact endpoint_fast_lo_row10 j
  · exact endpoint_fast_lo_row11 j
  · exact endpoint_fast_lo_row12 j
  · exact endpoint_fast_lo_row13 j
  · exact endpoint_fast_lo_row14 j
  · exact endpoint_fast_lo_row15 j
  · exact endpoint_fast_lo_row16 j
  · exact endpoint_fast_lo_row17 j
  · exact endpoint_fast_lo_row18 j
  · exact endpoint_fast_lo_row19 j
  · exact endpoint_fast_lo_row20 j
  · exact endpoint_fast_lo_row21 j
  · exact endpoint_fast_lo_row22 j
  · exact endpoint_fast_lo_row23 j
  · exact endpoint_fast_lo_row24 j
  · exact endpoint_fast_lo_row25 j

theorem endpoint_fast_hi : ∀ (i : Fin 26) (j : Fin 26), embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j + qFactor_hi * qsumFastZ tauNum_hi tauDen_hi i j = embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  intro i j
  fin_cases i
  · exact endpoint_fast_hi_row0 j
  · exact endpoint_fast_hi_row1 j
  · exact endpoint_fast_hi_row2 j
  · exact endpoint_fast_hi_row3 j
  · exact endpoint_fast_hi_row4 j
  · exact endpoint_fast_hi_row5 j
  · exact endpoint_fast_hi_row6 j
  · exact endpoint_fast_hi_row7 j
  · exact endpoint_fast_hi_row8 j
  · exact endpoint_fast_hi_row9 j
  · exact endpoint_fast_hi_row10 j
  · exact endpoint_fast_hi_row11 j
  · exact endpoint_fast_hi_row12 j
  · exact endpoint_fast_hi_row13 j
  · exact endpoint_fast_hi_row14 j
  · exact endpoint_fast_hi_row15 j
  · exact endpoint_fast_hi_row16 j
  · exact endpoint_fast_hi_row17 j
  · exact endpoint_fast_hi_row18 j
  · exact endpoint_fast_hi_row19 j
  · exact endpoint_fast_hi_row20 j
  · exact endpoint_fast_hi_row21 j
  · exact endpoint_fast_hi_row22 j
  · exact endpoint_fast_hi_row23 j
  · exact endpoint_fast_hi_row24 j
  · exact endpoint_fast_hi_row25 j

theorem weightedF_exact : weightedDifferences lambdaFZ xRowsZ = weightedFZ := by
  ext i j
  exact weightedFZ_identity i j

theorem weightedG_exact : weightedDifferences lambdaGZ zRowsZ = weightedGZ := by
  ext i j
  exact weightedGZ_identity i j

theorem crossZ_eq_integerCross (u v : Fin 26 → ℤ) :
    crossZ u v = ADMMNearSharpCertificate.integerCross u v := rfl

theorem qsumZ_fast_eq (a b : ℤ) : qsumZ a b = qsumFastZ a b := by
  unfold qsumZ qsumFastZ
  simp only [crossZ_eq_integerCross]
  rw [weighted_cross_sum, weighted_cross_sum, weightedF_exact, weightedG_exact]

private theorem S0Z_standard : S0Z = ADMMNearSharp.StandardRows.S0Z 11 := by
  ext i j
  exact (by decide +kernel : ∀ (i : Fin 24) (j : Fin 26),
    S0Z i j = ADMMNearSharp.StandardRows.S0Z 11 i j) i j

private theorem S1Z_standard : S1Z = ADMMNearSharp.StandardRows.S1Z 11 := by
  ext i j
  exact (by decide +kernel : ∀ (i : Fin 24) (j : Fin 26),
    S1Z i j = ADMMNearSharp.StandardRows.S1Z 11 i j) i j

theorem endpoint_identity_lo : ∀ i j : Fin 26,
    (S0Z.transpose * PloZ * S0Z - S1Z.transpose * PloZ * S1Z -
       den_lo • dissZ + qFactor_lo • qsumZ tauNum_lo tauDen_lo) i j =
    (diffRowsZ.transpose * TloZ * diffRowsZ) i j := by
  intro i j
  rw [qsumZ_fast_eq]
  simp only [diffRowsZ, S0Z_standard, S1Z_standard, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    S0_congruence_apply (d := 11), S1_congruence_apply (d := 11),
    difference_congruence_apply (d := 11)]
  exact endpoint_fast_lo i j

theorem endpoint_identity_hi : ∀ i j : Fin 26,
    (S0Z.transpose * PhiZ * S0Z - S1Z.transpose * PhiZ * S1Z -
       den_hi • dissZ + qFactor_hi • qsumZ tauNum_hi tauDen_hi) i j =
    (diffRowsZ.transpose * ThiZ * diffRowsZ) i j := by
  intro i j
  rw [qsumZ_fast_eq]
  simp only [diffRowsZ, S0Z_standard, S1Z_standard, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    S0_congruence_apply (d := 11), S1_congruence_apply (d := 11),
    difference_congruence_apply (d := 11)]
  exact endpoint_fast_hi i j

#print axioms endpoint_identity_lo
#print axioms endpoint_identity_hi
#print axioms lower_lo_gram_identity
#print axioms lower_hi_residual_dd

end ADMMNearSharpCertificate.Data188
