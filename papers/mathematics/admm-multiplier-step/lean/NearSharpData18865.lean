import IntegerCross
import IntegerEmbedding
import NearSharpData18865_lower_lo_gram
import NearSharpData18865_Tlo_gram
import NearSharpData18865_lower_hi_gram
import NearSharpData18865_Thi_gram
import NearSharpData18865_endpoint_lo
import NearSharpData18865_endpoint_hi
import NearSharpData18865_weightedF
import NearSharpData18865_weightedG
import NearSharpData18865_A_lo
import NearSharpData18865_B_lo
import NearSharpData18865_A_hi
import NearSharpData18865_B_hi
import NearSharpData18865_lower_lo_symmetric
import NearSharpData18865_Tlo_symmetric
import NearSharpData18865_lower_hi_symmetric
import NearSharpData18865_Thi_symmetric
import NearSharpData18865_aux

namespace ADMMNearSharpCertificate.Data18865

open scoped BigOperators
open ADMMNearSharp.StandardRows ADMMNearSharpCertificate.IntLists

set_option maxHeartbeats 0

theorem lower_lo_gram_identity : ∀ (i : Fin 40) (j : Fin 40), (lower_lo_Rden^2 • lower_loZ) i j = (den_lo • (lower_lo_RZ.transpose * lower_lo_RZ) + lower_lo_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, lower_lo_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact lower_lo_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact lower_lo_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact lower_lo_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact lower_lo_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact lower_lo_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact lower_lo_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact lower_lo_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact lower_lo_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 36 then exact lower_lo_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 36 ≤ i.val ∧ i.val < 40 then exact lower_lo_gram_ok_9 i h9.1 h9.2 j
  else omega

theorem lower_lo_residual_symmetric : ∀ i j : Fin 40, lower_lo_EZ i j = lower_lo_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 40, i.val < j.val → lower_lo_EZ i j = lower_lo_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 16 then exact lower_lo_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 16 ≤ i.val ∧ i.val < 32 then exact lower_lo_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 32 ≤ i.val ∧ i.val < 40 then exact lower_lo_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem lower_lo_residual_dd : ∀ i : Fin 40, (∑ j ∈ Finset.univ.erase i, |lower_lo_EZ i j|) ≤ lower_lo_EZ i i := by
  intro i
  exact dd_of_absSum lower_lo_EL i (lower_lo_dd_ok i)

theorem Tlo_gram_identity : ∀ (i : Fin 40) (j : Fin 40), (Tlo_Rden^2 • TloZ) i j = (den_lo • (Tlo_RZ.transpose * Tlo_RZ) + Tlo_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Tlo_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact Tlo_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact Tlo_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact Tlo_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact Tlo_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact Tlo_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact Tlo_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact Tlo_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact Tlo_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 36 then exact Tlo_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 36 ≤ i.val ∧ i.val < 40 then exact Tlo_gram_ok_9 i h9.1 h9.2 j
  else omega

theorem Tlo_residual_symmetric : ∀ i j : Fin 40, Tlo_EZ i j = Tlo_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 40, i.val < j.val → Tlo_EZ i j = Tlo_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 16 then exact Tlo_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 16 ≤ i.val ∧ i.val < 32 then exact Tlo_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 32 ≤ i.val ∧ i.val < 40 then exact Tlo_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem Tlo_residual_dd : ∀ i : Fin 40, (∑ j ∈ Finset.univ.erase i, |Tlo_EZ i j|) ≤ Tlo_EZ i i := by
  intro i
  exact dd_of_absSum Tlo_EL i (Tlo_dd_ok i)

theorem lower_hi_gram_identity : ∀ (i : Fin 40) (j : Fin 40), (lower_hi_Rden^2 • lower_hiZ) i j = (den_hi • (lower_hi_RZ.transpose * lower_hi_RZ) + lower_hi_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, lower_hi_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact lower_hi_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact lower_hi_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact lower_hi_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact lower_hi_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact lower_hi_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact lower_hi_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact lower_hi_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact lower_hi_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 36 then exact lower_hi_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 36 ≤ i.val ∧ i.val < 40 then exact lower_hi_gram_ok_9 i h9.1 h9.2 j
  else omega

theorem lower_hi_residual_symmetric : ∀ i j : Fin 40, lower_hi_EZ i j = lower_hi_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 40, i.val < j.val → lower_hi_EZ i j = lower_hi_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 16 then exact lower_hi_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 16 ≤ i.val ∧ i.val < 32 then exact lower_hi_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 32 ≤ i.val ∧ i.val < 40 then exact lower_hi_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem lower_hi_residual_dd : ∀ i : Fin 40, (∑ j ∈ Finset.univ.erase i, |lower_hi_EZ i j|) ≤ lower_hi_EZ i i := by
  intro i
  exact dd_of_absSum lower_hi_EL i (lower_hi_dd_ok i)

theorem Thi_gram_identity : ∀ (i : Fin 40) (j : Fin 40), (Thi_Rden^2 • ThiZ) i j = (den_hi • (Thi_RZ.transpose * Thi_RZ) + Thi_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Thi_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact Thi_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact Thi_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact Thi_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact Thi_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact Thi_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact Thi_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact Thi_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact Thi_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 36 then exact Thi_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 36 ≤ i.val ∧ i.val < 40 then exact Thi_gram_ok_9 i h9.1 h9.2 j
  else omega

theorem Thi_residual_symmetric : ∀ i j : Fin 40, Thi_EZ i j = Thi_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 40, i.val < j.val → Thi_EZ i j = Thi_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 16 then exact Thi_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 16 ≤ i.val ∧ i.val < 32 then exact Thi_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 32 ≤ i.val ∧ i.val < 40 then exact Thi_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem Thi_residual_dd : ∀ i : Fin 40, (∑ j ∈ Finset.univ.erase i, |Thi_EZ i j|) ≤ Thi_EZ i i := by
  intro i
  exact dd_of_absSum Thi_EL i (Thi_dd_ok i)

theorem weightedFZ_identity : ∀ (i : Fin 21) (j : Fin 42), IntArithmetic.weightedDifferences lambdaFZ xRowsZ i j = weightedFZ i j := by
  intro i j
  rw [lambdaFZ, xRowsZ, weighted_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 8 then exact weightedFZ_ok_0 i h0.1 h0.2 j
  else if h1 : 8 ≤ i.val ∧ i.val < 16 then exact weightedFZ_ok_1 i h1.1 h1.2 j
  else if h2 : 16 ≤ i.val ∧ i.val < 21 then exact weightedFZ_ok_2 i h2.1 h2.2 j
  else omega

theorem weightedF_exact : weightedDifferences lambdaFZ xRowsZ = weightedFZ := by
  ext i j
  exact weightedFZ_identity i j

theorem weightedGZ_identity : ∀ (i : Fin 21) (j : Fin 42), IntArithmetic.weightedDifferences lambdaGZ zRowsZ i j = weightedGZ i j := by
  intro i j
  rw [lambdaGZ, zRowsZ, weighted_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 8 then exact weightedGZ_ok_0 i h0.1 h0.2 j
  else if h1 : 8 ≤ i.val ∧ i.val < 16 then exact weightedGZ_ok_1 i h1.1 h1.2 j
  else if h2 : 16 ≤ i.val ∧ i.val < 21 then exact weightedGZ_ok_2 i h2.1 h2.2 j
  else omega

theorem weightedG_exact : weightedDifferences lambdaGZ zRowsZ = weightedGZ := by
  ext i j
  exact weightedGZ_identity i j

theorem A_lo_entry : ∀ (s : Fin 21) (k : Fin 42), aRowsZ tauNum_lo tauDen_lo s k = (A_loL.getD k.val []).getD s.val 0 := by
  intro s k
  have hA : ∀ k : Fin 42, A_loL.getD k.val [] = lin3N tauDen_lo (-tauNum_lo) (-tauDen_lo) 21 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) :=
    fun k => A_lo_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_lo (-tauNum_lo) (-tauDen_lo) A_loL prevZRowsL prevVRowsL xRowsL hA s k]
  simp only [aRowsZ, prevZRowsZ, prevVRowsZ, xRowsZ, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem B_lo_entry : ∀ (s : Fin 21) (k : Fin 42), bRowsZ tauNum_lo tauDen_lo s k = (B_loL.getD k.val []).getD s.val 0 := by
  intro s k
  have hB : ∀ k : Fin 42, B_loL.getD k.val [] = lin3N tauDen_lo tauNum_lo (-tauDen_lo) 21 (xRowsL.getD k.val []) (prevVRowsL.getD k.val []) (zRowsL.getD k.val []) :=
    fun k => B_lo_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_lo tauNum_lo (-tauDen_lo) B_loL xRowsL prevVRowsL zRowsL hB s k]
  simp only [bRowsZ, prevVRowsZ, xRowsZ, zRowsZ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem qsumFast_lo_entry (i j : Fin 42) : qsumFastZ tauNum_lo tauDen_lo i j =
    (dotN 21 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
      (dotN 21 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_loL.getD j.val [])) := by
  rw [qsumFastZ, Matrix.add_apply]
  simp only [crossZ]
  rw [cross_sum_entry (aRowsZ tauNum_lo tauDen_lo) weightedFZ A_loL weightedFL A_lo_entry (fun _ _ => rfl) i j,
    cross_sum_entry (bRowsZ tauNum_lo tauDen_lo) weightedGZ B_loL weightedGL B_lo_entry (fun _ _ => rfl) i j]

theorem endpoint_fast_lo : ∀ (i : Fin 42) (j : Fin 42), embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j + qFactor_lo * qsumFastZ tauNum_lo tauDen_lo i j = embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  intro i j
  rw [qsumFast_lo_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact endpoint_lo_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact endpoint_lo_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact endpoint_lo_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact endpoint_lo_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact endpoint_lo_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact endpoint_lo_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact endpoint_lo_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact endpoint_lo_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 36 then exact endpoint_lo_ok_8 i h8.1 h8.2 j
  else if h9 : 36 ≤ i.val ∧ i.val < 40 then exact endpoint_lo_ok_9 i h9.1 h9.2 j
  else if h10 : 40 ≤ i.val ∧ i.val < 42 then exact endpoint_lo_ok_10 i h10.1 h10.2 j
  else omega

theorem A_hi_entry : ∀ (s : Fin 21) (k : Fin 42), aRowsZ tauNum_hi tauDen_hi s k = (A_hiL.getD k.val []).getD s.val 0 := by
  intro s k
  have hA : ∀ k : Fin 42, A_hiL.getD k.val [] = lin3N tauDen_hi (-tauNum_hi) (-tauDen_hi) 21 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) :=
    fun k => A_hi_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_hi (-tauNum_hi) (-tauDen_hi) A_hiL prevZRowsL prevVRowsL xRowsL hA s k]
  simp only [aRowsZ, prevZRowsZ, prevVRowsZ, xRowsZ, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem B_hi_entry : ∀ (s : Fin 21) (k : Fin 42), bRowsZ tauNum_hi tauDen_hi s k = (B_hiL.getD k.val []).getD s.val 0 := by
  intro s k
  have hB : ∀ k : Fin 42, B_hiL.getD k.val [] = lin3N tauDen_hi tauNum_hi (-tauDen_hi) 21 (xRowsL.getD k.val []) (prevVRowsL.getD k.val []) (zRowsL.getD k.val []) :=
    fun k => B_hi_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_hi tauNum_hi (-tauDen_hi) B_hiL xRowsL prevVRowsL zRowsL hB s k]
  simp only [bRowsZ, prevVRowsZ, xRowsZ, zRowsZ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem qsumFast_hi_entry (i j : Fin 42) : qsumFastZ tauNum_hi tauDen_hi i j =
    (dotN 21 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 21 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
      (dotN 21 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 21 (weightedGL.getD i.val []) (B_hiL.getD j.val [])) := by
  rw [qsumFastZ, Matrix.add_apply]
  simp only [crossZ]
  rw [cross_sum_entry (aRowsZ tauNum_hi tauDen_hi) weightedFZ A_hiL weightedFL A_hi_entry (fun _ _ => rfl) i j,
    cross_sum_entry (bRowsZ tauNum_hi tauDen_hi) weightedGZ B_hiL weightedGL B_hi_entry (fun _ _ => rfl) i j]

theorem endpoint_fast_hi : ∀ (i : Fin 42) (j : Fin 42), embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j + qFactor_hi * qsumFastZ tauNum_hi tauDen_hi i j = embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  intro i j
  rw [qsumFast_hi_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact endpoint_hi_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact endpoint_hi_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact endpoint_hi_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact endpoint_hi_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact endpoint_hi_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact endpoint_hi_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact endpoint_hi_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact endpoint_hi_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 36 then exact endpoint_hi_ok_8 i h8.1 h8.2 j
  else if h9 : 36 ≤ i.val ∧ i.val < 40 then exact endpoint_hi_ok_9 i h9.1 h9.2 j
  else if h10 : 40 ≤ i.val ∧ i.val < 42 then exact endpoint_hi_ok_10 i h10.1 h10.2 j
  else omega

theorem crossZ_eq_integerCross (u v : Fin 42 → ℤ) :
    crossZ u v = ADMMNearSharpCertificate.integerCross u v := rfl

theorem qsumZ_fast_eq (a b : ℤ) : qsumZ a b = qsumFastZ a b := by
  unfold qsumZ qsumFastZ
  simp only [crossZ_eq_integerCross]
  rw [weighted_cross_sum, weighted_cross_sum, weightedF_exact, weightedG_exact]

private theorem S0Z_standard : S0Z = ADMMNearSharp.StandardRows.S0Z 19 := rfl

private theorem S1Z_standard : S1Z = ADMMNearSharp.StandardRows.S1Z 19 := rfl

theorem endpoint_identity_lo : ∀ i j : Fin 42,
    (S0Z.transpose * PloZ * S0Z - S1Z.transpose * PloZ * S1Z -
       den_lo • dissZ + qFactor_lo • qsumZ tauNum_lo tauDen_lo) i j =
    (diffRowsZ.transpose * TloZ * diffRowsZ) i j := by
  intro i j
  rw [qsumZ_fast_eq]
  simp only [diffRowsZ, S0Z_standard, S1Z_standard, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    S0_congruence_apply (d := 19), S1_congruence_apply (d := 19),
    difference_congruence_apply (d := 19)]
  exact endpoint_fast_lo i j

theorem endpoint_identity_hi : ∀ i j : Fin 42,
    (S0Z.transpose * PhiZ * S0Z - S1Z.transpose * PhiZ * S1Z -
       den_hi • dissZ + qFactor_hi • qsumZ tauNum_hi tauDen_hi) i j =
    (diffRowsZ.transpose * ThiZ * diffRowsZ) i j := by
  intro i j
  rw [qsumZ_fast_eq]
  simp only [diffRowsZ, S0Z_standard, S1Z_standard, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    S0_congruence_apply (d := 19), S1_congruence_apply (d := 19),
    difference_congruence_apply (d := 19)]
  exact endpoint_fast_hi i j

#print axioms endpoint_identity_lo
#print axioms endpoint_identity_hi
#print axioms lower_lo_gram_identity
#print axioms lower_hi_residual_dd

end ADMMNearSharpCertificate.Data18865
