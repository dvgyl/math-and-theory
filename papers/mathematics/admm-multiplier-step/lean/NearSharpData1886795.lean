import IntegerCross
import IntegerEmbedding
import NearSharpData1886795_lower_lo_gram_0
import NearSharpData1886795_lower_lo_gram_1
import NearSharpData1886795_lower_lo_gram_2
import NearSharpData1886795_lower_lo_gram_3
import NearSharpData1886795_Tlo_gram_0
import NearSharpData1886795_Tlo_gram_1
import NearSharpData1886795_Tlo_gram_2
import NearSharpData1886795_Tlo_gram_3
import NearSharpData1886795_lower_hi_gram_0
import NearSharpData1886795_lower_hi_gram_1
import NearSharpData1886795_lower_hi_gram_2
import NearSharpData1886795_lower_hi_gram_3
import NearSharpData1886795_Thi_gram_0
import NearSharpData1886795_Thi_gram_1
import NearSharpData1886795_Thi_gram_2
import NearSharpData1886795_Thi_gram_3
import NearSharpData1886795_endpoint_lo_0
import NearSharpData1886795_endpoint_lo_1
import NearSharpData1886795_endpoint_lo_2
import NearSharpData1886795_endpoint_lo_3
import NearSharpData1886795_endpoint_lo_4
import NearSharpData1886795_endpoint_hi_0
import NearSharpData1886795_endpoint_hi_1
import NearSharpData1886795_endpoint_hi_2
import NearSharpData1886795_endpoint_hi_3
import NearSharpData1886795_endpoint_hi_4
import NearSharpData1886795_weightedF_0
import NearSharpData1886795_weightedF_1
import NearSharpData1886795_weightedG_0
import NearSharpData1886795_weightedG_1
import NearSharpData1886795_A_lo
import NearSharpData1886795_B_lo
import NearSharpData1886795_A_hi
import NearSharpData1886795_B_hi
import NearSharpData1886795_lower_lo_symmetric
import NearSharpData1886795_Tlo_symmetric
import NearSharpData1886795_lower_hi_symmetric
import NearSharpData1886795_Thi_symmetric
import NearSharpData1886795_aux

namespace ADMMNearSharpCertificate.Data1886795

open scoped BigOperators
open ADMMNearSharp.StandardRows ADMMNearSharpCertificate.IntLists

set_option maxHeartbeats 0

theorem lower_lo_gram_identity : ∀ (i : Fin 64) (j : Fin 64), (lower_lo_Rden^2 • lower_loZ) i j = (den_lo • (lower_lo_RZ.transpose * lower_lo_RZ) + lower_lo_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, lower_lo_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 2 then exact lower_lo_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 2 ≤ i.val ∧ i.val < 4 then exact lower_lo_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 4 ≤ i.val ∧ i.val < 6 then exact lower_lo_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 6 ≤ i.val ∧ i.val < 8 then exact lower_lo_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 8 ≤ i.val ∧ i.val < 10 then exact lower_lo_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 10 ≤ i.val ∧ i.val < 12 then exact lower_lo_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 12 ≤ i.val ∧ i.val < 14 then exact lower_lo_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 14 ≤ i.val ∧ i.val < 16 then exact lower_lo_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 16 ≤ i.val ∧ i.val < 18 then exact lower_lo_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 18 ≤ i.val ∧ i.val < 20 then exact lower_lo_gram_ok_9 i h9.1 h9.2 j
  else if h10 : 20 ≤ i.val ∧ i.val < 22 then exact lower_lo_gram_ok_10 i h10.1 h10.2 j
  else if h11 : 22 ≤ i.val ∧ i.val < 24 then exact lower_lo_gram_ok_11 i h11.1 h11.2 j
  else if h12 : 24 ≤ i.val ∧ i.val < 26 then exact lower_lo_gram_ok_12 i h12.1 h12.2 j
  else if h13 : 26 ≤ i.val ∧ i.val < 28 then exact lower_lo_gram_ok_13 i h13.1 h13.2 j
  else if h14 : 28 ≤ i.val ∧ i.val < 30 then exact lower_lo_gram_ok_14 i h14.1 h14.2 j
  else if h15 : 30 ≤ i.val ∧ i.val < 32 then exact lower_lo_gram_ok_15 i h15.1 h15.2 j
  else if h16 : 32 ≤ i.val ∧ i.val < 34 then exact lower_lo_gram_ok_16 i h16.1 h16.2 j
  else if h17 : 34 ≤ i.val ∧ i.val < 36 then exact lower_lo_gram_ok_17 i h17.1 h17.2 j
  else if h18 : 36 ≤ i.val ∧ i.val < 38 then exact lower_lo_gram_ok_18 i h18.1 h18.2 j
  else if h19 : 38 ≤ i.val ∧ i.val < 40 then exact lower_lo_gram_ok_19 i h19.1 h19.2 j
  else if h20 : 40 ≤ i.val ∧ i.val < 42 then exact lower_lo_gram_ok_20 i h20.1 h20.2 j
  else if h21 : 42 ≤ i.val ∧ i.val < 44 then exact lower_lo_gram_ok_21 i h21.1 h21.2 j
  else if h22 : 44 ≤ i.val ∧ i.val < 46 then exact lower_lo_gram_ok_22 i h22.1 h22.2 j
  else if h23 : 46 ≤ i.val ∧ i.val < 48 then exact lower_lo_gram_ok_23 i h23.1 h23.2 j
  else if h24 : 48 ≤ i.val ∧ i.val < 50 then exact lower_lo_gram_ok_24 i h24.1 h24.2 j
  else if h25 : 50 ≤ i.val ∧ i.val < 52 then exact lower_lo_gram_ok_25 i h25.1 h25.2 j
  else if h26 : 52 ≤ i.val ∧ i.val < 54 then exact lower_lo_gram_ok_26 i h26.1 h26.2 j
  else if h27 : 54 ≤ i.val ∧ i.val < 56 then exact lower_lo_gram_ok_27 i h27.1 h27.2 j
  else if h28 : 56 ≤ i.val ∧ i.val < 58 then exact lower_lo_gram_ok_28 i h28.1 h28.2 j
  else if h29 : 58 ≤ i.val ∧ i.val < 60 then exact lower_lo_gram_ok_29 i h29.1 h29.2 j
  else if h30 : 60 ≤ i.val ∧ i.val < 62 then exact lower_lo_gram_ok_30 i h30.1 h30.2 j
  else if h31 : 62 ≤ i.val ∧ i.val < 64 then exact lower_lo_gram_ok_31 i h31.1 h31.2 j
  else omega

theorem lower_lo_residual_symmetric : ∀ i j : Fin 64, lower_lo_EZ i j = lower_lo_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 64, i.val < j.val → lower_lo_EZ i j = lower_lo_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 8 then exact lower_lo_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 8 ≤ i.val ∧ i.val < 16 then exact lower_lo_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 16 ≤ i.val ∧ i.val < 24 then exact lower_lo_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else if h3 : 24 ≤ i.val ∧ i.val < 32 then exact lower_lo_residual_upper_symmetric_3 i h3.1 h3.2 j hij
    else if h4 : 32 ≤ i.val ∧ i.val < 40 then exact lower_lo_residual_upper_symmetric_4 i h4.1 h4.2 j hij
    else if h5 : 40 ≤ i.val ∧ i.val < 48 then exact lower_lo_residual_upper_symmetric_5 i h5.1 h5.2 j hij
    else if h6 : 48 ≤ i.val ∧ i.val < 56 then exact lower_lo_residual_upper_symmetric_6 i h6.1 h6.2 j hij
    else if h7 : 56 ≤ i.val ∧ i.val < 64 then exact lower_lo_residual_upper_symmetric_7 i h7.1 h7.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem lower_lo_residual_dd : ∀ i : Fin 64, (∑ j ∈ Finset.univ.erase i, |lower_lo_EZ i j|) ≤ lower_lo_EZ i i := by
  intro i
  exact dd_of_absSum lower_lo_EL i (lower_lo_dd_ok i)

theorem Tlo_gram_identity : ∀ (i : Fin 64) (j : Fin 64), (Tlo_Rden^2 • TloZ) i j = (den_lo • (Tlo_RZ.transpose * Tlo_RZ) + Tlo_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Tlo_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 2 then exact Tlo_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 2 ≤ i.val ∧ i.val < 4 then exact Tlo_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 4 ≤ i.val ∧ i.val < 6 then exact Tlo_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 6 ≤ i.val ∧ i.val < 8 then exact Tlo_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 8 ≤ i.val ∧ i.val < 10 then exact Tlo_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 10 ≤ i.val ∧ i.val < 12 then exact Tlo_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 12 ≤ i.val ∧ i.val < 14 then exact Tlo_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 14 ≤ i.val ∧ i.val < 16 then exact Tlo_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 16 ≤ i.val ∧ i.val < 18 then exact Tlo_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 18 ≤ i.val ∧ i.val < 20 then exact Tlo_gram_ok_9 i h9.1 h9.2 j
  else if h10 : 20 ≤ i.val ∧ i.val < 22 then exact Tlo_gram_ok_10 i h10.1 h10.2 j
  else if h11 : 22 ≤ i.val ∧ i.val < 24 then exact Tlo_gram_ok_11 i h11.1 h11.2 j
  else if h12 : 24 ≤ i.val ∧ i.val < 26 then exact Tlo_gram_ok_12 i h12.1 h12.2 j
  else if h13 : 26 ≤ i.val ∧ i.val < 28 then exact Tlo_gram_ok_13 i h13.1 h13.2 j
  else if h14 : 28 ≤ i.val ∧ i.val < 30 then exact Tlo_gram_ok_14 i h14.1 h14.2 j
  else if h15 : 30 ≤ i.val ∧ i.val < 32 then exact Tlo_gram_ok_15 i h15.1 h15.2 j
  else if h16 : 32 ≤ i.val ∧ i.val < 34 then exact Tlo_gram_ok_16 i h16.1 h16.2 j
  else if h17 : 34 ≤ i.val ∧ i.val < 36 then exact Tlo_gram_ok_17 i h17.1 h17.2 j
  else if h18 : 36 ≤ i.val ∧ i.val < 38 then exact Tlo_gram_ok_18 i h18.1 h18.2 j
  else if h19 : 38 ≤ i.val ∧ i.val < 40 then exact Tlo_gram_ok_19 i h19.1 h19.2 j
  else if h20 : 40 ≤ i.val ∧ i.val < 42 then exact Tlo_gram_ok_20 i h20.1 h20.2 j
  else if h21 : 42 ≤ i.val ∧ i.val < 44 then exact Tlo_gram_ok_21 i h21.1 h21.2 j
  else if h22 : 44 ≤ i.val ∧ i.val < 46 then exact Tlo_gram_ok_22 i h22.1 h22.2 j
  else if h23 : 46 ≤ i.val ∧ i.val < 48 then exact Tlo_gram_ok_23 i h23.1 h23.2 j
  else if h24 : 48 ≤ i.val ∧ i.val < 50 then exact Tlo_gram_ok_24 i h24.1 h24.2 j
  else if h25 : 50 ≤ i.val ∧ i.val < 52 then exact Tlo_gram_ok_25 i h25.1 h25.2 j
  else if h26 : 52 ≤ i.val ∧ i.val < 54 then exact Tlo_gram_ok_26 i h26.1 h26.2 j
  else if h27 : 54 ≤ i.val ∧ i.val < 56 then exact Tlo_gram_ok_27 i h27.1 h27.2 j
  else if h28 : 56 ≤ i.val ∧ i.val < 58 then exact Tlo_gram_ok_28 i h28.1 h28.2 j
  else if h29 : 58 ≤ i.val ∧ i.val < 60 then exact Tlo_gram_ok_29 i h29.1 h29.2 j
  else if h30 : 60 ≤ i.val ∧ i.val < 62 then exact Tlo_gram_ok_30 i h30.1 h30.2 j
  else if h31 : 62 ≤ i.val ∧ i.val < 64 then exact Tlo_gram_ok_31 i h31.1 h31.2 j
  else omega

theorem Tlo_residual_symmetric : ∀ i j : Fin 64, Tlo_EZ i j = Tlo_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 64, i.val < j.val → Tlo_EZ i j = Tlo_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 8 then exact Tlo_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 8 ≤ i.val ∧ i.val < 16 then exact Tlo_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 16 ≤ i.val ∧ i.val < 24 then exact Tlo_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else if h3 : 24 ≤ i.val ∧ i.val < 32 then exact Tlo_residual_upper_symmetric_3 i h3.1 h3.2 j hij
    else if h4 : 32 ≤ i.val ∧ i.val < 40 then exact Tlo_residual_upper_symmetric_4 i h4.1 h4.2 j hij
    else if h5 : 40 ≤ i.val ∧ i.val < 48 then exact Tlo_residual_upper_symmetric_5 i h5.1 h5.2 j hij
    else if h6 : 48 ≤ i.val ∧ i.val < 56 then exact Tlo_residual_upper_symmetric_6 i h6.1 h6.2 j hij
    else if h7 : 56 ≤ i.val ∧ i.val < 64 then exact Tlo_residual_upper_symmetric_7 i h7.1 h7.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem Tlo_residual_dd : ∀ i : Fin 64, (∑ j ∈ Finset.univ.erase i, |Tlo_EZ i j|) ≤ Tlo_EZ i i := by
  intro i
  exact dd_of_absSum Tlo_EL i (Tlo_dd_ok i)

theorem lower_hi_gram_identity : ∀ (i : Fin 64) (j : Fin 64), (lower_hi_Rden^2 • lower_hiZ) i j = (den_hi • (lower_hi_RZ.transpose * lower_hi_RZ) + lower_hi_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, lower_hi_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 2 then exact lower_hi_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 2 ≤ i.val ∧ i.val < 4 then exact lower_hi_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 4 ≤ i.val ∧ i.val < 6 then exact lower_hi_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 6 ≤ i.val ∧ i.val < 8 then exact lower_hi_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 8 ≤ i.val ∧ i.val < 10 then exact lower_hi_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 10 ≤ i.val ∧ i.val < 12 then exact lower_hi_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 12 ≤ i.val ∧ i.val < 14 then exact lower_hi_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 14 ≤ i.val ∧ i.val < 16 then exact lower_hi_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 16 ≤ i.val ∧ i.val < 18 then exact lower_hi_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 18 ≤ i.val ∧ i.val < 20 then exact lower_hi_gram_ok_9 i h9.1 h9.2 j
  else if h10 : 20 ≤ i.val ∧ i.val < 22 then exact lower_hi_gram_ok_10 i h10.1 h10.2 j
  else if h11 : 22 ≤ i.val ∧ i.val < 24 then exact lower_hi_gram_ok_11 i h11.1 h11.2 j
  else if h12 : 24 ≤ i.val ∧ i.val < 26 then exact lower_hi_gram_ok_12 i h12.1 h12.2 j
  else if h13 : 26 ≤ i.val ∧ i.val < 28 then exact lower_hi_gram_ok_13 i h13.1 h13.2 j
  else if h14 : 28 ≤ i.val ∧ i.val < 30 then exact lower_hi_gram_ok_14 i h14.1 h14.2 j
  else if h15 : 30 ≤ i.val ∧ i.val < 32 then exact lower_hi_gram_ok_15 i h15.1 h15.2 j
  else if h16 : 32 ≤ i.val ∧ i.val < 34 then exact lower_hi_gram_ok_16 i h16.1 h16.2 j
  else if h17 : 34 ≤ i.val ∧ i.val < 36 then exact lower_hi_gram_ok_17 i h17.1 h17.2 j
  else if h18 : 36 ≤ i.val ∧ i.val < 38 then exact lower_hi_gram_ok_18 i h18.1 h18.2 j
  else if h19 : 38 ≤ i.val ∧ i.val < 40 then exact lower_hi_gram_ok_19 i h19.1 h19.2 j
  else if h20 : 40 ≤ i.val ∧ i.val < 42 then exact lower_hi_gram_ok_20 i h20.1 h20.2 j
  else if h21 : 42 ≤ i.val ∧ i.val < 44 then exact lower_hi_gram_ok_21 i h21.1 h21.2 j
  else if h22 : 44 ≤ i.val ∧ i.val < 46 then exact lower_hi_gram_ok_22 i h22.1 h22.2 j
  else if h23 : 46 ≤ i.val ∧ i.val < 48 then exact lower_hi_gram_ok_23 i h23.1 h23.2 j
  else if h24 : 48 ≤ i.val ∧ i.val < 50 then exact lower_hi_gram_ok_24 i h24.1 h24.2 j
  else if h25 : 50 ≤ i.val ∧ i.val < 52 then exact lower_hi_gram_ok_25 i h25.1 h25.2 j
  else if h26 : 52 ≤ i.val ∧ i.val < 54 then exact lower_hi_gram_ok_26 i h26.1 h26.2 j
  else if h27 : 54 ≤ i.val ∧ i.val < 56 then exact lower_hi_gram_ok_27 i h27.1 h27.2 j
  else if h28 : 56 ≤ i.val ∧ i.val < 58 then exact lower_hi_gram_ok_28 i h28.1 h28.2 j
  else if h29 : 58 ≤ i.val ∧ i.val < 60 then exact lower_hi_gram_ok_29 i h29.1 h29.2 j
  else if h30 : 60 ≤ i.val ∧ i.val < 62 then exact lower_hi_gram_ok_30 i h30.1 h30.2 j
  else if h31 : 62 ≤ i.val ∧ i.val < 64 then exact lower_hi_gram_ok_31 i h31.1 h31.2 j
  else omega

theorem lower_hi_residual_symmetric : ∀ i j : Fin 64, lower_hi_EZ i j = lower_hi_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 64, i.val < j.val → lower_hi_EZ i j = lower_hi_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 8 then exact lower_hi_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 8 ≤ i.val ∧ i.val < 16 then exact lower_hi_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 16 ≤ i.val ∧ i.val < 24 then exact lower_hi_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else if h3 : 24 ≤ i.val ∧ i.val < 32 then exact lower_hi_residual_upper_symmetric_3 i h3.1 h3.2 j hij
    else if h4 : 32 ≤ i.val ∧ i.val < 40 then exact lower_hi_residual_upper_symmetric_4 i h4.1 h4.2 j hij
    else if h5 : 40 ≤ i.val ∧ i.val < 48 then exact lower_hi_residual_upper_symmetric_5 i h5.1 h5.2 j hij
    else if h6 : 48 ≤ i.val ∧ i.val < 56 then exact lower_hi_residual_upper_symmetric_6 i h6.1 h6.2 j hij
    else if h7 : 56 ≤ i.val ∧ i.val < 64 then exact lower_hi_residual_upper_symmetric_7 i h7.1 h7.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem lower_hi_residual_dd : ∀ i : Fin 64, (∑ j ∈ Finset.univ.erase i, |lower_hi_EZ i j|) ≤ lower_hi_EZ i i := by
  intro i
  exact dd_of_absSum lower_hi_EL i (lower_hi_dd_ok i)

theorem Thi_gram_identity : ∀ (i : Fin 64) (j : Fin 64), (Thi_Rden^2 • ThiZ) i j = (den_hi • (Thi_RZ.transpose * Thi_RZ) + Thi_EZ) i j := by
  intro i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Thi_RZ, gram_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 2 then exact Thi_gram_ok_0 i h0.1 h0.2 j
  else if h1 : 2 ≤ i.val ∧ i.val < 4 then exact Thi_gram_ok_1 i h1.1 h1.2 j
  else if h2 : 4 ≤ i.val ∧ i.val < 6 then exact Thi_gram_ok_2 i h2.1 h2.2 j
  else if h3 : 6 ≤ i.val ∧ i.val < 8 then exact Thi_gram_ok_3 i h3.1 h3.2 j
  else if h4 : 8 ≤ i.val ∧ i.val < 10 then exact Thi_gram_ok_4 i h4.1 h4.2 j
  else if h5 : 10 ≤ i.val ∧ i.val < 12 then exact Thi_gram_ok_5 i h5.1 h5.2 j
  else if h6 : 12 ≤ i.val ∧ i.val < 14 then exact Thi_gram_ok_6 i h6.1 h6.2 j
  else if h7 : 14 ≤ i.val ∧ i.val < 16 then exact Thi_gram_ok_7 i h7.1 h7.2 j
  else if h8 : 16 ≤ i.val ∧ i.val < 18 then exact Thi_gram_ok_8 i h8.1 h8.2 j
  else if h9 : 18 ≤ i.val ∧ i.val < 20 then exact Thi_gram_ok_9 i h9.1 h9.2 j
  else if h10 : 20 ≤ i.val ∧ i.val < 22 then exact Thi_gram_ok_10 i h10.1 h10.2 j
  else if h11 : 22 ≤ i.val ∧ i.val < 24 then exact Thi_gram_ok_11 i h11.1 h11.2 j
  else if h12 : 24 ≤ i.val ∧ i.val < 26 then exact Thi_gram_ok_12 i h12.1 h12.2 j
  else if h13 : 26 ≤ i.val ∧ i.val < 28 then exact Thi_gram_ok_13 i h13.1 h13.2 j
  else if h14 : 28 ≤ i.val ∧ i.val < 30 then exact Thi_gram_ok_14 i h14.1 h14.2 j
  else if h15 : 30 ≤ i.val ∧ i.val < 32 then exact Thi_gram_ok_15 i h15.1 h15.2 j
  else if h16 : 32 ≤ i.val ∧ i.val < 34 then exact Thi_gram_ok_16 i h16.1 h16.2 j
  else if h17 : 34 ≤ i.val ∧ i.val < 36 then exact Thi_gram_ok_17 i h17.1 h17.2 j
  else if h18 : 36 ≤ i.val ∧ i.val < 38 then exact Thi_gram_ok_18 i h18.1 h18.2 j
  else if h19 : 38 ≤ i.val ∧ i.val < 40 then exact Thi_gram_ok_19 i h19.1 h19.2 j
  else if h20 : 40 ≤ i.val ∧ i.val < 42 then exact Thi_gram_ok_20 i h20.1 h20.2 j
  else if h21 : 42 ≤ i.val ∧ i.val < 44 then exact Thi_gram_ok_21 i h21.1 h21.2 j
  else if h22 : 44 ≤ i.val ∧ i.val < 46 then exact Thi_gram_ok_22 i h22.1 h22.2 j
  else if h23 : 46 ≤ i.val ∧ i.val < 48 then exact Thi_gram_ok_23 i h23.1 h23.2 j
  else if h24 : 48 ≤ i.val ∧ i.val < 50 then exact Thi_gram_ok_24 i h24.1 h24.2 j
  else if h25 : 50 ≤ i.val ∧ i.val < 52 then exact Thi_gram_ok_25 i h25.1 h25.2 j
  else if h26 : 52 ≤ i.val ∧ i.val < 54 then exact Thi_gram_ok_26 i h26.1 h26.2 j
  else if h27 : 54 ≤ i.val ∧ i.val < 56 then exact Thi_gram_ok_27 i h27.1 h27.2 j
  else if h28 : 56 ≤ i.val ∧ i.val < 58 then exact Thi_gram_ok_28 i h28.1 h28.2 j
  else if h29 : 58 ≤ i.val ∧ i.val < 60 then exact Thi_gram_ok_29 i h29.1 h29.2 j
  else if h30 : 60 ≤ i.val ∧ i.val < 62 then exact Thi_gram_ok_30 i h30.1 h30.2 j
  else if h31 : 62 ≤ i.val ∧ i.val < 64 then exact Thi_gram_ok_31 i h31.1 h31.2 j
  else omega

theorem Thi_residual_symmetric : ∀ i j : Fin 64, Thi_EZ i j = Thi_EZ j i := by
  intro i j
  have upper : ∀ i j : Fin 64, i.val < j.val → Thi_EZ i j = Thi_EZ j i := by
    intro i j hij
    have hlt := i.isLt
    if h0 : 0 ≤ i.val ∧ i.val < 8 then exact Thi_residual_upper_symmetric_0 i h0.1 h0.2 j hij
    else if h1 : 8 ≤ i.val ∧ i.val < 16 then exact Thi_residual_upper_symmetric_1 i h1.1 h1.2 j hij
    else if h2 : 16 ≤ i.val ∧ i.val < 24 then exact Thi_residual_upper_symmetric_2 i h2.1 h2.2 j hij
    else if h3 : 24 ≤ i.val ∧ i.val < 32 then exact Thi_residual_upper_symmetric_3 i h3.1 h3.2 j hij
    else if h4 : 32 ≤ i.val ∧ i.val < 40 then exact Thi_residual_upper_symmetric_4 i h4.1 h4.2 j hij
    else if h5 : 40 ≤ i.val ∧ i.val < 48 then exact Thi_residual_upper_symmetric_5 i h5.1 h5.2 j hij
    else if h6 : 48 ≤ i.val ∧ i.val < 56 then exact Thi_residual_upper_symmetric_6 i h6.1 h6.2 j hij
    else if h7 : 56 ≤ i.val ∧ i.val < 64 then exact Thi_residual_upper_symmetric_7 i h7.1 h7.2 j hij
    else omega
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact upper i j h
  · rw [Fin.ext h]
  · exact (upper j i h).symm

theorem Thi_residual_dd : ∀ i : Fin 64, (∑ j ∈ Finset.univ.erase i, |Thi_EZ i j|) ≤ Thi_EZ i i := by
  intro i
  exact dd_of_absSum Thi_EL i (Thi_dd_ok i)

theorem weightedFZ_identity : ∀ (i : Fin 33) (j : Fin 66), IntArithmetic.weightedDifferences lambdaFZ xRowsZ i j = weightedFZ i j := by
  intro i j
  rw [lambdaFZ, xRowsZ, weighted_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact weightedFZ_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact weightedFZ_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact weightedFZ_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact weightedFZ_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact weightedFZ_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact weightedFZ_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact weightedFZ_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact weightedFZ_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 33 then exact weightedFZ_ok_8 i h8.1 h8.2 j
  else omega

theorem weightedF_exact : weightedDifferences lambdaFZ xRowsZ = weightedFZ := by
  ext i j
  exact weightedFZ_identity i j

theorem weightedGZ_identity : ∀ (i : Fin 33) (j : Fin 66), IntArithmetic.weightedDifferences lambdaGZ zRowsZ i j = weightedGZ i j := by
  intro i j
  rw [lambdaGZ, zRowsZ, weighted_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 4 then exact weightedGZ_ok_0 i h0.1 h0.2 j
  else if h1 : 4 ≤ i.val ∧ i.val < 8 then exact weightedGZ_ok_1 i h1.1 h1.2 j
  else if h2 : 8 ≤ i.val ∧ i.val < 12 then exact weightedGZ_ok_2 i h2.1 h2.2 j
  else if h3 : 12 ≤ i.val ∧ i.val < 16 then exact weightedGZ_ok_3 i h3.1 h3.2 j
  else if h4 : 16 ≤ i.val ∧ i.val < 20 then exact weightedGZ_ok_4 i h4.1 h4.2 j
  else if h5 : 20 ≤ i.val ∧ i.val < 24 then exact weightedGZ_ok_5 i h5.1 h5.2 j
  else if h6 : 24 ≤ i.val ∧ i.val < 28 then exact weightedGZ_ok_6 i h6.1 h6.2 j
  else if h7 : 28 ≤ i.val ∧ i.val < 32 then exact weightedGZ_ok_7 i h7.1 h7.2 j
  else if h8 : 32 ≤ i.val ∧ i.val < 33 then exact weightedGZ_ok_8 i h8.1 h8.2 j
  else omega

theorem weightedG_exact : weightedDifferences lambdaGZ zRowsZ = weightedGZ := by
  ext i j
  exact weightedGZ_identity i j

theorem A_lo_entry : ∀ (s : Fin 33) (k : Fin 66), aRowsZ tauNum_lo tauDen_lo s k = (A_loL.getD k.val []).getD s.val 0 := by
  intro s k
  have hA : ∀ k : Fin 66, A_loL.getD k.val [] = lin3N tauDen_lo (-tauNum_lo) (-tauDen_lo) 33 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) :=
    fun k => A_lo_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_lo (-tauNum_lo) (-tauDen_lo) A_loL prevZRowsL prevVRowsL xRowsL hA s k]
  simp only [aRowsZ, prevZRowsZ, prevVRowsZ, xRowsZ, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem B_lo_entry : ∀ (s : Fin 33) (k : Fin 66), bRowsZ tauNum_lo tauDen_lo s k = (B_loL.getD k.val []).getD s.val 0 := by
  intro s k
  have hB : ∀ k : Fin 66, B_loL.getD k.val [] = lin3N tauDen_lo tauNum_lo (-tauDen_lo) 33 (xRowsL.getD k.val []) (prevVRowsL.getD k.val []) (zRowsL.getD k.val []) :=
    fun k => B_lo_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_lo tauNum_lo (-tauDen_lo) B_loL xRowsL prevVRowsL zRowsL hB s k]
  simp only [bRowsZ, prevVRowsZ, xRowsZ, zRowsZ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem qsumFast_lo_entry (i j : Fin 66) : qsumFastZ tauNum_lo tauDen_lo i j =
    (dotN 33 (A_loL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_loL.getD j.val [])) +
      (dotN 33 (B_loL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_loL.getD j.val [])) := by
  rw [qsumFastZ, Matrix.add_apply]
  simp only [crossZ]
  rw [cross_sum_entry (aRowsZ tauNum_lo tauDen_lo) weightedFZ A_loL weightedFL A_lo_entry (fun _ _ => rfl) i j,
    cross_sum_entry (bRowsZ tauNum_lo tauDen_lo) weightedGZ B_loL weightedGL B_lo_entry (fun _ _ => rfl) i j]

theorem endpoint_fast_lo : ∀ (i : Fin 66) (j : Fin 66), embeddedEntry 0 0 PloZ i j - embeddedEntry 2 2 PloZ i j - den_lo * dissZ i j + qFactor_lo * qsumFastZ tauNum_lo tauDen_lo i j = embeddedEntry 2 2 TloZ i j - embeddedEntry 2 0 TloZ i j - embeddedEntry 0 2 TloZ i j + embeddedEntry 0 0 TloZ i j := by
  intro i j
  rw [qsumFast_lo_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 2 then exact endpoint_lo_ok_0 i h0.1 h0.2 j
  else if h1 : 2 ≤ i.val ∧ i.val < 4 then exact endpoint_lo_ok_1 i h1.1 h1.2 j
  else if h2 : 4 ≤ i.val ∧ i.val < 6 then exact endpoint_lo_ok_2 i h2.1 h2.2 j
  else if h3 : 6 ≤ i.val ∧ i.val < 8 then exact endpoint_lo_ok_3 i h3.1 h3.2 j
  else if h4 : 8 ≤ i.val ∧ i.val < 10 then exact endpoint_lo_ok_4 i h4.1 h4.2 j
  else if h5 : 10 ≤ i.val ∧ i.val < 12 then exact endpoint_lo_ok_5 i h5.1 h5.2 j
  else if h6 : 12 ≤ i.val ∧ i.val < 14 then exact endpoint_lo_ok_6 i h6.1 h6.2 j
  else if h7 : 14 ≤ i.val ∧ i.val < 16 then exact endpoint_lo_ok_7 i h7.1 h7.2 j
  else if h8 : 16 ≤ i.val ∧ i.val < 18 then exact endpoint_lo_ok_8 i h8.1 h8.2 j
  else if h9 : 18 ≤ i.val ∧ i.val < 20 then exact endpoint_lo_ok_9 i h9.1 h9.2 j
  else if h10 : 20 ≤ i.val ∧ i.val < 22 then exact endpoint_lo_ok_10 i h10.1 h10.2 j
  else if h11 : 22 ≤ i.val ∧ i.val < 24 then exact endpoint_lo_ok_11 i h11.1 h11.2 j
  else if h12 : 24 ≤ i.val ∧ i.val < 26 then exact endpoint_lo_ok_12 i h12.1 h12.2 j
  else if h13 : 26 ≤ i.val ∧ i.val < 28 then exact endpoint_lo_ok_13 i h13.1 h13.2 j
  else if h14 : 28 ≤ i.val ∧ i.val < 30 then exact endpoint_lo_ok_14 i h14.1 h14.2 j
  else if h15 : 30 ≤ i.val ∧ i.val < 32 then exact endpoint_lo_ok_15 i h15.1 h15.2 j
  else if h16 : 32 ≤ i.val ∧ i.val < 34 then exact endpoint_lo_ok_16 i h16.1 h16.2 j
  else if h17 : 34 ≤ i.val ∧ i.val < 36 then exact endpoint_lo_ok_17 i h17.1 h17.2 j
  else if h18 : 36 ≤ i.val ∧ i.val < 38 then exact endpoint_lo_ok_18 i h18.1 h18.2 j
  else if h19 : 38 ≤ i.val ∧ i.val < 40 then exact endpoint_lo_ok_19 i h19.1 h19.2 j
  else if h20 : 40 ≤ i.val ∧ i.val < 42 then exact endpoint_lo_ok_20 i h20.1 h20.2 j
  else if h21 : 42 ≤ i.val ∧ i.val < 44 then exact endpoint_lo_ok_21 i h21.1 h21.2 j
  else if h22 : 44 ≤ i.val ∧ i.val < 46 then exact endpoint_lo_ok_22 i h22.1 h22.2 j
  else if h23 : 46 ≤ i.val ∧ i.val < 48 then exact endpoint_lo_ok_23 i h23.1 h23.2 j
  else if h24 : 48 ≤ i.val ∧ i.val < 50 then exact endpoint_lo_ok_24 i h24.1 h24.2 j
  else if h25 : 50 ≤ i.val ∧ i.val < 52 then exact endpoint_lo_ok_25 i h25.1 h25.2 j
  else if h26 : 52 ≤ i.val ∧ i.val < 54 then exact endpoint_lo_ok_26 i h26.1 h26.2 j
  else if h27 : 54 ≤ i.val ∧ i.val < 56 then exact endpoint_lo_ok_27 i h27.1 h27.2 j
  else if h28 : 56 ≤ i.val ∧ i.val < 58 then exact endpoint_lo_ok_28 i h28.1 h28.2 j
  else if h29 : 58 ≤ i.val ∧ i.val < 60 then exact endpoint_lo_ok_29 i h29.1 h29.2 j
  else if h30 : 60 ≤ i.val ∧ i.val < 62 then exact endpoint_lo_ok_30 i h30.1 h30.2 j
  else if h31 : 62 ≤ i.val ∧ i.val < 64 then exact endpoint_lo_ok_31 i h31.1 h31.2 j
  else if h32 : 64 ≤ i.val ∧ i.val < 66 then exact endpoint_lo_ok_32 i h32.1 h32.2 j
  else omega

theorem A_hi_entry : ∀ (s : Fin 33) (k : Fin 66), aRowsZ tauNum_hi tauDen_hi s k = (A_hiL.getD k.val []).getD s.val 0 := by
  intro s k
  have hA : ∀ k : Fin 66, A_hiL.getD k.val [] = lin3N tauDen_hi (-tauNum_hi) (-tauDen_hi) 33 (prevZRowsL.getD k.val []) (prevVRowsL.getD k.val []) (xRowsL.getD k.val []) :=
    fun k => A_hi_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_hi (-tauNum_hi) (-tauDen_hi) A_hiL prevZRowsL prevVRowsL xRowsL hA s k]
  simp only [aRowsZ, prevZRowsZ, prevVRowsZ, xRowsZ, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem B_hi_entry : ∀ (s : Fin 33) (k : Fin 66), bRowsZ tauNum_hi tauDen_hi s k = (B_hiL.getD k.val []).getD s.val 0 := by
  intro s k
  have hB : ∀ k : Fin 66, B_hiL.getD k.val [] = lin3N tauDen_hi tauNum_hi (-tauDen_hi) 33 (xRowsL.getD k.val []) (prevVRowsL.getD k.val []) (zRowsL.getD k.val []) :=
    fun k => B_hi_ok_0 k (Nat.zero_le _) k.isLt
  rw [← colMat_lin3 tauDen_hi tauNum_hi (-tauDen_hi) B_hiL xRowsL prevVRowsL zRowsL hB s k]
  simp only [bRowsZ, prevVRowsZ, xRowsZ, zRowsZ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem qsumFast_hi_entry (i j : Fin 66) : qsumFastZ tauNum_hi tauDen_hi i j =
    (dotN 33 (A_hiL.getD i.val []) (weightedFL.getD j.val []) + dotN 33 (weightedFL.getD i.val []) (A_hiL.getD j.val [])) +
      (dotN 33 (B_hiL.getD i.val []) (weightedGL.getD j.val []) + dotN 33 (weightedGL.getD i.val []) (B_hiL.getD j.val [])) := by
  rw [qsumFastZ, Matrix.add_apply]
  simp only [crossZ]
  rw [cross_sum_entry (aRowsZ tauNum_hi tauDen_hi) weightedFZ A_hiL weightedFL A_hi_entry (fun _ _ => rfl) i j,
    cross_sum_entry (bRowsZ tauNum_hi tauDen_hi) weightedGZ B_hiL weightedGL B_hi_entry (fun _ _ => rfl) i j]

theorem endpoint_fast_hi : ∀ (i : Fin 66) (j : Fin 66), embeddedEntry 0 0 PhiZ i j - embeddedEntry 2 2 PhiZ i j - den_hi * dissZ i j + qFactor_hi * qsumFastZ tauNum_hi tauDen_hi i j = embeddedEntry 2 2 ThiZ i j - embeddedEntry 2 0 ThiZ i j - embeddedEntry 0 2 ThiZ i j + embeddedEntry 0 0 ThiZ i j := by
  intro i j
  rw [qsumFast_hi_entry]
  have hlt := i.isLt
  if h0 : 0 ≤ i.val ∧ i.val < 2 then exact endpoint_hi_ok_0 i h0.1 h0.2 j
  else if h1 : 2 ≤ i.val ∧ i.val < 4 then exact endpoint_hi_ok_1 i h1.1 h1.2 j
  else if h2 : 4 ≤ i.val ∧ i.val < 6 then exact endpoint_hi_ok_2 i h2.1 h2.2 j
  else if h3 : 6 ≤ i.val ∧ i.val < 8 then exact endpoint_hi_ok_3 i h3.1 h3.2 j
  else if h4 : 8 ≤ i.val ∧ i.val < 10 then exact endpoint_hi_ok_4 i h4.1 h4.2 j
  else if h5 : 10 ≤ i.val ∧ i.val < 12 then exact endpoint_hi_ok_5 i h5.1 h5.2 j
  else if h6 : 12 ≤ i.val ∧ i.val < 14 then exact endpoint_hi_ok_6 i h6.1 h6.2 j
  else if h7 : 14 ≤ i.val ∧ i.val < 16 then exact endpoint_hi_ok_7 i h7.1 h7.2 j
  else if h8 : 16 ≤ i.val ∧ i.val < 18 then exact endpoint_hi_ok_8 i h8.1 h8.2 j
  else if h9 : 18 ≤ i.val ∧ i.val < 20 then exact endpoint_hi_ok_9 i h9.1 h9.2 j
  else if h10 : 20 ≤ i.val ∧ i.val < 22 then exact endpoint_hi_ok_10 i h10.1 h10.2 j
  else if h11 : 22 ≤ i.val ∧ i.val < 24 then exact endpoint_hi_ok_11 i h11.1 h11.2 j
  else if h12 : 24 ≤ i.val ∧ i.val < 26 then exact endpoint_hi_ok_12 i h12.1 h12.2 j
  else if h13 : 26 ≤ i.val ∧ i.val < 28 then exact endpoint_hi_ok_13 i h13.1 h13.2 j
  else if h14 : 28 ≤ i.val ∧ i.val < 30 then exact endpoint_hi_ok_14 i h14.1 h14.2 j
  else if h15 : 30 ≤ i.val ∧ i.val < 32 then exact endpoint_hi_ok_15 i h15.1 h15.2 j
  else if h16 : 32 ≤ i.val ∧ i.val < 34 then exact endpoint_hi_ok_16 i h16.1 h16.2 j
  else if h17 : 34 ≤ i.val ∧ i.val < 36 then exact endpoint_hi_ok_17 i h17.1 h17.2 j
  else if h18 : 36 ≤ i.val ∧ i.val < 38 then exact endpoint_hi_ok_18 i h18.1 h18.2 j
  else if h19 : 38 ≤ i.val ∧ i.val < 40 then exact endpoint_hi_ok_19 i h19.1 h19.2 j
  else if h20 : 40 ≤ i.val ∧ i.val < 42 then exact endpoint_hi_ok_20 i h20.1 h20.2 j
  else if h21 : 42 ≤ i.val ∧ i.val < 44 then exact endpoint_hi_ok_21 i h21.1 h21.2 j
  else if h22 : 44 ≤ i.val ∧ i.val < 46 then exact endpoint_hi_ok_22 i h22.1 h22.2 j
  else if h23 : 46 ≤ i.val ∧ i.val < 48 then exact endpoint_hi_ok_23 i h23.1 h23.2 j
  else if h24 : 48 ≤ i.val ∧ i.val < 50 then exact endpoint_hi_ok_24 i h24.1 h24.2 j
  else if h25 : 50 ≤ i.val ∧ i.val < 52 then exact endpoint_hi_ok_25 i h25.1 h25.2 j
  else if h26 : 52 ≤ i.val ∧ i.val < 54 then exact endpoint_hi_ok_26 i h26.1 h26.2 j
  else if h27 : 54 ≤ i.val ∧ i.val < 56 then exact endpoint_hi_ok_27 i h27.1 h27.2 j
  else if h28 : 56 ≤ i.val ∧ i.val < 58 then exact endpoint_hi_ok_28 i h28.1 h28.2 j
  else if h29 : 58 ≤ i.val ∧ i.val < 60 then exact endpoint_hi_ok_29 i h29.1 h29.2 j
  else if h30 : 60 ≤ i.val ∧ i.val < 62 then exact endpoint_hi_ok_30 i h30.1 h30.2 j
  else if h31 : 62 ≤ i.val ∧ i.val < 64 then exact endpoint_hi_ok_31 i h31.1 h31.2 j
  else if h32 : 64 ≤ i.val ∧ i.val < 66 then exact endpoint_hi_ok_32 i h32.1 h32.2 j
  else omega

theorem crossZ_eq_integerCross (u v : Fin 66 → ℤ) :
    crossZ u v = ADMMNearSharpCertificate.integerCross u v := rfl

theorem qsumZ_fast_eq (a b : ℤ) : qsumZ a b = qsumFastZ a b := by
  unfold qsumZ qsumFastZ
  simp only [crossZ_eq_integerCross]
  rw [weighted_cross_sum, weighted_cross_sum, weightedF_exact, weightedG_exact]

private theorem S0Z_standard : S0Z = ADMMNearSharp.StandardRows.S0Z 31 := rfl

private theorem S1Z_standard : S1Z = ADMMNearSharp.StandardRows.S1Z 31 := rfl

theorem endpoint_identity_lo : ∀ i j : Fin 66,
    (S0Z.transpose * PloZ * S0Z - S1Z.transpose * PloZ * S1Z -
       den_lo • dissZ + qFactor_lo • qsumZ tauNum_lo tauDen_lo) i j =
    (diffRowsZ.transpose * TloZ * diffRowsZ) i j := by
  intro i j
  rw [qsumZ_fast_eq]
  simp only [diffRowsZ, S0Z_standard, S1Z_standard, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    S0_congruence_apply (d := 31), S1_congruence_apply (d := 31),
    difference_congruence_apply (d := 31)]
  exact endpoint_fast_lo i j

theorem endpoint_identity_hi : ∀ i j : Fin 66,
    (S0Z.transpose * PhiZ * S0Z - S1Z.transpose * PhiZ * S1Z -
       den_hi • dissZ + qFactor_hi • qsumZ tauNum_hi tauDen_hi) i j =
    (diffRowsZ.transpose * ThiZ * diffRowsZ) i j := by
  intro i j
  rw [qsumZ_fast_eq]
  simp only [diffRowsZ, S0Z_standard, S1Z_standard, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    S0_congruence_apply (d := 31), S1_congruence_apply (d := 31),
    difference_congruence_apply (d := 31)]
  exact endpoint_fast_hi i j

#print axioms endpoint_identity_lo
#print axioms endpoint_identity_hi
#print axioms lower_lo_gram_identity
#print axioms lower_hi_residual_dd

end ADMMNearSharpCertificate.Data1886795
