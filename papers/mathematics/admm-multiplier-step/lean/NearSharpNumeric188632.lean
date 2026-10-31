import NearSharpPSD188632
import IntegerGap

open scoped BigOperators

namespace ADMMNearSharpCertificate.C188632

open ADMMBarrier
open ADMMNearSharpCertificate.Data188632

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def S0 : Matrix (Fin 40) (Fin 42) ℝ := castMat S0Z
noncomputable def S1 : Matrix (Fin 40) (Fin 42) ℝ := castMat S1Z
noncomputable def diffRows : Matrix (Fin 40) (Fin 42) ℝ := castMat diffRowsZ
noncomputable def diss : Matrix (Fin 42) (Fin 42) ℝ := castMat dissZ
noncomputable def xRows : Matrix (Fin 21) (Fin 42) ℝ := castMat xRowsZ
noncomputable def zRows : Matrix (Fin 21) (Fin 42) ℝ := castMat zRowsZ
noncomputable def prevZRows : Matrix (Fin 21) (Fin 42) ℝ := castMat prevZRowsZ
noncomputable def prevVRows : Matrix (Fin 21) (Fin 42) ℝ := castMat prevVRowsZ
noncomputable def aRows (τ : ℝ) : Matrix (Fin 21) (Fin 42) ℝ :=
  prevZRows - τ • prevVRows - xRows
noncomputable def bRows (τ : ℝ) : Matrix (Fin 21) (Fin 42) ℝ :=
  xRows + τ • prevVRows - zRows
noncomputable def lambdaF : Matrix (Fin 21) (Fin 21) ℝ :=
  fun i j => (lambdaFZ i j : ℝ) / lambdaDen
noncomputable def lambdaG : Matrix (Fin 21) (Fin 21) ℝ :=
  fun i j => (lambdaGZ i j : ℝ) / lambdaDen
noncomputable def qsum (τ : ℝ) : Matrix (Fin 42) (Fin 42) ℝ :=
  ADMMNearSharp.qsum xRows (aRows τ) lambdaF +
  ADMMNearSharp.qsum zRows (bRows τ) lambdaG
noncomputable def embed0 (P : Matrix (Fin 40) (Fin 40) ℝ) : Matrix (Fin 42) (Fin 42) ℝ :=
  S0.transpose * P * S0
noncomputable def embed1 (P : Matrix (Fin 40) (Fin 40) ℝ) : Matrix (Fin 42) (Fin 42) ℝ :=
  S1.transpose * P * S1

theorem lambdaF_nonneg (i j : Fin 21) : 0 ≤ lambdaF i j := by
  apply div_nonneg
  · exact_mod_cast lambdaFZ_nonneg i j
  · norm_num [lambdaDen]

theorem lambdaG_nonneg (i j : Fin 21) : 0 ≤ lambdaG i j := by
  apply div_nonneg
  · exact_mod_cast lambdaGZ_nonneg i j
  · norm_num [lambdaDen]

theorem lambdaF_flow (i : Fin 21) : (∑ j, lambdaF i j) = ∑ j, lambdaF j i := by
  simp only [lambdaF, ← Finset.sum_div]
  congr 1
  exact_mod_cast lambdaFZ_flow i

theorem lambdaG_flow (i : Fin 21) : (∑ j, lambdaG i j) = ∑ j, lambdaG j i := by
  simp only [lambdaG, ← Finset.sum_div]
  congr 1
  exact_mod_cast lambdaGZ_flow i

private theorem cast_qsumZ (a b : ℤ) (τ : ℝ) (ha : (a : ℝ) = (b : ℝ) * τ) :
    castMat (qsumZ a b) = (-2 * (b : ℝ) * (lambdaDen : ℝ)) • qsum τ := by
  have hLF : castMat lambdaFZ = (lambdaDen : ℝ) • lambdaF := by
    ext i j
    change (lambdaFZ i j : ℝ) = (lambdaDen : ℝ) *
      ((lambdaFZ i j : ℝ) / (lambdaDen : ℝ))
    norm_num [lambdaDen] <;> ring
  have hLG : castMat lambdaGZ = (lambdaDen : ℝ) • lambdaG := by
    ext i j
    change (lambdaGZ i j : ℝ) = (lambdaDen : ℝ) *
      ((lambdaGZ i j : ℝ) / (lambdaDen : ℝ))
    norm_num [lambdaDen] <;> ring
  have hA : castMat (aRowsZ a b) = (b : ℝ) • aRows τ := by
    simp only [aRowsZ, castMat_sub, castMat_smul]
    change (b : ℝ) • prevZRows - (a : ℝ) • prevVRows - (b : ℝ) • xRows =
      (b : ℝ) • (prevZRows - τ • prevVRows - xRows)
    rw [ha]
    module
  have hB : castMat (bRowsZ a b) = (b : ℝ) • bRows τ := by
    simp only [bRowsZ, castMat_sub, castMat_add, castMat_smul]
    change (b : ℝ) • xRows + (a : ℝ) • prevVRows - (b : ℝ) • zRows =
      (b : ℝ) • (xRows + τ • prevVRows - zRows)
    rw [ha]
    module
  simp only [qsumZ, castMat_add, crossZ_eq_integerCross]
  rw [cast_weighted_cross, cast_weighted_cross, hA, hB, hLF, hLG]
  simp only [ADMMNearSharp.qsum_smul_normals]
  rw [qsum_smul_weights (castMat xRowsZ) (aRows τ) lambdaF (lambdaDen : ℝ),
    qsum_smul_weights (castMat zRowsZ) (bRows τ) lambdaG (lambdaDen : ℝ)]
  change (-2 : ℝ) • ((b : ℝ) • ((lambdaDen : ℝ) •
      ADMMNearSharp.qsum xRows (aRows τ) lambdaF)) +
    (-2 : ℝ) • ((b : ℝ) • ((lambdaDen : ℝ) •
      ADMMNearSharp.qsum zRows (bRows τ) lambdaG)) =
    (-2 * (b : ℝ) * (lambdaDen : ℝ)) •
      (ADMMNearSharp.qsum xRows (aRows τ) lambdaF +
       ADMMNearSharp.qsum zRows (bRows τ) lambdaG)
  module

theorem identity_lo :
    embed0 Plo - embed1 Plo - diss - qsum (47157/25000 : ℝ) =
      diffRows.transpose * Tlo * diffRows := by
  have hZ : S0Z.transpose * PloZ * S0Z - S1Z.transpose * PloZ * S1Z -
      den_lo • dissZ + qFactor_lo • qsumZ tauNum_lo tauDen_lo =
      diffRowsZ.transpose * TloZ * diffRowsZ := by
    ext i j
    exact endpoint_identity_lo i j
  have h := congrArg castMat hZ
  simp only [castMat_add, castMat_sub, castMat_mul, castMat_transpose, castMat_smul] at h
  rw [cast_qsumZ tauNum_lo tauDen_lo (47157/25000) (by norm_num [tauNum_lo, tauDen_lo])] at h
  have hs := congrArg (fun M : Matrix (Fin 42) (Fin 42) ℝ => (den_lo : ℝ)⁻¹ • M) h
  norm_num [embed0, embed1, Plo, Tlo, S0, S1, diffRows, diss,
    smul_add, smul_sub, smul_smul, Matrix.mul_smul, Matrix.smul_mul,
    den_lo, qFactor_lo, tauDen_lo, lambdaDen] at hs ⊢
  exact hs

theorem identity_hi :
    embed0 Phi - embed1 Phi - diss - qsum (23579/12500 : ℝ) =
      diffRows.transpose * Thi * diffRows := by
  have hZ : S0Z.transpose * PhiZ * S0Z - S1Z.transpose * PhiZ * S1Z -
      den_hi • dissZ + qFactor_hi • qsumZ tauNum_hi tauDen_hi =
      diffRowsZ.transpose * ThiZ * diffRowsZ := by
    ext i j
    exact endpoint_identity_hi i j
  have h := congrArg castMat hZ
  simp only [castMat_add, castMat_sub, castMat_mul, castMat_transpose, castMat_smul] at h
  rw [cast_qsumZ tauNum_hi tauDen_hi (23579/12500) (by norm_num [tauNum_hi, tauDen_hi])] at h
  have hs := congrArg (fun M : Matrix (Fin 42) (Fin 42) ℝ => (den_hi : ℝ)⁻¹ • M) h
  norm_num [embed0, embed1, Phi, Thi, S0, S1, diffRows, diss,
    smul_add, smul_sub, smul_smul, Matrix.mul_smul, Matrix.smul_mul,
    den_hi, qFactor_hi, tauDen_hi, lambdaDen] at hs ⊢
  exact hs

#print axioms identity_lo
#print axioms identity_hi

end ADMMNearSharpCertificate.C188632
