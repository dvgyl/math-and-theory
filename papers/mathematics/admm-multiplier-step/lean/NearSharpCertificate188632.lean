import NearSharpNumeric188632
import AffineMatrix
import MatrixCertificate

namespace ADMMNearSharpCertificate.C188632

open ADMMBarrier
open ADMMNearSharpCertificate.Data188632
open scoped BigOperators

set_option maxHeartbeats 0

noncomputable def weight (τ : ℝ) : ℝ := (τ-(47157/25000))/((23579/12500)-(47157/25000))
noncomputable def P (τ : ℝ) : Matrix (Fin 40) (Fin 40) ℝ :=
  (1-weight τ) • Plo + weight τ • Phi
noncomputable def T (τ : ℝ) : Matrix (Fin 40) (Fin 40) ℝ :=
  (1-weight τ) • Tlo + weight τ • Thi

theorem weight_nonneg (τ : ℝ) (hlo : (47157/25000 : ℝ) ≤ τ) : 0 ≤ weight τ := by
  unfold weight
  apply div_nonneg
  · linarith
  · norm_num

theorem weight_le_one (τ : ℝ) (hhi : τ ≤ (23579/12500 : ℝ)) : weight τ ≤ 1 := by
  unfold weight
  apply (div_le_one (by norm_num : (0 : ℝ) < (23579/12500)-(47157/25000))).2
  linarith

theorem weight_param (τ : ℝ) : (1-weight τ)*(47157/25000)+weight τ*(23579/12500) = τ := by
  unfold weight
  ring

theorem P_lower_psd (τ : ℝ) (hlo : (47157/25000 : ℝ) ≤ τ) (hhi : τ ≤ (23579/12500 : ℝ)) :
    (P τ-coerc).PosSemidef :=
  affine_psd lower_lo_psd lower_hi_psd (weight_nonneg τ hlo) (weight_le_one τ hhi)

theorem T_psd (τ : ℝ) (hlo : (47157/25000 : ℝ) ≤ τ) (hhi : τ ≤ (23579/12500 : ℝ)) :
    (T τ).PosSemidef := by
  exact (psd_smul Tlo_psd (by have := weight_le_one τ hhi; linarith)).add
    (psd_smul Thi_psd (weight_nonneg τ hlo))

theorem identity (τ : ℝ) : embed0 (P τ)-embed1 (P τ)-diss-qsum τ =
    diffRows.transpose * T τ * diffRows := by
  have h := affine_identity S0 S1 diffRows diss xRows zRows prevZRows prevVRows
    lambdaF lambdaG Plo Phi Tlo Thi (47157/25000) (23579/12500) (weight τ) identity_lo identity_hi
  rw [weight_param] at h
  exact h

theorem S0_standard : S0 = ADMMNearSharp.StandardRows.S0 19 := by
  change castMat S0Z = castMat (ADMMNearSharp.StandardRows.S0Z 19)
  have hZ : S0Z = ADMMNearSharp.StandardRows.S0Z 19 := rfl
  exact congrArg castMat hZ

theorem S1_standard : S1 = ADMMNearSharp.StandardRows.S1 19 := by
  change castMat S1Z = castMat (ADMMNearSharp.StandardRows.S1Z 19)
  have hZ : S1Z = ADMMNearSharp.StandardRows.S1Z 19 := rfl
  exact congrArg castMat hZ

theorem coerc_standard : coerc = ADMMNearSharp.StandardRows.coerc 19 := by
  change castMat coercZ = castMat (ADMMNearSharp.StandardRows.coercZ 19)
  have hZ : coercZ = ADMMNearSharp.StandardRows.coercZ 19 := rfl
  exact congrArg castMat hZ

theorem diss_standard : diss = ADMMNearSharp.StandardRows.diss 19 := by
  change castMat dissZ = castMat (ADMMNearSharp.StandardRows.dissZ 19)
  have hZ : dissZ = ADMMNearSharp.StandardRows.dissZ 19 := rfl
  exact congrArg castMat hZ

theorem xRows_standard : xRows = ADMMNearSharp.StandardRows.xRows 19 := by
  change castMat xRowsZ = castMat (ADMMNearSharp.StandardRows.xRowsZ 19)
  have hZ : xRowsZ = ADMMNearSharp.StandardRows.xRowsZ 19 := by
    ext i j
    exact (by decide +kernel : ∀ (i : Fin 21) (j : Fin 42),
      xRowsZ i j = ADMMNearSharp.StandardRows.xRowsZ 19 i j) i j
  exact congrArg castMat hZ

theorem zRows_standard : zRows = ADMMNearSharp.StandardRows.zRows 19 := by
  change castMat zRowsZ = castMat (ADMMNearSharp.StandardRows.zRowsZ 19)
  have hZ : zRowsZ = ADMMNearSharp.StandardRows.zRowsZ 19 := by
    ext i j
    exact (by decide +kernel : ∀ (i : Fin 21) (j : Fin 42),
      zRowsZ i j = ADMMNearSharp.StandardRows.zRowsZ 19 i j) i j
  exact congrArg castMat hZ

theorem prevZRows_standard : prevZRows = ADMMNearSharp.StandardRows.prevZRows 19 := by
  change castMat prevZRowsZ = castMat (ADMMNearSharp.StandardRows.prevZRowsZ 19)
  have hZ : prevZRowsZ = ADMMNearSharp.StandardRows.prevZRowsZ 19 := by
    ext i j
    exact (by decide +kernel : ∀ (i : Fin 21) (j : Fin 42),
      prevZRowsZ i j = ADMMNearSharp.StandardRows.prevZRowsZ 19 i j) i j
  exact congrArg castMat hZ

theorem prevVRows_standard : prevVRows = ADMMNearSharp.StandardRows.prevVRows 19 := by
  change castMat prevVRowsZ = castMat (ADMMNearSharp.StandardRows.prevVRowsZ 19)
  have hZ : prevVRowsZ = ADMMNearSharp.StandardRows.prevVRowsZ 19 := by
    ext i j
    exact (by decide +kernel : ∀ (i : Fin 21) (j : Fin 42),
      prevVRowsZ i j = ADMMNearSharp.StandardRows.prevVRowsZ 19 i j) i j
  exact congrArg castMat hZ

theorem aRows_standard (τ : ℝ) : aRows τ = ADMMNearSharp.StandardRows.aRows 19 τ := by
  simp only [aRows, ADMMNearSharp.StandardRows.aRows,
    prevZRows_standard, prevVRows_standard, xRows_standard]

theorem bRows_standard (τ : ℝ) : bRows τ = ADMMNearSharp.StandardRows.bRows 19 τ := by
  simp only [bRows, ADMMNearSharp.StandardRows.bRows,
    prevVRows_standard, xRows_standard, zRows_standard]

/-- A fully instantiated, unconditional finite-history ADMM certificate. -/
noncomputable def certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ : ℝ) (hlo : (47157/25000 : ℝ) ≤ τ) (hhi : τ ≤ (23579/12500 : ℝ)) :
    ADMMNearSharp.MemoryCertificate 19 τ E :=
  ADMMNearSharp.certificateOfMatrices 19 τ (P τ) (T τ) diffRows lambdaF lambdaG
    (by simpa only [← coerc_standard] using P_lower_psd τ hlo hhi)
    (T_psd τ hlo hhi) lambdaF_nonneg lambdaG_nonneg lambdaF_flow lambdaG_flow
    (by simpa only [embed0, embed1, qsum, S0_standard, S1_standard, diss_standard,
      xRows_standard, zRows_standard, aRows_standard, bRows_standard] using identity τ)

#print axioms certificate

end ADMMNearSharpCertificate.C188632
