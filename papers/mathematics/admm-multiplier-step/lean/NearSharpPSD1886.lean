import NearSharpData1886
import IntegerMatrix

open scoped BigOperators

namespace ADMMNearSharpCertificate.C1886

open ADMMBarrier
open ADMMNearSharpCertificate.Data1886

noncomputable def Plo : Matrix (Fin 40) (Fin 40) ℝ :=
  (den_lo : ℝ)⁻¹ • castMat PloZ
noncomputable def Phi : Matrix (Fin 40) (Fin 40) ℝ :=
  (den_hi : ℝ)⁻¹ • castMat PhiZ
noncomputable def Tlo : Matrix (Fin 40) (Fin 40) ℝ :=
  (den_lo : ℝ)⁻¹ • castMat TloZ
noncomputable def Thi : Matrix (Fin 40) (Fin 40) ℝ :=
  (den_hi : ℝ)⁻¹ • castMat ThiZ
noncomputable def coerc : Matrix (Fin 40) (Fin 40) ℝ := castMat coercZ

theorem lower_lo_psd : (Plo - coerc).PosSemidef := by
  have h := psd_of_integer_gram_dd lower_loZ lower_lo_EZ lower_lo_RZ den_lo lower_lo_Rden
    (by norm_num [den_lo]) (by norm_num [lower_lo_Rden])
    (by ext i j; exact lower_lo_gram_identity i j)
    lower_lo_residual_symmetric lower_lo_residual_dd
  have he : (den_lo : ℝ)⁻¹ • castMat lower_loZ = Plo - coerc := by
    simp only [lower_loZ, castMat_sub, castMat_smul, smul_sub, smul_smul]
    norm_num [den_lo, Plo, coerc]
  simpa only [← he, castMat] using h

theorem lower_hi_psd : (Phi - coerc).PosSemidef := by
  have h := psd_of_integer_gram_dd lower_hiZ lower_hi_EZ lower_hi_RZ den_hi lower_hi_Rden
    (by norm_num [den_hi]) (by norm_num [lower_hi_Rden])
    (by ext i j; exact lower_hi_gram_identity i j)
    lower_hi_residual_symmetric lower_hi_residual_dd
  have he : (den_hi : ℝ)⁻¹ • castMat lower_hiZ = Phi - coerc := by
    simp only [lower_hiZ, castMat_sub, castMat_smul, smul_sub, smul_smul]
    norm_num [den_hi, Phi, coerc]
  simpa only [← he, castMat] using h

theorem Tlo_psd : Tlo.PosSemidef := by
  exact psd_of_integer_gram_dd TloZ Tlo_EZ Tlo_RZ den_lo Tlo_Rden
    (by norm_num [den_lo]) (by norm_num [Tlo_Rden])
    (by ext i j; exact Tlo_gram_identity i j)
    Tlo_residual_symmetric Tlo_residual_dd

theorem Thi_psd : Thi.PosSemidef := by
  exact psd_of_integer_gram_dd ThiZ Thi_EZ Thi_RZ den_hi Thi_Rden
    (by norm_num [den_hi]) (by norm_num [Thi_Rden])
    (by ext i j; exact Thi_gram_identity i j)
    Thi_residual_symmetric Thi_residual_dd

#print axioms lower_lo_psd
#print axioms lower_hi_psd
#print axioms Tlo_psd
#print axioms Thi_psd

end ADMMNearSharpCertificate.C1886
