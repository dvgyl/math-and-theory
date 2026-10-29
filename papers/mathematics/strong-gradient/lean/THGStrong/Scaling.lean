import THGStrong.Core

noncomputable section
open scoped InnerProductSpace

namespace THGStrong
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma scale_interpolation_identity (μ s f e : ℝ) (x y g k : E) (hμ : μ ≠ 1) :
    Q (s*μ) x y (s • g) (s • k) (s*f) (s*e) =
      (s*(1-s*μ)/(1-μ)) * Q μ x y g k f e +
      (s*(1-s)/(1-μ)) * sq ((g-k)-μ • (x-y)) := by
  have hn : 1-μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  simp only [Q, sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm x g, real_inner_comm x k,
    real_inner_comm y g, real_inner_comm y k]
  field_simp [hn]
  ring

lemma scale_interpolation_nonneg (μ s f e : ℝ) (x y g k : E)
    (hμ : μ < 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hQ : 0 ≤ Q μ x y g k f e) :
    0 ≤ Q (s*μ) x y (s • g) (s • k) (s*f) (s*e) := by
  rw [scale_interpolation_identity μ s f e x y g k (ne_of_lt hμ)]
  have hd : 0 ≤ 1-μ := sub_nonneg.mpr (le_of_lt hμ)
  have hsm : s*μ ≤ 1 := by
    by_cases hm : 0 ≤ μ
    · have hh := mul_le_mul_of_nonneg_right hs1 hm
      nlinarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_ge hm)
      linarith
  exact add_nonneg
    (mul_nonneg (div_nonneg (mul_nonneg hs (sub_nonneg.mpr hsm)) hd) hQ)
    (mul_nonneg (div_nonneg (mul_nonneg hs (sub_nonneg.mpr hs1)) hd) (sq_nonneg _))

#print axioms scale_interpolation_identity
#print axioms scale_interpolation_nonneg
end THGStrong
