import KellerKlein.KernelBounds

noncomputable section

namespace KellerKlein

lemma cotangent_remainder_bound {y : ℝ} (hy : 0 < y) (hyp : y ≤ Real.pi / 2) :
    1 - y * (Real.cos y / Real.sin y) ≤ y ^ 2 / 3 + y ^ 4 / 32 := by
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy
    (by linarith [Real.pi_pos])
  have h := cotangent_lower_product hy.le hyp
  have hd : 1 - y ^ 2 / 3 - y ^ 4 / 32 ≤ y * Real.cos y / Real.sin y :=
    (le_div_iff₀ hs).2 h
  rw [mul_div_assoc] at hd
  linarith

lemma cotangent_remainder_lower {y : ℝ} (hy : 0 < y) (hyp : y ≤ Real.pi / 2) :
    -(y ^ 3 / 32) ≤ Real.cos y / Real.sin y - 1 / y + y / 3 := by
  have hd := cotangent_remainder_bound hy hyp
  apply (mul_le_mul_right hy).mp
  have he : (Real.cos y / Real.sin y - 1 / y + y / 3) * y =
      y * (Real.cos y / Real.sin y) - 1 + y ^ 2 / 3 := by
    field_simp [hy.ne']
    ring
  rw [he]
  nlinarith

lemma cotangent_remainder_nonpos {y : ℝ} (hy : 0 < y) (hyp : y < Real.pi) :
    Real.cos y / Real.sin y - 1 / y + y / 3 ≤ 0 := by
  linarith [cot_le_inv_sub_third hy hyp]

end KellerKlein
