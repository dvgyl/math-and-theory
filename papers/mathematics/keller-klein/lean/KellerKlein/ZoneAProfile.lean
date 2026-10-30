import KellerKlein.ZoneAKernel
import KellerKlein.GaussianMoments

noncomputable section

namespace KellerKlein.ZoneA

lemma exp_neg_le_quadratic {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (-v) ≤ 1 - v + v ^ 2 / 2 := by
  have h : 0 ≤ 1 - v + v ^ 2 / 2 - Real.exp (-v) := by
    apply nonneg_of_derivative_nonneg hv
      (f' := fun y => -1 + y + Real.exp (-y))
    · simp
    · intro y hy
      convert (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
        ((hasDerivAt_pow 2 y).div_const 2)).sub
        ((hasDerivAt_id y).neg.exp) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      have h := Real.add_one_le_exp (-y)
      linarith
  linarith

lemma cosine_profile_le_quartic {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s)
    (hbs : b * s ≤ Real.pi / 2) :
    |Real.cos (b * s)| ^ (1 / b ^ 2 : ℝ) ≤
      Real.exp (-(s ^ 2 / 2) - b ^ 2 * s ^ 4 / 12) := by
  have hb2 : 0 < b ^ 2 := pow_pos hb 2
  have hphase : 0 ≤ b * s := mul_nonneg hb.le hs
  rcases hbs.eq_or_lt with heq | hlt
  · rw [heq, Real.cos_pi_div_two, abs_zero, Real.zero_rpow (by positivity)]
    exact (Real.exp_pos _).le
  · have hc : 0 < Real.cos (b * s) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hlt⟩
    rw [abs_of_pos hc, Real.rpow_def_of_pos hc]
    apply Real.exp_le_exp.mpr
    have h := neg_log_cos_lower_quartic hphase hlt
    have hm := mul_le_mul_of_nonneg_right
      (by linarith : Real.log (Real.cos (b * s)) ≤ -((b * s) ^ 2 / 2 + (b * s) ^ 4 / 12))
      (show 0 ≤ 1 / b ^ 2 by positivity)
    have he : -((b * s) ^ 2 / 2 + (b * s) ^ 4 / 12) * (1 / b ^ 2) =
        -(s ^ 2 / 2) - b ^ 2 * s ^ 4 / 12 := by
      field_simp [hb.ne']
      ring
    rwa [he] at hm

def primaryPolynomial (a b ξ s : ℝ) : ℝ :=
  upperPoly ξ (a * s) - (b ^ 2 * s ^ 4 / 12) * lowerPoly ξ (a * s) +
    (b ^ 4 * s ^ 8 / 288) * (1 + ξ)

lemma primary_profile_bound {a b ξ s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) (hs : 0 < s)
    (has : a * s < Real.pi) (hbs : b * s ≤ Real.pi / 2) :
    upperKernel ξ (a * s / Real.pi) * |Real.cos (b * s)| ^ (1 / b ^ 2 : ℝ) ≤
      gaussian s * primaryPolynomial a b ξ s := by
  let u := a * s / Real.pi
  let v := b ^ 2 * s ^ 4 / 12
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := (div_lt_one Real.pi_pos).2 has
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hk0 := upperKernel_nonneg hξ hξ1 hu hu1
  have hk1 := upperKernel_le_one_add hξ hξ1 hu hu1
  have hkU := upperKernel_le_upperPoly hξ hξ1 hu hu1
  have hkL := lowerPoly_le_upperKernel hξ hξ1 hu hu1
  have hy : Real.pi * u = a * s := by dsimp [u]; field_simp
  rw [hy] at hkU hkL
  have hp := cosine_profile_le_quartic hb hs.le hbs
  have he : Real.exp (-(s ^ 2 / 2) - b ^ 2 * s ^ 4 / 12) =
      gaussian s * Real.exp (-v) := by
    rw [sub_eq_add_neg, Real.exp_add]
    unfold gaussian v
    congr 2 <;> ring
  rw [he] at hp
  have hfirst := mul_le_mul_of_nonneg_left hp hk0
  have hsecond := mul_le_mul_of_nonneg_left (exp_neg_le_quadratic hv)
    (mul_nonneg hk0 (gaussian_nonneg s))
  have hL := mul_le_mul_of_nonneg_left hkL hv
  have hU := mul_le_mul_of_nonneg_left hk1 (sq_nonneg v)
  have hpoly : upperKernel ξ u * (1 - v + v ^ 2 / 2) ≤
      upperPoly ξ (a * s) - v * lowerPoly ξ (a * s) +
        v ^ 2 / 2 * (1 + ξ) := by
    nlinarith only [hkU, hL, hU]
  have hthird := mul_le_mul_of_nonneg_left hpoly (gaussian_nonneg s)
  have hepoly : upperPoly ξ (a * s) - v * lowerPoly ξ (a * s) +
      v ^ 2 / 2 * (1 + ξ) = primaryPolynomial a b ξ s := by
    unfold primaryPolynomial v
    ring
  rw [hepoly] at hthird
  change upperKernel ξ u * |Real.cos (b * s)| ^ (1 / b ^ 2 : ℝ) ≤ _
  nlinarith only [hfirst, hsecond, hthird]

end KellerKlein.ZoneA
