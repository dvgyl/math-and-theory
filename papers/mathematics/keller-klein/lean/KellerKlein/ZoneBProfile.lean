import KellerKlein.Elementary
import KellerKlein.GaussianMoments

noncomputable section

open Set

namespace KellerKlein

set_option maxHeartbeats 800000

lemma tan_upper_quintic_unit {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.tan y ≤ y + y^3/3 + 3*y^5/10 := by
  have hyp : y < Real.pi/2 := by linarith [Real.pi_gt_three]
  have hc : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hyp⟩
  have hy2 : y^2 ≤ 1 := by nlinarith
  have hy6 : y^6 ≤ 1 := by
    have h3 : (y^2)^3 ≤ (1 : ℝ)^3 := pow_le_pow_left₀ (sq_nonneg y) hy2 3
    nlinarith only [h3]
  have hp : 0 ≤ (1 : ℝ)/6 - 11*y^2/80 + 13*y^4/1080 - y^6/2400 := by
    nlinarith [sq_nonneg (y^2)]
  have hpos : 0 ≤ y+y^3/3+3*y^5/10 := by positivity
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_sextic hy) hpos
  have hsin := sin_upper_quintic hy
  have hid : (y+y^3/3+3*y^5/10)*(1-y^2/2+y^4/24-y^6/720) -
      (y-y^3/6+y^5/120) =
      y^5*((1 : ℝ)/6-11*y^2/80+13*y^4/1080-y^6/2400) := by ring
  have hnon := mul_nonneg (pow_nonneg hy 5) hp
  rw [← hid] at hnon
  rw [Real.tan_eq_sin_div_cos]
  apply (div_le_iff₀ hc).2
  linarith

lemma neg_log_cos_upper_unit {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    -Real.log (Real.cos y) ≤ y^2/2+y^4/12+y^6/20 := by
  have h : 0 ≤ y^2/2+y^4/12+y^6/20+Real.log (Real.cos y) := by
    apply nonneg_of_derivative_nonneg hy
      (f' := fun z => z+z^3/3+3*z^5/10-Real.tan z)
    · simp
    · intro z hz
      have hc : 0 < Real.cos z := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hz.1], by linarith [Real.pi_gt_three, hz.2]⟩
      have hdlog : HasDerivAt (fun w => Real.log (Real.cos w)) (-Real.tan z) z := by
        convert (Real.hasDerivAt_cos z).log hc.ne' using 1
        rw [Real.tan_eq_sin_div_cos]
        ring
      convert ((((hasDerivAt_pow 2 z).div_const 2).add
        ((hasDerivAt_pow 4 z).div_const 12)).add
        ((hasDerivAt_pow 6 z).div_const 20)).add hdlog using 1 <;>
        (try simp only [id_eq]) <;> ring
    · intro z hz
      linarith [tan_upper_quintic_unit hz.1 (hz.2.trans hy1)]
  linarith

def gaussianProfileLoss (a s : ℝ) : ℝ := a^2*s^4/12+a^4*s^6/20

lemma cosine_profile_loss_bound {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (has : a*s ≤ 1) :
    gaussian s - (Real.cos (a*s)) ^ (1/a^2 : ℝ) ≤
      gaussian s * gaussianProfileLoss a s := by
  have hy : 0 ≤ a*s := mul_nonneg ha.le hs
  have hyp : a*s < Real.pi/2 := by linarith [Real.pi_gt_three]
  have hc : 0 < Real.cos (a*s) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hyp⟩
  have hl := neg_log_cos_upper_unit hy has
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hscaled := (div_le_div_iff_of_pos_right ha2).2 hl
  have hid : ((a*s)^2/2+(a*s)^4/12+(a*s)^6/20)/a^2 =
      s^2/2+gaussianProfileLoss a s := by
    dsimp [gaussianProfileLoss]
    field_simp [ha.ne']
    ring
  rw [hid] at hscaled
  rw [neg_div] at hscaled
  have he := Real.add_one_le_exp (Real.log (Real.cos (a*s))/a^2+s^2/2)
  have hm := mul_le_mul_of_nonneg_left he (gaussian_nonneg s)
  have hexp : gaussian s * Real.exp (Real.log (Real.cos (a*s))/a^2+s^2/2) =
      (Real.cos (a*s)) ^ (1/a^2 : ℝ) := by
    rw [gaussian, ← Real.exp_add, Real.rpow_def_of_pos hc]
    congr 1
    ring
  rw [hexp] at hm
  have hscaled' : -gaussianProfileLoss a s ≤
      Real.log (Real.cos (a*s))/a^2+s^2/2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hscaled' (gaussian_nonneg s)
  nlinarith only [hm, hmul]

lemma cosine_profile_le_gaussian {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (has : a*s < Real.pi/2) :
    (Real.cos (a*s)) ^ (1/a^2 : ℝ) ≤ gaussian s := by
  have hy : 0 ≤ a*s := mul_nonneg ha.le hs
  have hc : 0 < Real.cos (a*s) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], has⟩
  rw [Real.rpow_def_of_pos hc, gaussian]
  apply Real.exp_le_exp.mpr
  have h := log_cos_le_neg_sq_half hy has
  have hd := (div_le_div_iff_of_pos_right (sq_pos_of_pos ha)).2 h
  have he : -((a*s)^2/2)/a^2 = -s^2/2 := by field_simp [ha.ne']; ring
  rw [he] at hd
  simpa only [div_eq_mul_inv, mul_one, one_mul] using hd

end KellerKlein
