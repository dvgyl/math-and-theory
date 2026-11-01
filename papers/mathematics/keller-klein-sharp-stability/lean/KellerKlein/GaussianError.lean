import KellerKlein.GaussianBaseline
import KellerKlein.GaussianTarget
import KellerKlein.ZoneAConstants

noncomputable section

open Set MeasureTheory

namespace KellerKlein

set_option maxHeartbeats 800000

lemma gaussian_inverse_le_power {a : ℝ} (ha : 0 < a) :
    gaussian (1/a) ≤ 46080*a^12 := by
  have hv : 0 < 1/(2*a^2) := by positivity
  have h : (1 / (2 * a ^ 2)) ^ 6 / 720 ≤ Real.exp (1 / (2 * a ^ 2)) := by
    convert Real.pow_div_factorial_le_exp (1 / (2 * a ^ 2)) hv.le 6 using 1 <;> norm_num
  have hp : 0 < (1/(2*a^2))^6/720 := by positivity
  have hi := one_div_le_one_div_of_le hp h
  have he : -(1/a)^2/2 = -(1/(2*a^2)) := by field_simp [ha.ne']; ring
  rw [gaussian, he, Real.exp_neg]
  have hpow : 1/((1/(2*a^2))^6/720) = 46080*a^12 := by
    field_simp [ha.ne']
    ring
  rw [hpow] at hi
  simpa only [one_div] using hi

lemma gaussian_remainder_budget {a : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100) :
    a^4/(15*Real.pi)+9*gaussian (1/a) ≤ a^4/40 := by
  have h8 := pow_le_pow_left₀ ha.le haMax 8
  have hnum : (9*46080 : ℝ)*(7/100)^8 ≤ 1/1000 := by norm_num
  have hcoeff : (9*46080 : ℝ)*a^8 ≤ 1/1000 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcoeff (pow_nonneg ha.le 4)
  have he : a^4*((9*46080 : ℝ)*a^8) = 9*46080*a^12 := by ring
  rw [he] at hmul
  have hg := gaussian_inverse_le_power ha
  have htail : 9*gaussian (1/a) ≤ a^4/1000 := by nlinarith only [hmul, hg]
  have hpi : (1 : ℝ)/(15*Real.pi) ≤ 1/45 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 15*Real.pi)).2
    linarith [Real.pi_gt_three]
  have hp := mul_le_mul_of_nonneg_left hpi (pow_nonneg ha.le 4)
  have hp' : a ^ 4 / (15 * Real.pi) ≤ a ^ 4 / 45 := by
    convert hp using 1 <;> ring
  nlinarith only [htail, hp', pow_nonneg ha.le 4]

lemma c_lower_third {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1/2) : a/3 ≤ c a := by
  have haSq : a^2 ≤ 1/4 := by nlinarith
  have ha3 : a^3 ≤ a/4 := by
    have h := mul_le_mul_of_nonneg_left haSq ha
    nlinarith only [h]
  have hn : 0 ≤ a-a^3/6 := by nlinarith
  calc
    a/3 ≤ (39/100 : ℝ)*(a-a^3/6) := by nlinarith
    _ ≤ phi0*(a-a^3/6) := mul_le_mul_of_nonneg_right ZoneA.phi0_lower hn
    _ ≤ c a := c_lower_cubic ha

lemma exp_neg_inverse_le_third {a : ℝ} (ha : 0 < a) (ha12 : a ≤ 1/12) :
    Real.exp (-(1/(2*a))) ≤ a/3 := by
  have hv : 0 < 1/(2*a) := by positivity
  have h : (1 / (2 * a)) ^ 3 / 6 ≤ Real.exp (1 / (2 * a)) := by
    convert Real.pow_div_factorial_le_exp (1 / (2 * a)) hv.le 3 using 1 <;> norm_num
  have hp : 0 < (1/(2*a))^3/6 := by positivity
  have hi := one_div_le_one_div_of_le hp h
  have hpow : 1/((1/(2*a))^3/6) = 48*a^3 := by
    field_simp [ha.ne']
    ring
  rw [hpow] at hi
  rw [Real.exp_neg]
  have he : (Real.exp (1/(2*a)))⁻¹ ≤ 48*a^3 := by simpa only [one_div] using hi
  have haSq : a^2 ≤ 1/144 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left haSq ha.le
  nlinarith only [he, hm]

lemma integral_phi_half : (∫ s in Ioi (0 : ℝ), phi s) = 1/2 := by
  unfold phi
  rw [integral_mul_const]
  have h0 : (∫ s in Ioi (0 : ℝ), gaussian s) = Real.pi*phi0 := by
    simpa only [halfMoment, pow_zero, one_mul] using halfMoment_zero
  rw [h0]
  nlinarith [two_pi_phi0_sq]

lemma c_add_tail {x : ℝ} (hx : 0 ≤ x) :
    c x+phi0*gaussianTailMoment 0 x = 1/2 := by
  have h := integral_Ioo_add_Ioi_of_nonneg hx integrable_phi.integrableOn
  have hc : (∫ s in Ioo (0 : ℝ) x, phi s) = c x := by
    rw [c, intervalIntegral.integral_of_le hx, integral_Ioc_eq_integral_Ioo]
  have ht : (∫ s in Ioi x, phi s) = phi0*gaussianTailMoment 0 x := by
    simp only [phi, gaussianTailMoment, pow_zero, one_mul, integral_mul_const]
    ring
  rw [hc, ht, integral_phi_half] at h
  exact h

lemma gaussian_mills {x : ℝ} (hx : 0 < x) : 1/2-c x ≤ phi x/x := by
  have hmass := c_add_tail hx.le
  have ht := mul_le_mul_of_nonneg_left (gaussianTailMoment_zero_le hx) phi0_pos.le
  calc
    1 / 2 - c x = phi0 * gaussianTailMoment 0 x := by linarith only [hmass]
    _ ≤ phi0 * (gaussian x / x) := ht
    _ = phi x / x := by unfold phi; ring

lemma one_le_H_add_H_of_large {a x : ℝ} (ha : 0 < a) (haMax : a ≤ 7/100)
    (hx : 0 ≤ x) (hax : 1 ≤ a*x^2) : 1 ≤ H x+H a := by
  have hx1 : 1 ≤ x := by
    by_contra h
    have hxl : x < 1 := lt_of_not_ge h
    have hxSq : x^2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hxSq ha.le
    nlinarith
  have hxpos : 0 < x := by linarith
  have hcomp : 1/a ≤ x^2 := by
    apply (div_le_iff₀ ha).2
    nlinarith only [hax]
  have hg : gaussian x ≤ Real.exp (-(1/(2*a))) := by
    unfold gaussian
    apply Real.exp_le_exp.mpr
    have he : -(1/(2*a)) = -(1/a)/2 := by ring
    rw [he]
    nlinarith only [hcomp]
  have hφ : phi x/x ≤ gaussian x := by
    apply (div_le_iff₀ hxpos).2
    have hp : phi0 ≤ x := ZoneA.phi0_upper.trans (by linarith)
    have hm := mul_le_mul_of_nonneg_left hp (gaussian_nonneg x)
    simpa only [phi, mul_comm] using hm
  have he := exp_neg_inverse_le_third ha (by linarith : a ≤ 1/12)
  have hc := c_lower_third ha.le (by linarith : a ≤ 1/2)
  have hm := gaussian_mills hxpos
  dsimp [H]
  linarith

end KellerKlein
