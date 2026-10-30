import KellerKlein.ZoneAProfile

noncomputable section

namespace KellerKlein.ZoneA

def aliasPolynomial (ξ t : ℝ) : ℝ :=
  t * Real.cos (Real.pi * ξ) + (Real.pi * ξ + Real.pi / 3) * t ^ 2 *
    Real.sin (Real.pi * ξ) + t ^ 4 * Real.sin (Real.pi * ξ)

lemma cosine_toward_origin_upper {β t : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ Real.pi / 2)
    (ht : 0 ≤ t) :
    Real.cos (β * (1 - t)) ≤ Real.cos β + β * t * Real.sin β := by
  have hc : 0 ≤ Real.cos β := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hβ1⟩
  have hs : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ
    (by linarith [Real.pi_pos])
  have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (β * t)) hc
  have h2 := mul_le_mul_of_nonneg_left (Real.sin_le (mul_nonneg hβ ht)) hs
  have he : β * (1 - t) = β - β * t := by ring
  rw [he, Real.cos_sub]
  nlinarith only [h1, h2]

lemma upperKernel_alias_bound {ξ t : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    upperKernel ξ (1 - t) ≤ aliasPolynomial ξ t := by
  have hβ : 0 ≤ Real.pi * ξ := mul_nonneg Real.pi_pos.le hξ
  have hβ1 : Real.pi * ξ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hz : 0 ≤ Real.pi * ξ * (1 - t) := mul_nonneg hβ (by linarith)
  have hzz : Real.pi * ξ * (1 - t) ≤ Real.pi * ξ := by nlinarith
  have hs : 0 ≤ Real.sin (Real.pi * ξ * (1 - t)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hz (by linarith [Real.pi_pos])
  have hsin : Real.sin (Real.pi * ξ * (1 - t)) ≤ Real.sin (Real.pi * ξ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hβ1 hzz
  have hr := rho_alias_bound ht ht1
  have hρ : 0 ≤ Real.pi * t ^ 2 / 3 + t ^ 4 := by positivity
  have hm := mul_le_mul hr hsin hs hρ
  have hcos := mul_le_mul_of_nonneg_left
    (cosine_toward_origin_upper hβ hβ1 ht.le) ht.le
  unfold upperKernel aliasPolynomial
  nlinarith only [hm, hcos]

lemma aliasPolynomial_nonneg {ξ t : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (ht : 0 ≤ t) : 0 ≤ aliasPolynomial ξ t := by
  have hβ : 0 ≤ Real.pi * ξ := mul_nonneg Real.pi_pos.le hξ
  have hβ1 : Real.pi * ξ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hc : 0 ≤ Real.cos (Real.pi * ξ) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hβ1⟩
  have hs : 0 ≤ Real.sin (Real.pi * ξ) := Real.sin_nonneg_of_nonneg_of_le_pi hβ
    (by linarith [Real.pi_pos])
  unfold aliasPolynomial
  positivity

lemma cosine_alias_profile_bound {b w : ℝ} (hb : 0 < b) (hw : 0 ≤ w)
    (hbw : b * w ≤ Real.pi / 2) :
    |Real.cos (Real.pi - b * w)| ^ (1 / b ^ 2 : ℝ) ≤ gaussian w := by
  rw [Real.cos_pi_sub, abs_neg]
  have h := cosine_profile_le_quartic hb hw hbw
  have he : Real.exp (-(w ^ 2 / 2) - b ^ 2 * w ^ 4 / 12) ≤ gaussian w := by
    unfold gaussian
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ b ^ 2 * w ^ 4 / 12 := by positivity
    linarith
  exact h.trans he

end KellerKlein.ZoneA
