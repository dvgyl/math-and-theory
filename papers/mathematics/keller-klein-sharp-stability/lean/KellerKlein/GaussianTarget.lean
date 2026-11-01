import KellerKlein.GaussianMoments

noncomputable section
open Set MeasureTheory

namespace KellerKlein

lemma phi_lower_quadratic (t : ℝ) : phi0 * (1 - t ^ 2 / 2) ≤ phi t := by
  have h := Real.add_one_le_exp (-(t ^ 2) / 2)
  have hm := mul_le_mul_of_nonneg_right h phi0_pos.le
  unfold phi gaussian
  nlinarith only [hm]

lemma c_lower_cubic {a : ℝ} (ha : 0 ≤ a) :
    phi0 * (a - a ^ 3 / 6) ≤ c a := by
  have hp : Continuous (fun t : ℝ => phi0 * (1 - t ^ 2 / 2)) := by fun_prop
  have hi : (∫ t in (0 : ℝ)..a, phi0 * (1 - t ^ 2 / 2)) =
      phi0 * (a - a ^ 3 / 6) := by
    have hder : ∀ t ∈ uIcc (0 : ℝ) a,
        HasDerivAt (fun t : ℝ => phi0 * (t - t ^ 3 / 6))
          (phi0 * (1 - t ^ 2 / 2)) t := by
      intro t ht
      convert ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).const_mul
        phi0 using 1 <;> (try simp only [id_eq]) <;> ring
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hp.intervalIntegrable 0 a)
  rw [← hi]
  exact intervalIntegral.integral_mono_on ha (hp.intervalIntegrable 0 a)
    (continuous_phi.intervalIntegrable 0 a) (fun t ht => phi_lower_quadratic t)

lemma c_pair_lower {a ξ : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ) :
    phi0 * a * (1 + ξ) - phi0 * a ^ 3 * (1 + ξ ^ 3) / 6 ≤ c a + c (ξ * a) := by
  have h1 := c_lower_cubic ha
  have h2 := c_lower_cubic (mul_nonneg hξ ha)
  nlinarith only [h1, h2]

end KellerKlein
