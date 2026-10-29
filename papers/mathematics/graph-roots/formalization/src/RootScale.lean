import GraphReturn

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

theorem norm_minus_re_eq {z : ℂ} (hz : 0 < z.re) :
    ‖z‖ - z.re = z.im ^ 2 / (‖z‖ + z.re) := by
  have hd : ‖z‖ + z.re ≠ 0 := by linarith [norm_nonneg z]
  have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  apply (eq_div_iff hd).2
  nlinarith

theorem lam_modulus_defect (L : ℕ → ℝ) (lam : ℕ → ℂ)
    (hL : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => lam n - center (L n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖lam n‖ - (L n - Real.log (L n))) atTop (𝓝 0) := by
  have hre := lam_re_tendsto_atTop L lam hL hd
  have himerr : Tendsto (fun n => (lam n - center (L n)).im) atTop (𝓝 0) := by
    simpa only [Complex.zero_im] using (Complex.continuous_im.tendsto (0 : ℂ)).comp hd
  have him : Tendsto (fun n => (lam n).im) atTop (𝓝 Real.pi) := by
    have h : Tendsto (fun n => (lam n - center (L n)).im + Real.pi) atTop (𝓝 Real.pi) := by
      simpa only [zero_add] using himerr.add_const Real.pi
    apply h.congr
    intro n
    simp [center]
  have hden : Tendsto (fun n => ‖lam n‖ + (lam n).re) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [norm_nonneg (lam n)]) hre
  have hquot : Tendsto (fun n => (lam n).im ^ 2 / (‖lam n‖ + (lam n).re)) atTop (𝓝 0) :=
    (him.pow 2).div_atTop hden
  have hnormre : Tendsto (fun n => ‖lam n‖ - (lam n).re) atTop (𝓝 0) := by
    apply hquot.congr'
    filter_upwards [hre.eventually_gt_atTop 0] with n hn
    exact (norm_minus_re_eq hn).symm
  have hreerr : Tendsto (fun n => (lam n).re - (L n - Real.log (L n))) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp hd
    change Tendsto (fun n => (lam n - center (L n)).re) atTop (𝓝 (0 : ℝ)) at h
    simpa [center] using h
  have hsum : Tendsto (fun n => (‖lam n‖ - (lam n).re) +
      ((lam n).re - (L n - Real.log (L n)))) atTop (𝓝 0) := by
    simpa only [zero_add] using hnormre.add hreerr
  apply hsum.congr
  intro n
  ring

theorem reciprocal_radius_identity {n : ℕ} (hn : 0 < n) {lam v : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) (hv : lam + v ≠ 0) :
    (4 * (n : ℝ)) / ‖(reciprocalCoordinate lam v)⁻¹‖ ^ 2 =
      ‖lam‖ * ‖1 + v / lam‖ ^ 2 := by
  have hw := coordinate_ne_zero (lam_ne_zero hn he) hv
  have hwreal : ‖reciprocalCoordinate lam v‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    (4 * (n : ℝ)) / ‖(reciprocalCoordinate lam v)⁻¹‖ ^ 2 =
        (4 * (n : ℝ)) * ‖reciprocalCoordinate lam v‖ ^ 2 := by
      rw [norm_inv]
      field_simp [hwreal]
    _ = (4 * (n : ℝ)) * (‖initialCoordinate lam‖ ^ 2 * ‖1 + v / lam‖ ^ 2) := by
      rw [reciprocalCoordinate, norm_mul, mul_pow]
    _ = _ := by
      rw [initialCoordinate_norm_square hn he]
      field_simp [hnreal]

theorem factor_modulus_defect (lam v : ℕ → ℂ)
    (hnorm : Tendsto (fun n => ‖lam n‖) atTop atTop)
    (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => ‖lam n‖ * ‖1 + v n / lam n‖ ^ 2 - ‖lam n‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (lam n)⁻¹) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_inv] using tendsto_inv_atTop_zero.comp hnorm
  have hdiv : Tendsto (fun n => v n / lam n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hv.mul hi
  have hnf : Tendsto (fun n => ‖(1 : ℂ) + v n / lam n‖) atTop (𝓝 1) := by
    simpa only [add_zero, norm_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).add hdiv).norm
  have hratio : Tendsto (fun n => ‖lam n + v n‖ / ‖lam n‖) atTop (𝓝 1) := by
    apply hnf.congr'
    filter_upwards [hnorm.eventually_gt_atTop 0] with n hn
    have hl : lam n ≠ 0 := norm_pos_iff.mp hn
    rw [← norm_div, add_div, div_self hl]
  have hdiff : Tendsto (fun n => ‖lam n + v n‖ - ‖lam n‖) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (by simpa only [norm_zero] using hv.norm)
    intro n
    simpa only [Real.norm_eq_abs, add_sub_cancel_left] using abs_norm_sub_norm_le (lam n + v n) (lam n)
  have hprod : Tendsto (fun n => (‖lam n + v n‖ - ‖lam n‖) *
      (‖lam n + v n‖ / ‖lam n‖ + 1)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hdiff.mul (hratio.add_const 1)
  apply hprod.congr'
  filter_upwards [hnorm.eventually_gt_atTop 0] with n hn
  have hl : lam n ≠ 0 := norm_pos_iff.mp hn
  have hn0 : ‖lam n‖ ≠ 0 := ne_of_gt hn
  have heq : ‖1 + v n / lam n‖ = ‖lam n + v n‖ / ‖lam n‖ := by
    rw [← norm_div, add_div, div_self hl]
  rw [heq]
  field_simp [hn0]
  ring

/-- Additive reciprocal-square precision of the actual constructed coordinate. -/
theorem reciprocal_scale_tendsto_zero (lam v : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ)))
    (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => 4 * (n : ℝ) / ‖(reciprocalCoordinate (lam n) (v n))⁻¹‖ ^ 2 -
      (logScale n - Real.log (logScale n))) atTop (𝓝 0) := by
  have hn := lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd
  have ha := factor_modulus_defect lam v hn hv
  have hb := lam_modulus_defect logScale lam logScale_tendsto_atTop hd
  have hs : Tendsto (fun n => (‖lam n‖ * ‖1 + v n / lam n‖ ^ 2 - ‖lam n‖) +
      (‖lam n‖ - (logScale n - Real.log (logScale n)))) atTop (𝓝 0) := by
    simpa only [zero_add] using ha.add hb
  apply hs.congr'
  have hvnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by simpa only [norm_zero] using hv.norm
  filter_upwards [he, eventually_ge_atTop 1, hn.eventually_gt_atTop 2,
    hvnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n he hn hlamNorm hnv
  have hv0 : lam n + v n ≠ 0 := by
    intro hz
    have h := norm_sub_norm_le (lam n) (-v n)
    rw [norm_neg, sub_neg_eq_add, hz, norm_zero] at h
    linarith
  rw [reciprocal_radius_identity (lt_of_lt_of_le Nat.zero_lt_one hn) he hv0]
  ring

#print axioms lam_modulus_defect
#print axioms factor_modulus_defect
#print axioms reciprocal_scale_tendsto_zero
end Transfer
end SquareFlowerCompletion
