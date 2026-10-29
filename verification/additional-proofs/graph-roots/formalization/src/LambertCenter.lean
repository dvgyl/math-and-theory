import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Lambert

def center (L : ℝ) : ℂ := ((L - Real.log L : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I

theorem center_div {L : ℝ} (hL : L ≠ 0) :
    center L / (L : ℂ) = 1 - ((Real.log L / L : ℝ) : ℂ) +
      ((Real.pi / L : ℝ) : ℂ) * Complex.I := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  push_cast
  dsimp [center]
  push_cast
  field_simp [hL']

theorem center_re_tendsto_atTop (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => (center (L n)).re) atTop atTop := by
  have hr : Tendsto (fun n => Real.log (L n) / L n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hL
  have hh : Tendsto (fun n => L n / 2) atTop atTop := hL.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hh
  filter_upwards [hL.eventually_gt_atTop 0, hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn hratio
  have hlog : Real.log (L n) ≤ L n / 2 := by
    have h := (div_lt_iff₀ hn).mp hratio
    linarith
  simp only [center, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  linarith

theorem center_ratio_tendsto_one (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => center (L n) / (L n : ℂ)) atTop (𝓝 1) := by
  have hr : Tendsto (fun n => Real.log (L n) / L n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hL
  have hi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hL
  have hp : Tendsto (fun n => Real.pi / L n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hi : Tendsto (fun n => Real.pi * (L n)⁻¹) atTop (𝓝 (Real.pi * 0)))
  have hlim : Tendsto (fun n => (1 : ℂ) - ((Real.log (L n) / L n : ℝ) : ℂ) +
      ((Real.pi / L n : ℝ) : ℂ) * Complex.I) atTop (𝓝 1) := by
    simpa only [Complex.ofReal_zero, sub_zero, zero_mul, add_zero] using
      ((tendsto_const_nhds.sub hr.ofReal).add (hp.ofReal.mul_const Complex.I))
  apply hlim.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with n hn
  exact (center_div hn.ne').symm

theorem log_center_defect_tendsto_zero (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => Complex.log (center (L n)) - (Real.log (L n) : ℂ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Complex.log (center (L n) / (L n : ℂ))) atTop (𝓝 0) := by
    simpa only [Complex.log_one] using (center_ratio_tendsto_one L hL).clog Complex.one_mem_slitPlane
  apply hlog.congr'
  filter_upwards [hL.eventually_gt_atTop 0, (center_re_tendsto_atTop L hL).eventually_gt_atTop 0] with n hl hc
  have hl0 : (L n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hc0 : center (L n) ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hc
    exact (lt_irrefl 0) hc
  have hdiv0 : center (L n) / (L n : ℂ) ≠ 0 := div_ne_zero hc0 hl0
  have hmul : (L n : ℂ) * (center (L n) / (L n : ℂ)) = center (L n) := by field_simp
  have hscale := Complex.log_ofReal_mul hl hdiv0
  rw [hmul] at hscale
  linear_combination -hscale

#print axioms center_re_tendsto_atTop
#print axioms center_ratio_tendsto_one
#print axioms log_center_defect_tendsto_zero
end Lambert
end SquareFlowerCompletion
