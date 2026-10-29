import SharpRadius

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion.Extremal
open Lambert

/-- The leading equivalent stated after the additive escape law. -/
theorem radius_leading_equivalent :
    Tendsto (fun n : ℕ => radius n / (2 * Real.sqrt ((n:ℝ)/Real.log (n:ℝ)))) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLratio : Tendsto (fun n : ℕ => logScale n / Real.log (n:ℝ)) atTop (𝓝 1) := by
    have hc : Tendsto (fun n : ℕ => Real.log 4 / Real.log (n:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have h := hc.add_const 1
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hln : Real.log (n:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn : (1:ℝ)<n)).ne'
    dsimp [logScale]
    rw [Real.log_mul (by norm_num) hnpos.ne', add_div, div_self hln]
  have hlogL : Tendsto (fun n : ℕ => Real.log (logScale n) / logScale n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp logScale_tendsto_atTop
  have hsmall : Tendsto (fun n : ℕ => Real.log (logScale n) / Real.log (n:ℝ)) atTop (𝓝 0) := by
    have h := hlogL.mul hLratio
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [logScale_tendsto_atTop.eventually_gt_atTop 0] with n hn
    field_simp
  have herr := radius_reciprocal_square_asymptotic.div_atTop hlog
  have hratio : Tendsto (fun n : ℕ => (4*(n:ℝ)/(radius n)^2) / Real.log (n:ℝ)) atTop (𝓝 1) := by
    have h := (herr.add hLratio).sub hsmall
    simp only [zero_add, sub_zero] at h
    apply h.congr
    intro n
    dsimp [logScale]
    ring
  have hs : Tendsto (fun n : ℕ => Real.sqrt (((4*(n:ℝ)/(radius n)^2) / Real.log (n:ℝ))⁻¹)) atTop (𝓝 1) := by
    simpa only [inv_one, Real.sqrt_one] using (hratio.inv₀ (by norm_num)).sqrt
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : 0 < n := by omega
  have hnreal : (0:ℝ) < n := by exact_mod_cast hnpos
  have hR : radius n ≠ 0 := (radius_pos hnpos).ne'
  have hln : Real.log (n:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn : (1:ℝ)<n)).ne'
  have heq : ((4*(n:ℝ)/(radius n)^2) / Real.log (n:ℝ))⁻¹ =
      (radius n)^2 / (4*((n:ℝ)/Real.log (n:ℝ))) := by
    field_simp
  rw [heq, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (radius_nonneg n),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num

#print axioms radius_leading_equivalent
end SquareFlowerCompletion.Extremal
