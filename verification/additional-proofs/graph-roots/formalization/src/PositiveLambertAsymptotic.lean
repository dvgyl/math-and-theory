import PositiveLambert
import Mathlib.Tactic.FieldSimp

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion.Radius

theorem positiveLambert_tendsto_atTop : Tendsto positiveLambert atTop atTop := by
  have hl := Real.tendsto_log_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have he := positiveLambert_log_equation hs
  have hb := Real.log_le_self (positiveLambert_spec hs).1.le
  linarith

theorem log_div_positiveLambert_tendsto_one :
    Tendsto (fun s : ℝ => Real.log s / positiveLambert s) atTop (𝓝 1) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    positiveLambert_tendsto_atTop
  have ht : Tendsto (fun s : ℝ => 1 + Real.log (positiveLambert s) / positiveLambert s)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hw := (positiveLambert_spec hs).1.ne'
  have he := positiveLambert_log_equation hs
  rw [← he, add_div, div_self hw]

theorem positiveLambert_additive_asymptotic :
    Tendsto (fun s : ℝ => positiveLambert s -
      (Real.log s - Real.log (Real.log s))) atTop (𝓝 0) := by
  have ht : Tendsto (fun s : ℝ => Real.log (Real.log s / positiveLambert s))
      atTop (𝓝 0) := by
    simpa using log_div_positiveLambert_tendsto_one.log (by norm_num : (1 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have hp := positiveLambert_spec (by linarith : 0 < s)
  have he := positiveLambert_log_equation (by linarith : 0 < s)
  rw [Real.log_div (ne_of_gt (Real.log_pos hs)) hp.1.ne']
  linarith

#print axioms positiveLambert_tendsto_atTop
#print axioms log_div_positiveLambert_tendsto_one
#print axioms positiveLambert_additive_asymptotic
end SquareFlowerCompletion.Radius
