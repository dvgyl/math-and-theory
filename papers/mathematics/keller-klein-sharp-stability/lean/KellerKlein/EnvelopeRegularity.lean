import KellerKlein.Envelopes

open Set MeasureTheory

namespace KellerKlein

lemma lowerEnvelope_measurable (a θ : ℝ) : Measurable (lowerEnvelope a θ) := by
  have hpow : 0 ≤ (1 / a ^ 2 : ℝ) := one_div_nonneg.mpr (sq_nonneg a)
  have hc : Continuous (fun t : ℝ => Real.cos (a * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hp : Continuous (fun t : ℝ => Real.cos (a * t) ^ (1 / a ^ 2 : ℝ)) :=
    (Real.continuous_rpow_const hpow).comp hc
  have hpabs : Continuous (fun t : ℝ => |Real.cos (a * t)| ^ (1 / a ^ 2 : ℝ)) :=
    (Real.continuous_rpow_const hpow).comp hc.abs
  have harg : Continuous (fun t : ℝ => -(1 - a ^ 2) * t ^ 2 / 2) :=
    (continuous_const.mul (continuous_id.pow 2)).div_const 2
  have hm : Continuous (fun t : ℝ =>
      -(|Real.cos (a * t)| * Real.exp (-(1 - a ^ 2) * t ^ 2 / 2))) :=
    (hc.abs.mul (Real.continuous_exp.comp harg)).neg
  have hset (b : ℝ) : MeasurableSet {t : ℝ | a * t ≤ b} :=
    measurableSet_le (measurable_const.mul measurable_id) measurable_const
  unfold lowerEnvelope
  exact hp.measurable.ite (hset (Real.pi / 2))
    (hm.measurable.ite (hset θ) (hpabs.neg.measurable.ite (hset Real.pi) measurable_const))

lemma upperEnvelope_measurable (a θ : ℝ) : Measurable (upperEnvelope a θ) := by
  have hpow : 0 ≤ (1 / a ^ 2 : ℝ) := one_div_nonneg.mpr (sq_nonneg a)
  have hpabs : Continuous (fun t : ℝ => |Real.cos (a * t)| ^ (1 / a ^ 2 : ℝ)) :=
    (Real.continuous_rpow_const hpow).comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs
  have he : Continuous (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg.div_const 2)
  have hset (b : ℝ) : MeasurableSet {t : ℝ | a * t ≤ b} :=
    measurableSet_le (measurable_const.mul measurable_id) measurable_const
  unfold upperEnvelope
  exact he.measurable.ite (hset θ) (hpabs.measurable.ite (hset Real.pi) measurable_const)

lemma upperEnvelope_nonneg (a θ t : ℝ) : 0 ≤ upperEnvelope a θ t := by
  unfold upperEnvelope
  split_ifs
  · exact (Real.exp_pos _).le
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · norm_num

lemma abs_upperEnvelope_le_one (a θ t : ℝ) : |upperEnvelope a θ t| ≤ 1 := by
  rw [abs_of_nonneg (upperEnvelope_nonneg a θ t)]
  unfold upperEnvelope
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg t]
  · exact Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _) (by positivity)
  · rfl

lemma abs_lowerEnvelope_le_one {a θ t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    |lowerEnvelope a θ t| ≤ 1 := by
  unfold lowerEnvelope
  split_ifs with hhalf hθ hπ
  · have hcos : 0 ≤ Real.cos (a * t) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [mul_nonneg ha.le ht, Real.pi_pos], hhalf⟩
    rw [abs_of_nonneg (Real.rpow_nonneg hcos _)]
    exact Real.rpow_le_one hcos (Real.cos_le_one _) (by positivity)
  · rw [abs_neg, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(1 - a ^ 2) * t ^ 2 / 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have ha2 : a ^ 2 ≤ 1 := by nlinarith
      have hh := mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg t)
      nlinarith
    exact mul_le_one₀ (Real.abs_cos_le_one _) (Real.exp_pos _).le he
  · rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _) (by positivity)
  · norm_num

end KellerKlein
