import KellerKlein.KernelDefs
import KellerKlein.Envelopes
import KellerKlein.KernelRegularity
import KellerKlein.EnvelopeRegularity

noncomputable section

open Set MeasureTheory

namespace KellerKlein

/-- The upper Prawitz envelope for the closed concentration event.  This uses
the plus-sine kernel, so it corresponds to the conventional `J(-x;a,pi/a)`. -/
def upperEnvelopeIntegrand (a x u : ℝ) : ℝ :=
  max (upperKernel (x/a) u * lowerEnvelope a crossoverRoot (Real.pi*u/a))
    (upperKernel (x/a) u * upperEnvelope a crossoverRoot (Real.pi*u/a))

def JUpper (a x : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, upperEnvelopeIntegrand a x u

lemma upperEnvelopeIntegrand_measurable (a x : ℝ) :
    Measurable (upperEnvelopeIntegrand a x) := by
  have ht : Measurable (fun u : ℝ => Real.pi*u/a) :=
    (measurable_const.mul measurable_id).div_const a
  exact ((measurable_upperKernel (x/a)).mul
    ((lowerEnvelope_measurable a crossoverRoot).comp ht)).max
      ((measurable_upperKernel (x/a)).mul
        ((upperEnvelope_measurable a crossoverRoot).comp ht))

lemma abs_upperEnvelopeIntegrand_le {a x u : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hu : 0 < u) (hu1 : u < 1) :
    |upperEnvelopeIntegrand a x u| ≤ 1+|x/a| := by
  have hK := abs_upperKernel_uniform (ξ := x/a) hu hu1
  have ht : 0 ≤ Real.pi*u/a := by positivity
  have hL := abs_lowerEnvelope_le_one (θ := crossoverRoot) ha ha1 ht
  have hU := abs_upperEnvelope_le_one a crossoverRoot (Real.pi*u/a)
  have hp : |upperKernel (x/a) u * lowerEnvelope a crossoverRoot (Real.pi*u/a)| ≤
      1+|x/a| := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hL).trans hK
  have hq : |upperKernel (x/a) u * upperEnvelope a crossoverRoot (Real.pi*u/a)| ≤
      1+|x/a| := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hU).trans hK
  rw [abs_le]
  constructor
  · exact (abs_le.mp hp).1.trans (le_max_left _ _)
  · exact max_le (abs_le.mp hp).2 (abs_le.mp hq).2

lemma intervalIntegrable_upperEnvelopeIntegrand {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (upperEnvelopeIntegrand a x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
  have hconst : IntegrableOn (fun _ : ℝ => 1+|x/a|) (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).1
      (continuous_const.intervalIntegrable 0 1)
  apply hconst.mono' (upperEnvelopeIntegrand_measurable a x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  simpa only [Real.norm_eq_abs] using abs_upperEnvelopeIntegrand_le ha ha1 hu.1 hu.2

end KellerKlein
