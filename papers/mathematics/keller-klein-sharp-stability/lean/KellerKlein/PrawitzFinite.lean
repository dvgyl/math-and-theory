import KellerKlein.PrawitzMajorant
import KellerKlein.Rademacher
import KellerKlein.KernelDefs

open MeasureTheory Set
open Causalean.Stat.CLT.BerryEsseen

namespace KellerKlein

noncomputable section

def prawitzMajorantValue (z : ℝ) : ℝ :=
  (1 + prawitzSignApprox z + Real.sinc (z / 2) ^ 2) / 2

def symmetricPrawitzKernel (x T u : ℝ) : ℝ :=
  (1 - u) * Real.cos (u * (T * x)) +
    prawitzSineWeight u * Real.sin (u * (T * x))

lemma symmetricPrawitzKernel_intervalIntegrable (x T : ℝ) :
    IntervalIntegrable (symmetricPrawitzKernel x T) volume 0 1 := by
  have hc : Continuous (fun u : ℝ => (1 - u) * Real.cos (u * (T * x))) := by fun_prop
  exact (hc.intervalIntegrable 0 1).add (prawitz_sine_intervalIntegrable (T * x))

lemma symmetricPrawitzKernel_mul_cos_intervalIntegrable (x y T : ℝ) :
    IntervalIntegrable
      (fun u => symmetricPrawitzKernel x T u * Real.cos ((T * u) * y)) volume 0 1 := by
  apply (symmetricPrawitzKernel_intervalIntegrable x T).mul_continuousOn
  exact (show Continuous (fun u : ℝ => Real.cos ((T * u) * y)) by fun_prop).continuousOn

lemma prawitzMajorantPair_eq_integral (x y T : ℝ) :
    prawitzMajorantValue (T * (x - y)) + prawitzMajorantValue (T * (x + y)) - 1 =
      2 * ∫ u in (0 : ℝ)..1, symmetricPrawitzKernel x T u * Real.cos ((T * u) * y) := by
  have hsm := prawitz_sine_intervalIntegrable (T * (x - y))
  have hsp := prawitz_sine_intervalIntegrable (T * (x + y))
  have hcm : IntervalIntegrable
      (fun u : ℝ => (1 - u) * Real.cos (u * (T * (x - y)))) volume 0 1 := by
    exact (show Continuous (fun u : ℝ => (1 - u) * Real.cos (u * (T * (x - y))))
      by fun_prop).intervalIntegrable 0 1
  have hcp : IntervalIntegrable
      (fun u : ℝ => (1 - u) * Real.cos (u * (T * (x + y)))) volume 0 1 := by
    exact (show Continuous (fun u : ℝ => (1 - u) * Real.cos (u * (T * (x + y))))
      by fun_prop).intervalIntegrable 0 1
  calc
    _ = (∫ u in (0 : ℝ)..1, prawitzSineWeight u * Real.sin (u * (T * (x - y)))) +
        (∫ u in (0 : ℝ)..1, prawitzSineWeight u * Real.sin (u * (T * (x + y)))) +
        (∫ u in (0 : ℝ)..1, (1 - u) * Real.cos (u * (T * (x - y)))) +
        (∫ u in (0 : ℝ)..1, (1 - u) * Real.cos (u * (T * (x + y)))) := by
      simp only [prawitzMajorantValue, prawitz_triangle_raw, prawitzSignApprox]
      ring
    _ = ∫ u in (0 : ℝ)..1,
        ((prawitzSineWeight u * Real.sin (u * (T * (x - y))) +
          prawitzSineWeight u * Real.sin (u * (T * (x + y)))) +
          (1 - u) * Real.cos (u * (T * (x - y)))) +
          (1 - u) * Real.cos (u * (T * (x + y))) := by
      rw [intervalIntegral.integral_add ((hsm.add hsp).add hcm) hcp,
        intervalIntegral.integral_add (hsm.add hsp) hcm,
        intervalIntegral.integral_add hsm hsp]
    _ = 2 * ∫ u in (0 : ℝ)..1,
        symmetricPrawitzKernel x T u * Real.cos ((T * u) * y) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext u
      have hm : u * (T * (x - y)) = u * (T * x) - u * (T * y) := by ring
      have hp : u * (T * (x + y)) = u * (T * x) + u * (T * y) := by ring
      have hy : (T * u) * y = u * (T * y) := by ring
      rw [hm, hp, hy, Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add]
      unfold symmetricPrawitzKernel
      ring

lemma closed_interval_indicator_le_prawitz {x T : ℝ} (hx : 0 ≤ x) (hT : 0 < T)
    (y : ℝ) :
    (if |y| ≤ x then (1 : ℝ) else 0) ≤
      prawitzMajorantValue (T * (x - y)) + prawitzMajorantValue (T * (x + y)) - 1 := by
  have hm := prawitz_indicator_majorant (T * (x - y))
  have hp := prawitz_indicator_majorant (T * (x + y))
  simp only [mul_nonneg_iff_of_pos_left hT] at hm hp
  rw [closed_interval_indicator_identity hx]
  unfold prawitzMajorantValue
  linarith

/-- Prawitz's upper concentration bound for the actual uniform Boolean cube.
No distributional or characteristic-function hypothesis is assumed. -/
theorem rademacher_concentration_le_prawitz {n : ℕ} (c : Fin n → ℝ)
    {x T : ℝ} (hx : 0 ≤ x) (hT : 0 < T) :
    rademacherConcentration c x ≤
      2 * ∫ u in (0 : ℝ)..1, symmetricPrawitzKernel x T u * cosProduct Finset.univ c (T * u) := by
  classical
  rw [rademacherConcentration, cubeProbability_eq_expectation]
  calc
    _ ≤ cubeExpectation (fun ω =>
        prawitzMajorantValue (T * (x - rademacherSum c ω)) +
          prawitzMajorantValue (T * (x + rademacherSum c ω)) - 1) :=
      cubeExpectation_mono (fun ω => closed_interval_indicator_le_prawitz hx hT _)
    _ = cubeExpectation (fun ω => 2 * ∫ u in (0 : ℝ)..1,
        symmetricPrawitzKernel x T u * Real.cos ((T * u) * rademacherSum c ω)) := by
      congr 1
      funext ω
      exact prawitzMajorantPair_eq_integral x _ T
    _ = 2 * ∫ u in (0 : ℝ)..1,
        symmetricPrawitzKernel x T u * cosProduct Finset.univ c (T * u) := by
      rw [cubeExpectation_const_mul,
        cubeExpectation_intervalIntegral _ (fun ω => symmetricPrawitzKernel_mul_cos_intervalIntegrable x _ T)]
      congr 1
      congr 1
      funext u
      rw [cubeExpectation_const_mul]
      have heq : (fun ω : BoolCube n => Real.cos ((T * u) * rademacherSum c ω)) =
          (fun ω => Real.cos (rademacherSum c ω * (T * u))) := by
        funext ω
        rw [mul_comm (T * u)]
      rw [heq, rademacher_cos_expectation]

lemma symmetricPrawitzKernel_eq_upperKernel {a : ℝ} (ha : a ≠ 0) (x u : ℝ) :
    symmetricPrawitzKernel x (Real.pi / a) u = upperKernel (x / a) u := by
  have hphase : u * (Real.pi / a * x) = Real.pi * (x / a) * u := by ring
  unfold symmetricPrawitzKernel upperKernel prawitzSineWeight rho
  rw [hphase]
  ring

end

end KellerKlein
