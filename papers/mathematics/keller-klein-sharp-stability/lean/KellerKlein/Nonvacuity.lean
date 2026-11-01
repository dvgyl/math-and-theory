import KellerKlein.Main

open scoped BigOperators

namespace KellerKlein

noncomputable def exampleCoefficients : Fin 256 → ℝ := fun _ => 1 / 16

theorem exampleCoefficients_normalized : ∑ i, exampleCoefficients i ^ 2 = 1 := by
  norm_num [exampleCoefficients, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem exampleCoefficients_bounded : ∀ i, |exampleCoefficients i| ≤ (1 / 16 : ℝ) := by
  intro i
  exact (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).le

/-- An explicit 256-variable normalized model satisfying the central theorem's
strictly positive coefficient and nonempty range hypotheses. -/
theorem central_hypotheses_nonvacuous :
    (0 : ℝ) < 1 / 16 ∧ (1 / 16 : ℝ) ≤ 7 / 100 ∧
      (∀ i, |exampleCoefficients i| ≤ (1 / 16 : ℝ)) ∧
        (∑ i, exampleCoefficients i ^ 2) = 1 := by
  exact ⟨by norm_num, by norm_num, exampleCoefficients_bounded, exampleCoefficients_normalized⟩

theorem example_actual_cdf_bound (x : ℝ) (hx : 0 ≤ x) :
    rademacherCDF exampleCoefficients x -
        ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x ≤
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (1 / 16) - 1 / 2 :=
  small_coefficient_upper_cdf exampleCoefficients (by norm_num) (by norm_num)
    exampleCoefficients_bounded exampleCoefficients_normalized hx

end KellerKlein
