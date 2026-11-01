import KellerKlein.Imports

/-! The normalized sine, including its removable value at the origin.
This compatibility definition is needed because the pinned mathlib predates
the separate trigonometric Sinc module. -/

namespace Real

theorem cos_two_mul_eq_one_sub (x : ℝ) : cos (2*x) = 1-2*sin x^2 := by
  rw [cos_two_mul]
  nlinarith [sin_sq_add_cos_sq x]

noncomputable def sinc (x : ℝ) : ℝ := dslope sin 0 x

@[simp] theorem sinc_zero : sinc 0 = 1 := by
  simp [sinc, dslope_same, deriv_sin]

theorem sinc_of_ne_zero {x : ℝ} (hx : x ≠ 0) : sinc x = sin x / x := by
  simp [sinc, dslope_of_ne _ hx, slope_def_field]

@[fun_prop] theorem continuous_sinc : Continuous sinc := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr (differentiable_sin.differentiableAt)
  · exact (continuousAt_dslope_of_ne hx).mpr continuous_sin.continuousAt

@[simp] theorem sinc_neg (x : ℝ) : sinc (-x) = sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero (neg_ne_zero.mpr hx), sinc_of_ne_zero hx, sin_neg]

end Real
