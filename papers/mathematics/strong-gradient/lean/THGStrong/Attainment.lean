import THGStrong.Huber
import THGStrong.Reduction

/-!
The known Huber and quadratic examples give exact attainment of the complete
normalized curve. This is a formal sharpness companion, not a novelty claim
for the lower-bound examples.
-/

noncomputable section

namespace THGStrong.Sharpness

def NormalizedAttainment (μ h : ℝ) (N : ℕ) (c : ℝ) : Prop :=
  ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ),
    StrongConvexOn Set.univ μ f ∧
    (∀ z, HasGradientAt f (g z) z) ∧
    (∀ y z, ‖g y-g z‖ ≤ ‖y-z‖) ∧
    (∀ z, f 0 ≤ f z) ∧ x 0 = 1 ∧
    (∀ i < N, x (i+1) = x i-h*g (x i)) ∧
    ‖g (x N)‖ = c

lemma gradientRate_zero_step (μ : ℝ) (N : ℕ) : gradientRate μ 0 N = 1 := by
  unfold gradientRate
  by_cases hμ : μ = 0
  · simp [hμ]
  · simp only [hμ, ite_false, mul_zero, sub_zero, one_pow, mul_one,
      zero_mul, add_zero, abs_one]
    have hd : 1-(1-μ) = μ := by ring
    rw [hd, div_self hμ]
    norm_num

/-- Actual one-dimensional attainment for every curvature ratio, every closed
normalized step in [0,2], and every finite horizon, including all endpoints. -/
theorem attain_rate {μ h : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hh : 0 ≤ h) (hh2 : h ≤ 2) (N : ℕ) :
    NormalizedAttainment μ h N (gradientRate μ h N) := by
  by_cases hh0 : h = 0
  · subst h
    rw [gradientRate_zero_step]
    simpa only [sub_zero, abs_one, one_pow] using
      quadratic_oscillation_attainment hμ1 0 N
  have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  by_cases ha : 0 < 1-μ*h
  · have hτ : threshold μ h N = if μ = 0 then (1+(N:ℝ)*h)⁻¹ else
        μ*(1-μ*h)^N/(1-(1-μ)*(1-μ*h)^N) :=
      progress_rate_formula hμ0 hhp ha N
    have hr : gradientRate μ h N = max (threshold μ h N) (|1-h|^N) := by
      unfold gradientRate
      rw [hτ]
    rw [hr]
    by_cases hb : |1-h|^N ≤ threshold μ h N
    · rw [max_eq_left hb]
      exact huber_progress_attainment hμ0 hμ1 hhp ha N
    · rw [max_eq_right (le_of_not_ge hb)]
      exact quadratic_oscillation_attainment hμ1 h N
  · have ha0 : 1-μ*h ≤ 0 := le_of_not_gt ha
    have hμne : μ ≠ 0 := by
      intro he
      simp [he] at ha
    have hμp : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμne)
    have hμh := mul_le_mul_of_nonneg_right hμ1 hh
    have hr0 : 0 ≤ h-1 := by nlinarith
    have habs : |1-h| = h-1 := by
      rw [abs_of_nonpos (by linarith : 1-h ≤ 0)]
      ring
    have hd := nonpositive_affine_rate_dominated hμp hμ1 hh hh2 ha0 N
    have hr : gradientRate μ h N = |1-h|^N := by
      unfold gradientRate
      rw [if_neg hμne]
      apply max_eq_right
      simpa only [habs] using hd
    rw [hr]
    exact quadratic_oscillation_attainment hμ1 h N

#print axioms attain_rate

end THGStrong.Sharpness
