import PolynomialFormula

noncomputable section
open scoped BigOperators
namespace FilteredF3

/-- The explicit sextic for three Bloch coordinates. -/
theorem three_dimensional_sextic (h g : Fin 3 → ℝ) (z : ℝ) :
    secularPolynomial h g z =
      (z - h 0) ^ 2 * (z - h 1) ^ 2 * (z - h 2) ^ 2 -
      (g 0) ^ 2 * (z - h 1) ^ 2 * (z - h 2) ^ 2 -
      (g 1) ^ 2 * (z - h 0) ^ 2 * (z - h 2) ^ 2 -
      (g 2) ^ 2 * (z - h 0) ^ 2 * (z - h 1) ^ 2 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have he1 : ({0, 1, 2} : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have he2 : ({0, 1, 2} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  simp only [secularPolynomial, hu]
  simp [he1, he2]
  ring

/-- Three-coordinate specialization with the final value written as three
explicit rational terms of the greatest real sextic root. -/
theorem closed_form_three_dimensional (τ : ℝ) (h g : Fin 3 → ℝ) :
    let μ := max 0 (largestRealRoot h g)
    IsGreatest {v : ℝ | ∃ x : Fin 3 → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (τ + μ + (g 0) ^ 2 / (μ - h 0) + (g 1) ^ 2 / (μ - h 1) +
        (g 2) ^ 2 / (μ - h 2)) := by
  simpa [secularValue, Fin.sum_univ_succ, add_assoc] using closed_form_diagonal τ h g

section Shift
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem secularPolynomial_shift (h g : ι → ℝ) (d z : ℝ) :
    secularPolynomial (fun i => h i - d) g z = secularPolynomial h g (z + d) := by
  have heach : ∀ i, z - (h i - d) = z + d - h i := by intro i; ring
  unfold secularPolynomial
  simp only [heach]

theorem secularValue_shift (τ : ℝ) (h g : ι → ℝ) (d z : ℝ) :
    secularValue τ (fun i => h i - d) g z = secularValue (τ - d) h g (z + d) := by
  have heach : ∀ i, z - (h i - d) = z + d - h i := by intro i; ring
  unfold secularValue
  simp only [heach]
  ring

variable [Nonempty ι]

theorem largestRealRoot_shift (h g : ι → ℝ) (d : ℝ) :
    largestRealRoot (fun i => h i - d) g = largestRealRoot h g - d := by
  have h₁ := largestRealRoot_spec (fun i => h i - d) g
  have h₂ := largestRealRoot_spec h g
  have hroot₁ := h₁.1
  change secularPolynomial (fun i => h i - d) g (largestRealRoot (fun i => h i - d) g) = 0 at hroot₁
  rw [secularPolynomial_shift] at hroot₁
  have hle₁ := h₂.2 hroot₁
  have hroot₂ : secularPolynomial (fun i => h i - d) g (largestRealRoot h g - d) = 0 := by
    rw [secularPolynomial_shift, sub_add_cancel]
    exact h₂.1
  have hle₂ := h₁.2 hroot₂
  linarith

theorem max_zero_sub_add (d ν : ℝ) : max 0 (ν - d) + d = max d ν := by
  by_cases hd : d ≤ ν
  · rw [max_eq_right (sub_nonneg.mpr hd), max_eq_right hd]
    ring
  · have hν : ν ≤ d := le_of_not_ge hd
    rw [max_eq_left (sub_nonpos.mpr hν), max_eq_left hν, zero_add]

/-- The unshifted-eigenvalue form used for the filtered F3 formula:
η=max(d,ν), with ν the greatest root of the Q-based sextic. -/
theorem closed_form_shifted (τ d : ℝ) (h g : ι → ℝ) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧
        diagObjective τ (fun i => h i - d) g x = v}
      (secularValue (τ - d) h g (max d (largestRealRoot h g))) := by
  have hmain := closed_form_diagonal τ (fun i => h i - d) g
  rw [secularValue_shift, largestRealRoot_shift, max_zero_sub_add] at hmain
  exact hmain

end Shift
end FilteredF3
