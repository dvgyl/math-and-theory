import PolynomialFormula

noncomputable section
open scoped BigOperators
namespace FilteredF3
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The algebraic root selector automatically satisfies all multiplier
compatibility conditions; none are additional input assumptions. -/
theorem selected_multiplier_conditions (h g : ι → ℝ) :
    let μ := max 0 (largestRealRoot h g)
    0 ≤ μ ∧ (∀ i, h i ≤ μ) ∧ (∀ i, h i = μ → g i = 0) ∧ secular h g μ ≤ 1 := by
  obtain ⟨μ, hl, hb, _⟩ := exact_diagonal_solution 0 h g
  have heq := branch_multiplier_is_root_formula h g μ hb
  dsimp only
  rw [← heq]
  refine ⟨le_trans (spectralThreshold_nonneg h) hl,
    (fun i => le_trans (le_spectralThreshold h i) hl), ?_, ?_⟩
  · rcases hb with ⟨hz, hc, _⟩ | ⟨hlt, _⟩
    · simpa [hz] using hc
    · intro i hi
      have ht : h i < μ := lt_of_le_of_lt (le_spectralThreshold h i) hlt
      exact False.elim ((ne_of_lt ht) hi)
  · rcases hb with ⟨hz, _, hs⟩ | ⟨_, hs⟩
    · simpa [hz] using hs
    · exact hs.le

/-- Every extremizer of the algebraic closed-form objective is classified:
nonzero multiplier directions are fixed by the pseudoinverse solution;
null directions are free, subject to the ball and complementarity. -/
theorem all_extremizers (τ : ℝ) (h g x : ι → ℝ) (hx : radiusSq x ≤ 1) :
    let μ := max 0 (largestRealRoot h g)
    diagObjective τ h g x = secularValue τ h g μ ↔
      (∀ i, μ = h i ∨ x i = g i / (μ - h i)) ∧
      (μ = 0 ∨ radiusSq x = 1) := by
  let μ := max 0 (largestRealRoot h g)
  obtain ⟨hμ, hdiag, hc, _⟩ := selected_multiplier_conditions h g
  have hstation : ∀ i, (μ - h i) * secularPoint h g μ i = g i := by
    intro i
    by_cases hi : h i = μ
    · simp [secularPoint, hi, hc i hi]
    · exact mul_div_cancel₀ (g i) (sub_ne_zero.mpr (Ne.symm hi))
  change diagObjective τ h g x = secularValue τ h g μ ↔ _
  rw [← diagValue_secular]
  rw [diagonal_equality_iff τ μ h g (secularPoint h g μ) x hμ hdiag hstation hx]
  simp only [secularPoint, mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℝ)), μ]

end FilteredF3
