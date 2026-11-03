import SpectralBridge
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Tactic.FunProp

/-! The exact algebraic maximum on the closed Bloch ball is the supremum
over its open ball. This closes the distinction between singular filters
and the invertible filters used in Equation 10. -/

noncomputable section
open scoped BigOperators
namespace FilteredF3

theorem continuous_closedBall_isLUB_openBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : Continuous f) (V : ℝ)
    (hV : IsGreatest {v : ℝ | ∃ x : E, ‖x‖ ≤ 1 ∧ f x = v} V) :
    IsLUB {v : ℝ | ∃ x : E, ‖x‖ < 1 ∧ f x = v} V := by
  constructor
  · rintro v ⟨x, hx, hv⟩
    exact hV.2 ⟨x, hx.le, hv⟩
  · intro u hu
    obtain ⟨x, hx, hv⟩ := hV.1
    have hclosed : IsClosed {y : E | f y ≤ u} := isClosed_le hf continuous_const
    have hsub : Metric.ball (0 : E) 1 ⊆ {y : E | f y ≤ u} := by
      intro y hy
      apply hu
      exact ⟨y, by simpa using hy, rfl⟩
    have hcl := closure_minimal hsub hclosed
    rw [closure_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hcl
    have hfx := hcl (show x ∈ Metric.closedBall (0 : E) 1 by simpa using hx)
    simpa [hv] using hfx

theorem inner_closedBall_isLUB_openBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (hf : Continuous f) (V : ℝ)
    (hV : IsGreatest {v : ℝ | ∃ x : E, inner (𝕜 := ℝ) x x ≤ 1 ∧ f x = v} V) :
    IsLUB {v : ℝ | ∃ x : E, inner (𝕜 := ℝ) x x < 1 ∧ f x = v} V := by
  have hle : ∀ x : E, ‖x‖ ≤ 1 ↔ inner (𝕜 := ℝ) x x ≤ 1 := by
    intro x
    rw [real_inner_self_eq_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  have hlt : ∀ x : E, ‖x‖ < 1 ↔ inner (𝕜 := ℝ) x x < 1 := by
    intro x
    rw [real_inner_self_eq_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  simpa only [hlt] using continuous_closedBall_isLUB_openBall f hf V
    (by simpa only [hle] using hV)

/-- Actual open-ball supremum for an arbitrary real symmetric 3 by 3 matrix,
with no diagonalization, root-existence, or attainment hypotheses. -/
theorem open_ball_real_matrix_three (τ : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsHermitian) (g : Fin 3 → ℝ) :
    IsLUB {v : ℝ | ∃ x : Fin 3 → ℝ, radiusSq x < 1 ∧ matrixObjective τ H g x = v}
      (matrixAlgebraicValue τ H hH g) := by
  let ge : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm g
  have hcH : Continuous H.toEuclideanLin := H.toEuclideanLin.continuous_of_finiteDimensional
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => objective τ ge H.toEuclideanLin x) := by
    unfold objective
    fun_prop
  have hm := inner_closedBall_isLUB_openBall
    (fun x : EuclideanSpace ℝ (Fin 3) => objective τ ge H.toEuclideanLin x) hc
    (matrixAlgebraicValue τ H hH g) (closed_form_real_symmetric_three τ ge H hH)
  have heq : {v : ℝ | ∃ x : EuclideanSpace ℝ (Fin 3),
      inner (𝕜 := ℝ) x x < 1 ∧ objective τ ge H.toEuclideanLin x = v} =
      {v : ℝ | ∃ x : Fin 3 → ℝ, radiusSq x < 1 ∧ matrixObjective τ H g x = v} := by
    ext v
    constructor
    · rintro ⟨x, hx, hv⟩
      let y : Fin 3 → ℝ := WithLp.equiv 2 _ x
      have hy : (WithLp.equiv 2 _).symm y = x := (WithLp.equiv 2 _).symm_apply_apply x
      refine ⟨y, ?_, ?_⟩
      · have hi := plain_real_inner_three y y
        rw [hy] at hi
        simpa [radiusSq, dotProduct, pow_two, hi] using hx
      · rw [← matrix_objective_operator, hy]
        exact hv
    · rintro ⟨x, hx, hv⟩
      refine ⟨(WithLp.equiv 2 _).symm x, ?_, ?_⟩
      · rw [plain_real_inner_three]
        simpa [radiusSq, dotProduct, pow_two] using hx
      · rw [matrix_objective_operator]
        exact hv
  rwa [heq] at hm

end FilteredF3
