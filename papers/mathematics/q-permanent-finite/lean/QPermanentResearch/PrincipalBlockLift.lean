import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
A positive principal block plus a strictly positive correction in the last
coordinate makes a positive-semidefinite matrix positive definite. This is the
finite matrix step in the three-mode inertia obstruction; no integral or
asymptotic identification is asserted here.
-/

namespace QPermanentResearch
open scoped BigOperators

def lastCoordinateDiagonal (n : ℕ) (c : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.diagonal (fun i => if i = Fin.last n then c else 0)

theorem lastCoordinateDiagonal_isHermitian (n : ℕ) (c : ℝ) :
    (lastCoordinateDiagonal n c).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  rfl

theorem lastCoordinateDiagonal_quadratic (n : ℕ) (c : ℝ) (x : Fin (n+1) → ℝ) :
    dotProduct (star x) ((lastCoordinateDiagonal n c).mulVec x) =
      c * (x (Fin.last n))^2 := by
  classical
  simp only [lastCoordinateDiagonal, Matrix.mulVec_diagonal, dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp only [Pi.star_apply, star_trivial, Pi.mul_apply, Fin.castSucc_ne_last,
    ite_false, zero_mul, mul_zero, Finset.sum_const_zero, ite_true, zero_add]
  ring

theorem principalBlock_quadratic_of_last_zero {n : ℕ}
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (x : Fin (n+1) → ℝ)
    (hx : x (Fin.last n) = 0) :
    dotProduct (star x) (D.mulVec x) =
      dotProduct (star (fun i : Fin n => x i.castSucc))
        ((D.submatrix Fin.castSucc Fin.castSucc).mulVec
          (fun i : Fin n => x i.castSucc)) := by
  classical
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, hx, Matrix.submatrix_apply]

/-- The only possible null direction left by the positive principal block is
removed by a positive diagonal correction in the complementary coordinate. -/
theorem posDef_add_lastCoordinateDiagonal {n : ℕ}
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (c : ℝ)
    (hD : D.PosSemidef)
    (hblock : (D.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hc : 0 < c) : (D + lastCoordinateDiagonal n c).PosDef := by
  refine ⟨hD.1.add (lastCoordinateDiagonal_isHermitian n c), ?_⟩
  intro x hx
  rw [Matrix.add_mulVec, dotProduct_add, lastCoordinateDiagonal_quadratic]
  by_cases hl : x (Fin.last n) = 0
  · have hold : (fun i : Fin n => x i.castSucc) ≠ 0 := by
      intro hold
      apply hx
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hl
      · exact congrFun hold j
    rw [principalBlock_quadratic_of_last_zero D x hl]
    simpa only [hl, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
      hblock.2 (fun i : Fin n => x i.castSucc) hold
  · exact add_pos_of_nonneg_of_pos (hD.2 x) (mul_pos hc (sq_pos_of_ne_zero hl))

theorem three_dimensional_principal_plane_lift_posDef
    (D : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ)
    (hD : D.PosSemidef)
    (hplane : (D.submatrix (Fin.castSucc : Fin 2 → Fin 3)
      (Fin.castSucc : Fin 2 → Fin 3)).PosDef) (hc : 0 < c) :
    (D + Matrix.diagonal ![0, 0, c]).PosDef := by
  have hdiag : (fun i : Fin 3 => if i = Fin.last 2 then c else 0) = ![0, 0, c] := by
    ext i
    fin_cases i <;> rfl
  simpa only [lastCoordinateDiagonal, hdiag] using
    posDef_add_lastCoordinateDiagonal D c hD hplane hc

end QPermanentResearch
