module
public import MathAndTheory.Mathematics.DomiRank.Matrix
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Star.Real

/-!
A rational LDL certificate proves that 15 I + 4 A is positive semidefinite.
Consequently I + s A is positive definite for every 0 ≤ s < 4/15,
including the full counterexample interval [251/1000,63/250].
Every entry of the factorization is checked by ordinary Lean proofs;
there is no floating-point eigenvalue assumption.
-/
noncomputable section

@[expose] public section

namespace MathAndTheory.DomiRank
open Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def ldlD : Fin 14 → ℝ := ![15, 15, (209 / 15), (3491 / 285), (42317 / 3491), (46233 / 3847), (45013 / 4203), (481723 / 45013), (468303 / 43793), (9733 / 1851), (116379 / 9733), (144605 / 12931), (285735 / 28921), (137655 / 19049)]

private def ldlR : Matrix (Fin 14) (Fin 14) ℝ := ![
  ![1, 0, 0, (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), 0, 0, 0, 0],
  ![0, 1, (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), (4 / 15), 0, 0, 0, 0],
  ![0, 0, 1, (4 / 19), (4 / 19), (4 / 19), (4 / 19), (4 / 19), (4 / 19), (4 / 19), 0, 0, 0, 0],
  ![0, 0, 0, 1, (356 / 3491), (356 / 3491), (-784 / 3491), (-784 / 3491), (-784 / 3491), (-784 / 3491), 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, (356 / 3847), (-784 / 3847), (-784 / 3847), (-784 / 3847), (-784 / 3847), 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, (-784 / 4203), (-784 / 4203), (-784 / 4203), (-784 / 4203), 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, (-1220 / 45013), (-1220 / 45013), (-18032 / 45013), 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, (-1220 / 43793), (-18032 / 43793), 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, (-784 / 1851), 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (7404 / 9733), (7404 / 9733), (7404 / 9733), (7404 / 9733)],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-9872 / 38793), (-9872 / 38793), (-9872 / 38793)],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-9872 / 28921), (-9872 / 28921)],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-9872 / 19049)],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

private theorem ldlD_nonneg : ∀ i, 0 ≤ ldlD i := by
  intro i
  fin_cases i <;> norm_num [ldlD]

/-- Exact rational Gram factorization of the shifted adjacency matrix. -/
private theorem shifted_factorization :
    (15 : ℝ) • (1 : Matrix (Fin 14) (Fin 14) ℝ) + (4 : ℝ) • A =
      ldlRᴴ * diagonal ldlD * ldlR := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial]
  fin_cases i <;> fin_cases j <;>
    norm_num [ldlR, ldlD, A, adjData, Fin.sum_univ_succ, Matrix.one_apply]

/-- A certified lower spectral bound; equivalently every eigenvalue of A is ≥ -15/4. -/
theorem shifted_posSemidef :
    ((15 : ℝ) • (1 : Matrix (Fin 14) (Fin 14) ℝ) + (4 : ℝ) • A).PosSemidef := by
  rw [shifted_factorization]
  exact (Matrix.PosSemidef.diagonal ldlD_nonneg).conjTranspose_mul_mul_same ldlR

/-- The entire interval 0 ≤ s < 4/15 lies in the nonsingular stable DomiRank range. -/
theorem resolvent_posDef (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 4 / 15) :
    (resolvent s).PosDef := by
  have hp : 0 < 1 - 15 * s / 4 := by linarith
  have hq : 0 ≤ s / 4 := by positivity
  have hI : ((1 - 15 * s / 4) • (1 : Matrix (Fin 14) (Fin 14) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hp
  have hM := shifted_posSemidef.smul hq
  have heq : resolvent s =
      (1 - 15 * s / 4) • (1 : Matrix (Fin 14) (Fin 14) ℝ) +
        (s / 4) • ((15 : ℝ) • (1 : Matrix (Fin 14) (Fin 14) ℝ) + (4 : ℝ) • A) := by
    ext i j
    simp only [resolvent, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hI.add_posSemidef hM

theorem resolvent_isUnit (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 4 / 15) :
    IsUnit (resolvent s) := (resolvent_posDef s hs0 hs1).isUnit

end MathAndTheory.DomiRank
