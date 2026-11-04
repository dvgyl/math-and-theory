module

public import MatCKronecker.NonnegativeRank
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace PositiveCore.ConeObstruction

open Matrix MatCKronecker
open scoped BigOperators

def twist : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, -1, -1; -1, 1, 1, -1; -1, -1, 1, 1; 1, -1, -1, 1]

noncomputable def nested (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => 1 + a * twist i j

noncomputable def score (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, ∑ j, twist i j * M i j

noncomputable def mass (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j

theorem difference_mul_le (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x - y) * z ≤ (x + y) * |z| := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    nlinarith [mul_nonneg hy hz]
  · rw [abs_of_nonpos hz]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hx hz]

/-- A separating functional for rank-one terms intrinsic to the nested-square
row and column spaces. This is homogeneous and permits zero vectors. -/
theorem cone_pairing_bound (u v : Fin 4 → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hurel : u 0 + u 2 = u 1 + u 3)
    (hvrel : v 0 + v 2 = v 1 + v 3) :
    score (Matrix.vecMulVec u v) ≤ (∑ i, u i) * (∑ j, v j) / 2 := by
  let s := u 0 + u 2
  let t := v 0 + v 2
  let c₀ := v 0 + v 1 - v 2 - v 3
  let c₁ := -v 0 + v 1 + v 2 - v 3
  have hs : 0 ≤ s := add_nonneg (hu 0) (hu 2)
  have hsumu : (∑ i, u i) = 2 * s := by
    norm_num [Fin.sum_univ_succ]
    dsimp [s]
    linarith
  have hsumv : (∑ i, v i) = 2 * t := by
    norm_num [Fin.sum_univ_succ]
    dsimp [t]
    linarith
  have hfirst := difference_mul_le (u 0) (u 2) c₀ (hu 0) (hu 2)
  have hsecond := difference_mul_le (u 1) (u 3) c₁ (hu 1) (hu 3)
  rw [← hurel] at hsecond
  have hcorner : |c₀| + |c₁| ≤ 2 * t := by
    rcases le_total 0 c₀ with h₀ | h₀ <;>
      rcases le_total 0 c₁ with h₁ | h₁
    · rw [abs_of_nonneg h₀, abs_of_nonneg h₁]
      dsimp [c₀, c₁, t]
      linarith [hv 3]
    · rw [abs_of_nonneg h₀, abs_of_nonpos h₁]
      dsimp [c₀, c₁, t]
      linarith [hv 2]
    · rw [abs_of_nonpos h₀, abs_of_nonneg h₁]
      dsimp [c₀, c₁, t]
      linarith [hv 0]
    · rw [abs_of_nonpos h₀, abs_of_nonpos h₁]
      dsimp [c₀, c₁, t]
      linarith [hv 1]
  calc
    score (Matrix.vecMulVec u v) = (u 0 - u 2) * c₀ + (u 1 - u 3) * c₁ := by
      norm_num [score, twist, Matrix.vecMulVec, Fin.sum_univ_succ, c₀, c₁] <;> ring
    _ ≤ s * |c₀| + s * |c₁| := add_le_add hfirst hsecond
    _ = s * (|c₀| + |c₁|) := by ring
    _ ≤ s * (2 * t) := mul_le_mul_of_nonneg_left hcorner hs
    _ = (∑ i, u i) * (∑ j, v j) / 2 := by rw [hsumu, hsumv]; ring

theorem score_mul {p : Type*} [Fintype p]
    (U : Matrix (Fin 4) p ℝ) (V : Matrix p (Fin 4) ℝ) :
    score (U * V) = ∑ h, score (Matrix.vecMulVec (fun i => U i h) (V h)) := by
  classical
  simp only [score, Matrix.mul_apply, Finset.mul_sum, Matrix.vecMulVec_apply]
  calc
    (∑ i, ∑ j, ∑ h, twist i j * (U i h * V h j)) =
        ∑ i, ∑ h, ∑ j, twist i j * (U i h * V h j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ h, ∑ i, ∑ j, twist i j * (U i h * V h j) := Finset.sum_comm

theorem mass_mul {p : Type*} [Fintype p]
    (U : Matrix (Fin 4) p ℝ) (V : Matrix p (Fin 4) ℝ) :
    mass (U * V) = ∑ h, (∑ i, U i h) * (∑ j, V h j) := by
  classical
  simp only [mass, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ h, U i h * V h j) =
        ∑ i, ∑ h, ∑ j, U i h * V h j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ h, ∑ i, ∑ j, U i h * V h j := Finset.sum_comm
    _ = ∑ h, ∑ j, ∑ i, U i h * V h j := by
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm

/-- Every nonnegative factorization whose columns and rows lie in the two
rank-three intrinsic spaces obeys the separating-functional inequality. -/
theorem factorization_score_bound {p : Type*} [Fintype p]
    (U : Matrix (Fin 4) p ℝ) (V : Matrix p (Fin 4) ℝ)
    (hU : EntryNonneg U) (hV : EntryNonneg V)
    (hu : ∀ h, U 0 h + U 2 h = U 1 h + U 3 h)
    (hv : ∀ h, V h 0 + V h 2 = V h 1 + V h 3) :
    score (U * V) ≤ mass (U * V) / 2 := by
  classical
  rw [score_mul, mass_mul, Finset.sum_div]
  exact Finset.sum_le_sum fun h _ =>
    cone_pairing_bound (fun i => U i h) (V h) (fun i => hU i h) (hV h) (hu h) (hv h)

theorem score_nested (a : ℝ) : score (nested a) = 16 * a := by
  norm_num [score, nested, twist, Fin.sum_univ_succ] <;> ring

theorem mass_nested (a : ℝ) : mass (nested a) = 16 := by
  norm_num [mass, nested, twist, Fin.sum_univ_succ] <;> ring

/-- Intrinsic nonnegative factorizations of the nested-square family require
the parameter to be at most one half, independently of factorization width. -/
theorem parameter_le_half {p : Type*} [Fintype p]
    (a : ℝ) (U : Matrix (Fin 4) p ℝ) (V : Matrix p (Fin 4) ℝ)
    (hU : EntryNonneg U) (hV : EntryNonneg V)
    (hu : ∀ h, U 0 h + U 2 h = U 1 h + U 3 h)
    (hv : ∀ h, V h 0 + V h 2 = V h 1 + V h 3)
    (hUV : U * V = nested a) : a ≤ (1 : ℝ) / 2 := by
  have h := factorization_score_bound U V hU hV hu hv
  rw [hUV, score_nested, mass_nested] at h
  linarith

end PositiveCore.ConeObstruction
