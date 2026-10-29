import GraphReturn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Max

noncomputable section
namespace SquareFlowerCompletion
namespace Extremal

abbrev graphPolynomial (n : ℕ) : Polynomial ℂ := Counting.complexDominationPolynomial n

theorem graphPolynomial_ne_zero (n : ℕ) : graphPolynomial n ≠ 0 := by
  have h7 : (1 : ℝ) ≤ (7 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpos : 0 < (7 : ℝ) ^ n + (5 : ℝ) ^ n - 1 := by linarith
  have hval : (graphPolynomial n).eval 1 = (((7 : ℝ) ^ n + (5 : ℝ) ^ n - 1 : ℝ) : ℂ) := by
    rw [graphPolynomial, Counting.eval_complexDominationPolynomial]
    norm_num
  intro hp
  apply Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  rw [← hval, hp]
  simp

theorem graphPolynomial_eval_zero (n : ℕ) : (graphPolynomial n).eval 0 = 0 := by
  rw [graphPolynomial, Counting.eval_complexDominationPolynomial]
  simp

def rootFinset (n : ℕ) : Finset ℂ := by classical exact (graphPolynomial n).roots.toFinset

theorem mem_rootFinset {n : ℕ} {z : ℂ} : z ∈ rootFinset n ↔ (graphPolynomial n).eval z = 0 := by
  classical
  simp only [rootFinset, Multiset.mem_toFinset, Polynomial.mem_roots (graphPolynomial_ne_zero n),
    Polynomial.IsRoot.def]

def rootNorms (n : ℕ) : Finset ℝ := by classical exact (rootFinset n).image norm

theorem rootNorms_nonempty (n : ℕ) : (rootNorms n).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  exact Finset.mem_image.mpr ⟨0, mem_rootFinset.mpr (graphPolynomial_eval_zero n), norm_zero⟩

def radius (n : ℕ) : ℝ := (rootNorms n).max' (rootNorms_nonempty n)

theorem norm_le_radius {n : ℕ} {z : ℂ} (hz : (graphPolynomial n).eval z = 0) : ‖z‖ ≤ radius n := by
  classical
  exact (rootNorms n).le_max' ‖z‖ (Finset.mem_image.mpr ⟨z, mem_rootFinset.mpr hz, rfl⟩)

theorem radius_nonneg (n : ℕ) : 0 ≤ radius n := by
  simpa only [norm_zero] using norm_le_radius (graphPolynomial_eval_zero n)

theorem radius_attained (n : ℕ) : ∃ z : ℂ, (graphPolynomial n).eval z = 0 ∧ ‖z‖ = radius n := by
  classical
  have h := (rootNorms n).max'_mem (rootNorms_nonempty n)
  change radius n ∈ (rootFinset n).image norm at h
  obtain ⟨z, hz, hnorm⟩ := Finset.mem_image.mp h
  exact ⟨z, mem_rootFinset.mp hz, hnorm⟩

#print axioms graphPolynomial_ne_zero
#print axioms mem_rootFinset
#print axioms norm_le_radius
#print axioms radius_attained
end Extremal
end SquareFlowerCompletion
