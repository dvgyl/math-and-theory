import ExtremalRadius
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
namespace SquareFlowerCompletion.Extremal
open Polynomial

def bracketPolynomial (n : ℕ) : Polynomial ℂ :=
  X * (X^2 + 3*X + 3)^n + (X^2 + 3*X + 1)^n - 1

theorem quadratic_natDegree (a : ℂ) :
    (X^2 + 3*X + C a : Polynomial ℂ).natDegree = 2 := by
  rw [natDegree_add_C, natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simp

theorem bracket_natDegree (n : ℕ) : (bracketPolynomial n).natDegree = 2*n+1 := by
  have ha : (X^2 + 3*X + 3 : Polynomial ℂ).natDegree = 2 := quadratic_natDegree 3
  have hb : (X^2 + 3*X + 1 : Polynomial ℂ).natDegree = 2 := quadratic_natDegree 1
  have han : (X^2 + 3*X + 3 : Polynomial ℂ)^n ≠ 0 := by
    apply pow_ne_zero
    intro h
    simp [h] at ha
  dsimp [bracketPolynomial]
  change (X * (X^2 + 3*X + 3)^n + (X^2 + 3*X + 1)^n - C 1 : Polynomial ℂ).natDegree = _
  rw [natDegree_sub_C, natDegree_add_eq_left_of_natDegree_lt]
  · rw [natDegree_X_mul han, natDegree_pow, ha]
    omega
  · rw [natDegree_X_mul han, natDegree_pow, natDegree_pow, ha, hb]
    omega

theorem bracket_coeff_zero (n : ℕ) : (bracketPolynomial n).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [bracketPolynomial]

theorem bracket_divX_eval_zero (n : ℕ) : (bracketPolynomial n).divX.eval 0 =
    (3 : ℂ)^n + 3*(n : ℂ) := by
  have h : ((bracketPolynomial n).derivative).eval 0 = (3 : ℂ)^n + 3*(n : ℂ) := by
    simp [bracketPolynomial, derivative_sub, derivative_add, derivative_mul, derivative_pow]
    ring
  simpa only [← coeff_zero_eq_eval_zero, coeff_divX, zero_add, coeff_derivative,
    Nat.cast_zero, Nat.cast_one, mul_one] using h

theorem exists_nonzero_graph_root {n : ℕ} (hn : 0 < n) :
    ∃ z : ℂ, z ≠ 0 ∧ (graphPolynomial n).eval z = 0 := by
  have hdeg : 0 < (bracketPolynomial n).divX.degree := by
    apply natDegree_pos_iff_degree_pos.mp
    rw [natDegree_divX_eq_natDegree_tsub_one, bracket_natDegree]
    omega
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz0 : z ≠ 0 := by
    intro h
    have hr : (0 : ℝ) < 3^n + 3*(n : ℝ) := by positivity
    have hc : (3 : ℂ)^n + 3*(n : ℂ) ≠ 0 := by
      exact_mod_cast hr.ne'
    apply hc
    simpa only [h, Polynomial.IsRoot.def, bracket_divX_eval_zero] using hz
  refine ⟨z, hz0, ?_⟩
  apply (Counting.eval_eq_zero_iff_bracket hz0).2
  have hp := (bracketPolynomial n).X_mul_divX_add
  rw [bracket_coeff_zero, map_zero, add_zero] at hp
  have he : (bracketPolynomial n).eval z = 0 := by
    rw [← hp]
    simpa only [eval_mul, eval_X, Polynomial.IsRoot.def] using mul_eq_zero_of_right z hz
  simpa [bracketPolynomial] using he

def nonzeroRootFinset (n : ℕ) : Finset ℂ := by
  classical
  exact (rootFinset n).filter (· ≠ 0)

theorem mem_nonzeroRootFinset {n : ℕ} {z : ℂ} :
    z ∈ nonzeroRootFinset n ↔ z ≠ 0 ∧ (graphPolynomial n).eval z = 0 := by
  classical
  simp only [nonzeroRootFinset, Finset.mem_filter, mem_rootFinset, and_comm]

theorem nonzeroRootFinset_nonempty {n : ℕ} (hn : 0 < n) :
    (nonzeroRootFinset n).Nonempty := by
  obtain ⟨z, hz⟩ := exists_nonzero_graph_root hn
  exact ⟨z, mem_nonzeroRootFinset.mpr hz⟩

theorem radius_pos {n : ℕ} (hn : 0 < n) : 0 < radius n := by
  obtain ⟨z, hz, hr⟩ := exists_nonzero_graph_root hn
  exact (norm_pos_iff.mpr hz).trans_le (norm_le_radius hr)

theorem radius_attained_nonzero {n : ℕ} (hn : 0 < n) :
    ∃ z : ℂ, z ∈ nonzeroRootFinset n ∧ ‖z‖ = radius n := by
  obtain ⟨z, hz, hr⟩ := radius_attained n
  refine ⟨z, mem_nonzeroRootFinset.mpr ⟨?_, hz⟩, hr⟩
  exact norm_pos_iff.mp (hr.symm ▸ radius_pos hn)

theorem radius_eq_nonzero_max {n : ℕ} (hn : 0 < n) :
    radius n = ((nonzeroRootFinset n).image norm).max'
      ((nonzeroRootFinset_nonempty hn).image norm) := by
  classical
  apply le_antisymm
  · obtain ⟨z, hz, hr⟩ := radius_attained_nonzero hn
    rw [← hr]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · apply Finset.max'_le
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    exact norm_le_radius (mem_nonzeroRootFinset.mp hz).2

#print axioms exists_nonzero_graph_root
#print axioms radius_pos
#print axioms radius_eq_nonzero_max
end SquareFlowerCompletion.Extremal
