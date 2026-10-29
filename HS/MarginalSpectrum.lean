module
public import HS.Witness
public import HS.Spectral
public import HS.SpectralFunctions
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Matrix Polynomial

namespace HS

noncomputable def hsSpectrum : Fin 4 → ℝ := ![1/6, 1/6, 1/2, 1/6]

theorem hsMarginal_charpoly :
    hsMarginal.charpoly = (Matrix.diagonal (fun i => (hsSpectrum i : ℂ))).charpoly := by
  have h3 : Polynomial.C ((1 : ℂ) / 3) =
      (2 : ℂ[X]) * Polynomial.C ((1 : ℂ) / 6) := by
    calc
      _ = Polynomial.C ((2 : ℂ) * ((1 : ℂ) / 6)) := by congr 1; norm_num
      _ = _ := by simp [Polynomial.C_ofNat]
  have h2 : Polynomial.C ((1 : ℂ) / 2) =
      (3 : ℂ[X]) * Polynomial.C ((1 : ℂ) / 6) := by
    calc
      _ = Polynomial.C ((3 : ℂ) * ((1 : ℂ) / 6)) := by congr 1; norm_num
      _ = _ := by simp [Polynomial.C_ofNat]
  rw [Matrix.charpoly_diagonal]
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero,
    Matrix.submatrix_apply, Matrix.charmatrix_apply, Fin.sum_univ_succ, Fin.prod_univ_succ]
  norm_num [hsMarginal, hsSpectrum, Matrix.diagonal, Fin.succAbove]
  simp only [h3, h2]
  left
  ring

theorem hsMarginal_principalE3 : principalE3 hsMarginal = (5 / 108 : ℂ) := by
  simp only [principalE3, minor3, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_succ]
  norm_num [hsMarginal, Fin.succAbove]

theorem hsState_cut_minorSum (cut : Fin 3) :
    (∑ r : Fin 4, ∑ c : Fin 4,
      Complex.normSq (minor3 (flatten cut hsState) r c)) = (5 / 108 : ℝ) := by
  have h := principalE3_gram (flatten cut hsState)
  change principalE3 (reduced cut hsState) = _ at h
  rw [hsState_reduced, hsMarginal_principalE3] at h
  have h' := congrArg Complex.re h.symm
  norm_num at h'
  exact h'

theorem hsState_minorSum : minorSum hsState = (5 / 36 : ℝ) := by
  unfold minorSum
  simp only [hsState_cut_minorSum]
  norm_num

theorem hsSpectrum_entropy :
    (∑ i, -(hsSpectrum i) * Real.log (hsSpectrum i)) = Real.log 2 + Real.log 3 / 2 := by
  have h6 : Real.log ((1 : ℝ) / 6) = -(Real.log 2 + Real.log 3) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0),
      Real.log_one, show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have h2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one]
    ring
  norm_num [hsSpectrum, Fin.sum_univ_succ, h6, h2]
  ring

theorem hsState_cut_entropy (cut : Fin 3) :
    (∑ i, -(cutEigenvalues cut hsState i) * Real.log (cutEigenvalues cut hsState i)) =
      Real.log 2 + Real.log 3 / 2 := by
  have h := sum_function_eigenvalues_of_charpoly_eq_diagonal
    (reduced cut hsState) (reduced_isHermitian cut hsState) hsSpectrum
    (by rw [hsState_reduced]; exact hsMarginal_charpoly)
    (fun x => -x * Real.log x)
  exact h.trans hsSpectrum_entropy

/-- The Higuchi--Sudbery state attains the claimed average entropy exactly. -/
theorem hsState_entropy :
    (∑ cut : Fin 3, ∑ i : Fin 4,
      -(cutEigenvalues cut hsState i) * Real.log (cutEigenvalues cut hsState i)) / 3 =
      Real.log 2 + Real.log 3 / 2 := by
  simp only [hsState_cut_entropy, Fin.sum_univ_three]
  ring

end HS
