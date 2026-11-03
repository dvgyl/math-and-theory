import SpectralPencil
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Actual matrix-inverse frontend for the all-case spectral pair theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace UnilateralCHSH
namespace Spectral

noncomputable section

theorem matVec_eq_mulVec (A : Mat) (x : Vec) : matVec A x = A.mulVec x := by
  funext i
  simp [matVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

theorem nonsingular_right_inverse (K : Mat) (hdet : K.det ≠ 0) (x : Vec) :
    matVec K (matVec K⁻¹ x) = x := by
  simp only [matVec_eq_mulVec]
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv K (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem nonsingular_left_inverse (K : Mat) (hdet : K.det ≠ 0) (x : Vec) :
    matVec K⁻¹ (matVec K x) = x := by
  simp only [matVec_eq_mulVec]
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul K (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem pair_iff_schur_eigenvector (A C : Mat) (s mu : ℝ) (n v : Vec)
    (hdet : (shift A (-s)).det ≠ 0) :
    IsPair A C s mu n v ↔
      v = -matVec (shift A (-s))⁻¹ (matVec C n) ∧
      matVec (schurMatrix A C (shift A (-s))⁻¹) n = fun i => mu * n i := by
  constructor
  · intro h
    exact spectral_reconstruction_converse A C (shift A (-s))⁻¹ n v s mu
      (nonsingular_left_inverse (shift A (-s)) hdet) h.1 h.2
  · rintro ⟨hv, hn⟩
    subst v
    exact spectral_reconstruction A C (shift A (-s))⁻¹ n s mu
      (nonsingular_right_inverse (shift A (-s)) hdet) hn

theorem generic_eligible_iff (A C : Mat) (s mu : ℝ)
    (hdet : (shift A (-s)).det ≠ 0) :
    mu ∈ EligibleLevel A C s ↔
      ∃ n : Vec, n ≠ 0 ∧
        matVec (schurMatrix A C (shift A (-s))⁻¹) n = (fun i => mu * n i) ∧
        normSq (matVec (shift A (-s))⁻¹ (matVec C n)) ≤ normSq n := by
  constructor
  · rintro ⟨n, v, hn, hp, hsize⟩
    obtain ⟨hv, he⟩ := (pair_iff_schur_eigenvector A C s mu n v hdet).mp hp
    refine ⟨n, hn, he, ?_⟩
    rw [hv] at hsize
    simpa [normSq, dot] using hsize
  · rintro ⟨n, hn, he, hsize⟩
    refine ⟨n, -matVec (shift A (-s))⁻¹ (matVec C n), hn, ?_, ?_⟩
    · exact (pair_iff_schur_eigenvector A C s mu n _ hdet).mpr ⟨rfl, he⟩
    · simpa [normSq, dot] using hsize

theorem generic_strict_eligible_iff (A C : Mat) (s mu : ℝ)
    (hdet : (shift A (-s)).det ≠ 0) :
    mu ∈ StrictEligibleLevel A C s ↔
      ∃ n : Vec, n ≠ 0 ∧
        matVec (schurMatrix A C (shift A (-s))⁻¹) n = (fun i => mu * n i) ∧
        normSq (matVec (shift A (-s))⁻¹ (matVec C n)) < normSq n := by
  constructor
  · rintro ⟨n, v, hn, hp, hsize⟩
    obtain ⟨hv, he⟩ := (pair_iff_schur_eigenvector A C s mu n v hdet).mp hp
    refine ⟨n, hn, he, ?_⟩
    rw [hv] at hsize
    simpa [normSq, dot] using hsize
  · rintro ⟨n, hn, he, hsize⟩
    refine ⟨n, -matVec (shift A (-s))⁻¹ (matVec C n), hn, ?_, ?_⟩
    · exact (pair_iff_schur_eigenvector A C s mu n _ hdet).mpr ⟨rfl, he⟩
    · simpa [normSq, dot] using hsize

end
end Spectral
end UnilateralCHSH
