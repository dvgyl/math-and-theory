/- Reused from the existing Milne formalization in the user workspace.
   Provenance and original SHA256 are recorded in QuantumPrior/PROVENANCE.json.
   Imports were dependency-minimized; proof statements and bodies are unchanged. -/
import QuantumPrior.MilnePauliAlgebra

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

theorem qubitBall_trace (x : V3) :
    Matrix.trace (1 + spin x) = (2 : ℂ) := by
  simp [Matrix.trace, Matrix.diag, spin, Fin.sum_univ_two]
  ring

theorem qubitBall_det (x : V3) :
    Matrix.det (1 + spin x) = ((1-vSq x : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [spin, Matrix.one_apply, vSq, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, pow_two]
  all_goals ring

/-- The closed Bloch ball consists of positive qubit matrices, including its
rank-one boundary. This proof uses only the two real eigenvalues, their sum,
and their product, and therefore does not divide by an eigenvalue. -/
theorem qubitBall_psd (x : V3) (hx : vSq x ≤ 1) :
    (1 + spin x).PosSemidef := by
  have hH : (1 + spin x).IsHermitian := Matrix.isHermitian_one.add (spin_hermitian x)
  have hsum : hH.eigenvalues 0 + hH.eigenvalues 1 = 2 := by
    have h := trace_eq_eigenvalue_sum hH
    rw [qubitBall_trace] at h
    simpa [Fin.sum_univ_two] using h.symm
  have hprod : hH.eigenvalues 0 * hH.eigenvalues 1 = 1-vSq x := by
    have h := hH.det_eq_prod_eigenvalues
    rw [qubitBall_det] at h
    have h' := congrArg Complex.re h
    simpa [Fin.prod_univ_two, Complex.mul_re] using h'.symm
  have h0 : 0 ≤ hH.eigenvalues 0 := by
    by_contra hn
    have hn' : hH.eigenvalues 0 < 0 := lt_of_not_ge hn
    have hp : 0 < hH.eigenvalues 1 := by linarith
    have hm := mul_neg_of_neg_of_pos hn' hp
    linarith
  have h1 : 0 ≤ hH.eigenvalues 1 := by
    by_contra hn
    have hn' : hH.eigenvalues 1 < 0 := lt_of_not_ge hn
    have hp : 0 < hH.eigenvalues 0 := by linarith
    have hm := mul_neg_of_pos_of_neg hp hn'
    linarith
  apply hH.posSemidef_of_eigenvalues_nonneg
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- The positive square-root filter realizing a point of the closed Bloch
ball. Its determinant vanishes precisely on the rank-one boundary. -/
def qubitBallFilter (x : V3) (hx : vSq x ≤ 1) : Matrix Q Q ℂ :=
  (qubitBall_psd x hx).sqrt

theorem qubitBallFilter_psd (x : V3) (hx : vSq x ≤ 1) :
    (qubitBallFilter x hx).PosSemidef :=
  (qubitBall_psd x hx).posSemidef_sqrt

theorem qubitBallFilter_hermitian (x : V3) (hx : vSq x ≤ 1) :
    (qubitBallFilter x hx).IsHermitian :=
  (qubitBallFilter_psd x hx).1

theorem qubitBallFilter_squared (x : V3) (hx : vSq x ≤ 1) :
    qubitBallFilter x hx * qubitBallFilter x hx = 1 + spin x :=
  (qubitBall_psd x hx).sqrt_mul_self

theorem qubitBallFilter_trace_squared (x : V3) (hx : vSq x ≤ 1) :
    Matrix.trace (qubitBallFilter x hx * qubitBallFilter x hx) = 2 := by
  rw [qubitBallFilter_squared, qubitBall_trace]

theorem qubitBallFilter_det_squared (x : V3) (hx : vSq x ≤ 1) :
    (qubitBallFilter x hx).det ^ 2 = ((1-vSq x : ℝ) : ℂ) := by
  rw [pow_two, ← Matrix.det_mul, qubitBallFilter_squared, qubitBall_det]

theorem qubitBallFilter_det_ne_zero (x : V3) (hx : vSq x < 1) :
    (qubitBallFilter x (le_of_lt hx)).det ≠ 0 := by
  intro h0
  have h := qubitBallFilter_det_squared x (le_of_lt hx)
  rw [h0] at h
  have hr := congrArg Complex.re h
  norm_num at hr
  linarith

theorem qubitBallFilter_det_eq_zero_iff (x : V3) (hx : vSq x ≤ 1) :
    (qubitBallFilter x hx).det = 0 ↔ vSq x = 1 := by
  constructor
  · intro h0
    have h := qubitBallFilter_det_squared x hx
    rw [h0] at h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  · intro h1
    have h := qubitBallFilter_det_squared x hx
    rw [h1] at h
    norm_num at h
    exact h

end Milne

#print axioms Milne.qubitBall_psd
#print axioms Milne.qubitBallFilter_det_ne_zero
#print axioms Milne.qubitBallFilter_det_eq_zero_iff
