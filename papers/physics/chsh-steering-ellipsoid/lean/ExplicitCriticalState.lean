import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false

namespace ExplicitCriticalState
noncomputable section

abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ
abbrev Vec := Fin 4 → ℂ

def outer (v : Vec) : Mat := fun i j => v i * star (v j)
def quadratic (A : Mat) (w : Vec) : ℂ := dotProduct (star w) (A.mulVec w)

/-- Standard density-operator conditions written without an external PSD API. -/
def Density (A : Mat) : Prop :=
  A.conjTranspose = A ∧ A.trace = 1 ∧ ∀ w : Vec, 0 ≤ (quadratic A w).re

def v0 : Vec := ![(3 / 4 : ℂ), -1 / 4, (Real.sqrt 6 : ℂ) / 8, (Real.sqrt 6 : ℂ) / 8]
def v1 : Vec := ![(Real.sqrt 6 : ℂ) / 8, (Real.sqrt 6 : ℂ) / 8, 0, 0]

def rho : Mat := (1 / 32 : ℂ) •
  !![21, -3, 3 * (Real.sqrt 6 : ℂ), 3 * (Real.sqrt 6 : ℂ);
     -3, 5, -(Real.sqrt 6 : ℂ), -(Real.sqrt 6 : ℂ);
     3 * (Real.sqrt 6 : ℂ), -(Real.sqrt 6 : ℂ), 3, 3;
     3 * (Real.sqrt 6 : ℂ), -(Real.sqrt 6 : ℂ), 3, 3]

theorem outer_mulVec (v w : Vec) :
    (outer v).mulVec w = (dotProduct (star v) w) • v := by
  ext i
  simp only [Matrix.mulVec, outer, dotProduct, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem outer_hermitian (v : Vec) : (outer v).conjTranspose = outer v := by
  ext i j
  simp only [Matrix.conjTranspose_apply, outer, star_mul, star_star]

theorem outer_quadratic_nonneg (v w : Vec) : 0 ≤ (quadratic (outer v) w).re := by
  unfold quadratic
  rw [outer_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [Matrix.star_dotProduct w v]
  change 0 ≤ ((dotProduct (star v) w) * (starRingEnd ℂ) (dotProduct (star v) w)).re
  rw [Complex.mul_conj]
  simpa using Complex.normSq_nonneg (dotProduct (star v) w)

/-- The printed density matrix has a literal two-vector PSD decomposition. -/
theorem rho_decomposition : rho = outer v0 + outer v1 := by
  have hs : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [rho, outer, v0, v1, Matrix.smul_apply, Matrix.add_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def] <;> nlinarith

theorem rho_trace : rho.trace = 1 := by
  norm_num [rho, Matrix.trace, Matrix.diag, Fin.sum_univ_three, Fin.sum_univ_four,
    Matrix.smul_apply, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]

theorem rho_is_density : Density rho := by
  refine ⟨?_, rho_trace, ?_⟩
  · rw [rho_decomposition, Matrix.conjTranspose_add, outer_hermitian, outer_hermitian]
  · intro w
    rw [rho_decomposition]
    unfold quadratic
    rw [Matrix.add_mulVec, dotProduct_add]
    have h0 := outer_quadratic_nonneg v0 w
    have h1 := outer_quadratic_nonneg v1 w
    unfold quadratic at h0 h1
    simpa only [Complex.add_re] using add_nonneg h0 h1

/-- The real Pauli correlation matrix of this state, verified below by readouts. -/
def T : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt 6 / 8, 0, Real.sqrt 6 / 4;
     0, -Real.sqrt 6 / 4, 0;
     -3 / 8, 0, 1 / 2]

def G : Matrix (Fin 3) (Fin 3) ℝ :=
  !![15 / 32, 0, 5 * Real.sqrt 6 / 64;
     0, 3 / 8, 0;
     5 * Real.sqrt 6 / 64, 0, 25 / 64]

theorem correlation_gram : T * T.transpose = G := by
  have hs : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T, G, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff] <;>
    nlinarith

theorem gram_characteristic (t : ℝ) :
    Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - G) =
      (t - 5 / 8) * (t - 3 / 8) * (t - 15 / 64) := by
  have hs : Real.sqrt (6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  rw [Matrix.det_fin_three]
  norm_num [G, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
  have he : (t - 15 / 32) * (t - 3 / 8) * (t - 25 / 64) -
      (5 * Real.sqrt 6 / 64) * (t - 3 / 8) * (5 * Real.sqrt 6 / 64) =
      (t - 5 / 8) * (t - 3 / 8) * (t - 15 / 64) +
        (6 - Real.sqrt 6 ^ 2) * (25 * t / 4096 - 75 / 32768) := by ring
  rw [hs] at he
  nlinarith

theorem gram_eigenvalue_order_and_CHSH :
    (15 / 64 : ℝ) < 3 / 8 ∧ (3 / 8 : ℝ) < 5 / 8 ∧
      (5 / 8 : ℝ) + 3 / 8 = 1 ∧
      2 * Real.sqrt ((5 / 8 : ℝ) + 3 / 8) = 2 := by
  norm_num

abbrev QubitMat := Matrix (Fin 2) (Fin 2) ℂ

def pauli (i : Fin 3) : QubitMat :=
  (![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]) i

/-- Standard tensor product in the |00>,|01>,|10>,|11> ordering. -/
def tensor (A B : QubitMat) : Mat := fun i j =>
  A ((finProdFinEquiv (m := 2) (n := 2)).symm i).1
    ((finProdFinEquiv (m := 2) (n := 2)).symm j).1 *
  B ((finProdFinEquiv (m := 2) (n := 2)).symm i).2
    ((finProdFinEquiv (m := 2) (n := 2)).symm j).2

def readout (A : Mat) : ℂ := (rho * A).trace

def a : Fin 3 → ℝ := ![Real.sqrt 6 / 8, 0, 5 / 8]
def b : Fin 3 → ℝ := ![0, 0, 1 / 2]

/-- Actual Pauli expectations of the explicit density matrix on Alice's side. -/
theorem alice_readout (i : Fin 3) : readout (tensor (pauli i) 1) = (a i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, a, rho, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

/-- Actual Pauli expectations of the explicit density matrix on Bob's side. -/
theorem bob_readout (i : Fin 3) : readout (tensor 1 (pauli i)) = (b i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, b, rho, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

/-- Every entry of the correlation matrix comes from its actual tensor Pauli operator. -/
theorem correlation_readout (i j : Fin 3) :
    readout (tensor (pauli i) (pauli j)) = (T i j : ℂ) := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, T, rho, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

/-- The usual nonsingular steering-centre formula, evaluated on the real readouts. -/
def centre : Fin 3 → ℝ := fun i =>
  (a i - (T.mulVec b) i) / (1 - dotProduct b b)

theorem bob_length_square : dotProduct b b = 1 / 4 := by
  norm_num [dotProduct, b, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.vecCons, Matrix.vecHead,
    Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ]

theorem centre_value : centre = ![0, 0, (1 / 2 : ℝ)] := by
  ext i
  fin_cases i <;>
    norm_num [centre, a, T, b, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ] <;> ring

theorem centre_length_square : dotProduct centre centre = 1 / 4 := by
  rw [centre_value]
  norm_num [dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.vecCons, Matrix.vecHead,
    Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ]

theorem bob_noncanonical : b ≠ 0 := by
  intro he
  have hb := bob_length_square
  rw [he] at hb
  norm_num at hb

end
end ExplicitCriticalState
