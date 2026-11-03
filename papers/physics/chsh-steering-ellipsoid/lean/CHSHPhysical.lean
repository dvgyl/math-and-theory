import CHSHAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
Minimal-import reconstruction of the actual physical extremizer family.
Definitions and proofs match the frozen v1 family, without complex-norm,
topological, or determinant imports. Positivity tests every complex vector.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false

namespace CHSHPhysical
noncomputable section

abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ
abbrev Vec := Fin 4 → ℂ

def outer (v : Vec) : Mat := fun i j => v i * star (v j)
def quadratic (A : Mat) (w : Vec) : ℂ := dotProduct (star w) (A.mulVec w)

/-- Standard density-operator conditions written without an external PSD API. -/
def Density (A : Mat) : Prop :=
  A.conjTranspose = A ∧ A.trace = 1 ∧ ∀ w : Vec, 0 ≤ (quadratic A w).re

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

abbrev QubitMat := Matrix (Fin 2) (Fin 2) ℂ

def pauli (i : Fin 3) : QubitMat :=
  (![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]) i

/-- Standard tensor product in the |00>,|01>,|10>,|11> ordering. -/
def tensor (A B : QubitMat) : Mat := fun i j =>
  A ((finProdFinEquiv (m := 2) (n := 2)).symm i).1
    ((finProdFinEquiv (m := 2) (n := 2)).symm j).1 *
  B ((finProdFinEquiv (m := 2) (n := 2)).symm i).2
    ((finProdFinEquiv (m := 2) (n := 2)).symm j).2

def v0 (a r : ℝ) : Vec :=
  ![(((1 + r) / 2 : ℝ) : ℂ), (((r - 1) / 2 : ℝ) : ℂ), ((a / 2 : ℝ) : ℂ), ((a / 2 : ℝ) : ℂ)]
def v1 (d : ℝ) : Vec := ![((d / 2 : ℝ) : ℂ), ((d / 2 : ℝ) : ℂ), 0, 0]
def state (a d r : ℝ) : Mat := outer (v0 a r) + outer (v1 d)
def readout (a d r : ℝ) (A : Mat) : ℂ := (state a d r * A).trace

def alice (a r : ℝ) : Fin 3 → ℝ := ![r * a, 0, 1 - a ^ 2]
def bob (r : ℝ) : Fin 3 → ℝ := ![0, 0, r]
def T (a r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![r * a, 0, a; 0, -a, 0; -a ^ 2, 0, r]

theorem state_trace (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    (state a d r).trace = 1 := by
  apply Complex.ext <;>
    norm_num [state, outer, v0, v1, Matrix.trace, Matrix.diag, Matrix.add_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;> nlinarith

theorem state_is_density (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    Density (state a d r) := by
  refine ⟨?_, state_trace a d r hb, ?_⟩
  · unfold state
    rw [Matrix.conjTranspose_add, outer_hermitian, outer_hermitian]
  · intro w
    unfold state quadratic
    rw [Matrix.add_mulVec, dotProduct_add]
    have h0 := outer_quadratic_nonneg (v0 a r) w
    have h1 := outer_quadratic_nonneg (v1 d) w
    unfold quadratic at h0 h1
    simpa only [Complex.add_re] using add_nonneg h0 h1

theorem alice_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) (i : Fin 3) :
    readout a d r (tensor (pauli i) 1) = (alice a r i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, alice, state, outer, v0, v1,
      Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> nlinarith

theorem bob_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) (i : Fin 3) :
    readout a d r (tensor 1 (pauli i)) = (bob r i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, bob, state, outer, v0, v1,
      Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> nlinarith

theorem correlation_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2)
    (i j : Fin 3) :
    readout a d r (tensor (pauli i) (pauli j)) = (T a r i j : ℂ) := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, T, state, outer, v0, v1,
      Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> nlinarith

def centre (a r : ℝ) : Fin 3 → ℝ := fun i =>
  (alice a r i - ((T a r).mulVec (bob r)) i) / (1 - dotProduct (bob r) (bob r))

theorem bob_length_square (r : ℝ) : dotProduct (bob r) (bob r) = r ^ 2 := by
  norm_num [dotProduct, bob, Fin.sum_univ_three, Matrix.vecCons, Matrix.vecHead,
    Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ]
  ring

theorem centre_value (c a r : ℝ) (hr : r ^ 2 < 1)
    (ha : a ^ 2 = (1 - c) * (1 - r ^ 2)) :
    centre a r = ![0, 0, c] := by
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  ext i
  fin_cases i <;>
    norm_num [centre, alice, T, bob, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, mul_comm]
  apply (div_eq_iff (show 1 - r * r ≠ 0 by nlinarith)).mpr
  nlinarith

/-- Square-root choices exist at every physical centre and every r²≤1. -/
theorem square_root_parameters (c r : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr : r ^ 2 ≤ 1) :
    let a := Real.sqrt ((1 - c) * (1 - r ^ 2))
    let d := Real.sqrt (c * (1 - r ^ 2))
    a ^ 2 = (1 - c) * (1 - r ^ 2) ∧
    d ^ 2 = c * (1 - r ^ 2) ∧ a ^ 2 + d ^ 2 = 1 - r ^ 2 := by
  have hp : 0 ≤ 1 - c := by linarith
  have hs : 0 ≤ 1 - r ^ 2 := by linarith
  have ha := Real.sq_sqrt (mul_nonneg hp hs)
  have hd := Real.sq_sqrt (mul_nonneg hc0 hs)
  dsimp only
  exact ⟨ha, hd, by nlinarith⟩


end
end CHSHPhysical
