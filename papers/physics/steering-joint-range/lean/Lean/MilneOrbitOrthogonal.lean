import MilneOrbitDiagonal
import MilneBlochDefs
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Exact orthogonal-coordinate identities for the complete orbit solver. -/

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

def trustQuadratic (τ : ℝ) (k : V3) (K : T3) (x : V3) : ℝ :=
  τ+2*vDot k x-vDot x (tVec K x)

theorem trust_completed_square (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (p : V3) (hp : tVec K p=k) (x : V3) :
    trustQuadratic τ k K p-trustQuadratic τ k K x=
      vDot (x-p) (tVec K (x-p)) := by
  rw [← hp]
  have h10 : K 1 0=K 0 1 := by simpa using hK.apply 0 1
  have h20 : K 2 0=K 0 2 := by simpa using hK.apply 0 2
  have h21 : K 2 1=K 1 2 := by simpa using hK.apply 1 2
  simp [trustQuadratic,vDot,tVec,Pi.sub_apply,Fin.sum_univ_three]
  rw [h10,h20,h21]
  ring

theorem trust_vDot_self (x : V3) : vDot x x=vSq x := by
  simp [vDot,vSq,pow_two]

theorem trust_tVec_mul (A B : T3) (x : V3) :
    tVec A (tVec B x)=tVec (A*B) x := Matrix.mulVec_mulVec _ _ _

theorem trust_tVec_one (x : V3) : tVec (1 : T3) x=x := Matrix.one_mulVec _

theorem trust_vDot_left_transform (A : T3) (x y : V3) :
    vDot (tVec A x) y=vDot x (tVec A.transpose y) := by
  simp [vDot,tVec,Matrix.transpose_apply,Fin.sum_univ_three]
  ring

theorem trust_vDot_right_transform (A : T3) (x y : V3) :
    vDot x (tVec A y)=vDot (tVec A.transpose x) y := by
  simp [vDot,tVec,Matrix.transpose_apply,Fin.sum_univ_three]
  ring

theorem trust_orthogonal_norm (U : T3) (hU : U.transpose*U=1) (x : V3) :
    vSq (tVec U x)=vSq x := by
  rw [← trust_vDot_self,trust_vDot_left_transform,trust_tVec_mul,hU,
    trust_tVec_one,trust_vDot_self]

theorem trust_vSq_smul (s : ℝ) (x : V3) : vSq (s • x)=s^2*vSq x := by
  simp [vSq,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]

def trustEigenbasis (K : T3) (hK : K.IsHermitian) : T3 := hK.eigenvectorUnitary

def trustEigenvalues (K : T3) (hK : K.IsHermitian) : V3 := hK.eigenvalues

def trustEigenLinear (K : T3) (hK : K.IsHermitian) (k : V3) : V3 :=
  tVec (trustEigenbasis K hK).transpose k

theorem trustEigenbasis_left (K : T3) (hK : K.IsHermitian) :
    (trustEigenbasis K hK).transpose*trustEigenbasis K hK=1 := by
  simpa only [trustEigenbasis,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    unitary.coe_star_mul_self hK.eigenvectorUnitary

theorem trustEigenbasis_right (K : T3) (hK : K.IsHermitian) :
    trustEigenbasis K hK*(trustEigenbasis K hK).transpose=1 := by
  simpa only [trustEigenbasis,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    unitary.coe_mul_star_self hK.eigenvectorUnitary

theorem trustEigenbasis_diagonal (K : T3) (hK : K.IsHermitian) :
    (trustEigenbasis K hK).transpose*K*trustEigenbasis K hK=
      Matrix.diagonal (trustEigenvalues K hK) := by
  simpa [trustEigenbasis,trustEigenvalues,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def] using
    hK.star_mul_self_mul_eq_diagonal

theorem trustEigenbasis_reconstruction (K : T3) (hK : K.IsHermitian) :
    K=trustEigenbasis K hK*Matrix.diagonal (trustEigenvalues K hK)*
      (trustEigenbasis K hK).transpose := by
  simpa [trustEigenbasis,trustEigenvalues,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def] using hK.spectral_theorem

theorem trustEigenbasis_norm (K : T3) (hK : K.IsHermitian) (x : V3) :
    vSq (tVec (trustEigenbasis K hK) x)=vSq x :=
  trust_orthogonal_norm _ (trustEigenbasis_left K hK) x

theorem trustEigenbasis_transpose_norm (K : T3) (hK : K.IsHermitian) (x : V3) :
    vSq (tVec (trustEigenbasis K hK).transpose x)=vSq x := by
  apply trust_orthogonal_norm
  rw [Matrix.transpose_transpose,trustEigenbasis_right]

theorem trustEigenbasis_inverse_left (K : T3) (hK : K.IsHermitian) (x : V3) :
    tVec (trustEigenbasis K hK).transpose (tVec (trustEigenbasis K hK) x)=x := by
  rw [trust_tVec_mul,trustEigenbasis_left,trust_tVec_one]

theorem trustEigenbasis_inverse_right (K : T3) (hK : K.IsHermitian) (x : V3) :
    tVec (trustEigenbasis K hK) (tVec (trustEigenbasis K hK).transpose x)=x := by
  rw [trust_tVec_mul,trustEigenbasis_right,trust_tVec_one]

theorem trust_diagonal_objective (τ : ℝ) (d h y : V3) :
    trustQuadratic τ h (Matrix.diagonal d) y=trustDiagObjective τ d h y := by
  simp [trustQuadratic,trustDiagObjective,vDot,tVec,Matrix.diagonal_apply,Fin.sum_univ_three]
  ring

/-- The generic matrix objective is exactly the diagonal objective in its
actual orthonormal eigenbasis. -/
theorem trust_quadratic_eigenbasis (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (y : V3) :
    trustQuadratic τ k K (tVec (trustEigenbasis K hK) y)=
      trustDiagObjective τ (trustEigenvalues K hK) (trustEigenLinear K hK k) y := by
  rw [← trust_diagonal_objective]
  have hlin : vDot k (tVec (trustEigenbasis K hK) y)=
      vDot (trustEigenLinear K hK k) y := trust_vDot_right_transform _ _ _
  have hquad : vDot (tVec (trustEigenbasis K hK) y)
      (tVec K (tVec (trustEigenbasis K hK) y))=
      vDot y (tVec (Matrix.diagonal (trustEigenvalues K hK)) y) := by
    rw [trust_vDot_left_transform (trustEigenbasis K hK) y,
      trust_tVec_mul,trust_tVec_mul,trustEigenbasis_diagonal]
  unfold trustQuadratic
  rw [hlin,hquad]

theorem trust_quadratic_original_coordinates (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (x : V3) :
    trustQuadratic τ k K x=
      trustDiagObjective τ (trustEigenvalues K hK) (trustEigenLinear K hK k)
        (tVec (trustEigenbasis K hK).transpose x) := by
  conv_lhs => rw [← trustEigenbasis_inverse_right K hK x]
  exact trust_quadratic_eigenbasis τ k K hK _

def trustShiftMatrix (K : T3) (l : ℝ) : T3 := K+l • (1 : T3)

theorem trust_shift_objective (τ : ℝ) (k : V3) (K : T3) (l : ℝ) (x : V3) :
    trustQuadratic τ k (trustShiftMatrix K l) x=
      trustQuadratic τ k K x-l*vSq x := by
  simp [trustQuadratic,trustShiftMatrix,vDot,tVec,vSq,Matrix.one_apply,
    Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three]
  ring

theorem trustEigenbasis_shift (K : T3) (hK : K.IsHermitian) (l : ℝ) :
    trustShiftMatrix K l=trustEigenbasis K hK*
      Matrix.diagonal (fun i => trustEigenvalues K hK i+l)*
        (trustEigenbasis K hK).transpose := by
  have hd : Matrix.diagonal (fun i => trustEigenvalues K hK i+l)=
      Matrix.diagonal (trustEigenvalues K hK)+l • (1 : T3) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  rw [hd,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,
    trustEigenbasis_right,← trustEigenbasis_reconstruction]
  rfl

theorem trustEigenbasis_shift_psd (K : T3) (hK : K.IsHermitian) (l : ℝ)
    (hl : ∀ i, 0 ≤ trustEigenvalues K hK i+l) :
    (trustShiftMatrix K l).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => trustEigenvalues K hK i+l)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr hl
  have hu := hd.mul_mul_conjTranspose_same (trustEigenbasis K hK)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,← trustEigenbasis_shift] at hu
  exact hu

theorem trustEigenbasis_shift_equation (k : V3) (K : T3) (hK : K.IsHermitian)
    (p : V3) (l : ℝ)
    (hp : ∀ i, (trustEigenvalues K hK i+l)*p i=trustEigenLinear K hK k i) :
    tVec (trustShiftMatrix K l) (tVec (trustEigenbasis K hK) p)=k := by
  let U := trustEigenbasis K hK
  let D : T3 := Matrix.diagonal (fun i => trustEigenvalues K hK i+l)
  have hDp : tVec D p=trustEigenLinear K hK k := by
    funext i
    simpa [D,tVec,Matrix.diagonal_apply] using hp i
  calc
    tVec (trustShiftMatrix K l) (tVec U p)=
        tVec U (tVec D (tVec U.transpose (tVec U p))) := by
      rw [trustEigenbasis_shift]
      simp only [trust_tVec_mul,Matrix.mul_assoc]
      rfl
    _ = tVec U (tVec D p) := by rw [trustEigenbasis_inverse_left]
    _ = tVec U (trustEigenLinear K hK k) := by rw [hDp]
    _ = k := trustEigenbasis_inverse_right K hK k

end Milne
