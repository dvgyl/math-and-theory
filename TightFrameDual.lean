module
public import NegativeDepolarizingEffects


@[expose] public section

/-! Rational four-dimensional dual certificates for the tight-frame witnesses.
All identities here are exact matrix identities; no eigenvalue formula is used. -/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace TightFrameDual
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000

abbrev F := Fin 4

def gram (r : ℝ) : Matrix F F ℂ := Matrix.diagonal ![(r:ℂ),1,1,r]
def signBase : Matrix F F ℂ := Matrix.diagonal ![1,0,0,-1]
def center : Matrix F F ℂ := Matrix.diagonal ![0,1,1,0]
def inputCorrection : Matrix F F ℂ := Matrix.diagonal ![0,1,-1,0]

def inputDifference (u : ℝ) : Matrix F F ℂ :=
  !![1, (u:ℂ), 0, 0;
     u, (u:ℂ)^2, 0, 0;
     0, 0, -(u:ℂ)^2, -u;
     0, 0, -u, -1]

def den (r t : ℝ) : ℝ := 1+r*t^2
def cosine (r t : ℝ) : ℝ := (1-r*t^2)/den r t

def correction (r t : ℝ) : Matrix F F ℂ :=
  !![((-2*t^2/den r t : ℝ):ℂ), ((-2*t/den r t : ℝ):ℂ), 0, 0;
     ((-2*t/den r t : ℝ):ℂ), (-(cosine r t):ℂ), 0, 0;
     0, 0, ((cosine r t):ℂ), ((2*t/den r t : ℝ):ℂ);
     0, 0, ((2*t/den r t : ℝ):ℂ), ((2*t^2/den r t : ℝ):ℂ)]

theorem den_pos (r t : ℝ) (hr : 0 ≤ r) : 0 < den r t := by
  unfold den
  positivity

theorem signBase_hermitian : signBase.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [signBase, _root_.IsSelfAdjoint]

theorem correction_hermitian (r t : ℝ) : (correction r t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [correction, Matrix.conjTranspose_apply, Complex.star_def]

theorem inputCorrection_hermitian : inputCorrection.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [inputCorrection, _root_.IsSelfAdjoint]

theorem correction_identity (r t : ℝ) (hr : 0 ≤ r) :
    signBase * correction r t + correction r t * signBase +
      correction r t * gram r * correction r t = center := by
  have hd : den r t ≠ 0 := (den_pos r t hr).ne'
  have hdc : ((den r t : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  ext i j
  simp only [Matrix.add_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [signBase, correction, gram, center, cosine,
      Fin.sum_univ_succ, Matrix.diagonal] <;>
    field_simp <;> simp only [den] <;> push_cast <;> ring

theorem inputCorrection_identity (r : ℝ) :
    signBase * inputCorrection + inputCorrection * signBase +
      inputCorrection * gram r * inputCorrection = center := by
  ext i j
  simp only [Matrix.add_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [signBase, inputCorrection, gram, center, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal]

theorem input_pairing (r u : ℝ) :
    (inputDifference u * gram r * signBase).trace.re +
      (inputCorrection * gram r * inputDifference u * gram r).trace.re =
        2*(r+u^2) := by
  have hpow (x : ℝ) : ((x:ℂ)^2).re=x^2 := by
    rw [←Complex.ofReal_pow,Complex.ofReal_re]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  norm_num [inputDifference, gram, signBase, inputCorrection, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal, Complex.mul_re,
    Complex.mul_im]
  simp only [hpow]
  ring

theorem output_pairing (r t u b s : ℝ) (hr : 0 ≤ r) :
    (correction r t *
      (b • (gram r * signBase) - s • (gram r * inputDifference u * gram r))).trace.re -
      s * (inputDifference u * gram r * signBase).trace.re =
        2*b*(cosine r t-1) - 2*s*cosine r t*(r-u^2) +
          8*s*r*t*u/den r t := by
  have hd : den r t ≠ 0 := (den_pos r t hr).ne'
  have hpow (x : ℝ) : ((x:ℂ)^2).re=x^2 := by
    rw [←Complex.ofReal_pow,Complex.ofReal_re]
  have h₂₃ : (2 : Fin 4) ≠ Fin.succ (2 : Fin 3) := by decide
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.sub_apply,Matrix.smul_apply]
  norm_num [correction, inputDifference, gram, signBase, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal,
    Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,h₂₃]
  simp only [hpow]
  unfold cosine
  field_simp
  unfold den
  ring

variable {S : Type} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- The only large-matrix square calculation reduces to a four-dimensional
Gram identity. The ambient reference dimension is arbitrary. -/
theorem corrected_square [DecidableEq S] (T : Matrix S S ℂ) (K : Matrix S F ℂ)
    (J G D E : Matrix F F ℂ) (hT : T.IsHermitian) (hJ : J.IsHermitian)
    (hTK : T*K=K*J) (hGram : Kᴴ*K=G)
    (hD : J*D+D*J+D*G*D=E) :
    (T+K*D*Kᴴ)*(T+K*D*Kᴴ) = T*T+K*E*Kᴴ := by
  have hKT : Kᴴ*T=J*Kᴴ := by
    have hh := congrArg Matrix.conjTranspose hTK
    simpa only [Matrix.conjTranspose_mul,hT.eq,hJ.eq] using hh
  have h₁ : T*(K*D*Kᴴ)=K*(J*D)*Kᴴ := by
    calc
      _ = (T*K)*D*Kᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTK]; simp only [Matrix.mul_assoc]
  have h₂ : (K*D*Kᴴ)*T=K*(D*J)*Kᴴ := by
    calc
      _ = K*D*(Kᴴ*T) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hKT]; simp only [Matrix.mul_assoc]
  have h₃ : (K*D*Kᴴ)*(K*D*Kᴴ)=K*(D*G*D)*Kᴴ := by
    calc
      _ = K*D*(Kᴴ*K)*D*Kᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hGram]; simp only [Matrix.mul_assoc]
  calc
    _ = T*T+K*(J*D+D*J+D*G*D)*Kᴴ := by
      simp only [Matrix.add_mul,Matrix.mul_add]
      rw [h₁,h₂,h₃]
      abel
    _ = _ := by rw [hD]

end
end TightFrameDual
