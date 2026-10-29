module
public import ImplicitCumulants

@[expose] public section

/-!
The first two characteristic coefficient equations follow from a residual
that vanishes to second order at zero. An exact eigenvalue branch is not
required. This is designed to accept the determinant jet established from
the actual finite-state Poisson correctors.
-/

namespace UnicyclicImplicit

noncomputable section

def characteristicResidual (P : Polynomial ℝ) (U V : ℝ) (f : ℝ → ℝ)
    (x : ℝ) : ℝ :=
  P.eval (f x) - (U*(Real.exp x-1)+V*(Real.exp (-x)-1))

theorem cumulant_equations_of_zero_residual_jet
    (P : Polynomial ℝ) (U V : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0)
    (hres1 : deriv (characteristicResidual P U V f) 0 = 0)
    (hres2 : deriv (deriv (characteristicResidual P U V f)) 0 = 0) :
    P.coeff 1 * deriv f 0 = U-V ∧
    P.coeff 1 * deriv (deriv f) 0 + 2*P.coeff 2*(deriv f 0)^2 = U+V := by
  have hf' : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have hfirstfun : deriv (characteristicResidual P U V f) =
      (fun x => P.derivative.eval (f x)*deriv f x -
        (U*Real.exp x-V*Real.exp (-x))) := by
    funext x
    have hleft := (P.hasDerivAt (f x)).comp x
      (hf.differentiable (by norm_num) x).hasDerivAt
    have hright := (((Real.hasDerivAt_exp x).sub_const 1).const_mul U).add
      (((hasDerivAt_exp_neg x).sub_const 1).const_mul V)
    have hh := (hleft.sub hright).deriv
    simp only [Function.comp_def] at hh
    simpa only [characteristicResidual, mul_neg, sub_eq_add_neg,
      add_neg_cancel_right] using hh
  have h1 := hres1
  rw [hfirstfun] at h1
  have h2 := hres2
  rw [hfirstfun] at h2
  have hleft := ((P.derivative.hasDerivAt (f 0)).comp 0
      (hf.differentiable (by norm_num) 0).hasDerivAt).mul
        (hf'.differentiable (by norm_num) 0).hasDerivAt
  have hright := ((Real.hasDerivAt_exp 0).const_mul U).sub
      ((hasDerivAt_exp_neg 0).const_mul V)
  have hd := (hleft.sub hright).deriv
  simp only [Function.comp_def] at hd
  rw [hd] at h2
  norm_num [hf0, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative] at h1 h2
  constructor <;> nlinarith only [h1,h2]

def quadraticBranch (J C2 x : ℝ) : ℝ := J*x+C2*x^2/2

theorem quadraticBranch_deriv (J C2 x : ℝ) :
    HasDerivAt (quadraticBranch J C2) (J+C2*x) x := by
  convert ((hasDerivAt_id x).const_mul J).add
    ((((hasDerivAt_id x).pow 2).const_mul C2).div_const 2) using 1 ;
    simp only [quadraticBranch, id_eq, Nat.cast_ofNat] ; ring

theorem quadraticBranch_deriv_fun (J C2 : ℝ) :
    deriv (quadraticBranch J C2) = (fun x => J+C2*x) := by
  funext x
  exact (quadraticBranch_deriv J C2 x).deriv

theorem quadraticBranch_second_deriv_zero (J C2 : ℝ) :
    deriv (deriv (quadraticBranch J C2)) 0 = C2 := by
  rw [quadraticBranch_deriv_fun]
  simpa using (((hasDerivAt_id (0 : ℝ)).const_mul C2).const_add J).deriv

theorem quadraticBranch_contDiff (J C2 : ℝ) :
    ContDiff ℝ 2 (quadraticBranch J C2) := by
  exact ((contDiff_const.mul contDiff_id).add
    ((contDiff_const.mul (contDiff_id.pow 2)).div_const 2))

/-- This is the direct input/output interface for a determinant `ZeroJet2`. -/
theorem quadratic_coefficient_equations_of_zero_residual_jet
    (P : Polynomial ℝ) (U V J C2 : ℝ)
    (hres1 : deriv (characteristicResidual P U V (quadraticBranch J C2)) 0 = 0)
    (hres2 : deriv (deriv
      (characteristicResidual P U V (quadraticBranch J C2))) 0 = 0) :
    P.coeff 1*J = U-V ∧ P.coeff 1*C2+2*P.coeff 2*J^2 = U+V := by
  have h := cumulant_equations_of_zero_residual_jet P U V
    (quadraticBranch J C2) (quadraticBranch_contDiff J C2)
    (by simp [quadraticBranch]) hres1 hres2
  rw [quadraticBranch_second_deriv_zero] at h
  simpa only [quadraticBranch_deriv_fun,
    mul_zero, add_zero] using h

#print axioms cumulant_equations_of_zero_residual_jet
#print axioms quadratic_coefficient_equations_of_zero_residual_jet

end
end UnicyclicImplicit
