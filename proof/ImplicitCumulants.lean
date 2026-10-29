module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Implicit differentiation of a unicyclic characteristic equation.

This module proves the first three coefficient/cumulant equations for any
C^3 real branch satisfying the displayed characteristic equation. It does
not assume those three equations. Identifying the characteristic equation
with the transition-rate matrix remains a separate matrix theorem.
-/

namespace UnicyclicImplicit

noncomputable section

theorem hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa only [Function.comp_def, mul_neg_one] using
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg

theorem implicit_cumulant_equations_of_jets
    (P : Polynomial ℝ) (U V : ℝ) (f f1 f2 f3 : ℝ → ℝ)
    (hf1 : ∀ x, HasDerivAt f (f1 x) x)
    (hf2 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hf3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hf0 : f 0 = 0)
    (hroot : ∀ x, P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1)) :
    P.coeff 1 * f1 0 = U-V ∧
    P.coeff 1 * f2 0 + 2*P.coeff 2*(f1 0)^2 = U+V ∧
    P.coeff 1 * f3 0 + 6*P.coeff 2*f1 0*f2 0 +
      6*P.coeff 3*(f1 0)^3 = U-V := by
  have hrootfun : (fun x => P.eval (f x)) =
      (fun x => U*(Real.exp x-1)+V*(Real.exp (-x)-1)) := funext hroot
  have hfirst : ∀ x, P.derivative.eval (f x) * f1 x =
      U*Real.exp x - V*Real.exp (-x) := by
    intro x
    have hleft := (P.hasDerivAt (f x)).comp x (hf1 x)
    have hright := (((Real.hasDerivAt_exp x).sub_const 1).const_mul U).add
      (((hasDerivAt_exp_neg x).sub_const 1).const_mul V)
    simp only [Function.comp_def] at hleft
    rw [hrootfun] at hleft
    have heq := hleft.unique hright
    nlinarith only [heq]
  have hfirstfun : (fun x => P.derivative.eval (f x) * f1 x) =
      (fun x => U*Real.exp x - V*Real.exp (-x)) := funext hfirst
  have hsecond : ∀ x,
      P.derivative.eval (f x)*f2 x + P.derivative.derivative.eval (f x)*(f1 x)^2 =
      U*Real.exp x + V*Real.exp (-x) := by
    intro x
    have hleft := ((P.derivative.hasDerivAt (f x)).comp x (hf1 x)).mul (hf2 x)
    have hright := ((Real.hasDerivAt_exp x).const_mul U).sub
      ((hasDerivAt_exp_neg x).const_mul V)
    simp only [Function.comp_def] at hleft
    rw [hfirstfun] at hleft
    have heq := hleft.unique hright
    nlinarith only [heq]
  have hsecondfun : (fun x =>
      P.derivative.eval (f x)*f2 x + P.derivative.derivative.eval (f x)*(f1 x)^2) =
      (fun x => U*Real.exp x + V*Real.exp (-x)) := funext hsecond
  have hthird : ∀ x,
      P.derivative.eval (f x)*f3 x +
      3*P.derivative.derivative.eval (f x)*f1 x*f2 x +
      P.derivative.derivative.derivative.eval (f x)*(f1 x)^3 =
      U*Real.exp x - V*Real.exp (-x) := by
    intro x
    have hleft := (((P.derivative.hasDerivAt (f x)).comp x (hf1 x)).mul (hf3 x)).add
      (((P.derivative.derivative.hasDerivAt (f x)).comp x (hf1 x)).mul ((hf2 x).pow 2))
    have hright := ((Real.hasDerivAt_exp x).const_mul U).add
      ((hasDerivAt_exp_neg x).const_mul V)
    simp only [Function.comp_def] at hleft
    rw [hsecondfun] at hleft
    have heq := hleft.unique hright
    norm_num at heq
    nlinarith only [heq]
  have h1 := hfirst 0
  have h2 := hsecond 0
  have h3 := hthird 0
  norm_num [hf0, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · exact h1
  · nlinarith only [h2]
  · nlinarith only [h3]

theorem implicit_cumulant_equations
    (P : Polynomial ℝ) (U V : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 3 f) (hf0 : f 0 = 0)
    (hroot : ∀ x, P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1)) :
    P.coeff 1 * deriv f 0 = U-V ∧
    P.coeff 1 * deriv (deriv f) 0 + 2*P.coeff 2*(deriv f 0)^2 = U+V ∧
    P.coeff 1 * deriv (deriv (deriv f)) 0 +
      6*P.coeff 2*deriv f 0*deriv (deriv f) 0 +
      6*P.coeff 3*(deriv f 0)^3 = U-V := by
  have hf' : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have hf'' : ContDiff ℝ 1 (deriv (deriv f)) := (contDiff_succ_iff_deriv.mp hf').2.2
  apply implicit_cumulant_equations_of_jets P U V f
    (deriv f) (deriv (deriv f)) (deriv (deriv (deriv f)))
  · intro x
    exact (hf.differentiable (by norm_num) x).hasDerivAt
  · intro x
    exact (hf'.differentiable (by norm_num) x).hasDerivAt
  · intro x
    exact (hf''.differentiable (by norm_num) x).hasDerivAt
  · exact hf0
  · exact hroot

#print axioms implicit_cumulant_equations_of_jets
#print axioms implicit_cumulant_equations

end
end UnicyclicImplicit
