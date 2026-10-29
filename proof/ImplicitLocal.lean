module
public import ImplicitCumulants
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Local version of the implicit characteristic-equation differentiation.
Only a C³ germ and the characteristic equation near zero are required.
This proves the derivative equations; it does not construct an eigenbranch.
-/

open Filter
open scoped Topology

namespace UnicyclicImplicit

noncomputable section

theorem implicit_cumulant_equations_of_local_jets
    (P : Polynomial ℝ) (U V : ℝ) (f f1 f2 f3 : ℝ → ℝ)
    (hf1 : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f (f1 x) x)
    (hf2 : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f1 (f2 x) x)
    (hf3 : HasDerivAt f2 (f3 0) 0)
    (hf0 : f 0 = 0)
    (hroot : ∀ᶠ x in 𝓝 (0 : ℝ),
      P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1)) :
    P.coeff 1 * f1 0 = U-V ∧
    P.coeff 1 * f2 0 + 2*P.coeff 2*(f1 0)^2 = U+V ∧
    P.coeff 1 * f3 0 + 6*P.coeff 2*f1 0*f2 0 +
      6*P.coeff 3*(f1 0)^3 = U-V := by
  have hfirst : ∀ᶠ x in 𝓝 (0 : ℝ),
      P.derivative.eval (f x) * f1 x = U*Real.exp x - V*Real.exp (-x) := by
    filter_upwards [hroot.eventually_nhds, hf1] with x hxroot hxf1
    have hleft := (P.hasDerivAt (f x)).comp x hxf1
    have hright := (((Real.hasDerivAt_exp x).sub_const 1).const_mul U).add
      (((hasDerivAt_exp_neg x).sub_const 1).const_mul V)
    simp only [Function.comp_def] at hleft
    have heq := (hleft.congr_of_eventuallyEq
      (hxroot.mono (fun _ h => h.symm))).unique hright
    nlinarith only [heq]
  have hsecond : ∀ᶠ x in 𝓝 (0 : ℝ),
      P.derivative.eval (f x)*f2 x + P.derivative.derivative.eval (f x)*(f1 x)^2 =
      U*Real.exp x + V*Real.exp (-x) := by
    filter_upwards [hfirst.eventually_nhds, hf1, hf2] with x hxfirst hxf1 hxf2
    have hleft := ((P.derivative.hasDerivAt (f x)).comp x hxf1).mul hxf2
    have hright := ((Real.hasDerivAt_exp x).const_mul U).sub
      ((hasDerivAt_exp_neg x).const_mul V)
    simp only [Function.comp_def] at hleft
    have heq := (hleft.congr_of_eventuallyEq
      (hxfirst.mono (fun _ h => h.symm))).unique hright
    nlinarith only [heq]
  have hthird :
      P.derivative.eval (f 0)*f3 0 +
      3*P.derivative.derivative.eval (f 0)*f1 0*f2 0 +
      P.derivative.derivative.derivative.eval (f 0)*(f1 0)^3 =
      U*Real.exp 0 - V*Real.exp (-0) := by
    have hleft := (((P.derivative.hasDerivAt (f 0)).comp 0 hf1.self_of_nhds).mul hf3).add
      (((P.derivative.derivative.hasDerivAt (f 0)).comp 0 hf1.self_of_nhds).mul
        (hf2.self_of_nhds.pow 2))
    have hright := ((Real.hasDerivAt_exp 0).const_mul U).add
      ((hasDerivAt_exp_neg 0).const_mul V)
    simp only [Function.comp_def] at hleft
    have heq := (hleft.congr_of_eventuallyEq
      (hsecond.mono (fun _ h => h.symm))).unique hright
    norm_num at heq ⊢
    nlinarith only [heq]
  have h1 := hfirst.self_of_nhds
  have h2 := hsecond.self_of_nhds
  have h3 := hthird
  norm_num [hf0, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative] at h1 h2 h3
  refine ⟨h1, ?_, ?_⟩
  · nlinarith only [h2]
  · nlinarith only [h3]

theorem implicit_cumulant_equations_local
    (P : Polynomial ℝ) (U V : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0 = 0)
    (hroot : ∀ᶠ x in 𝓝 (0 : ℝ),
      P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1)) :
    P.coeff 1 * deriv f 0 = U-V ∧
    P.coeff 1 * deriv (deriv f) 0 + 2*P.coeff 2*(deriv f 0)^2 = U+V ∧
    P.coeff 1 * deriv (deriv (deriv f)) 0 +
      6*P.coeff 2*deriv f 0*deriv (deriv f) 0 +
      6*P.coeff 3*(deriv f 0)^3 = U-V := by
  have hf' : ContDiffAt ℝ 2 (deriv f) 0 := by
    exact hf.derivWithin (by norm_num)
  have hf'' : ContDiffAt ℝ 1 (deriv (deriv f)) 0 := by
    exact hf'.derivWithin (by norm_num)
  apply implicit_cumulant_equations_of_local_jets P U V f
    (deriv f) (deriv (deriv f)) (deriv (deriv (deriv f)))
  · filter_upwards [hf.eventually (by norm_num)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasDerivAt
  · filter_upwards [hf'.eventually (by norm_num)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasDerivAt
  · exact (hf''.differentiableAt (by norm_num)).hasDerivAt
  · exact hf0
  · exact hroot

#print axioms implicit_cumulant_equations_of_local_jets
#print axioms implicit_cumulant_equations_local

end
end UnicyclicImplicit
