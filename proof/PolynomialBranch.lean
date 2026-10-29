module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Existence of a local C³ branch for a simple polynomial root.

This is an application of mathlib's proved inverse function theorem, with
the nonzero derivative discharged by the linear polynomial coefficient.
It constructs the scalar root germ, not a Perron eigenvector or the
long-time stochastic cumulant generating function.
-/

open Filter
open scoped Topology

namespace UnicyclicImplicit

noncomputable section

theorem polynomial_eval_contDiff (P : Polynomial ℝ) :
    ContDiff ℝ 3 (fun x : ℝ => P.eval x) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
    simpa using (contDiff_const (c := a)).mul (contDiff_id.pow n)

theorem exists_local_polynomial_branch
    (P : Polynomial ℝ) (g : ℝ → ℝ)
    (hP0 : P.eval 0 = 0) (hP1 : P.coeff 1 ≠ 0)
    (hg : ContDiffAt ℝ 3 g 0) (hg0 : g 0 = 0) :
    ∃ f : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ f 0 = 0 ∧
      ∀ᶠ x in 𝓝 (0 : ℝ), P.eval (f x) = g x := by
  have hPder : P.derivative.eval 0 ≠ 0 := by
    simpa [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] using hP1
  have hPd : ContDiffAt ℝ 3 (fun x : ℝ => P.eval x) 0 :=
    (polynomial_eval_contDiff P).contDiffAt
  have hPf := (P.hasDerivAt 0).hasFDerivAt_equiv hPder
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  let v : ℝ → ℝ := hPd.localInverse hPf hn
  have hv0 : v 0 = 0 := by
    simpa [v, hP0] using hPd.localInverse_apply_image hPf hn
  have hv : ContDiffAt ℝ 3 v 0 := by
    simpa [v, hP0] using hPd.to_localInverse hPf hn
  have hvr : ∀ᶠ y in 𝓝 (0 : ℝ), P.eval (v y) = y := by
    simpa [v, ContDiffAt.localInverse, hP0] using
      (hPd.hasStrictFDerivAt' hPf hn).eventually_right_inverse
  refine ⟨fun x => v (g x), ?_, ?_, ?_⟩
  · have hv' : ContDiffAt ℝ 3 v (g 0) := by simpa [hg0] using hv
    exact hv'.comp 0 hg
  · simpa [hg0] using hv0
  · have hgt : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa [hg0] using hg.continuousAt.tendsto
    exact hgt.eventually hvr

theorem exists_local_winding_branch
    (P : Polynomial ℝ) (U V : ℝ)
    (hP0 : P.eval 0 = 0) (hP1 : P.coeff 1 ≠ 0) :
    ∃ f : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ f 0 = 0 ∧
      ∀ᶠ x in 𝓝 (0 : ℝ),
        P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1) := by
  apply exists_local_polynomial_branch P
    (fun x => U*(Real.exp x-1)+V*(Real.exp (-x)-1)) hP0 hP1
  · exact ((contDiff_const.mul (Real.contDiff_exp.sub contDiff_const)).add
      (contDiff_const.mul
        ((Real.contDiff_exp.comp contDiff_id.neg).sub contDiff_const))).contDiffAt
  · simp

#print axioms exists_local_polynomial_branch
#print axioms exists_local_winding_branch

end
end UnicyclicImplicit
