module
public import TwoStateSkewness
public import BranchCumulants
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
The actual counted-channel tilted determinant for the two-state ring.
Two parallel reaction channels must remain distinguished: the counting
factor is placed only on u0 and v0, not on an entire combined matrix entry.
This supplies the small-size boundary case of the winding theorem.
-/

open Filter Polynomial
open scoped Topology

namespace UnicyclicTwoState

noncomputable section

open UnicyclicCumulant UnicyclicImplicit

def twoStateMatrix (u0 u1 v0 v1 s z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z+u0+v1, -(u1+v0*Real.exp (-s));
     -(u0*Real.exp s+v1), z+u1+v0]

def quadraticRatePolynomial (u0 u1 v0 v1 : ℝ) : Polynomial ℝ :=
  X^2+C (u0+u1+v0+v1)*X

theorem twoState_characteristic_formula (u0 u1 v0 v1 s z : ℝ) :
    (twoStateMatrix u0 u1 v0 v1 s z).det =
      (quadraticRatePolynomial u0 u1 v0 v1).eval z -
        ((u0*u1)*(Real.exp s-1)+(v0*v1)*(Real.exp (-s)-1)) := by
  simp only [twoStateMatrix,Matrix.det_fin_two_of,
    quadraticRatePolynomial,Polynomial.eval_add,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero s]
  ring

theorem quadraticRatePolynomial_coefficients (u0 u1 v0 v1 : ℝ) :
    (quadraticRatePolynomial u0 u1 v0 v1).eval 0=0 ∧
    (quadraticRatePolynomial u0 u1 v0 v1).coeff 1=u0+u1+v0+v1 ∧
    (quadraticRatePolynomial u0 u1 v0 v1).coeff 2=1 ∧
    (quadraticRatePolynomial u0 u1 v0 v1).coeff 3=0 := by
  norm_num [quadraticRatePolynomial,Polynomial.coeff_add,
    Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X]

theorem two_state_winding_interval
    (u0 u1 v0 v1 : ℝ) (hu0 : 0<u0) (hu1 : 0<u1)
    (hv0 : 0<v0) (hv1 : 0<v1) (hUV : u0*u1 ≠ v0*v1)
    (f : ℝ → ℝ) (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hroot : ∀ᶠ s in 𝓝 (0 : ℝ), (twoStateMatrix u0 u1 v0 v1 s (f s)).det=0) :
    deriv f 0 ≠ 0 ∧
      (1/4 : ℝ) ≤ deriv (deriv (deriv f)) 0 / deriv f 0 ∧
      deriv (deriv (deriv f)) 0 / deriv f 0 ≤ 1 := by
  have ha : 0<u0+u1+v0+v1 := by positivity
  obtain ⟨hp0,hp1,hp2,hp3⟩ := quadraticRatePolynomial_coefficients u0 u1 v0 v1
  have hp1ne : (quadraticRatePolynomial u0 u1 v0 v1).coeff 1≠0 := by
    rw [hp1]
    exact ne_of_gt ha
  have heq : ∀ᶠ s in 𝓝 (0 : ℝ),
      (quadraticRatePolynomial u0 u1 v0 v1).eval (f s) =
        (u0*u1)*(Real.exp s-1)+(v0*v1)*(Real.exp (-s)-1) := by
    filter_upwards [hroot] with s hs
    rw [twoState_characteristic_formula] at hs
    exact sub_eq_zero.mp hs
  obtain ⟨h1,h2,h3⟩ := local_branch_derivatives
    (quadraticRatePolynomial u0 u1 v0 v1) (u0*u1) (v0*v1)
    f hp1ne hf hf0 heq
  simp only [hp1,hp2,hp3] at h1 h2 h3
  rw [h1,h3]
  refine ⟨div_ne_zero (sub_ne_zero.mpr hUV) (ne_of_gt ha), ?_⟩
  exact two_state_coefficient_skewness_interval u0 u1 v0 v1 hu0 hu1 hv0 hv1 hUV

theorem exists_two_state_winding_branch_and_interval
    (u0 u1 v0 v1 : ℝ) (hu0 : 0<u0) (hu1 : 0<u1)
    (hv0 : 0<v0) (hv1 : 0<v1) (hUV : u0*u1 ≠ v0*v1) :
    ∃ f : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ f 0=0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), (twoStateMatrix u0 u1 v0 v1 s (f s)).det=0) ∧
      deriv f 0 ≠ 0 ∧
      (1/4 : ℝ) ≤ deriv (deriv (deriv f)) 0 / deriv f 0 ∧
      deriv (deriv (deriv f)) 0 / deriv f 0 ≤ 1 := by
  have ha : 0<u0+u1+v0+v1 := by positivity
  obtain ⟨hp0,hp1,hp2,hp3⟩ := quadraticRatePolynomial_coefficients u0 u1 v0 v1
  have hp1ne : (quadraticRatePolynomial u0 u1 v0 v1).coeff 1≠0 := by
    rw [hp1]
    exact ne_of_gt ha
  obtain ⟨f,hf,hf0,hroot⟩ := exists_local_winding_branch
    (quadraticRatePolynomial u0 u1 v0 v1) (u0*u1) (v0*v1) hp0 hp1ne
  have hz : ∀ᶠ s in 𝓝 (0 : ℝ), (twoStateMatrix u0 u1 v0 v1 s (f s)).det=0 := by
    filter_upwards [hroot] with s hs
    rw [twoState_characteristic_formula,hs,sub_self]
  exact ⟨f,hf,hf0,hz,two_state_winding_interval u0 u1 v0 v1 hu0 hu1 hv0 hv1 hUV
    f hf hf0 hz⟩

#print axioms twoState_characteristic_formula
#print axioms two_state_winding_interval
#print axioms exists_two_state_winding_branch_and_interval

end
end UnicyclicTwoState
