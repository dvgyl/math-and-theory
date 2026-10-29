module
public import CumulantAlgebra
public import ImplicitLocal
public import PolynomialBranch

@[expose] public section

/-!
Identification of the explicit characteristic coefficients with the
derivatives of the constructed local smooth root. This avoids treating
the coefficient formulas as an unproved definition of root derivatives.
-/

open Filter
open scoped Topology

namespace UnicyclicCumulant

noncomputable section

theorem first_swap (a1 U V : ℝ) : first a1 V U = -first a1 U V := by
  dsimp [first]
  ring

theorem second_swap (a1 a2 U V : ℝ) :
    second a1 a2 V U = second a1 a2 U V := by
  dsimp [second]
  rw [first_swap]
  ring

theorem third_swap (a1 a2 a3 U V : ℝ) :
    third a1 a2 a3 V U = -third a1 a2 a3 U V := by
  dsimp [third]
  rw [first_swap,second_swap]
  ring

theorem skewness_swap (a1 a2 a3 U V : ℝ) :
    third a1 a2 a3 V U / first a1 V U =
      third a1 a2 a3 U V / first a1 U V := by
  rw [third_swap,first_swap]
  simp

theorem first_second_unique
    (a1 a2 U V C1 C2 : ℝ) (ha1 : a1 ≠ 0)
    (h1 : a1*C1 = U-V)
    (h2 : a1*C2+2*a2*C1^2 = U+V) :
    C1 = first a1 U V ∧ C2 = second a1 a2 U V := by
  have he1 := first_equation a1 U V ha1
  have he2 := second_equation a1 a2 U V ha1
  have hc1 : C1 = first a1 U V := mul_left_cancel₀ ha1 (h1.trans he1.symm)
  rw [hc1] at h2
  have hc2 : a1*C2 = a1*second a1 a2 U V := by linarith only [h2,he2]
  exact ⟨hc1,mul_left_cancel₀ ha1 hc2⟩

theorem first_three_unique
    (a1 a2 a3 U V C1 C2 C3 : ℝ) (ha1 : a1 ≠ 0)
    (h1 : a1*C1 = U-V)
    (h2 : a1*C2+2*a2*C1^2 = U+V)
    (h3 : a1*C3+6*a2*C1*C2+6*a3*C1^3 = U-V) :
    C1 = first a1 U V ∧ C2 = second a1 a2 U V ∧
      C3 = third a1 a2 a3 U V := by
  obtain ⟨hc1,hc2⟩ := first_second_unique a1 a2 U V C1 C2 ha1 h1 h2
  rw [hc1,hc2] at h3
  have he3 := third_equation a1 a2 a3 U V ha1
  have hc3 : a1*C3 = a1*third a1 a2 a3 U V := by linarith only [h3,he3]
  exact ⟨hc1,hc2,mul_left_cancel₀ ha1 hc3⟩

theorem local_branch_derivatives
    (P : Polynomial ℝ) (U V : ℝ) (f : ℝ → ℝ)
    (hP1 : P.coeff 1 ≠ 0) (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0 = 0)
    (hroot : ∀ᶠ x in 𝓝 (0 : ℝ),
      P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1)) :
    deriv f 0 = first (P.coeff 1) U V ∧
    deriv (deriv f) 0 = second (P.coeff 1) (P.coeff 2) U V ∧
    deriv (deriv (deriv f)) 0 = third (P.coeff 1) (P.coeff 2) (P.coeff 3) U V := by
  obtain ⟨h1,h2,h3⟩ := UnicyclicImplicit.implicit_cumulant_equations_local
    P U V f hf hf0 hroot
  exact first_three_unique (P.coeff 1) (P.coeff 2) (P.coeff 3) U V
    (deriv f 0) (deriv (deriv f) 0) (deriv (deriv (deriv f)) 0)
    hP1 h1 h2 h3

theorem exists_local_branch_with_explicit_derivatives
    (P : Polynomial ℝ) (U V : ℝ)
    (hP0 : P.eval 0 = 0) (hP1 : P.coeff 1 ≠ 0) :
    ∃ f : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ f 0 = 0 ∧
      (∀ᶠ x in 𝓝 (0 : ℝ),
        P.eval (f x) = U*(Real.exp x-1)+V*(Real.exp (-x)-1)) ∧
      deriv f 0 = first (P.coeff 1) U V ∧
      deriv (deriv f) 0 = second (P.coeff 1) (P.coeff 2) U V ∧
      deriv (deriv (deriv f)) 0 = third (P.coeff 1) (P.coeff 2) (P.coeff 3) U V := by
  obtain ⟨f,hf,hf0,hroot⟩ :=
    UnicyclicImplicit.exists_local_winding_branch P U V hP0 hP1
  exact ⟨f,hf,hf0,hroot,local_branch_derivatives P U V f hP1 hf hf0 hroot⟩

#print axioms first_second_unique
#print axioms first_three_unique
#print axioms skewness_swap
#print axioms local_branch_derivatives
#print axioms exists_local_branch_with_explicit_derivatives

end
end UnicyclicCumulant
