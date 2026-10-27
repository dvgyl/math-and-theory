module

public import MathAndTheory.Mathematics.Gyires.OneSuccess
public import MathAndTheory.Mathematics.Gyires.ExceptionalScalar

@[expose] public section

open scoped BigOperators
open Finset Polynomial
open MathAndTheory.Gyires.Bernoulli

namespace MathAndTheory.Gyires.Exceptional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def specialParameters (a b : ℝ) (e : ι) : ι → ℝ := fun i => if i = e then a else b

lemma oneSuccess_eq_derivative_eval_zero (u : ι → ℝ) :
    oneSuccess u = (derivative (generating u)).eval 0 := by
  rw [oneSuccess_eq_probability, ← generating_coeff, ← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

lemma generating_specialParameters (a b : ℝ) (e : ι) (k : ℕ)
    (hcard : Fintype.card ι = k+2) :
    generating (specialParameters a b e) =
      (C (1-a)+C a*X) * (C (1-b)+C b*X)^(k+1) := by
  unfold generating
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  have he : (∏ i ∈ Finset.univ.erase e,
      (C (1-specialParameters a b e i)+C (specialParameters a b e i)*X)) =
      ∏ _ ∈ Finset.univ.erase e, (C (1-b)+C b*X : Polynomial ℝ) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [specialParameters, (Finset.mem_erase.mp hi).1]
  rw [he]
  simp [specialParameters, hcard]

lemma oneSuccess_specialParameters (a b : ℝ) (e : ι) (k : ℕ)
    (hcard : Fintype.card ι = k+2) :
    oneSuccess (specialParameters a b e) =
      (1-b)^k * (a*(1-b)+((k : ℝ)+1)*b*(1-a)) := by
  rw [oneSuccess_eq_derivative_eval_zero, generating_specialParameters a b e k hcard]
  simp [derivative_mul, derivative_pow_succ, eval_mul, eval_add, eval_pow]
  ring

lemma oneSuccess_reference (k : ℕ) (hcard : Fintype.card ι = k+2) :
    oneSuccess (fun _ : ι => 1/(Fintype.card ι : ℝ)) =
      (((k : ℝ)+1)/((k : ℝ)+2))^(k+1) := by
  rw [oneSuccess_const, hcard]
  push_cast
  have hn : (0 : ℝ) < (k : ℝ)+2 := by positivity
  have hs : 1-1/((k : ℝ)+2) = ((k : ℝ)+1)/((k : ℝ)+2) := by field_simp; ring
  rw [hs]
  have hm : ((k : ℝ)+2)*(1/((k : ℝ)+2)) = 1 := by field_simp
  rw [hm, one_mul]

lemma special_reference_eq_scalarR (a : ℝ) (e : ι) (k : ℕ)
    (hcard : Fintype.card ι = k+2) :
    oneSuccess (specialParameters a ((1-a)/((k : ℝ)+1)) e) *
      (((k : ℝ)+1)/((k : ℝ)+2))^(k+1) = scalarR k a := by
  have hm : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have hn : (0 : ℝ) < (k : ℝ)+2 := by positivity
  rw [oneSuccess_specialParameters a _ e k hcard]
  have h1 : 1-(1-a)/((k : ℝ)+1) = ((k : ℝ)+a)/((k : ℝ)+1) := by field_simp; ring
  have h2 : a*(((k : ℝ)+a)/((k : ℝ)+1)) +
      ((k : ℝ)+1)*((1-a)/((k : ℝ)+1))*(1-a) = scalarKernel k a / ((k : ℝ)+1) := by
    unfold scalarKernel
    field_simp
    ring
  rw [h1, h2]
  unfold scalarR
  rw [div_pow, div_pow]
  simp only [pow_succ]
  field_simp [hm.ne', hn.ne', pow_ne_zero k hm.ne', pow_ne_zero k hn.ne']


end MathAndTheory.Gyires.Exceptional
