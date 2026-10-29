import BookOuterRoots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision

set_option maxHeartbeats 1000000
noncomputable section
open Polynomial Filter
open scoped Topology
namespace BookCompletion

theorem actual_polynomial_ne_zero (n : ℕ) : realPolynomial n≠0 := by
  intro hz
  have hp := eval_realPolynomial_positive n (x:=1) (by norm_num)
  simp only [hz,eval_zero,lt_self_iff_false] at hp

theorem actual_simple_of_normalized_derivative (n : ℕ) (hn : 1≤n) {t d : ℝ}
    (ht : 0<t) (hroot : (realPolynomial n).IsRoot (-t))
    (hd : HasDerivAt (normalized n) d t) (hdne : d≠0) :
    (realPolynomial n).rootMultiplicity (-t)=1 := by
  have htne : t≠0 := ne_of_gt ht
  have hnorm : normalized n t=0 := (real_root_iff_normalized n hn ht).1 hroot
  have hprod := (hasDerivAt_pow n t).mul hd
  have hprod' : HasDerivAt (fun s : ℝ => s^n*normalized n s) (t^n*d) t := by
    simpa only [hnorm,mul_zero,zero_add] using hprod
  have hnear : (fun s : ℝ => (realPolynomial n).eval (-s)) =ᶠ[𝓝 t]
      (fun s : ℝ => s^n*normalized n s) := by
    filter_upwards [eventually_ne_nhds htne] with s hs
    exact eval_negative_factor n hn hs
  have hactual : HasDerivAt (fun s : ℝ => (realPolynomial n).eval (-s)) (t^n*d) t :=
    hprod'.congr_of_eventuallyEq hnear
  have hpoly := ((realPolynomial n).hasDerivAt (-t)).comp t (hasDerivAt_neg t)
  have hval : -(realPolynomial n).derivative.eval (-t)=t^n*d := by
    simpa only [mul_neg_one] using hpoly.unique hactual
  have hderiv : ¬(realPolynomial n).derivative.IsRoot (-t) := by
    intro hh
    have hh0 : (realPolynomial n).derivative.eval (-t)=0 := hh
    rw [hh0,neg_zero] at hval
    exact mul_ne_zero (pow_ne_zero n htne) hdne hval.symm
  have hpne := actual_polynomial_ne_zero n
  have hpos := (rootMultiplicity_pos hpne).2 hroot
  have hnot : ¬1<(realPolynomial n).rootMultiplicity (-t) := by
    intro hm
    exact hderiv ((one_lt_rootMultiplicity_iff_isRoot hpne).1 hm).2
  omega

theorem outer_even_actual_simple (n : ℕ) (hn : 2≤n) (he : Even n) {t : ℝ}
    (ht : 2<t) (hroot : (realPolynomial n).IsRoot (-t)) :
    (realPolynomial n).rootMultiplicity (-t)=1 := by
  have htpos : 0<t := by linarith
  have hd := (outer_hasDerivAt n (ne_of_gt htpos)).sub_const 2
  have heq : normalized n = (fun s : ℝ => outerK n s-2) := by
    funext s
    exact normalized_even_outerK n he s
  have hnorm : HasDerivAt (normalized n) (outerDerivative n t) t := by
    rw [heq]
    exact hd
  exact actual_simple_of_normalized_derivative n (by omega) htpos hroot hnorm
    (ne_of_gt (outerDerivative_pos n ht))

theorem outer_even_complex_simple (n : ℕ) (hn : 2≤n) (he : Even n) {t : ℝ}
    (ht : 2<t) (hroot : (realPolynomial n).IsRoot (-t)) :
    (complexPolynomial n).rootMultiplicity ((-t:ℝ):ℂ)=1 := by
  have hreal := outer_even_actual_simple n hn he ht hroot
  have heq := Polynomial.eq_rootMultiplicity_map (p:=realPolynomial n)
    (f:=Complex.ofRealHom) Complex.ofReal_injective (-t)
  rw [map_realPolynomial] at heq
  exact heq.symm.trans hreal

#print axioms actual_polynomial_ne_zero
#print axioms actual_simple_of_normalized_derivative
#print axioms outer_even_actual_simple
#print axioms outer_even_complex_simple
end BookCompletion
