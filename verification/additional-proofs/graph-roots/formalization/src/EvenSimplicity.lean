import EvenRoots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision

noncomputable section
namespace SquareFlowerCompletion.RealCompanion

def complexA (z : ℂ) : ℂ := z^2-3*z+3
def complexF (n : ℕ) (z : ℂ) : ℂ :=
  (2-complexA z)^n-z*(complexA z)^n-1
def complexFderiv (n : ℕ) (z : ℂ) : ℂ :=
  (n:ℂ)*(3-2*z)*((2-complexA z)^(n-1)+z*(complexA z)^(n-1))-
    (complexA z)^n

theorem complexF_ofReal (n : ℕ) (t : ℝ) : complexF n (t:ℂ) = (F n t:ℂ) := by
  simp [complexF,complexA,F,a]

theorem complexFderiv_ofReal (n : ℕ) (t : ℝ) :
    complexFderiv n (t:ℂ) = (Fderiv n t:ℂ) := by
  simp [complexFderiv,complexA,Fderiv,a]

theorem hasDerivAt_complexF (n : ℕ) (z : ℂ) :
    HasDerivAt (complexF n) (complexFderiv n z) z := by
  have ha : HasDerivAt complexA (2*z-3) z := by
    convert (((hasDerivAt_id z).pow 2).sub ((hasDerivAt_id z).const_mul 3)).add_const 3 using 1
    simp [complexA]
  have hb : HasDerivAt (fun w => 2-complexA w) (3-2*z) z := by
    convert ha.const_sub 2 using 1
    ring
  convert (((hb.pow n).sub ((hasDerivAt_id z).mul (ha.pow n))).sub_const 1) using 1
  dsimp [complexF,complexFderiv]
  ring

theorem eval_negative_eq_complexF {n : ℕ} (he : Even n) (z : ℂ) :
    (Counting.complexDominationPolynomial n).eval (-z) = (-z)^n*complexF n z := by
  rw [Counting.eval_complexDominationPolynomial]
  have ha : (-z)^2+3*(-z)+3 = complexA z := by dsimp [complexA]; ring
  have hb : (-z)^2+3*(-z)+1 = -(2-complexA z) := by dsimp [complexA]; ring
  have hp : (-(2-complexA z))^n = (2-complexA z)^n := he.neg_pow _
  rw [ha,hb,hp]
  dsimp [complexF]
  ring

theorem graph_derivative_ne_zero_of_F {n : ℕ} (he : Even n) {t : ℝ}
    (ht : t ≠ 0) (hF : F n t = 0) (hd : Fderiv n t ≠ 0) :
    (Counting.complexDominationPolynomial n).derivative.eval (-(t:ℂ)) ≠ 0 := by
  let p := Counting.complexDominationPolynomial n
  have hFc : complexF n (t:ℂ) = 0 := by rw [complexF_ofReal,hF]; rfl
  have hleft : HasDerivAt (fun z : ℂ => p.eval (-z))
      (-p.derivative.eval (-(t:ℂ))) (t:ℂ) := by
    simpa using (p.hasDerivAt (-(t:ℂ))).comp (t:ℂ) (hasDerivAt_id (t:ℂ)).neg
  have hright : HasDerivAt (fun z : ℂ => (-z)^n*complexF n z)
      ((-(t:ℂ))^n*complexFderiv n (t:ℂ)) (t:ℂ) := by
    simpa only [hFc,mul_zero,zero_add] using
      (((hasDerivAt_id (t:ℂ)).neg.pow n).mul (hasDerivAt_complexF n (t:ℂ)))
  have hfun : (fun z : ℂ => p.eval (-z)) = (fun z : ℂ => (-z)^n*complexF n z) :=
    funext (eval_negative_eq_complexF he)
  rw [hfun] at hleft
  have heq := hleft.unique hright
  have htc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hdc : complexFderiv n (t:ℂ) ≠ 0 := by
    rw [complexFderiv_ofReal]
    exact Complex.ofReal_ne_zero.mpr hd
  intro hz
  have hm := mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr htc)) hdc
  apply hm
  rw [← heq]
  change -((Counting.complexDominationPolynomial n).derivative.eval (-(t:ℂ))) = 0
  rw [hz,neg_zero]

theorem even_nonzero_real_root_derivative_ne_zero {n : ℕ} (he : Even n) (hn : 4 ≤ n)
    {x : ℝ} (hx : x ≠ 0)
    (hroot : (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0) :
    (Counting.complexDominationPolynomial n).derivative.eval (x:ℂ) ≠ 0 := by
  obtain ⟨l,hl,r,hr,hFl,hFr,hclass,hdl,hdr⟩ := even_order_real_root_classification he hn
  rcases (hclass x).mp hroot with hzero | rfl | rfl
  · exact (hx hzero).elim
  · simpa only [Complex.ofReal_neg] using
      graph_derivative_ne_zero_of_F he (by linarith [hl.1] : l ≠ 0) hFl hdl.ne'
  · simpa only [Complex.ofReal_neg] using
      graph_derivative_ne_zero_of_F he (by linarith [hr.1] : r ≠ 0) hFr hdr.ne

theorem even_nonzero_real_root_multiplicity_one {n : ℕ} (he : Even n) (hn : 4 ≤ n)
    {x : ℝ} (hx : x ≠ 0)
    (hroot : (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0) :
    (Counting.complexDominationPolynomial n).rootMultiplicity (x:ℂ) = 1 := by
  have hp := Extremal.graphPolynomial_ne_zero n
  have hpos : 0 < (Counting.complexDominationPolynomial n).rootMultiplicity (x:ℂ) :=
    (Polynomial.rootMultiplicity_pos hp).mpr hroot
  have hderiv := even_nonzero_real_root_derivative_ne_zero he hn hx hroot
  have hle : (Counting.complexDominationPolynomial n).rootMultiplicity (x:ℂ) ≤ 1 := by
    by_contra h
    have hgt : 1 < (Counting.complexDominationPolynomial n).rootMultiplicity (x:ℂ) := by omega
    have hdroot := ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mp hgt).2
    exact hderiv hdroot
  omega

#print axioms complexF_ofReal
#print axioms complexFderiv_ofReal
#print axioms hasDerivAt_complexF
#print axioms eval_negative_eq_complexF
#print axioms graph_derivative_ne_zero_of_F
#print axioms even_nonzero_real_root_derivative_ne_zero
#print axioms even_nonzero_real_root_multiplicity_one
end SquareFlowerCompletion.RealCompanion
