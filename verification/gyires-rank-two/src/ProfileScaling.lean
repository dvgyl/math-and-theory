module

public import CertificatePolynomials
public import ProfilePolynomial

@[expose] public section

open scoped BigOperators
open Polynomial Finset

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma elementary_scale (u : ι → ℝ) (s : ℝ) (k : ℕ) :
    elementary (fun i => s*u i) k = s^k*elementary u k := by
  unfold elementary
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hS).2]

omit [DecidableEq ι] in
lemma elementaryGenerating_scale (u : ι → ℝ) (s : ℝ) :
    elementaryGenerating (fun i => s*u i) = (elementaryGenerating u).comp (C s*X) := by
  unfold elementaryGenerating
  rw [Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.add_comp, Polynomial.one_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, map_mul]
  ring

namespace Certificate

noncomputable def clearedProfilePolynomial (n a m L R : ℕ) (U V : ℝ) : ℝ[X] :=
  (1+C ((m : ℝ)*(((n : ℝ)-L)*U+((n : ℝ)-R)*V))*X)^a *
    (1+C (((n : ℝ)*((L : ℝ)-a)-m*L)*U+((n : ℝ)*((R : ℝ)-a)-m*R)*V)*X)^m *
      (1+C (-(m : ℝ)*((L : ℝ)*U+R*V))*X)^(n-a-m)

theorem eval_profileForms (f : ℕ →* ℝ) (n a m L R : ℕ) :
    ((profileForms n a m L R).map (fun p => (1+C (SparsePolynomial.eval f p)*X : ℝ[X]))).prod =
      clearedProfilePolynomial n a m L R (f 2) (f 3) := by
  simp only [profileForms, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, eval_linear, Int.cast_mul, Int.cast_sub, Int.cast_neg,
    Int.cast_natCast, clearedProfilePolynomial]
  congr 2 <;> congr 2 <;> ring

theorem eval_Xpoly (f : ℕ →* ℝ) (n a m L R k : ℕ) :
    SparsePolynomial.eval f (Xpoly n a m L R k) =
      (clearedProfilePolynomial n a m L R (f 2) (f 3)).coeff k := by
  rw [Xpoly, eval_elementaryPolys, eval_profileForms]

lemma comp_positive_linear (r s : ℝ) :
    (1+C r*X : ℝ[X]).comp (C s*X) = 1+C (s*r)*X := by
  simp only [Polynomial.add_comp, Polynomial.one_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, map_mul]
  ring

lemma comp_negative_linear (r s : ℝ) :
    (1-C r*X : ℝ[X]).comp (C s*X) = 1+C (-s*r)*X := by
  simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, map_mul, map_neg]
  ring

theorem clearedProfilePolynomial_eq_comp (n a m L R : ℕ) (U V : ℝ)
    (hn : (n : ℝ) ≠ 0) (hm : (m : ℝ) ≠ 0) (hUV : U+V ≠ 0) :
    clearedProfilePolynomial n a m L R U V =
      (profilePolynomial n a m (((L : ℝ)*U+R*V)/(U+V))).comp
        (C ((n : ℝ)*m*(U+V))*X) := by
  have h1 : (n : ℝ)*m*(U+V)*(1-(((L : ℝ)*U+R*V)/(U+V))/n) =
      m*(((n : ℝ)-L)*U+((n : ℝ)-R)*V) := by
    field_simp [hn, hUV]
    ring
  have h2 : (n : ℝ)*m*(U+V)*
      (((((L : ℝ)*U+R*V)/(U+V))-a)/m-(((L : ℝ)*U+R*V)/(U+V))/n) =
        ((n : ℝ)*((L : ℝ)-a)-m*L)*U+((n : ℝ)*((R : ℝ)-a)-m*R)*V := by
    field_simp [hn, hm, hUV]
    ring
  have h0 : -((n : ℝ)*m*(U+V))*((((L : ℝ)*U+R*V)/(U+V))/n) =
      -(m : ℝ)*((L : ℝ)*U+R*V) := by field_simp [hn, hUV]
  simp only [profilePolynomial, Polynomial.mul_comp, Polynomial.pow_comp,
    comp_positive_linear, comp_negative_linear, h1, h2, h0,
    clearedProfilePolynomial]

omit [DecidableEq ι] in
theorem eval_Xpoly_actual (f : ℕ →* ℝ) (n a m L R k : ℕ)
    (p : ι → ℝ) (hncard : Fintype.card ι = n) (hk : k ≤ n)
    (hn : (n : ℝ) ≠ 0) (hm : (m : ℝ) ≠ 0) (hUV : f 2+f 3 ≠ 0)
    (hprofile : elementaryGenerating p =
      profilePolynomial n a m (((L : ℝ)*f 2+R*f 3)/(f 2+f 3))) :
    SparsePolynomial.eval f (Xpoly n a m L R k) = ((n : ℝ)*m*(f 2+f 3))^k*elementary p k := by
  rw [eval_Xpoly, clearedProfilePolynomial_eq_comp n a m L R _ _ hn hm hUV,
    ← hprofile, ← elementaryGenerating_scale,
    elementaryGenerating_coeff _ k (by simpa only [hncard] using hk), elementary_scale]

end Certificate
end MathAndTheory.Gyires.RankTwo
