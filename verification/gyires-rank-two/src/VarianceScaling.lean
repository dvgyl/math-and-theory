module

public import CertificatePolynomials
public import CenteredParameters

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι]

theorem centered_variance_deficit (p : ι → ℝ) (t : ℝ)
    (hn : Fintype.card ι ≠ 0) (hmean : ∑ i, p i = t) :
    (∑ i, (p i-t/Fintype.card ι)^2) =
      t-t^2/Fintype.card ι-(∑ i, p i*(1-p i)) := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn
  have hmean' : ∑ i, p i = (Fintype.card ι : ℝ)*(t/Fintype.card ι) := by
    rw [hmean]
    field_simp [hn']
  have hs := centered_variance_eq p (t/Fintype.card ι) hmean'
  have hterms : (∑ i, p i*(1-p i)) = t-(∑ i, (p i)^2) := by
    calc
      _ = ∑ i, (p i-(p i)^2) := by apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [Finset.sum_sub_distrib, hmean]
  change (∑ i, (p i-t/Fintype.card ι)^2) = _ at hs
  rw [hs, hterms]
  field_simp [hn']
  ring

namespace Certificate

theorem interval_scale_identity (N L R U V : ℝ) (hN : N ≠ 0) (hs : U+V ≠ 0) :
    (((L*U+R*V)/(U+V))*(N-(L*U+R*V)/(U+V))/N^2) =
      ((L*U+R*V)*((N-L)*U+(N-R)*V))/(N^2*(U+V)^2) := by
  field_simp [hN, hs]
  ring

theorem variance_scale_identity (N c l L R U V : ℝ)
    (hN : N ≠ 0) (hl : l ≠ 0) (hs : U+V ≠ 0)
    (hD : (L*U+R*V)*((N-L)*U+(N-R)*V) ≠ 0) :
    (((L*U+R*V)/(U+V))-((L*U+R*V)/(U+V))^2/N-
      (((L*U+R*V)/(U+V))-c)*(l+c-(L*U+R*V)/(U+V))/l) /
      (N*(((L*U+R*V)*((N-L)*U+(N-R)*V))/(N^2*(U+V)^2))) =
    (l*((L*U+R*V)*((N-L)*U+(N-R)*V))-
      N*((L-c)*U+(R-c)*V)*((l+c-L)*U+(l+c-R)*V)) /
        (l*((L*U+R*V)*((N-L)*U+(N-R)*V))) := by
  have hT : L*U+R*V ≠ 0 := (mul_ne_zero_iff.mp hD).1
  have hW : (N-L)*U+(N-R)*V ≠ 0 := (mul_ne_zero_iff.mp hD).2
  field_simp [hN, hl, hs, hT, hW]
  ring

theorem eval_Kpoly_actual (f : ℕ →* ℝ) (n c l L R : ℕ) (p : ι → ℝ)
    (hncard : Fintype.card ι = n) (hn : n ≠ 0) (hl : l ≠ 0)
    (hs : f 2+f 3 ≠ 0) (hD : SparsePolynomial.eval f (Dpoly n L R) ≠ 0)
    (hmean : ∑ i, p i = ((L : ℝ)*f 2+R*f 3)/(f 2+f 3))
    (hprofile : (∑ i, p i*(1-p i)) =
      ((((L : ℝ)*f 2+R*f 3)/(f 2+f 3))-c)*
        ((l : ℝ)+c-((L : ℝ)*f 2+R*f 3)/(f 2+f 3))/l) :
    (∑ i, (p i-(((L : ℝ)*f 2+R*f 3)/(f 2+f 3))/n)^2) /
      ((n : ℝ)*(SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2))) =
      SparsePolynomial.eval f (Kpoly n c l L R)/((l : ℝ)*SparsePolynomial.eval f (Dpoly n L R)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hsum := centered_variance_deficit p _ (by simpa only [hncard] using hn) hmean
  rw [hncard, hprofile] at hsum
  rw [hsum, eval_Dpoly, eval_Kpoly, eval_Dpoly]
  exact variance_scale_identity n c l L R (f 2) (f 3) hn' hl' hs
    (by simpa only [eval_Dpoly] using hD)

end Certificate
end MathAndTheory.Gyires.RankTwo
