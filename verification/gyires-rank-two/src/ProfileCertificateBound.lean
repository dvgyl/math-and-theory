module

public import ProfileRatios

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo.Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem profile_contraction_of_check (f : ℕ →* ℝ) (hf : ∀ z, 0 ≤ f z)
    (n a m c l L R : ℕ) (u v : ι → ℝ) (hncard : Fintype.card ι = n)
    (hn : 0 < n) (hm : 0 < m) (hl : 0 < l) (hs : f 2+f 3 ≠ 0)
    (hD : 0 < SparsePolynomial.eval f (Dpoly n L R)) (hv : ∑ i, v i = 0)
    (hpu : elementaryGenerating u =
      profilePolynomial n a m (((L : ℝ)*f 2+R*f 3)/(f 2+f 3)))
    (hpv : elementaryGenerating v =
      profilePolynomial n c l (((L : ℝ)*f 2+R*f 3)/(f 2+f 3)))
    (hvariance : (∑ i, (v i)^2)/
      ((n : ℝ)*(SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2))) =
      SparsePolynomial.eval f (Kpoly n c l L R)/((l : ℝ)*SparsePolynomial.eval f (Dpoly n L R)))
    (hcheck : SparsePolynomial.coeffsNonneg (Hpoly n a m c l L R) = true) :
    let σ := SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2)
    let A := centered (1/((n : ℝ)*σ)) u v
    (A*A.transpose).permanent ≤ A.permanent := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hl0 : l ≠ 0 := Nat.ne_of_gt hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hconstant : 0 < (n.factorial : ℝ)/(n : ℝ)^n :=
    div_pos hfac (pow_pos hn' n)
  have hcross := permanent_profile_ratio f n a m c l L R u v hncard hn0 hm0 hl0 hs
    (ne_of_gt hD) hpu hpv
  have hgram := gram_profile_ratio f n a m c l L R u v hncard hn0 hm0 hl0 hs
    (ne_of_gt hD) hv hpu hvariance
  have hnonneg := SparsePolynomial.eval_nonneg_of_check f hf _ hcheck
  rw [eval_Hpoly] at hnonneg
  have hden : 0 < (n.factorial : ℝ)*(m : ℝ)^(2*n)*(l : ℝ)^n*
      SparsePolynomial.eval f (Dpoly n L R)^(2*n) := by positivity
  have hratio : 0 ≤ SparsePolynomial.eval f (Cpoly n a m c l L R) /
      ((n.factorial : ℝ)*(m : ℝ)^n*(l : ℝ)^n*SparsePolynomial.eval f (Dpoly n L R)^n) -
      SparsePolynomial.eval f (Gpoly n a m c l L R) /
      ((n.factorial : ℝ)*(m : ℝ)^(2*n)*(l : ℝ)^n*SparsePolynomial.eval f (Dpoly n L R)^(2*n)) := by
    rw [contraction_fraction _ _ _ _ _ _ n (ne_of_gt hm') (ne_of_gt hl')
      (ne_of_gt hD) (ne_of_gt hfac)]
    exact div_nonneg hnonneg hden.le
  dsimp only at hcross hgram ⊢
  rw [← hcross, ← hgram] at hratio
  exact (div_le_div_iff_of_pos_right hconstant).mp (sub_nonneg.mp hratio)

end MathAndTheory.Gyires.RankTwo.Certificate
