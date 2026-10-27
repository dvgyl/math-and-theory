module

public import ProfileScaling
public import VarianceScaling
public import DenominatorAlgebra
public import NormalizedPermanent

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo.Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem permanent_profile_ratio (f : ℕ →* ℝ) (n a m c l L R : ℕ)
    (u v : ι → ℝ) (hncard : Fintype.card ι = n) (hn : n ≠ 0)
    (hm : m ≠ 0) (hl : l ≠ 0) (hs : f 2+f 3 ≠ 0)
    (hD : SparsePolynomial.eval f (Dpoly n L R) ≠ 0)
    (hpu : elementaryGenerating u =
      profilePolynomial n a m (((L : ℝ)*f 2+R*f 3)/(f 2+f 3)))
    (hpv : elementaryGenerating v =
      profilePolynomial n c l (((L : ℝ)*f 2+R*f 3)/(f 2+f 3))) :
    let σ := SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2)
    (centered (1/((n : ℝ)*σ)) u v).permanent / ((n.factorial : ℝ)/(n : ℝ)^n) =
      SparsePolynomial.eval f (Cpoly n a m c l L R) /
        ((n.factorial : ℝ)*(m : ℝ)^n*(l : ℝ)^n*SparsePolynomial.eval f (Dpoly n L R)^n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hσ : SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2) ≠ 0 :=
    div_ne_zero hD (mul_ne_zero (pow_ne_zero 2 hn') (pow_ne_zero 2 hs))
  have hnorm := permanent_centered_normalized (ι := ι)
    (by simpa only [hncard] using hn) _ hσ u v
  rw [hncard] at hnorm
  dsimp only
  rw [hnorm, eval_Cpoly, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [eval_Xpoly_actual f n a m L R k u hncard hk' hn' hm' hs hpu,
    eval_Xpoly_actual f n c l L R k v hncard hk' hn' hl' hs hpv]
  have hterm := cleared_cross_term (n : ℝ) m l (f 2+f 3)
    (SparsePolynomial.eval f (Dpoly n L R))
    ((k.factorial : ℝ)*((n-k).factorial : ℝ)) (n.factorial : ℝ)
    (elementary u k) (elementary v k) n k hk' hn' hm' hl' hs hD hfac
  calc
    _ = ((k.factorial : ℝ)*((n-k).factorial : ℝ))*
        ((n : ℝ)*m*(f 2+f 3))^k*elementary u k*
        ((n : ℝ)*l*(f 2+f 3))^k*elementary v k*((m : ℝ)*l)^(n-k)*
        SparsePolynomial.eval f (Dpoly n L R)^(n-k)/
        ((n.factorial : ℝ)*(m : ℝ)^n*(l : ℝ)^n*SparsePolynomial.eval f (Dpoly n L R)^n) := hterm
    _ = _ := by ring

theorem gram_profile_ratio (f : ℕ →* ℝ) (n a m c l L R : ℕ)
    (u v : ι → ℝ) (hncard : Fintype.card ι = n) (hn : n ≠ 0)
    (hm : m ≠ 0) (hl : l ≠ 0) (hs : f 2+f 3 ≠ 0)
    (hD : SparsePolynomial.eval f (Dpoly n L R) ≠ 0)
    (hv : ∑ i, v i = 0)
    (hpu : elementaryGenerating u =
      profilePolynomial n a m (((L : ℝ)*f 2+R*f 3)/(f 2+f 3)))
    (hvariance : (∑ i, (v i)^2)/
      ((n : ℝ)*(SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2))) =
      SparsePolynomial.eval f (Kpoly n c l L R)/((l : ℝ)*SparsePolynomial.eval f (Dpoly n L R))) :
    let σ := SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2)
    let A := centered (1/((n : ℝ)*σ)) u v
    (A*A.transpose).permanent / ((n.factorial : ℝ)/(n : ℝ)^n) =
      SparsePolynomial.eval f (Gpoly n a m c l L R) /
        ((n.factorial : ℝ)*(m : ℝ)^(2*n)*(l : ℝ)^n*SparsePolynomial.eval f (Dpoly n L R)^(2*n)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hσ : SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2) ≠ 0 :=
    div_ne_zero hD (mul_ne_zero (pow_ne_zero 2 hn') (pow_ne_zero 2 hs))
  have hnorm := permanent_centered_gram_left_normalized (ι := ι)
    (by simpa only [hncard] using hn) _ hσ u v hv
  rw [hncard] at hnorm
  dsimp only at hnorm ⊢
  rw [hnorm, hvariance, eval_Gpoly, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [eval_Xpoly_actual f n a m L R k u hncard hk' hn' hm' hs hpu]
  have hterm := cleared_gram_term (n : ℝ) m l (f 2+f 3)
    (SparsePolynomial.eval f (Dpoly n L R)) (SparsePolynomial.eval f (Kpoly n c l L R))
    ((k.factorial : ℝ)*((n-k).factorial : ℝ)) (n.factorial : ℝ)
    (elementary u k) n k hk' hn' hm' hl' hs hD hfac
  calc
    _ = ((k.factorial : ℝ)*((n-k).factorial : ℝ))*
        (((n : ℝ)*m*(f 2+f 3))^k*elementary u k)^2*
        SparsePolynomial.eval f (Kpoly n c l L R)^k*
        (m : ℝ)^(2*(n-k))*(l : ℝ)^(n-k)*SparsePolynomial.eval f (Dpoly n L R)^(2*(n-k))/
        ((n.factorial : ℝ)*(m : ℝ)^(2*n)*(l : ℝ)^n*SparsePolynomial.eval f (Dpoly n L R)^(2*n)) := hterm
    _ = _ := by ring

end MathAndTheory.Gyires.RankTwo.Certificate
