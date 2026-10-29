import BookNegative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
namespace BookCompletion
open Set

def innerA (t : ℝ) : ℝ := (1-t)^2/(t*(2-t))
def innerE (t : ℝ) : ℝ := (1-t)*(2-t)
def innerADeriv (t : ℝ) : ℝ := -2*(1-t)/(t^2*(2-t)^2)
def innerQ (n : ℕ) (t : ℝ) : ℝ := t^2*(innerA t)^n
def innerC (n : ℕ) (t : ℝ) : ℝ := 2*(innerE t-(n:ℝ))/(t*innerE t)
def innerCDeriv (n : ℕ) (t : ℝ) : ℝ :=
  2*((2*t-3)*(t*innerE t)-(innerE t-(n:ℝ))*(innerE t+t*(2*t-3)))/(t*innerE t)^2
def innerD (n : ℕ) (t : ℝ) : ℝ :=
  2*((innerE t)^2+(n:ℝ)*t*(6-t)+2*(n:ℝ)*((n:ℝ)-3))/(t^2*(innerE t)^2)
def innerQprime (n : ℕ) (t : ℝ) : ℝ := innerQ n t*innerC n t
def innerQsecond (n : ℕ) (t : ℝ) : ℝ := innerQ n t*innerD n t

theorem inner_domain {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    0 < 1-t ∧ 0 < 2-t ∧ 0 < innerE t ∧ innerE t < 2 ∧ 0 < innerA t := by
  have h1 : 0 < 1-t := by linarith [ht.2]
  have h2 : 0 < 2-t := by linarith [ht.2]
  have he : innerE t < 2 := by
    have hp := mul_pos ht.1 (by linarith [ht.2] : 0 < 3-t)
    dsimp [innerE]
    nlinarith
  exact ⟨h1,h2,mul_pos h1 h2,he,div_pos (sq_pos_of_pos h1) (mul_pos ht.1 h2)⟩

theorem hasDerivAt_innerE (t : ℝ) : HasDerivAt innerE (2*t-3) t := by
  convert ((hasDerivAt_id t).const_sub 1).mul ((hasDerivAt_id t).const_sub 2) using 1
  simp only [id_eq]
  ring

theorem hasDerivAt_innerA {t : ℝ} (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) :
    HasDerivAt innerA (innerADeriv t) t := by
  convert (((hasDerivAt_id t).const_sub 1).pow 2).div
    ((hasDerivAt_id t).mul ((hasDerivAt_id t).const_sub 2)) (mul_ne_zero ht0 ht2) using 1
  dsimp [innerA,innerADeriv]
  field_simp [ht0,ht2]
  ring

theorem hasDerivAt_innerQ {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerQ n) (innerQprime n t) t := by
  have hf := inner_domain ht
  have ht0 := ht.1.ne'
  have ht1 := hf.1.ne'
  have ht2 := hf.2.1.ne'
  have hpow : (innerA t)^n = (innerA t)^(n-1)*innerA t := by
    rw [← pow_succ,Nat.sub_add_cancel hn]
  have hcore : 2*t*innerA t+t^2*(n:ℝ)*innerADeriv t = t^2*innerA t*innerC n t := by
    dsimp [innerADeriv,innerA,innerC,innerE]
    field_simp [ht0,ht1,ht2]
    ring
  have h := ((hasDerivAt_id t).pow 2).mul ((hasDerivAt_innerA ht0 ht2).pow n)
  convert h using 1
  dsimp [innerQprime,innerQ]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul,id_eq]
  simp only [hpow]
  calc
    t^2*((innerA t)^(n-1)*innerA t)*innerC n t =
        (innerA t)^(n-1)*(t^2*innerA t*innerC n t) := by ring
    _ = (innerA t)^(n-1)*(2*t*innerA t+t^2*(n:ℝ)*innerADeriv t) := by rw [← hcore]
    _ = 2*t*((innerA t)^(n-1)*innerA t)+t^2*((n:ℝ)*(innerA t)^(n-1)*innerADeriv t) := by ring

theorem hasDerivAt_innerC (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerC n) (innerCDeriv n t) t := by
  have hf := inner_domain ht
  have he := hasDerivAt_innerE t
  convert ((he.sub_const (n:ℝ)).const_mul 2).div ((hasDerivAt_id t).mul he)
    (mul_ne_zero ht.1.ne' hf.2.2.1.ne') using 1
  dsimp [innerC,innerCDeriv]
  ring

theorem innerC_square_add_deriv (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    (innerC n t)^2+innerCDeriv n t = innerD n t := by
  have hf := inner_domain ht
  dsimp [innerC,innerCDeriv,innerD,innerE]
  field_simp [ht.1.ne',hf.1.ne',hf.2.1.ne']
  ring

theorem hasDerivAt_innerQprime {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerQprime n) (innerQsecond n t) t := by
  have h := (hasDerivAt_innerQ hn ht).mul (hasDerivAt_innerC n ht)
  convert h using 1
  dsimp [innerQsecond,innerQprime]
  rw [← innerC_square_add_deriv n ht]
  ring

theorem innerQ_pos (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) : 0 < innerQ n t := by
  exact mul_pos (sq_pos_of_pos ht.1) (pow_pos (inner_domain ht).2.2.2.2 n)

theorem innerQprime_neg {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    innerQprime n t < 0 := by
  have hf := inner_domain ht
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hC : innerC n t < 0 :=
    div_neg_of_neg_of_pos (by linarith [hf.2.2.2.1]) (mul_pos ht.1 hf.2.2.1)
  exact mul_neg_of_pos_of_neg (innerQ_pos n ht) hC

theorem innerQsecond_pos {n : ℕ} (hn : 3 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    0 < innerQsecond n t := by
  have hf := inner_domain ht
  have hN : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hn3 : 0 ≤ (n:ℝ)-3 := by linarith
  have h6 : 0 < 6-t := by linarith [ht.2]
  have he2 : 0 < (innerE t)^2 := sq_pos_of_pos hf.2.2.1
  have hmid : 0 < (n:ℝ)*t*(6-t) := mul_pos (mul_pos hN0 ht.1) h6
  have hlast : 0 ≤ 2*(n:ℝ)*((n:ℝ)-3) := mul_nonneg (by positivity) hn3
  have hD : 0 < innerD n t := div_pos
    (by positivity) (mul_pos (sq_pos_of_pos ht.1) he2)
  exact mul_pos (innerQ_pos n ht) hD

#print axioms inner_domain
#print axioms hasDerivAt_innerE
#print axioms hasDerivAt_innerA
#print axioms hasDerivAt_innerQ
#print axioms hasDerivAt_innerC
#print axioms innerC_square_add_deriv
#print axioms hasDerivAt_innerQprime
#print axioms innerQ_pos
#print axioms innerQprime_neg
#print axioms innerQsecond_pos
end BookCompletion
