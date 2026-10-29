import BookBasicRoots
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp

noncomputable section
open Polynomial
namespace BookCompletion

def u (t : ℝ) : ℝ := (1-t)^2/t

def normalized (n : ℕ) (t : ℝ) : ℝ :=
  t^2*(u t)^n + (-1:ℝ)^n*((1-2*t)*(2-t)^n-2)

theorem eval_negative_factor (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : t≠0) :
    (realPolynomial n).eval (-t) = t^n * normalized n t := by
  rw [eval_realPolynomial n hn]
  have hb : (-t)^2+2*(-t) = (-t)*(2-t) := by ring
  have hc : 1 + -t = 1-t := by ring
  rw [hb,hc,pow_mul]
  have hnegn : (-t)^n = (-1:ℝ)^n*t^n := by rw [neg_eq_neg_one_mul, mul_pow]
  have hneg2 : (-t)^2 = t^2 := by ring
  simp only [normalized, u, div_pow, mul_pow, hnegn, hneg2]
  field_simp [ht]
  ring

theorem real_root_iff_normalized (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : 0<t) :
    (realPolynomial n).IsRoot (-t) ↔ normalized n t=0 := by
  rw [Polynomial.IsRoot.def, eval_negative_factor n hn (ne_of_gt ht), mul_eq_zero]
  simp [pow_ne_zero n (ne_of_gt ht)]

theorem normalized_odd (n : ℕ) (ho : Odd n) (t : ℝ) :
    normalized n t = t^2*(u t)^n + (2*t-1)*(2-t)^n + 2 := by
  rw [normalized, ho.neg_one_pow]
  ring

theorem normalized_even (n : ℕ) (he : Even n) (t : ℝ) :
    normalized n t = t^2*(u t)^n + (1-2*t)*(2-t)^n - 2 := by
  rw [normalized, he.neg_one_pow]
  ring

theorem normalized_odd_middle_pos (n : ℕ) (ho : Odd n) {t : ℝ}
    (ht : 1/2 ≤ t) (ht2 : t≤2) : 0 < normalized n t := by
  rw [normalized_odd n ho]
  have htpos : 0<t := by linarith
  have hu : 0≤u t := div_nonneg (sq_nonneg _) htpos.le
  have hv : 0≤(2-t)^n := pow_nonneg (by linarith) _
  have hc : 0≤2*t-1 := by linarith
  positivity

theorem u_eq (t : ℝ) (ht : t≠0) : u t = t-2+1/t := by
  unfold u
  field_simp [ht]
  ring

theorem K_pos (n : ℕ) {t : ℝ} (ht : 2<t) :
    0 < t^2*(u t)^n - (2*t-1)*(t-2)^n := by
  have htpos : 0<t := by linarith
  have hvpos : 0<t-2 := by linarith
  have hupos : 0<u t := by rw [u_eq t (ne_of_gt htpos)]; positivity
  have hvu : t-2 ≤ u t := by
    rw [u_eq t (ne_of_gt htpos)]
    linarith [one_div_pos.mpr htpos]
  have hpow : (t-2)^n ≤ (u t)^n := pow_le_pow_left₀ hvpos.le hvu n
  have hcoef : 2*t-1 < t^2 := by nlinarith [sq_nonneg (t-2)]
  have hmul : (2*t-1)*(t-2)^n < t^2*(u t)^n := by
    calc
      _ ≤ (2*t-1)*(u t)^n := mul_le_mul_of_nonneg_left hpow (by linarith)
      _ < _ := mul_lt_mul_of_pos_right hcoef (pow_pos hupos n)
  linarith

theorem normalized_odd_outer_pos (n : ℕ) (ho : Odd n) {t : ℝ}
    (ht : 2<t) : 0 < normalized n t := by
  rw [normalized_odd n ho]
  have hpow : (2-t)^n = -((t-2)^n) := by
    rw [show 2-t = -(t-2) by ring, ho.neg_pow]
  rw [hpow]
  have hk := K_pos n ht
  nlinarith

theorem odd_nonzero_real_root_interval (n : ℕ) (hn : 1≤n) (ho : Odd n)
    {x : ℝ} (hx : x≠0) (hroot : (realPolynomial n).IsRoot x) :
    -(1/2)<x ∧ x<0 := by
  have hxneg : x<0 := lt_of_le_of_ne (realPolynomial_nonpositive_root n hroot) hx
  have ht : 0 < -x := neg_pos.mpr hxneg
  have hz : normalized n (-x)=0 := by
    apply (real_root_iff_normalized n hn ht).mp
    simpa using hroot
  refine ⟨?_,hxneg⟩
  by_contra h
  have htlo : 1/2 ≤ -x := by linarith
  by_cases hthi : -x≤2
  · have hp := normalized_odd_middle_pos n ho htlo hthi
    linarith
  · have hp := normalized_odd_outer_pos n ho (lt_of_not_ge hthi)
    linarith

theorem normalized_even_middle_neg (n : ℕ) (hn : 2≤n) (he : Even n) {t : ℝ}
    (ht : 1/2 ≤ t) (ht2 : t≤2) : normalized n t < 0 := by
  have htpos : 0<t := by linarith
  have hu0 : 0≤u t := div_nonneg (sq_nonneg _) htpos.le
  have hu1 : u t ≤ 1/2 := by
    rw [u, div_le_iff₀ htpos]
    have hp : (t-1/2)*(t-2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
  have hpow1 : (u t)^n ≤ (1/2:ℝ)^n := pow_le_pow_left₀ hu0 hu1 n
  have hpow2 : (1/2:ℝ)^n ≤ (1/2:ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have htSq : t^2≤4 := by nlinarith
  have hmul : t^2*(u t)^n ≤ 4*(1/2:ℝ)^2 :=
    mul_le_mul htSq (hpow1.trans hpow2) (pow_nonneg hu0 _) (by norm_num)
  have hneg : (1-2*t)*(2-t)^n ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg (by linarith) _)
  rw [normalized_even n he]
  nlinarith

theorem even_nonzero_root_regions (n : ℕ) (hn : 2≤n) (he : Even n)
    {x : ℝ} (hx : x≠0) (hroot : (realPolynomial n).IsRoot x) :
    x < -2 ∨ (-(1/2)<x ∧ x<0) := by
  have hxneg : x<0 := lt_of_le_of_ne (realPolynomial_nonpositive_root n hroot) hx
  have ht : 0 < -x := neg_pos.mpr hxneg
  have hz : normalized n (-x)=0 := by
    apply (real_root_iff_normalized n (by omega) ht).mp
    simpa using hroot
  by_cases hout : x < -2
  · exact Or.inl hout
  · right
    refine ⟨?_,hxneg⟩
    by_contra h
    have hp := normalized_even_middle_neg n hn he (t:=-x) (by linarith) (by linarith)
    linarith

#print axioms eval_negative_factor
#print axioms real_root_iff_normalized
#print axioms normalized_odd
#print axioms normalized_even
#print axioms normalized_odd_middle_pos
#print axioms u_eq
#print axioms K_pos
#print axioms normalized_odd_outer_pos
#print axioms odd_nonzero_real_root_interval
#print axioms normalized_even_middle_neg
#print axioms even_nonzero_root_regions
end BookCompletion
