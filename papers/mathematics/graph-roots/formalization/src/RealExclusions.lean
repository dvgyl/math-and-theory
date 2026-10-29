import GraphDegree

noncomputable section
namespace SquareFlowerCompletion.RealCompanion

def a (t : ℝ) : ℝ := t^2 - 3*t + 3
def realBracket (n : ℕ) (x : ℝ) : ℝ :=
  x*(x^2+3*x+3)^n + (x^2+3*x+1)^n - 1

theorem a_pos (t : ℝ) : 0 < a t := by
  dsimp [a]
  nlinarith [sq_nonneg (t-3/2)]

theorem bracket_negative_coordinate (n : ℕ) (t : ℝ) :
    realBracket n (-t) = (a t - 2)^n - t*(a t)^n - 1 := by
  have h1 : (-t)^2 + 3*(-t) + 3 = a t := by dsimp [a]; ring
  have h2 : (-t)^2 + 3*(-t) + 1 = a t - 2 := by dsimp [a]; ring
  rw [realBracket,h1,h2]
  ring

theorem graph_root_iff_realBracket {n : ℕ} {x : ℝ} (hx : x ≠ 0) :
    (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0 ↔ realBracket n x = 0 := by
  rw [Counting.eval_eq_zero_iff_bracket (by exact_mod_cast hx)]
  dsimp [realBracket]
  norm_cast

theorem positive_not_root (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (Counting.complexDominationPolynomial n).eval (x:ℂ) ≠ 0 := by
  intro h
  have hr := (graph_root_iff_realBracket hx.ne').mp h
  have ha : 0 < x^2+3*x+3 := by positivity
  have hb : 1 ≤ x^2+3*x+1 := by nlinarith [sq_nonneg x]
  have hp : 0 < x*(x^2+3*x+3)^n := mul_pos hx (pow_pos ha n)
  have hpow : 1 ≤ (x^2+3*x+1)^n := one_le_pow₀ hb
  dsimp [realBracket] at hr
  linarith

theorem bounded_power_le_one (n : ℕ) {b : ℝ} (hb : |b| ≤ 1) : b^n ≤ 1 := by
  calc
    b^n ≤ |b^n| := le_abs_self _
    _ = |b|^n := abs_pow _ _
    _ ≤ 1 := pow_le_one₀ (abs_nonneg _) hb

theorem bracket_negative_outside (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hout : t ≤ 1 ∨ 2 ≤ t) : realBracket n (-t) < 0 := by
  rw [bracket_negative_coordinate]
  have ha := a_pos t
  have hpos : 0 < t*(a t)^n := mul_pos ht (pow_pos ha n)
  by_cases ht3 : t ≤ 3
  · have hab : |a t - 2| ≤ 1 := by
      rw [abs_le]
      dsimp [a]
      rcases hout with h | h
      · constructor <;> nlinarith [sq_nonneg t, mul_nonneg ht.le (by linarith : 0 ≤ 1-t)]
      · constructor <;> nlinarith [sq_nonneg (t-2), mul_nonneg (by linarith : 0 ≤ t-2) (by linarith : 0 ≤ 3-t)]
    have hp := bounded_power_le_one n hab
    linarith
  · have hab : 0 ≤ a t - 2 := by dsimp [a]; nlinarith [sq_nonneg (t-3)]
    have hp : (a t - 2)^n ≤ (a t)^n := pow_le_pow_left₀ hab (by linarith) n
    have hpow : 0 < (a t)^n := pow_pos ha n
    nlinarith

theorem real_root_negative_interval {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hr : (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0) :
    -2 < x ∧ x < -1 := by
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => positive_not_root n h hr)) hx
  have ht : 0 < -x := by linarith
  have hb := (graph_root_iff_realBracket hx).mp hr
  have hout : 1 < -x ∧ -x < 2 := by
    by_contra h
    have hh : -x ≤ 1 ∨ 2 ≤ -x := by
      by_cases h1 : -x ≤ 1
      · exact Or.inl h1
      · right
        by_contra h2
        exact h ⟨by linarith, by linarith⟩
    have hn := bracket_negative_outside n ht hh
    rw [neg_neg,hb] at hn
    linarith
  constructor <;> linarith [hout.1,hout.2]

theorem odd_order_only_zero {n : ℕ} (hn : Odd n) {x : ℝ} :
    (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0 ↔ x = 0 := by
  constructor
  · intro hr
    by_contra hx
    obtain ⟨hx2,hx1⟩ := real_root_negative_interval hx hr
    have ht1 : 1 < -x := by linarith
    have ht2 : -x < 2 := by linarith
    have hab : a (-x)-2 < 0 := by
      dsimp [a]
      nlinarith [mul_pos (by linarith : 0 < -x-1) (by linarith : 0 < 2+x)]
    have hp : (a (-x)-2)^n < 0 := hn.pow_neg hab
    have hpos : 0 < (-x)*(a (-x))^n := mul_pos (by linarith) (pow_pos (a_pos _) n)
    have hb := (graph_root_iff_realBracket hx).mp hr
    have hi := bracket_negative_coordinate n (-x)
    rw [neg_neg,hb] at hi
    linarith
  · intro h
    subst x
    exact Extremal.graphPolynomial_eval_zero n

theorem order_two_only_zero {x : ℝ} :
    (Counting.complexDominationPolynomial 2).eval (x:ℂ) = 0 ↔ x = 0 := by
  constructor
  · intro hr
    by_contra hx
    obtain ⟨hx2,hx1⟩ := real_root_negative_interval hx hr
    have hi : (a (-x)-2)^2 - (-x)*(a (-x))^2 - 1 =
        -(2*(-x)-3)^2 - ((-x)-1)*(a (-x))^2 := by dsimp [a]; ring
    have hpos : 0 < ((-x)-1)*(a (-x))^2 := mul_pos (by linarith) (sq_pos_of_pos (a_pos _))
    have hb := (graph_root_iff_realBracket hx).mp hr
    have hc := bracket_negative_coordinate 2 (-x)
    rw [neg_neg,hb] at hc
    linarith [sq_nonneg (2*(-x)-3)]
  · intro h
    subst x
    exact Extremal.graphPolynomial_eval_zero 2

#print axioms positive_not_root
#print axioms real_root_negative_interval
#print axioms odd_order_only_zero
#print axioms order_two_only_zero
end SquareFlowerCompletion.RealCompanion
