import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NesterovThresholdModel

structure PowerExponent where
  n : ℕ
  even : Even n
  two_le : 2 ≤ n

namespace PowerExponent

theorem pos (q : PowerExponent) : 0 < q.n := lt_of_lt_of_le (by decide) q.two_le
theorem ne_zero (q : PowerExponent) : q.n ≠ 0 := Nat.ne_of_gt q.pos
theorem pred_pos (q : PowerExponent) : 0 < q.n-1 := by have := q.two_le; omega
theorem pred_succ (q : PowerExponent) : q.n-1+1=q.n := Nat.sub_add_cancel (by have:=q.two_le;omega)

noncomputable def p (q : PowerExponent) : ℝ := 1+1/((q.n:ℝ)-1)

theorem p_gt_one (q : PowerExponent) : 1<q.p := by
  have hn : (1:ℝ)<q.n := by exact_mod_cast (show 1<q.n by have := q.two_le; omega)
  unfold p
  linarith [one_div_pos.mpr (sub_pos.mpr hn)]

theorem p_le_two (q : PowerExponent) : q.p≤2 := by
  have hn : (2:ℝ)≤q.n := by exact_mod_cast q.two_le
  have hh : 1/((q.n:ℝ)-1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
  unfold p
  linarith

theorem p_mul_pred (q : PowerExponent) : q.p*((q.n:ℝ)-1)=q.n := by
  have hn : (2:ℝ)≤q.n := by exact_mod_cast q.two_le
  unfold p
  rw [add_mul,one_mul,one_div_mul_cancel (by linarith : (q.n:ℝ)-1≠0)]
  ring

end PowerExponent

theorem one_sub_pow_lower {h : ℝ} (hh : 0≤h) (h1 : h≤1) {m : ℕ} (hm : 1≤m) :
    1-h≤1-h^m := by
  have hp : h^m≤h := by simpa only [pow_one] using pow_le_pow_of_le_one hh h1 hm
  linarith

theorem one_sub_pow_upper {h : ℝ} (hh : 0≤h) (m : ℕ) :
    1-h^m≤(m:ℝ)*(1-h) := by
  have hp := one_add_mul_le_pow (a:=h-1) (by linarith : -2≤h-1) m
  simp only [add_sub_cancel] at hp
  nlinarith

theorem pow_tangent_nonneg {h : ℝ} (hh : 0≤h) (m : ℕ) :
    0≤1-((m:ℝ)+1)*h^m+(m:ℝ)*h^(m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := mul_nonneg (mul_nonneg (by positivity : 0≤(m:ℝ)+1) (pow_nonneg hh m))
      (sq_nonneg (1-h))
    simp only [Nat.cast_succ,pow_succ] at *
    nlinarith

theorem consecutive_power_bound {h : ℝ} (hh : 0≤h) (m : ℕ) :
    (m:ℝ)*(1-h^(m+1))≤((m:ℝ)+1)*(1-h^m) := by
  have hp := pow_tangent_nonneg hh m
  linarith

theorem abs_le_one_of_even_pow_le {q : ℕ} (hq : Even q) (hq0 : q≠0)
    {a : ℝ} (ha : a^q≤1) : |a|≤1 := by
  apply le_of_pow_le_pow_left₀ hq0 (by norm_num : (0:ℝ)≤1)
  simpa only [hq.pow_abs,one_pow] using ha

theorem even_power_double_pred_bound (q : PowerExponent) {h b : ℝ}
    (hh : 0≤h) (h1 : h≤1) (hb : |b|≤1) :
    h^(2*(q.n-1))+b^(2*(q.n-1))≤h^q.n+b^q.n := by
  have he : q.n≤2*(q.n-1) := by have := q.two_le; omega
  have hl := pow_le_pow_of_le_one hh h1 he
  have hr := pow_le_pow_of_le_one (abs_nonneg b) hb he
  have hev : Even (2*(q.n-1)) := even_two_mul _
  rw [hev.pow_abs,q.even.pow_abs] at hr
  exact add_le_add hl hr

end NesterovThresholdModel
