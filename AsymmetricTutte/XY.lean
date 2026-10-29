module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Convert
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Topology.Algebra.InfiniteSum.Order


@[expose] public section

/-! The two families of boundary inequalities force (x - 1)(y - 1) > 1. -/
namespace AsymmetricTutte

set_option maxHeartbeats 100000

private theorem curves_all_nat (a b : ℝ)
    (h : ∀ k : ℕ, 2 ≤ k → (a + (k : ℝ) * b)^2 ≤ (1+a^2)*(1+b^2)^k) :
    ∀ k : ℕ, (a + (k : ℝ) * b)^2 ≤ (1+a^2)*(1+b^2)^k := by
  intro k
  rcases k with _ | k
  · norm_num
  rcases k with _ | k
  · norm_num
    nlinarith [sq_nonneg (a*b-1)]
  · exact h _ (by omega)

private theorem geometric_curve_bound (a b : ℝ) (hb : 0 < b)
    (h : ∀ k : ℕ, (a + (k : ℝ) * b)^2 ≤ (1+a^2)*(1+b^2)^k) :
    2*a^2*b^2 + 3*b^2 ≥ 2*a*b + 1 := by
  let q : ℝ := 1 / (1 + 2*b^2)
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hd : 0 < 1 + 2*b^2 := by positivity
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_iff₀ hd).2
    nlinarith
  have hqnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hr0 : 0 < (1+b^2)*q := by positivity
  have hr1 : (1+b^2)*q < 1 := by
    dsimp [q]
    rw [← mul_div_assoc, mul_one]
    apply (div_lt_iff₀ hd).2
    nlinarith
  have hrnorm : ‖(1+b^2)*q‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hzero := hasSum_geometric_of_norm_lt_one hqnorm
  have hone := hasSum_coe_mul_geometric_of_norm_lt_one hqnorm
  have htwo := hasSum_choose_mul_geometric_of_norm_lt_one 2 hqnorm
  have hleft : HasSum (fun n : ℕ => (a+(n:ℝ)*b)^2*q^n)
      ((2*b^2)/(1-q)^3 + (2*a*b-3*b^2)*q/(1-q)^2 + (a^2-2*b^2)/(1-q)) := by
    have hs := ((htwo.mul_left (2*b^2)).add
      (hone.mul_left (2*a*b-3*b^2))).add (hzero.mul_left (a^2-2*b^2))
    have hh := hs.congr_fun (g := fun n : ℕ => (a+(n:ℝ)*b)^2*q^n) (by
      intro n
      rw [Nat.cast_choose_two]
      push_cast
      ring)
    simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc, show (2:ℕ)+1=3 by rfl] using hh
  have hright : HasSum (fun n : ℕ => (1+a^2)*((1+b^2)*q)^n)
      ((1+a^2)/(1-(1+b^2)*q)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hrnorm).mul_left (1+a^2)
  have hpoint : ∀ n : ℕ, (a+(n:ℝ)*b)^2*q^n ≤ (1+a^2)*((1+b^2)*q)^n := by
    intro n
    calc (a+(n:ℝ)*b)^2*q^n ≤ ((1+a^2)*(1+b^2)^n)*q^n :=
      mul_le_mul_of_nonneg_right (h n) (pow_nonneg hq0.le n)
      _ = (1+a^2)*((1+b^2)*q)^n := by rw [mul_pow]; ring
  have hle := Summable.tsum_le_tsum hpoint hleft.summable hright.summable
  rw [hleft.tsum_eq, hright.tsum_eq] at hle
  have hc : 0 < (1+2*b^2)/(4*b^4) := by positivity
  have hden1 : 1-q = (2*b^2)/(1+2*b^2) := by
    dsimp [q]
    field_simp
    ring
  have hden2 : 1-(1+b^2)*q = b^2/(1+2*b^2) := by
    dsimp [q]
    field_simp
    ring
  have heq :
      ((2*b^2)/(1-q)^3 + (2*a*b-3*b^2)*q/(1-q)^2 + (a^2-2*b^2)/(1-q))
      - (1+a^2)/(1-(1+b^2)*q) =
      ((1+2*b^2)/(4*b^4)) * (1+2*a*b-2*a^2*b^2-3*b^2) := by
    rw [hden1, hden2]
    dsimp [q]
    field_simp [ne_of_gt hb, ne_of_gt hd]
    ring
  have hprod : ((1+2*b^2)/(4*b^4)) * (1+2*a*b-2*a^2*b^2-3*b^2) ≤ 0 := by
    rw [← heq]
    linarith
  have := nonpos_of_mul_nonpos_right hprod hc
  linarith

private theorem curves_small_second_impossible (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a*b ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ k : ℕ, 2 ≤ k → (a + (k : ℝ) * b)^2 ≤ (1+a^2)*(1+b^2)^k) : False := by
  have hg := geometric_curve_bound a b hb (curves_all_nat a b h)
  have ht : 0 < a*b := mul_pos ha hb
  have ht2 : (a*b)^2 ≤ a*b := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hab)]
  have hb2lo : (1:ℝ)/3 ≤ b^2 := by nlinarith
  have hb2hi : b^2 ≤ 1 := by
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb1)]
  by_cases hbeq : b = 1
  · subst b
    have h2 := h 2 (by omega)
    norm_num at h2 hab
    nlinarith only [h2, ht2, ha]
  have hblt : b < 1 := lt_of_le_of_ne hb1 hbeq
  have hb2lt : b^2 < 1 := by
    nlinarith only [hblt, mul_pos hb (sub_pos.mpr hblt)]
  have h3 := h 3 (by omega)
  norm_num at h3
  let B := b^2
  let t := a*b
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBhi : B < 1 := hb2lt
  have hBlo : (1:ℝ)/3 ≤ B := hb2lo
  have ht0 : 0 < t := ht
  have ht1 : t ≤ 1 := hab
  have htt : t^2 ≤ t := ht2
  have hc0 : (1+B)^3 - 9*B < 0 := by
    have hi := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg B) (sub_nonpos.mpr hBhi.le)
    have hj := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hBlo) (sub_nonpos.mpr hBhi.le)
    nlinarith only [hi, hj, hBpos]
  have hc : B*((1+B)^3-9*B) < 0 := mul_neg_of_pos_of_neg hBpos hc0
  have he : (1+B)^4-(1+3*B)^2 < 0 := by
    have hi : B*(B-1)*(B^2+5*B+2) < 0 := by
      apply mul_neg_of_neg_of_pos
      · exact mul_neg_of_pos_of_neg hBpos (sub_neg.mpr hBhi)
      · positivity
    nlinarith only [hi]
  have hA : 0 ≤ (1+B)^3-1 := by
    nlinarith only [hBpos, sq_nonneg B, pow_nonneg hBpos.le 3]
  have hconv := mul_nonneg hA (sub_nonneg.mpr htt)
  have hcweight : (1-t)*(B*((1+B)^3-9*B)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hc.le
  have heweight : t*((1+B)^4-(1+3*B)^2) < 0 :=
    mul_neg_of_pos_of_neg ht0 he
  have hneg : (t^2+B)*(1+B)^3-(t+3*B)^2 < 0 := by
    nlinarith only [hconv, hcweight, heweight]
  have hnonneg : 0 ≤ (t^2+B)*(1+B)^3-(t+3*B)^2 := by
    have hmul := mul_nonneg (show 0 ≤ b^2 by positivity) (sub_nonneg.mpr h3)
    dsimp [t, B]
    nlinarith only [hmul]
  linarith

theorem curves_force_sqrt_product_gt_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ k : ℕ, 2 ≤ k → (a + (k : ℝ) * b)^2 ≤ (1+a^2)*(1+b^2)^k)
    (hd : ∀ k : ℕ, 2 ≤ k → (b + (k : ℝ) * a)^2 ≤ (1+b^2)*(1+a^2)^k) :
    1 < a*b := by
  by_contra hn
  have hab : a*b ≤ 1 := le_of_not_gt hn
  by_cases hb1 : b ≤ 1
  · exact curves_small_second_impossible a b ha hb hab hb1 h
  · have ha1 : a ≤ 1 := by
      nlinarith [mul_nonneg ha.le (show 0 ≤ b-1 by linarith)]
    exact curves_small_second_impossible b a hb ha (by nlinarith) ha1 hd

theorem curves_force_XY_gt_one (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (h : ∀ k : ℕ, 2 ≤ k →
      (Real.sqrt X + (k : ℝ) * Real.sqrt Y)^2 ≤ (1+X)*(1+Y)^k)
    (hd : ∀ k : ℕ, 2 ≤ k →
      (Real.sqrt Y + (k : ℝ) * Real.sqrt X)^2 ≤ (1+Y)*(1+X)^k) :
    1 < X*Y := by
  have ha : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hb : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY
  have hsX : (Real.sqrt X)^2 = X := Real.sq_sqrt hX.le
  have hsY : (Real.sqrt Y)^2 = Y := Real.sq_sqrt hY.le
  have hprod := curves_force_sqrt_product_gt_one (Real.sqrt X) (Real.sqrt Y) ha hb
    (by simpa only [hsX, hsY] using h) (by simpa only [hsX, hsY] using hd)
  have hsq : (Real.sqrt X * Real.sqrt Y)^2 = X*Y := by rw [mul_pow, hsX, hsY]
  nlinarith [sq_nonneg (Real.sqrt X * Real.sqrt Y - 1)]

theorem curves_force_shifted_product_gt_one (x y : ℝ) (hx : 1 < x) (hy : 1 < y)
    (h : ∀ k : ℕ, 2 ≤ k →
      (Real.sqrt (x-1) + (k : ℝ) * Real.sqrt (y-1))^2 ≤ x*y^k)
    (hd : ∀ k : ℕ, 2 ≤ k →
      (Real.sqrt (y-1) + (k : ℝ) * Real.sqrt (x-1))^2 ≤ y*x^k) :
    1 < (x-1)*(y-1) := by
  apply curves_force_XY_gt_one (x-1) (y-1) (by linarith) (by linarith)
  · simpa only [show 1+(x-1)=x by ring, show 1+(y-1)=y by ring] using h
  · simpa only [show 1+(x-1)=x by ring, show 1+(y-1)=y by ring] using hd

end AsymmetricTutte
