import AsymmetricTutte.Scalar

/-! An explicit admissible point with one parameter smaller than two. -/

namespace AsymmetricTutte

private lemma fast_power_bound (k : ℕ) (hk : 2 ≤ k) :
    1 + 14 * (k : ℝ) ^ 2 ≤ (3 / 2 : ℝ) * 8 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hp : 1 + 14 * ((k : ℝ) + 1) ^ 2 ≤ 8 * (1 + 14 * (k : ℝ) ^ 2) := by
      nlinarith only [hk2, sq_nonneg ((k : ℝ) - 1)]
    calc
      1 + 14 * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 8 * (1 + 14 * (k : ℝ) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hp
      _ ≤ 8 * ((3 / 2 : ℝ) * 8 ^ k) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (3 / 2 : ℝ) * 8 ^ (k + 1) := by rw [pow_succ]; ring

private lemma slow_power_bound (k : ℕ) (hk : 2 ≤ k) :
    14 + (k : ℝ) ^ 2 ≤ 8 * (3 / 2 : ℝ) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : 14 + ((k : ℝ) + 1) ^ 2 ≤ (3 / 2 : ℝ) * (14 + (k : ℝ) ^ 2) := by
      nlinarith only [sq_nonneg ((k : ℝ) - 2)]
    calc
      14 + ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (3 / 2 : ℝ) * (14 + (k : ℝ) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hp
      _ ≤ (3 / 2 : ℝ) * (8 * (3 / 2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 8 * (3 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- A concrete point of the universal region with first parameter less than two. -/
theorem region_three_halves_eight : Region (3 / 2) 8 := by
  have ha : (Real.sqrt ((3 / 2 : ℝ) - 1)) ^ 2 = 1 / 2 := by
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hb : (Real.sqrt ((8 : ℝ) - 1)) ^ 2 = 7 := by
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hc (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
    nlinarith only [sq_nonneg (u - v)]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro k hk
    have h := hc (Real.sqrt ((3 / 2 : ℝ) - 1))
      ((k : ℝ) * Real.sqrt ((8 : ℝ) - 1))
    rw [mul_pow, ha, hb] at h
    have hbnd := fast_power_bound k hk
    nlinarith only [h, hbnd]
  · intro k hk
    have h := hc (Real.sqrt ((8 : ℝ) - 1))
      ((k : ℝ) * Real.sqrt ((3 / 2 : ℝ) - 1))
    rw [mul_pow, ha, hb] at h
    have hbnd := slow_power_bound k hk
    nlinarith only [h, hbnd]

end AsymmetricTutte
