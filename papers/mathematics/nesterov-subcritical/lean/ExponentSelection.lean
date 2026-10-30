import PowerAlgebra

set_option autoImplicit false

namespace NesterovThresholdModel

/-- Every strictly subcritical damping admits an even polynomial dual body
whose conjugate exponent supplies the required energy inequality. -/
theorem exists_powerExponent {r : ℝ} (hr : r < 3) :
    ∃ q : PowerExponent, q.p * (r - 1) ≤ 2 := by
  have hgap : 0 < 3 - r := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / (3 - r))
  let q : PowerExponent := ⟨2 * (m + 1), even_two_mul _, by omega⟩
  have hqn : (q.n : ℝ) = 2 * (m + 1) := by simp [q]
  have hqge : (m : ℝ) ≤ q.n := by
    rw [hqn]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hproduct : 2 < (q.n : ℝ) * (3 - r) := by
    have hx := (div_lt_iff₀ hgap).mp hm
    have hy := mul_le_mul_of_nonneg_right hqge hgap.le
    linarith
  have hpred : 0 < (q.n : ℝ) - 1 := by
    have hn : (2 : ℝ) ≤ q.n := by exact_mod_cast q.two_le
    linarith
  refine ⟨q, ?_⟩
  apply (mul_le_mul_right hpred).mp
  have hid := q.p_mul_pred
  calc
    q.p * (r - 1) * ((q.n : ℝ) - 1) = (r - 1) * (q.p * ((q.n : ℝ) - 1)) := by ring
    _ = (r - 1) * q.n := by rw [hid]
    _ ≤ 2 * ((q.n : ℝ) - 1) := by nlinarith

#print axioms exists_powerExponent

end NesterovThresholdModel
