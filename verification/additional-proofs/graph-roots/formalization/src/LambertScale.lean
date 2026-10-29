import SquareFlowerLambert
import LambertGrowth
import UniformLog
import Mathlib.Data.Real.Sqrt

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Lambert

def epsilon (lam : ℂ) : ℝ := ‖initialCoordinate lam‖ * (1 + (1 / 4 : ℝ) / ‖lam‖)
def reciprocalCoordinate (lam v : ℂ) : ℂ := initialCoordinate lam * (1 + v / lam)

theorem epsilon_nonneg (lam : ℂ) : 0 ≤ epsilon lam := by dsimp [epsilon]; positivity

theorem reciprocalCoordinate_bound (lam v : ℂ) (hv : ‖v‖ ≤ (1 / 4 : ℝ)) :
    ‖reciprocalCoordinate lam v‖ ≤ epsilon lam := by
  dsimp [reciprocalCoordinate, epsilon]
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖1 + v / lam‖ ≤ ‖(1 : ℂ)‖ + ‖v / lam‖ := norm_add_le _ _
    _ = 1 + ‖v‖ / ‖lam‖ := by rw [norm_one, norm_div]
    _ ≤ _ := by gcongr

theorem initialCoordinate_norm (lam : ℂ) :
    ‖initialCoordinate lam‖ = Real.exp (-(lam.re / 2)) := by
  simp [initialCoordinate, Complex.norm_exp, Complex.div_ofReal_re, neg_div]

theorem epsilon_tendsto_zero (L : ℕ → ℝ) (lam : ℕ → ℂ)
    (hL : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => lam n - center (L n)) atTop (𝓝 0)) :
    Tendsto (fun n => epsilon (lam n)) atTop (𝓝 0) := by
  have hreal := (lam_re_tendsto_atTop L lam hL hd).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hinit : Tendsto (fun n => ‖initialCoordinate (lam n)‖) atTop (𝓝 0) := by
    simpa only [initialCoordinate_norm] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hreal
  have hi : Tendsto (fun n => ‖lam n‖⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (lam_norm_tendsto_atTop L lam hL hd)
  have hf : Tendsto (fun n => 1 + (1 / 4 : ℝ) / ‖lam n‖) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hi) :
        Tendsto (fun n => (1 : ℝ) + (1 / 4 : ℝ) * ‖lam n‖⁻¹) atTop (𝓝 (1 + (1 / 4 : ℝ) * 0)))
  simpa only [epsilon, zero_mul] using hinit.mul hf

theorem cubic_scale_square_bound {N a b e L : ℝ} (hN : 0 < N)
    (_ha : 0 ≤ a) (hb0 : 0 ≤ b) (he0 : 0 ≤ e) (_hL0 : 0 ≤ L)
    (he : e ≤ 2 * a) (hab : a ^ 2 = b / (4 * N)) (hb : b ≤ 2 * L) :
    (N * e ^ 3) ^ 2 ≤ 8 * L ^ 3 / N := by
  calc
    (N * e ^ 3) ^ 2 ≤ (N * (2 * a) ^ 3) ^ 2 := by gcongr
    _ = 64 * N ^ 2 * (a ^ 2) ^ 3 := by ring
    _ = 64 * N ^ 2 * (b / (4 * N)) ^ 3 := by rw [hab]
    _ = b ^ 3 / N := by field_simp; ring
    _ ≤ 8 * L ^ 3 / N := by
      apply (div_le_div_iff_of_pos_right hN).2
      have h := pow_le_pow_left₀ hb0 hb 3
      nlinarith

theorem cubic_log_scale_tendsto_zero :
    Tendsto (fun n : ℕ => 8 * logScale n ^ 3 / (n : ℝ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => 4 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
  have hr := (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero.comp hx
  have h : Tendsto (fun n : ℕ => 32 * (Real.log (4 * (n : ℝ)) ^ 3 / (4 * (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hr :
      Tendsto (fun n : ℕ => (32 : ℝ) * (Real.log (4 * (n : ℝ)) ^ 3 / (4 * (n : ℝ)))) atTop (𝓝 (32 * 0)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn).ne'
  dsimp [logScale]
  field_simp
  ring

/-- The actual Lambert coordinate has the cubic scale required by uniform logarithm transfer. -/
theorem epsilon_cubic_scale (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    Tendsto (fun n : ℕ => (n : ℝ) * epsilon (lam n) ^ 3) atTop (𝓝 0) := by
  have hnorm := lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd
  have hupper : ∀ᶠ (n : ℕ) in atTop,
      ((n : ℝ) * epsilon (lam n) ^ 3) ^ 2 ≤ 8 * logScale n ^ 3 / (n : ℝ) := by
    filter_upwards [he, eventually_ge_atTop 1,
      hnorm.eventually_ge_atTop (1 / 4),
      eventually_norm_lam_le logScale lam logScale_tendsto_atTop hd,
      logScale_tendsto_atTop.eventually_ge_atTop 0] with n he hn hnorm hbound hL
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnormpos : 0 < ‖lam n‖ := by linarith
    have hfactor : (1 / 4 : ℝ) / ‖lam n‖ ≤ 1 := (div_le_one hnormpos).2 hnorm
    have heps : epsilon (lam n) ≤ 2 * ‖initialCoordinate (lam n)‖ := by
      dsimp [epsilon]
      nlinarith [norm_nonneg (initialCoordinate (lam n))]
    exact cubic_scale_square_bound hnreal (norm_nonneg _) (norm_nonneg _)
      (epsilon_nonneg _) hL heps (initialCoordinate_norm_square hnpos he) hbound
  have hsq : Tendsto (fun n : ℕ => ((n : ℝ) * epsilon (lam n) ^ 3) ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) hupper cubic_log_scale_tendsto_zero
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (((n : ℝ) * epsilon (lam n) ^ 3) ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hsq.sqrt
  apply hsqrt.congr
  intro n
  exact Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (epsilon_nonneg _) 3))

/-- The scaled logarithmic error vanishes uniformly for the actual Lambert coordinates. -/
theorem uniform_actual_log_remainder (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ (n : ℕ) in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    TendstoUniformlyOn
      (fun (n : ℕ) v => (n : ℂ) *
        (Complex.log (Reciprocal.Q (reciprocalCoordinate (lam n) v)) -
          Complex.log (Reciprocal.P (reciprocalCoordinate (lam n) v)) +
            2 * reciprocalCoordinate (lam n) v ^ 2))
      (fun _ => 0) atTop (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  apply Reciprocal.uniform_scaled_log_remainder
    (fun n v => reciprocalCoordinate (lam n) v) (fun n => epsilon (lam n))
    (epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd)
    (epsilon_cubic_scale lam hd he)
  exact Eventually.of_forall fun n v hv => reciprocalCoordinate_bound _ _
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)

#print axioms uniform_actual_log_remainder

#print axioms reciprocalCoordinate_bound
#print axioms epsilon_tendsto_zero
#print axioms epsilon_cubic_scale
end Lambert
end SquareFlowerCompletion
