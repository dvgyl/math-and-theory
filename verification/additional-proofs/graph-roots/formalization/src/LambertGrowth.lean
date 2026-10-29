import LambertCenter

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Lambert

theorem lam_re_tendsto_atTop (L : ℕ → ℝ) (lam : ℕ → ℂ)
    (hL : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => lam n - center (L n)) atTop (𝓝 0)) :
    Tendsto (fun n => (lam n).re) atTop atTop := by
  have hc : Tendsto (fun n => (center (L n)).re - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1) (center_re_tendsto_atTop L hL)
  have hn : Tendsto (fun n => ‖lam n - center (L n)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hd.norm
  apply tendsto_atTop_mono' atTop _ hc
  filter_upwards [hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  have h := Complex.abs_re_le_norm (lam n - center (L n))
  have hneg := neg_abs_le (lam n - center (L n)).re
  simp only [Complex.sub_re] at h hneg
  linarith

theorem lam_norm_tendsto_atTop (L : ℕ → ℝ) (lam : ℕ → ℂ)
    (hL : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => lam n - center (L n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖lam n‖) atTop atTop :=
  tendsto_atTop_mono (fun n => Complex.re_le_norm (lam n)) (lam_re_tendsto_atTop L lam hL hd)

theorem eventually_norm_lam_le (L : ℕ → ℝ) (lam : ℕ → ℂ)
    (hL : Tendsto L atTop atTop)
    (hd : Tendsto (fun n => lam n - center (L n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ‖lam n‖ ≤ 2 * L n := by
  have hn : Tendsto (fun n => ‖lam n - center (L n)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hd.norm
  filter_upwards [hL.eventually_ge_atTop (Real.pi + 1),
    hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hlarge hsmall
  have hL1 : 1 ≤ L n := by linarith [Real.pi_pos]
  have hL0 : 0 ≤ L n := by linarith
  have hlog0 : 0 ≤ Real.log (L n) := Real.log_nonneg hL1
  have ha : 0 ≤ L n - Real.log (L n) := by linarith [Real.log_le_self hL0]
  have hc : ‖center (L n)‖ ≤ L n + Real.pi := by
    calc
      ‖center (L n)‖ ≤ ‖((L n - Real.log (L n) : ℝ) : ℂ)‖ +
          ‖(Real.pi : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = L n - Real.log (L n) + Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      _ ≤ _ := by linarith
  have htri := norm_add_le (lam n - center (L n)) (center (L n))
  rw [sub_add_cancel] at htri
  linarith

#print axioms lam_re_tendsto_atTop
#print axioms lam_norm_tendsto_atTop
#print axioms eventually_norm_lam_le
end Lambert
end SquareFlowerCompletion
