import DerivativeB
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

theorem norm_Pprime_le {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) : ‖3 + 6 * w‖ ≤ 4 := by
  have h := norm_add_le (3 : ℂ) (6 * w)
  norm_num [norm_mul] at h
  linarith

theorem norm_BD_le {n : ℕ} (hn : 0 < n) {lam v : ℂ}
    (hw : ‖reciprocalCoordinate lam v‖ ≤ (1 / 16 : ℝ))
    (hc : ‖initialCoordinate lam / lam‖ ≤ 1) :
    ‖BD n lam v‖ ≤ 4 * (n : ℝ) * (1 / 128 : ℝ) ^ n := by
  let w := reciprocalCoordinate lam v
  obtain ⟨hps, hqs⟩ := slitPlane_bounds hw
  obtain ⟨hp, hq⟩ := denominator_bounds hw
  have hp0 := Complex.slitPlane_ne_zero hps
  have hpr := norm_Pprime_le hw
  have hrat : ‖w‖ ^ (2 * n) / ‖P w‖ ^ n ≤ (1 / 128 : ℝ) ^ n := by
    calc
      _ ≤ (1 / 16 : ℝ) ^ (2 * n) / (1 / 2 : ℝ) ^ n := by gcongr
      _ = (1 / 128 : ℝ) ^ n := by rw [pow_mul, ← div_pow]; norm_num
  have ht : ‖(n : ℂ) * w * (3 + 6 * w) / P w‖ ≤ (n : ℝ) / 2 := by
    calc
      _ = (n : ℝ) * ‖w‖ * ‖3 + 6 * w‖ / ‖P w‖ := by simp only [norm_div, norm_mul, Complex.norm_natCast]
      _ ≤ (n : ℝ) * (1 / 16 : ℝ) * 4 / (1 / 2 : ℝ) := by gcongr
      _ = _ := by ring
  have hnat : ‖2 * (n : ℂ) + 1‖ = 2 * (n : ℝ) + 1 := by
    have heq : 2 * (n : ℂ) + 1 = ((2 * n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_natCast]
    push_cast
    rfl
  have hbracket : ‖(2 * (n : ℂ) + 1) - (n : ℂ) * w * (3 + 6 * w) / P w‖ ≤ 4 * (n : ℝ) := by
    have h := norm_sub_le (2 * (n : ℂ) + 1) ((n : ℂ) * w * (3 + 6 * w) / P w)
    rw [hnat] at h
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
    linarith
  have hexp : Complex.exp (-((n : ℂ) * Complex.log (P w))) = (P w ^ n)⁻¹ := by
    rw [Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_log hp0]
  calc
    ‖BD n lam v‖ = ‖initialCoordinate lam / lam‖ *
        (‖w‖ ^ (2 * n) / ‖P w‖ ^ n) *
          ‖(2 * (n : ℂ) + 1) - (n : ℂ) * w * (3 + 6 * w) / P w‖ := by
      dsimp [BD]
      change ‖(initialCoordinate lam / lam) * w ^ (2 * n) *
        Complex.exp (-((n : ℂ) * Complex.log (P w))) *
          ((2 * (n : ℂ) + 1) - (n : ℂ) * w * (3 + 6 * w) / P w)‖ = _
      rw [hexp]
      simp only [norm_mul, norm_pow, norm_inv, div_eq_mul_inv]
      ring
    _ ≤ 1 * (1 / 128 : ℝ) ^ n * (4 * (n : ℝ)) := by gcongr
    _ = _ := by ring

theorem uniform_BD (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n v => BD n (lam n) v) (fun _ => 0) atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have hε := epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd
  have hre := (lam_re_tendsto_atTop logScale lam logScale_tendsto_atTop hd).atTop_div_const
    (by norm_num : (0 : ℝ) < 2)
  have hinit : Tendsto (fun n => ‖initialCoordinate (lam n)‖) atTop (𝓝 0) := by
    simpa only [initialCoordinate_norm] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hre
  have hi : Tendsto (fun n => ‖lam n‖⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd)
  have hc : Tendsto (fun n => ‖initialCoordinate (lam n) / lam n‖) atTop (𝓝 0) := by
    simpa only [norm_div, norm_mul, norm_inv, div_eq_mul_inv, zero_mul] using hinit.mul hi
  have hgeo : Tendsto (fun n : ℕ => 4 * (n : ℝ) * (1 / 128 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 128) (by norm_num : (1 / 128 : ℝ) < 1)) :
        Tendsto (fun n : ℕ => (4 : ℝ) * ((n : ℝ) * (1 / 128 : ℝ) ^ n)) atTop (𝓝 (4 * 0)))
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  filter_upwards [eventually_ge_atTop 1,
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hgeo.eventually (gt_mem_nhds hη)] with n hn hεn hcn hgn v hv
  have hvnorm : ‖v‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hw : ‖reciprocalCoordinate (lam n) v‖ ≤ (1 / 16 : ℝ) :=
    (reciprocalCoordinate_bound _ _ hvnorm).trans hεn.le
  simpa only [dist_eq_norm, zero_sub, norm_neg] using
    (norm_BD_le (lt_of_lt_of_le Nat.zero_lt_one hn) hw hcn.le).trans_lt hgn

#print axioms norm_BD_le
#print axioms uniform_BD
end Transfer
end SquareFlowerCompletion
