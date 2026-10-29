import RootScale
import NonzeroRoots
import RadiusActual

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

theorem logScale_mul_epsilon_tendsto_zero (lam : ℕ → ℂ)
    (hd : Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0))
    (he : ∀ᶠ n : ℕ in atTop, lam n * Complex.exp (lam n) = -(4 * (n : ℂ))) :
    Tendsto (fun n => logScale n * epsilon (lam n)) atTop (𝓝 0) := by
  have hnorm := lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd
  have hb : ∀ᶠ n : ℕ in atTop,
      (logScale n * epsilon (lam n))^2 ≤ 8 * logScale n^3 / (n : ℝ) := by
    filter_upwards [he, eventually_ge_atTop 1, hnorm.eventually_ge_atTop (1/4),
      eventually_norm_lam_le logScale lam logScale_tendsto_atTop hd,
      logScale_tendsto_atTop.eventually_ge_atTop 0] with n he hn hnorm hu hL
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnormpos : 0 < ‖lam n‖ := by linarith
    have hf : (1/4 : ℝ) / ‖lam n‖ ≤ 1 := (div_le_one hnormpos).2 hnorm
    have heps : epsilon (lam n) ≤ 2 * ‖initialCoordinate (lam n)‖ := by
      dsimp [epsilon]
      nlinarith [norm_nonneg (initialCoordinate (lam n))]
    calc
      (logScale n * epsilon (lam n))^2 ≤ (logScale n * (2*‖initialCoordinate (lam n)‖))^2 := by
        gcongr
        exact mul_nonneg hL (epsilon_nonneg _)
      _ = 4 * logScale n^2 * (‖lam n‖ / (4*(n:ℝ))) := by
        rw [mul_pow, mul_pow, initialCoordinate_norm_square hnpos he]
        ring
      _ ≤ 4 * logScale n^2 * (2*logScale n / (4*(n:ℝ))) := by gcongr
      _ = 2 * logScale n^3 / (n:ℝ) := by ring
      _ ≤ 8 * logScale n^3 / (n:ℝ) := by gcongr; norm_num
  have hs := squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) hb cubic_log_scale_tendsto_zero
  have ha : Tendsto (fun n => |logScale n * epsilon (lam n)|) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hs.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr ha

/-- Actual graph roots with additive reciprocal-square precision. -/
theorem exists_actual_graph_roots_with_scale : ∃ z : ℕ → ℂ,
    (∀ᶠ n : ℕ in atTop, z n ≠ 0 ∧ (Counting.complexDominationPolynomial n).eval (z n) = 0) ∧
    Tendsto (fun n : ℕ => 4*(n:ℝ)/‖z n‖^2 - (logScale n - Real.log (logScale n))) atTop (𝓝 0) := by
  obtain ⟨lam,v,z,hd,hv,hz,he⟩ := exists_actual_graph_roots
  refine ⟨z, he.mono (fun n h => ⟨h.1,h.2.1⟩), ?_⟩
  have h := reciprocal_scale_tendsto_zero lam v hd (he.mono fun n h => h.2.2) hv
  simpa only [hz] using h

end Transfer
namespace Extremal
open Lambert Reciprocal Transfer

theorem shifted_reciprocal_lower {N T L r e : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hTL : T ≤ L) (hr : 4 ≤ r)
    (hb : T ≤ 4*N/(r-3)^2) (hi : 1/r ≤ e) :
    T - 6*L*e ≤ 4*N/r^2 := by
  have hrpos : 0 < r := by linarith
  have hr3pos : 0 < r-3 := by linarith
  have hb' := (le_div_iff₀ (sq_pos_of_pos hr3pos)).mp hb
  have heq : (T - 6*T/r)*r^2 = T*(r-3)^2 - 9*T := by
    field_simp
    ring
  have hlower : T - 6*T/r ≤ 4*N/r^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hrpos)).2
    rw [heq]
    linarith
  have hsmall : T/r ≤ L*e := by
    calc
      T/r ≤ L/r := div_le_div_of_nonneg_right hTL hrpos.le
      _ = L*(1/r) := by ring
      _ ≤ L*e := mul_le_mul_of_nonneg_left hi hL
  calc
    T - 6*L*e ≤ T - 6*(T/r) := by nlinarith [hsmall]
    _ = T - 6*T/r := by ring
    _ ≤ _ := hlower

/-- The maximal modulus of the complete actual graph root set has additive precision. -/
theorem radius_reciprocal_square_asymptotic :
    Tendsto (fun n : ℕ => 4*(n:ℝ)/(radius n)^2 -
      (Real.log (4*(n:ℝ)) - Real.log (Real.log (4*(n:ℝ))))) atTop (𝓝 0) := by
  obtain ⟨lam,v,z,hd,hv,hz,he⟩ := exists_actual_graph_roots
  have hle := he.mono fun n h => h.2.2
  have hzscale := reciprocal_scale_tendsto_zero lam v hd hle hv
  have hzscale' : Tendsto (fun n : ℕ => 4*(n:ℝ)/‖z n‖^2 -
      (logScale n - Real.log (logScale n))) atTop (𝓝 0) := by
    simpa only [hz] using hzscale
  have heps := epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd
  have hlogeps := logScale_mul_epsilon_tendsto_zero lam hd hle
  have hvnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by simpa only [norm_zero] using hv.norm
  have hb : ∀ᶠ n : ℕ in atTop,
      -(6 * (logScale n * epsilon (lam n))) ≤
        4*(n:ℝ)/(radius n)^2 - (logScale n - Real.log (logScale n)) ∧
      4*(n:ℝ)/(radius n)^2 - (logScale n - Real.log (logScale n)) ≤
        4*(n:ℝ)/‖z n‖^2 - (logScale n - Real.log (logScale n)) := by
    filter_upwards [he, eventually_ge_atTop 1, logScale_tendsto_atTop.eventually_ge_atTop 1,
      hvnorm.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
      heps.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))] with n he hn hL hvn hen
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hzpos : 0 < ‖z n‖ := norm_pos_iff.mpr he.1
    have hrpos := radius_pos hnpos
    have hzle : ‖z n‖ ≤ radius n := norm_le_radius he.2.1
    have hwbound : ‖reciprocalCoordinate (lam n) (v n)‖ ≤ epsilon (lam n) :=
      reciprocalCoordinate_bound _ _ hvn.le
    have hzinv : 1/‖z n‖ = ‖reciprocalCoordinate (lam n) (v n)‖ := by
      rw [hz, norm_inv, one_div, inv_inv]
    have hinv : 1/(radius n) ≤ epsilon (lam n) := by
      calc
        1/(radius n) ≤ 1/‖z n‖ := one_div_le_one_div_of_le hzpos hzle
        _ ≤ epsilon (lam n) := by rw [hzinv]; exact hwbound
    have hr : 4 ≤ radius n := by
      have hi : 1/(radius n) < 1/4 := hinv.trans_lt hen
      have hmul := (div_lt_div_iff₀ hrpos (by norm_num : (0:ℝ)<4)).mp hi
      linarith
    have hlog0 : 0 ≤ Real.log (logScale n) := Real.log_nonneg hL
    have hlogle : Real.log (logScale n) ≤ logScale n - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have hT : 0 ≤ logScale n - Real.log (logScale n) := by linarith
    obtain ⟨zr,hzr,hrnorm⟩ := radius_attained n
    have hmaxbound : logScale n - Real.log (logScale n) ≤ 4*(n:ℝ)/(radius n-3)^2 := by
      have h := Radius.actual_graph_root_radius_bound n zr hnpos hzr (hrnorm.symm ▸ hr) hL
      simpa only [hrnorm, logScale] using h
    have hlower := shifted_reciprocal_lower hT (by linarith : 0 ≤ logScale n)
      (by linarith : logScale n - Real.log (logScale n) ≤ logScale n) hr hmaxbound hinv
    have hupper : 4*(n:ℝ)/(radius n)^2 ≤ 4*(n:ℝ)/‖z n‖^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hzpos)
        (pow_le_pow_left₀ (norm_nonneg _) hzle 2)
    constructor <;> linarith
  have hlow : Tendsto (fun n => -(6*(logScale n * epsilon (lam n)))) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero, neg_zero] using (hlogeps.const_mul 6).neg
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hzscale'
    (hb.mono fun n h => h.1) (hb.mono fun n h => h.2)
  simpa only [logScale] using hlim

#print axioms shifted_reciprocal_lower
#print axioms radius_reciprocal_square_asymptotic
end Extremal
end SquareFlowerCompletion
