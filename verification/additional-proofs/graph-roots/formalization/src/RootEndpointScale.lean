import RootMotion
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

noncomputable section
namespace SquareFlowerCompletion.RealCompanion
open Set Filter Topology Asymptotics

def endpointS (t : ℝ) : ℝ := (t-1)*(2-t)

theorem endpointS_bounds {t : ℝ} (ht : t ∈ Ioo 1 2) :
    0 < endpointS t ∧ endpointS t ≤ 1/4 := by
  constructor
  · exact mul_pos (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
  · dsimp [endpointS]
    nlinarith [sq_nonneg (t-3/2)]

theorem a_eq_one_sub_endpointS (t : ℝ) : a t = 1-endpointS t := by
  dsimp [a,endpointS]
  ring

theorem F_root_endpoint_equation {n : ℕ} {t : ℝ} (hF : F n t = 0) :
    (1+endpointS t)^n = 1+t*(1-endpointS t)^n := by
  rw [F,a_eq_one_sub_endpointS] at hF
  have h : 2-(1-endpointS t) = 1+endpointS t := by ring
  rw [h] at hF
  linarith

theorem log_one_add_lower_half {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s/2 ≤ Real.log (1+s) := by
  have hpos : 0 < 1+s := by linarith
  have hinv : (1+s)⁻¹ ≤ 1-s/2 := by
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

theorem root_scaled_endpointS_bound {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioo 1 2) (hF : F n t = 0) :
    (n:ℝ)*endpointS t ≤ 2*Real.log 3 := by
  have hs := endpointS_bounds ht
  have hEq := F_root_endpoint_equation hF
  have ha0 : 0 ≤ 1-endpointS t := by linarith [hs.2]
  have hpow : (1-endpointS t)^n ≤ 1 := pow_le_one₀ ha0 (by linarith [hs.1])
  have hprod := mul_le_mul_of_nonneg_left hpow (by linarith [ht.1] : 0 ≤ t)
  have hbound : (1+endpointS t)^n ≤ 3 := by rw [hEq]; nlinarith [ht.2]
  have hlog := Real.log_le_log (pow_pos (by linarith [hs.1] : 0 < 1+endpointS t) n) hbound
  rw [Real.log_pow] at hlog
  have hlow := log_one_add_lower_half hs.1.le (by linarith [hs.2] : endpointS t ≤ 1)
  have hmul := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith

theorem leftCoordinate_distance_bound {n : ℕ} (hn : 4 ≤ n) :
    leftCoordinate n-1 ≤ 4*Real.log 3/(n:ℝ) := by
  have hs := leftCoordinate_spec hn
  have ht : leftCoordinate n ∈ Ioo 1 2 := ⟨hs.1.1,by linarith [hs.1.2]⟩
  have hscale := root_scaled_endpointS_bound ht hs.2
  have hdist : leftCoordinate n-1 ≤ 2*endpointS (leftCoordinate n) := by
    have hp := mul_nonneg (sub_nonneg.mpr hs.1.1.le)
      (by linarith [hs.1.2] : 0 ≤ 3-2*leftCoordinate n)
    dsimp [endpointS]
    nlinarith
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ hN).mpr
  have hm := mul_le_mul_of_nonneg_left hdist hN.le
  nlinarith

theorem rightCoordinate_distance_bound {n : ℕ} (hn : 4 ≤ n) :
    2-rightCoordinate n ≤ 4*Real.log 3/(n:ℝ) := by
  have hs := rightCoordinate_spec hn
  have ht : rightCoordinate n ∈ Ioo 1 2 := ⟨by linarith [hs.1.1],hs.1.2⟩
  have hscale := root_scaled_endpointS_bound ht hs.2
  have hdist : 2-rightCoordinate n ≤ 2*endpointS (rightCoordinate n) := by
    have hp := mul_nonneg (by linarith [hs.1.1] : 0 ≤ 2*rightCoordinate n-3)
      (sub_nonneg.mpr hs.1.2.le)
    dsimp [endpointS]
    nlinarith
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ hN).mpr
  have hm := mul_le_mul_of_nonneg_left hdist hN.le
  nlinarith

theorem leftCoordinate_distance_bigO :
    (fun n : ℕ => leftCoordinate n-1) =O[atTop] (fun n => (n:ℝ)⁻¹) := by
  apply IsBigO.of_bound (4*Real.log 3)
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hd : 0 < leftCoordinate n-1 := sub_pos.mpr (leftCoordinate_spec hn).1.1
  simpa only [Real.norm_eq_abs,abs_of_pos hd,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ) ≤ n)),div_eq_mul_inv] using
      leftCoordinate_distance_bound hn

theorem rightCoordinate_distance_bigO :
    (fun n : ℕ => 2-rightCoordinate n) =O[atTop] (fun n => (n:ℝ)⁻¹) := by
  apply IsBigO.of_bound (4*Real.log 3)
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hd : 0 < 2-rightCoordinate n := sub_pos.mpr (rightCoordinate_spec hn).1.2
  simpa only [Real.norm_eq_abs,abs_of_pos hd,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ) ≤ n)),div_eq_mul_inv] using
      rightCoordinate_distance_bound hn

#print axioms endpointS_bounds
#print axioms a_eq_one_sub_endpointS
#print axioms F_root_endpoint_equation
#print axioms log_one_add_lower_half
#print axioms root_scaled_endpointS_bound
#print axioms leftCoordinate_distance_bound
#print axioms rightCoordinate_distance_bound
#print axioms leftCoordinate_distance_bigO
#print axioms rightCoordinate_distance_bigO
end SquareFlowerCompletion.RealCompanion
