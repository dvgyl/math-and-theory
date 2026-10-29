import RootPowerErrors

noncomputable section
namespace SquareFlowerCompletion.RealCompanion
open Set Filter Topology Asymptotics

def endpointPhi : ℝ := (1+Real.sqrt 5)/2

theorem endpointPhi_gt_one : 1 < endpointPhi := by
  dsimp [endpointPhi]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),Real.sqrt_nonneg (5:ℝ)]

theorem endpointPhi_residual_zero : endpointResidual 1 (Real.log endpointPhi) = 0 := by
  have hp : 0 < endpointPhi := lt_trans (by norm_num) endpointPhi_gt_one
  have hs : endpointPhi^2-endpointPhi-1 = 0 := by
    dsimp [endpointPhi]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  dsimp [endpointResidual]
  rw [Real.exp_neg,Real.exp_log hp]
  field_simp [hp.ne']
  nlinarith

theorem endpointTwo_residual_zero : endpointResidual 2 (Real.log 2) = 0 := by
  norm_num [endpointResidual,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 2)]

theorem endpoint_residual_inverse_bound {τ c y : ℝ} (hτ : 0 ≤ τ)
    (hc : 0 ≤ c) (hy : 0 ≤ y) (hzero : endpointResidual τ c = 0) :
    |y-c| ≤ |endpointResidual τ y| := by
  let H : ℝ → ℝ := fun x => endpointResidual τ x-x
  have hH : ∀ x : ℝ, HasDerivAt H (Real.exp x+τ*Real.exp (-x)-1) x := by
    intro x
    have hneg := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
    convert ((((Real.hasDerivAt_exp x).sub_const 1).sub (hneg.const_mul τ)).sub
      (hasDerivAt_id x)) using 1
    dsimp [H,endpointResidual]
    ring
  have hmono : MonotoneOn H (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr (fun x => (hH x).continuousAt)).continuousOn
      (fun x _ => (hH x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hH x).deriv]
    have hx0 : 0 ≤ x := interior_subset hx
    have hExp : 1 ≤ Real.exp x := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hx0
    have hmul := mul_nonneg hτ (Real.exp_pos (-x)).le
    linarith
  rcases le_total c y with hcy | hyc
  · have hm := hmono hc hy hcy
    change endpointResidual τ c-c ≤ endpointResidual τ y-y at hm
    rw [hzero] at hm
    have hR : 0 ≤ endpointResidual τ y := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hcy),abs_of_nonneg hR]
    linarith
  · have hm := hmono hy hc hyc
    change endpointResidual τ y-y ≤ endpointResidual τ c-c at hm
    rw [hzero] at hm
    have hR : endpointResidual τ y ≤ 0 := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hyc),abs_of_nonpos hR]
    linarith

theorem endpoint_recovery_bound {n : ℕ} (hn : 0 < n) {d s c C K : ℝ}
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hdb : d ≤ C/(n:ℝ)) (hs : s = d-d^2)
    (hscaled : |(n:ℝ)*s-c| ≤ K/(n:ℝ)) :
    |d-c/(n:ℝ)| ≤ (K+C^2)/(n:ℝ)^2 := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hsq : d^2 ≤ (C/(n:ℝ))^2 := by
    simpa only [pow_two] using mul_le_mul hdb hdb hd (div_nonneg hC hN.le)
  have hID : d-c/(n:ℝ) = ((n:ℝ)*s-c)/(n:ℝ)+d^2 := by
    rw [hs]
    field_simp [hN.ne']
    ring
  rw [hID]
  calc
    |((n:ℝ)*s-c)/(n:ℝ)+d^2| ≤ |((n:ℝ)*s-c)/(n:ℝ)|+|d^2| := abs_add _ _
    _ = |(n:ℝ)*s-c|/(n:ℝ)+d^2 := by
      rw [abs_div,abs_of_pos hN,abs_of_nonneg (sq_nonneg d)]
    _ ≤ (K/(n:ℝ))/(n:ℝ)+(C/(n:ℝ))^2 :=
      add_le_add (div_le_div_of_nonneg_right hscaled hN.le) hsq
    _ = (K+C^2)/(n:ℝ)^2 := by
      field_simp [hN.ne']
      ring

theorem leftCoordinate_endpoint_error {n : ℕ} (hn : 4 ≤ n) :
    |leftCoordinate n-1-Real.log endpointPhi/(n:ℝ)| ≤
      (104*(Real.log 3)^2+4*Real.log 3)/(n:ℝ)^2 := by
  have hs := leftCoordinate_spec hn
  have hy : 0 ≤ (n:ℝ)*endpointS (leftCoordinate n) :=
    mul_nonneg (Nat.cast_nonneg n) (endpointS_bounds ⟨hs.1.1,by linarith [hs.1.2]⟩).1.le
  have hc : 0 ≤ Real.log endpointPhi := Real.log_nonneg endpointPhi_gt_one.le
  have hi := endpoint_residual_inverse_bound (by norm_num : (0:ℝ) ≤ 1) hc hy
    endpointPhi_residual_zero
  have hscaled := hi.trans (leftCoordinate_residual_bound hn)
  have hC : 0 ≤ 4*Real.log 3 := by positivity
  have hrecover := endpoint_recovery_bound (show 0 < n by omega)
    (sub_nonneg.mpr hs.1.1.le) hC (leftCoordinate_distance_bound hn)
    (show endpointS (leftCoordinate n) = (leftCoordinate n-1)-(leftCoordinate n-1)^2 by
      dsimp [endpointS]; ring) hscaled
  convert hrecover using 1
  ring

theorem rightCoordinate_endpoint_error {n : ℕ} (hn : 4 ≤ n) :
    |rightCoordinate n-2+Real.log 2/(n:ℝ)| ≤
      (104*(Real.log 3)^2+4*Real.log 3)/(n:ℝ)^2 := by
  have hs := rightCoordinate_spec hn
  have hy : 0 ≤ (n:ℝ)*endpointS (rightCoordinate n) :=
    mul_nonneg (Nat.cast_nonneg n) (endpointS_bounds ⟨by linarith [hs.1.1],hs.1.2⟩).1.le
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi := endpoint_residual_inverse_bound (by norm_num : (0:ℝ) ≤ 2) hc hy
    endpointTwo_residual_zero
  have hscaled := hi.trans (rightCoordinate_residual_bound hn)
  have hC : 0 ≤ 4*Real.log 3 := by positivity
  have hrecover := endpoint_recovery_bound (show 0 < n by omega)
    (sub_nonneg.mpr hs.1.2.le) hC (rightCoordinate_distance_bound hn)
    (show endpointS (rightCoordinate n) = (2-rightCoordinate n)-(2-rightCoordinate n)^2 by
      dsimp [endpointS]; ring) hscaled
  rw [show rightCoordinate n-2+Real.log 2/(n:ℝ) =
    -(2-rightCoordinate n-Real.log 2/(n:ℝ)) by ring,abs_neg]
  convert hrecover using 1
  ring

theorem leftCoordinate_endpoint_expansion :
    (fun n : ℕ => leftCoordinate n-1-Real.log endpointPhi/(n:ℝ)) =O[atTop]
      (fun n => ((n:ℝ)^2)⁻¹) := by
  apply IsBigO.of_bound (104*(Real.log 3)^2+4*Real.log 3)
  filter_upwards [eventually_ge_atTop 4] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (n:ℝ))),
    div_eq_mul_inv] using leftCoordinate_endpoint_error hn

theorem rightCoordinate_endpoint_expansion :
    (fun n : ℕ => rightCoordinate n-2+Real.log 2/(n:ℝ)) =O[atTop]
      (fun n => ((n:ℝ)^2)⁻¹) := by
  apply IsBigO.of_bound (104*(Real.log 3)^2+4*Real.log 3)
  filter_upwards [eventually_ge_atTop 4] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (n:ℝ))),
    div_eq_mul_inv] using rightCoordinate_endpoint_error hn

theorem even_leftCoordinate_endpoint_expansion :
    (fun k : ℕ => leftCoordinate (2*k+4)-1-Real.log endpointPhi/((2*k+4:ℕ):ℝ)) =O[atTop]
      (fun k => ((((2*k+4:ℕ):ℝ))^2)⁻¹) := by
  simpa only [Function.comp_def] using leftCoordinate_endpoint_expansion.comp_tendsto even_index_tendsto

theorem even_rightCoordinate_endpoint_expansion :
    (fun k : ℕ => rightCoordinate (2*k+4)-2+Real.log 2/((2*k+4:ℕ):ℝ)) =O[atTop]
      (fun k => ((((2*k+4:ℕ):ℝ))^2)⁻¹) := by
  simpa only [Function.comp_def] using rightCoordinate_endpoint_expansion.comp_tendsto even_index_tendsto

#print axioms endpointPhi_gt_one
#print axioms endpointPhi_residual_zero
#print axioms endpointTwo_residual_zero
#print axioms endpoint_residual_inverse_bound
#print axioms endpoint_recovery_bound
#print axioms leftCoordinate_endpoint_error
#print axioms rightCoordinate_endpoint_error
#print axioms leftCoordinate_endpoint_expansion
#print axioms rightCoordinate_endpoint_expansion
#print axioms even_leftCoordinate_endpoint_expansion
#print axioms even_rightCoordinate_endpoint_expansion
end SquareFlowerCompletion.RealCompanion
