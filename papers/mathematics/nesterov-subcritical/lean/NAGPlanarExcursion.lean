import NAGODELimit
import NAGHilbertModel
import VolterraAcceleration
import FiniteActual
import TimeScaling

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Set

namespace DiscreteNesterov
open NesterovThresholdModel NesterovHilbert

lemma normalGradient_lipschitz (e : PowerExponent) {ε : ℝ}
    (he : 0 < ε) (he1 : ε ≤ 1) : LipschitzWith 1 (normalGradient e ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := mul_le_mul_of_nonneg_left (gradient_dist_le e he x y)
    (div_nonneg (sq_nonneg ε) (by norm_num : (0:ℝ) ≤ 4))
  have heq : ε^2/4*(ε⁻¹*‖x-y‖) = (ε/4)*‖x-y‖ := by
    field_simp
    ring
  rw [heq] at h
  rw [normalGradient, normalGradient, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h.trans (by nlinarith [norm_nonneg (x-y)])

lemma normalGradient_norm_le_two (e : PowerExponent) {ε : ℝ}
    (he : 0 < ε) (he1 : ε ≤ 1) (x : Plane) :
    ‖normalGradient e ε x‖ ≤ 2 := by
  have he2 : ε^2 ≤ 1 := by nlinarith
  have h := mul_le_mul_of_nonneg_left (gradient_norm_le_three e ε x)
    (div_nonneg (sq_nonneg ε) (by norm_num : (0:ℝ) ≤ 4))
  rw [normalGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

lemma normalGradient_coordinate_nonpos (e : PowerExponent) (ε : ℝ) (x : Plane) :
    normalGradient e ε x 0 ≤ 0 := by
  simpa only [normalGradient, PiLp.smul_apply, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (sq_nonneg ε) (by norm_num : (0:ℝ) ≤ 4))
      (gradient_first_nonpos e ε x)

lemma normalGradient_eq_scale (e : PowerExponent) (ε : ℝ) :
    normalGradient e ε = scaleGradient 1 (ε/2) (gradient e ε) := by
  funext x
  simp only [normalGradient, scaleGradient, one_mul, inv_one, one_smul]
  congr 1
  ring

theorem normal_nagX_monotone {r h : ℝ} (hr : 0 < r)
    (e : PowerExponent) (ε : ℝ) (b : Plane) :
    Monotone (fun k => nagX r h (normalGradient e ε) b k 0) := by
  exact nagX_coordinate_monotone hr (normalGradient e ε) b
    (EuclideanSpace.proj 0) (normalGradient_coordinate_nonpos e ε)

/-- A literal canonical Nesterov orbit crosses any prescribed planar threshold.
Both the smooth Moreau parameter and discrete step are chosen here. The ODE
used in the proof exists from the actual gradient and has its singular initial
acceleration established; no trajectory or approximation assumption remains. -/
theorem exists_planar_discrete_excursion (e : PowerExponent) {r M : ℝ}
    (hr : 1 < r) (hpr : e.p * (r-1) ≤ 2) (hM : 2 ≤ M) :
    ∃ ε h : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < h ∧ h ≤ 1 ∧
      (∃ N : ℕ, M < nagX r h (normalGradient e ε) (point 2 1) N 0) ∧
      Monotone (fun N => nagX r h (normalGradient e ε) (point 2 1) N 0) := by
  obtain ⟨ε, he, he1, hexc⟩ :=
    NesterovThreshold.exists_parameter_actual_excursion e hr hpr (M := M+2) (by linarith)
  have hg := normalGradient_lipschitz e he he1
  obtain ⟨q, u, a, hq, hu, ha, hq0, hu0, _ha0, hqd, hud, hode⟩ :=
    GeneralNesterovExistence.exists_global_nesterov_with_acceleration hr
      (normalGradient e ε) hg (normalGradient_norm_le_two e he he1) (point 2 1)
  have hhalf : 0 < ε/2 := by positivity
  have hqinitial : q 0 = (1:ℝ) • point 2 1 := by simpa using hq0
  obtain ⟨hQ0, hU0⟩ := rescaled_initial (by norm_num : (0:ℝ)<1)
    (ε := ε/2) hqinitial hu0
  have hqn : ∀ t>0, HasDerivAt q (u t) t := fun t ht => hqd t ht.le
  have hun : ∀ t>0, HasDerivAt u
      (-(r/t) • u t-scaleGradient 1 (ε/2) (gradient e ε) (q t)) t := by
    intro t ht
    have hd := hud t ht
    rw [hode t ht, normalGradient_eq_scale] at hd
    exact hd
  have hQd : ∀ t>0, HasDerivAt (rescaledPosition 1 (ε/2) q)
      (rescaledVelocity 1 (ε/2) u t) t :=
    fun t ht => rescaled_position_deriv (by norm_num) hhalf ht hqn
  have hUd : ∀ t>0, HasDerivAt (rescaledVelocity 1 (ε/2) u)
      (-(r/t) • rescaledVelocity 1 (ε/2) u t -
        gradient e ε (rescaledPosition 1 (ε/2) q t)) t :=
    fun t ht => rescaled_velocity_deriv (by norm_num) hhalf ht hun
  obtain ⟨⟨s, hs0, hs⟩, _hmono⟩ := hexc
    (rescaledPosition 1 (ε/2) q) (rescaledVelocity 1 (ε/2) u)
    (rescaled_position_continuous hq).continuousOn
    (rescaled_velocity_continuous hu).continuousOn hQd hUd hQ0 hU0
  have hspos : 0 < s := by
    by_contra hn
    have hsze : s=0 := le_antisymm (le_of_not_gt hn) hs0
    rw [hsze, hQ0, point_first] at hs
    linarith
  let T : ℝ := (ε/2)⁻¹*s
  have hT : 0 < T := by dsimp [T]; positivity
  have hqT : M+2 < q T 0 := by
    simpa only [rescaledPosition, inv_one, one_smul] using hs
  obtain ⟨h, N, hh, hh1, _hgrid, hclose⟩ := finite_horizon_approximation
    (by linarith : 0<r) hT (by norm_num : (0:ℝ)<1)
    (normalGradient e ε) hg (point 2 1) q u a hq hu ha hq0 hu0 hqn hud hode
  have hcoord : |nagX r h (normalGradient e ε) (point 2 1) (N+1) 0-q T 0| ≤ 1 := by
    have hn := PiLp.norm_apply_le
      (nagX r h (normalGradient e ε) (point 2 1) (N+1)-q T) 0
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hn.trans hclose
  have hcross : M < nagX r h (normalGradient e ε) (point 2 1) (N+1) 0 := by
    have hl := (abs_le.mp hcoord).1
    linarith
  exact ⟨ε, h, he, he1, hh, hh1, ⟨N+1, hcross⟩,
    normal_nagX_monotone (by linarith) e ε (point 2 1)⟩

theorem exists_exponent_all_discrete_excursions {r : ℝ}
    (hr : 1 < r) (hr3 : r < 3) :
    ∃ e : PowerExponent, ∀ M : ℝ, 2 ≤ M →
      ∃ ε h : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < h ∧ h ≤ 1 ∧
        (∃ N : ℕ, M < nagX r h (normalGradient e ε) (point 2 1) N 0) ∧
        Monotone (fun N => nagX r h (normalGradient e ε) (point 2 1) N 0) := by
  obtain ⟨e, he⟩ := NesterovThresholdModel.exists_powerExponent hr3
  exact ⟨e, fun M hM => exists_planar_discrete_excursion e hr he hM⟩

#print axioms finite_horizon_approximation
#print axioms exists_planar_discrete_excursion
#print axioms exists_exponent_all_discrete_excursions

end DiscreteNesterov
