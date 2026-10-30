import FourierCertificates
import FourierSums
import FourierRobustness
import AsymptoticParameters

/-!+# Four-dimensional nonlinear CP cycles for every step product above two

The final theorem quantifies over the genuine step-size product `κ > 2`.
It constructs two finite convex hulls in ordinary Euclidean R4, proves that
they have the saddle `(0,0)`, and proves nonconvergence of the actual globally
defined projection iteration for every extrapolation parameter in one positive
interval. The points, hulls, and initial condition are fixed on that interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

namespace AsymptoticCP

open FiniteCP

theorem spectralD2_eq (N : ℕ) : spectralD2 N = 2 + 2 * Real.sin (angle N) := by
  simp only [spectralD2, mode2Angle, Real.cos_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_sub]
  ring

theorem sin_angle_pos (N : ℕ) : 0 < Real.sin (angle N) := by
  have h := (mode2Angle_bounds N).2
  unfold mode2Angle at h
  exact Real.sin_pos_of_pos_of_lt_pi (angle_pos N) (by linarith [Real.pi_pos])

def thetaRadius (N : ℕ) (κ : ℝ) : ℝ := Real.sin (angle N) ^ 3 / sizeM N κ

theorem thetaRadius_pos (N : ℕ) (κ : ℝ) (hN : 1 ≤ N)
    (hκ : spectralD2 N < κ) : 0 < thetaRadius N κ :=
  div_pos (pow_pos (sin_angle_pos N) _) (sizeM_pos N κ hN hκ)

/-- Every extrapolation parameter in the explicit interval preserves the
actual finite orbit, including all wraparound steps. -/
theorem fourier_family_normal_certificate (N : ℕ) (κ θ : ℝ) (hN : 1 ≤ N)
    (hκ : spectralD2 N < κ) (hsmall : Real.sin (angle N) ≤ 1 / 8)
    (hθ : 0 ≤ θ) (hθr : θ ≤ thetaRadius N κ) :
    NormalCertificate (primalPoints N κ) (dualPoints N κ) κ θ := by
  apply positive_theta_normal_certificate (primalPoints N κ) (dualPoints N κ)
    (lt_trans (spectralD2_pos N) hκ) hθ (sin_angle_pos N).le (sizeM_pos N κ hN hκ)
    hθr
  · intro i
    rfl
  · exact dualPoints_norm_sq N κ hN hκ
  · exact dualPoints_support_bound N κ hN hκ hsmall

theorem fourier_family_nonconvergence (N : ℕ) (κ θ : ℝ) (hN : 1 ≤ N)
    (hκ : spectralD2 N < κ) (hsmall : Real.sin (angle N) ≤ 1 / 8)
    (hθ : 0 ≤ θ) (hθr : θ ≤ thetaRadius N κ) :
    ¬ ∃ w, Filter.Tendsto
      (fun k : ℕ => (cpMap (primalPoints N κ) (dualPoints N κ) κ θ)^[k]
        (primalPoints N κ 0, dualPoints N κ 0)) Filter.atTop (nhds w) := by
  exact certified_nonconvergence (primalPoints N κ) (dualPoints N κ) κ θ
    (fourier_family_normal_certificate N κ θ hN hκ hsmall hθ hθr)
    0 1 (primalPoints_zero_ne_one N κ hN hκ)

theorem fourier_family_periodic (N : ℕ) (κ θ : ℝ) (hN : 1 ≤ N)
    (hκ : spectralD2 N < κ) (hsmall : Real.sin (angle N) ≤ 1 / 8)
    (hθ : 0 ≤ θ) (hθr : θ ≤ thetaRadius N κ) (k : ℕ) :
    (cpMap (primalPoints N κ) (dualPoints N κ) κ θ)^[k + period N]
      (primalPoints N κ 0, dualPoints N κ 0) =
    (cpMap (primalPoints N κ) (dualPoints N κ) κ θ)^[k]
      (primalPoints N κ 0, dualPoints N κ 0) := by
  have hc := fourier_family_normal_certificate N κ θ hN hκ hsmall hθ hθr
  rw [iterate_eq_orbit _ _ _ _ hc, iterate_eq_orbit _ _ _ _ hc]
  exact orbit_periodic _ _ _

/-- For every product `κ > 2`, one fixed pair of compact convex polytopes in
R4 has a saddle point but nonconvergent actual CP iterates for an entire
positive interval of extrapolation parameters. -/
theorem counterexamples_for_every_product_above_two {κ : ℝ} (hκ : 2 < κ) :
    ∃ N : ℕ, 4 ≤ N ∧ ∃ ε : ℝ, 0 < ε ∧
      Convex ℝ (hull (primalPoints N κ)) ∧ IsCompact (hull (primalPoints N κ)) ∧
      Convex ℝ (hull (dualPoints N κ)) ∧ IsCompact (hull (dualPoints N κ)) ∧
      IsSaddle (hull (primalPoints N κ)) (hull (dualPoints N κ)) 0 0 ∧
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ ε →
        (∀ k : ℕ,
          (cpMap (primalPoints N κ) (dualPoints N κ) κ θ)^[k + period N]
            (primalPoints N κ 0, dualPoints N κ 0) =
          (cpMap (primalPoints N κ) (dualPoints N κ) κ θ)^[k]
            (primalPoints N κ 0, dualPoints N κ 0)) ∧
        ¬ ∃ w, Filter.Tendsto
          (fun k : ℕ => (cpMap (primalPoints N κ) (dualPoints N κ) κ θ)^[k]
            (primalPoints N κ 0, dualPoints N κ 0)) Filter.atTop (nhds w) := by
  obtain ⟨N, hN, ht, ht8, hk⟩ := exists_fourier_period hκ
  have hN1 : 1 ≤ N := by omega
  have htsmall : angle N < 1 / 8 := by simpa [angle, period] using ht8
  have hspec : spectralD2 N < κ := by
    rw [spectralD2_eq]
    simpa [angle, period] using hk
  have hsmall : Real.sin (angle N) ≤ 1 / 8 :=
    (Real.sin_le (angle_pos N).le).trans htsmall.le
  refine ⟨N, hN, thetaRadius N κ, thetaRadius_pos N κ hN1 hspec,
    hull_convex _, hull_compact _, hull_convex _, hull_compact _, ?_, ?_⟩
  · exact origin_saddle _ _ (primalPoints_sum_zero N κ hN1) (dualPoints_sum_zero N κ)
  · intro θ hθ hθr
    exact ⟨fourier_family_periodic N κ θ hN1 hspec hsmall hθ hθr,
      fourier_family_nonconvergence N κ θ hN1 hspec hsmall hθ hθr⟩

end AsymptoticCP

#print axioms AsymptoticCP.counterexamples_for_every_product_above_two
