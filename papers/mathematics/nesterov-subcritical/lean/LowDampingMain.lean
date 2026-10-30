import LowDampingTrajectory

/-! Optional classical low-damping branch, independent of the frozen Hilbert
counterexample. The central novelty claim does not depend on this file. -/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace NesterovLowDamping
variable {r : ℝ}

def objective (r x : ℝ) : ℝ := potential r x / 64
def gradient (r x : ℝ) : ℝ := -force r x / 64
def scaledPosition (r t : ℝ) : ℝ := position r (t/8)
def scaledVelocity (r t : ℝ) : ℝ := velocity r (t/8)/8

lemma objective_gradient (hr : 0<r) (hr1 : r≤1) (x : ℝ) :
    HasGradientAt (objective r) (gradient r x) x := by
  have h := (potential_hasDerivAt hr hr1 x).div_const 64
  simpa only [objective, gradient] using h.hasGradientAt

lemma objective_convex (hr : 0<r) (hr1 : r≤1) :
    ConvexOn ℝ univ (objective r) := by
  have h := (potential_convex hr hr1).smul (by norm_num : (0:ℝ)≤1/64)
  simpa only [objective, smul_eq_mul, div_eq_mul_inv, mul_comm, one_mul] using h

lemma gradient_lipschitz (hr : 0<r) (hr1 : r≤1) :
    LipschitzWith 1 (gradient r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (force_lipschitz hr hr1).dist_le_mul x y
  simp only [NNReal.coe_ofNat, Real.dist_eq] at h
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, gradient]
  have he : -force r x/64- -force r y/64= -(force r x-force r y)/64 := by ring
  rw [he, abs_div, abs_neg]
  norm_num
  nlinarith [abs_nonneg (x-y)]

lemma force_upper (hr : 0<r) (hr1 : r≤1) (x : ℝ) : force r x≤4 := by
  have hb := beta_bounds hr hr1
  have hs := (root_bounds hr hr1 x).2.1
  have hn : 0≤(1-root r x)/(2*beta r) :=
    div_nonneg (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_left (show 1-(1-root r x)/(2*beta r)≤1 by linarith)
    (show 0≤2*(r+1) by positivity)
  unfold force
  nlinarith

lemma gradient_bound (hr : 0<r) (hr1 : r≤1) (x : ℝ) : ‖gradient r x‖≤2 := by
  have h0 := force_nonneg hr hr1 x
  have h1 := force_upper hr hr1 x
  simp only [gradient, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg h0]
  norm_num
  linarith

lemma scaledPosition_derivative (hr : 0<r) (t : ℝ) :
    HasDerivAt (scaledPosition r) (scaledVelocity r t) t := by
  have h := (position_hasDerivAt hr (t/8)).comp t ((hasDerivAt_id t).div_const 8)
  simpa only [scaledPosition, scaledVelocity, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h

lemma scaledVelocity_derivative (hr : 0<r) (hr1 : r≤1) {t : ℝ} (ht : 0<t) :
    HasDerivAt (scaledVelocity r)
      (-(r/t)*scaledVelocity r t-gradient r (scaledPosition r t)) t := by
  have h := ((velocity_hasDerivAt hr (t/8)).comp t
    ((hasDerivAt_id t).div_const 8)).div_const 8
  have ht8 : 0<t/8 := by positivity
  have he : acceleration r (t/8)*(1/8)/8=
      -(r/t)*scaledVelocity r t-gradient r (scaledPosition r t) := by
    rw [ode_identity hr hr1 ht8]
    unfold scaledVelocity gradient scaledPosition
    field_simp
    ring
  simpa only [scaledVelocity, Function.comp_def, id_eq, he] using h

lemma scaledPosition_tendsto (hr : 0<r) (hr1 : r≤1) :
    Tendsto (scaledPosition r) atTop atTop :=
  (position_tendsto hr hr1).comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<8))

/-- A one-dimensional C1,1 counterexample in the classical low-damping range.
The construction is explicit and includes zero initial velocity and genuine
derivatives at the singular initial time. This theorem is not a novelty claim. -/
theorem exists_low_damping_escape (hr : 0<r) (hr1 : r≤1) :
    ∃ (F G X V : ℝ → ℝ) (z : ℝ),
      ConvexOn ℝ univ F ∧
      (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖≤2) ∧
      F z=0 ∧ (∀ x, 0≤F x) ∧
      Continuous X ∧ Continuous V ∧ X 0=0 ∧ V 0=0 ∧
      (∀ t≥0, HasDerivAt X (V t) t) ∧
      (∀ t>0, HasDerivAt V (-(r/t)*V t-G (X t)) t) ∧
      Tendsto X atTop atTop := by
  refine ⟨objective r,gradient r,scaledPosition r,scaledVelocity r,edge r,
    objective_convex hr hr1,objective_gradient hr hr1,gradient_lipschitz hr hr1,
    gradient_bound hr hr1,?_,?_,?_,?_,?_,?_,?_,?_,scaledPosition_tendsto hr hr1⟩
  · simp [objective]
  · intro x
    exact div_nonneg (potential_nonneg hr hr1 x) (by norm_num)
  · exact continuous_iff_continuousAt.mpr (fun t => (scaledPosition_derivative hr t).continuousAt)
  · have hu : Continuous (velocity r) :=
      continuous_iff_continuousAt.mpr (fun t => (velocity_hasDerivAt hr t).continuousAt)
    exact (hu.comp (continuous_id.div_const 8)).div_const 8
  · simp [scaledPosition]
  · simp [scaledVelocity]
  · intro t _
    exact scaledPosition_derivative hr t
  · intro t ht
    exact scaledVelocity_derivative hr hr1 ht

#print axioms exists_low_damping_escape
end NesterovLowDamping
