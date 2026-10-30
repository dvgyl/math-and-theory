import HilbertEscape
import HighDamping
import MoreauTrajectory
import FiniteExcursion
import ExponentSelection

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology

namespace NesterovSharpThreshold
open NesterovThresholdModel NesterovThreshold NesterovHilbert

/-- For each damping strictly between one and three, a convex C1,1
objective with globally 1-Lipschitz gradient on the concrete real Hilbert space l2(N;R2) has an actual, globally
existing, zero-initial-velocity Nesterov trajectory whose norm tends to infinity.
The objective is nonnegative, vanishes at zero, and has globally 1-Lipschitz,
globally bounded gradient. There are no assumed trajectories or abstract model
hypotheses in this statement. -/
theorem exists_subcritical_norm_divergent_flow {r : ℝ} (hr : 1<r) (hr3 : r<3) :
    ∃ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (X V : ℝ → Hilbert),
      ConvexOn ℝ univ F ∧
      (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖≤2) ∧
      F 0=0 ∧ (∀ x, 0≤F x) ∧
      Continuous X ∧ Continuous V ∧
      X 0=initialData (point 2 1) ∧ V 0=0 ∧
      (∀ t≥0, HasDerivAt X (V t) t) ∧
      (∀ t>0, HasDerivAt V (-(r/t) • V t-G (X t)) t) ∧
      Tendsto (fun t => ‖X t‖) atTop atTop := by
  obtain ⟨e,he⟩ := exists_powerExponent hr3
  have hparam (n : ℕ) : ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧
      ∀ S : ValleyPath r e.p ε, ∃ t : ℝ, 0≤t ∧ target n<S.x t :=
    exists_parameter_excursion hr e.p_gt_one e.p_le_two he (target_ge_two n)
  choose ε hε0 hε1 hεexc using hparam
  have hε : ∀ n, 0<ε n ∧ ε n≤1 := fun n => ⟨hε0 n,hε1 n⟩
  have hblock (n : ℕ) : BlockExcursion r e (ε n) (target n) := by
    intro X V hX hV hX0 hV0 hXd hVd
    let S := ValleyPath.ofVector e (hε0 n) (hε1 n) X V hX hV hXd hVd hX0 hV0
    exact ⟨hεexc n S,S.first_coordinate_monotone hr⟩
  obtain ⟨X,V,hX,hV,hX0,hV0,hXd,hVd,hescape⟩ := escape_from_blocks hr e ε hε hblock
  exact ⟨hilbertPotential e ε,hilbertGradient e ε,X,V,
    hilbert_convex e hε,hilbert_hasGradient e hε,hilbert_lipschitz e hε,
    hilbert_gradient_bound e hε,hilbert_zero e ε,hilbert_nonneg e hε,
    hX,hV,hX0,hV0,hXd,hVd,hescape⟩

/-- Universal boundedness for all globally 1-Lipschitz convex gradient fields
with an attained minimum, on the same concrete Hilbert space as the examples.
Position and velocity are continuous through zero; the stated derivatives are
actual derivatives, and the initial velocity is zero. -/
def UniversalBoundedness (r : ℝ) : Prop :=
  ∀ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (X V : ℝ → Hilbert),
    ConvexOn ℝ univ F →
    (∀ x, HasGradientAt F (G x) x) →
    LipschitzWith 1 G →
    (∃ z, ∀ x, F z≤F x) →
    Continuous X → Continuous V → V 0=0 →
    (∀ t≥0, HasDerivAt X (V t) t) →
    (∀ t>0, HasDerivAt V (-(r/t) • V t-G (X t)) t) →
    ∃ C : ℝ, ∀ t≥0, ‖X t‖≤C

/-- The classical high-damping implication, proved here for completeness. -/
theorem universalBoundedness_of_three_le {r : ℝ} (hr : 3≤r) :
    UniversalBoundedness r := by
  intro F G X V hconv hgrad _hLip hmin hX hV _hV0 hXd hVd
  obtain ⟨z,hz⟩ := hmin
  have hb := NesterovHighDamping.bounded_distance hr hconv hgrad
    hX.continuousOn hV.continuousOn (fun t ht => hXd t ht.le) hVd hz
  refine ⟨‖X 0-z‖+‖z‖,?_⟩
  intro t ht
  calc
    ‖X t‖=‖X t-z+z‖ := by rw [sub_add_cancel]
    _≤‖X t-z‖+‖z‖ := norm_add_le _ _
    _≤‖X 0-z‖+‖z‖ := add_le_add_right (hb t ht) _

/-- Exact universal boundedness classification throughout the nontrivial
integrably decaying free-velocity range r>1. The negative direction is the new
smooth Hilbert counterexample; the positive direction is classical. -/
theorem sharp_boundedness_threshold {r : ℝ} (hr : 1<r) :
    UniversalBoundedness r ↔ 3≤r := by
  constructor
  · intro hU
    by_contra hn
    have hr3 : r<3 := lt_of_not_ge hn
    obtain ⟨F,G,X,V,hconv,hgrad,hLip,_hbound,hF0,hFpos,hX,hV,_hX0,hV0,hXd,hVd,hescape⟩ :=
      exists_subcritical_norm_divergent_flow hr hr3
    have hmin : ∃ z, ∀ x, F z≤F x := ⟨0,fun x => by rw [hF0]; exact hFpos x⟩
    obtain ⟨C,hC⟩ := hU F G X V hconv hgrad hLip hmin hX hV hV0 hXd hVd
    have hbig : ∀ᶠ t in atTop, C+1≤‖X t‖ := (tendsto_atTop.1 hescape) (C+1)
    obtain ⟨t,ht,hlarge⟩ := ((eventually_ge_atTop (0:ℝ)).and hbig).exists
    have hsmall := hC t ht
    linarith
  · exact universalBoundedness_of_three_le

#print axioms exists_subcritical_norm_divergent_flow
#print axioms sharp_boundedness_threshold
end NesterovSharpThreshold
