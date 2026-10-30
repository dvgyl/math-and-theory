import NAGAxisLift
import NAGLowDamping

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
set_option autoImplicit false

namespace DiscreteNesterov
open NesterovHilbert

/-- The elementary range 0<r≤1 on the same concrete Hilbert space as the
subcritical construction. This range is included for completeness. -/
theorem exists_low_discrete_norm_divergence {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    ∃ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (b z : Hilbert),
      ConvexOn ℝ univ F ∧ (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖≤2) ∧
      F z=0 ∧ (∀ x, 0≤F x) ∧
      Tendsto (fun k => ‖nagX r 1 G b k‖) atTop atTop := by
  obtain ⟨F,G,b,z,hc,hg,hL,hB,hz,hpos,hescape⟩ :=
    NAGLowDamping.exists_scalar_escape hr hr1
  refine ⟨axisPotential discreteUnitAxis F,axisGradient discreteUnitAxis G,
    b • discreteUnitAxis,z • discreteUnitAxis,
    axisPotential_convex discreteUnitAxis hc,axisPotential_hasGradient discreteUnitAxis hg,
    axisGradient_lipschitz discreteUnitAxis norm_discreteUnitAxis hL,
    axisGradient_bound discreteUnitAxis norm_discreteUnitAxis hB,?_,
    (fun x => hpos _),lift_discrete_escape discreteUnitAxis norm_discreteUnitAxis hescape⟩
  simpa only [axisPotential, axis_inner discreteUnitAxis norm_discreteUnitAxis] using hz

#print axioms exists_low_discrete_norm_divergence
end DiscreteNesterov
