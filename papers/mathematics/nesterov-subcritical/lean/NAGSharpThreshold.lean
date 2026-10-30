import NAGHilbertEscape
import NAGPlanarExcursion
import NAGHighDamping
import NAGLowHilbert

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
set_option autoImplicit false

namespace DiscreteNesterov
open NesterovThresholdModel NesterovHilbert

/-- For each 1<r<3, the actual recursively defined canonical Nesterov method,
with one fixed unit step and its prescribed zero-momentum initialization,
has norm-divergent iterates on a convex C1,1 objective on l2(N;R2).
The minimum is attained at zero. The actual gradient is globally 1-Lipschitz
and globally bounded. No trajectory, model inequality, or finite-excursion
premise is assumed. -/
theorem exists_subcritical_discrete_norm_divergence {r : ℝ} (hr : 1<r) (hr3 : r<3) :
    ∃ (F : Hilbert → ℝ) (G : Hilbert → Hilbert),
      ConvexOn ℝ univ F ∧
      (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖≤2) ∧
      F 0=0 ∧ (∀ x, 0≤F x) ∧
      Tendsto (fun k => ‖nagX r 1 G (initialData (point 2 1)) k‖) atTop atTop := by
  obtain ⟨e,he⟩ := exists_exponent_all_discrete_excursions hr hr3
  have hp (n : ℕ) := he (excursionTarget n) (excursionTarget_ge_two n)
  choose ε h hε0 hε1 hh0 hh1 hexc hmono using hp
  have hε : ∀ n, 0<ε n ∧ ε n≤1 := fun n => ⟨hε0 n,hε1 n⟩
  have hh : ∀ n, 0<h n ∧ h n≤1 := fun n => ⟨hh0 n,hh1 n⟩
  refine ⟨discretePotential e ε h,discreteGradient e ε h,
    discrete_convex e hε hh,discrete_hasGradient e hε hh,
    discrete_lipschitz e hε hh,discrete_gradient_bound e hε hh,
    discrete_zero e ε h,discrete_nonneg e hε,?_⟩
  exact discrete_escape_from_blocks (by linarith) e ε h hε hh hexc

/-- Universal boundedness of the actual fixed-unit-step canonical algorithm
on the concrete Hilbert space used by the counterexamples. -/
def UniversalDiscreteBoundedness (r : ℝ) : Prop :=
  ∀ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (b : Hilbert),
    ConvexOn ℝ univ F →
    (∀ x, HasGradientAt F (G x) x) →
    LipschitzWith 1 G →
    (∃ z, ∀ x, F z≤F x) →
    ∃ C : ℝ, ∀ k : ℕ, ‖nagX r 1 G b k‖≤C

/-- The classical positive direction; the stronger distance bound is proved
in nag_bounded_distance for every real Hilbert space. -/
theorem universalDiscreteBoundedness_of_three_le {r : ℝ} (hr : 3≤r) :
    UniversalDiscreteBoundedness r := by
  intro F G b hc hg hLip hmin
  obtain ⟨z,hz⟩ := hmin
  have hb := nag_bounded_distance hr hc hg hLip b hz
  refine ⟨‖b-z‖+‖z‖,?_⟩
  intro k
  calc
    ‖nagX r 1 G b k‖=‖nagX r 1 G b k-z+z‖ := by rw [sub_add_cancel]
    _≤‖nagX r 1 G b k-z‖+‖z‖ := norm_add_le _ _
    _≤‖b-z‖+‖z‖ := add_le_add_right (hb k) _

/-- All positive subcritical parameters admit actual norm-divergent iterates,
even with a globally bounded gradient and an attained minimum. The low range
is elementary; the interval 1<r<3 is supplied by the Hilbert construction. -/
theorem exists_discrete_norm_divergence_below_three {r : ℝ} (hr : 0<r) (hr3 : r<3) :
    ∃ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (b z : Hilbert),
      ConvexOn ℝ univ F ∧ (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖≤2) ∧
      F z=0 ∧ (∀ x, 0≤F x) ∧
      Tendsto (fun k => ‖nagX r 1 G b k‖) atTop atTop := by
  by_cases hr1 : 1<r
  · obtain ⟨F,G,hc,hg,hL,hB,hz,hpos,hescape⟩ :=
      exists_subcritical_discrete_norm_divergence hr1 hr3
    exact ⟨F,G,initialData (point 2 1),0,hc,hg,hL,hB,hz,hpos,hescape⟩
  · exact exists_low_discrete_norm_divergence hr (le_of_not_gt hr1)

/-- The exact universal boundedness threshold for all positive parameters
of the canonical discrete Nesterov family. -/
theorem sharp_discrete_boundedness_threshold {r : ℝ} (hr : 0<r) :
    UniversalDiscreteBoundedness r ↔ 3≤r := by
  constructor
  · intro hU
    by_contra hn
    have hr3 : r<3 := lt_of_not_ge hn
    obtain ⟨F,G,b,z,hc,hg,hL,_hB,hz,hpos,hescape⟩ :=
      exists_discrete_norm_divergence_below_three hr hr3
    have hmin : ∃ z, ∀ x, F z≤F x := ⟨z,fun x => by rw [hz]; exact hpos x⟩
    obtain ⟨C,hC⟩ := hU F G b hc hg hL hmin
    have hbig : ∀ᶠ k in atTop, C+1≤‖nagX r 1 G b k‖ :=
      (tendsto_atTop.1 hescape) (C+1)
    obtain ⟨k,hk⟩ := hbig.exists
    have hsmall := hC k
    linarith
  · exact universalDiscreteBoundedness_of_three_le

#print axioms exists_subcritical_discrete_norm_divergence
#print axioms exists_discrete_norm_divergence_below_three
#print axioms sharp_discrete_boundedness_threshold
end DiscreteNesterov
