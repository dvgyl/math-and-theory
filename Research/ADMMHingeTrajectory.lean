module
public import Research.ADMMHinge
public import Research.ADMMCounterexample

@[expose] public section

/-!
The actual infinite ADMM orbit for the explicit everywhere finite objectives
in ADMMHinge. The theorem checks their unique global proximal minimizers,
their unique constrained optimizer, and persistent nonzero primal residuals.

The analytic regularity claims (convexity, strong convexity, C² regularity,
and Lipschitz gradients) are established in the accompanying handwritten
proof and are not asserted as formally checked by this module.
-/

namespace ADMMHingeTrajectory

noncomputable section

open ADMMHinge ADMMData ADMMCounterexample ADMMGeometry Filter
open scoped Topology

def IsFunctionADMMTrajectory (F G : ADMMData.Vec → ℝ) (t : ℝ)
    (X Z U : ℕ → ADMMData.Vec) : Prop :=
  ∀ n, IsProx F (Z n - U n) (X (n + 1)) ∧
    IsProx G (X (n + 1) + U n) (Z (n + 1)) ∧
    U (n + 1) = U n + t • (X (n + 1) - Z (n + 1))

theorem actual_trajectory : IsFunctionADMMTrajectory f g tau X Z U := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · have h := f_prox (phase (n + 1))
    simpa only [X, Z, U, prev_phase_succ] using h
  · have h := g_prox (phase (n + 1))
    simpa only [X, Z, U, prev_phase_succ] using h
  · have h := dual_update (phase (n + 1))
    simpa only [X, Z, U, prev_phase_succ] using h

/-- The full infinite orbit and optimizer claim for the explicit real-valued
objectives. See the module header for the precise regularity boundary. -/
theorem verified_orbit_and_optimizer :
    (1 : ℝ) < tau ∧ tau < 2 ∧
    (f 0 + g 0 = 0 ∧
      (∀ w, 0 ≤ f w + g w) ∧ (∀ w, f w + g w ≤ 0 → w = 0)) ∧
    IsFunctionADMMTrajectory f g tau X Z U ∧
    (∀ n, X (n + 5) = X n) ∧
    (∀ n, Z (n + 5) = Z n) ∧
    (∀ n, U (n + 5) = U n) ∧
    X 0 ≠ X 1 ∧
    (∀ n, (500000 : ℝ) ≤ sqDist (X n) (Z n)) ∧
    ¬ Tendsto (fun n : ℕ => sqDist (X n) (Z n)) atTop (𝓝 (0 : ℝ)) := by
  exact ⟨tau_bounds.1, tau_bounds.2, unique_optimizer, actual_trajectory,
    five_periodic.1, five_periodic.2.1, five_periodic.2.2, nonconstant,
    residual_always_large, residual_not_tendsto_zero⟩

end

end ADMMHingeTrajectory

#print axioms ADMMHingeTrajectory.verified_orbit_and_optimizer
