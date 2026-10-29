import Research.ADMMGeometry
import Research.ADMMData
import Mathlib.Topology.Order.OrderClosed

/-! A concrete nonconvergent trajectory of classical two-block ADMM.

The constraint is x = z, the objectives are indicators of two nonempty compact
convex polytopes, the penalty is one, and only the multiplier update is scaled
by tau = 199/100.  `IsProjection` certifies unique minimizers of the complete
primal subproblems.  The final theorem includes every iteration of the actual
ADMM recurrence and failure of the squared primal residual to tend to zero.
-/

noncomputable section

namespace ADMMCounterexample

open ADMMGeometry ADMMData Filter
open scoped Topology

def C : Set ADMMData.Vec := polytope x
def D : Set ADMMData.Vec := polytope z

def phase (n : ℕ) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩
def X (n : ℕ) : ADMMData.Vec := x (phase n)
def Z (n : ℕ) : ADMMData.Vec := z (phase n)
def U (n : ℕ) : ADMMData.Vec := u (phase n)

/-- The classical two-block ADMM update for a feasibility problem x = z,
with penalty one and a scaled multiplier u.  Each primal subproblem has the
stated unique minimizer. -/
def IsADMMTrajectory (C D : Set ADMMData.Vec) (t : ℝ)
    (X Z U : ℕ → ADMMData.Vec) : Prop :=
  ∀ n, IsProjection C (Z n - U n) (X (n + 1)) ∧
    IsProjection D (X (n + 1) + U n) (Z (n + 1)) ∧
    U (n + 1) = U n + t • (X (n + 1) - Z (n + 1))

theorem C_properties : Convex ℝ C ∧ IsCompact C ∧ IsClosed C ∧ (0 : ADMMData.Vec) ∈ C := by
  exact ⟨convex_polytope x, compact_polytope x, closed_polytope x,
    zero_mem_polytope x sum_x⟩

theorem D_properties : Convex ℝ D ∧ IsCompact D ∧ IsClosed D ∧ (0 : ADMMData.Vec) ∈ D := by
  exact ⟨convex_polytope z, compact_polytope z, closed_polytope z,
    zero_mem_polytope z sum_z⟩

/-- A feasible zero is its own unique Euclidean projection. -/
theorem zero_projection (S : Set ADMMData.Vec) (hzero : (0 : ADMMData.Vec) ∈ S) :
    IsProjection S 0 0 := by
  refine ⟨hzero, ?_, ?_⟩
  · intro y _
    simpa only [sqDist_self] using sqDist_nonneg 0 y
  · intro y _ hmin
    have hle : sqDist 0 y ≤ 0 := by simpa only [sqDist_self] using hmin
    exact (eq_of_sqDist_eq_zero 0 y (le_antisymm hle (sqDist_nonneg 0 y))).symm

/-- The same instance has the zero fixed trajectory at every multiplier step. -/
theorem zero_fixed_trajectory (t : ℝ) :
    IsADMMTrajectory C D t (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  intro n
  simpa only [sub_self, zero_add, smul_zero] using
    And.intro (zero_projection C C_properties.2.2.2)
      (And.intro (zero_projection D D_properties.2.2.2) (rfl : (0 : ADMMData.Vec) = 0))

theorem x_projection (i : Fin 5) :
    IsProjection C (z (prev i) - u (prev i)) (x i) := by
  apply projection_of_vertex_normals x i
  intro j
  exact x_normal i j

theorem z_projection (i : Fin 5) :
    IsProjection D (x i + u (prev i)) (z i) := by
  apply projection_of_vertex_normals z i
  intro j
  exact z_normal i j

theorem prev_phase_succ (n : ℕ) : prev (phase (n + 1)) = phase n := by
  apply Fin.ext
  simp only [prev, phase]
  omega

theorem phase_add_five (n : ℕ) : phase (n + 5) = phase n := by
  apply Fin.ext
  simp [phase, Nat.add_mod]

theorem actual_admm_trajectory : IsADMMTrajectory C D tau X Z U := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · have h := x_projection (phase (n + 1))
    simpa only [X, Z, U, prev_phase_succ] using h
  · have h := z_projection (phase (n + 1))
    simpa only [X, Z, U, prev_phase_succ] using h
  · have h := dual_update (phase (n + 1))
    simpa only [X, Z, U, prev_phase_succ] using h

theorem five_periodic : (∀ n, X (n + 5) = X n) ∧
    (∀ n, Z (n + 5) = Z n) ∧ (∀ n, U (n + 5) = U n) := by
  exact ⟨fun n => congrArg x (phase_add_five n),
    fun n => congrArg z (phase_add_five n), fun n => congrArg u (phase_add_five n)⟩

theorem nonconstant : X 0 ≠ X 1 := by
  exact x_zero_ne_x_one

theorem residual_always_large (n : ℕ) : (500000 : ℝ) ≤ sqDist (X n) (Z n) := by
  exact residual_lower_bound (phase n)

theorem residual_not_tendsto_zero :
    ¬ Tendsto (fun n : ℕ => sqDist (X n) (Z n)) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have hle : (500000 : ℝ) ≤ 0 := ge_of_tendsto' h residual_always_large
  norm_num at hle

/-- All hypotheses and the full nonconvergent trajectory are combined here.
In particular this does not assume either the projection inequalities or an
unproved convergence/divergence statement. -/
theorem counterexample :
    (1 : ℝ) < tau ∧ tau < 2 ∧
    Convex ℝ C ∧ IsCompact C ∧ IsClosed C ∧
    Convex ℝ D ∧ IsCompact D ∧ IsClosed D ∧
    (0 : ADMMData.Vec) ∈ C ∩ D ∧
    IsADMMTrajectory C D tau (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
    IsADMMTrajectory C D tau X Z U ∧
    (∀ n, X (n + 5) = X n) ∧
    (∀ n, Z (n + 5) = Z n) ∧
    (∀ n, U (n + 5) = U n) ∧
    X 0 ≠ X 1 ∧
    (∀ n, (500000 : ℝ) ≤ sqDist (X n) (Z n)) ∧
    ¬ Tendsto (fun n : ℕ => sqDist (X n) (Z n)) atTop (𝓝 (0 : ℝ)) := by
  exact ⟨tau_bounds.1, tau_bounds.2,
    C_properties.1, C_properties.2.1, C_properties.2.2.1,
    D_properties.1, D_properties.2.1, D_properties.2.2.1,
    ⟨C_properties.2.2.2, D_properties.2.2.2⟩,
    zero_fixed_trajectory tau,
    actual_admm_trajectory, five_periodic.1, five_periodic.2.1, five_periodic.2.2,
    nonconstant, residual_always_large, residual_not_tendsto_zero⟩

end ADMMCounterexample

#print axioms ADMMCounterexample.counterexample
