import CycleAlgebra
import ScaledProximalModel
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

open ADMM74 ADMMCycle

namespace ADMM128Counterexample

theorem compact_prox_exists (S : Set V) (hcompact : IsCompact S)
    (hne : S.Nonempty) (c : V) : ∃ y, IsProx S (fun _ => 0) c y := by
  have hcont : Continuous (fun y : V => (1 / 2 : ℝ) * ‖y - c‖ ^ 2) := by
    fun_prop
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  refine ⟨y, hy, ?_⟩
  intro z hz
  simpa only [zero_add] using hmin hz

theorem C_global_prox (c : V) : ∃ y, IsProx C (fun _ => 0) c y :=
  compact_prox_exists C C_properties.2.1 ⟨0, C_properties.2.2.2⟩ c

theorem D_global_prox (c : V) : ∃ y, IsProx D (fun _ => 0) c y :=
  compact_prox_exists D D_properties.2.1 ⟨0, D_properties.2.2.2⟩ c

theorem C_global_unique_prox (c : V) : ∃! y, IsProx C (fun _ => 0) c y := by
  obtain ⟨y, hy⟩ := C_global_prox c
  refine ⟨y, hy, fun z hz => ?_⟩
  exact ADMMCycle.prox_unique x hz hy

theorem D_global_unique_prox (c : V) : ∃! y, IsProx D (fun _ => 0) c y := by
  obtain ⟨y, hy⟩ := D_global_prox c
  refine ⟨y, hy, fun w hw => ?_⟩
  exact ADMMCycle.prox_unique z hw hy

def proxC (c : V) : V := Classical.choose (C_global_prox c)
def proxD (c : V) : V := Classical.choose (D_global_prox c)

theorem proxC_spec (c : V) : IsProx C (fun _ => 0) c (proxC c) :=
  Classical.choose_spec (C_global_prox c)

theorem proxD_spec (c : V) : IsProx D (fun _ => 0) c (proxD c) :=
  Classical.choose_spec (D_global_prox c)

/-- The displayed proximal trajectory is an orbit of exactly the same
multiplier-only ADMM map used by the convergence theorem. -/
theorem originalMap_orbit_of_trajectory (τ : ℝ)
    (h : IsADMMTrajectory τ X Z (U τ)) (n : ℕ) :
    (Z (n+1), U τ (n+1)) =
      ADMMInterval.originalMap τ proxC proxD (Z n, U τ n) := by
  have hx : proxC (Z n - U τ n) = X (n+1) :=
    ADMMCycle.prox_unique x (proxC_spec _) (h n).1
  have hz : proxD (X (n+1) + U τ n) = Z (n+1) :=
    ADMMCycle.prox_unique z (proxD_spec _) (h n).2.1
  simp only [ADMMInterval.originalMap, hx, hz]
  rw [(h n).2.2]

end ADMM128Counterexample
