import CycleWellposed
import CycleData

noncomputable section
open scoped Topology
open Filter ADMM74 ADMMCycle ADMMCycleData

namespace ADMM128Counterexample

theorem counterexample (τ : ℝ) (hτ : tau0 ≤ τ) :
    (∀ c : V, ∃! y, IsProx C (fun _ => 0) c y) ∧
    (∀ c : V, ∃! y, IsProx D (fun _ => 0) c y) ∧
    (∀ n, (Z (n+1), U τ (n+1)) =
      ADMMInterval.originalMap τ proxC proxD (Z n, U τ n)) ∧
    Convex ℝ C ∧ IsCompact C ∧ IsClosed C ∧
    Convex ℝ D ∧ IsCompact D ∧ IsClosed D ∧ (0 : V) ∈ C ∩ D ∧
    IsSaddle C D (fun _ => 0) (fun _ => 0) (0 : V) 0 ∧
    IsADMMTrajectory τ X Z (U τ) ∧
    (∀ n, (∀ y, IsProx C (fun _ => 0) (Z n - U τ n) y → y = X (n + 1)) ∧
      (∀ y, IsProx D (fun _ => 0) (X (n + 1) + U τ n) y → y = Z (n + 1))) ∧
    (∀ n, X (n + 128) = X n) ∧ (∀ n, Z (n + 128) = Z n) ∧
    (∀ n, U τ (n + 128) = U τ n) ∧
    (∀ n, ‖X n - Z n‖ ^ 2 = 1638399999999268052811275665408) ∧
    ¬ Tendsto (fun n : ℕ => ‖X n - Z n‖ ^ 2) atTop (𝓝 (0 : ℝ)) ∧
    (∀ l : V, ¬ Tendsto Z atTop (𝓝 l)) :=
  ⟨C_global_unique_prox, D_global_unique_prox,
    originalMap_orbit_of_trajectory τ (actual_admm_trajectory all_rows τ hτ),
    counterexample_of_rows all_rows τ hτ⟩

end ADMM128Counterexample

#print axioms ADMM128Counterexample.counterexample
