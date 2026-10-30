import SevenCycle
import AttractingCycle

set_option autoImplicit false

noncomputable section

namespace SevenCP

open FiniteCP

/-- The explicit seven-cycle captures all sufficiently close starting points
in exactly one update, throughout the stated parameter rectangle. -/
theorem seven_cycle_one_step_capture {κ θ : ℝ}
    (hκlo : 2499 / 1000 ≤ κ) (hκhi : κ ≤ 2501 / 1000)
    (hθlo : 0 ≤ θ) (hθhi : θ ≤ 1 / 400) (i : Fin 7) :
    ∀ᶠ w in nhds (X i, Y i), ∀ k : ℕ,
      (cpMap X Y κ θ)^[k + 1] w = (cpMap X Y κ θ)^[k + 1] (X i, Y i) := by
  have h := strict_normal_certificate hκlo hκhi hθlo hθhi
  exact cycle_one_step_capture X Y κ θ h.1 h.2 i

/-- Every cycle state has a neighborhood consisting entirely of nonconvergent
initial conditions for the actual, globally defined projection algorithm. -/
theorem seven_cycle_open_basin {κ θ : ℝ}
    (hκlo : 2499 / 1000 ≤ κ) (hκhi : κ ≤ 2501 / 1000)
    (hθlo : 0 ≤ θ) (hθhi : θ ≤ 1 / 400) (i : Fin 7) :
    ∀ᶠ w in nhds (X i, Y i),
      ¬ ∃ v, Filter.Tendsto (fun k : ℕ => (cpMap X Y κ θ)^[k] w)
        Filter.atTop (nhds v) := by
  have h := strict_normal_certificate hκlo hκhi hθlo hθhi
  exact nearby_iterates_not_convergent X Y κ θ h.1 h.2 0 1 X_zero_ne_one i

/-- A single rational point in the open positive-extrapolation regime; this
corollary also makes the satisfiability of all rectangle premises explicit. -/
theorem rational_example_open_basin (i : Fin 7) :
    ∀ᶠ w in nhds (X i, Y i),
      ¬ ∃ v, Filter.Tendsto (fun k : ℕ => (cpMap X Y (5 / 2) (1 / 1000))^[k] w)
        Filter.atTop (nhds v) := by
  apply seven_cycle_open_basin <;> norm_num

end SevenCP
