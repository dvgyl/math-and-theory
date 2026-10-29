import RadiusEquivalent
import PositiveLambertAsymptotic
import RealExclusions

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion.Extremal

/-- The complete main escape theorem for the actual finite square-flower graph. -/
theorem main_escape_theorem :
    (∀ n : ℕ, 0 < n → radius n <
      2 + Real.sqrt (4*(n:ℝ)/Radius.positiveLambert (4*(n:ℝ)))) ∧
    Tendsto (fun n : ℕ => 4*(n:ℝ)/(radius n)^2 -
      (Real.log (4*(n:ℝ)) - Real.log (Real.log (4*(n:ℝ))))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => radius n / (2*Real.sqrt ((n:ℝ)/Real.log (n:ℝ)))) atTop (𝓝 1) :=
  ⟨fun _ hn => radius_strict_global_bound hn,
    radius_reciprocal_square_asymptotic, radius_leading_equivalent⟩

end SquareFlowerCompletion.Extremal
