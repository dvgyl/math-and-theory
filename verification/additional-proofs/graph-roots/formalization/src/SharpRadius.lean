import ExtremalSqueeze
import GraphDegree
import RadiusExact

noncomputable section
namespace SquareFlowerCompletion.Extremal

/-- The original strict bound applies to the complete finite graph root maximum. -/
theorem radius_strict_global_bound {n : ℕ} (hn : 0 < n) :
    radius n < 2 + Real.sqrt (4*(n:ℝ) / Radius.positiveLambert (4*(n:ℝ))) := by
  obtain ⟨z,hz,he⟩ := radius_attained n
  rw [← he]
  exact Radius.actual_graph_root_strict_global_bound n z hn hz

#print axioms radius_strict_global_bound
end SquareFlowerCompletion.Extremal
