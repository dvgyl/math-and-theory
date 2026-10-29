import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section

open NNReal

namespace SquareFlowerCompletion

/-- A contraction of a closed disk yields a true zero with a quantitative error bound. -/
theorem exists_small_zero_of_lipschitz
    (H : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hsmall : ‖H 0‖ ≤ r / 2)
    (hlip : ∀ u ∈ Metric.closedBall (0 : ℂ) r,
      ∀ v ∈ Metric.closedBall (0 : ℂ) r,
      ‖(u + H u) - (v + H v)‖ ≤ (1 / 2 : ℝ) * ‖u - v‖) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) r, H z = 0 ∧ ‖z‖ ≤ 2 * ‖H 0‖ := by
  let S := Metric.closedBall (0 : ℂ) r
  have hzero : (0 : ℂ) ∈ S := by simpa [S] using hr.le
  have hmap : Set.MapsTo (fun z => z + H z) S S := by
    intro z hz
    have hzbound : ‖z‖ ≤ r := by simpa [S, dist_zero_right] using hz
    have h := hlip z hz 0 hzero
    simp only [zero_add, sub_zero] at h
    have htri := norm_add_le (z + H z - H 0) (H 0)
    have heq : z + H z - H 0 + H 0 = z + H z := by abel
    rw [heq] at htri
    have : ‖z + H z‖ ≤ r := by linarith
    simpa [S, dist_zero_right] using this
  let F : S → S := fun z => ⟨z.1 + H z.1, hmap z.2⟩
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) F := by
    refine ⟨by change ((1 / 2 : ℝ≥0) : ℝ) < 1; norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    simpa [F, Subtype.dist_eq, dist_eq_norm] using hlip u.1 u.2 v.1 v.2
  letI : Nonempty S := ⟨⟨0, hzero⟩⟩
  letI : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  let z : S := ContractingWith.fixedPoint F hcontract
  have hz : F z = z := hcontract.fixedPoint_isFixedPt
  have hzval : z.1 + H z.1 = z.1 := congrArg Subtype.val hz
  have hHz : H z.1 = 0 := by linear_combination hzval
  refine ⟨z.1, z.2, hHz, ?_⟩
  have h := hlip z.1 z.2 0 hzero
  simp only [hHz, add_zero, zero_add, sub_zero] at h
  have htri := norm_add_le (z.1 - H 0) (H 0)
  have heq : z.1 - H 0 + H 0 = z.1 := by abel
  rw [heq] at htri
  linarith

/-- The complex derivative bound is sufficient for the closed-disk contraction. -/
theorem exists_small_zero_of_derivative
    (H d : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hsmall : ‖H 0‖ ≤ r / 2)
    (hderiv : ∀ z ∈ Metric.closedBall (0 : ℂ) r, HasDerivAt H (d z) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖1 + d z‖ ≤ (1 / 2 : ℝ)) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) r, H z = 0 ∧ ‖z‖ ≤ 2 * ‖H 0‖ := by
  apply exists_small_zero_of_lipschitz H r hr hsmall
  intro u hu v hv
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => ((hasDerivAt_id z).add (hderiv z hz)).hasDerivWithinAt)
    hbound (convex_closedBall (0 : ℂ) r) hv hu

#print axioms exists_small_zero_of_lipschitz
#print axioms exists_small_zero_of_derivative

end SquareFlowerCompletion
