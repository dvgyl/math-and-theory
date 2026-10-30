import PlanarMain
import LowDampingHilbert

/-!
Planar escape for every damping `0 < r ≤ 2`.  For `1 < r ≤ 2` the witness is the
planar Huber valley of `PlanarMain`; for `0 < r ≤ 1` it is the classical
one-dimensional low-damping example (`NesterovLowDamping.exists_low_damping_escape`)
lifted along the unit vector `(1, 0)` with `NesterovAxisLift.lift_flow`.
The low-damping branch is a completion of the range, not a new claim.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovPlanar

/-- The lift axis `NesterovModel.axis` is the unit vector `(1, 0)`. -/
lemma axis_eq_point : NesterovModel.axis = NesterovModel.point 1 0 := by
  ext i
  fin_cases i <;> simp [NesterovModel.axis, NesterovModel.point]

/-- Low-damping planar branch, `0 < r ≤ 1`: the scalar example lifted along
`(1, 0)`. -/
theorem planar_escape_low_branch {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (F : EuclideanSpace ℝ (Fin 2) → ℝ)
      (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      ConvexOn ℝ univ F ∧ (∀ z, HasGradientAt F (G z) z) ∧ LipschitzWith 1 G ∧
      (∀ z, ‖G z‖ ≤ 2) ∧ (∃ zmin, ∀ z, F zmin ≤ F z) ∧
      ∃ q u : ℝ → EuclideanSpace ℝ (Fin 2),
        Continuous q ∧ Continuous u ∧ u 0 = 0 ∧ HasDerivAt q 0 0 ∧
        (∀ t ≥ 0, HasDerivAt q (u t) t) ∧
        (∀ t > 0, HasDerivAt u (-(r / t) • u t - G (q t)) t) ∧
        Tendsto (fun t => ‖q t‖) atTop atTop := by
  obtain ⟨F, G, X, V, z, hconv, hgrad, hLip, hbound, hFz, hFpos,
    hX, hV, hX0, hV0, hXd, hVd, hescape⟩ :=
    NesterovLowDamping.exists_low_damping_escape hr hr1
  obtain ⟨hc, hg, hl, hb, hz, hpos, hXc, hVc, -, hV0', hXd', hVd', hesc⟩ :=
    NesterovAxisLift.lift_flow NesterovModel.axis NesterovModel.axis_norm hconv hgrad hLip
      hbound hFz hFpos hX hV hX0 hV0 hXd hVd hescape
  refine ⟨NesterovAxisLift.potential NesterovModel.axis F,
    NesterovAxisLift.gradient NesterovModel.axis G, hc, hg, hl, hb,
    ⟨z • NesterovModel.axis, fun w => by rw [hz]; exact hpos w⟩,
    fun t => X t • NesterovModel.axis, fun t => V t • NesterovModel.axis,
    hXc, hVc, hV0', ?_, hXd', hVd', hesc⟩
  simpa only [hV0'] using hXd' 0 le_rfl

/-- High-damping planar branch, `1 < r ≤ 2`: the Huber valley. -/
theorem planar_escape_valley_branch {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) :
    ∃ (F : EuclideanSpace ℝ (Fin 2) → ℝ)
      (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      ConvexOn ℝ univ F ∧ (∀ z, HasGradientAt F (G z) z) ∧ LipschitzWith 1 G ∧
      (∀ z, ‖G z‖ ≤ 2) ∧ (∃ zmin, ∀ z, F zmin ≤ F z) ∧
      ∃ q u : ℝ → EuclideanSpace ℝ (Fin 2),
        Continuous q ∧ Continuous u ∧ u 0 = 0 ∧ HasDerivAt q 0 0 ∧
        (∀ t ≥ 0, HasDerivAt q (u t) t) ∧
        (∀ t > 0, HasDerivAt u (-(r / t) • u t - G (q t)) t) ∧
        Tendsto (fun t => ‖q t‖) atTop atTop := by
  obtain ⟨-, hconv, -, hgrad, hlip, -, -, q, u, hqc, huc, -, hu0, hq0', hqd, hud, -, hnorm⟩ :=
    planar_valley_escape hr hr2
  exact ⟨NesterovModel.potential, NesterovModel.gradient, hconv, hgrad, hlip,
    NesterovModel.gradient_norm_le_two,
    ⟨NesterovModel.point 1 0, (NesterovModel.potential_minimizers _).mpr ⟨by simp, by simp⟩⟩,
    q, u, hqc, huc, hu0, hq0', hqd, hud, hnorm⟩

/-- Planar escape for every damping `0 < r ≤ 2`: a convex objective on `ℝ²`
with 1-Lipschitz gradient (bounded by 2) attaining its minimum, and an actual
zero-initial-velocity trajectory of `q'' + (r/t) q' + ∇F(q) = 0` whose norm
tends to infinity. -/
theorem planar_escape_all_low_damping {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ∃ (F : EuclideanSpace ℝ (Fin 2) → ℝ)
      (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      ConvexOn ℝ univ F ∧ (∀ z, HasGradientAt F (G z) z) ∧ LipschitzWith 1 G ∧
      (∀ z, ‖G z‖ ≤ 2) ∧ (∃ zmin, ∀ z, F zmin ≤ F z) ∧
      ∃ q u : ℝ → EuclideanSpace ℝ (Fin 2),
        Continuous q ∧ Continuous u ∧ u 0 = 0 ∧ HasDerivAt q 0 0 ∧
        (∀ t ≥ 0, HasDerivAt q (u t) t) ∧
        (∀ t > 0, HasDerivAt u (-(r / t) • u t - G (q t)) t) ∧
        Tendsto (fun t => ‖q t‖) atTop atTop := by
  rcases le_or_lt r 1 with h1 | h1
  · exact planar_escape_low_branch hr h1
  · exact planar_escape_valley_branch h1 hr2

end NesterovPlanar
