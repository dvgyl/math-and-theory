import PlanarUnbounded
import ValleyModel

/-!
Coordinate translation of the literal vector Nesterov ODE with damping `r`
for the planar Huber valley, and escape of every actual trajectory with the
data `q(0) = (2, 1)`, `q'(0) = 0`, for every damping `1 < r ≤ 2`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovPlanar

lemma hasDerivAt_coordinate {q : ℝ → NesterovModel.Plane}
    {q' : NesterovModel.Plane} {t : ℝ} (h : HasDerivAt q q' t) (i : Fin 2) :
    HasDerivAt (fun s => q s i) (q' i) t := by
  exact ((EuclideanSpace.proj i : NesterovModel.Plane →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt t h

/-- Coordinate translation of the literal vector Nesterov ODE with damping `r`. -/
def PlanarTrajectory.ofVector {r : ℝ}
    (q u : ℝ → NesterovModel.Plane)
    (hq : ContinuousOn q (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (hqd : ∀ t > 0, HasDerivAt q (u t) t)
    (hud : ∀ t > 0, HasDerivAt u (-(r / t) • u t - NesterovModel.gradient (q t)) t)
    (hq0 : q 0 = NesterovModel.point 2 1) (hu0 : u 0 = 0) : PlanarTrajectory r where
  x := fun t => q t 0
  y := fun t => q t 1
  v := fun t => u t 0
  w := fun t => u t 1
  cont_x := (EuclideanSpace.proj (0 : Fin 2) : NesterovModel.Plane →L[ℝ] ℝ).continuous.comp_continuousOn hq
  cont_y := (EuclideanSpace.proj (1 : Fin 2) : NesterovModel.Plane →L[ℝ] ℝ).continuous.comp_continuousOn hq
  cont_v := (EuclideanSpace.proj (0 : Fin 2) : NesterovModel.Plane →L[ℝ] ℝ).continuous.comp_continuousOn hu
  cont_w := (EuclideanSpace.proj (1 : Fin 2) : NesterovModel.Plane →L[ℝ] ℝ).continuous.comp_continuousOn hu
  deriv_x := fun t ht => hasDerivAt_coordinate (hqd t ht) 0
  deriv_y := fun t ht => hasDerivAt_coordinate (hqd t ht) 1
  deriv_v := by
    intro t ht
    convert hasDerivAt_coordinate (hud t ht) 0 using 1
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      NesterovModel.gradient_first, NesterovModel.norm_eq_sqrt, radius]
    ring
  deriv_w := by
    intro t ht
    convert hasDerivAt_coordinate (hud t ht) 1 using 1
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      NesterovModel.gradient_second, NesterovModel.norm_eq_sqrt, radius]
    ring
  initial_x := by rw [hq0]; exact NesterovModel.point_first 2 1
  initial_y := by rw [hq0]; exact NesterovModel.point_second 2 1
  initial_v := by simp [hu0]
  initial_w := by simp [hu0]

/-- Every actual trajectory of the damping-`r` vector flow (`1 < r ≤ 2`) for the
global convex C¹ valley objective, with `q(0) = (2, 1)` and zero initial
velocity, escapes to infinity. No interpolation model is assumed here; global
existence is supplied separately in `PlanarMain`. -/
theorem every_planar_trajectory_escapes {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (q u : ℝ → NesterovModel.Plane)
    (hq : ContinuousOn q (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (hqd : ∀ t > 0, HasDerivAt q (u t) t)
    (hud : ∀ t > 0, HasDerivAt u (-(r / t) • u t - NesterovModel.gradient (q t)) t)
    (hq0 : q 0 = NesterovModel.point 2 1) (hu0 : u 0 = 0) :
    Tendsto (fun t => q t 0) atTop atTop ∧ Tendsto (fun t => ‖q t‖) atTop atTop := by
  have hx := (PlanarTrajectory.ofVector q u hq hu hqd hud hq0 hu0).first_coordinate_tendsto_atTop
    hr hr2
  exact ⟨hx, tendsto_atTop_mono (fun t => NesterovModel.first_coordinate_le_norm (q t)) hx⟩

end NesterovPlanar
