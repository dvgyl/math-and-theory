import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

noncomputable section
namespace SquareFlowerCompletion
namespace Reciprocal

def P (w : ℂ) : ℂ := 1 + 3 * w + 3 * w ^ 2
def Q (w : ℂ) : ℂ := 1 + 3 * w + w ^ 2
def remainder (w : ℂ) : ℂ := Complex.log (Q w) - Complex.log (P w) + 2 * w ^ 2
def remainderDeriv (w : ℂ) : ℂ :=
  w ^ 2 * (18 + 52 * w + 48 * w ^ 2 + 12 * w ^ 3) / (P w * Q w)

theorem polynomial_bounds {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    ‖P w - 1‖ ≤ (1 / 4 : ℝ) ∧ ‖Q w - 1‖ ≤ (1 / 4 : ℝ) := by
  have hs : ‖w‖ ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by gcongr
  have hp : ‖P w - 1‖ ≤ 3 * ‖w‖ + 3 * ‖w‖ ^ 2 := by
    calc
      ‖P w - 1‖ = ‖3 * w + 3 * w ^ 2‖ := by congr 1; dsimp [P]; ring
      _ ≤ ‖(3 : ℂ) * w‖ + ‖(3 : ℂ) * w ^ 2‖ := norm_add_le _ _
      _ = _ := by norm_num [norm_mul, norm_pow]
  have hq : ‖Q w - 1‖ ≤ 3 * ‖w‖ + ‖w‖ ^ 2 := by
    calc
      ‖Q w - 1‖ = ‖3 * w + w ^ 2‖ := by congr 1; dsimp [Q]; ring
      _ ≤ ‖(3 : ℂ) * w‖ + ‖w ^ 2‖ := norm_add_le _ _
      _ = _ := by norm_num [norm_mul, norm_pow]
  constructor <;> nlinarith

theorem denominator_bounds {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖P w‖ ∧ (1 / 2 : ℝ) ≤ ‖Q w‖ := by
  obtain ⟨hp, hq⟩ := polynomial_bounds hw
  have hp' := norm_sub_norm_le (1 : ℂ) (P w)
  have hq' := norm_sub_norm_le (1 : ℂ) (Q w)
  rw [norm_one, norm_sub_rev] at hp' hq'
  constructor <;> linarith

theorem slitPlane_bounds {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    P w ∈ Complex.slitPlane ∧ Q w ∈ Complex.slitPlane := by
  obtain ⟨hp, hq⟩ := polynomial_bounds hw
  constructor
  · have h := Complex.mem_slitPlane_of_norm_lt_one (by linarith : ‖P w - 1‖ < 1)
    convert h using 1; ring
  · have h := Complex.mem_slitPlane_of_norm_lt_one (by linarith : ‖Q w - 1‖ < 1)
    convert h using 1; ring

theorem hasDerivAt_remainder {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    HasDerivAt remainder (remainderDeriv w) w := by
  obtain ⟨hp, hq⟩ := slitPlane_bounds hw
  have hp0 := Complex.slitPlane_ne_zero hp
  have hq0 := Complex.slitPlane_ne_zero hq
  have hP : HasDerivAt P (3 + 6 * w) w := by
    convert (((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).const_mul 3)).add
      (((hasDerivAt_id w).pow 2).const_mul 3)) using 1; dsimp [P]; ring
  have hQ : HasDerivAt Q (3 + 2 * w) w := by
    convert (((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).const_mul 3)).add
      ((hasDerivAt_id w).pow 2)) using 1; dsimp [Q]; ring
  have h := (((Complex.hasDerivAt_log hq).comp w hQ).sub
    ((Complex.hasDerivAt_log hp).comp w hP)).add (((hasDerivAt_id w).pow 2).const_mul 2)
  convert h using 1
  dsimp [remainderDeriv]
  field_simp [hp0, hq0]
  dsimp [P, Q]
  ring

theorem norm_remainderDeriv_le {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    ‖remainderDeriv w‖ ≤ 100 * ‖w‖ ^ 2 := by
  have h0 := norm_nonneg w
  have hs : ‖w‖ ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by gcongr
  have hc : ‖w‖ ^ 3 ≤ (1 / 16 : ℝ) ^ 3 := by gcongr
  have hn : ‖(18 : ℂ) + 52 * w + 48 * w ^ 2 + 12 * w ^ 3‖ ≤ 25 := by
    have ht : ‖(18 : ℂ) + 52 * w + 48 * w ^ 2 + 12 * w ^ 3‖ ≤
        18 + 52 * ‖w‖ + 48 * ‖w‖ ^ 2 + 12 * ‖w‖ ^ 3 := by
      calc
        _ ≤ ‖(18 : ℂ) + 52 * w + 48 * w ^ 2‖ + ‖(12 : ℂ) * w ^ 3‖ := norm_add_le _ _
        _ ≤ (‖(18 : ℂ) + 52 * w‖ + ‖(48 : ℂ) * w ^ 2‖) + ‖(12 : ℂ) * w ^ 3‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖(18 : ℂ)‖ + ‖(52 : ℂ) * w‖) + ‖(48 : ℂ) * w ^ 2‖) + ‖(12 : ℂ) * w ^ 3‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by norm_num [norm_mul, norm_pow]
    nlinarith
  obtain ⟨hp, hq⟩ := denominator_bounds hw
  have hpq : (1 / 4 : ℝ) ≤ ‖P w * Q w‖ := by
    rw [norm_mul]
    nlinarith
  have hpos : 0 < ‖P w * Q w‖ := by linarith
  rw [remainderDeriv, norm_div, norm_mul, norm_pow]
  apply (div_le_iff₀ hpos).2
  have hnum := mul_le_mul_of_nonneg_left hn (sq_nonneg ‖w‖)
  have hden := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 100 * ‖w‖ ^ 2 by positivity)
  nlinarith

/-- A fixed-neighborhood cubic remainder, valid for the literal reciprocal polynomials. -/
theorem norm_log_remainder_le {w : ℂ} (hw : ‖w‖ ≤ (1 / 16 : ℝ)) :
    ‖Complex.log (Q w) - Complex.log (P w) + 2 * w ^ 2‖ ≤ 100 * ‖w‖ ^ 3 := by
  have hd : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      HasDerivWithinAt remainder (remainderDeriv z) (Metric.closedBall (0 : ℂ) ‖w‖) z := by
    intro z hz
    have hz' : ‖z‖ ≤ ‖w‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (hasDerivAt_remainder (hz'.trans hw)).hasDerivWithinAt
  have hb : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖remainderDeriv z‖ ≤ 100 * ‖w‖ ^ 2 := by
    intro z hz
    have hz' : ‖z‖ ≤ ‖w‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    calc
      _ ≤ 100 * ‖z‖ ^ 2 := norm_remainderDeriv_le (hz'.trans hw)
      _ ≤ _ := by gcongr
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (x := (0 : ℂ)) (y := w) hd hb
    (convex_closedBall (0 : ℂ) ‖w‖) (by simp) (by simp)
  simpa [remainder, P, Q, pow_succ, mul_assoc] using h

#print axioms norm_log_remainder_le
end Reciprocal
end SquareFlowerCompletion
