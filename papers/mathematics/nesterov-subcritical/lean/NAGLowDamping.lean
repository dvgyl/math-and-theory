import NAGBasic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace NAGLowDamping

def gradient (x : ℝ) : ℝ := min (max (x - 2) (-1)) 0

/-- A convex one-sided Huber potential, with minimum zero on `[2,∞)`. -/
def potential (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, gradient t

theorem gradient_nonpos (x : ℝ) : gradient x ≤ 0 := min_le_right _ _

theorem gradient_ge_neg_one (x : ℝ) : -1 ≤ gradient x := by
  exact le_min (le_max_right _ _) (by norm_num)

theorem gradient_norm_le (x : ℝ) : ‖gradient x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨gradient_ge_neg_one x, (gradient_nonpos x).trans (by norm_num)⟩

theorem gradient_lipschitz : LipschitzWith 1 gradient := by
  have h : LipschitzWith 1 (fun x : ℝ => x - 2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq, sub_sub_sub_cancel_right]
  exact (h.max_const (-1)).min_const 0

theorem gradient_continuous : Continuous gradient := gradient_lipschitz.continuous

theorem gradient_monotone : Monotone gradient := by
  intro x y hxy
  exact min_le_min (max_le_max (sub_le_sub_right hxy 2) le_rfl) le_rfl

theorem gradient_eq_zero {x : ℝ} (hx : 2 ≤ x) : gradient x = 0 := by
  unfold gradient
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

theorem gradient_eq_neg_one {x : ℝ} (hx : x ≤ 1) : gradient x = -1 := by
  unfold gradient
  rw [max_eq_right (by linarith), min_eq_left (by norm_num)]

theorem gradient_eq_linear {x : ℝ} (hx : 1 ≤ x) (hy : x ≤ 2) :
    gradient x = x - 2 := by
  unfold gradient
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

theorem potential_hasDerivAt (x : ℝ) : HasDerivAt potential (gradient x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (gradient_continuous.intervalIntegrable 2 x)
    gradient_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    gradient_continuous.continuousAt

theorem potential_hasGradientAt (x : ℝ) : HasGradientAt potential (gradient x) x :=
  (potential_hasDerivAt x).hasGradientAt'

theorem potential_convex : ConvexOn ℝ univ potential := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (potential_hasDerivAt x).differentiableAt)
  intro x y hxy
  simpa only [(potential_hasDerivAt x).deriv, (potential_hasDerivAt y).deriv]
    using gradient_monotone hxy

theorem potential_eq_zero {x : ℝ} (hx : 2 ≤ x) : potential x = 0 := by
  unfold potential
  calc
    (∫ t in (2:ℝ)..x, gradient t) = ∫ t in (2:ℝ)..x, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact gradient_eq_zero ht.1
    _ = 0 := by simp

theorem potential_nonneg (x : ℝ) : 0 ≤ potential x := by
  by_cases hx : 2 ≤ x
  · rw [potential_eq_zero hx]
  · have hx' : x ≤ 2 := le_of_lt (lt_of_not_ge hx)
    unfold potential
    rw [intervalIntegral.integral_symm]
    have hi : 0 ≤ (∫ t in x..(2:ℝ), -gradient t) := by
      exact intervalIntegral.integral_nonneg hx' (fun t _ => neg_nonneg.mpr (gradient_nonpos t))
    simpa only [intervalIntegral.integral_neg] using hi

theorem potential_eq_quadratic {x : ℝ} (hx : 1 ≤ x) (hy : x ≤ 2) :
    potential x = (2 - x)^2 / 2 := by
  unfold potential
  calc
    (∫ t in (2:ℝ)..x, gradient t) = ∫ t in (2:ℝ)..x, (t-2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hy] at ht
      exact gradient_eq_linear (hx.trans ht.1) ht.2
    _ = (2-x)^2/2 := by
      rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => (2:ℝ))
        (continuous_id.intervalIntegrable 2 x) (continuous_const.intervalIntegrable 2 x)]
      rw [integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

theorem potential_eq_affine {x : ℝ} (hx : x ≤ 1) : potential x = 3/2 - x := by
  have hsplit : (∫ t in (2:ℝ)..1, gradient t) + (∫ t in (1:ℝ)..x, gradient t) =
      ∫ t in (2:ℝ)..x, gradient t := intervalIntegral.integral_add_adjacent_intervals
    (gradient_continuous.intervalIntegrable (2:ℝ) 1)
    (gradient_continuous.intervalIntegrable (1:ℝ) x)
  have hleft : (∫ t in (2:ℝ)..1, gradient t) = 1/2 := by
    have h := potential_eq_quadratic (x:=1) (by norm_num) (by norm_num)
    norm_num [potential] at h
    exact h
  have hright : (∫ t in (1:ℝ)..x, gradient t) = 1-x := by
    calc
      (∫ t in (1:ℝ)..x, gradient t) = ∫ t in (1:ℝ)..x, (-1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hx] at ht
        exact gradient_eq_neg_one ht.2
      _ = 1-x := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  change (∫ t in (2:ℝ)..x, gradient t) = 3/2-x
  rw [hleft, hright] at hsplit
  linarith

theorem potential_formula (x : ℝ) :
    potential x = if x ≤ 1 then 3/2-x else if x ≤ 2 then (2-x)^2/2 else 0 := by
  split_ifs with hx hy
  · exact potential_eq_affine hx
  · exact potential_eq_quadratic (le_of_lt (lt_of_not_ge hx)) hy
  · exact potential_eq_zero (le_of_lt (lt_of_not_ge hy))

abbrev X (r : ℝ) (k : ℕ) : ℝ := DiscreteNesterov.nagX r 1 gradient 0 k
abbrev Y (r : ℝ) (k : ℕ) : ℝ := DiscreteNesterov.nagY r 1 gradient 0 k

theorem X_one (r : ℝ) : X r 1 = 1 := by
  norm_num [X, DiscreteNesterov.nagX, DiscreteNesterov.nagState, gradient]

theorem X_two (r : ℝ) : X r 2 = 2 := by
  norm_num [X, DiscreteNesterov.nagX, DiscreteNesterov.nagState,
    DiscreteNesterov.momentum, gradient]

theorem X_succ (r : ℝ) (k : ℕ) : X r (k+1) = Y r k - gradient (Y r k) := by
  simpa only [one_pow, one_smul] using
    (DiscreteNesterov.nagX_succ r 1 gradient 0 k)

theorem Y_succ (r : ℝ) (k : ℕ) :
    Y r (k+1) = X r (k+1) + DiscreteNesterov.momentum r k * (X r (k+1) - X r k) := by
  simpa only [smul_eq_mul] using
    (DiscreteNesterov.nagY_succ r 1 gradient 0 k)

/-- A direct lower bound for increments of the actual canonical iterates. -/
theorem increment_lower {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (k : ℕ) :
    1 / ((k:ℝ)+1) ≤ X r (k+2) - X r (k+1) := by
  induction k with
  | zero => norm_num [X_one, X_two]
  | succ k ih =>
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hratio : 1 / (((k+1:ℕ):ℝ)+1) ≤
        DiscreteNesterov.momentum r (k+1) * (1/((k:ℝ)+1)) := by
      unfold DiscreteNesterov.momentum
      push_cast
      calc
        1 / ((k:ℝ)+1+1) ≤ 1 / ((k:ℝ)+1+r) := by
          apply one_div_le_one_div_of_le (by positivity)
          linarith
        _ = (((k:ℝ)+1) / ((k:ℝ)+1+r)) * (1/((k:ℝ)+1)) := by
          field_simp
    have hm := DiscreteNesterov.momentum_nonneg hr (k+1)
    calc
      1 / (((k+1:ℕ):ℝ)+1) ≤
          DiscreteNesterov.momentum r (k+1) * (1/((k:ℝ)+1)) := hratio
      _ ≤ DiscreteNesterov.momentum r (k+1) * (X r (k+2)-X r (k+1)) :=
        mul_le_mul_of_nonneg_left ih hm
      _ ≤ X r ((k+1)+2)-X r ((k+1)+1) := by
        change _ ≤ X r ((k+2)+1)-X r (k+2)
        rw [X_succ r (k+2), Y_succ r (k+1)]
        have hg := gradient_nonpos (Y r (k+2))
        rw [Y_succ r (k+1)] at hg
        linarith

theorem harmonic_lower {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 / (i+1) : ℝ)) ≤ X r (k+1) := by
  induction k with
  | zero => simp [X_one]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hi := increment_lower hr hr1 k
    exact_mod_cast (by linarith : (∑ i ∈ Finset.range k, (1 / (i+1) : ℝ)) +
      1/((k:ℝ)+1) ≤ X r (k+2))

/-- Every parameter `0 < r ≤ 1` has escape for this single explicit scalar model. -/
theorem canonical_escape {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Tendsto (X r) atTop atTop := by
  apply (tendsto_add_atTop_iff_nat 1).1
  exact tendsto_atTop_mono (harmonic_lower hr hr1)
    Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem canonical_norm_escape {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Tendsto (fun k => ‖X r k‖) atTop atTop := by
  apply tendsto_atTop_mono (fun k => ?_) (canonical_escape hr hr1)
  exact le_trans (le_abs_self (X r k)) (by rw [Real.norm_eq_abs])

/-- A complete scalar instance of the canonical method, including all regularity,
attainment, and global gradient bounds needed by the Hilbert-space lift. -/
theorem exists_scalar_escape {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (F : ℝ → ℝ) (G : ℝ → ℝ) (b z : ℝ),
      ConvexOn ℝ univ F ∧
      (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧
      (∀ x, ‖G x‖ ≤ 2) ∧
      F z = 0 ∧
      (∀ x, 0 ≤ F x) ∧
      Tendsto (DiscreteNesterov.nagX r 1 G b) atTop atTop := by
  refine ⟨potential, gradient, 0, 2, potential_convex, potential_hasGradientAt,
    gradient_lipschitz, ?_, potential_eq_zero le_rfl, potential_nonneg,
    canonical_escape hr hr1⟩
  intro x
  exact (gradient_norm_le x).trans (by norm_num)

end NAGLowDamping
