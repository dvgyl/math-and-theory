import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
An independent algebraic formalization of the critical c = 1/2
maximally-obese steering-ellipsoid CHSH equality family.

The quantum interpretation is explained in the accompanying report. This file
proves the exact eigenvalue/radical formula's upper bound and all its equality
cases. It does not assume a CHSH bound or a quantum physicality theorem.
-/

set_option autoImplicit false

namespace CriticalCap
noncomputable section

/-- Squared Bob Bloch length, with `u` the squared transverse length. -/
def radiusSq (u z : ℝ) : ℝ := u + z ^ 2

/-- The transverse eigenvalue of the filtered correlation Gram matrix. -/
def middle (u z : ℝ) : ℝ := (1 - radiusSq u z) / 2

/-- Trace of its two-dimensional axial block. -/
def blockTrace (z : ℝ) : ℝ := (3 + 2 * z - z ^ 2) / 4

/-- Discriminant of that block's characteristic polynomial. -/
def discriminant (u z : ℝ) : ℝ :=
  blockTrace z ^ 2 - (1 - radiusSq u z) * (1 + z) ^ 2 / 2

def lower (u z : ℝ) : ℝ :=
  (blockTrace z - Real.sqrt (discriminant u z)) / 2

def upper (u z : ℝ) : ℝ :=
  (blockTrace z + Real.sqrt (discriminant u z)) / 2

/-- The sum of the largest two Gram eigenvalues. -/
def chshQuarterSq (u z : ℝ) : ℝ := middle u z + upper u z

/-- Explicit squared-eigenvalue difference plus four off-diagonal squares. -/
theorem discriminant_decomposition (u z : ℝ) :
    discriminant u z =
      ((1 - z ^ 2) / 2 - (1 + z) ^ 2 / 4) ^ 2 +
        u * (1 + z) ^ 2 / 2 := by
  unfold discriminant blockTrace radiusSq
  ring

theorem discriminant_nonneg (u z : ℝ) (hu : 0 ≤ u) :
    0 ≤ discriminant u z := by
  rw [discriminant_decomposition]
  positivity

/-- Exact sum-of-squares determinant certificate for the desired upper bound. -/
theorem gap_square_identity (u z : ℝ) :
    (1 + radiusSq u z - blockTrace z) ^ 2 - discriminant u z =
      (radiusSq u z - z) ^ 2 := by
  unfold discriminant blockTrace radiusSq
  ring

theorem root_bound_nonneg (u z : ℝ) (hu : 0 ≤ u) :
    0 ≤ 1 + radiusSq u z - blockTrace z := by
  unfold radiusSq blockTrace
  nlinarith [sq_nonneg (z - 1), sq_nonneg z]

theorem root_upper_bound (u z : ℝ) (hu : 0 ≤ u) :
    Real.sqrt (discriminant u z) ≤ 1 + radiusSq u z - blockTrace z := by
  have hd := discriminant_nonneg u z hu
  have hr := Real.sq_sqrt hd
  have hs := Real.sqrt_nonneg (discriminant u z)
  have hb := root_bound_nonneg u z hu
  have hi := gap_square_identity u z
  have hsq := sq_nonneg (radiusSq u z - z)
  nlinarith

/-- This bound is valid even outside the unit ball when `u` is nonnegative. -/
theorem chshQuarterSq_le_one (u z : ℝ) (hu : 0 ≤ u) :
    chshQuarterSq u z ≤ 1 := by
  have h := root_upper_bound u z hu
  unfold chshQuarterSq middle upper
  linarith

/-- Exact equality locus; no target inequality is an assumption. -/
theorem chshQuarterSq_eq_one_iff (u z : ℝ) (hu : 0 ≤ u) :
    chshQuarterSq u z = 1 ↔ radiusSq u z = z := by
  have hd := discriminant_nonneg u z hu
  have hr := Real.sq_sqrt hd
  have hs := Real.sqrt_nonneg (discriminant u z)
  have hb := root_bound_nonneg u z hu
  have hi := gap_square_identity u z
  unfold chshQuarterSq middle upper
  constructor
  · intro heq
    have he : Real.sqrt (discriminant u z) =
        1 + radiusSq u z - blockTrace z := by linarith
    rw [he] at hr
    nlinarith [sq_nonneg (radiusSq u z - z)]
  · intro heq
    have he : Real.sqrt (discriminant u z) =
        1 + radiusSq u z - blockTrace z := by
      rw [heq] at hi
      nlinarith
    linarith

/-- The same equality locus written as a sphere of radius 1/2. -/
theorem equality_sphere (u z : ℝ) (hu : 0 ≤ u) :
    chshQuarterSq u z = 1 ↔ u + (z - 1 / 2) ^ 2 = 1 / 4 := by
  rw [chshQuarterSq_eq_one_iff u z hu]
  unfold radiusSq
  constructor <;> intro h <;> nlinarith

/-- Relative location of the transverse eigenvalue in the axial spectrum. -/
theorem middle_discriminant_identity (u z : ℝ) :
    discriminant u z - (2 * middle u z - blockTrace z) ^ 2 =
      2 * middle u z * u := by
  unfold discriminant blockTrace middle radiusSq
  ring

theorem middle_nonneg (u z : ℝ) (hr : radiusSq u z ≤ 1) :
    0 ≤ middle u z := by
  unfold middle
  linarith

/-- Therefore `middle + upper` really selects the largest two roots. -/
theorem spectral_order (u z : ℝ) (hu : 0 ≤ u)
    (hr : radiusSq u z ≤ 1) :
    lower u z ≤ middle u z ∧ middle u z ≤ upper u z := by
  have hd := discriminant_nonneg u z hu
  have hs := Real.sqrt_nonneg (discriminant u z)
  have hsq := Real.sq_sqrt hd
  have hm := middle_nonneg u z hr
  have hi := middle_discriminant_identity u z
  have hp : 0 ≤ 2 * middle u z * u := by positivity
  have hl : -Real.sqrt (discriminant u z) ≤
      2 * middle u z - blockTrace z := by nlinarith
  have hh : 2 * middle u z - blockTrace z ≤
      Real.sqrt (discriminant u z) := by nlinarith
  unfold lower upper
  constructor <;> linarith

/-- The axial eigenvalues solve the exact characteristic polynomial. -/
theorem block_eigenvalue_equations (u z : ℝ) (hu : 0 ≤ u) :
    (lower u z) ^ 2 - blockTrace z * lower u z +
        middle u z * (1 + z) ^ 2 / 4 = 0 ∧
    (upper u z) ^ 2 - blockTrace z * upper u z +
        middle u z * (1 + z) ^ 2 / 4 = 0 := by
  have hs := Real.sq_sqrt (discriminant_nonneg u z hu)
  unfold lower upper
  have hd : discriminant u z = blockTrace z ^ 2 -
      (1 - radiusSq u z) * (1 + z) ^ 2 / 2 := rfl
  unfold middle
  constructor <;> nlinarith

/-- Strictly interior equality points have `0 ≤ z < 1`. -/
theorem equality_parameter_range (u z : ℝ) (hu : 0 ≤ u)
    (hr : radiusSq u z < 1) (heq : chshQuarterSq u z = 1) :
    0 ≤ z ∧ z < 1 := by
  have he := (chshQuarterSq_eq_one_iff u z hu).mp heq
  have hn : 0 ≤ radiusSq u z := by
    unfold radiusSq
    positivity
  constructor <;> linarith

/-- Each height in [0,1) gives a nonnegative transverse square and equality. -/
theorem equality_parameterization (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ z - z ^ 2 ∧
    radiusSq (z - z ^ 2) z < 1 ∧
    chshQuarterSq (z - z ^ 2) z = 1 := by
  have hu : 0 ≤ z - z ^ 2 := by nlinarith
  refine ⟨hu, ?_, ?_⟩
  · unfold radiusSq
    linarith
  · apply (chshQuarterSq_eq_one_iff (z - z ^ 2) z hu).mpr
    unfold radiusSq
    ring

end
end CriticalCap
