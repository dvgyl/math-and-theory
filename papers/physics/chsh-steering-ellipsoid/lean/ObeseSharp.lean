import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Exact eigenvalue proof of joint centre/marginal sharpness for the maximally
obese ellipsoid family. All positivity, root ordering, upper bounds, equality
cases and attaining parameters are proved below without assuming a CHSH bound.
The link from density operators to this explicit Gram block is analytic in the
accompanying report, not silently included as a Lean hypothesis.
-/

set_option autoImplicit false

namespace ObeseSharp
noncomputable section

def radiusSq (u z : ℝ) : ℝ := u + z ^ 2
def q (c u z : ℝ) : ℝ := (1 - c) * (1 - radiusSq u z)
def k (c u z : ℝ) : ℝ := (1 - 2 * c) * (1 - radiusSq u z)
def axial (c z : ℝ) : ℝ := c + (1 - c) * z
def xx (c z : ℝ) : ℝ := (1 - c) * (1 - z ^ 2)
def zz (c u z : ℝ) : ℝ := k c u z + axial c z ^ 2
def offSq (c u z : ℝ) : ℝ := (1 - c) * u * axial c z ^ 2
def trace (c u z : ℝ) : ℝ := xx c z + zz c u z
def discr (c u z : ℝ) : ℝ := (xx c z - zz c u z) ^ 2 + 4 * offSq c u z
def lower (c u z : ℝ) : ℝ := (trace c u z - Real.sqrt (discr c u z)) / 2
def upper (c u z : ℝ) : ℝ := (trace c u z + Real.sqrt (discr c u z)) / 2
def M (c u z : ℝ) : ℝ := q c u z + upper c u z
def H (c u z : ℝ) : ℝ := 1 + k c u z
def h (c u z : ℝ) : ℝ := H c u z - q c u z

theorem first_principal_gap (c u z : ℝ) :
    h c u z - xx c z = c * u + z ^ 2 := by
  unfold h H q k xx radiusSq
  ring

theorem second_principal_gap (c u z : ℝ) :
    h c u z - zz c u z = (1 - c) * (u + c * (z - 1) ^ 2) := by
  simp only [h, H, q, k, zz, axial, radiusSq]
  ring

/-- The determinant of `h I - B` factors as a positive multiple of one square. -/
theorem determinant_gap (c u z : ℝ) :
    (h c u z - xx c z) * (h c u z - zz c u z) - offSq c u z =
      c * (1 - c) * (radiusSq u z - z) ^ 2 := by
  simp only [h, H, q, k, xx, zz, offSq, axial, radiusSq]
  ring

/-- Equivalent discriminant identity, used for the exact radical comparison. -/
theorem root_gap (c u z : ℝ) :
    (2 * h c u z - trace c u z) ^ 2 - discr c u z =
      4 * c * (1 - c) * (radiusSq u z - z) ^ 2 := by
  have hd := determinant_gap c u z
  unfold trace discr
  nlinarith

theorem discr_nonneg (c u z : ℝ) (hc : c ≤ 1) (hu : 0 ≤ u) :
    0 ≤ discr c u z := by
  unfold discr offSq
  have hp : 0 ≤ 1 - c := by linarith
  positivity

theorem root_target_nonneg (c u z : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu : 0 ≤ u) :
    0 ≤ 2 * h c u z - trace c u z := by
  have h1 := first_principal_gap c u z
  have h2 := second_principal_gap c u z
  have hp : 0 ≤ 1 - c := by linarith
  have hp1 : 0 ≤ c * u + z ^ 2 := by positivity
  have hp2 : 0 ≤ (1 - c) * (u + c * (z - 1) ^ 2) := by positivity
  unfold trace
  linarith

/-- A checked bound for the actual larger eigenvalue, not a numerical test. -/
theorem upper_le_h (c u z : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu : 0 ≤ u) :
    upper c u z ≤ h c u z := by
  have hd := discr_nonneg c u z hc1 hu
  have hs := Real.sqrt_nonneg (discr c u z)
  have hs2 := Real.sq_sqrt hd
  have ht := root_target_nonneg c u z hc0 hc1 hu
  have hg := root_gap c u z
  have hp : 0 ≤ 1 - c := by linarith
  have hn : 0 ≤ 4 * c * (1 - c) * (radiusSq u z - z) ^ 2 := by positivity
  unfold upper
  nlinarith

theorem M_le_H (c u z : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu : 0 ≤ u) :
    M c u z ≤ H c u z := by
  have hb := upper_le_h c u z hc0 hc1 hu
  unfold M h at *
  linarith

/-- For nonendpoint centres, exactly one quadratic equation describes equality. -/
theorem M_eq_H_iff (c u z : ℝ) (hc0 : 0 < c)
    (hc1 : c < 1) (hu : 0 ≤ u) :
    M c u z = H c u z ↔ radiusSq u z = z := by
  have hd := discr_nonneg c u z (le_of_lt hc1) hu
  have hs := Real.sqrt_nonneg (discr c u z)
  have hs2 := Real.sq_sqrt hd
  have ht := root_target_nonneg c u z (le_of_lt hc0) (le_of_lt hc1) hu
  have hg := root_gap c u z
  have hp0 : 0 < 1 - c := by linarith
  have hp : 0 < 4 * c * (1 - c) := by positivity
  have hb : M c u z = H c u z ↔
      Real.sqrt (discr c u z) = 2 * h c u z - trace c u z := by
    unfold M upper h
    constructor <;> intro he <;> linarith
  rw [hb]
  constructor
  · intro he
    rw [he] at hs2
    have hzero : (radiusSq u z - z) ^ 2 = 0 := by
      have hprod : (4 * c * (1 - c)) * (radiusSq u z - z) ^ 2 = 0 := by
        nlinarith
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hp)
    nlinarith
  · intro he
    rw [he] at hg
    nlinarith

/-- The equality locus is a sphere independent of the centre parameter. -/
theorem equality_sphere (c u z : ℝ) (hc0 : 0 < c)
    (hc1 : c < 1) (hu : 0 ≤ u) :
    M c u z = H c u z ↔ u + (z - 1 / 2) ^ 2 = 1 / 4 := by
  rw [M_eq_H_iff c u z hc0 hc1 hu]
  unfold radiusSq
  constructor <;> intro he <;> nlinarith

/-- The transverse eigenvalue lies between the two axial-block eigenvalues. -/
theorem middle_root_gap (c u z : ℝ) :
    discr c u z - (2 * q c u z - trace c u z) ^ 2 =
      4 * c * (1 - c) * u * (1 - radiusSq u z) := by
  unfold discr trace xx zz offSq axial q k radiusSq
  ring

theorem spectral_order (c u z : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu : 0 ≤ u) (hr : radiusSq u z ≤ 1) :
    lower c u z ≤ q c u z ∧ q c u z ≤ upper c u z := by
  have hd := discr_nonneg c u z hc1 hu
  have hs := Real.sqrt_nonneg (discr c u z)
  have hs2 := Real.sq_sqrt hd
  have hg := middle_root_gap c u z
  have hp : 0 ≤ 1 - c := by linarith
  have hR : 0 ≤ 1 - radiusSq u z := by linarith
  have hn : 0 ≤ 4 * c * (1 - c) * u * (1 - radiusSq u z) := by positivity
  have hl : -Real.sqrt (discr c u z) ≤
      2 * q c u z - trace c u z := by nlinarith
  have hh : 2 * q c u z - trace c u z ≤
      Real.sqrt (discr c u z) := by nlinarith
  unfold lower upper
  constructor <;> linarith

/-- Both radical roots solve the characteristic polynomial of the axial block. -/
theorem block_eigenvalue_equations (c u z : ℝ) (hc : c ≤ 1) (hu : 0 ≤ u) :
    (lower c u z) ^ 2 - trace c u z * lower c u z +
        xx c z * zz c u z - offSq c u z = 0 ∧
    (upper c u z) ^ 2 - trace c u z * upper c u z +
        xx c z * zz c u z - offSq c u z = 0 := by
  have hs2 := Real.sq_sqrt (discr_nonneg c u z hc hu)
  have hd : discr c u z =
      trace c u z ^ 2 - 4 * (xx c z * zz c u z - offSq c u z) := by
    unfold discr trace
    ring
  unfold lower upper
  constructor <;> nlinarith

/-- Attainment for every prescribed squared Bob marginal length `s < 1`. -/
theorem prescribed_radius_attainment (c s : ℝ) (hc0 : 0 < c)
    (hc1 : c < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ s * (1 - s) ∧
    radiusSq (s * (1 - s)) s = s ∧
    radiusSq (s * (1 - s)) s < 1 ∧
    M c (s * (1 - s)) s = 1 + (1 - 2 * c) * (1 - s) := by
  have hs : 0 ≤ 1 - s := by linarith
  have hu : 0 ≤ s * (1 - s) := by positivity
  have hr : radiusSq (s * (1 - s)) s = s := by
    unfold radiusSq
    ring
  refine ⟨hu, hr, ?_, ?_⟩
  · simpa only [hr] using hs1
  · have he := (M_eq_H_iff c (s * (1 - s)) s hc0 hc1 hu).mpr hr
    simpa only [H, k, hr] using he

/-- The centre-only conjecture follows algebraically from this joint envelope. -/
theorem H_le_centre_envelope (c u z : ℝ) (hu : 0 ≤ u) (hr : radiusSq u z ≤ 1) :
    H c u z ≤ max (2 * (1 - c)) 1 := by
  have hR : 0 ≤ radiusSq u z := by
    unfold radiusSq
    positivity
  unfold H k
  by_cases hc : c ≤ 1 / 2
  · have he : 1 ≤ 2 * (1 - c) := by linarith
    rw [max_eq_left he]
    have hc2 : 0 ≤ 1 - 2 * c := by linarith
    have hp : 0 ≤ (1 - 2 * c) * radiusSq u z := by positivity
    nlinarith
  · have he : 2 * (1 - c) ≤ 1 := by linarith
    rw [max_eq_right he]
    have hp : (1 - 2 * c) * (1 - radiusSq u z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith

/-- At centre zero the family consists of pure states and every filter is sharp. -/
theorem endpoint_zero (u z : ℝ) (hu : 0 ≤ u) :
    M 0 u z = H 0 u z := by
  have hR : 0 ≤ radiusSq u z := by
    unfold radiusSq
    positivity
  have hd : discr 0 u z = radiusSq u z ^ 2 := by
    unfold discr xx zz offSq axial k radiusSq
    ring
  have hs : Real.sqrt (discr 0 u z) = radiusSq u z := by
    rw [hd, Real.sqrt_sq hR]
  unfold M upper H q k trace xx zz axial
  rw [hs]
  simp only [k]
  ring

/-- At centre one the family is product and every filter is sharp. -/
theorem endpoint_one (u z : ℝ) (hu : 0 ≤ u) :
    M 1 u z = H 1 u z := by
  have hR : 0 ≤ radiusSq u z := by
    unfold radiusSq
    positivity
  have hd : discr 1 u z = radiusSq u z ^ 2 := by
    unfold discr xx zz offSq axial k radiusSq
    ring
  have hs : Real.sqrt (discr 1 u z) = radiusSq u z := by
    rw [hd, Real.sqrt_sq hR]
  unfold M upper H q k trace xx zz axial
  rw [hs]
  simp only [k]
  ring

/-- Below the critical centre, nonzero Bob marginal excludes centre-only equality. -/
theorem centre_envelope_strict_below (c u z : ℝ) (hc : c < 1 / 2)
    (hr : 0 < radiusSq u z) :
    H c u z < 2 * (1 - c) := by
  have hp : 0 < 1 - 2 * c := by linarith
  have hm : 0 < (1 - 2 * c) * radiusSq u z := mul_pos hp hr
  unfold H k
  nlinarith

/-- Above the critical centre, invertible filters exclude centre-only equality. -/
theorem centre_envelope_strict_above (c u z : ℝ) (hc : 1 / 2 < c)
    (hr : radiusSq u z < 1) :
    H c u z < 1 := by
  have hp : 1 - 2 * c < 0 := by linarith
  have hR : 0 < 1 - radiusSq u z := by linarith
  have hm : (1 - 2 * c) * (1 - radiusSq u z) < 0 := mul_neg_of_neg_of_pos hp hR
  unfold H k
  linarith

/-- The critical centre has a flat joint envelope. -/
theorem critical_envelope (u z : ℝ) : H (1 / 2) u z = 1 := by
  unfold H k
  ring

/-- The exact algebraic eigenvalue quantity is nonnegative on the physical domain. -/
theorem M_nonneg (c u z : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu : 0 ≤ u) (hr : radiusSq u z ≤ 1) :
    0 ≤ M c u z := by
  have horder := (spectral_order c u z hc0 hc1 hu hr).2
  have hp : 0 ≤ 1 - c := by linarith
  have hR : 0 ≤ 1 - radiusSq u z := by linarith
  have hq : 0 ≤ q c u z := by
    unfold q
    positivity
  unfold M
  linarith

/-- Standard CHSH normalization of the proved bound. -/
theorem beta_le (c u z : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu : 0 ≤ u) :
    2 * Real.sqrt (M c u z) ≤ 2 * Real.sqrt (H c u z) := by
  have hs := Real.sqrt_le_sqrt (M_le_H c u z hc0 hc1 hu)
  linarith

end
end ObeseSharp
