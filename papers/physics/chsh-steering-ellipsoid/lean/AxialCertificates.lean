import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Exact determinant certificates for axial steering ellipsoids. Here S=s² is the
squared transverse semiaxis, t is the signed axial coefficient (the written
classification uses t≥0), c is the centre coordinate, r is Bob's radius, and z
is its axial coordinate. Off-diagonal entries enter only through their square,
so every identity is polynomial or a rational identity with D=S-t² ≠ 0.
These identities do not assume the desired spectral inequality.

The second part defines the two actual radical roots of the real symmetric
2x2 block, proves their characteristic equations and interlacing, and derives
the oblate spectral upper bounds and equality directions from principal gaps.
It does not encode the density-operator/filtering/Horodecki bridge.
-/

set_option autoImplicit false

namespace AxialCertificates
noncomputable section

def q (S r : ℝ) : ℝ := S * (1 - r ^ 2)
def difference (S t : ℝ) : ℝ := S - t ^ 2
def b11 (S z : ℝ) : ℝ := S * (1 - z ^ 2)
def b22 (c t r z : ℝ) : ℝ := (1 - r ^ 2) * (t ^ 2 - c ^ 2) + (c + t * z) ^ 2
def offSquare (S c t r z : ℝ) : ℝ := S * (r ^ 2 - z ^ 2) * (c + t * z) ^ 2
def characteristic (S c t r z h : ℝ) : ℝ :=
  (h - b11 S z) * (h - b22 c t r z) - offSquare S c t r z

def interiorCap (S c t r : ℝ) : ℝ := S + S * c ^ 2 * r ^ 2 / difference S t
def interiorZ (S c t r : ℝ) : ℝ := c * t * r ^ 2 / difference S t
def boundaryCap (c t r : ℝ) : ℝ := (t + c * r) ^ 2

/-- Exact interlacing sign, including the transition to the prolate case. -/
theorem interlacing_identity (S c t r z : ℝ) :
    characteristic S c t r z (q S r) =
      -S * (r ^ 2 - z ^ 2) * (1 - r ^ 2) * (difference S t + c ^ 2) := by
  unfold characteristic q b11 b22 offSquare difference
  ring

/-- The interior cap has a perfect-square characteristic residual. -/
theorem interior_square (S c t r z : ℝ) (hD : difference S t ≠ 0) :
    characteristic S c t r z (interiorCap S c t r) =
      S * (difference S t + c ^ 2) * (z - interiorZ S c t r) ^ 2 := by
  unfold characteristic b11 b22 offSquare interiorCap interiorZ
  field_simp [hD]
  unfold difference
  ring

/-- The interior cap's first principal gap is manifestly nonnegative. -/
theorem interior_first_gap (S c t r z : ℝ) :
    interiorCap S c t r - b11 S z =
      S * z ^ 2 + S * c ^ 2 * r ^ 2 / difference S t := by
  unfold interiorCap b11
  ring

/-- An exact boundary factorization; no branch hypothesis is built into it. -/
theorem boundary_factorization (S c t r z : ℝ) :
    characteristic S c t r z (boundaryCap c t r) =
      (boundaryCap c t r * difference S t + q S r * c ^ 2) * (r - z) ^ 2 +
      2 * (c + r * t) * (t + c * r) *
        (c * t * r - difference S t) * (r - z) := by
  unfold characteristic b11 b22 offSquare boundaryCap difference q
  ring

/-- Difference of the two caps is another exact square. -/
theorem cap_difference_square (S c t r : ℝ) (hD : difference S t ≠ 0) :
    (interiorCap S c t r - boundaryCap c t r) * difference S t =
      (difference S t - c * t * r) ^ 2 := by
  unfold interiorCap boundaryCap
  field_simp [hD]
  unfold difference
  ring

/-- The two candidate values agree exactly at the angular transition. -/
theorem transition_agreement (S c t r : ℝ) (hD : difference S t ≠ 0)
    (htrans : c * t * r = difference S t) :
    interiorCap S c t r = boundaryCap c t r := by
  have hh := cap_difference_square S c t r hD
  rw [htrans, sub_self, zero_pow (by decide : 2 ≠ 0)] at hh
  have hz := (mul_eq_zero.mp hh).resolve_right hD
  exact sub_eq_zero.mp hz

/-- Feasibility of the exact interior direction follows from the branch test. -/
theorem interior_direction_feasible (S c t r : ℝ)
    (hD : 0 < difference S t) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hbranch : c * t * r ≤ difference S t) :
    0 ≤ interiorZ S c t r ∧ interiorZ S c t r ≤ r := by
  unfold interiorZ
  constructor
  · positivity
  · apply (div_le_iff₀ hD).mpr
    have hm := mul_le_mul_of_nonneg_right hbranch hr
    nlinarith

/-- Nonnegative determinant in the oblate boundary branch. -/
theorem oblate_boundary_nonnegative (S c t r z : ℝ)
    (hS : 0 ≤ S) (hD : 0 ≤ difference S t)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ≤ r) (hbranch : difference S t ≤ c * t * r) :
    0 ≤ characteristic S c t r z (boundaryCap c t r) := by
  rw [boundary_factorization]
  have hq : 0 ≤ q S r := by
    unfold q
    exact mul_nonneg hS (by nlinarith)
  have hcap : 0 ≤ boundaryCap c t r := sq_nonneg _
  have ha : 0 ≤ boundaryCap c t r * difference S t + q S r * c ^ 2 := by positivity
  have hb : 0 ≤ 2 * (c + r * t) * (t + c * r) *
      (c * t * r - difference S t) * (r - z) := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · linarith
  exact add_nonneg (mul_nonneg ha (sq_nonneg _)) hb

/-- The other interior principal gap also has a sum-of-squares certificate. -/
theorem interior_second_gap (S c t r z : ℝ) (hD : difference S t ≠ 0) :
    interiorCap S c t r - b22 c t r z =
      ((difference S t - c * t * z) ^ 2 +
        t ^ 2 * (difference S t + c ^ 2) * (r ^ 2 - z ^ 2)) / difference S t := by
  unfold interiorCap b22
  field_simp [hD]
  unfold difference
  ring

/-- The boundary cap's second principal gap is nonnegative throughout the ball. -/
theorem boundary_second_gap (c t r z : ℝ) :
    boundaryCap c t r - b22 c t r z =
      (r - z) * (t ^ 2 * (r + z) + 2 * c * t) := by
  unfold boundaryCap b22
  ring

def trace (S c t r z : ℝ) : ℝ := b11 S z + b22 c t r z
def discriminant (S c t r z : ℝ) : ℝ :=
  (b11 S z - b22 c t r z) ^ 2 + 4 * offSquare S c t r z
def lower (S c t r z : ℝ) : ℝ :=
  (trace S c t r z - Real.sqrt (discriminant S c t r z)) / 2
def upper (S c t r z : ℝ) : ℝ :=
  (trace S c t r z + Real.sqrt (discriminant S c t r z)) / 2
def spectralSum (S c t r z : ℝ) : ℝ := q S r + upper S c t r z

theorem offSquare_nonnegative (S c t r z : ℝ) (hS : 0 ≤ S)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    0 ≤ offSquare S c t r z := by
  unfold offSquare
  positivity

theorem discriminant_nonnegative (S c t r z : ℝ) (hS : 0 ≤ S)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    0 ≤ discriminant S c t r z := by
  have hw := offSquare_nonnegative S c t r z hS hu
  unfold discriminant
  positivity

/-- A universal 2x2 radical comparison identity, independent of branch tests. -/
theorem radical_gap (S c t r z h : ℝ) :
    (2 * h - trace S c t r z) ^ 2 - discriminant S c t r z =
      4 * characteristic S c t r z h := by
  unfold trace discriminant characteristic
  ring

/-- These are the two genuine quadratic eigenvalue roots of the block. -/
theorem block_root_equations (S c t r z : ℝ) (hS : 0 ≤ S)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    characteristic S c t r z (lower S c t r z) = 0 ∧
    characteristic S c t r z (upper S c t r z) = 0 := by
  have hs2 := Real.sq_sqrt (discriminant_nonnegative S c t r z hS hu)
  have hd : discriminant S c t r z =
      trace S c t r z ^ 2 -
        4 * (b11 S z * b22 c t r z - offSquare S c t r z) := by
    unfold discriminant trace
    ring
  unfold characteristic lower upper
  unfold trace at *
  constructor <;> nlinarith

theorem roots_ordered (S c t r z : ℝ) :
    lower S c t r z ≤ upper S c t r z := by
  have hs := Real.sqrt_nonneg (discriminant S c t r z)
  unfold lower upper
  linarith

/-- The y eigenvalue lies between the radical block roots in the oblate regime. -/
theorem oblate_interlacing (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : 0 ≤ difference S t) (hR : r ^ 2 ≤ 1)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    lower S c t r z ≤ q S r ∧ q S r ≤ upper S c t r z := by
  have hd := discriminant_nonnegative S c t r z hS hu
  have hs := Real.sqrt_nonneg (discriminant S c t r z)
  have hs2 := Real.sq_sqrt hd
  have hg := radical_gap S c t r z (q S r)
  have hchar : characteristic S c t r z (q S r) ≤ 0 := by
    rw [interlacing_identity]
    have hR0 : 0 ≤ 1 - r ^ 2 := by linarith
    have hp : 0 ≤ S * (r ^ 2 - z ^ 2) * (1 - r ^ 2) *
        (difference S t + c ^ 2) := by positivity
    nlinarith
  have hl : -Real.sqrt (discriminant S c t r z) ≤
      2 * q S r - trace S c t r z := by nlinarith
  have hh : 2 * q S r - trace S c t r z ≤
      Real.sqrt (discriminant S c t r z) := by nlinarith
  unfold lower upper
  constructor <;> linarith

/-- The defined spectral sum is actually the largest pair sum of the three roots. -/
theorem spectralSum_is_largest_pair (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : 0 ≤ difference S t) (hR : r ^ 2 ≤ 1)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    max (lower S c t r z + q S r)
      (max (lower S c t r z + upper S c t r z)
        (q S r + upper S c t r z)) = spectralSum S c t r z := by
  obtain ⟨hl, hh⟩ := oblate_interlacing S c t r z hS hD hR hu
  have hlo := roots_ordered S c t r z
  unfold spectralSum
  rw [max_eq_right (by linarith :
    lower S c t r z + upper S c t r z ≤ q S r + upper S c t r z)]
  exact max_eq_right (by linarith)

/-- Positive principal gaps and determinant bound the explicit larger root. -/
theorem upper_le_of_principal_gaps (S c t r z h : ℝ)
    (hS : 0 ≤ S) (hu : 0 ≤ r ^ 2 - z ^ 2)
    (hx : 0 ≤ h - b11 S z) (hy : 0 ≤ h - b22 c t r z)
    (hdet : 0 ≤ characteristic S c t r z h) :
    upper S c t r z ≤ h := by
  have hd := discriminant_nonnegative S c t r z hS hu
  have hs := Real.sqrt_nonneg (discriminant S c t r z)
  have hs2 := Real.sq_sqrt hd
  have ht : 0 ≤ 2 * h - trace S c t r z := by
    unfold trace
    linarith
  have hg := radical_gap S c t r z h
  unfold upper
  nlinarith

/-- With principal gaps, equality of the larger root is exactly determinant zero. -/
theorem upper_eq_iff_characteristic_zero (S c t r z h : ℝ)
    (hS : 0 ≤ S) (hu : 0 ≤ r ^ 2 - z ^ 2)
    (hx : 0 ≤ h - b11 S z) (hy : 0 ≤ h - b22 c t r z) :
    upper S c t r z = h ↔ characteristic S c t r z h = 0 := by
  have hd := discriminant_nonnegative S c t r z hS hu
  have hs := Real.sqrt_nonneg (discriminant S c t r z)
  have hs2 := Real.sq_sqrt hd
  have ht : 0 ≤ 2 * h - trace S c t r z := by
    unfold trace
    linarith
  have hg := radical_gap S c t r z h
  have heq : upper S c t r z = h ↔
      Real.sqrt (discriminant S c t r z) = 2 * h - trace S c t r z := by
    unfold upper
    constructor <;> intro he <;> linarith
  rw [heq]
  constructor <;> intro he
  · rw [he] at hs2
    nlinarith
  · nlinarith

theorem interior_principal_gaps_nonnegative (S c t r z : ℝ)
    (hD : 0 < difference S t) (hu : 0 ≤ r ^ 2 - z ^ 2) :
    0 ≤ interiorCap S c t r - b11 S z ∧
    0 ≤ interiorCap S c t r - b22 c t r z := by
  have hS : 0 < S := by
    unfold difference at hD
    nlinarith [sq_nonneg t]
  constructor
  · rw [interior_first_gap]
    positivity
  · rw [interior_second_gap S c t r z (ne_of_gt hD)]
    positivity

/-- A proved explicit-eigenvalue bound for every feasible interior-block direction. -/
theorem interior_upper_bound (S c t r z : ℝ)
    (hD : 0 < difference S t) (hu : 0 ≤ r ^ 2 - z ^ 2) :
    upper S c t r z ≤ interiorCap S c t r := by
  have hS : 0 ≤ S := by
    unfold difference at hD
    nlinarith [sq_nonneg t]
  obtain ⟨hx, hy⟩ := interior_principal_gaps_nonnegative S c t r z hD hu
  apply upper_le_of_principal_gaps S c t r z (interiorCap S c t r) hS hu hx hy
  rw [interior_square S c t r z (ne_of_gt hD)]
  positivity

/-- The exact equality latitude is proved from the radical formula, not assumed. -/
theorem interior_upper_eq_iff (S c t r z : ℝ)
    (hD : 0 < difference S t) (hu : 0 ≤ r ^ 2 - z ^ 2) :
    upper S c t r z = interiorCap S c t r ↔ z = interiorZ S c t r := by
  have hS : 0 < S := by
    unfold difference at hD
    nlinarith [sq_nonneg t]
  obtain ⟨hx, hy⟩ := interior_principal_gaps_nonnegative S c t r z hD hu
  rw [upper_eq_iff_characteristic_zero S c t r z (interiorCap S c t r)
    (le_of_lt hS) hu hx hy, interior_square S c t r z (ne_of_gt hD)]
  have hp : 0 < S * (difference S t + c ^ 2) := by positivity
  constructor
  · intro he
    have hz2 : (z - interiorZ S c t r) ^ 2 = 0 :=
      (mul_eq_zero.mp he).resolve_left (ne_of_gt hp)
    nlinarith
  · intro hz
    rw [hz, sub_self]
    simp

theorem interior_spectral_bound (S c t r z : ℝ)
    (hD : 0 < difference S t) (hu : 0 ≤ r ^ 2 - z ^ 2) :
    spectralSum S c t r z ≤ q S r + interiorCap S c t r := by
  have hh := interior_upper_bound S c t r z hD hu
  unfold spectralSum
  linarith

theorem interior_spectral_eq_iff (S c t r z : ℝ)
    (hD : 0 < difference S t) (hu : 0 ≤ r ^ 2 - z ^ 2) :
    spectralSum S c t r z = q S r + interiorCap S c t r ↔
      z = interiorZ S c t r := by
  unfold spectralSum
  rw [add_right_inj, interior_upper_eq_iff S c t r z hD hu]

/-- The maximizing latitude is feasible and attains the cap under the branch test. -/
theorem interior_prescribed_radius_attainment (S c t r : ℝ)
    (hD : 0 < difference S t) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hbranch : c * t * r ≤ difference S t) :
    0 ≤ interiorZ S c t r ∧ interiorZ S c t r ≤ r ∧
    spectralSum S c t r (interiorZ S c t r) = q S r + interiorCap S c t r := by
  obtain ⟨hz0, hzr⟩ := interior_direction_feasible S c t r hD hc ht hr hbranch
  have hu : 0 ≤ r ^ 2 - interiorZ S c t r ^ 2 := by nlinarith
  exact ⟨hz0, hzr, (interior_spectral_eq_iff S c t r (interiorZ S c t r) hD hu).mpr rfl⟩

theorem boundary_principal_gaps_nonnegative (S c t r z : ℝ)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) (hbranch : difference S t ≤ c * t * r) :
    0 ≤ boundaryCap c t r - b11 S z ∧
    0 ≤ boundaryCap c t r - b22 c t r z := by
  constructor
  · have hp : 0 ≤ c * t * r := by positivity
    have hcr : 0 ≤ c ^ 2 * r ^ 2 := by positivity
    have hsz : 0 ≤ S * z ^ 2 := by positivity
    unfold boundaryCap b11
    unfold difference at hbranch
    nlinarith
  · rw [boundary_second_gap c t r z]
    have hv : 0 ≤ r - z := by linarith
    have hw : 0 ≤ r + z := by linarith
    positivity

/-- The aligned branch bounds the explicit larger eigenvalue. -/
theorem oblate_boundary_upper_bound (S c t r z : ℝ)
    (hS : 0 ≤ S) (hD : 0 ≤ difference S t)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) (hbranch : difference S t ≤ c * t * r) :
    upper S c t r z ≤ boundaryCap c t r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  obtain ⟨hx, hy⟩ := boundary_principal_gaps_nonnegative S c t r z hS hc ht hr hz0 hz1 hbranch
  exact upper_le_of_principal_gaps S c t r z (boundaryCap c t r) hS hu hx hy
    (oblate_boundary_nonnegative S c t r z hS hD hc ht hr hr1 hz1 hbranch)

/-- Generic boundary equality: only the aligned direction reaches the cap. -/
theorem oblate_boundary_upper_eq_iff (S c t r z : ℝ)
    (hS : 0 < S) (hD : 0 ≤ difference S t)
    (hc : 0 < c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hr1 : r < 1)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) (hbranch : difference S t ≤ c * t * r) :
    upper S c t r z = boundaryCap c t r ↔ z = r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  obtain ⟨hx, hy⟩ := boundary_principal_gaps_nonnegative S c t r z
    (le_of_lt hS) (le_of_lt hc) ht hr hz0 hz1 hbranch
  rw [upper_eq_iff_characteristic_zero S c t r z (boundaryCap c t r)
    (le_of_lt hS) hu hx hy, boundary_factorization]
  have hq : 0 < q S r := by
    unfold q
    exact mul_pos hS (by nlinarith)
  have hcap : 0 ≤ boundaryCap c t r := sq_nonneg _
  have ha : 0 < boundaryCap c t r * difference S t + q S r * c ^ 2 := by positivity
  have hb : 0 ≤ 2 * (c + r * t) * (t + c * r) *
      (c * t * r - difference S t) * (r - z) := by
    have hdiff : 0 ≤ c * t * r - difference S t := by linarith
    have hz : 0 ≤ r - z := by linarith
    positivity
  constructor
  · intro he
    have hsquare : (r - z) ^ 2 = 0 := by nlinarith [sq_nonneg (r - z)]
    nlinarith
  · intro hz
    rw [hz, sub_self]
    simp

theorem oblate_boundary_spectral_bound (S c t r z : ℝ)
    (hS : 0 ≤ S) (hD : 0 ≤ difference S t)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) (hbranch : difference S t ≤ c * t * r) :
    spectralSum S c t r z ≤ q S r + boundaryCap c t r := by
  have hh := oblate_boundary_upper_bound S c t r z hS hD hc ht hr hr1 hz0 hz1 hbranch
  unfold spectralSum
  linarith

theorem oblate_boundary_prescribed_radius_attainment (S c t r : ℝ)
    (hS : 0 < S) (hD : 0 ≤ difference S t)
    (hc : 0 < c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hr1 : r < 1)
    (hbranch : difference S t ≤ c * t * r) :
    spectralSum S c t r r = q S r + boundaryCap c t r := by
  have hh := (oblate_boundary_upper_eq_iff S c t r r hS hD hc ht hr hr1
    (by linarith) (le_refl r) hbranch).mpr rfl
  unfold spectralSum
  rw [hh]

/-! Prolate blocks require a genuine ordering split: the y root can be middle
or smallest. The following theorems prove both branches explicitly. -/

def pairMaximum (S c t r z : ℝ) : ℝ :=
  max (lower S c t r z + q S r)
    (max (lower S c t r z + upper S c t r z)
      (q S r + upper S c t r z))

def boundaryCoefficient (S c t r : ℝ) : ℝ :=
  boundaryCap c t r * difference S t + q S r * c ^ 2
def boundaryLinear (S c t r : ℝ) : ℝ :=
  (c + r * t) * (t + c * r) * (c * t * r - difference S t)
def boundaryRemainder (S c t r z : ℝ) : ℝ :=
  boundaryCoefficient S c t r * (r - z) + 2 * boundaryLinear S c t r

theorem boundary_remainder_factorization (S c t r z : ℝ) :
    characteristic S c t r z (boundaryCap c t r) =
      (r - z) * boundaryRemainder S c t r z := by
  rw [boundary_factorization]
  unfold boundaryRemainder boundaryCoefficient boundaryLinear
  ring

theorem boundary_remainder_alternative (S c t r z : ℝ) :
    boundaryRemainder S c t r z =
      2 * c * t * (boundaryCap c t r - q S r) -
        boundaryCoefficient S c t r * (r + z) := by
  unfold boundaryRemainder boundaryCoefficient boundaryLinear boundaryCap difference q
  ring

theorem prolate_cap_above_q (S c t r : ℝ) (hS : 0 ≤ S)
    (hD : difference S t ≤ 0) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 ≤ boundaryCap c t r - q S r := by
  have hctr : 0 ≤ c * t * r := by positivity
  have hcr : 0 ≤ c ^ 2 * r ^ 2 := by positivity
  have hsr : 0 ≤ S * r ^ 2 := by positivity
  unfold boundaryCap q
  unfold difference at hD
  nlinarith

theorem prolate_cap_strictly_above_q (S c t r : ℝ) (hS : 0 ≤ S)
    (hD : difference S t < 0) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 < boundaryCap c t r - q S r := by
  have hctr : 0 ≤ c * t * r := by positivity
  have hcr : 0 ≤ c ^ 2 * r ^ 2 := by positivity
  have hsr : 0 ≤ S * r ^ 2 := by positivity
  unfold boundaryCap q
  unfold difference at hD
  nlinarith

/-- The affine residual is nonnegative at both relevant endpoints. -/
theorem prolate_remainder_nonnegative (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t ≤ 0) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    0 ≤ boundaryRemainder S c t r z := by
  have hv : 0 ≤ r - z := by linarith
  have hw : 0 ≤ r + z := by linarith
  have hdiff : 0 ≤ c * t * r - difference S t := by
    have hp : 0 ≤ c * t * r := by positivity
    linarith
  have hL : 0 ≤ boundaryLinear S c t r := by
    unfold boundaryLinear
    positivity
  by_cases hA : 0 ≤ boundaryCoefficient S c t r
  · unfold boundaryRemainder
    positivity
  · rw [boundary_remainder_alternative]
    have hcap := prolate_cap_above_q S c t r hS hD hc ht hr
    have hleft : 0 ≤ 2 * c * t * (boundaryCap c t r - q S r) := by positivity
    have hright : 0 ≤ -boundaryCoefficient S c t r * (r + z) :=
      mul_nonneg (by linarith) hw
    nlinarith

theorem prolate_remainder_positive (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t < 0) (hc : 0 < c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    0 < boundaryRemainder S c t r z := by
  have ht0 : 0 < t := by
    unfold difference at hD
    nlinarith
  have hv : 0 ≤ r - z := by linarith
  have hw : 0 ≤ r + z := by linarith
  have hdiff : 0 < c * t * r - difference S t := by
    have hp : 0 ≤ c * t * r := by positivity
    linarith
  have hL : 0 < boundaryLinear S c t r := by
    unfold boundaryLinear
    positivity
  by_cases hA : 0 ≤ boundaryCoefficient S c t r
  · unfold boundaryRemainder
    have hp : 0 ≤ boundaryCoefficient S c t r * (r - z) := mul_nonneg hA hv
    linarith
  · rw [boundary_remainder_alternative]
    have hcap := prolate_cap_strictly_above_q S c t r hS hD (le_of_lt hc) ht hr
    have hleft : 0 < 2 * c * t * (boundaryCap c t r - q S r) := by positivity
    have hright : 0 ≤ -boundaryCoefficient S c t r * (r + z) :=
      mul_nonneg (by linarith) hw
    nlinarith

theorem prolate_boundary_upper_bound (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t ≤ 0) (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    upper S c t r z ≤ boundaryCap c t r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  have hbranch : difference S t ≤ c * t * r := by
    have hp : 0 ≤ c * t * r := by positivity
    linarith
  obtain ⟨hx, hy⟩ := boundary_principal_gaps_nonnegative S c t r z hS hc ht hr hz0 hz1 hbranch
  apply upper_le_of_principal_gaps S c t r z (boundaryCap c t r) hS hu hx hy
  rw [boundary_remainder_factorization]
  exact mul_nonneg (by linarith)
    (prolate_remainder_nonnegative S c t r z hS hD hc ht hr hz0 hz1)

theorem prolate_boundary_upper_eq_iff (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t < 0) (hc : 0 < c) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    upper S c t r z = boundaryCap c t r ↔ z = r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  have hbranch : difference S t ≤ c * t * r := by
    have hp : 0 ≤ c * t * r := by positivity
    linarith
  obtain ⟨hx, hy⟩ := boundary_principal_gaps_nonnegative S c t r z
    hS (le_of_lt hc) ht hr hz0 hz1 hbranch
  rw [upper_eq_iff_characteristic_zero S c t r z (boundaryCap c t r) hS hu hx hy,
    boundary_remainder_factorization]
  have hp := prolate_remainder_positive S c t r z hS hD hc ht hr hz0 hz1
  constructor
  · intro he
    have hz := (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
    linarith
  · intro he
    rw [he, sub_self, zero_mul]

/-- Interlacing also holds for prolate blocks when translation is large enough. -/
theorem translation_interlacing (S c t r z : ℝ) (hS : 0 ≤ S)
    (hDC : 0 ≤ difference S t + c ^ 2) (hR : r ^ 2 ≤ 1)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    lower S c t r z ≤ q S r ∧ q S r ≤ upper S c t r z := by
  have hd := discriminant_nonnegative S c t r z hS hu
  have hs := Real.sqrt_nonneg (discriminant S c t r z)
  have hs2 := Real.sq_sqrt hd
  have hg := radical_gap S c t r z (q S r)
  have hchar : characteristic S c t r z (q S r) ≤ 0 := by
    rw [interlacing_identity]
    have hR0 : 0 ≤ 1 - r ^ 2 := by linarith
    have hp : 0 ≤ S * (r ^ 2 - z ^ 2) * (1 - r ^ 2) *
        (difference S t + c ^ 2) := by positivity
    nlinarith
  have hl : -Real.sqrt (discriminant S c t r z) ≤
      2 * q S r - trace S c t r z := by nlinarith
  have hh : 2 * q S r - trace S c t r z ≤
      Real.sqrt (discriminant S c t r z) := by nlinarith
  unfold lower upper
  constructor <;> linarith

theorem pairMaximum_of_interlacing (S c t r z : ℝ)
    (hl : lower S c t r z ≤ q S r) (hh : q S r ≤ upper S c t r z) :
    pairMaximum S c t r z = q S r + upper S c t r z := by
  have hlo := roots_ordered S c t r z
  unfold pairMaximum
  rw [max_eq_right (by linarith :
    lower S c t r z + upper S c t r z ≤ q S r + upper S c t r z)]
  exact max_eq_right (by linarith)

/-- In the other prolate regime, q is the smallest root, not the middle one. -/
theorem lower_above_q (S c t r z : ℝ) (hS : 0 ≤ S)
    (hDC : difference S t + c ^ 2 ≤ 0) (hR : r ^ 2 ≤ 1)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    q S r ≤ lower S c t r z := by
  have hR0 : 0 ≤ 1 - r ^ 2 := by linarith
  have hx : 0 ≤ b11 S z - q S r := by
    have hp : 0 ≤ S * (r ^ 2 - z ^ 2) := mul_nonneg hS hu
    unfold b11 q
    nlinarith
  have hy : 0 ≤ b22 c t r z - q S r := by
    have hp : 0 ≤ (1 - r ^ 2) * (-(difference S t + c ^ 2)) :=
      mul_nonneg hR0 (by linarith)
    unfold b22 q
    unfold difference at hp
    nlinarith [sq_nonneg (c + t * z)]
  have hchar : 0 ≤ characteristic S c t r z (q S r) := by
    rw [interlacing_identity]
    have hDCneg : 0 ≤ -(difference S t + c ^ 2) := by linarith
    have hp : 0 ≤ S * (r ^ 2 - z ^ 2) * (1 - r ^ 2) *
        (-(difference S t + c ^ 2)) := by positivity
    nlinarith
  have hd := discriminant_nonnegative S c t r z hS hu
  have hs := Real.sqrt_nonneg (discriminant S c t r z)
  have hs2 := Real.sq_sqrt hd
  have hg := radical_gap S c t r z (q S r)
  have htarg : 0 ≤ trace S c t r z - 2 * q S r := by
    unfold trace
    linarith
  unfold lower
  nlinarith

theorem pairMaximum_of_q_smallest (S c t r z : ℝ)
    (hl : q S r ≤ lower S c t r z) :
    pairMaximum S c t r z = trace S c t r z := by
  have hlo := roots_ordered S c t r z
  unfold pairMaximum
  rw [max_eq_left (by linarith : q S r + upper S c t r z ≤
    lower S c t r z + upper S c t r z)]
  rw [max_eq_right (by linarith : lower S c t r z + q S r ≤
    lower S c t r z + upper S c t r z)]
  unfold lower upper
  ring

theorem prolate_trace_gap (S c t r z : ℝ) :
    q S r + boundaryCap c t r - trace S c t r z =
      (r - z) * ((t ^ 2 - S) * (r + z) + 2 * c * t) := by
  unfold q boundaryCap trace b11 b22
  ring

theorem prolate_trace_upper_bound (S c t r z : ℝ)
    (hD : difference S t ≤ 0) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    trace S c t r z ≤ q S r + boundaryCap c t r := by
  have hgap := prolate_trace_gap S c t r z
  have hE : 0 ≤ t ^ 2 - S := by unfold difference at hD; linarith
  have hv : 0 ≤ r - z := by linarith
  have hw : 0 ≤ r + z := by linarith
  have hp : 0 ≤ (r - z) * ((t ^ 2 - S) * (r + z) + 2 * c * t) := by positivity
  linarith

theorem prolate_trace_eq_iff (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t < 0) (hc : 0 < c) (ht : 0 ≤ t)
    (hz0 : -r ≤ z) :
    trace S c t r z = q S r + boundaryCap c t r ↔ z = r := by
  have hE : 0 < t ^ 2 - S := by unfold difference at hD; linarith
  have ht0 : 0 < t := by nlinarith
  have hw : 0 ≤ r + z := by linarith
  have hp : 0 < (t ^ 2 - S) * (r + z) + 2 * c * t := by positivity
  have hgap := prolate_trace_gap S c t r z
  constructor
  · intro he
    have hzprod : (r - z) * ((t ^ 2 - S) * (r + z) + 2 * c * t) = 0 := by linarith
    have hz := (mul_eq_zero.mp hzprod).resolve_right (ne_of_gt hp)
    linarith
  · intro he
    rw [he, sub_self, zero_mul] at hgap
    rw [he]
    linarith

/-- Both prolate ordering branches give the same sharp bound on the largest pair. -/
theorem prolate_pair_bound (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t ≤ 0) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1) (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    pairMaximum S c t r z ≤ q S r + boundaryCap c t r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  by_cases hDC : 0 ≤ difference S t + c ^ 2
  · obtain ⟨hl, hh⟩ := translation_interlacing S c t r z hS hDC hR hu
    rw [pairMaximum_of_interlacing S c t r z hl hh]
    have hup := prolate_boundary_upper_bound S c t r z hS hD hc ht hr hz0 hz1
    linarith
  · have hsmall := lower_above_q S c t r z hS (by linarith) hR hu
    rw [pairMaximum_of_q_smallest S c t r z hsmall]
    exact prolate_trace_upper_bound S c t r z hD hc ht hz0 hz1

/-- Generic prolate equality is exactly the aligned filter direction. -/
theorem prolate_pair_eq_iff (S c t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t < 0) (hc : 0 < c) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1) (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    pairMaximum S c t r z = q S r + boundaryCap c t r ↔ z = r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  by_cases hDC : 0 ≤ difference S t + c ^ 2
  · obtain ⟨hl, hh⟩ := translation_interlacing S c t r z hS hDC hR hu
    rw [pairMaximum_of_interlacing S c t r z hl hh, add_right_inj]
    exact prolate_boundary_upper_eq_iff S c t r z hS hD hc ht hr hz0 hz1
  · have hsmall := lower_above_q S c t r z hS (by linarith) hR hu
    rw [pairMaximum_of_q_smallest S c t r z hsmall]
    exact prolate_trace_eq_iff S c t r z hS hD hc ht hz0

/-- Prolate attainment also includes centred ellipsoids and rank-one shapes. -/
theorem prolate_prescribed_radius_attainment (S c t r : ℝ) (hS : 0 ≤ S)
    (hD : difference S t ≤ 0) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1) :
    pairMaximum S c t r r = q S r + boundaryCap c t r := by
  have hu : 0 ≤ r ^ 2 - r ^ 2 := by linarith
  by_cases hDC : 0 ≤ difference S t + c ^ 2
  · obtain ⟨hl, hh⟩ := translation_interlacing S c t r r hS hDC hR hu
    rw [pairMaximum_of_interlacing S c t r r hl hh]
    have hbranch : difference S t ≤ c * t * r := by
      have hp : 0 ≤ c * t * r := by positivity
      linarith
    obtain ⟨hx, hy⟩ := boundary_principal_gaps_nonnegative S c t r r
      hS hc ht hr (by linarith) (le_refl r) hbranch
    have hchar : characteristic S c t r r (boundaryCap c t r) = 0 := by
      rw [boundary_remainder_factorization, sub_self, zero_mul]
    have he := (upper_eq_iff_characteristic_zero S c t r r (boundaryCap c t r)
      hS hu hx hy).mpr hchar
    rw [he]
  · have hsmall := lower_above_q S c t r r hS (by linarith) hR hu
    rw [pairMaximum_of_q_smallest S c t r r hsmall]
    have hg := prolate_trace_gap S c t r r
    rw [sub_self, zero_mul] at hg
    linarith

/-- The two poles, rather than a single pole, optimize a centred prolate shape. -/
theorem centred_prolate_pair_eq_iff (S t r z : ℝ) (hS : 0 ≤ S)
    (hD : difference S t < 0) (hR : r ^ 2 ≤ 1)
    (hu : 0 ≤ r ^ 2 - z ^ 2) :
    pairMaximum S 0 t r z = q S r + boundaryCap 0 t r ↔ z = r ∨ z = -r := by
  have hDC : difference S t + (0 : ℝ) ^ 2 ≤ 0 := by nlinarith
  have hsmall := lower_above_q S 0 t r z hS hDC hR hu
  rw [pairMaximum_of_q_smallest S 0 t r z hsmall]
  have hE : 0 < t ^ 2 - S := by unfold difference at hD; linarith
  have hg : q S r + boundaryCap 0 t r - trace S 0 t r z =
      (t ^ 2 - S) * ((r - z) * (r + z)) := by
    unfold q boundaryCap trace b11 b22
    ring
  constructor
  · intro he
    have hprod : (t ^ 2 - S) * ((r - z) * (r + z)) = 0 := by linarith
    have hzprod := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hE)
    rcases mul_eq_zero.mp hzprod with hleft | hright
    · left; linarith
    · right; linarith
  · intro he
    rcases he with hz | hz
    · rw [hz, sub_self, zero_mul, mul_zero] at hg
      rw [hz]
      linarith
    · rw [hz] at hg
      have hz0 : r + -r = 0 := by ring
      rw [hz0, mul_zero, mul_zero] at hg
      rw [hz]
      linarith

/-- The degenerate oblate boundary cases also attain at the aligned pole. -/
theorem oblate_boundary_pair_attainment (S c t r : ℝ) (hS : 0 ≤ S)
    (hD : 0 ≤ difference S t) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1) (hbranch : difference S t ≤ c * t * r) :
    pairMaximum S c t r r = q S r + boundaryCap c t r := by
  have hu : 0 ≤ r ^ 2 - r ^ 2 := by linarith
  obtain ⟨hl, hh⟩ := oblate_interlacing S c t r r hS hD hR hu
  rw [pairMaximum_of_interlacing S c t r r hl hh]
  obtain ⟨hx, hy⟩ := boundary_principal_gaps_nonnegative S c t r r
    hS hc ht hr (by linarith) (le_refl r) hbranch
  have hchar : characteristic S c t r r (boundaryCap c t r) = 0 := by
    rw [boundary_remainder_factorization, sub_self, zero_mul]
  have he := (upper_eq_iff_characteristic_zero S c t r r (boundaryCap c t r)
    hS hu hx hy).mpr hchar
  rw [he]

def exactEnvelope (S c t r : ℝ) : ℝ :=
  if 0 < difference S t ∧ c * t * r ≤ difference S t then
    q S r + interiorCap S c t r
  else q S r + boundaryCap c t r

/-- Unified sharp upper bound for the actual largest pair of the three roots. -/
theorem axial_pair_bound (S c t r z : ℝ) (hS : 0 ≤ S)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1)
    (hz0 : -r ≤ z) (hz1 : z ≤ r) :
    pairMaximum S c t r z ≤ exactEnvelope S c t r := by
  have hu : 0 ≤ r ^ 2 - z ^ 2 := by nlinarith
  by_cases hi : 0 < difference S t ∧ c * t * r ≤ difference S t
  · rw [exactEnvelope, if_pos hi]
    obtain ⟨hl, hh⟩ := oblate_interlacing S c t r z hS (le_of_lt hi.1) hR hu
    rw [pairMaximum_of_interlacing S c t r z hl hh]
    exact add_le_add_left (interior_upper_bound S c t r z hi.1 hu) _
  · rw [exactEnvelope, if_neg hi]
    by_cases hD : difference S t ≤ 0
    · exact prolate_pair_bound S c t r z hS hD hc ht hr hR hz0 hz1
    · have hDpos : 0 < difference S t := by linarith
      have hbranch : difference S t ≤ c * t * r := by
        by_contra hn
        exact hi ⟨hDpos, by linarith⟩
      obtain ⟨hl, hh⟩ := oblate_interlacing S c t r z hS (le_of_lt hDpos) hR hu
      rw [pairMaximum_of_interlacing S c t r z hl hh]
      have hr1 : r ≤ 1 := by nlinarith
      exact add_le_add_left
        (oblate_boundary_upper_bound S c t r z hS (le_of_lt hDpos) hc ht hr hr1
          hz0 hz1 hbranch) _

/-- Every allowed axial shape and radius has a direction attaining the envelope. -/
theorem axial_pair_attainment (S c t r : ℝ) (hS : 0 ≤ S)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1) :
    ∃ z : ℝ, -r ≤ z ∧ z ≤ r ∧ pairMaximum S c t r z = exactEnvelope S c t r := by
  by_cases hi : 0 < difference S t ∧ c * t * r ≤ difference S t
  · obtain ⟨hz0, hz1⟩ := interior_direction_feasible S c t r hi.1 hc ht hr hi.2
    have hu : 0 ≤ r ^ 2 - interiorZ S c t r ^ 2 := by nlinarith
    obtain ⟨hl, hh⟩ := oblate_interlacing S c t r (interiorZ S c t r)
      hS (le_of_lt hi.1) hR hu
    refine ⟨interiorZ S c t r, by linarith, hz1, ?_⟩
    rw [exactEnvelope, if_pos hi,
      pairMaximum_of_interlacing S c t r (interiorZ S c t r) hl hh]
    have he := (interior_upper_eq_iff S c t r (interiorZ S c t r) hi.1 hu).mpr rfl
    rw [he]
  · refine ⟨r, by linarith, le_refl r, ?_⟩
    rw [exactEnvelope, if_neg hi]
    by_cases hD : difference S t ≤ 0
    · exact prolate_prescribed_radius_attainment S c t r hS hD hc ht hr hR
    · have hDpos : 0 < difference S t := by linarith
      have hbranch : difference S t ≤ c * t * r := by
        by_contra hn
        exact hi ⟨hDpos, by linarith⟩
      exact oblate_boundary_pair_attainment S c t r hS (le_of_lt hDpos)
        hc ht hr hR hbranch

/-- Complete fixed-radius axial spectral optimization, with no assumed bound. -/
theorem axial_exact_maximum (S c t r : ℝ) (hS : 0 ≤ S)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hr : 0 ≤ r) (hR : r ^ 2 ≤ 1) :
    (∀ z : ℝ, -r ≤ z → z ≤ r → pairMaximum S c t r z ≤ exactEnvelope S c t r) ∧
    (∃ z : ℝ, -r ≤ z ∧ z ≤ r ∧ pairMaximum S c t r z = exactEnvelope S c t r) := by
  constructor
  · intro z hz0 hz1
    exact axial_pair_bound S c t r z hS hc ht hr hR hz0 hz1
  · exact axial_pair_attainment S c t r hS hc ht hr hR

end
end AxialCertificates
