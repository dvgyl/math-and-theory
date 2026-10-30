import FiniteCycle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Periodic

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000

noncomputable section

namespace AsymptoticCP

open FiniteCP

abbrev E := Space 4
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

def period (N : ℕ) : ℕ := 4 * N + 3
instance (N : ℕ) : NeZero (period N) := ⟨by unfold period; omega⟩

def angle (N : ℕ) : ℝ := Real.pi / (2 * (period N : ℝ))
def mode1Angle (N : ℕ) : ℝ := Real.pi / 2 - 3 * angle N
def mode2Angle (N : ℕ) : ℝ := Real.pi / 2 + angle N
def spectralD1 (N : ℕ) : ℝ := 2 - 2 * Real.cos (mode1Angle N)
def spectralD2 (N : ℕ) : ℝ := 2 - 2 * Real.cos (mode2Angle N)
def weight1 (N : ℕ) (κ : ℝ) : ℝ := κ / (κ - spectralD1 N)
def weight2 (N : ℕ) (κ : ℝ) : ℝ := 3 * κ / (κ - spectralD2 N)
def sizeM (N : ℕ) (κ : ℝ) : ℝ :=
  spectralD1 N * weight1 N κ + spectralD2 N * weight2 N κ

/-- Two real rotation modes, represented explicitly in ordinary Euclidean R4. -/
def wave (a b φ ψ r : ℝ) : E :=
  !₂[a * Real.cos (r * φ), a * Real.sin (r * φ),
     b * Real.cos (r * ψ), b * Real.sin (r * ψ)]

def rawPrimal (N : ℕ) (κ r : ℝ) : E :=
  wave (Real.sqrt (weight1 N κ)) (Real.sqrt (weight2 N κ))
    (mode1Angle N) (mode2Angle N) r

def primalPoints (N : ℕ) (κ : ℝ) (i : Fin (period N)) : E := rawPrimal N κ i.val
def dualPoints (N : ℕ) (κ : ℝ) (i : Fin (period N)) : E :=
  primalPoints N κ i - primalPoints N κ (nextIndex i)

theorem inner_wave (a b c d φ ψ r s : ℝ) :
    ⟪wave a b φ ψ r, wave c d φ ψ s⟫ =
      a * c * Real.cos ((s - r) * φ) + b * d * Real.cos ((s - r) * ψ) := by
  norm_num [wave, PiLp.inner_apply, Fin.sum_univ_succ, Matrix.cons_val_succ,
    real_inner_eq_re_inner, RCLike.inner_apply, sub_mul, Real.cos_sub]
  ring

theorem wave_norm_sq (a b φ ψ r : ℝ) : ‖wave a b φ ψ r‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_wave]
  simp
  ring

theorem wave_sub_norm_sq (a b φ ψ r s : ℝ) :
    ‖wave a b φ ψ r - wave a b φ ψ s‖ ^ 2 =
      (2 - 2 * Real.cos ((s - r) * φ)) * a ^ 2 +
      (2 - 2 * Real.cos ((s - r) * ψ)) * b ^ 2 := by
  rw [norm_sub_sq_real, wave_norm_sq, wave_norm_sq, inner_wave]
  ring

theorem wave_recurrence (a b φ ψ r : ℝ) :
    wave a b φ ψ r + wave a b φ ψ (r + 2) =
      wave (2 * Real.cos φ * a) (2 * Real.cos ψ * b) φ ψ (r + 1) := by
  have hc (v : ℝ) : Real.cos (r * v) + Real.cos ((r + 2) * v) =
      2 * Real.cos v * Real.cos ((r + 1) * v) := by
    have h1 : r * v = (r + 1) * v - v := by ring
    have h2 : (r + 2) * v = (r + 1) * v + v := by ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hs (v : ℝ) : Real.sin (r * v) + Real.sin ((r + 2) * v) =
      2 * Real.cos v * Real.sin ((r + 1) * v) := by
    have h1 : r * v = (r + 1) * v - v := by ring
    have h2 : (r + 2) * v = (r + 1) * v + v := by ring
    rw [h1, h2, Real.sin_sub, Real.sin_add]
    ring
  ext j
  fin_cases j <;> norm_num [wave, Matrix.cons_val_succ]
  · linear_combination a * hc φ
  · linear_combination a * hs φ
  · linear_combination b * hc ψ
  · linear_combination b * hs ψ

theorem wave_raw_normal (a b φ ψ κ r : ℝ) :
    (wave a b φ ψ r - wave a b φ ψ (r + 1)) + κ • wave a b φ ψ (r + 1) -
      (wave a b φ ψ (r + 1) - wave a b φ ψ (r + 2)) =
    wave ((κ - (2 - 2 * Real.cos φ)) * a)
      ((κ - (2 - 2 * Real.cos ψ)) * b) φ ψ (r + 1) := by
  have h := wave_recurrence a b φ ψ r
  ext j
  have hj := congrArg (fun z : E => z j) h
  fin_cases j <;> norm_num [wave, Matrix.cons_val_succ] at hj ⊢ <;> nlinarith only [hj]

theorem period_mode1Angle (N : ℕ) :
    (period N : ℝ) * mode1Angle N = (N : ℝ) * (2 * Real.pi) := by
  have hK : (period N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (period N))
  unfold mode1Angle angle
  field_simp
  push_cast [period]
  ring

theorem period_mode2Angle (N : ℕ) :
    (period N : ℝ) * mode2Angle N = ((N + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
  have hK : (period N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (period N))
  unfold mode2Angle angle
  field_simp
  push_cast [period]
  ring

theorem rawPrimal_periodic (N : ℕ) (κ : ℝ) :
    Function.Periodic (fun i : ℕ => rawPrimal N κ i) (period N) := by
  intro i
  have hφ : ((i + period N : ℕ) : ℝ) * mode1Angle N =
      (i : ℝ) * mode1Angle N + (N : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [add_mul, period_mode1Angle]
  have hψ : ((i + period N : ℕ) : ℝ) * mode2Angle N =
      (i : ℝ) * mode2Angle N + ((N + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [add_mul, period_mode2Angle]
    push_cast
    rfl
  ext j
  fin_cases j <;> norm_num only [rawPrimal, wave, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, PiLp.add_apply] <;>
    simp only [hφ, hψ, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

theorem primalPoints_next (N : ℕ) (κ : ℝ) (i : Fin (period N)) :
    primalPoints N κ (nextIndex i) = rawPrimal N κ ((i.val : ℝ) + 1) := by
  simpa only [primalPoints, nextIndex, Nat.cast_add, Nat.cast_one] using
    (rawPrimal_periodic N κ).map_mod_nat (i.val + 1)

theorem dualPoints_raw (N : ℕ) (κ : ℝ) (i : Fin (period N)) :
    dualPoints N κ i = rawPrimal N κ i.val - rawPrimal N κ ((i.val : ℝ) + 1) := by
  rw [dualPoints, primalPoints_next]
  rfl

end AsymptoticCP
