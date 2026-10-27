import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The logarithmic multiplicity potential

This file proves the scalar inequality used to merge the two children of a
read-k decision tree. Counts equal to zero are allowed; their influence must
then be zero. All logarithms in `logCount` are to base two.
-/

namespace ReadK

noncomputable def logCount (k : ℕ) : ℝ :=
  Real.log ((max 1 k : ℕ) : ℝ) / Real.log 2

@[simp] theorem logCount_zero : logCount 0 = 0 := by
  simp [logCount]

@[simp] theorem logCount_one : logCount 1 = 0 := by
  simp [logCount]

theorem logCount_nonneg (k : ℕ) : 0 ≤ logCount k := by
  have h : (1 : ℝ) ≤ ((max 1 k : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left 1 k)
  exact div_nonneg (Real.log_nonneg h) (le_of_lt (Real.log_pos (by norm_num)))

theorem logCount_mono : Monotone logCount := by
  intro a b hab
  have hpos : (0 : ℝ) < ((max 1 a : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((max 1 a : ℕ) : ℝ) := by
      exact_mod_cast (le_max_left 1 a)
    linarith
  have hab' : ((max 1 a : ℕ) : ℝ) ≤ ((max 1 b : ℕ) : ℝ) := by
    exact_mod_cast (max_le_max (le_refl 1) hab)
  exact div_le_div_of_nonneg_right (Real.log_le_log hpos hab')
    (le_of_lt (Real.log_pos (by norm_num)))

theorem logCount_of_pos {k : ℕ} (hk : 0 < k) :
    logCount k = Real.log (k : ℝ) / Real.log 2 := by
  have hk' : 1 ≤ k := hk
  simp [logCount, max_eq_right hk']

/-- AM-GM implies that the two logarithmic increments sum to at least two. -/
theorem logCount_merge_gap {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    2 ≤ 2 * logCount (a + b) - logCount a - logCount b := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hsq : 4 * (a : ℝ) * (b : ℝ) ≤ ((a : ℝ) + (b : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))]
  have hprod : (0 : ℝ) < 4 * (a : ℝ) * (b : ℝ) := by positivity
  have hlog := Real.log_le_log hprod hsq
  rw [Real.log_mul (mul_ne_zero (by norm_num) ha'.ne') hb'.ne',
    Real.log_mul (by norm_num) ha'.ne', Real.log_pow] at hlog
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (2 : ℝ) = (2 * Real.log 2) / Real.log 2 := by field_simp [htwo.ne']
    _ ≤ (2 * Real.log ((a : ℝ) + (b : ℝ)) - Real.log (a : ℝ) -
        Real.log (b : ℝ)) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ htwo.le
      linarith
    _ = 2 * logCount (a + b) - logCount a - logCount b := by
      rw [logCount_of_pos (Nat.add_pos_left ha b), logCount_of_pos ha,
        logCount_of_pos hb, Nat.cast_add]
      ring

/-- The scalar potential inequality that pays for an overlap covariance. -/
theorem logCount_potential (a b : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha0 : a = 0 → A = 0) (hb0 : b = 0 → B = 0) :
    min A B + (A * logCount a + B * logCount b) / 2 ≤
      ((A + B) / 2) * logCount (a + b) := by
  by_cases ha : a = 0
  · have hAzero : A = 0 := ha0 ha
    subst a
    subst A
    simp only [logCount_zero, zero_mul, zero_add, min_eq_left hB]
    ring_nf
    exact le_rfl
  by_cases hb : b = 0
  · have hBzero : B = 0 := hb0 hb
    subst b
    subst B
    simp only [logCount_zero, zero_mul, mul_zero, add_zero, min_eq_right hA]
    ring_nf
    exact le_rfl
  have hgap := logCount_merge_gap (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
  have hla : logCount a ≤ logCount (a + b) :=
    logCount_mono (Nat.le_add_right a b)
  have hlb : logCount b ≤ logCount (a + b) :=
    logCount_mono (Nat.le_add_left b a)
  have hda : 0 ≤ logCount (a + b) - logCount a := sub_nonneg.mpr hla
  have hdb : 0 ≤ logCount (a + b) - logCount b := sub_nonneg.mpr hlb
  have hm : 0 ≤ min A B := le_min hA hB
  have hleft := mul_le_mul_of_nonneg_right (min_le_left A B) hda
  have hright := mul_le_mul_of_nonneg_right (min_le_right A B) hdb
  have hsum := mul_le_mul_of_nonneg_left hgap hm
  nlinarith

end ReadK
