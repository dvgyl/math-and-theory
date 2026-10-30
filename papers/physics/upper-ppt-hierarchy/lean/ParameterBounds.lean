import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

noncomputable section
namespace UpperNoncollapse

/-- Number of fourfold error contractions used in the reverse construction. -/
def orbitPower (q : ℕ) : ℕ := 4 ^ q

/-- A power of two chosen to dominate the simultaneous concentration bound. -/
def orbitBase (q : ℕ) : ℝ := 2 ^ (2 * q + 4)

/-- The local dimension of the explicit physical instance. -/
def orbitDimension (q : ℕ) : ℝ := orbitBase q ^ orbitPower q

/-- Allowed coordinate error, indexed by the remaining depth. -/
def orbitError (q k : ℕ) : ℝ := 2 / orbitBase q ^ (4 ^ k)

lemma orbitPower_pos (q : ℕ) : 0 < orbitPower q := by
  unfold orbitPower
  positivity

lemma orbitPower_ge_one (q : ℕ) : 1 ≤ orbitPower q := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (orbitPower_pos q))

lemma le_orbitPower (q : ℕ) : q ≤ orbitPower q := by
  induction q with
  | zero => simp [orbitPower]
  | succ q ih =>
    simp only [orbitPower, pow_succ] at *
    have hp : 1 ≤ 4 ^ q := Nat.one_le_pow q 4 (by norm_num)
    omega

lemma orbitBase_eq (q : ℕ) : orbitBase q = 16 * (orbitPower q : ℝ) := by
  simp only [orbitBase, orbitPower, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add, pow_mul]
  norm_num
  ring

lemma orbitBase_ge (q : ℕ) : 16 ≤ orbitBase q := by
  rw [orbitBase_eq]
  have hp : (1 : ℝ) ≤ (orbitPower q : ℝ) := by exact_mod_cast orbitPower_ge_one q
  nlinarith

lemma orbitBase_pos (q : ℕ) : 0 < orbitBase q := lt_of_lt_of_le (by norm_num) (orbitBase_ge q)

lemma orbitBase_one_le (q : ℕ) : 1 ≤ orbitBase q := le_trans (by norm_num) (orbitBase_ge q)

lemma orbitDimension_pos (q : ℕ) : 0 < orbitDimension q := by
  unfold orbitDimension
  exact pow_pos (orbitBase_pos q) _

lemma orbitDimension_eq (q : ℕ) :
    orbitDimension q = 2 ^ ((2 * q + 4) * 4 ^ q) := by
  simp [orbitDimension, orbitBase, orbitPower, pow_mul]

lemma orbitError_pos (q k : ℕ) : 0 < orbitError q k := by
  unfold orbitError
  exact div_pos (by norm_num) (pow_pos (orbitBase_pos q) _)

lemma orbitError_le_eighth (q k : ℕ) : orbitError q k ≤ 1 / 8 := by
  have hp : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by norm_num)
  have hpow : orbitBase q ≤ orbitBase q ^ (4 ^ k) := by
    calc
      orbitBase q = orbitBase q ^ 1 := by ring
      _ ≤ orbitBase q ^ (4 ^ k) := pow_le_pow_right₀ (orbitBase_one_le q) hp
  rw [orbitError, div_le_iff₀ (pow_pos (orbitBase_pos q) _)]
  nlinarith [orbitBase_ge q]

lemma orbitError_initial (q : ℕ) : orbitError q q = 2 / orbitDimension q := rfl

lemma orbitError_step_small (q k : ℕ) :
    orbitError q (k + 1) ≤ 1 / orbitBase q ^ (4 ^ k) := by
  have hb := orbitBase_ge q
  have hp : 0 < orbitBase q ^ (4 ^ k) := pow_pos (orbitBase_pos q) _
  have hl : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by norm_num)
  have hpow : 16 ≤ orbitBase q ^ (4 ^ k) := by
    calc
      16 ≤ orbitBase q := hb
      _ = orbitBase q ^ 1 := by ring
      _ ≤ orbitBase q ^ (4 ^ k) := pow_le_pow_right₀ (orbitBase_one_le q) hl
  rw [orbitError, pow_succ, pow_mul]
  rw [div_le_div_iff₀ (pow_pos hp 4) hp]
  have h3 : (2 : ℝ) ≤ (orbitBase q ^ (4 ^ k)) ^ 3 := by
    calc
      2 ≤ (16 : ℝ) ^ 3 := by norm_num
      _ ≤ (orbitBase q ^ (4 ^ k)) ^ 3 := pow_le_pow_left₀ (by norm_num) hpow 3
  nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]

lemma orbitError_step_add (q k : ℕ) :
    orbitError q (k + 1) + 1 / orbitBase q ^ (4 ^ k) ≤ orbitError q k := by
  have hs := orbitError_step_small q k
  calc
    orbitError q (k + 1) + 1 / orbitBase q ^ (4 ^ k) ≤
        1 / orbitBase q ^ (4 ^ k) + 1 / orbitBase q ^ (4 ^ k) := add_le_add_right hs _
    _ = orbitError q k := by unfold orbitError; ring


/-- Radius used by one inverse step with this remaining-depth index. -/
def orbitRadius (q k : ℕ) : ℝ := 1 / orbitBase q ^ (4 ^ k)

/-- Exponential tilt for the finite potential argument. -/
def orbitTilt (q k : ℕ) : ℝ := (orbitBase q ^ (4 ^ k)) ^ 3 / 8

lemma orbitRadius_pos (q k : ℕ) : 0 < orbitRadius q k := by
  unfold orbitRadius
  have hb := orbitBase_pos q
  positivity

lemma orbitTilt_pos (q k : ℕ) : 0 < orbitTilt q k := by
  unfold orbitTilt
  have hb := orbitBase_pos q
  positivity

lemma orbitTilt_bound (q k : ℕ) (hk : k < q) :
    2 * orbitTilt q k / orbitDimension q ≤ 1 := by
  have he : 4 ^ (k + 1) ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have he' : (4 ^ k) * 3 ≤ orbitPower q := by
    unfold orbitPower
    rw [pow_succ] at he
    omega
  have hp : (orbitBase q ^ (4 ^ k)) ^ 3 ≤ orbitDimension q := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (orbitBase_one_le q) he'
  rw [div_le_iff₀ (orbitDimension_pos q)]
  unfold orbitTilt
  nlinarith [orbitDimension_pos q]

lemma orbit_exponent_id (q k : ℕ) :
    2 * orbitError q (k + 1) * orbitTilt q k ^ 2 =
      (orbitBase q ^ (4 ^ k)) ^ 2 / 16 := by
  have hn : orbitBase q ^ (4 ^ k) ≠ 0 := ne_of_gt (pow_pos (orbitBase_pos q) _)
  unfold orbitError orbitTilt
  rw [pow_succ, pow_mul]
  field_simp
  ring

lemma orbit_target_id (q k : ℕ) :
    orbitTilt q k * orbitRadius q k = (orbitBase q ^ (4 ^ k)) ^ 2 / 8 := by
  have hn : orbitBase q ^ (4 ^ k) ≠ 0 := ne_of_gt (pow_pos (orbitBase_pos q) _)
  unfold orbitTilt orbitRadius
  field_simp
  ring

lemma log_orbitDimension (q : ℕ) :
    Real.log (orbitDimension q) =
      ((2 * q + 4 : ℕ) : ℝ) * (orbitPower q : ℝ) * Real.log 2 := by
  rw [orbitDimension, Real.log_pow, orbitBase, Real.log_pow]
  ring

lemma orbit_count_bound (q k : ℕ) :
    2 * orbitDimension q ^ 2 < Real.exp ((orbitBase q ^ (4 ^ k)) ^ 2 / 16) := by
  have hd := orbitDimension_pos q
  have hh := orbitBase_pos q
  have hp : (1 : ℝ) ≤ (orbitPower q : ℝ) := by exact_mod_cast orbitPower_ge_one q
  have hq : (q : ℝ) ≤ (orbitPower q : ℝ) := by exact_mod_cast le_orbitPower q
  have hqp : (4 : ℝ) * (orbitPower q : ℝ) * q ≤
      4 * (orbitPower q : ℝ)^2 := by nlinarith
  have hpp : (orbitPower q : ℝ) ≤ (orbitPower q : ℝ)^2 := by nlinarith
  have hcoef : 1 + 4 * (orbitPower q : ℝ) * q + 8 * (orbitPower q : ℝ) ≤
      13 * (orbitPower q : ℝ)^2 := by nlinarith
  have hlog : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have hl : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by norm_num)
  have hx : orbitBase q ≤ orbitBase q ^ (4 ^ k) := by
    calc
      orbitBase q = orbitBase q ^ 1 := by ring
      _ ≤ orbitBase q ^ (4 ^ k) := pow_le_pow_right₀ (orbitBase_one_le q) hl
  have hx' : 16 * (orbitPower q : ℝ)^2 ≤ (orbitBase q ^ (4 ^ k))^2 / 16 := by
    have hx0 : 16 * (orbitPower q : ℝ) ≤ orbitBase q ^ (4 ^ k) := by
      calc
        16 * (orbitPower q : ℝ) = orbitBase q := (orbitBase_eq q).symm
        _ ≤ orbitBase q ^ (4 ^ k) := hx
    nlinarith [sq_nonneg (orbitBase q ^ (4 ^ k) - 16 * (orbitPower q : ℝ))]
  have hid : Real.log (2 * orbitDimension q ^ 2) =
      (1 + 4 * (orbitPower q : ℝ) * q + 8 * (orbitPower q : ℝ)) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt hd)), Real.log_pow,
      log_orbitDimension]
    push_cast
    ring
  apply (Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 2 * orbitDimension q ^ 2)).mp
  rw [hid]
  have hcpos : 0 < 1 + 4 * (orbitPower q : ℝ) * q + 8 * (orbitPower q : ℝ) := by positivity
  have hmul := mul_lt_mul_of_pos_left hlog hcpos
  nlinarith

lemma orbit_mass_bound (q k : ℕ) :
    2 * orbitDimension q ^ 2 * Real.exp (2 * orbitError q (k + 1) * orbitTilt q k ^ 2) <
      Real.exp (orbitTilt q k * orbitRadius q k) := by
  rw [orbit_exponent_id, orbit_target_id]
  have hcount := orbit_count_bound q k
  have hm := mul_lt_mul_of_pos_right hcount
    (Real.exp_pos ((orbitBase q ^ (4 ^ k)) ^ 2 / 16))
  rw [← Real.exp_add] at hm
  convert hm using 1
  congr 1
  ring

end UpperNoncollapse
