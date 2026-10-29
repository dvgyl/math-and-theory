module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section
open scoped BigOperators

namespace THGStrong

def powerSum (t : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, t ^ (j + 1)
def geomSum (a : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (a⁻¹) ^ (j + 1)
def progressSum (h a : ℝ) (n : ℕ) : ℝ := h * geomSum a n
def invPower (r : ℝ) (n : ℕ) : ℝ := (r⁻¹) ^ n
def halfPower (r : ℝ) (n : ℕ) : ℝ := ((invPower r n) ^ 2 - 1) / 2
def forwardRatio (h a r : ℝ) (n : ℕ) : ℝ :=
  progressSum h a n / (invPower r n + 1)
def reverseRatio (h a r : ℝ) (n : ℕ) : ℝ :=
  progressSum h a n / (invPower r n - 1)

@[simp] lemma powerSum_zero (t : ℝ) : powerSum t 0 = 0 := by simp [powerSum]
@[simp] lemma geomSum_zero (a : ℝ) : geomSum a 0 = 0 := by simp [geomSum]
@[simp] lemma progressSum_zero (h a : ℝ) : progressSum h a 0 = 0 := by
  simp [progressSum]
@[simp] lemma invPower_zero (r : ℝ) : invPower r 0 = 1 := by simp [invPower]

lemma powerSum_succ (t : ℝ) (n : ℕ) :
    powerSum t (n+1) = powerSum t n + t^(n+1) := by
  simp [powerSum, Finset.sum_range_succ]

lemma geomSum_succ (a : ℝ) (n : ℕ) :
    geomSum a (n+1) = geomSum a n + (a⁻¹)^(n+1) := by
  exact powerSum_succ (a⁻¹) n

lemma powerSum_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ powerSum t n := by
  unfold powerSum
  positivity

lemma powerSum_pos {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    0 < powerSum t n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [powerSum_succ]
  exact add_pos_of_nonneg_of_pos (powerSum_nonneg (le_of_lt ht) k) (pow_pos ht _)

lemma powerSum_cross_nonneg {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (n : ℕ) :
    0 ≤ powerSum p n * q^(n+1) - p^(n+1) * powerSum q n := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := mul_nonneg (le_of_lt hq) ih
    have h2 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hpq)
      (pow_nonneg (le_of_lt hp) (n+1)))
      (powerSum_nonneg (le_of_lt hq) (n+1))
    rw [powerSum_succ] at h2
    simp only [powerSum_succ, pow_succ] at *
    nlinarith only [h1, h2]

lemma powerSum_cross_pos {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {n : ℕ} (hn : 0 < n) :
    0 < powerSum p n * q^(n+1) - p^(n+1) * powerSum q n := by
  have hq : 0 < q := lt_trans hp hpq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hi := powerSum_cross_nonneg hp (le_of_lt hpq) k
  have h1 := mul_nonneg (le_of_lt hq) hi
  have h2 := mul_pos (mul_pos (sub_pos.mpr hpq) (pow_pos hp (k+1)))
    (powerSum_pos hq (Nat.zero_lt_succ k))
  rw [powerSum_succ] at h2
  simp only [powerSum_succ, pow_succ] at *
  nlinarith only [h1, h2]

lemma geomSum_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 < geomSum a n := powerSum_pos (inv_pos.mpr ha) hn

lemma progressSum_pos {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    {n : ℕ} (hn : 0 < n) : 0 < progressSum h a n := by
  exact mul_pos hh (geomSum_pos ha hn)

lemma invPower_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < invPower r n := by
  exact pow_pos (inv_pos.mpr hr) n

lemma invPower_gt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {n : ℕ} (hn : 0 < n) : 1 < invPower r n := by
  have ht : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  exact one_lt_pow₀ ht (Nat.ne_of_gt hn)

lemma invPower_sub_one {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    invPower r n - 1 = (1-r) * geomSum r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geomSum_succ, mul_add, ← ih]
    simp only [invPower, pow_succ]
    have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    have hp := congrArg (fun t : ℝ => t * (r⁻¹)^n) hi
    nlinarith only [hp]


end THGStrong
