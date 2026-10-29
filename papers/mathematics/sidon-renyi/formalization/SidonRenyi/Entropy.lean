import SidonRenyi.Core
import SidonRenyi.SidonLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rényi entropy of the actual Sidon convolution

The entropy formula and comparison theorems in this file are used only at
orders different from one. Shannon entropy at order one is a separate limit.
-/

namespace SidonRenyi

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
/-- A normalized finite law has at least one positive coordinate. -/
theorem exists_pos_of_normalized (p : ι → ℝ) (hnorm : (∑ i, p i) = 1) :
    ∃ i, 0 < p i := by
  classical
  by_contra h
  push_neg at h
  have hh : (∑ i, p i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
  rw [hnorm] at hh
  norm_num at hh

/-- The moment is strictly positive, including on the boundary of the simplex. -/
theorem powerMoment_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hnorm : (∑ i, p i) = 1) (a : ℝ) : 0 < powerMoment a p := by
  classical
  unfold powerMoment
  rw [← pairWeight_powerMoment p hp a]
  obtain ⟨i, hi⟩ := exists_pos_of_normalized p hnorm
  apply Finset.sum_pos'
  · intro x hx
    exact Real.rpow_nonneg (pairWeight_nonneg p hp x) _
  · refine ⟨(i, i), by simp, ?_⟩
    exact Real.rpow_pos_of_pos (by simpa [pairWeight] using mul_pos hi hi) _

omit [LinearOrder ι] in
/-- Exact value of the moment at uniform input; written without division by a power. -/
theorem uniform_powerMoment (a : ℝ) :
    powerMoment a (fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      ((Fintype.card ι : ℝ) + (2 : ℝ) ^ (a - 1) *
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) *
        (1 / (Fintype.card ι : ℝ)) ^ (2 * a) := by
  unfold powerMoment
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hh : (1 / (Fintype.card ι : ℝ)) ^ (2 * a) =
      ((1 / (Fintype.card ι : ℝ)) ^ a) ^ 2 := by
    rw [mul_comm (2 : ℝ) a, Real.rpow_mul (by positivity), Real.rpow_two]
  rw [hh]
  ring

omit [LinearOrder ι] in
theorem uniform_weights_nonneg (_i : ι) : 0 ≤ 1 / (Fintype.card ι : ℝ) := by
  positivity

omit [LinearOrder ι] in
theorem uniform_weights_normalized [Nonempty ι] :
    (∑ _ : ι, 1 / (Fintype.card ι : ℝ)) = 1 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [hn]

section Convolution

variable {A : Type*} [AddCommSemigroup A] [DecidableEq A]

/-- Rényi entropy, using natural logarithms, of the sum of two iid finite draws.
The intended parameter range is `0 < a` and `a ≠ 1`. -/
noncomputable def renyiSumEntropy (a : ℝ) (p : ι → ℝ) (v : ι → A) : ℝ :=
  Real.log (∑ z ∈ sumSupport v, (iidConvolution p v z) ^ a) / (1 - a)

theorem iidConvolution_power_sum_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hnorm : (∑ i, p i) = 1) (v : ι → A) (hv : IsSidonMap v) (a : ℝ) :
    0 < ∑ z ∈ sumSupport v, (iidConvolution p v z) ^ a := by
  rw [iidConvolution_powerMoment p hp v hv a]
  exact powerMoment_pos p hp hnorm a

/-- The probability-law theorem connects entropy to the optimized moment. -/
theorem renyiSumEntropy_eq_log_powerMoment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (v : ι → A) (hv : IsSidonMap v) (a : ℝ) :
    renyiSumEntropy a p v = Real.log (powerMoment a p) / (1 - a) := by
  unfold renyiSumEntropy
  rw [iidConvolution_powerMoment p hp v hv a]
  rfl

/-- For orders above one, smaller power moment means larger Rényi entropy. -/
theorem entropy_le_of_powerMoment_le (a : ℝ) (ha : 1 < a)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp_norm : (∑ i, p i) = 1) (hq_norm : (∑ i, q i) = 1)
    (v : ι → A) (hv : IsSidonMap v)
    (h : powerMoment a p ≤ powerMoment a q) :
    renyiSumEntropy a q v ≤ renyiSumEntropy a p v := by
  rw [renyiSumEntropy_eq_log_powerMoment q hq v hv a,
    renyiSumEntropy_eq_log_powerMoment p hp v hv a]
  apply div_le_div_of_nonpos_of_le (by linarith : 1 - a ≤ 0)
  exact (Real.log_le_log_iff (powerMoment_pos p hp hp_norm a)
    (powerMoment_pos q hq hq_norm a)).2 h

/-- A strict moment improvement is a strict entropy improvement. -/
theorem entropy_lt_of_powerMoment_lt (a : ℝ) (ha : 1 < a)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp_norm : (∑ i, p i) = 1) (hq_norm : (∑ i, q i) = 1)
    (v : ι → A) (hv : IsSidonMap v)
    (h : powerMoment a p < powerMoment a q) :
    renyiSumEntropy a q v < renyiSumEntropy a p v := by
  rw [renyiSumEntropy_eq_log_powerMoment q hq v hv a,
    renyiSumEntropy_eq_log_powerMoment p hp v hv a]
  apply div_lt_div_of_neg_of_lt (by linarith : 1 - a < 0)
  exact (Real.log_lt_log_iff (powerMoment_pos p hp hp_norm a)
    (powerMoment_pos q hq hq_norm a)).2 h

/-- Below order one the power-moment order is preserved. -/
theorem entropy_le_of_powerMoment_le_below_one (a : ℝ) (ha : a < 1)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp_norm : (∑ i, p i) = 1) (hq_norm : (∑ i, q i) = 1)
    (v : ι → A) (hv : IsSidonMap v)
    (h : powerMoment a p ≤ powerMoment a q) :
    renyiSumEntropy a p v ≤ renyiSumEntropy a q v := by
  rw [renyiSumEntropy_eq_log_powerMoment q hq v hv a,
    renyiSumEntropy_eq_log_powerMoment p hp v hv a]
  exact div_le_div_of_nonneg_right
    ((Real.log_le_log_iff (powerMoment_pos p hp hp_norm a)
      (powerMoment_pos q hq hq_norm a)).2 h) (by linarith)

end Convolution

end SidonRenyi
