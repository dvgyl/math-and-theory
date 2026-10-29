module
public import AsymmetricTutte.PublicDefs
import all AsymmetricTutte.Necessity.ThickUniform


section

namespace AsymmetricMerinoWelsh

open Finset Matroid Filter Topology
open Results.TutteThreshold

noncomputable section

theorem tutte_axis_nonnegative {α : Type*} (M : Matroid α) [M.Finite]
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ tutte M x 0 := by
  classical
  have H := (toRk M).Z_nonneg_alpha (x - 1) unitWeights (sub_nonneg.mpr hx)
    (by intro e he; norm_num [unitWeights])
  unfold unitWeights at H
  simpa only [AsymmetricTutte.public_tutte_eq_Z, zero_sub] using H

theorem tutte_other_axis_nonnegative {α : Type*} (M : Matroid α) [M.Finite]
    {y : ℝ} (hy : 1 ≤ y) : 0 ≤ tutte M 0 y := by
  classical
  have H := (toRk M).Z_nonneg_beta (y - 1) unitWeights (sub_nonneg.mpr hy)
    (by intro e he; norm_num [unitWeights])
  unfold unitWeights at H
  simpa only [AsymmetricTutte.public_tutte_eq_Z, zero_sub] using H

/-- A geometric progression bounded by a linear factor has base at most one. -/
theorem le_of_powers_le_linear {a s : ℝ} (hs : 0 < s)
    (h : ∀ n : ℕ, a ^ n ≤ ((n : ℝ) + 1) * s ^ n) : a ≤ s := by
  by_contra hnot
  have has : s < a := lt_of_not_ge hnot
  have hc : 1 < a / s := (one_lt_div hs).mpr has
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 1 hc
  simp only [pow_one] at hlim
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (a / s) ^ n < (1 / 4 : ℝ) :=
    (tendsto_order.mp hlim).2 _ (by norm_num)
  obtain ⟨n, hn, hnlt⟩ := ((eventually_ge_atTop (1 : ℕ)).and hev).exists
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < s ^ n := pow_pos hs n
  have hcp : 0 < (a / s) ^ n := pow_pos (by linarith) n
  have hratio : (a / s) ^ n ≤ (n : ℝ) + 1 := by
    rw [div_pow, div_le_iff₀ hsn]
    exact h n
  have hsmall := (div_lt_iff₀ hcp).mp hnlt
  nlinarith

/-- Universal validity bounds each term of a weighted binomial expansion. -/
theorem binomial_term_bound {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (hU : Universal x y) {k n r : ℕ} (hk : 2 ≤ k) (hr : 0 < r) (hrn : r ≤ n) :
    (n.choose r : ℝ) * ((k : ℝ) * Real.sqrt (y - 1)) ^ r *
        (Real.sqrt (x - 1)) ^ (n - r) ≤
      (Real.sqrt (x * y ^ k)) ^ n := by
  let P := thickUniform r n k
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hkpos : 0 < k := by omega
  have hA := thickUniform_axis_upper hr hrn hkpos hx
  have hB := thickUniform_other_axis_upper hrn hkpos hy
  have hbase := thickUniform_bases_lower hrn hkpos
  have hAd : IsAdmissible P := thickUniform_admissible hr hk
  have hprod := hU (Fin n × Fin k) P hAd
  have hAn : 0 ≤ tutte P x 0 := tutte_axis_nonnegative P hx.le
  have hBn : 0 ≤ tutte P 0 y := tutte_other_axis_nonnegative P hy.le
  have hbase0 : 0 ≤ (n.choose r : ℝ) * (k : ℝ) ^ r := by positivity
  have hbaseSq : ((n.choose r : ℝ) * (k : ℝ) ^ r) ^ 2 ≤ (tutte P 1 1) ^ 2 :=
    (sq_le_sq₀ hbase0 (hbase0.trans hbase)).mpr hbase
  have hX : 0 < x - 1 := sub_pos.mpr hx
  have hY : 0 < y - 1 := sub_pos.mpr hy
  have hweight : 0 ≤ (x - 1) ^ (n - r) * (y - 1) ^ r := by positivity
  have hmain : ((n.choose r : ℝ) * (k : ℝ) ^ r) ^ 2 *
      ((x - 1) ^ (n - r) * (y - 1) ^ r) ≤ x ^ n * y ^ (n * k) := by
    calc
      _ ≤ (tutte P x 0 * tutte P 0 y) *
          ((x - 1) ^ (n - r) * (y - 1) ^ r) :=
        mul_le_mul_of_nonneg_right (hbaseSq.trans hprod) hweight
      _ = (tutte P x 0 * (x - 1) ^ (n - r)) *
          (tutte P 0 y * (y - 1) ^ r) := by ring
      _ ≤ x ^ n * y ^ (n * k) :=
        mul_le_mul hA hB (mul_nonneg hBn (pow_nonneg hY.le r))
          (pow_nonneg (by linarith) n)
  have ha : (Real.sqrt (x - 1)) ^ 2 = x - 1 := Real.sq_sqrt hX.le
  have hb : (Real.sqrt (y - 1)) ^ 2 = y - 1 := Real.sq_sqrt hY.le
  have hs : (Real.sqrt (x * y ^ k)) ^ 2 = x * y ^ k :=
    Real.sq_sqrt (by positivity)
  have haN : (Real.sqrt (x - 1) ^ (n - r)) ^ 2 = (x - 1) ^ (n - r) := by
    calc
      _ = (Real.sqrt (x - 1) ^ 2) ^ (n - r) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = _ := by rw [ha]
  have hbR : (Real.sqrt (y - 1) ^ r) ^ 2 = (y - 1) ^ r := by
    calc
      _ = (Real.sqrt (y - 1) ^ 2) ^ r := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = _ := by rw [hb]
  apply le_of_sq_le_sq _ (by positivity)
  calc
    ((n.choose r : ℝ) * ((k : ℝ) * Real.sqrt (y - 1)) ^ r *
        Real.sqrt (x - 1) ^ (n - r)) ^ 2 =
      ((n.choose r : ℝ) * (k : ℝ) ^ r) ^ 2 *
        ((x - 1) ^ (n - r) * (y - 1) ^ r) := by
          simp only [mul_pow]
          rw [haN, hbR]
          ring
    _ ≤ x ^ n * y ^ (n * k) := hmain
    _ = (x * y ^ k) ^ n := by rw [mul_pow, ← pow_mul, Nat.mul_comm k n]
    _ = (Real.sqrt (x * y ^ k) ^ n) ^ 2 := by
      symm
      calc
        _ = (Real.sqrt (x * y ^ k) ^ 2) ^ n := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
        _ = _ := by rw [hs]

/-- Every parallel-thickening constraint is necessary. -/
theorem universal_curve {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (hU : Universal x y) {k : ℕ} (hk : 2 ≤ k) :
    (Real.sqrt (x - 1) + (k : ℝ) * Real.sqrt (y - 1)) ^ 2 ≤ x * y ^ k := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hs : 0 < Real.sqrt (x * y ^ k) := Real.sqrt_pos.mpr (by positivity)
  have ha : Real.sqrt (x - 1) ≤ Real.sqrt (x * y ^ k) := by
    apply Real.sqrt_le_sqrt
    have hkpow : 1 ≤ y ^ k := one_le_pow₀ hy.le
    nlinarith
  have H : Real.sqrt (x - 1) + (k : ℝ) * Real.sqrt (y - 1) ≤
      Real.sqrt (x * y ^ k) := by
    apply le_of_powers_le_linear hs
    intro n
    have hsum := add_pow ((k : ℝ) * Real.sqrt (y - 1)) (Real.sqrt (x - 1)) n
    rw [add_comm] at hsum
    rw [hsum]
    calc
      ∑ r ∈ range (n + 1), ((k : ℝ) * Real.sqrt (y - 1)) ^ r *
          Real.sqrt (x - 1) ^ (n - r) * (n.choose r : ℝ)
          ≤ ∑ _r ∈ range (n + 1), Real.sqrt (x * y ^ k) ^ n := by
            apply sum_le_sum
            intro r hr
            by_cases hr0 : r = 0
            · subst r
              simpa using pow_le_pow_left₀ (Real.sqrt_nonneg _) ha n
            · have H := binomial_term_bound hx hy hU hk (Nat.pos_of_ne_zero hr0)
                (Nat.le_of_lt_succ (mem_range.mp hr))
              nlinarith
      _ = ((n : ℝ) + 1) * Real.sqrt (x * y ^ k) ^ n := by simp
  have hnon : 0 ≤ Real.sqrt (x - 1) + (k : ℝ) * Real.sqrt (y - 1) := by positivity
  have Hsq := (sq_le_sq₀ hnon hs.le).mpr H
  rwa [Real.sq_sqrt (by positivity : 0 ≤ x * y ^ k)] at Hsq

end

end AsymmetricMerinoWelsh
