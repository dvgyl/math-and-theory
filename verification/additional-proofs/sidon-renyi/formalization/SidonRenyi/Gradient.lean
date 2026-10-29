import SidonRenyi.Core
import SidonRenyi.PowerDifference

/-! Ordering of the moment gradient up to the exact scalar threshold. -/

open scoped BigOperators
open Finset Real

namespace SidonRenyi

/-- The moment gradient is strictly ordered by the coordinates, including at the threshold. -/
theorem momentGradient_lt {ι : Type*} [Fintype ι] {a : ℝ} {p : ι → ℝ} {i j : ι}
    (ha : 1 < a) (hcrit : (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1)
    (hp : ∀ k, 0 < p k) (hij : p i < p j) :
    momentGradient a p i < momentGradient a p j := by
  classical
  have hne : i ≠ j := by
    intro heq
    subst j
    exact (lt_irrefl _ hij)
  have hsum : (p i) ^ a + (p j) ^ a ≤ ∑ k, (p k) ^ a := by
    have hh := Finset.sum_le_univ_sum_of_nonneg
      (s := ({i, j} : Finset ι)) (fun k => Real.rpow_nonneg (hp k).le a)
    simpa [hne] using hh
  have hd : 0 ≤ (p j) ^ (a - 1) - (p i) ^ (a - 1) := by
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow (hp i).le hij.le (by linarith)
  have hc : 0 ≤ (2 : ℝ) ^ (a - 1) := Real.rpow_nonneg (by norm_num) _
  have hlarge :
      (2 : ℝ) ^ (a - 1) *
          (((p j) ^ a + (p i) ^ a) * ((p j) ^ (a - 1) - (p i) ^ (a - 1))) ≤
        (2 : ℝ) ^ (a - 1) * (∑ k, (p k) ^ a) *
          ((p j) ^ (a - 1) - (p i) ^ (a - 1)) := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hd
    apply mul_le_mul_of_nonneg_left _ hc
    linarith
  have hcross := power_cross_identity (a := a) (hp j) (hp i)
  have hbridge :
      (2 : ℝ) ^ (a - 1) *
          (((p j) ^ a + (p i) ^ a) * ((p j) ^ (a - 1) - (p i) ^ (a - 1))) -
        ((2 : ℝ) ^ (a - 1) - 1) * ((p j) ^ (2 * a - 1) - (p i) ^ (2 * a - 1)) =
      ((p j) ^ (2 * a - 1) - (p i) ^ (2 * a - 1)) -
        (2 : ℝ) ^ (a - 1) * (p j * p i) ^ (a - 1) * (p j - p i) := by
    rw [hcross]
    ring
  have hscalar := power_difference_lt ha (hp i) hij
  have hcrit_scaled :
      (2 : ℝ) ^ (a - 1) * (p j * p i) ^ (a - 1) * (p j - p i) ≤
        (2 * a - 1) * (p j * p i) ^ (a - 1) * (p j - p i) := by
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hij.le)
    exact mul_le_mul_of_nonneg_right hcrit
      (Real.rpow_nonneg (mul_nonneg (hp j).le (hp i).le) _)
  have hbase : 0 <
      (2 : ℝ) ^ (a - 1) *
          (((p j) ^ a + (p i) ^ a) * ((p j) ^ (a - 1) - (p i) ^ (a - 1))) -
        ((2 : ℝ) ^ (a - 1) - 1) *
          ((p j) ^ (2 * a - 1) - (p i) ^ (2 * a - 1)) := by
    rw [hbridge]
    linarith
  have htotal : 0 <
      (2 : ℝ) ^ (a - 1) * (∑ k, (p k) ^ a) *
          ((p j) ^ (a - 1) - (p i) ^ (a - 1)) -
        ((2 : ℝ) ^ (a - 1) - 1) *
          ((p j) ^ (2 * a - 1) - (p i) ^ (2 * a - 1)) := by
    linarith
  have hgrad : momentGradient a p j - momentGradient a p i =
      2 * a * ((2 : ℝ) ^ (a - 1) * (∑ k, (p k) ^ a) *
          ((p j) ^ (a - 1) - (p i) ^ (a - 1)) -
        ((2 : ℝ) ^ (a - 1) - 1) *
          ((p j) ^ (2 * a - 1) - (p i) ^ (2 * a - 1))) := by
    unfold momentGradient
    rw [rpow_twice_sub_one (hp i), rpow_twice_sub_one (hp j)]
    ring
  have hh : 0 < momentGradient a p j - momentGradient a p i := by
    rw [hgrad]
    exact mul_pos (by linarith) htotal
  linarith

/-- Coordinate monotonicity of the moment gradient throughout the admissible order range. -/
theorem momentGradient_mono {ι : Type*} [Fintype ι] {a : ℝ} {p : ι → ℝ} {i j : ι}
    (ha : 1 < a) (hcrit : (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1)
    (hp : ∀ k, 0 < p k) (hij : p i ≤ p j) :
    momentGradient a p i ≤ momentGradient a p j := by
  obtain hlt | heq := lt_or_eq_of_le hij
  · exact (momentGradient_lt ha hcrit hp hlt).le
  · simp only [momentGradient, heq, le_refl]

end SidonRenyi
