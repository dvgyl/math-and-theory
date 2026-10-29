module
public import AsymmetricTutte.Necessity.Curves
public import AsymmetricTutte.Necessity.Monotone
public import AsymmetricTutte.Basics


@[expose] public section

namespace AsymmetricMerinoWelsh

open Finset Matroid
open Results.TutteThreshold

noncomputable section

theorem Universal.swap {x y : ℝ} (hU : Universal x y) : Universal y x := by
  intro α M _ hM
  have H := hU α M✶ (AsymmetricTutte.admissible_dual M hM)
  simpa only [AsymmetricTutte.tutte_dual, mul_comm] using H

theorem Universal.left_gt_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hU : Universal x y) : 1 < x := by
  by_contra hnot
  have hx1 : x ≤ 1 := le_of_not_gt hnot
  obtain ⟨n, hn⟩ := exists_nat_gt (y + 2)
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) < n := by linarith
    exact_mod_cast this.le
  have hn0 : 0 < n := by omega
  let P := thickUniform 1 1 n
  have hAd : IsAdmissible P := thickUniform_admissible (by omega) hn2
  have hb : (n : ℝ) ≤ tutte P 1 1 := by
    simpa [P] using (thickUniform_bases_lower (r := 1) (n := 1) (k := n) (by omega) hn0)
  have hprod := hU (Fin 1 × Fin n) P✶ (AsymmetricTutte.admissible_dual P hAd)
  simp only [AsymmetricTutte.tutte_dual] at hprod
  have hsmall : tutte P 0 x ≤ tutte P 1 1 :=
    tutte_mono P (by norm_num) hx (by norm_num) hx1
  have hraise : tutte P y 0 ≤ tutte P (y + 2) 0 :=
    tutte_mono P hy (by norm_num) (by linarith) le_rfl
  have hbound : tutte P (y + 2) 0 ≤ y + 2 := by
    simpa [P] using (thickUniform_axis_upper (r := 1) (n := 1) (k := n)
      (by omega) (by omega) hn0 (x := y + 2) (by linarith))
  have hb0 : 0 ≤ tutte P 1 1 := tutte_nonneg P (by norm_num) (by norm_num)
  have hy0 : 0 ≤ tutte P y 0 := tutte_nonneg P hy (by norm_num)
  have hlast : tutte P 0 x * tutte P y 0 ≤ tutte P 1 1 * (y + 2) :=
    mul_le_mul hsmall (hraise.trans hbound) hy0 hb0
  have hsq := hprod.trans hlast
  nlinarith

theorem Universal.right_gt_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hU : Universal x y) : 1 < y :=
  hU.swap.left_gt_one hy hx

theorem necessary_conditions {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hU : Universal x y) :
    1 < x ∧ 1 < y ∧ ∀ k : ℕ, 2 ≤ k →
      (Real.sqrt (x - 1) + (k : ℝ) * Real.sqrt (y - 1)) ^ 2 ≤ x * y ^ k ∧
      (Real.sqrt (y - 1) + (k : ℝ) * Real.sqrt (x - 1)) ^ 2 ≤ y * x ^ k := by
  have hx1 := hU.left_gt_one hx hy
  have hy1 := hU.right_gt_one hx hy
  exact ⟨hx1, hy1, fun k hk => ⟨universal_curve hx1 hy1 hU hk,
    universal_curve hy1 hx1 hU.swap hk⟩⟩

end

end AsymmetricMerinoWelsh
