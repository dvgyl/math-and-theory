import EvenShape
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace SquareFlowerCompletion.RealCompanion
open Set

theorem F_strictMono_left {n : ℕ} (hn : 4 ≤ n) :
    StrictMonoOn (F n) (Icc 1 (5/4)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_F n).continuousOn
  intro t ht
  rw [(hasDerivAt_F n t).deriv]
  have h := Fderiv_left hn (interior_subset ht)
  linarith

theorem F_strictAnti_right {n : ℕ} (hn : 4 ≤ n) :
    StrictAntiOn (F n) (Icc (3/2) 2) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_F n).continuousOn
  intro t ht
  rw [(hasDerivAt_F n t).deriv]
  exact Fderiv_right hn (interior_subset ht)

theorem F_left_zero {n : ℕ} (hn : 4 ≤ n) :
    ∃ t ∈ Ioo 1 (5/4), F n t = 0 := by
  have hp : 0 < F n (5/4) := F_middle_pos hn ⟨le_rfl, by norm_num⟩
  have hz : (0:ℝ) ∈ Icc (F n 1) (F n (5/4)) := by
    rw [F_one]
    exact ⟨by norm_num,hp.le⟩
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 5/4)
    (continuous_F n).continuousOn hz
  refine ⟨t,⟨?_,?_⟩,hzero⟩
  · by_contra h
    have he : t = 1 := by linarith [ht.1]
    rw [he,F_one] at hzero
    norm_num at hzero
  · by_contra h
    have he : t = 5/4 := by linarith [ht.2]
    rw [he] at hzero
    linarith

theorem F_right_zero {n : ℕ} (hn : 4 ≤ n) :
    ∃ t ∈ Ioo (3/2) 2, F n t = 0 := by
  have hp : 0 < F n (3/2) := F_middle_pos hn ⟨by norm_num,le_rfl⟩
  have hz : (0:ℝ) ∈ Icc (F n 2) (F n (3/2)) := by
    rw [F_two]
    exact ⟨by norm_num,hp.le⟩
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc' (by norm_num : (3/2:ℝ) ≤ 2)
    (continuous_F n).continuousOn hz
  refine ⟨t,⟨?_,?_⟩,hzero⟩
  · by_contra h
    have he : t = 3/2 := by linarith [ht.1]
    rw [he] at hzero
    linarith
  · by_contra h
    have he : t = 2 := by linarith [ht.2]
    rw [he,F_two] at hzero
    norm_num at hzero

theorem F_zero_classification {n : ℕ} (hn : 4 ≤ n) {l r : ℝ}
    (hl : l ∈ Ioo 1 (5/4)) (hr : r ∈ Ioo (3/2) 2)
    (hFl : F n l = 0) (hFr : F n r = 0) {t : ℝ}
    (ht : t ∈ Ioo 1 2) : F n t = 0 ↔ t = l ∨ t = r := by
  constructor
  · intro hzero
    by_cases hleft : t ≤ 5/4
    · left
      exact (F_strictMono_left hn).injOn ⟨ht.1.le,hleft⟩
        ⟨hl.1.le,hl.2.le⟩ (hzero.trans hFl.symm)
    · by_cases hright : 3/2 ≤ t
      · right
        exact (F_strictAnti_right hn).injOn ⟨hright,ht.2.le⟩
          ⟨hr.1.le,hr.2.le⟩ (hzero.trans hFr.symm)
      · have hp := F_middle_pos hn (t:=t) ⟨by linarith,by linarith⟩
        linarith
  · rintro (rfl | rfl) <;> assumption

theorem even_order_real_root_classification {n : ℕ} (he : Even n) (hn : 4 ≤ n) :
    ∃ l ∈ Ioo 1 (5/4), ∃ r ∈ Ioo (3/2) 2,
      F n l = 0 ∧ F n r = 0 ∧
      (∀ x : ℝ, (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0 ↔
        x = 0 ∨ x = -l ∨ x = -r) ∧
      0 < Fderiv n l ∧ Fderiv n r < 0 := by
  obtain ⟨l,hl,hFl⟩ := F_left_zero hn
  obtain ⟨r,hr,hFr⟩ := F_right_zero hn
  refine ⟨l,hl,r,hr,hFl,hFr,?_,?_,?_⟩
  · intro x
    constructor
    · intro hroot
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        obtain ⟨hx2,hx1⟩ := real_root_negative_interval hx hroot
        have hbr := (graph_root_iff_realBracket hx).mp hroot
        have hF : F n (-x) = 0 := by
          rw [F_eq_realBracket he,neg_neg]
          exact hbr
        have hc := (F_zero_classification hn hl hr hFl hFr
          (t:=-x) ⟨by linarith,by linarith⟩).mp hF
        rcases hc with hc | hc
        · left; linarith
        · right; linarith
    · rintro (rfl | rfl | rfl)
      · exact Extremal.graphPolynomial_eval_zero n
      · apply (graph_root_iff_realBracket (by linarith [hl.1] : -l ≠ 0)).mpr
        rw [← F_eq_realBracket he]
        exact hFl
      · apply (graph_root_iff_realBracket (by linarith [hr.1] : -r ≠ 0)).mpr
        rw [← F_eq_realBracket he]
        exact hFr
  · have h := Fderiv_left hn ⟨hl.1.le,hl.2.le⟩
    linarith
  · exact Fderiv_right hn ⟨hr.1.le,hr.2.le⟩

#print axioms F_strictMono_left
#print axioms F_strictAnti_right
#print axioms F_left_zero
#print axioms F_right_zero
#print axioms F_zero_classification
#print axioms even_order_real_root_classification
end SquareFlowerCompletion.RealCompanion
