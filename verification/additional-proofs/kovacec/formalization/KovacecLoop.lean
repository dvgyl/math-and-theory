import KovacecJordan
import KovacecBoundary

/-! The complete topological boundary is the range of a simple closed loop. -/
noncomputable section
namespace KovacecJordan
open Set Complex
set_option maxHeartbeats 6000000

private theorem q_on1 (t : ℝ) (ht : t ≤ 1) :
    q t = pt (6-4*t) (-2+3*t) := by simp [q, ht]
private theorem q_on2 (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    q t = pt (4-2*t) t := by
  unfold q q2 q3 q4 q5
  split_ifs <;> apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
private theorem q_on3 (t : ℝ) (ht2 : 2 ≤ t) (ht3 : t ≤ 3) :
    q t = pt (t-2) (6-2*t) := by
  unfold q q2 q3 q4 q5
  split_ifs <;> apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
private theorem q_on4 (t : ℝ) (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    q t = pt (4-t) (3-t) := by
  unfold q q2 q3 q4 q5
  split_ifs <;> apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
private theorem q_on5 (t : ℝ) (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    q t = pt (2*t-8) (3-t) := by
  unfold q q2 q3 q4 q5
  split_ifs <;> apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
private theorem q_on6 (t : ℝ) (ht5 : 5 ≤ t) (ht6 : t ≤ 6) :
    q t = pt (4*t-18) (-2) := by
  unfold q q2 q3 q4 q5
  split_ifs <;> apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith

theorem q_mem_J (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 6) : q t ∈ J := by
  rcases ht with ⟨ht0, ht6⟩
  unfold q q2 q3 q4 q5
  split_ifs
  all_goals
    simp only [J, C, Set.mem_setOf_eq, pt_re, pt_im]
    unfold L R
    split_ifs
    all_goals
      constructor
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
      · first
          | exact Or.inl True.intro
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | (left; linarith)
          | (right; left; linarith)
          | (right; right; left; linarith)
          | (right; right; right; linarith)

theorem J_subset_q_image : J ⊆ q '' Set.Icc (0 : ℝ) 6 := by
  intro z hz
  rcases hz with ⟨hC, hbd⟩
  rcases hC with ⟨hylo, hyhi, hxlo, hxhi⟩
  rcases hbd with hy | hy | hx | hx
  · have hxl : 2 ≤ z.re := by norm_num [hy, L] at hxlo; linarith
    have hxr : z.re ≤ 6 := by norm_num [hy, R] at hxhi; linarith
    refine ⟨(z.re + 18)/4, ⟨by linarith, by linarith⟩, ?_⟩
    rw [q_on6 _ (by linarith) (by linarith)]
    apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
  · have hxl : 0 ≤ z.re := by norm_num [hy, L] at hxlo; linarith
    have hxr : z.re ≤ 0 := by norm_num [hy, R] at hxhi; linarith
    refine ⟨2, by norm_num, ?_⟩
    rw [q_on2 _ (by norm_num) (by norm_num)]
    apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
  · by_cases h1 : z.im ≤ -1
    · simp only [L, if_pos h1] at hx
      refine ⟨3-z.im, ⟨by linarith, by linarith⟩, ?_⟩
      rw [q_on5 _ (by linarith) (by linarith)]
      apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
    · by_cases h0 : z.im ≤ 0
      · simp only [L, if_neg h1, if_pos h0] at hx
        refine ⟨3-z.im, ⟨by linarith, by linarith⟩, ?_⟩
        rw [q_on4 _ (by linarith) (by linarith)]
        apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
      · simp only [L, if_neg h1, if_neg h0] at hx
        refine ⟨(6-z.im)/2, ⟨by linarith, by linarith⟩, ?_⟩
        rw [q_on3 _ (by linarith) (by linarith)]
        apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
  · by_cases h1 : z.im ≤ 1
    · simp only [R, if_pos h1] at hx
      refine ⟨(z.im+2)/3, ⟨by linarith, by linarith⟩, ?_⟩
      rw [q_on1 _ (by linarith)]
      apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith
    · simp only [R, if_neg h1] at hx
      refine ⟨z.im, ⟨by linarith, by linarith⟩, ?_⟩
      rw [q_on2 _ (by linarith) hyhi]
      apply Complex.ext <;> simp only [pt_re, pt_im] <;> linarith

theorem q_image_Icc_eq_J : q '' Set.Icc (0 : ℝ) 6 = J := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact q_mem_J t ht
  · exact J_subset_q_image

/-- Standard interval-parametrization definition of a Jordan curve: the image
of a continuous closed loop with no repeated points except its two endpoints. -/
def IsJordanCurve (Γ : Set ℂ) : Prop :=
  ∃ f : ℝ → ℂ, ContinuousOn f (Set.Icc (0 : ℝ) 6) ∧ f 0 = f 6 ∧
    Set.InjOn f (Set.Ico (0 : ℝ) 6) ∧ f '' Set.Icc (0 : ℝ) 6 = Γ

theorem J_isJordanCurve : IsJordanCurve J := by
  exact ⟨q, q_continuous.continuousOn, q_zero_eq_six, q_injective_on_Ico,
    q_image_Icc_eq_J⟩

theorem frontier_C_isJordanCurve : IsJordanCurve (frontier C) := by
  rw [frontier_C_eq_J]
  exact J_isJordanCurve

#print axioms q_image_Icc_eq_J
#print axioms frontier_C_isJordanCurve
end KovacecJordan
