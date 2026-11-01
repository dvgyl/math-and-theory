import AdversarialCentralGap

/-!
Finite weighted probability: fourth moments and concentration force a small
second moment. The Cauchy--Schwarz step is proved from actual finite sums.
-/

open scoped BigOperators

set_option maxHeartbeats 2000000

namespace Breakthrough.AdversarialFiniteMoments

noncomputable section

def moment {ι : Type*} (s : Finset ι) (p z : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, p i * z i ^ k

def tailMass {ι : Type*} (s : Finset ι) (p z : ι → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ s, if x < |z i| then p i else 0

def tailSecond {ι : Type*} (s : Finset ι) (p z : ι → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ s, if x < |z i| then p i * z i ^ 2 else 0

lemma second_nonneg {ι : Type*} (s : Finset ι) (p z : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) : 0 ≤ moment s p z 2 := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hp i hi) (sq_nonneg _))

lemma tailMass_nonneg {ι : Type*} (s : Finset ι) (p z : ι → ℝ) (x : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) : 0 ≤ tailMass s p z x := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hp i hi
  · norm_num

lemma tailSecond_nonneg {ι : Type*} (s : Finset ι) (p z : ι → ℝ) (x : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) : 0 ≤ tailSecond s p z x := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact mul_nonneg (hp i hi) (sq_nonneg _)
  · norm_num

/-- Weighted Cauchy--Schwarz on the tail event, with the fourth moment on the
whole space. No square-root weights or conditional-probability convention are
needed. -/
theorem tailSecond_sq_le_fourth_mul_tail {ι : Type*} (s : Finset ι)
    (p z : ι → ℝ) (x : ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    tailSecond s p z x ^ 2 ≤ moment s p z 4 * tailMass s p z x := by
  classical
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
  · intro i hi
    exact mul_nonneg (hp i hi) (by positivity)
  · intro i hi
    split_ifs
    · exact hp i hi
    · norm_num
  · intro i hi
    split_ifs <;> ring

theorem second_le_threshold_add_tail {ι : Type*} (s : Finset ι)
    (p z : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hprob : ∑ i ∈ s, p i = 1) :
    moment s p z 2 ≤ x ^ 2 + tailSecond s p z x := by
  classical
  calc
    _ ≤ ∑ i ∈ s, (p i * x ^ 2 + if x < |z i| then p i * z i ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ht : x < |z i|
      · simp only [ht, if_true]
        nlinarith [mul_nonneg (hp i hi) (sq_nonneg x)]
      · simp only [ht, if_false, add_zero]
        apply mul_le_mul_of_nonneg_left _ (hp i hi)
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (z i)) hx).mpr (le_of_not_gt ht)
    _ = x ^ 2 + tailSecond s p z x := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hprob, one_mul]
      rfl

/-- The quantitative concentration-to-variance inequality, retaining the
sharp absorption factor obtained from a fourth-moment bound. -/
theorem second_absorption {ι : Type*} (s : Finset ι) (p z : ι → ℝ)
    {x C η : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hprob : ∑ i ∈ s, p i = 1)
    (hfourth : moment s p z 4 ≤ C * moment s p z 2 ^ 2)
    (htail : tailMass s p z x ≤ η) :
    (1 - Real.sqrt (C * η)) * moment s p z 2 ≤ x ^ 2 := by
  have hW := second_nonneg s p z hp
  have hT := tailSecond_nonneg s p z x hp
  have hP := tailMass_nonneg s p z x hp
  have hcs := tailSecond_sq_le_fourth_mul_tail s p z x hp
  have hsqrt := Real.sq_sqrt (mul_nonneg hC hη)
  have hbound : tailSecond s p z x ^ 2 ≤
      (Real.sqrt (C * η) * moment s p z 2) ^ 2 := by
    calc
      _ ≤ moment s p z 4 * tailMass s p z x := hcs
      _ ≤ (C * moment s p z 2 ^ 2) * η :=
        mul_le_mul hfourth htail hP (mul_nonneg hC (sq_nonneg _))
      _ = _ := by rw [mul_pow, hsqrt]; ring
  have ht : tailSecond s p z x ≤ Real.sqrt (C * η) * moment s p z 2 :=
    (sq_le_sq₀ hT (mul_nonneg (Real.sqrt_nonneg _) hW)).mp hbound
  have hm := second_le_threshold_add_tail s p z hx hp hprob
  nlinarith

/-- With `C η ≤ 1/4`, at least half of the second moment is absorbed. -/
theorem second_le_two_threshold_sq {ι : Type*} (s : Finset ι) (p z : ι → ℝ)
    {x C η : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hprob : ∑ i ∈ s, p i = 1)
    (hfourth : moment s p z 4 ≤ C * moment s p z 2 ^ 2)
    (htail : tailMass s p z x ≤ η) (hsmall : C * η ≤ 1 / 4) :
    moment s p z 2 ≤ 2 * x ^ 2 := by
  have h := second_absorption s p z hx hC hη hp hprob hfourth htail
  have hW := second_nonneg s p z hp
  have hsqrt : Real.sqrt (C * η) ≤ 1 / 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    rw [Real.sq_sqrt (mul_nonneg hC hη)]
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsqrt hW
  nlinarith

/-- Constants used by the balanced-slice inverse argument. -/
theorem second_le_two_threshold_sq_twelve {ι : Type*} (s : Finset ι)
    (p z : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hprob : ∑ i ∈ s, p i = 1)
    (hfourth : moment s p z 4 ≤ 12 * moment s p z 2 ^ 2)
    (htail : tailMass s p z x ≤ 1 / 48) :
    moment s p z 2 ≤ 2 * x ^ 2 := by
  exact second_le_two_threshold_sq s p z hx (by norm_num) (by norm_num)
    hp hprob hfourth htail (by norm_num)

#print axioms tailSecond_sq_le_fourth_mul_tail
#print axioms second_le_threshold_add_tail
#print axioms second_absorption
#print axioms second_le_two_threshold_sq
#print axioms second_le_two_threshold_sq_twelve

end
end Breakthrough.AdversarialFiniteMoments
