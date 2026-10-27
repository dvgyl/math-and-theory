module
public import RankTwoContraction
public import MathAndTheory.Mathematics.Gyires.PermanentCauchySchwarz
@[expose] public section
open scoped BigOperators
namespace MathAndTheory.Gyires.RankTwo
open Bernoulli Certificate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The checked profiles imply all three permanent contractions. -/
theorem rank_two_contractions_of_checks (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hn : 2 ≤ Fintype.card ι) (hcheck : allProfileChecks (Fintype.card ι) = true)
    (hrank : A.rank ≤ 2) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      (A.transpose * A).permanent ≤ A.permanent ∧ (A * A).permanent ≤ A.permanent := by
  have hl := (rank_two_gram_bounds_of_checks hn hcheck A hA hrank).1
  have hr := (rank_two_gram_bounds_of_checks hn hcheck A.transpose (transpose_mem_doublyStochastic_iff.mpr hA) (by simpa only [Matrix.rank_transpose] using hrank)).1
  simp only [Matrix.transpose_transpose, Matrix.permanent_transpose] at hr
  have hs := MathAndTheory.GyiresCirculant5.PermanentGram.permanent_square_bound_of_gram_bounds
    A 1 A.permanent (by norm_num) (by simpa only [one_mul] using hl) (by simpa only [one_mul] using hr)
  exact ⟨hl, hr, by simpa only [one_mul] using hs⟩

/-- The contraction bounds imply a nonnegative Gyires margin. -/
theorem rank_two_margin_of_checks (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hn : 2 ≤ Fintype.card ι) (hcheck : allProfileChecks (Fintype.card ι) = true)
    (hrank : A.rank ≤ 2) :
    4 * A.permanent * (A.permanent - dimensionConstant (Fintype.card ι)) ≤
      4 * A.permanent ^ 2 - dimensionConstant (Fintype.card ι) *
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ∧
    0 ≤ 4 * A.permanent * (A.permanent - dimensionConstant (Fintype.card ι)) := by
  obtain ⟨hl, hr, hs⟩ := rank_two_contractions_of_checks A hA hn hcheck hrank
  have hd := (rank_two_gram_bounds_of_checks hn hcheck A hA hrank).2.1
  have hc := dimensionConstant_nonneg (Fintype.card ι)
  have hsum : (A * A.transpose).permanent + (A.transpose * A).permanent +
      2 * (A * A).permanent ≤ 4 * A.permanent := by linarith
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hsum hc
    nlinarith [h]
  · exact mul_nonneg (mul_nonneg (by norm_num) (hc.trans hd)) (sub_nonneg.mpr hd)

/-- The checked profiles imply Gyires's inequality for rank at most two. -/
theorem rank_two_gyires_of_checks (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hn : 2 ≤ Fintype.card ι) (hcheck : allProfileChecks (Fintype.card ι) = true)
    (hrank : A.rank ≤ 2) :
    dimensionConstant (Fintype.card ι) *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
        4 * A.permanent ^ 2 := by
  have h := rank_two_margin_of_checks A hA hn hcheck hrank
  linarith [h.1, h.2]

/-- Equality in Gyires's inequality holds exactly at the uniform matrix. -/
theorem rank_two_gyires_eq_iff_of_checks (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι)
    (hn : 2 ≤ Fintype.card ι) (hcheck : allProfileChecks (Fintype.card ι) = true)
    (hrank : A.rank ≤ 2) :
    dimensionConstant (Fintype.card ι) *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
        4 * A.permanent ^ 2 ↔ A = uniformMatrix := by
  constructor
  · intro heq
    have hbounds := rank_two_gram_bounds_of_checks hn hcheck A hA hrank
    apply hbounds.2.2.mp
    have hmargin := (rank_two_margin_of_checks A hA hn hcheck hrank).1
    have hc := dimensionConstant_pos_all (Fintype.card ι)
    have hd : 0 < A.permanent := hc.trans_le hbounds.2.1
    by_contra hne
    have hstrict : dimensionConstant (Fintype.card ι) < A.permanent :=
      lt_of_le_of_ne hbounds.2.1 (Ne.symm hne)
    have hpositive : 0 < 4 * A.permanent * (A.permanent - dimensionConstant (Fintype.card ι)) := by
      exact mul_pos (mul_pos (by norm_num) hd) (sub_pos.mpr hstrict)
    linarith [hmargin]
  · intro heq
    rw [heq, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    ring

/-- The normalized left Gram bound follows from the contraction and the permanent lower bound. -/
theorem rank_two_strong_left_of_checks (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (hn : 2 ≤ Fintype.card ι)
    (hcheck : allProfileChecks (Fintype.card ι) = true) (hrank : A.rank ≤ 2) :
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent ≤ A.permanent^2 := by
  obtain ⟨hcontract, hlower, _⟩ := rank_two_gram_bounds_of_checks hn hcheck A hA hrank
  have hc := dimensionConstant_nonneg (Fintype.card ι)
  have hd : 0 ≤ A.permanent := hc.trans hlower
  have h1 := mul_le_mul_of_nonneg_left hcontract hc
  have h2 := mul_le_mul_of_nonneg_right hlower hd
  nlinarith

theorem rank_two_strong_left_eq_iff_of_checks (A : Matrix ι ι ℝ)
    (hA : A ∈ doublyStochastic ℝ ι) (hn : 2 ≤ Fintype.card ι)
    (hcheck : allProfileChecks (Fintype.card ι) = true) (hrank : A.rank ≤ 2) :
    dimensionConstant (Fintype.card ι) * (A*A.transpose).permanent = A.permanent^2 ↔
      A = uniformMatrix := by
  constructor
  · intro heq
    obtain ⟨hcontract, hlower, hequal⟩ := rank_two_gram_bounds_of_checks hn hcheck A hA hrank
    apply hequal.mp
    by_contra hne
    have hc := dimensionConstant_pos_all (Fintype.card ι)
    have hd : 0 < A.permanent := hc.trans_le hlower
    have hstrict : dimensionConstant (Fintype.card ι) < A.permanent :=
      lt_of_le_of_ne hlower (Ne.symm hne)
    have h1 := mul_le_mul_of_nonneg_left hcontract hc.le
    have h2 := mul_lt_mul_of_pos_right hstrict hd
    nlinarith
  · intro heq
    rw [heq, uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    ring

end MathAndTheory.Gyires.RankTwo
