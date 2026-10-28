module
public import RangeEightComplete
@[expose] public section
open scoped BigOperators
open MathAndTheory.Gyires MathAndTheory.Gyires.RankTwo MathAndTheory.Gyires.Bernoulli
example (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 2)) (hrank : A.rank ≤ 2) :
    (A*A.transpose).permanent ≤ A.permanent ∧
    (A.transpose*A).permanent ≤ A.permanent ∧
    (A*A).permanent ≤ A.permanent := by
  obtain ⟨hl, hr, hs, _⟩ := rank_two_complete (by decide) (by decide) A hA hrank
  exact ⟨hl, hr, hs⟩
example (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 2)) (hrank : A.rank ≤ 2) :
    (1/2 : ℝ)*((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ≤
      4*A.permanent^2 := by
  obtain ⟨_, _, _, _, _, _, hg, _⟩ := rank_two_complete (by decide) (by decide) A hA hrank
  norm_num [dimensionConstant] at hg
  exact hg
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hmax : Fintype.card ι ≤ 6)
    (A : Matrix ι ι ℝ) (hA : A ∈ doublyStochastic ℝ ι) (hrank : Matrix.rank A ≤ 2) :
    (A*A.transpose).permanent ≤ A.permanent ∧
    (A.transpose*A).permanent ≤ A.permanent ∧
    (A*A).permanent ≤ A.permanent := by
  obtain ⟨hl, hr, hs, _⟩ := rank_two_complete hn hmax A hA hrank
  exact ⟨hl, hr, hs⟩
example (A : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 6)) (hrank : A.rank ≤ 2) :
    (5/324 : ℝ)*((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ≤
      4*A.permanent^2 ∧
    ((5/324 : ℝ)*((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) =
      4*A.permanent^2 ↔ A = uniformMatrix) := by
  obtain ⟨_, _, _, _, _, _, hg, heq⟩ := rank_two_complete (by decide) (by decide) A hA hrank
  norm_num [dimensionConstant] at hg heq
  exact ⟨hg, heq⟩
#print axioms MathAndTheory.Gyires.RankTwo.rank_two_complete_through_eight
