module
public import RankTwoConsequences
public import OrderTwoPrototype
public import OrderThreeCertificates
public import OrderFourCertificates
public import OrderFiveCertificates
@[expose] public section
open scoped BigOperators
namespace MathAndTheory.Gyires.RankTwo
open Bernoulli Certificate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank_two_complete (hn : 2 ≤ Fintype.card ι) (hmax : Fintype.card ι ≤ 5)
    (A : Matrix ι ι ℝ) (hA : A ∈ doublyStochastic ℝ ι) (hrank : A.rank ≤ 2) :
    (A*A.transpose).permanent ≤ A.permanent ∧
    (A.transpose*A).permanent ≤ A.permanent ∧
    (A*A).permanent ≤ A.permanent ∧
    4*A.permanent*(A.permanent-dimensionConstant (Fintype.card ι)) ≤
      4*A.permanent^2-dimensionConstant (Fintype.card ι)*
        ((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ∧
    0 ≤ 4*A.permanent*(A.permanent-dimensionConstant (Fintype.card ι)) ∧
    dimensionConstant (Fintype.card ι)*(A*A.transpose).permanent ≤ A.permanent^2 ∧
    dimensionConstant (Fintype.card ι)*
      ((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ≤
        4*A.permanent^2 ∧
    (dimensionConstant (Fintype.card ι)*
      ((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) =
        4*A.permanent^2 ↔ A = uniformMatrix) := by
  have hc : allProfileChecks (Fintype.card ι) = true := by
    have hcard : Fintype.card ι = 2 ∨ Fintype.card ι = 3 ∨ Fintype.card ι = 4 ∨ Fintype.card ι = 5 := by omega
    rcases hcard with hcard | hcard | hcard | hcard
    · rw [hcard]
      exact order_two_all_profile_checks
    · rw [hcard]
      exact order_three_all_profile_checks
    · rw [hcard]
      exact order_four_all_profile_checks
    · rw [hcard]
      exact order_five_all_profile_checks
  obtain ⟨hl, hr, hs⟩ := rank_two_contractions_of_checks A hA hn hc hrank
  obtain ⟨hmargin, hnonneg⟩ := rank_two_margin_of_checks A hA hn hc hrank
  exact ⟨hl, hr, hs, hmargin, hnonneg,
    rank_two_strong_left_of_checks A hA hn hc hrank,
    rank_two_gyires_of_checks A hA hn hc hrank,
    rank_two_gyires_eq_iff_of_checks A hA hn hc hrank⟩

end MathAndTheory.Gyires.RankTwo
