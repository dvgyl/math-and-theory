module
public import RangeComplete
@[expose] public section
open scoped BigOperators
open MathAndTheory.Gyires MathAndTheory.Gyires.RankTwo MathAndTheory.Gyires.RankTwo.Certificate
open MathAndTheory.Gyires.Bernoulli
namespace RankTwoScopedAudit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem all_range_conclusions (hn : 2 ≤ Fintype.card ι) (hmax : Fintype.card ι ≤ 6)
    (A : Matrix ι ι ℝ)
    (h0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (hcol : ∀ j, ∑ i, A i j = 1) (hrank : Matrix.rank A ≤ 2) :
    (A*A.transpose).permanent ≤ A.permanent ∧
    (A.transpose*A).permanent ≤ A.permanent ∧
    (A*A).permanent ≤ A.permanent ∧
    4*A.permanent*(A.permanent-(((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι)) ≤
      4*A.permanent^2-(((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι)*
        ((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ∧
    0 ≤ 4*A.permanent*(A.permanent-(((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι)) ∧
    (((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι)*(A*A.transpose).permanent ≤ A.permanent^2 ∧
    (((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι)*
      ((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ≤
        4*A.permanent^2 ∧
    ((((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι)*
      ((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) =
        4*A.permanent^2 ↔ A = (fun _ _ => 1/(Fintype.card ι : ℝ))) :=
  rank_two_complete hn hmax A (mem_doublyStochastic_iff_sum.mpr ⟨h0,hrow,hcol⟩) hrank

theorem explicit_order_6_gyires (A : Matrix (Fin 6) (Fin 6) ℝ)
    (h0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (hcol : ∀ j, ∑ i, A i j = 1) (hrank : Matrix.rank A ≤ 2) :
    (5/324 : ℝ)*((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) ≤
      4*A.permanent^2 ∧
    ((5/324 : ℝ)*((A*A.transpose).permanent+(A.transpose*A).permanent+2*(A*A).permanent) =
      4*A.permanent^2 ↔ A = (fun _ _ => (1/6 : ℝ))) := by
  have h := rank_two_complete (by decide) (by decide) A
    (mem_doublyStochastic_iff_sum.mpr ⟨h0,hrow,hcol⟩) hrank
  have hg := h.2.2.2.2.2.2
  norm_num [dimensionConstant,uniformMatrix] at hg
  exact hg

theorem all_sixth_pairs (a m c l : ℕ) (hm : 0 < m) (ham : a+m ≤ 6)
    (hl : 0 < l) (hcl : c+l ≤ 6) (hoverlap : max a c < min (a+m) (c+l)) :
    SparsePolynomial.coeffsNonneg (Hpoly 6 a m c l (max a c) (min (a+m) (c+l))) = true :=
  profile_check_of_all 6 a m c l hm ham hl hcl hoverlap order_six_all_profile_checks

/-- The five explicit order cases discharge the finite checks for the whole range. -/
theorem all_range_profile_checks {n : ℕ} (hn : 2 ≤ n) (hmax : n ≤ 6) :
    allProfileChecks n = true := by
  have hcard : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hcard with hcard | hcard | hcard | hcard | hcard
  · rw [hcard]
    exact order_two_all_profile_checks
  · rw [hcard]
    exact order_three_all_profile_checks
  · rw [hcard]
    exact order_four_all_profile_checks
  · rw [hcard]
    exact order_five_all_profile_checks
  · rw [hcard]
    exact order_six_all_profile_checks

/-- The manuscript's strong-left equality is an additional proved package theorem. -/
theorem strong_left_equality (hn : 2 ≤ Fintype.card ι) (hmax : Fintype.card ι ≤ 6)
    (A : Matrix ι ι ℝ)
    (h0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j = 1)
    (hcol : ∀ j, ∑ i, A i j = 1) (hrank : Matrix.rank A ≤ 2) :
    ((((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι) *
      (A*A.transpose).permanent = A.permanent^2 ↔
      A = (fun _ _ => 1/(Fintype.card ι : ℝ))) := by
  exact
    (rank_two_strong_left_eq_iff_of_checks A
      (mem_doublyStochastic_iff_sum.mpr ⟨h0,hrow,hcol⟩) hn
      (all_range_profile_checks hn hmax) hrank)
end RankTwoScopedAudit

#print axioms MathAndTheory.Gyires.RankTwo.rank_two_complete
#print axioms RankTwoScopedAudit.all_range_conclusions
#print axioms RankTwoScopedAudit.explicit_order_6_gyires
#print axioms RankTwoScopedAudit.all_sixth_pairs
#print axioms RankTwoScopedAudit.all_range_profile_checks
#print axioms RankTwoScopedAudit.strong_left_equality
