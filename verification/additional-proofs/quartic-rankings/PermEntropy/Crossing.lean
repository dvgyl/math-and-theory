import PermEntropy.Comparison
import PermEntropy.Cut
import PermEntropy.Membership
import PermEntropy.WordCrossing
import PermEntropy.BinaryEntropy

noncomputable section
open scoped BigOperators
namespace PermEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cutSum_eq_indicator (B : V → V → ℝ) (L R : Finset V) :
    cutSum B L R = ∑ u, ∑ v, if u ∈ L ∧ v ∈ R then B u v else 0 := by
  simp_rw [ite_and]
  simp [← Finset.sum_filter, cutSum]

namespace Ranking

theorem wordCrossing_membershipWord (r : Ranking V) (s : Finset V) :
    wordCrossing (r.membershipWord s) = cutSum (compareSign r) sᶜ s := by
  rw [wordCrossing_eq_pair_sum, cutSum_eq_indicator]
  calc
    _ = ∑ i : Fin (Fintype.card V), ∑ j : Fin (Fintype.card V),
        if r.enum i ∈ sᶜ ∧ r.enum j ∈ s then compareSign r (r.enum i) (r.enum j) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [membershipWord, compareSign]
    _ = ∑ u : V, ∑ v : V, if u ∈ sᶜ ∧ v ∈ s then compareSign r u v else 0 := by
      calc
        _ = ∑ i : Fin (Fintype.card V), ∑ v : V,
            if r.enum i ∈ sᶜ ∧ v ∈ s then compareSign r (r.enum i) v else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact r.sum_enum (fun v =>
            if r.enum i ∈ sᶜ ∧ v ∈ s then compareSign r (r.enum i) v else 0)
        _ = _ := r.sum_enum (fun u => ∑ v : V,
          if u ∈ sᶜ ∧ v ∈ s then compareSign r u v else 0)

end Ranking
namespace FinDist

theorem expect_wordCrossing_membershipWord (p : FinDist (Ranking V)) (s : Finset V) :
    p.expect (fun r => wordCrossing (r.membershipWord s)) = cutSum p.meanComparison sᶜ s := by
  simp_rw [Ranking.wordCrossing_membershipWord, cutSum]
  simp only [expect_sum, meanComparison]

theorem membershipWord_entropy_le_log_choose (p : FinDist (Ranking V)) (s : Finset V) :
    (p.map (fun r => r.membershipWord s)).entropy ≤
      Real.log ((Fintype.card V).choose s.card : ℝ) -
        (cutSum p.meanComparison sᶜ s)^2 / (2 * (Fintype.card V : ℝ)^3) := by
  have h := p.binaryWord_entropy_le_log_choose_map (fun r => r.membershipWord s)
    s.card (fun r => r.wordCount_membershipWord s)
  simpa only [p.expect_wordCrossing_membershipWord] using h

theorem membershipWord_entropy_le_log_choose_no_deficit (p : FinDist (Ranking V)) (s : Finset V) :
    (p.map (fun r => r.membershipWord s)).entropy ≤
      Real.log ((Fintype.card V).choose s.card : ℝ) := by
  have h := p.membershipWord_entropy_le_log_choose s
  have hnn : 0 ≤ (cutSum p.meanComparison sᶜ s)^2 / (2 * (Fintype.card V : ℝ)^3) := by positivity
  linarith

end FinDist
end PermEntropy
