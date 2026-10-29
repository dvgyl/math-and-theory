module
public import MainPowers

@[expose] public section

noncomputable section
namespace PowerRank

/-- Sum of all unreduced characteristic multiplicities. -/
def rankBaseline (M : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 * M + 1), (M + j + 1) * (j / 2 + 1)

def layerWeightSum (M : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 * M + 1), (j / 2 + 1)

def exceptionalPairCount (M : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 * M + 1), ∑ k ∈ Finset.range (M + j + 1),
    if j % 2 = 1 ∧ (((M + j : ℕ) : ℚ) - 2 * k) ^ 2 = (M + j : ℕ) then 1 else 0

theorem layerWeightSum_eq (M : ℕ) : layerWeightSum M = (M + 1) ^ 2 := by
  induction M with
  | zero => norm_num [layerWeightSum]
  | succ M ih =>
    unfold layerWeightSum at ih ⊢
    rw [show 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h0 : (2 * M + 1) / 2 = M := by omega
    have h1 : (2 * M + 1 + 1) / 2 = M + 1 := by omega
    rw [h0, h1]
    ring

theorem rankBaseline_succ (M : ℕ) :
    rankBaseline (M + 1) = rankBaseline M + (M + 1) ^ 2 +
      (3 * M + 3) * (M + 1) + (3 * M + 4) * (M + 2) := by
  unfold rankBaseline
  rw [show 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hcommon : (∑ j ∈ Finset.range (2 * M + 1), (M + 1 + j + 1) * (j / 2 + 1)) =
      (∑ j ∈ Finset.range (2 * M + 1), (M + j + 1) * (j / 2 + 1)) + layerWeightSum M := by
    unfold layerWeightSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcommon, layerWeightSum_eq]
  have h0 : (2 * M + 1) / 2 = M := by omega
  have h1 : (2 * M + 1 + 1) / 2 = M + 1 := by omega
  rw [h0, h1]
  ring

theorem rankBaseline_six_mul (M : ℕ) :
    6 * rankBaseline M = (M + 1) * (2 * M + 1) * (7 * M + 6) := by
  induction M with
  | zero => norm_num [rankBaseline]
  | succ M ih =>
    rw [rankBaseline_succ]
    calc
      _ = 6 * rankBaseline M + 6 * ((M + 1) ^ 2 +
        (3 * M + 3) * (M + 1) + (3 * M + 4) * (M + 2)) := by ring
      _ = _ := by rw [ih]; ring

theorem rankBaseline_eq_cubic (M : ℕ) :
    rankBaseline M = (M + 1) * (2 * M + 1) * (7 * M + 6) / 6 := by
  rw [← rankBaseline_six_mul]
  omega

/-- No loss is hidden by natural subtraction: add all exceptions back exactly. -/
theorem mainPower_rank_add_exceptional_pairs (M : ℕ) :
    recurrenceRank (mainPowerSequence M) + exceptionalPairCount M = rankBaseline M := by
  classical
  rw [mainPower_recurrenceRank_sum, exceptionalPairCount, rankBaseline,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ k ∈ Finset.range (M + j + 1), (j / 2 + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold expectedMultiplicity
      split_ifs <;> omega
    _ = _ := by simp

end PowerRank
