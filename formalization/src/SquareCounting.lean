module
public import RankBaseline
public import SquareSolutions

@[expose] public section

noncomputable section
namespace PowerRank

def eligibleSquareLayers (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * M + 1)).filter
    (fun j => j % 2 = 1 ∧ ∃ q : ℕ, q ^ 2 = M + j)

def paritySquareSet (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3 * M + 1)).filter
    (fun q => M < q ^ 2 ∧ q ^ 2 < 3 * M ∧ (q ^ 2 - M) % 2 = 1)

def squareCorrection (M : ℕ) : ℕ := (paritySquareSet M).card

theorem eligibleSquareLayers_mem_iff (M j : ℕ) :
    j ∈ eligibleSquareLayers M ↔ j ≤ 2 * M ∧ j % 2 = 1 ∧ ∃ q : ℕ, q ^ 2 = M + j := by
  classical
  simp [eligibleSquareLayers]

theorem paritySquareSet_mem_iff (M q : ℕ) :
    q ∈ paritySquareSet M ↔ M < q ^ 2 ∧ q ^ 2 < 3 * M ∧ (q ^ 2 - M) % 2 = 1 := by
  classical
  simp only [paritySquareSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hqle := square_root_le_square q
    exact ⟨by omega, h⟩

theorem sqrt_square_of_exists (N : ℕ) (h : ∃ q : ℕ, q ^ 2 = N) :
    Nat.sqrt N ^ 2 = N := by
  obtain ⟨q, hq⟩ := h
  rw [← hq, Nat.sqrt_eq']

/-- Odd square layers are exactly the parity-restricted roots in the strict interval. -/
theorem eligibleSquareLayers_card (M : ℕ) :
    (eligibleSquareLayers M).card = squareCorrection M := by
  classical
  unfold squareCorrection
  apply Finset.card_nbij' (fun j => Nat.sqrt (M + j)) (fun q => q ^ 2 - M)
  · intro j hj
    change j ∈ eligibleSquareLayers M at hj
    have hj := (eligibleSquareLayers_mem_iff M j).mp hj
    have hjpos : 0 < j := by omega
    have hjupper : j < 2 * M := by omega
    have hs := sqrt_square_of_exists (M + j) hj.2.2
    apply (paritySquareSet_mem_iff M _).mpr
    rw [hs]
    exact ⟨by omega, by omega, by simpa using hj.2.1⟩
  · intro q hq
    have h := (paritySquareSet_mem_iff M q).mp hq
    change q ^ 2 - M ∈ eligibleSquareLayers M
    apply (eligibleSquareLayers_mem_iff M _).mpr
    refine ⟨by omega, h.2.2, q, ?_⟩
    omega
  · intro j hj
    change j ∈ eligibleSquareLayers M at hj
    have hj := (eligibleSquareLayers_mem_iff M j).mp hj
    change Nat.sqrt (M + j) ^ 2 - M = j
    rw [sqrt_square_of_exists (M + j) hj.2.2]
    omega
  · intro q hq
    have h := (paritySquareSet_mem_iff M q).mp hq
    change Nat.sqrt (M + (q ^ 2 - M)) = q
    rw [show M + (q ^ 2 - M) = q ^ 2 by omega, Nat.sqrt_eq']

/-- Each exceptional odd layer contributes precisely two deleted units. -/
theorem exceptionalPairCount_eq_two_squareCorrection (M : ℕ) :
    exceptionalPairCount M = 2 * squareCorrection M := by
  classical
  have hlayer (j : ℕ) (hj : j ∈ Finset.range (2 * M + 1)) :
      (∑ k ∈ Finset.range (M + j + 1),
        if j % 2 = 1 ∧ (((M + j : ℕ) : ℚ) - 2 * k) ^ 2 = (M + j : ℕ) then 1 else 0) =
      if j % 2 = 1 ∧ (∃ q : ℕ, q ^ 2 = M + j) then 2 else 0 := by
    by_cases hodd : j % 2 = 1
    · by_cases hsquare : ∃ q : ℕ, q ^ 2 = M + j
      · obtain ⟨q, hq⟩ := hsquare
        have hN : 2 ≤ M + j := by
          have hjle : j ≤ 2 * M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          omega
        have hsquare : ∃ q : ℕ, q ^ 2 = M + j := ⟨q, hq⟩
        simp only [hodd, true_and, ite_eq_left hsquare]
        exact square_solution_count (M + j) q hN hq
      · rw [ite_eq_right (by intro h; exact hsquare h.2)]
        apply Finset.sum_eq_zero
        intro k hk
        apply ite_eq_right
        intro h
        exact hsquare (rational_integer_square_nat_square _ k h.2)
    · simp [hodd]
  calc
    exceptionalPairCount M = ∑ j ∈ Finset.range (2 * M + 1),
        if j % 2 = 1 ∧ (∃ q : ℕ, q ^ 2 = M + j) then 2 else 0 := by
      apply Finset.sum_congr rfl
      exact hlayer
    _ = 2 * (∑ j ∈ Finset.range (2 * M + 1),
        if j % 2 = 1 ∧ (∃ q : ℕ, q ^ 2 = M + j) then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = 2 * (eligibleSquareLayers M).card := by rw [Finset.sum_boole]; rfl
    _ = 2 * squareCorrection M := by rw [eligibleSquareLayers_card]

/-- Exact cubic minus the stated parity-restricted square count, for every power. -/
theorem mainPower_rank_cubic_squareCorrection (M : ℕ) :
    recurrenceRank (mainPowerSequence M) =
      (M + 1) * (2 * M + 1) * (7 * M + 6) / 6 - 2 * squareCorrection M := by
  have h := mainPower_rank_add_exceptional_pairs M
  rw [exceptionalPairCount_eq_two_squareCorrection, rankBaseline_eq_cubic] at h
  omega

end PowerRank
