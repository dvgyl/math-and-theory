module
public import SquareEstimate
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

noncomputable section
namespace PowerRank

/-- Positive integers through n with the parity opposite to e. -/
def parityPrefix (n e : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter (fun q => q % 2 = 1 - e)

theorem parityPrefix_card (n e : ℕ) (he : e ≤ 1) :
    (parityPrefix n e).card = (n + 1 - e) / 2 := by
  classical
  induction n with
  | zero => simp [parityPrefix]; omega
  | succ n ih =>
    have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext q
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ parityPrefix n e := by simp [parityPrefix]
    unfold parityPrefix at ih hnot ⊢
    rw [hI, Finset.filter_insert]
    by_cases hpar : (n + 1) % 2 = 1 - e
    · rw [ite_eq_left hpar, Finset.card_insert_of_notMem hnot, ih]
      omega
    · rw [ite_eq_right hpar, ih]
      omega

theorem paritySquareSet_eq_prefix_sdiff (M : ℕ) (hM : 1 ≤ M) :
    paritySquareSet M = parityPrefix (Nat.sqrt (3 * M - 1)) (M % 2) \
      parityPrefix (Nat.sqrt M) (M % 2) := by
  classical
  ext q
  rw [paritySquareSet_mem_iff]
  simp only [Finset.mem_sdiff, parityPrefix, Finset.mem_filter, Finset.mem_Icc]
  have hroot : q ≤ Nat.sqrt (3 * M - 1) ↔ q ^ 2 ≤ 3 * M - 1 := Nat.le_sqrt'
  have hlower : Nat.sqrt M < q ↔ M < q ^ 2 := Nat.sqrt_lt'
  have hpar := square_difference_parity_iff M q
  constructor
  · rintro ⟨hlo, hhi, hp⟩
    have hqpos : 1 ≤ q := by nlinarith
    have he := hpar hlo.le
    exact ⟨⟨⟨hqpos, hroot.mpr (by omega)⟩, he.mp hp⟩,
      by intro hh; exact not_le_of_gt (hlower.mpr hlo) hh.1.2⟩
  · rintro ⟨⟨⟨hqpos, hqup⟩, hp⟩, hnlo⟩
    have hlo : Nat.sqrt M < q := by omega
    have hlo' := hlower.mp hlo
    exact ⟨hlo', by have := hroot.mp hqup; omega, (hpar hlo'.le).mpr hp⟩

/-- The exact floor formula, with both strict square endpoints. Natural sqrt
is floor(real sqrt), and the divisions below are natural floor divisions. -/
theorem squareCorrection_floor (M : ℕ) (hM : 1 ≤ M) :
    squareCorrection M =
      (Nat.sqrt (3 * M - 1) + 1 - M % 2) / 2 -
      (Nat.sqrt M + 1 - M % 2) / 2 := by
  classical
  rw [squareCorrection, paritySquareSet_eq_prefix_sdiff M hM,
    Finset.card_sdiff_of_subset]
  · rw [parityPrefix_card _ _ (by omega), parityPrefix_card _ _ (by omega)]
  · intro q hq
    simp only [parityPrefix, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans (Nat.sqrt_le_sqrt (by omega))⟩, hq.2⟩

end PowerRank
