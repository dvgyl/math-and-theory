module
public import LayerDegrees
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

noncomputable section
namespace PowerRank

theorem square_root_parity (q : ℕ) : q ^ 2 % 2 = q % 2 := by
  have hlt : q % 2 < 2 := Nat.mod_lt q (by decide)
  have hcases : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [Nat.pow_mod, h]

theorem square_root_le_square (q : ℕ) : q ≤ q ^ 2 := by
  by_cases hq : q = 0
  · simp [hq]
  · have h1 : 1 ≤ q := by omega
    simpa [pow_two] using Nat.mul_le_mul_left q h1

/-- Exact two positions of a square exception, with both natural endpoints. -/
theorem rational_square_solutions_iff (N q k : ℕ) (hN : 2 ≤ N) (hq : q ^ 2 = N) :
    ((N : ℚ) - 2 * k) ^ 2 = N ↔ k = (N - q) / 2 ∨ k = (N + q) / 2 := by
  have hqpos : 0 < q := by nlinarith
  have hqle : q ≤ N := hq ▸ square_root_le_square q
  have hpar : N % 2 = q % 2 := by rw [← hq, square_root_parity]
  have hlo : 2 * ((N - q) / 2) = N - q := by omega
  have hhi : 2 * ((N + q) / 2) = N + q := by omega
  have hqcast : (q : ℚ) ^ 2 = (N : ℚ) := by exact_mod_cast hq
  constructor
  · intro hs
    have heq : ((N : ℚ) - 2 * k) ^ 2 = (q : ℚ) ^ 2 := hs.trans hqcast.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · have heqcast : ((2 * k : ℕ) : ℚ) = ((N - q : ℕ) : ℚ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hqle]
        linarith
      have heqnat : 2 * k = N - q := by exact_mod_cast heqcast
      left
      omega
    · have heqcast : ((2 * k : ℕ) : ℚ) = ((N + q : ℕ) : ℚ) := by
        push_cast
        linarith
      have heqnat : 2 * k = N + q := by exact_mod_cast heqcast
      right
      omega
  · rintro (rfl | rfl)
    · have h : (2 : ℚ) * ((N - q) / 2 : ℕ) = ((N - q : ℕ) : ℚ) := by exact_mod_cast hlo
      rw [Nat.cast_sub hqle] at h
      linear_combination hqcast - ((N : ℚ) - 2 * ((N - q) / 2 : ℕ) + q) * h
    · have h : (2 : ℚ) * ((N + q) / 2 : ℕ) = (N : ℚ) + q := by exact_mod_cast hhi
      linear_combination hqcast - ((N : ℚ) - 2 * ((N + q) / 2 : ℕ) - q) * h

theorem square_solution_positions_distinct (N q : ℕ) (hN : 2 ≤ N) (hq : q ^ 2 = N) :
    (N - q) / 2 ≠ (N + q) / 2 := by
  have hqpos : 0 < q := by nlinarith
  have hqle : q ≤ N := hq ▸ square_root_le_square q
  have hpar : N % 2 = q % 2 := by rw [← hq, square_root_parity]
  omega

/-- Every eligible square layer loses exactly two characteristic multiplicities. -/
theorem square_solution_count (N q : ℕ) (hN : 2 ≤ N) (hq : q ^ 2 = N) :
    (∑ k ∈ Finset.range (N + 1), if ((N : ℚ) - 2 * k) ^ 2 = N then 1 else 0 : ℕ) = 2 := by
  classical
  have hqle : q ≤ N := hq ▸ square_root_le_square q
  have hset : (Finset.range (N + 1)).filter (fun k : ℕ => ((N : ℚ) - 2 * k) ^ 2 = N) =
      {(N - q) / 2, (N + q) / 2} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    rw [rational_square_solutions_iff N q k hN hq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rcases h with rfl | rfl <;> omega
  rw [Finset.sum_boole, hset]
  simp [square_solution_positions_distinct N q hN hq]

end PowerRank
