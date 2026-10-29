module
public import SquareCounting
public import LatticeCount

@[expose] public section

noncomputable section
namespace PowerRank

theorem square_difference_parity_iff (M q : ℕ) (hMq : M ≤ q ^ 2) :
    (q ^ 2 - M) % 2 = 1 ↔ q % 2 = 1 - M % 2 := by
  have hp := square_root_parity q
  have hMmod := Nat.mod_lt M (by decide : 0 < 2)
  have hqmod := Nat.mod_lt q (by decide : 0 < 2)
  omega

/-- The actual square count is one parity lattice in the strict square-root interval. -/
theorem paritySquareSet_mem_real (M q : ℕ) :
    q ∈ paritySquareSet M ↔
      Real.sqrt (M : ℝ) < q ∧ (q : ℝ) < Real.sqrt ((3 * M : ℕ) : ℝ) ∧
        q % 2 = 1 - M % 2 := by
  rw [paritySquareSet_mem_iff]
  constructor
  · rintro ⟨hlo, hhi, hpar⟩
    refine ⟨(Real.sqrt_lt (Nat.cast_nonneg M) (Nat.cast_nonneg q)).mpr (by exact_mod_cast hlo),
      ?_, (square_difference_parity_iff M q hlo.le).mp hpar⟩
    apply lt_of_not_ge
    intro hbad
    have hsq := (Real.sqrt_le_iff.mp hbad).2
    have hhiReal : (q : ℝ) ^ 2 < ((3 * M : ℕ) : ℝ) := by exact_mod_cast hhi
    linarith
  · rintro ⟨hlo, hhi, hpar⟩
    have hloNat : M < q ^ 2 := by
      exact_mod_cast (Real.sqrt_lt (Nat.cast_nonneg M) (Nat.cast_nonneg q)).mp hlo
    refine ⟨hloNat, ?_, (square_difference_parity_iff M q hloNat.le).mpr hpar⟩
    by_contra hbad
    have hsq : ((3 * M : ℕ) : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast (Nat.le_of_not_gt hbad)
    exact not_le_of_gt hhi (Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg q, hsq⟩)

theorem squareCorrection_lattice_error (M : ℕ) (hM : 1 ≤ M) :
    |(squareCorrection M : ℝ) -
      (Real.sqrt ((3 * M : ℕ) : ℝ) - Real.sqrt (M : ℝ)) / 2| ≤ 1 := by
  apply parity_lattice_count_error (paritySquareSet M)
    (Real.sqrt (M : ℝ)) (Real.sqrt ((3 * M : ℕ) : ℝ)) (1 - M % 2)
  · omega
  · apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact_mod_cast hM
  · apply Real.sqrt_lt_sqrt (Nat.cast_nonneg M)
    exact_mod_cast (show M < 3 * M by omega)
  · exact paritySquareSet_mem_real M

/-- Sharp square-root correction, with the manuscript's error constant two. -/
theorem squareCorrection_sqrt_error (M : ℕ) (hM : 1 ≤ M) :
    |2 * (squareCorrection M : ℝ) - (Real.sqrt 3 - 1) * Real.sqrt (M : ℝ)| ≤ 2 := by
  have h := squareCorrection_lattice_error M hM
  have hprod : Real.sqrt ((3 * M : ℕ) : ℝ) = Real.sqrt 3 * Real.sqrt (M : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) (M : ℝ)
  calc
    _ = |2 * ((squareCorrection M : ℝ) -
        (Real.sqrt ((3 * M : ℕ) : ℝ) - Real.sqrt (M : ℝ)) / 2)| := by
      congr 1
      rw [hprod]
      ring
    _ = 2 * |(squareCorrection M : ℝ) -
        (Real.sqrt ((3 * M : ℕ) : ℝ) - Real.sqrt (M : ℝ)) / 2| := by rw [abs_mul]; norm_num
    _ ≤ 2 := by linarith

def rankCubicValue (M : ℕ) : ℝ :=
  ((M : ℝ) + 1) * (2 * M + 1) * (7 * M + 6) / 6

theorem rankBaseline_real_eq_cubic (M : ℕ) : (rankBaseline M : ℝ) = rankCubicValue M := by
  have h := rankBaseline_six_mul M
  have hReal : (6 : ℝ) * rankBaseline M = ((M : ℝ) + 1) * (2 * M + 1) * (7 * M + 6) := by
    exact_mod_cast h
  unfold rankCubicValue
  linarith

theorem mainPower_cubic_sub_rank (M : ℕ) :
    rankCubicValue M - (recurrenceRank (mainPowerSequence M) : ℝ) = 2 * squareCorrection M := by
  have h := mainPower_rank_add_exceptional_pairs M
  rw [exceptionalPairCount_eq_two_squareCorrection] at h
  have hReal : (recurrenceRank (mainPowerSequence M) : ℝ) + 2 * squareCorrection M = rankBaseline M := by
    exact_mod_cast h
  rw [rankBaseline_real_eq_cubic] at hReal
  linarith

/-- The main quantitative assertion for every positive power, with exact ranks. -/
theorem mainPower_sqrt_error (M : ℕ) (hM : 1 ≤ M) :
    |rankCubicValue M - (recurrenceRank (mainPowerSequence M) : ℝ) -
      (Real.sqrt 3 - 1) * Real.sqrt (M : ℝ)| ≤ 2 := by
  rw [mainPower_cubic_sub_rank]
  exact squareCorrection_sqrt_error M hM

end PowerRank
