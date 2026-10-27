import DominationULC.ConditionalSequences
import DominationULC.Euler
import Mathlib.Tactic.Positivity

namespace DominationULC

/-- The coefficient inequality for positive bounded cyclic gaps. The pointing
identity converts this exactly to ultra log-concavity of cycle domination. -/
theorem cycle_coeff_ulc (m : ℕ) (N : ℤ) (j : ℕ) :
    ((j : ℝ) + 2) * ((N : ℝ) - ((j : ℝ) + 1)) *
        (part m ^ (j + 1)) N * (part m ^ (j + 3)) N ≤
      ((j : ℝ) + 1) * ((N : ℝ) - ((j : ℝ) + 2)) *
        ((part m ^ (j + 2)) N) ^ 2 := by
  let P : Seq := part m
  have hcut : cutoff (P^2) (m : ℤ) = tpart m := by
    change (P^2 : Seq).filter (fun z => z ≤ (m : ℤ)) = tpart m
    simpa only [P, pow_two] using cut_part_mul m m le_rfl
  have hc := conditional_coefficient_mono (P^2) (P^j)
    (nonnegative_pow (part_nonnegative m) 2)
    (tp2_pow (part_tp2 m) j) m N (m : ℤ)
  rw [hcut] at hc
  have hp₁ : P^2 * (P^j * part m) = P^(j+3) := by
    simp only [P, pow_add]
    ring
  have hp₂ : P^2 * P^j = P^(j+2) := by
    rw [pow_add]
    ring
  have hp₃ : tpart m * (P^j * part m) = tpart m * P^(j+1) := by
    simp only [pow_succ, P]
  rw [hp₁, hp₂, hp₃] at hc
  have he₁ := euler_power_excess P j N
  have he₂ := euler_power_excess P (j+1) N
  change ((N : ℝ) - (j+1 : ℕ)) * (P^(j+1)) N =
    (j+1 : ℕ) * (tpart m * P^j) N at he₁
  change ((N : ℝ) - (j+1+1 : ℕ)) * (P^(j+1+1)) N =
    (j+1+1 : ℕ) * (tpart m * P^(j+1)) N at he₂
  push_cast at he₁ he₂
  have hfactor : 0 ≤ ((j : ℝ)+1) * ((j : ℝ)+2) := by positivity
  calc
    _ = ((j : ℝ)+2) * (((N : ℝ)-((j : ℝ)+1)) * (P^(j+1)) N) *
        (P^(j+3)) N := by dsimp [P]; ring
    _ = ((j : ℝ)+2) * (((j : ℝ)+1) * (tpart m * P^j) N) *
        (P^(j+3)) N := by rw [he₁]
    _ = (((j : ℝ)+1) * ((j : ℝ)+2)) *
        ((tpart m * P^j) N * (P^(j+3)) N) := by ring
    _ ≤ (((j : ℝ)+1) * ((j : ℝ)+2)) *
        ((tpart m * P^(j+1)) N * (P^(j+2)) N) :=
      mul_le_mul_of_nonneg_left hc hfactor
    _ = ((j : ℝ)+1) *
        (((j : ℝ)+1+1) * (tpart m * P^(j+1)) N) * (P^(j+2)) N := by ring
    _ = ((j : ℝ)+1) *
        (((N : ℝ)-((j : ℝ)+1+1)) * (P^(j+1+1)) N) * (P^(j+2)) N := by
      rw [he₂]
    _ = _ := by dsimp [P]; ring

end DominationULC
