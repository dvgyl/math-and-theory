import MainSequence
import SequenceSemantics

noncomputable section
open Polynomial
namespace PowerRank

/-- The exact integer-valued form, including the signed square in the manuscript. -/
def mainInteger (n : ℕ) : ℤ :=
  1 + 2 ^ n + 3 ^ n * (1 - 2 ^ n) ^ 2 + (n : ℤ) * 9 ^ n * (1 + 2 ^ n) ^ 3

theorem mainInteger_pos (n : ℕ) : 0 < mainInteger n := by
  unfold mainInteger
  positivity

theorem mainSequence_eq_intCast (n : ℕ) : mainSequence n = (mainInteger n : ℂ) := by
  simp [mainSequence, mainInteger]

theorem mainSequence_ne_zero (n : ℕ) : mainSequence n ≠ 0 := by
  rw [mainSequence_eq_intCast]
  exact_mod_cast ne_of_gt (mainInteger_pos n)

theorem mainSequence_recurrenceRank : recurrenceRank mainSequence = 13 :=
  recurrenceRank_eq_of_hasRecurrenceRank _ _ mainSequence_rank_thirteen

theorem mainSequence_annihilates_all_indices :
    ∀ n, polyAction initialCharacteristic mainSequence n = 0 := by
  have h := polyAction_sum_eq_zero_of_eventually mainBases mainBases_ne_zero
    mainBases_injective mainCoefficients initialCharacteristic
    (by rw [← mainSequence_expansion]; exact mainSequence_minimalCharacteristic.1.2.2)
  rw [← mainSequence_expansion] at h
  intro n
  exact congrFun h n

/-- The zeroth-power boundary is the constant sequence one. -/
theorem constant_one_recurrenceRank : recurrenceRank (fun _ : ℕ => (1 : ℂ)) = 1 := by
  let lam : Fin 1 → ℂ := fun _ => 1
  let P : Fin 1 → ℂ[X] := fun _ => 1
  have h := recurrenceRank_expPoly_sum lam (by intro i; simp [lam])
    (by intro i j h; exact Subsingleton.elim i j) P (by intro i; simp [P])
  have heq : expPoly (1 : ℂ) (1 : ℂ[X]) = (fun _ : ℕ => (1 : ℂ)) := by
    ext n
    simp [expPoly]
  simpa only [lam, P, Fin.sum_univ_one, natDegree_one, zero_add, heq] using h

theorem mainSequence_zeroth_power_rank :
    recurrenceRank (fun n => mainSequence n ^ 0) = 1 := by
  simpa only [pow_zero] using constant_one_recurrenceRank

end PowerRank
