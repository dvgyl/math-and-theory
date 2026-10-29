module
public import MainProperties
public import Nonquasipolynomial
public import SquareFloor
public import IntegralFields

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

theorem minimalCharacteristic_unique {p q : ℂ[X]} {u : Seq}
    (hp : MinimalCharacteristic p u) (hq : MinimalCharacteristic q u) : p = q :=
  eq_of_monic_of_associated hp.1.1 hq.1.1
    (associated_of_dvd_dvd (hp.2 q hq.1) (hq.2 p hp.1))

theorem mainPower_first_characteristic : powerCharacteristic 1 = initialCharacteristic := by
  apply minimalCharacteristic_unique (mainPower_minimalCharacteristic 1)
  have hseq : mainPowerSequence 1 = mainSequence := by ext n; simp [mainPowerSequence]
  rw [hseq]
  exact mainSequence_minimalCharacteristic

theorem mainPower_zero_characteristic : powerCharacteristic 0 = X - 1 := by
  unfold powerCharacteristic
  rw [Fintype.prod_sigma]
  norm_num [powerBase, expectedMultiplicity, Fin.prod_univ_succ]

/-- A monic annihilator gives the usual forward recurrence, at the actual
sequence index and with its true degree. -/
theorem forward_recurrence_of_monic (q : ℂ[X]) (hq : q.Monic) (u : Seq) (n : ℕ)
    (hann : polyAction q u n = 0) :
    u (n + q.natDegree) = -∑ k ∈ Finset.range q.natDegree, q.coeff k * u (n + k) := by
  rw [polyAction_apply, Finset.sum_range_succ, hq.coeff_natDegree, one_mul] at hann
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hann)

/-- Each integral displayed polynomial gives the literal recurrence from n=0. -/
theorem mainPower_integral_forward_recurrence (M n : ℕ) :
    mainSequence (n + (integralPowerCharacteristic M).natDegree) ^ M =
      -∑ k ∈ Finset.range (integralPowerCharacteristic M).natDegree,
        ((integralPowerCharacteristic M).coeff k : ℂ) * mainSequence (n + k) ^ M := by
  have h := forward_recurrence_of_monic (powerCharacteristic M)
    (mainPower_minimalCharacteristic M).1.1 (mainPowerSequence M) n
    (mainPower_annihilates_all_indices M n)
  rw [← integralPowerCharacteristic_map] at h
  rw [natDegree_map_eq_of_injective
    (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)] at h
  simpa only [coeff_map, mainPowerSequence, Int.coe_castRingHom] using h

/-- The literal sequence, exact all-power polynomial/rank formula, quantitative
correction and nonquasipolynomial conclusion of the main theorem. -/
theorem main_result :
    (∀ n, 0 < mainInteger n ∧ mainSequence n = (mainInteger n : ℂ)) ∧
    recurrenceRank mainSequence = 13 ∧
    (∀ M, MinimalCharacteristic (powerCharacteristic M) (mainPowerSequence M)) ∧
    (∀ M, recurrenceRank (mainPowerSequence M) =
      (M + 1) * (2 * M + 1) * (7 * M + 6) / 6 - 2 * squareCorrection M) ∧
    (∀ M ≥ 1, |rankCubicValue M - (recurrenceRank (mainPowerSequence M) : ℝ) -
      (Real.sqrt 3 - 1) * Real.sqrt (M : ℝ)| ≤ 2) ∧
    ¬ EventuallyQuasipolynomial (fun M => (recurrenceRank (mainPowerSequence M) : ℝ)) := by
  exact ⟨fun n => ⟨mainInteger_pos n, mainSequence_eq_intCast n⟩,
    mainSequence_recurrenceRank, mainPower_minimalCharacteristic,
    mainPower_rank_cubic_squareCorrection, mainPower_sqrt_error,
    mainPower_not_eventuallyQuasipolynomial⟩

end PowerRank
