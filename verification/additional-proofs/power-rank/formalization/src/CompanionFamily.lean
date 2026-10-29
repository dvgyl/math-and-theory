import CompanionExpansion
import MainTheorem

noncomputable section
open Polynomial
namespace PowerRank.Companion

def characteristic {k : ℕ} (p : OddPrimes k) (d M : ℕ) : ℂ[X] :=
  ∏ b : NormalComposition k d M, (X-C (complexBase p b))

def integralCharacteristic {k : ℕ} (p : OddPrimes k) (d M : ℕ) : ℤ[X] :=
  ∏ b : NormalComposition k d M, (X-C (natBase p d b.1.1 : ℤ))

theorem characteristic_eq_product {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    characteristic p d M = characteristicProduct
      (fun b : NormalComposition k d M => complexBase p b) (coefficientPolynomial hd) := by
  simp [characteristic, characteristicProduct, coefficientPolynomial]

theorem power_minimalCharacteristic {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    MinimalCharacteristic (characteristic p d M) (powerSequence p d M) := by
  rw [powerSequence_expansion p d hd, characteristic_eq_product p d hd]
  exact minimalCharacteristic_expPoly_sum _ (complexBase_ne_zero p)
    (complexBase_injective p hd) (coefficientPolynomial hd) (coefficientPolynomial_ne_zero hd)

theorem power_rank {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    recurrenceRank (powerSequence p d M) = (M+k+2).choose (k+2) -
      if M < d then 0 else (M-d+k+2).choose (k+2) := by
  rw [powerSequence_expansion p d hd, recurrenceRank_expPoly_sum _
    (complexBase_ne_zero p) (complexBase_injective p hd) (coefficientPolynomial hd)
    (coefficientPolynomial_ne_zero hd)]
  simpa [coefficientPolynomial] using normalComposition_card k d M

theorem sequence_rank {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 2 ≤ d) :
    recurrenceRank (sequence p d) = k+3 := by
  have h := power_rank p d (by omega) 1
  have he : (1+k+2).choose (k+2) = k+3 := by
    rw [Nat.choose_symm_of_eq_add (show 1+k+2 = (k+2)+1 by omega), Nat.choose_one_right]
    omega
  have hseq : powerSequence p d 1 = sequence p d := by
    funext n
    exact pow_one _
  rw [hseq] at h
  simpa [he, show 1 < d by omega] using h

theorem integralCharacteristic_map {k : ℕ} (p : OddPrimes k) (d M : ℕ) :
    (integralCharacteristic p d M).map (Int.castRingHom ℂ) = characteristic p d M := by
  simp [integralCharacteristic, characteristic, complexBase, Polynomial.map_prod]

theorem integralCharacteristic_monic {k : ℕ} (p : OddPrimes k) (d M : ℕ) :
    (integralCharacteristic p d M).Monic := by
  unfold integralCharacteristic
  exact monic_prod_of_monic _ _ (fun b hb => monic_X_sub_C _)

theorem integralCharacteristic_constant_ne_zero {k : ℕ} (p : OddPrimes k)
    (d : ℕ) (hd : 0 < d) (M : ℕ) : (integralCharacteristic p d M).coeff 0 ≠ 0 := by
  have h := (power_minimalCharacteristic p d hd M).1.2.1
  rw [← integralCharacteristic_map] at h
  simpa using h

theorem characteristic_monic {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    (characteristic p d M).Monic := (power_minimalCharacteristic p d hd M).1.1

theorem characteristic_constant_ne_zero {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    (characteristic p d M).coeff 0 ≠ 0 := (power_minimalCharacteristic p d hd M).1.2.1

theorem power_annihilates_all_indices {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M n : ℕ) :
    polyAction (characteristic p d M) (powerSequence p d M) n = 0 := by
  rw [powerSequence_expansion p d hd, characteristic_eq_product p d hd]
  exact characteristicProduct_annihilates_all_indices _ (complexBase_ne_zero p)
    (complexBase_injective p hd) (coefficientPolynomial hd) (coefficientPolynomial_ne_zero hd) n

theorem integral_forward_recurrence {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M n : ℕ) :
    sequence p d (n+(integralCharacteristic p d M).natDegree)^M =
      -∑ j ∈ Finset.range (integralCharacteristic p d M).natDegree,
        ((integralCharacteristic p d M).coeff j : ℂ) * sequence p d (n+j)^M := by
  have h := forward_recurrence_of_monic (characteristic p d M)
    (characteristic_monic p d hd M) (powerSequence p d M) n
    (power_annihilates_all_indices p d hd M n)
  rw [← integralCharacteristic_map] at h
  rw [natDegree_map_eq_of_injective
    (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)] at h
  simpa only [coeff_map, powerSequence, Int.coe_castRingHom] using h

theorem power_ranks_over_subfield {K : Type*} [Field K] [CharZero K] (f : K →+* ℂ)
    {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    recurrenceRankOver f (powerSequence p d M) = recurrenceRank (powerSequence p d M) := by
  apply recurrenceRankOver_eq_of_integral f _ (integralCharacteristic p d M)
  rw [integralCharacteristic_map]
  exact power_minimalCharacteristic p d hd M

theorem composition_zero {k : ℕ} (b : Composition k 0) : b.1 = 0 := by
  funext i
  have hl : b.1 i ≤ ∑ j, b.1 j :=
    Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  rw [b.2] at hl
  exact Nat.eq_zero_of_le_zero hl

theorem zero_power_characteristic {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) :
    characteristic p d 0 = X-C 1 := by
  have hcard : Fintype.card (NormalComposition k d 0) = 1 := by
    simpa [hd] using normalComposition_card k d 0
  have hb : ∀ b : NormalComposition k d 0, complexBase p b = 1 := by
    intro b
    simp [complexBase, composition_zero b.1, natBase]
  simp only [characteristic, hb, Finset.prod_const, Finset.card_univ, hcard, pow_one]

theorem ranks_differ_at_smaller_parameter {k : ℕ} (p : OddPrimes k) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hde : d < e) :
    recurrenceRank (powerSequence p d d) ≠ recurrenceRank (powerSequence p e d) := by
  rw [power_rank p d hd, power_rank p e he]
  have hp : 0 < (d+k+2).choose (k+2) := Nat.choose_pos (by omega)
  simp only [lt_self_iff_false, ite_false, Nat.sub_self, zero_add, Nat.choose_self, hde, ite_true,
    Nat.sub_zero]
  omega

theorem power_rank_functions_injective {k : ℕ} (p : OddPrimes k) :
    Function.Injective (fun d : {d : ℕ // 2 ≤ d} =>
      fun M => recurrenceRank (powerSequence p d.1 M)) := by
  intro d e heq
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ranks_differ_at_smaller_parameter p (by omega) (by omega) hlt (congrFun heq d.1)
  · exact ranks_differ_at_smaller_parameter p (by omega) (by omega) hgt (congrFun heq e.1).symm

theorem all_r_power_rank (r d M : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d) (p : OddPrimes (r-3)) :
    recurrenceRank (powerSequence p d M) = (M+r-1).choose (r-1) -
      if M < d then 0 else (M-d+r-1).choose (r-1) := by
  have h := power_rank p d (by omega) M
  have hk : r-3+2 = r-1 := by omega
  have hM : M+(r-3)+2 = M+r-1 := by omega
  have hMd : M-d+(r-3)+2 = M-d+r-1 := by omega
  simpa only [hk, hM, hMd] using h

theorem all_r_sequence_rank (r d : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d) (p : OddPrimes (r-3)) :
    recurrenceRank (sequence p d) = r := by
  simpa [show r-3+3=r by omega] using sequence_rank p d hd

theorem family_result (r d : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d) (p : OddPrimes (r-3)) :
    (∀ n, 0 < naturalSequence p d n ∧ sequence p d n = (naturalSequence p d n : ℂ)) ∧
    recurrenceRank (sequence p d) = r ∧
    (∀ M, MinimalCharacteristic (characteristic p d M) (powerSequence p d M)) ∧
    (∀ M, recurrenceRank (powerSequence p d M) = (M+r-1).choose (r-1) -
      if M < d then 0 else (M-d+r-1).choose (r-1)) ∧
    Function.Injective (fun e : {e : ℕ // 2 ≤ e} =>
      fun M => recurrenceRank (powerSequence p e.1 M)) := by
  exact ⟨fun n => ⟨naturalSequence_pos p d n, rfl⟩,
    all_r_sequence_rank r d hr hd p,
    power_minimalCharacteristic p d (by omega),
    fun M => all_r_power_rank r d M hr hd p,
    power_rank_functions_injective p⟩

#print axioms characteristic_eq_product
#print axioms power_minimalCharacteristic
#print axioms power_rank
#print axioms sequence_rank
#print axioms integralCharacteristic_map
#print axioms integralCharacteristic_monic
#print axioms integralCharacteristic_constant_ne_zero
#print axioms characteristic_monic
#print axioms characteristic_constant_ne_zero
#print axioms power_annihilates_all_indices
#print axioms integral_forward_recurrence
#print axioms power_ranks_over_subfield
#print axioms composition_zero
#print axioms zero_power_characteristic
#print axioms ranks_differ_at_smaller_parameter
#print axioms power_rank_functions_injective
#print axioms all_r_power_rank
#print axioms all_r_sequence_rank
#print axioms family_result
end PowerRank.Companion
