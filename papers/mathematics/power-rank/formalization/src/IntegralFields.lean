import MainPowers

noncomputable section
open Polynomial
namespace PowerRank

/-- The manuscript's full characteristic polynomial with integer coefficients. -/
def integralPowerCharacteristic (M : ℕ) : ℤ[X] :=
  ∏ i : PowerIndex M,
    (X - C ((2 : ℤ) ^ i.2.val * (3 : ℤ) ^ i.1.val)) ^
      expectedMultiplicity M i.1.val i.2.val

theorem integralPowerCharacteristic_map (M : ℕ) :
    (integralPowerCharacteristic M).map (Int.castRingHom ℂ) = powerCharacteristic M := by
  simp [integralPowerCharacteristic, powerCharacteristic, powerBase, Polynomial.map_prod, Polynomial.C_ofNat]

theorem integralPowerCharacteristic_monic (M : ℕ) :
    (integralPowerCharacteristic M).Monic := by
  unfold integralPowerCharacteristic
  exact monic_prod_of_monic _ _ (fun i hi => (monic_X_sub_C _).pow _)

theorem integralPowerCharacteristic_constant_ne_zero (M : ℕ) :
    (integralPowerCharacteristic M).coeff 0 ≠ 0 := by
  have h := (mainPower_minimalCharacteristic M).1.2.1
  rw [← integralPowerCharacteristic_map] at h
  simpa using h

/-- Recurrence rank over a subfield of C: admissible coefficients are embedded
by f, with the same eventual convention and nonzero constant coefficient. -/
def recurrenceRankOver {K : Type*} [Field K] (f : K →+* ℂ) (u : Seq) : ℕ :=
  sInf {r : ℕ | ∃ q : K[X], AdmissibleAnnihilator (q.map f) u ∧ q.natDegree = r}

/-- An integral minimal characteristic polynomial gives equal ranks over any
characteristic-zero subfield of C, against arbitrary eventual recurrences. -/
theorem recurrenceRankOver_eq_of_integral {K : Type*} [Field K] [CharZero K]
    (f : K →+* ℂ) (u : Seq) (χ : ℤ[X])
    (hχ : MinimalCharacteristic (χ.map (Int.castRingHom ℂ)) u) :
    recurrenceRankOver f u = recurrenceRank u := by
  have hdeg : (χ.map (Int.castRingHom ℂ)).natDegree = χ.natDegree :=
    natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective) χ
  have hRank : recurrenceRank u = χ.natDegree := by
    apply recurrenceRank_eq_of_hasRecurrenceRank
    refine ⟨⟨χ.map (Int.castRingHom ℂ), hχ.1, hdeg⟩, ?_⟩
    intro q hq
    rw [← hdeg]
    exact natDegree_le_of_dvd (hχ.2 q hq) hq.1.ne_zero
  rw [hRank]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨χ.map (Int.castRingHom K), ?_, ?_⟩
    · have hcomp : (χ.map (Int.castRingHom K)).map f = χ.map (Int.castRingHom ℂ) := by
        rw [Polynomial.map_map]
        congr 1
        ext z
        simp
      rw [hcomp]
      exact hχ.1
    · exact natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom K) from Int.cast_injective) χ
  · rintro d ⟨q, hq, hd⟩
    rw [← hd, ← natDegree_map_eq_of_injective f.injective q, ← hdeg]
    exact natDegree_le_of_dvd (hχ.2 (q.map f) hq) hq.1.ne_zero

/-- Rational and real ranks equal the already-proved complex rank for every M. -/
theorem mainPower_rational_real_ranks (M : ℕ) :
    recurrenceRankOver (algebraMap ℚ ℂ) (mainPowerSequence M) = recurrenceRank (mainPowerSequence M) ∧
    recurrenceRankOver Complex.ofRealHom (mainPowerSequence M) = recurrenceRank (mainPowerSequence M) := by
  have hχ : MinimalCharacteristic
      ((integralPowerCharacteristic M).map (Int.castRingHom ℂ)) (mainPowerSequence M) := by
    rw [integralPowerCharacteristic_map]
    exact mainPower_minimalCharacteristic M
  exact ⟨recurrenceRankOver_eq_of_integral _ _ _ hχ,
    recurrenceRankOver_eq_of_integral _ _ _ hχ⟩

end PowerRank
