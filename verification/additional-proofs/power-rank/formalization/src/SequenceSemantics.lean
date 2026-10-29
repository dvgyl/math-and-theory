import RankPrinciple

noncomputable section
open Polynomial
namespace PowerRank

/-- The least admissible eventual complex recurrence order. On the domain of
constant-recursive sequences, the order set is nonempty. -/
def recurrenceRank (u : Seq) : ℕ :=
  sInf {r : ℕ | ∃ q : ℂ[X], AdmissibleAnnihilator q u ∧ q.natDegree = r}

theorem recurrenceRank_eq_of_hasRecurrenceRank (u : Seq) (r : ℕ)
    (h : HasRecurrenceRank u r) : recurrenceRank u = r := by
  apply IsLeast.csInf_eq
  refine ⟨h.1, ?_⟩
  rintro d ⟨q, hq, hd⟩
  rw [← hd]
  exact h.2 q hq

theorem recurrenceRank_expPoly_sum {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    recurrenceRank (∑ i, expPoly (lam i) (P i)) = ∑ i, ((P i).natDegree + 1) :=
  recurrenceRank_eq_of_hasRecurrenceRank _ _
    (hasRecurrenceRank_expPoly_sum lam hlam hinj P hP)

/-- For exponential-polynomial sequences every eventual annihilator works from zero. -/
theorem polyAction_sum_eq_zero_of_eventually {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (q : ℂ[X])
    (hq : EventuallyAnnihilates q (∑ i, expPoly (lam i) (P i))) :
    polyAction q (∑ i, expPoly (lam i) (P i)) = 0 := by
  classical
  have heach := (eventual_annihilator_sum_iff lam hlam hinj P q).mp hq
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [polyAction_expPoly,
    (eventual_annihilator_iff_coeff_kernel (lam i) (hlam i) q (P i)).mp (heach i)]
  ext n
  simp [expPoly]

theorem characteristicProduct_annihilates_all_indices {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    ∀ n, polyAction (characteristicProduct lam P) (∑ i, expPoly (lam i) (P i)) n = 0 := by
  have h := polyAction_sum_eq_zero_of_eventually lam hlam hinj P _
    (minimalCharacteristic_expPoly_sum lam hlam hinj P hP).1.2.2
  intro n
  exact congrFun h n

/-- The manuscript's rank-zero convention follows from the literal annihilator 1. -/
theorem recurrenceRank_eq_zero_of_eventually_zero (u : Seq)
    (hu : ∃ N, ∀ n ≥ N, u n = 0) : recurrenceRank u = 0 := by
  apply recurrenceRank_eq_of_hasRecurrenceRank
  refine ⟨⟨1, ⟨monic_one, by simp, ?_⟩, by simp⟩, fun q hq => Nat.zero_le _⟩
  simpa only [EventuallyAnnihilates, polyAction, map_one, Module.End.one_apply] using hu

end PowerRank
