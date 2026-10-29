module
public import MixedComponents

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

/-- The full claimed polynomial, including repeated characteristic roots. -/
def characteristicProduct {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (P : ι → ℂ[X]) : ℂ[X] :=
  ∏ i, (X - C (lam i)) ^ ((P i).natDegree + 1)

/-- Every eventual complex annihilator has exactly the required root multiplicities. -/
theorem eventual_annihilator_sum_iff_product_dvd {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) (q : ℂ[X]) :
    EventuallyAnnihilates q (∑ i, expPoly (lam i) (P i)) ↔
      characteristicProduct lam P ∣ q := by
  classical
  constructor
  · intro h
    have heach := (eventual_annihilator_sum_iff lam hlam hinj P q).mp h
    apply Fintype.prod_dvd_of_coprime
      (fun i j hij => (pairwise_coprime_X_sub_C hinj hij).pow)
    intro i
    exact (eventual_annihilator_expPoly_iff_dvd (lam i) (hlam i) (P i) (hP i) q).mp
      (heach i)
  · intro h
    apply (eventual_annihilator_sum_iff lam hlam hinj P q).mpr
    intro i
    apply (eventual_annihilator_expPoly_iff_dvd (lam i) (hlam i) (P i) (hP i) q).mpr
    have hterm : (X - C (lam i)) ^ ((P i).natDegree + 1) ∣ characteristicProduct lam P := by
      unfold characteristicProduct
      exact Finset.dvd_prod_of_mem (fun j => (X - C (lam j)) ^ ((P j).natDegree + 1))
        (Finset.mem_univ i)
    exact hterm.trans h

/-- The candidate's actual minimal-characteristic notion, over C and on a tail. -/
theorem minimalCharacteristic_expPoly_sum {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    MinimalCharacteristic (characteristicProduct lam P) (∑ i, expPoly (lam i) (P i)) := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact monic_prod_of_monic _ _ (fun i hi => (monic_X_sub_C _).pow _)
  · rw [coeff_zero_eq_eval_zero, characteristicProduct, eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [eval_pow, eval_sub, eval_X, eval_C, zero_sub]
    exact pow_ne_zero _ (neg_ne_zero.mpr (hlam i))
  · exact (eventual_annihilator_sum_iff_product_dvd lam hlam hinj P hP _).mpr dvd_rfl
  · intro q hq
    exact (eventual_annihilator_sum_iff_product_dvd lam hlam hinj P hP q).mp hq.2.2

/-- Exact sum of all characteristic-root multiplicities. -/
theorem characteristicProduct_natDegree {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (P : ι → ℂ[X]) :
    (characteristicProduct lam P).natDegree = ∑ i, ((P i).natDegree + 1) := by
  classical
  rw [characteristicProduct, natDegree_prod]
  · simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  · intro i hi
    exact pow_ne_zero _ (X_sub_C_ne_zero _)

/-- A faithful least-order proposition, without assuming a candidate rank formula. -/
def HasRecurrenceRank (u : Seq) (r : ℕ) : Prop :=
  (∃ q, AdmissibleAnnihilator q u ∧ q.natDegree = r) ∧
    ∀ q, AdmissibleAnnihilator q u → r ≤ q.natDegree

theorem hasRecurrenceRank_expPoly_sum {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    HasRecurrenceRank (∑ i, expPoly (lam i) (P i)) (∑ i, ((P i).natDegree + 1)) := by
  let χ := characteristicProduct lam P
  have hminimal := minimalCharacteristic_expPoly_sum lam hlam hinj P hP
  refine ⟨⟨χ, hminimal.1, characteristicProduct_natDegree lam P⟩, ?_⟩
  intro q hq
  rw [← characteristicProduct_natDegree lam P]
  exact natDegree_le_of_dvd (hminimal.2 q hq) hq.1.ne_zero

end PowerRank
