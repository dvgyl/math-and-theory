import QPermanentResearch.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
The generic endpoint identity by swapping the selected pair of rows.
Adapted to an arbitrary commutative ring and the genuine real q-permanent
from Kitamura's Apache-2.0 PairMinorIdentity.lean, pinned commit
4200da4fc1a132d69c23fb877795b5b72089544b. Its license is included as
LICENSE-Kitamura; see THIRD_PARTY_NOTICES.md.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section
variable {R : Type*} [CommRing R]

def permutationTerm {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) : R := ∏ i, A i (σ i)

def rowPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

theorem rowPairs_card (n : ℕ) : (rowPairs n).card = n.choose 2 := by
  classical
  have hinner (j : Fin n) :
      (Finset.univ.filter (fun i : Fin n => i < j)).card = j.val := by
    have hset : Finset.univ.filter (fun i : Fin n => i < j) = Finset.Iio j := by
      ext i
      simp
    rw [hset]
    exact Fin.card_Iio j
  calc
    (rowPairs n).card =
        ∑ p : Fin n × Fin n, if p.1 < p.2 then (1 : ℕ) else 0 := by
      simp [rowPairs]
    _ = ∑ j : Fin n, ∑ i : Fin n, if i < j then (1 : ℕ) else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ j : Fin n, j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_boole]
      exact hinner j
    _ = n * (n - 1) / 2 := by
      rw [← Finset.sum_range (fun i : ℕ => i)]
      exact Finset.sum_range_id n
    _ = n.choose 2 := (Nat.choose_two_right n).symm

theorem inversionCount_eq_filterCard {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (rowPairs n |>.filter fun p => σ p.2 < σ p.1).card = inversionCount σ := by
  classical
  simp [rowPairs, inversionCount, Finset.filter_filter]

def remainingProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) : R :=
  ∏ k ∈ (Finset.univ.erase i).erase j, A k (σ k)

theorem permutationTerm_split {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permutationTerm A σ = A i (σ i) * A j (σ j) * remainingProduct A σ i j := by
  classical
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
  unfold permutationTerm remainingProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ hj]
  ring

theorem remainingProduct_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    remainingProduct A (σ * Equiv.swap i j) i j = remainingProduct A σ i j := by
  classical
  apply Finset.prod_congr rfl
  intro k hk
  have hkj := Finset.ne_of_mem_erase hk
  have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

def pairMinorContribution {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) (σ : Equiv.Perm (Fin n)) : R :=
  if σ i < σ j then
    (A i (σ i) * A j (σ j) - A i (σ j) * A j (σ i)) *
      remainingProduct A σ i j
  else 0

theorem pairMinorContribution_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) (hij : i ≠ j) (σ : Equiv.Perm (Fin n)) :
    pairMinorContribution A i j σ =
      (if σ i < σ j then permutationTerm A σ else 0) -
        (if σ i < σ j then permutationTerm A (σ * Equiv.swap i j) else 0) := by
  classical
  by_cases h : σ i < σ j
  · simp only [pairMinorContribution, if_pos h]
    rw [permutationTerm_split A σ i j hij,
      permutationTerm_split A (σ * Equiv.swap i j) i j hij, remainingProduct_swap]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · simp [pairMinorContribution, h]

theorem ascent_swapped_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (∑ σ : Equiv.Perm (Fin n),
      if σ i < σ j then permutationTerm A (σ * Equiv.swap i j) else 0) =
      ∑ σ : Equiv.Perm (Fin n), if σ j < σ i then permutationTerm A σ else 0 := by
  classical
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using
    (Group.mulRight_bijective (Equiv.swap i j)).sum_comp
      (fun σ : Equiv.Perm (Fin n) => if σ j < σ i then permutationTerm A σ else 0)

theorem pairMinor_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) (hij : i ≠ j) :
    (∑ σ : Equiv.Perm (Fin n), pairMinorContribution A i j σ) =
      ∑ σ : Equiv.Perm (Fin n),
        (permutationTerm A σ - 2 * (if σ j < σ i then permutationTerm A σ else 0)) := by
  classical
  simp_rw [pairMinorContribution_eq A i j hij]
  rw [Finset.sum_sub_distrib, ascent_swapped_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, not_lt_of_ge h.le]
  · simp [h, not_lt_of_ge h.le]
    ring

/-- The minors are represented by ascending images and complementary bijections. -/
def pairMinorSum {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  ∑ p ∈ rowPairs n, ∑ σ : Equiv.Perm (Fin n), pairMinorContribution A p.1 p.2 σ

def endpointSum {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  ∑ σ : Equiv.Perm (Fin n), (inversionCount σ : R) * permutationTerm A σ

theorem descent_pair_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) :
    (∑ p ∈ rowPairs n, if σ p.2 < σ p.1 then permutationTerm A σ else 0) =
      (inversionCount σ : R) * permutationTerm A σ := by
  classical
  rw [← Finset.sum_filter]
  simp [inversionCount_eq_filterCard, nsmul_eq_mul]

theorem pairMinorSum_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    pairMinorSum A = (rowPairs n).card * qPermanent A 1 -
      2 * endpointSum A := by
  classical
  unfold pairMinorSum
  have hpair : ∀ p ∈ rowPairs n,
      (∑ σ : Equiv.Perm (Fin n), pairMinorContribution A p.1 p.2 σ) =
        ∑ σ : Equiv.Perm (Fin n),
          (permutationTerm A σ - 2 * (if σ p.2 < σ p.1 then permutationTerm A σ else 0)) := by
    intro p hp
    exact pairMinor_sum A p.1 p.2 (Finset.mem_filter.mp hp).2.ne
  simp_rw [Finset.sum_congr rfl hpair]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, descent_pair_sum]
  simp [qPermanent, endpointSum, permutationTerm, Finset.mul_sum, nsmul_eq_mul]


theorem endpointSum_eq_derivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    endpointSum A = qPermanentDerivative A 1 := by
  simp [endpointSum, permutationTerm, qPermanentDerivative]

/-- The actual derivative equals the permanent term minus the sum of two-by-two
    determinants times complementary products. Ascending images uniquely index
    each complementary bijection; no signed permutation sum is assumed. -/
theorem endpointDerivative_pairMinorSum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    2 * qPermanentDerivative A 1 =
      (rowPairs n).card * qPermanent A 1 - pairMinorSum A := by
  rw [pairMinorSum_eq, endpointSum_eq_derivative]
  ring

theorem endpointDerivative_choose_pairMinorSum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    2 * qPermanentDerivative A 1 =
      (n.choose 2 : ℝ) * qPermanent A 1 - pairMinorSum A := by
  simpa only [rowPairs_card] using endpointDerivative_pairMinorSum A

end
end QPermanentResearch
