import CyclicDeterminant

/-!
Extension from a single tilted edge to independent reciprocal edge tilts.
This file is an auxiliary bridge, not a proof of the original current bound.
-/

open scoped BigOperators
open Equiv

namespace UnicyclicDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cycleTilt (A : Matrix ι ι ℝ) (σ : Perm ι) (q : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = σ j then q j else 1) *
    (if j = σ i then (q i)⁻¹ else 1) * A i j

theorem cycleTilt_prod (A : Matrix ι ι ℝ) (σ π : Perm ι) (q : ι → ℝ) :
    (∏ j, cycleTilt A σ q (π j) j) =
      (∏ j, if π j = σ j then q j else 1) *
      (∏ j, if π (σ j) = j then (q j)⁻¹ else 1) *
      (∏ j, A (π j) j) := by
  have hinv (j : ι) : π⁻¹ j = σ j ↔ π (σ j) = j := by
    constructor
    · intro h
      have hh := congrArg π h
      simpa using hh.symm
    · intro h
      apply π.injective
      simpa using h.symm
  have hb : (∏ j, if j = σ (π j) then (q (π j))⁻¹ else 1) =
      ∏ j, if π (σ j) = j then (q j)⁻¹ else 1 := by
    calc
      _ = ∏ j, if π⁻¹ j = σ j then (q j)⁻¹ else 1 := by
        simpa using Equiv.prod_comp π (fun j => if π⁻¹ j = σ j then (q j)⁻¹ else 1)
      _ = _ := by simp_rw [hinv]
  simp only [cycleTilt, Finset.prod_mul_distrib]
  rw [hb]

theorem cycle_forward_ne_backward (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (i : ι) : σ i ≠ σ⁻¹ i := by
  intro h
  apply cycle_no_two σ hc hn i
  simpa using congrArg σ h

theorem permutation_term_multitilt (A : Matrix ι ι ℝ) (σ π : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hA : ∀ i j, i ≠ j → i ≠ σ j → i ≠ σ⁻¹ j → A i j = 0)
    (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (a : ι) :
    (∏ j, cycleTilt A σ q (π j) j) =
      (∏ j, A (π j) j) +
      (if π = σ then ((∏ j, q j) - 1) * ∏ j, A (π j) j else 0) +
      (if π = σ⁻¹ then ((∏ j, q j)⁻¹ - 1) * ∏ j, A (π j) j else 0) := by
  rw [cycleTilt_prod]
  have hinv : σ ≠ σ⁻¹ := by
    intro h
    exact cycle_forward_ne_backward σ hc hn a (congrArg (fun f : Perm ι => f a) h)
  by_cases hp : π = σ
  · subst π
    simp only [ite_true, hinv, ite_false, add_zero,
      cycle_no_two σ hc hn, Finset.prod_const_one, mul_one]
    ring
  by_cases hp' : π = σ⁻¹
  · subst π
    have hrev (j : ι) : σ⁻¹ j ≠ σ j := (cycle_forward_ne_backward σ hc hn j).symm
    simp only [hp, ite_false, add_zero, ite_true, hrev,
      Perm.inv_apply_self, Finset.prod_const_one, one_mul, Finset.prod_inv_distrib]
    ring
  simp only [hp, hp', ite_false, add_zero]
  by_cases hz : (∏ j, A (π j) j) = 0
  · simp [hz]
  have hs : ∀ j, π j = j ∨ π j = σ j ∨ π j = σ⁻¹ j := by
    intro j
    by_contra h
    push_neg at h
    exact hz (Finset.prod_eq_zero (Finset.mem_univ j)
      (hA (π j) j h.1 h.2.1 h.2.2))
  have hpairs (j : ι) := counted_edge_paired σ π hc hn hs hp hp' j
  have hb : (∏ j, if π (σ j) = j then (q j)⁻¹ else 1) =
      (∏ j, if π j = σ j then q j else 1)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases he : π j = σ j
    · simp [he, (hpairs j).mp he]
    · have he' : π (σ j) ≠ j := fun h => he ((hpairs j).mpr h)
      simp [he, he']
  have hnz : (∏ j, if π j = σ j then q j else 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    split_ifs <;> simp_all
  rw [hb, mul_inv_cancel₀ hnz, one_mul]

theorem cyclic_determinant_multitilt (A : Matrix ι ι ℝ) (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hA : ∀ i j, i ≠ j → i ≠ σ j → i ≠ σ⁻¹ j → A i j = 0)
    (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (a : ι) :
    (cycleTilt A σ q).det = A.det +
      ((∏ j, q j) - 1) * ((Perm.sign σ : ℤ) : ℝ) * (∏ j, A (σ j) j) +
      ((∏ j, q j)⁻¹ - 1) * ((Perm.sign σ⁻¹ : ℤ) : ℝ) *
        (∏ j, A (σ⁻¹ j) j) := by
  have hterm (π : Perm ι) :
      ((Perm.sign π : ℤ) : ℝ) * (∏ j, cycleTilt A σ q (π j) j) =
        ((Perm.sign π : ℤ) : ℝ) * (∏ j, A (π j) j) +
        (if π = σ then ((∏ j, q j) - 1) * ((Perm.sign σ : ℤ) : ℝ) *
          (∏ j, A (σ j) j) else 0) +
        (if π = σ⁻¹ then ((∏ j, q j)⁻¹ - 1) * ((Perm.sign σ⁻¹ : ℤ) : ℝ) *
          (∏ j, A (σ⁻¹ j) j) else 0) := by
    rw [permutation_term_multitilt A σ π hc hn hA q hq a]
    split_ifs <;> simp_all <;> ring
  simp_rw [Matrix.det_apply', hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

#print axioms cyclic_determinant_multitilt

end

end UnicyclicDeterminant
