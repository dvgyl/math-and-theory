import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-!
The arbitrary-size combinatorial and determinant bridge for a tilted cycle.
This is an auxiliary development; it does not yet state or prove the original
Markov-current inequality. No hypothesis is intended to assume the determinant
identity itself.
-/

open scoped BigOperators
open Equiv

namespace UnicyclicDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem cycle_no_fixed [Fintype ι] [DecidableEq ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (i : ι) : σ i ≠ i := by
  intro h
  have hd : Fintype.card ι ∣ 1 := by
    simpa using (hc.pow_apply_eq (Finset.mem_univ i) (n := 1)).mp (by simpa using h)
  have := Nat.le_of_dvd (by decide : 0 < 1) hd
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem cycle_no_two [Fintype ι] [DecidableEq ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (i : ι) : σ (σ i) ≠ i := by
  intro h
  have hd : Fintype.card ι ∣ 2 := by
    apply (hc.pow_apply_eq (Finset.mem_univ i) (n := 2)).mp
    simpa [pow_two, Perm.mul_apply] using h
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem unpaired_forward_forces_cycle (σ π : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hs : ∀ i, π i = i ∨ π i = σ i ∨ π i = σ⁻¹ i)
    (i : ι) (hi : π i = σ i) (hnext : π (σ i) ≠ i) : π = σ := by
  have step (j : ι) (hj : π j = σ j ∧ π (σ j) ≠ j) :
      π (σ j) = σ (σ j) ∧ π (σ (σ j)) ≠ σ j := by
    have hforward : π (σ j) = σ (σ j) := by
      rcases hs (σ j) with hfix | hforward | hback
      · have hh : σ j = j := π.injective (hfix.trans hj.1.symm)
        exact False.elim (cycle_no_fixed σ hc hn j hh)
      · exact hforward
      · exact False.elim (hj.2 (by simpa using hback))
    refine ⟨hforward, ?_⟩
    intro hbad
    have hh : σ (σ j) = j := π.injective (hbad.trans hj.1.symm)
    exact cycle_no_two σ hc hn j hh
  have propagate : ∀ k : ℕ,
      π ((σ ^ k) i) = σ ((σ ^ k) i) ∧
        π (σ ((σ ^ k) i)) ≠ (σ ^ k) i := by
    intro k
    induction k with
    | zero => simpa using And.intro hi hnext
    | succ k ih => simpa [pow_succ', Perm.mul_apply] using step ((σ ^ k) i) ih
  apply Equiv.ext
  intro j
  obtain ⟨k, _, hk⟩ := hc.exists_pow_eq (Finset.mem_univ i) (Finset.mem_univ j)
  simpa [hk] using (propagate k).1

theorem counted_edge_paired (σ π : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hs : ∀ i, π i = i ∨ π i = σ i ∨ π i = σ⁻¹ i)
    (hforward : π ≠ σ) (hback : π ≠ σ⁻¹) (i : ι) :
    π i = σ i ↔ π (σ i) = i := by
  constructor
  · intro hi
    by_contra hnext
    exact hforward (unpaired_forward_forces_cycle σ π hc hn hs i hi hnext)
  · intro hi
    by_contra hprev
    have hs' : ∀ j, π j = j ∨ π j = σ⁻¹ j ∨ π j = (σ⁻¹)⁻¹ j := by
      intro j
      simpa [or_comm, or_left_comm, or_assoc] using hs j
    apply hback
    apply unpaired_forward_forces_cycle σ⁻¹ π hc.inv hn hs' (σ i)
    · simpa using hi
    · simpa using hprev

def edgeTilt (A : Matrix ι ι ℝ) (a b : ι) (q : ℝ) : Matrix ι ι ℝ :=
  fun i j =>
    (if j = a then if i = b then q else 1 else 1) *
    (if j = b then if i = a then q⁻¹ else 1 else 1) * A i j

theorem edgeTilt_prod (A : Matrix ι ι ℝ) (a b : ι) (q : ℝ) (π : Perm ι) :
    (∏ j, edgeTilt A a b q (π j) j) =
      (if π a = b then q else 1) * (if π b = a then q⁻¹ else 1) *
        ∏ j, A (π j) j := by
  unfold edgeTilt
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem permutation_term_tilt (A : Matrix ι ι ℝ) (σ π : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hA : ∀ i j, i ≠ j → i ≠ σ j → i ≠ σ⁻¹ j → A i j = 0)
    (a : ι) (q : ℝ) (hq : q ≠ 0) :
    (∏ j, edgeTilt A a (σ a) q (π j) j) =
      (∏ j, A (π j) j) +
      (if π = σ then (q - 1) * ∏ j, A (π j) j else 0) +
      (if π = σ⁻¹ then (q⁻¹ - 1) * ∏ j, A (π j) j else 0) := by
  rw [edgeTilt_prod]
  have hinv : σ ≠ σ⁻¹ := by
    intro h
    have hh := congrArg (fun f : Perm ι => f (σ a)) h
    exact cycle_no_two σ hc hn a (by simpa using hh)
  by_cases hp : π = σ
  · subst π
    simp only [ite_true, hinv, ite_false, add_zero,
      cycle_no_two σ hc hn a, mul_one]
    ring
  by_cases hp' : π = σ⁻¹
  · subst π
    have hrev : σ⁻¹ a ≠ σ a := by
      intro h
      have hh := congrArg σ h
      exact cycle_no_two σ hc hn a (by simpa using hh.symm)
    simp only [hp, ite_false, add_zero, ite_true, hrev, one_mul,
      Perm.inv_apply_self]
    ring
  simp only [hp, hp', ite_false, add_zero]
  by_cases hz : (∏ j, A (π j) j) = 0
  · simp [hz]
  have hs : ∀ j, π j = j ∨ π j = σ j ∨ π j = σ⁻¹ j := by
    intro j
    by_contra h
    push_neg at h
    have he : A (π j) j = 0 := hA (π j) j h.1 h.2.1 h.2.2
    exact hz (Finset.prod_eq_zero (Finset.mem_univ j) he)
  have hpair := counted_edge_paired σ π hc hn hs hp hp' a
  by_cases he : π a = σ a
  · simp [he, hpair.mp he, hq]
  · have he' : π (σ a) ≠ a := fun h => he (hpair.mpr h)
    simp [he, he']

theorem cyclic_determinant_tilt (A : Matrix ι ι ℝ) (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hA : ∀ i j, i ≠ j → i ≠ σ j → i ≠ σ⁻¹ j → A i j = 0)
    (a : ι) (q : ℝ) (hq : q ≠ 0) :
    (edgeTilt A a (σ a) q).det = A.det +
      (q - 1) * ((Perm.sign σ : ℤ) : ℝ) * (∏ j, A (σ j) j) +
      (q⁻¹ - 1) * ((Perm.sign σ⁻¹ : ℤ) : ℝ) * (∏ j, A (σ⁻¹ j) j) := by
  have hterm (π : Perm ι) :
      ((Perm.sign π : ℤ) : ℝ) * (∏ j, edgeTilt A a (σ a) q (π j) j) =
        ((Perm.sign π : ℤ) : ℝ) * (∏ j, A (π j) j) +
        (if π = σ then (q - 1) * ((Perm.sign σ : ℤ) : ℝ) *
          (∏ j, A (σ j) j) else 0) +
        (if π = σ⁻¹ then (q⁻¹ - 1) * ((Perm.sign σ⁻¹ : ℤ) : ℝ) *
          (∏ j, A (σ⁻¹ j) j) else 0) := by
    rw [permutation_term_tilt A σ π hc hn hA a q hq]
    split_ifs <;> simp_all <;> ring
  simp_rw [Matrix.det_apply', hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

theorem one_way_permutation (σ π : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hs : ∀ i, π i = i ∨ π i = σ i) (hp : π ≠ 1) : π = σ := by
  have hex : ∃ i, π i ≠ i := by
    by_contra h
    push_neg at h
    exact hp (Equiv.ext h)
  obtain ⟨i, hi⟩ := hex
  have hforward : π i = σ i := (hs i).resolve_left hi
  have hnext : π (σ i) ≠ i := by
    intro h
    rcases hs (σ i) with hf | hf
    · exact cycle_no_fixed σ hc hn i (hf.symm.trans h)
    · exact cycle_no_two σ hc hn i (hf.symm.trans h)
  exact unpaired_forward_forces_cycle σ π hc hn
    (fun j => (hs j).imp_right Or.inl) i hforward hnext

theorem cyclic_bidiagonal_determinant (A : Matrix ι ι ℝ) (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι)
    (hA : ∀ i j, i ≠ j → i ≠ σ j → A i j = 0) (a : ι) :
    A.det = (∏ j, A j j) +
      ((Perm.sign σ : ℤ) : ℝ) * (∏ j, A (σ j) j) := by
  have hσ : σ ≠ 1 := by
    intro h
    exact cycle_no_fixed σ hc hn a (by simp [h])
  have hterm (π : Perm ι) :
      ((Perm.sign π : ℤ) : ℝ) * (∏ j, A (π j) j) =
        (if π = 1 then (∏ j, A j j) else 0) +
        (if π = σ then ((Perm.sign σ : ℤ) : ℝ) *
          (∏ j, A (σ j) j) else 0) := by
    by_cases hp : π = 1
    · subst π
      simp [hσ.symm]
    by_cases hp' : π = σ
    · subst π
      simp [hσ]
    simp only [hp, hp', ite_false, zero_add]
    suffices hz : (∏ j, A (π j) j) = 0 by simp [hz]
    by_contra hz
    have hs : ∀ j, π j = j ∨ π j = σ j := by
      intro j
      by_contra h
      push_neg at h
      exact hz (Finset.prod_eq_zero (Finset.mem_univ j) (hA (π j) j h.1 h.2))
    exact hp' (one_way_permutation σ π hc hn hs hp)
  calc
    A.det = ∑ π : Perm ι,
        ((if π = 1 then (∏ j, A j j) else 0) +
        (if π = σ then ((Perm.sign σ : ℤ) : ℝ) *
          (∏ j, A (σ j) j) else 0)) := by
      rw [Matrix.det_apply']
      exact Finset.sum_congr rfl (fun π _ => hterm π)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp

def cyclicBidiagonal (σ : Perm ι) (a b : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then a j else if i = σ j then -b j else 0

theorem cycle_sign (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a : ι) :
    ((Perm.sign σ : ℤ) : ℝ) = -(-1 : ℝ) ^ Fintype.card ι := by
  have hcycle : σ.IsCycle := by
    refine ⟨a, cycle_no_fixed σ hc hn a, ?_⟩
    intro b _
    exact hc.2 (Finset.mem_univ a) (Finset.mem_univ b)
  have hs : σ.support = Finset.univ := by
    ext i
    simp [Perm.mem_support, cycle_no_fixed σ hc hn i]
  have hh := hcycle.sign
  rw [hs, Finset.card_univ] at hh
  have hh' := congrArg (fun x : ℤˣ => ((x : ℤ) : ℝ)) hh
  simpa using hh'

theorem cyclicBidiagonal_det (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ) (i : ι) :
    (cyclicBidiagonal σ a b).det = (∏ j, a j) - ∏ j, b j := by
  have hs : ∀ k j, k ≠ j → k ≠ σ j → cyclicBidiagonal σ a b k j = 0 := by
    intro k j hk hkj
    simp [cyclicBidiagonal, hk, hkj]
  rw [cyclic_bidiagonal_determinant (cyclicBidiagonal σ a b) σ hc hn hs i]
  simp only [cyclicBidiagonal, ite_true, cycle_no_fixed σ hc hn, ite_false]
  rw [cycle_sign σ hc hn i, Finset.prod_neg]
  have hh : (-1 : ℝ) ^ Fintype.card ι * (-1) ^ Fintype.card ι = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [Finset.card_univ]
  rw [neg_mul, ← mul_assoc, hh, one_mul]
  rfl

theorem cyclic_gram_posDef (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ) (i : ι)
    (hab : (∏ j, a j) ≠ ∏ j, b j) :
    ((cyclicBidiagonal σ a b).transpose * cyclicBidiagonal σ a b).PosDef := by
  have hdet : (cyclicBidiagonal σ a b).det ≠ 0 := by
    rw [cyclicBidiagonal_det σ hc hn a b i]
    exact sub_ne_zero.mpr hab
  have hu : IsUnit (cyclicBidiagonal σ a b) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hi : Function.Injective (cyclicBidiagonal σ a b).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hp := (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).conjTranspose_mul_mul_same hi
  simpa using hp

#print axioms unpaired_forward_forces_cycle
#print axioms counted_edge_paired
#print axioms cyclic_determinant_tilt
#print axioms cyclic_gram_posDef

end

end UnicyclicDeterminant
