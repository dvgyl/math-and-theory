import FourierAlgebra
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Zero averages of the explicit Fourier-cycle vertices

Cyclic summation of the second-order wave recurrence proves the zero primal
average without a complex geometric-series argument.  The dual average is a
telescoping finite cyclic sum.  These facts provide the origin saddle point for
the actual compact polytopal construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace AsymptoticCP

open FiniteCP

theorem nextIndex_eq_finRotate {n : ℕ} [NeZero n] (i : Fin n) :
    nextIndex i = finRotate n i := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n =>
    rw [finRotate_succ_apply]
    apply Fin.ext
    simp [nextIndex, Fin.add_def, Nat.add_mod]

theorem sum_nextIndex {n : ℕ} [NeZero n] {V : Type*} [AddCommMonoid V]
    (f : Fin n → V) : (∑ i, f (nextIndex i)) = ∑ i, f i := by
  simpa only [nextIndex_eq_finRotate] using Equiv.sum_comp (finRotate n) f

theorem sum_periodic_shift {n : ℕ} [NeZero n] (f : ℕ → ℝ)
    (hf : Function.Periodic f n) :
    (∑ i : Fin n, f (i.val + 1)) = ∑ i : Fin n, f i.val := by
  calc
    (∑ i : Fin n, f (i.val + 1)) = ∑ i : Fin n, f (nextIndex i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hf.map_mod_nat (i.val + 1)).symm
    _ = ∑ i : Fin n, f i.val := sum_nextIndex (fun i => f i.val)

theorem sum_periodic_recurrence_zero {n : ℕ} [NeZero n] (f : ℕ → ℝ)
    (c : ℝ) (hc : c ≠ 2) (hf : Function.Periodic f n)
    (hrec : ∀ m : ℕ, f m + f (m + 2) = c * f (m + 1)) :
    (∑ i : Fin n, f i.val) = 0 := by
  have hs1 := sum_periodic_shift f hf
  have hf1 : Function.Periodic (fun m : ℕ => f (m + 1)) n := by
    intro m
    simpa only [Nat.add_assoc, Nat.add_comm n 1] using hf (m + 1)
  have hs2 : (∑ i : Fin n, f (i.val + 2)) = ∑ i : Fin n, f i.val := by
    calc
      (∑ i : Fin n, f (i.val + 2)) = ∑ i : Fin n, f (i.val + 1) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using
          sum_periodic_shift (fun m => f (m + 1)) hf1
      _ = ∑ i : Fin n, f i.val := hs1
  have he : (∑ i : Fin n, (f i.val + f (i.val + 2))) =
      ∑ i : Fin n, c * f (i.val + 1) := by
    exact Finset.sum_congr rfl (fun i hi => hrec i.val)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs1, hs2] at he
  have hprod : (2 - c) * (∑ i : Fin n, f i.val) = 0 := by linarith
  rcases mul_eq_zero.mp hprod with hz | hz
  · exact False.elim (hc (by linarith))
  · exact hz

theorem wave_coordinate_recurrence (a b φ ψ r : ℝ) (j : Fin 4) :
    (wave a b φ ψ r) j + (wave a b φ ψ (r + 2)) j =
      (if j.val < 2 then 2 * Real.cos φ else 2 * Real.cos ψ) *
        (wave a b φ ψ (r + 1)) j := by
  have h := congrArg (fun z : E => z j) (wave_recurrence a b φ ψ r)
  fin_cases j <;> norm_num [wave, Matrix.cons_val_succ] at h ⊢ <;> nlinarith only [h]

theorem sum_euclidean_apply {ι : Type*} [Fintype ι] {d : ℕ}
    (f : ι → Space d) (j : Fin d) : (∑ i, f i) j = ∑ i, (f i) j := by
  classical
  have h (s : Finset ι) : (∑ i ∈ s, f i) j = ∑ i ∈ s, (f i) j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp only [Finset.sum_insert ha, PiLp.add_apply, ih]
  exact h Finset.univ

/-- Every primal Fourier vertex family has zero average; the spectral condition
on the step size is not needed for this geometric fact. -/
theorem primalPoints_sum_zero (N : ℕ) (κ : ℝ) (hN : 1 ≤ N) :
    (∑ i : Fin (period N), primalPoints N κ i) = 0 := by
  have hφ : 2 * Real.cos (mode1Angle N) ≠ 2 := by
    have h := spectralD1_pos N hN
    unfold spectralD1 at h
    linarith
  have hψ : 2 * Real.cos (mode2Angle N) ≠ 2 := by
    have h := spectralD2_pos N
    unfold spectralD2 at h
    linarith
  ext j
  rw [sum_euclidean_apply]
  change (∑ i : Fin (period N), (rawPrimal N κ i.val) j) = 0
  let c := if j.val < 2 then 2 * Real.cos (mode1Angle N) else 2 * Real.cos (mode2Angle N)
  have hc : c ≠ 2 := by dsimp [c]; split_ifs <;> assumption
  have hp : Function.Periodic (fun m : ℕ => (rawPrimal N κ m) j) (period N) := by
    intro m
    exact congrArg (fun z : E => z j) (rawPrimal_periodic N κ m)
  apply sum_periodic_recurrence_zero (fun m => (rawPrimal N κ m) j) c hc hp
  intro m
  simpa only [rawPrimal, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, c] using
    wave_coordinate_recurrence (Real.sqrt (weight1 N κ)) (Real.sqrt (weight2 N κ))
      (mode1Angle N) (mode2Angle N) (m : ℝ) j

/-- The dual vertices are consecutive primal differences, so their sum is zero
for every member of the family, without any step-size assumptions. -/
theorem dualPoints_sum_zero (N : ℕ) (κ : ℝ) :
    (∑ i : Fin (period N), dualPoints N κ i) = 0 := by
  unfold dualPoints
  rw [Finset.sum_sub_distrib, sum_nextIndex, sub_self]

end AsymptoticCP

#print axioms AsymptoticCP.primalPoints_sum_zero
#print axioms AsymptoticCP.dualPoints_sum_zero
