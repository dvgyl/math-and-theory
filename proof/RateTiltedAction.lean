module
public import PositiveRateMatrices
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-! Component identity for the tilted backward-generator residual. -/

open scoped BigOperators
open Equiv

namespace UnicyclicDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem edgeTilt_eq_single_cycleTilt [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (σ : Perm ι) (a : ι) (q : ℝ) :
    edgeTilt A a (σ a) q = cycleTilt A σ (fun j => if j = a then q else 1) := by
  ext i j
  by_cases hj : j = a
  · subst j
    by_cases hi : i = a
    · subst i
      simp [edgeTilt, cycleTilt]
    · simp [edgeTilt, cycleTilt, hi]
  · by_cases hi : i = a
    · subst i
      simp [edgeTilt, cycleTilt, hj]
    · simp [edgeTilt, cycleTilt, hj, hi]

theorem cycleTilt_ringMatrix (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (d f g q : ι → ℝ) :
    cycleTilt (ringMatrix σ d f g) σ q =
      ringMatrix σ d (fun j => q j * f j) (fun j => (q j)⁻¹ * g j) := by
  ext i j
  by_cases hij : i = j
  · subst i
    simp [cycleTilt, ringMatrix, (cycle_no_fixed σ hc hn j).symm]
  by_cases hf : i = σ j
  · subst i
    simp [cycleTilt, ringMatrix, cycle_no_fixed σ hc hn j,
      (cycle_no_two σ hc hn j).symm]
  by_cases hr : j = σ i
  · subst j
    simp [cycleTilt, ringMatrix, (cycle_no_fixed σ hc hn i).symm,
      (cycle_no_two σ hc hn i).symm]
  · simp [cycleTilt, ringMatrix, hij, hf, hr]

theorem ringMatrix_transpose_mulVec (σ : Perm ι) (d f g r : ι → ℝ) (i : ι) :
    (ringMatrix σ d f g).transpose.mulVec r i =
      d i * r i + f i * r (σ i) + g (σ⁻¹ i) * r (σ⁻¹ i) := by
  have hrev (j : ι) : i = σ j ↔ j = σ⁻¹ i := by
    constructor
    · intro h
      simpa using (congrArg (fun k => σ⁻¹ k) h).symm
    · intro h
      simpa using (congrArg σ h).symm
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, ringMatrix,
    add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, hrev,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem tilted_rate_transpose_mulVec (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (u v r : ι → ℝ) (a i : ι) (lam q : ℝ) :
    (edgeTilt (rateMatrix σ u v lam) a (σ a) q).transpose.mulVec r i =
      (lam + u i + v (σ⁻¹ i)) * r i -
      u i * (if i = a then q else 1) * r (σ i) -
      v (σ⁻¹ i) * (if σ⁻¹ i = a then q⁻¹ else 1) * r (σ⁻¹ i) := by
  rw [edgeTilt_eq_single_cycleTilt]
  unfold rateMatrix
  rw [cycleTilt_ringMatrix σ hc hn, ringMatrix_transpose_mulVec]
  have hinv : (if σ⁻¹ i = a then q else 1)⁻¹ =
      (if σ⁻¹ i = a then q⁻¹ else 1) := by
    split_ifs <;> simp
  rw [hinv]
  ring

theorem tilted_rate_residual (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (u v r : ι → ℝ) (a i : ι) (lam s : ℝ) :
    (edgeTilt (rateMatrix σ u v lam) a (σ a) (Real.exp s)).transpose.mulVec r i =
      lam * r i -
      u i * Real.exp (s * (if i = a then 1 else 0)) * r (σ i) -
      v (σ⁻¹ i) * Real.exp (-s * (if σ⁻¹ i = a then 1 else 0)) * r (σ⁻¹ i) +
      (u i + v (σ⁻¹ i)) * r i := by
  rw [tilted_rate_transpose_mulVec σ hc hn]
  have hf : Real.exp (s * (if i = a then 1 else 0)) =
      (if i = a then Real.exp s else 1) := by
    split_ifs <;> simp
  have hb : Real.exp (-s * (if σ⁻¹ i = a then 1 else 0)) =
      (if σ⁻¹ i = a then (Real.exp s)⁻¹ else 1) := by
    split_ifs <;> simp [Real.exp_neg]
  rw [hf, hb]
  ring

#print axioms tilted_rate_transpose_mulVec
#print axioms tilted_rate_residual

end

end UnicyclicDeterminant
