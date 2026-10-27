module

public import MathAndTheory.Mathematics.Gyires.FourBlock

/-!
These statements cover every doubly stochastic square matrix with at most two distinct row
vectors and at most two distinct column vectors. The orders zero and one are included.
The permanent and matrix products are the Mathlib definitions. The normalization is `n!/n^n`.
The hypotheses permit unequal class sizes, an empty chosen class, and zero entries.
-/

@[expose] public section

namespace MathAndTheory.GyiresFourBlock

noncomputable def rowVectorCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ := by
  classical
  exact (Finset.univ.image (fun i => fun j => A i j)).card

noncomputable def columnVectorCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ := by
  classical
  exact (Finset.univ.image (fun j => fun i => A i j)).card

open MathAndTheory.Gyires MathAndTheory.Gyires.Bernoulli

theorem contractions {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      (A.transpose * A).permanent ≤ A.permanent ∧ (A * A).permanent ≤ A.permanent := by
  change (columnTypes A.transpose).card ≤ 2 at hrow
  change (columnTypes A).card ≤ 2 at hcol
  simpa only [dimensionConstant, Fintype.card_fin, MathAndTheory.Gyires.Bernoulli.uniformMatrix] using fourBlock_contractions A hA hrow hcol

theorem margin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    4 * A.permanent * (A.permanent - (Nat.factorial n : ℝ) / (n : ℝ)^n) ≤
      4 * A.permanent^2 - (Nat.factorial n : ℝ) / (n : ℝ)^n *
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ∧
    0 ≤ 4 * A.permanent * (A.permanent - (Nat.factorial n : ℝ) / (n : ℝ)^n) := by
  change (columnTypes A.transpose).card ≤ 2 at hrow
  change (columnTypes A).card ≤ 2 at hcol
  simpa only [dimensionConstant, Fintype.card_fin, MathAndTheory.Gyires.Bernoulli.uniformMatrix] using fourBlock_margin A hA hrow hcol

theorem gyires {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    (Nat.factorial n : ℝ) / (n : ℝ)^n *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
        4 * A.permanent^2 := by
  change (columnTypes A.transpose).card ≤ 2 at hrow
  change (columnTypes A).card ≤ 2 at hcol
  simpa only [dimensionConstant, Fintype.card_fin, MathAndTheory.Gyires.Bernoulli.uniformMatrix] using fourBlock_gyires A hA hrow hcol

theorem gyires_eq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    (Nat.factorial n : ℝ) / (n : ℝ)^n *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
        4 * A.permanent^2 ↔ A = fun _ _ => 1 / (n : ℝ) := by
  change (columnTypes A.transpose).card ≤ 2 at hrow
  change (columnTypes A).card ≤ 2 at hcol
  have hu : (uniformMatrix : Matrix (Fin n) (Fin n) ℝ) = (fun _ _ => 1 / (n : ℝ)) := by
    ext i j
    simp [uniformMatrix]
  simpa only [dimensionConstant, Fintype.card_fin, hu] using fourBlock_gyires_eq_iff A hA hrow hcol

end MathAndTheory.GyiresFourBlock
