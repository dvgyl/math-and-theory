module
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Analysis.Real.Sqrt

/-! The theorem classifies nonnegative parameter pairs for actual finite matroids.
The rank-sum definitions agree with Mingchang Liu's Tutte-threshold statement.
Finiteness applies to the ground set. The ambient type can be infinite. -/
@[expose] public section
open Matroid
noncomputable section

namespace Results.TutteThreshold

/-- The natural-number rank of a set. -/
def rk {α : Type*} (M : Matroid α) (S : Set α) : ℕ := (M.eRk S).toNat

/-- The Tutte polynomial is a sum over all subsets of the finite ground set. -/
def tutte {α : Type*} (M : Matroid α) [M.Finite] (x y : ℝ) : ℝ :=
  ∑ S ∈ M.ground_finite.toFinset.powerset,
    (x - 1) ^ (M.eRank.toNat - rk M (S : Set α)) *
      (y - 1) ^ (S.card - rk M (S : Set α))

/-- An admissible matroid has no loops and no coloops. -/
def IsAdmissible {α : Type*} (M : Matroid α) : Prop :=
  (∀ e, ¬ M.IsLoop e) ∧ (∀ e, ¬ M.IsColoop e)

end Results.TutteThreshold

namespace AsymmetricMerinoWelsh
open Results.TutteThreshold

/-- The inequality holds for every finite admissible matroid, including the empty matroid. -/
def Universal (x y : ℝ) : Prop :=
  ∀ (α : Type) (M : Matroid α) [M.Finite], IsAdmissible M →
    (tutte M 1 1) ^ 2 ≤ tutte M x 0 * tutte M 0 y

end AsymmetricMerinoWelsh

namespace AsymmetricTutte

/-- Both scalar families are required for every natural number at least two. -/
def Region (x y : ℝ) : Prop :=
  1 < x ∧ 1 < y ∧
    (∀ k : ℕ, 2 ≤ k → (Real.sqrt (x - 1) + (k : ℝ) * Real.sqrt (y - 1)) ^ 2 ≤
      x * y ^ k) ∧
    (∀ k : ℕ, 2 ≤ k → (Real.sqrt (y - 1) + (k : ℝ) * Real.sqrt (x - 1)) ^ 2 ≤
      y * x ^ k)

end AsymmetricTutte

end
