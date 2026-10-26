module
public import MathAndTheory.Mathematics.QPermanent.Definitions
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
Exact finite counterexample to real extended q-permanent monotonicity.
All computations below are intended for kernel checking; no native_decide,
external oracle, or assumed polynomial identity is used.
-/

namespace MathAndTheory.QPermanent

open scoped BigOperators Matrix

def counterexampleInt : Matrix (Fin 5) (Fin 5) ℤ :=
  !![5, 0, 0, 4, 1;
     0, 5, 0, -1, 4;
     0, 0, 1, 0, 0;
     4, -1, 0, 5, 0;
     1, 4, 0, 0, 5]

def counterexampleReal : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (counterexampleInt i j : ℝ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem counterexample_q14_int :
    qPermanent counterexampleInt (14 : ℤ) = 8968822249 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem counterexample_q15_int :
    qPermanent counterexampleInt (15 : ℤ) = 7441960000 := by
  decide

theorem counterexample_q14 :
    qPermanent counterexampleReal (14 : ℝ) = 8968822249 := by
  have h := congrArg (Int.castRingHom ℝ) counterexample_q14_int
  rw [map_qPermanent] at h
  change qPermanent counterexampleReal ((14 : ℤ) : ℝ) = ((8968822249 : ℤ) : ℝ) at h
  norm_num only [Int.cast_ofNat] at h
  exact h

theorem counterexample_q15 :
    qPermanent counterexampleReal (15 : ℝ) = 7441960000 := by
  have h := congrArg (Int.castRingHom ℝ) counterexample_q15_int
  rw [map_qPermanent] at h
  change qPermanent counterexampleReal ((15 : ℤ) : ℝ) = ((7441960000 : ℤ) : ℝ) at h
  norm_num only [Int.cast_ofNat] at h
  exact h

theorem counterexample_decreases :
    qPermanent counterexampleReal (15 : ℝ) <
      qPermanent counterexampleReal (14 : ℝ) := by
  rw [counterexample_q14, counterexample_q15]
  norm_num

theorem counterexample_isHermitian : counterexampleReal.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [counterexampleReal, counterexampleInt, Matrix.conjTranspose_apply]

/-- An exact positive sum-of-squares identity for the quadratic form. -/
theorem counterexample_quadratic (x : Fin 5 → ℝ) :
    star x ⬝ᵥ (counterexampleReal *ᵥ x) =
      5 * (x 0 + (4 : ℝ) / 5 * x 3 + (1 : ℝ) / 5 * x 4) ^ 2 +
      5 * (x 1 - (1 : ℝ) / 5 * x 3 + (4 : ℝ) / 5 * x 4) ^ 2 +
      (x 2) ^ 2 + (8 : ℝ) / 5 * (x 3) ^ 2 + (8 : ℝ) / 5 * (x 4) ^ 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    counterexampleReal, counterexampleInt]
  ring

/-- The usual mathlib positive-definiteness predicate, with no assumed eigenvalues. -/
theorem counterexample_posDef : counterexampleReal.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos counterexample_isHermitian
  intro x hx
  rw [counterexample_quadratic]
  have h0 := sq_nonneg (x 0 + (4 : ℝ) / 5 * x 3 + (1 : ℝ) / 5 * x 4)
  have h1 := sq_nonneg (x 1 - (1 : ℝ) / 5 * x 3 + (4 : ℝ) / 5 * x 4)
  have h2 := sq_nonneg (x 2)
  have h3 := sq_nonneg (x 3)
  have h4 := sq_nonneg (x 4)
  by_contra! h
  have hz2 : x 2 = 0 := by nlinarith
  have hz3 : x 3 = 0 := by nlinarith
  have hz4 : x 4 = 0 := by nlinarith
  have hz0 : x 0 = 0 := by simp only [hz2, hz3, hz4] at h; nlinarith [sq_nonneg (x 1)]
  have hz1 : x 1 = 0 := by simp only [hz0, hz2, hz3, hz4] at h; nlinarith
  apply hx
  funext i
  fin_cases i <;> simp_all

/-- A strictly positive-definite real matrix violates monotonicity above 1. -/
theorem exists_posDef_counterexample :
    ∃ A : Matrix (Fin 5) (Fin 5) ℝ,
      A.PosDef ∧ qPermanent A (15 : ℝ) < qPermanent A (14 : ℝ) :=
  ⟨counterexampleReal, counterexample_posDef, counterexample_decreases⟩

theorem counterexample_not_monotoneOn :
    ¬ MonotoneOn (qPermanent counterexampleReal) (Set.Ici (1 : ℝ)) := by
  intro h
  have hle := h (by norm_num : (14 : ℝ) ∈ Set.Ici 1)
    (by norm_num : (15 : ℝ) ∈ Set.Ici 1) (by norm_num : (14 : ℝ) ≤ 15)
  exact (not_le_of_gt counterexample_decreases) hle

theorem counterexample_has_nonzero_offDiagonal :
    ∃ i j : Fin 5, i ≠ j ∧ counterexampleReal i j ≠ 0 := by
  refine ⟨0, 3, by decide, ?_⟩
  norm_num [counterexampleReal, counterexampleInt]

/-- This directly refutes either version of the proposed left endpoint. -/
theorem counterexample_not_strictMonoOn_halfline (ε : ℝ) (hε : ε ≤ 1) :
    ¬ StrictMonoOn (qPermanent counterexampleReal) (Set.Ioi ε) := by
  intro h
  have h₁ : (14 : ℝ) ∈ Set.Ioi ε := by change ε < 14; linarith
  have h₂ : (15 : ℝ) ∈ Set.Ioi ε := by change ε < 15; linarith
  exact (lt_asymm (h h₁ h₂ (by norm_num))) counterexample_decreases

/-- The universal real positive-definite extension is false. -/
theorem not_universal_extended_monotonicity :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → MonotoneOn (qPermanent A) (Set.Ici (1 : ℝ))) := by
  intro h
  exact counterexample_not_monotoneOn (h 5 counterexampleReal counterexample_posDef)

/-- The published extension is false even with the non-diagonal restriction
included explicitly, rather than relying on a diagonal constant polynomial. -/
theorem not_daFonseca_extended_conjecture :
    ¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef → (∃ i j, i ≠ j ∧ A i j ≠ 0) →
      ∃ ε : ℝ, ε ≤ -1 ∧ StrictMonoOn (qPermanent A) (Set.Ioi ε)) := by
  intro h
  obtain ⟨ε, hε, hmono⟩ := h 5 counterexampleReal counterexample_posDef
    counterexample_has_nonzero_offDiagonal
  exact counterexample_not_strictMonoOn_halfline ε (by linarith) hmono

end MathAndTheory.QPermanent
