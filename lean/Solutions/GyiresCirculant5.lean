module

/- Source attribution: MathAndTheory/Mathematics/GyiresCirculant5/PROVENANCE.md. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.MathlibStatements
public import Solutions.GyiresFourBlock
public import Solutions.GyiresExceptional

/-!
# Solution for Gyires's inequality for circulant matrices of order five

Each statement of `Challenges.GyiresCirculant5` is derived from the library `MathAndTheory.GyiresCirculant5`: the
matrix theorems in `MathAndTheory.GyiresCirculant5.Theorems`, the normalized form in `MathAndTheory.GyiresCirculant5.Corollaries` and
`MathAndTheory.GyiresCirculant5.Normalization`, and the translation to Mathlib's `Matrix.circulant` together with the
margin and its sharpness in `MathAndTheory.GyiresCirculant5.MathlibStatements`.
-/

public section

namespace MathAndTheory.GyiresCirculant5

open Matrix MathAndTheory.GyiresCirculant5

private theorem factorial_ratio : (Nat.factorial 5 : ℝ) / 5 ^ 5 = 24 / 625 := by
  norm_num [Nat.factorial]

theorem gyires_ratio (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 5))
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 ≤
      4 * A.permanent ^ 2 /
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) := by
  obtain ⟨v, rfl⟩ := hcirc
  obtain ⟨hv, hsum⟩ := weights_of_doublyStochastic v hA
  rw [factorial_ratio, gyiresDenominator_circulant, permanent_circulant, ← permanent_circ]
  exact normalizedGyiresRatio v hv hsum

theorem gyires_ratio_eq_iff (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 5)) (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    4 * A.permanent ^ 2 /
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) =
      (Nat.factorial 5 : ℝ) / 5 ^ 5 ↔
      A = of fun _ _ => (5 : ℝ)⁻¹ := by
  obtain ⟨v, rfl⟩ := hcirc
  obtain ⟨hv, hsum⟩ := weights_of_doublyStochastic v hA
  rw [factorial_ratio, gyiresDenominator_circulant, permanent_circulant, ← permanent_circ,
    normalizedGyiresRatio_eq_iff v hv hsum, circulant_eq_const_iff]
  norm_num

theorem gyires_denominator_pos (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 5)) (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    0 < (A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent := by
  obtain ⟨v, rfl⟩ := hcirc
  obtain ⟨hv, hsum⟩ := weights_of_doublyStochastic v hA
  rw [gyiresDenominator_circulant]
  exact positiveDenominator v hv hsum

theorem gyires_homogeneous (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 *
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) ≤
      4 * A.permanent ^ 2 := by
  obtain ⟨v, rfl⟩ := hcirc
  have hv := weights_nonneg_of_entries v hA
  have h := gyires_matrix_inequality v hv
  rw [factorial_ratio, gyiresDenominator_circulant, permanent_circulant, ← permanent_circ]
  change 24 * gyiresDenominator v ≤ 2500 * (circ v).permanent ^ 2 at h
  linarith

theorem gyires_homogeneous_eq_iff (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 *
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) =
      4 * A.permanent ^ 2 ↔
      ∃ c : ℝ, A = of fun _ _ => c := by
  obtain ⟨v, rfl⟩ := hcirc
  have hv := weights_nonneg_of_entries v hA
  have h := gyires_matrix_equality_iff v hv
  change 24 * gyiresDenominator v = 2500 * (circ v).permanent ^ 2 ↔ _ at h
  rw [factorial_ratio, gyiresDenominator_circulant, permanent_circulant, ← permanent_circ]
  simp only [circulant_eq_const_iff]
  rw [← h]
  constructor <;> intro h' <;> linarith

theorem strong_inequality (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 * (A * Aᵀ).permanent ≤ A.permanent ^ 2 := by
  obtain ⟨v, rfl⟩ := hcirc
  have h := strong_matrix_inequality v (weights_nonneg_of_entries v hA)
  rw [circ_mul_transpose, permanent_circ, permanent_circ] at h
  rw [factorial_ratio, permanent_circulant_mul_transpose, permanent_circulant]
  linarith

theorem strong_inequality_eq_iff (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 * (A * Aᵀ).permanent = A.permanent ^ 2 ↔
      ∃ c : ℝ, A = of fun _ _ => c := by
  obtain ⟨v, rfl⟩ := hcirc
  have h := strong_matrix_equality_iff v (weights_nonneg_of_entries v hA)
  rw [circ_mul_transpose, permanent_circ, permanent_circ] at h
  rw [factorial_ratio, permanent_circulant_mul_transpose, permanent_circulant]
  simp only [circulant_eq_const_iff]
  rw [← h]
  constructor <;> intro h' <;> linarith

theorem strong_margin (v : Fin 5 → ℝ) (hv : ∀ i, 0 ≤ v i) (σ : Equiv.Perm (Fin 5))
    (hσ : Monotone (v ∘ σ)) :
    484 * ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 ≤
      625 * (circulant v).permanent ^ 2 - 24 * (circulant v * (circulant v)ᵀ).permanent := by
  rw [permanent_circulant, permanent_circulant_mul_transpose]
  exact strongDefect_margin v hv σ hσ

theorem strong_margin_attained :
    ∃ v : Fin 5 → ℝ, (∀ i, 0 ≤ v i) ∧ ∃ σ : Equiv.Perm (Fin 5), Monotone (v ∘ σ) ∧
      ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 = 1 ∧
      625 * (circulant v).permanent ^ 2 - 24 * (circulant v * (circulant v)ᵀ).permanent = 484 := by
  obtain ⟨v, hv, σ, hσ, hsum, hdef⟩ := strongDefect_margin_attained
  refine ⟨v, hv, σ, hσ, hsum, ?_⟩
  rw [permanent_circulant, permanent_circulant_mul_transpose]
  exact hdef

theorem strong_margin_sharp (K : ℝ)
    (hK : ∀ v : Fin 5 → ℝ, (∀ i, 0 ≤ v i) → ∀ σ : Equiv.Perm (Fin 5), Monotone (v ∘ σ) →
      K * ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 ≤
        625 * (circulant v).permanent ^ 2 - 24 * (circulant v * (circulant v)ᵀ).permanent) :
    K ≤ 484 := by
  apply strongDefect_margin_sharp K
  intro v hv σ hσ
  have h := hK v hv σ hσ
  rwa [permanent_circulant, permanent_circulant_mul_transpose] at h

end MathAndTheory.GyiresCirculant5
