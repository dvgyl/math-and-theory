module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Normalization
public import MathAndTheory.Mathematics.GyiresCirculant5.Symmetry
public import MathAndTheory.Mathematics.GyiresCirculant5.Defects
public import MathAndTheory.Mathematics.GyiresCirculant5.MatrixBridge
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The two-point example and the sharpness of `484`

For `w = (t, t, 0, 0, 0)`: `P(w) = 2t⁵`, `P(g(w)) = P(h(w)) = 84 t¹⁰`, and both defects equal
`484 t¹⁰`. For `t = 1/2` the normalized ratio is `1/21`, and `per(C Cᵀ) = 21/256 > per C =
1/16`. `gap_coefficient_optimal` shows that no constant larger than `484` can replace it in the
chamber margin of `Theorems.strong_chambers`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false

namespace MathAndTheory.GyiresCirculant5

open scoped BigOperators

@[simp] private theorem vec5_two (a b c d e : ℝ) :
    (![a, b, c, d, e] : Fin 5 → ℝ) 2 = c := rfl
@[simp] private theorem vec5_three (a b c d e : ℝ) :
    (![a, b, c, d, e] : Fin 5 → ℝ) 3 = d := rfl
@[simp] private theorem vec5_four (a b c d e : ℝ) :
    (![a, b, c, d, e] : Fin 5 → ℝ) 4 = e := rfl
@[simp] private theorem vec5_five (a b c d e : ℝ) :
    (![a, b, c, d, e] : Fin 5 → ℝ) 5 = a := rfl

def twoSupport (t : ℝ) : Fin 5 → ℝ := ![t, t, 0, 0, 0]

theorem P5_twoSupport (t : ℝ) : P5 (twoSupport t) = 2 * t^5 := by
  norm_num [twoSupport, P5]
  ring

private theorem gram_twoSupport (t : ℝ) :
    gram (twoSupport t) = ![2 * t^2, t^2, 0, 0, t^2] := by
  funext i
  fin_cases i <;> norm_num [gram, twoSupport, Fin.sum_univ_succ] <;> ring

private theorem conv_twoSupport (t : ℝ) :
    conv (twoSupport t) = ![t^2, 2 * t^2, t^2, 0, 0] := by
  funext i
  fin_cases i <;> norm_num [conv, twoSupport, Fin.sum_univ_succ] <;> ring

theorem P5_gram_twoSupport (t : ℝ) :
    P5 (gram (twoSupport t)) = 84 * t^10 := by
  rw [gram_twoSupport]
  norm_num [P5]
  ring

theorem P5_conv_twoSupport (t : ℝ) :
    P5 (conv (twoSupport t)) = 84 * t^10 := by
  rw [conv_twoSupport]
  norm_num [P5]
  ring

theorem strongDefect_twoSupport (t : ℝ) :
    strongDefect (twoSupport t) = 484 * t^10 := by
  unfold strongDefect
  rw [P5_twoSupport, P5_gram_twoSupport]
  ring

theorem gyiresDefect_twoSupport (t : ℝ) :
    gyiresDefect (twoSupport t) = 484 * t^10 := by
  unfold gyiresDefect
  rw [P5_twoSupport, P5_gram_twoSupport, P5_conv_twoSupport]
  ring

theorem gyiresDenominator_twoSupport (t : ℝ) :
    gyiresDenominator (twoSupport t) = 336 * t^10 := by
  unfold gyiresDenominator
  rw [circ_mul_transpose, transpose_mul_circ, circ_mul_self]
  simp only [permanent_circ, P5_gram_twoSupport, P5_conv_twoSupport]
  ring

theorem twoSupport_half_nonneg : ∀ i, 0 ≤ twoSupport (1 / 2) i := by
  intro i
  fin_cases i
  · change (0 : ℝ) ≤ 1 / 2
    norm_num
  · change (0 : ℝ) ≤ 1 / 2
    norm_num
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

theorem twoSupport_half_sum : ∑ i, twoSupport (1 / 2) i = 1 := by
  norm_num [twoSupport, Fin.sum_univ_succ]

theorem permanent_twoSupport_half : (circ (twoSupport (1 / 2))).permanent = 1 / 16 := by
  rw [permanent_circ, P5_twoSupport]
  norm_num

theorem permanent_gram_twoSupport_half :
    (circ (twoSupport (1 / 2)) * (circ (twoSupport (1 / 2))).transpose).permanent =
      21 / 256 := by
  rw [circ_mul_transpose, permanent_circ, P5_gram_twoSupport]
  norm_num

theorem permanent_square_twoSupport_half :
    (circ (twoSupport (1 / 2)) * circ (twoSupport (1 / 2))).permanent = 21 / 256 := by
  rw [circ_mul_self, permanent_circ, P5_conv_twoSupport]
  norm_num

theorem normalizedGyiresRatio_twoSupport_half :
    4 * (circ (twoSupport (1 / 2))).permanent^2 /
      gyiresDenominator (twoSupport (1 / 2)) = 1 / 21 := by
  rw [permanent_twoSupport_half, gyiresDenominator_twoSupport]
  norm_num

theorem gap_coefficient_optimal (K : ℝ)
    (h : ∀ k : Fin 6, ∀ z : Fin 5 → ℝ, (∀ i, 0 ≤ z i) →
      K * ((z 1)^10 + (z 2)^10 + (z 3)^10 + (z 4)^10) ≤
        strongDefect (canonicalWeights k z)) : K ≤ 484 := by
  have hz : ∀ i : Fin 5, 0 ≤ (![0, 0, 0, 1, 0] : Fin 5 → ℝ) i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact zero_le_one
    · exact le_rfl
  have hh := h 0 (![0, 0, 0, 1, 0]) hz
  have heq : canonicalWeights 0 (![0, 0, 0, 1, 0]) = twoSupport 1 ∘ affine 0 2 := by
    funext i
    fin_cases i
    · change (0 : ℝ) = 0
      rfl
    · change (0 : ℝ) + 0 = 0
      norm_num
    · change (0 : ℝ) + 0 + 0 = 0
      norm_num
    · change (0 : ℝ) + 0 + 0 + 1 = 1
      norm_num
    · change (0 : ℝ) + 0 + 0 + 1 + 0 = 1
      norm_num
  rw [heq, strongDefect_affine, strongDefect_twoSupport] at hh
  change K * ((0 : ℝ)^10 + 0^10 + 1^10 + 0^10) ≤ 484 * 1^10 at hh
  norm_num at hh
  exact hh

end MathAndTheory.GyiresCirculant5
