module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.MatrixBridge
public import MathAndTheory.Mathematics.GyiresCirculant5.OrderCover
public import MathAndTheory.Mathematics.GyiresCirculant5.Symmetry
public import MathAndTheory.Mathematics.GyiresCirculant5.PermanentGram
public import MathAndTheory.Mathematics.GyiresCirculant5.Strong0
public import MathAndTheory.Mathematics.GyiresCirculant5.Strong1
public import MathAndTheory.Mathematics.GyiresCirculant5.Strong2
public import MathAndTheory.Mathematics.GyiresCirculant5.Strong3
public import MathAndTheory.Mathematics.GyiresCirculant5.Strong4
public import MathAndTheory.Mathematics.GyiresCirculant5.Strong5
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The main inequalities

`strong_chambers` collects the six chamber certificates: in sorted-gap coordinates the defect is
at least `484 (z₁¹⁰ + z₂¹⁰ + z₃¹⁰ + z₄¹⁰)`. With the affine symmetry and the chamber cover this
gives the strong inequality `24 per(C Cᵀ) ≤ 625 per(C)²` (`strong_matrix_inequality`), Gyires's
homogeneous inequality (`gyires_matrix_inequality`), and both equality cases: equality holds
exactly when all five weights are equal.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MathAndTheory.GyiresCirculant5

open scoped BigOperators

private theorem all_six {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ k, P k := by
  intro k
  fin_cases k <;> assumption

private theorem canonicalWeights_eq_0 (z : Fin 5 → ℝ) :
    canonicalWeights 0 z =
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2,
        z 0 + z 1 + z 2 + z 3, z 0 + z 1 + z 2 + z 3 + z 4] := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalWeights_eq_1 (z : Fin 5 → ℝ) :
    canonicalWeights 1 z =
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2,
        z 0 + z 1 + z 2 + z 3 + z 4, z 0 + z 1 + z 2 + z 3] := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalWeights_eq_2 (z : Fin 5 → ℝ) :
    canonicalWeights 2 z =
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2 + z 3,
        z 0 + z 1 + z 2, z 0 + z 1 + z 2 + z 3 + z 4] := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalWeights_eq_3 (z : Fin 5 → ℝ) :
    canonicalWeights 3 z =
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2 + z 3 + z 4,
        z 0 + z 1 + z 2, z 0 + z 1 + z 2 + z 3] := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalWeights_eq_4 (z : Fin 5 → ℝ) :
    canonicalWeights 4 z =
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2 + z 3,
        z 0 + z 1 + z 2 + z 3 + z 4, z 0 + z 1 + z 2] := by
  funext i
  fin_cases i <;> rfl

private theorem canonicalWeights_eq_5 (z : Fin 5 → ℝ) :
    canonicalWeights 5 z =
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2 + z 3 + z 4,
        z 0 + z 1 + z 2 + z 3, z 0 + z 1 + z 2] := by
  funext i
  fin_cases i <;> rfl

theorem strong_chambers (k : Fin 6) (z : Fin 5 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    484 * ((z 1)^10 + (z 2)^10 + (z 3)^10 + (z 4)^10) ≤
      strongDefect (canonicalWeights k z) := by
  revert k
  apply all_six
  · rw [canonicalWeights_eq_0]
    exact strong_chamber_0 (z 0) (z 1) (z 2) (z 3) (z 4)
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  · rw [canonicalWeights_eq_1]
    exact strong_chamber_1 (z 0) (z 1) (z 2) (z 3) (z 4)
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  · rw [canonicalWeights_eq_2]
    exact strong_chamber_2 (z 0) (z 1) (z 2) (z 3) (z 4)
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  · rw [canonicalWeights_eq_3]
    exact strong_chamber_3 (z 0) (z 1) (z 2) (z 3) (z 4)
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  · rw [canonicalWeights_eq_4]
    exact strong_chamber_4 (z 0) (z 1) (z 2) (z 3) (z 4)
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  · rw [canonicalWeights_eq_5]
    exact strong_chamber_5 (z 0) (z 1) (z 2) (z 3) (z 4)
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)

private theorem strongDefect_le_gyiresDefect (w : Fin 5 → ℝ) :
    strongDefect w ≤ gyiresDefect w := by
  have h := conv_permanent_le_gram w
  unfold strongDefect gyiresDefect
  linarith

theorem gyires_chambers (k : Fin 6) (z : Fin 5 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    484 * ((z 1)^10 + (z 2)^10 + (z 3)^10 + (z 4)^10) ≤
      gyiresDefect (canonicalWeights k z) :=
  (strong_chambers k z hz).trans (strongDefect_le_gyiresDefect _)

theorem strongDefect_nonneg (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ strongDefect w := by
  apply nonneg_of_canonical_chambers strongDefect strongDefect_affine ?_ w hw
  intro k z hz
  have hm := strong_chambers k z hz
  have hs : 0 ≤ 484 * ((z 1)^10 + (z 2)^10 + (z 3)^10 + (z 4)^10) := by
    positivity
  exact hs.trans hm

theorem gyiresDefect_nonneg (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ gyiresDefect w :=
  (strongDefect_nonneg w hw).trans (strongDefect_le_gyiresDefect w)

private theorem zero_of_tenth_le_zero (x : ℝ) (hx : 0 ≤ x) (hp : x^10 ≤ 0) :
    x = 0 := by
  by_contra hn
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hn)
  have hpow : 0 < x^10 := pow_pos hpos 10
  linarith

private theorem tail_zero_of_margin (z : Fin 5 → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hm : 484 * ((z 1)^10 + (z 2)^10 + (z 3)^10 + (z 4)^10) ≤ 0) :
    ∀ i : Fin 5, i ≠ 0 → z i = 0 := by
  have hp1 := pow_nonneg (hz 1) 10
  have hp2 := pow_nonneg (hz 2) 10
  have hp3 := pow_nonneg (hz 3) 10
  have hp4 := pow_nonneg (hz 4) 10
  have h1 : z 1 = 0 := zero_of_tenth_le_zero _ (hz 1) (by linarith)
  have h2 : z 2 = 0 := zero_of_tenth_le_zero _ (hz 2) (by linarith)
  have h3 : z 3 = 0 := zero_of_tenth_le_zero _ (hz 3) (by linarith)
  have h4 : z 4 = 0 := zero_of_tenth_le_zero _ (hz 4) (by linarith)
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact h1
  · exact h2
  · exact h3
  · exact h4

private theorem strongDefect_constant (c : ℝ) :
    strongDefect (fun _ : Fin 5 => c) = 0 := by
  norm_num [strongDefect, P5, gram, Fin.sum_univ_succ]
  ring

private theorem gyiresDefect_constant (c : ℝ) :
    gyiresDefect (fun _ : Fin 5 => c) = 0 := by
  norm_num [gyiresDefect, P5, gram, conv, Fin.sum_univ_succ]
  ring

theorem strongDefect_eq_zero_iff (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    strongDefect w = 0 ↔ ∃ c : ℝ, ∀ i, w i = c := by
  constructor
  · intro hzero
    apply constant_of_zero_of_canonical_chambers
      strongDefect strongDefect_affine ?_ w hw hzero
    intro k z hz hcz
    apply tail_zero_of_margin z hz
    have h := strong_chambers k z hz
    rw [hcz] at h
    exact h
  · rintro ⟨c, hc⟩
    have heq : w = fun _ => c := funext hc
    rw [heq]
    exact strongDefect_constant c

theorem gyiresDefect_eq_zero_iff (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    gyiresDefect w = 0 ↔ ∃ c : ℝ, ∀ i, w i = c := by
  constructor
  · intro hzero
    have hs := strongDefect_nonneg w hw
    have hsg := strongDefect_le_gyiresDefect w
    apply (strongDefect_eq_zero_iff w hw).mp
    linarith
  · rintro ⟨c, hc⟩
    have heq : w = fun _ => c := funext hc
    rw [heq]
    exact gyiresDefect_constant c

theorem strong_matrix_inequality (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    24 * (circ w * (circ w).transpose).permanent ≤ 625 * (circ w).permanent^2 := by
  rw [circ_mul_transpose, permanent_circ, permanent_circ]
  have h := strongDefect_nonneg w hw
  unfold strongDefect at h
  linarith

theorem gyires_matrix_inequality (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    24 * ((circ w * (circ w).transpose).permanent +
      ((circ w).transpose * circ w).permanent + 2 * (circ w * circ w).permanent) ≤
      2500 * (circ w).permanent^2 := by
  rw [circ_mul_transpose, transpose_mul_circ, circ_mul_self]
  simp only [permanent_circ]
  have h := gyiresDefect_nonneg w hw
  unfold gyiresDefect at h
  linarith

theorem strong_matrix_equality_iff (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    24 * (circ w * (circ w).transpose).permanent = 625 * (circ w).permanent^2 ↔
      ∃ c : ℝ, ∀ i, w i = c := by
  calc
    _ ↔ strongDefect w = 0 := by
      rw [circ_mul_transpose, permanent_circ, permanent_circ]
      unfold strongDefect
      constructor <;> intro h <;> linarith
    _ ↔ _ := strongDefect_eq_zero_iff w hw

theorem gyires_matrix_equality_iff (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    24 * ((circ w * (circ w).transpose).permanent +
      ((circ w).transpose * circ w).permanent + 2 * (circ w * circ w).permanent) =
      2500 * (circ w).permanent^2 ↔ ∃ c : ℝ, ∀ i, w i = c := by
  calc
    _ ↔ gyiresDefect w = 0 := by
      rw [circ_mul_transpose, transpose_mul_circ, circ_mul_self]
      simp only [permanent_circ]
      unfold gyiresDefect
      constructor <;> intro h <;> linarith
    _ ↔ _ := gyiresDefect_eq_zero_iff w hw

theorem normalized_equality_weights (w : Fin 5 → ℝ) (hsum : ∑ i, w i = 1) :
    (∃ c : ℝ, ∀ i, w i = c) ↔ ∀ i, w i = 1 / 5 := by
  constructor
  · rintro ⟨c, hc⟩
    have hs := hsum
    simp_rw [hc] at hs
    norm_num at hs
    have hcval : c = 1 / 5 := by linarith
    intro i
    rw [hc, hcval]
  · intro h
    exact ⟨1 / 5, h⟩

end MathAndTheory.GyiresCirculant5
