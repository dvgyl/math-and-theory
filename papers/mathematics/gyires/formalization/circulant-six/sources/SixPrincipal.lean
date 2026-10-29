import SixAllChambers
import SixDoublyStochasticBridge
import SixNormalizedSharpness
import SixGyiresMargin
namespace MathAndTheory.Gyires.CirculantSix
open MathAndTheory.Gyires.CirculantCertificate
open SixCertificates

theorem strong_margin (σ : Equiv.Perm (Fin 6)) (g : Fin 6 → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    296 * gapPowerSum g ≤
      324 * (matrix (gapWeights σ g)).permanent ^ 2 -
        5 * (matrix (gapWeights σ g) * (matrix (gapWeights σ g)).transpose).permanent :=
  strong_margin_of_chamber_margins all_chambers_raw_margin σ g hg

theorem sorted_margin (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) :
    296 * (∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12) ≤
      324 * (matrix w).permanent ^ 2 -
        5 * (matrix w * (matrix w).transpose).permanent :=
  sorted_margin_of_chamber_margins all_chambers_raw_margin σ w hw hm

theorem sorted_gyires_margin (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) :
    1184 * (∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12) ≤
      1296 * (matrix w).permanent ^ 2 -
        5 * ((matrix w * (matrix w).transpose).permanent +
          ((matrix w).transpose * matrix w).permanent +
          2 * (matrix w * matrix w).permanent) :=
  sorted_gyires_margin_of_chamber_margins all_chambers_raw_margin σ w hw hm

theorem strong_inequality (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * (matrix w * (matrix w).transpose).permanent ≤ 324 * (matrix w).permanent ^ 2 :=
  strong_inequality_of_chamber_margins all_chambers_raw_margin w hw

theorem strong_equality (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * (matrix w * (matrix w).transpose).permanent = 324 * (matrix w).permanent ^ 2 ↔
      ∃ c : ℝ, w = fun _ => c :=
  strong_equality_of_chamber_margins all_chambers_raw_margin w hw

theorem gyires (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * ((matrix w * (matrix w).transpose).permanent +
      ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) ≤
      1296 * (matrix w).permanent ^ 2 :=
  gyires_of_chamber_margins all_chambers_raw_margin w hw

theorem gyires_equality (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * ((matrix w * (matrix w).transpose).permanent +
      ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) =
      1296 * (matrix w).permanent ^ 2 ↔ ∃ c : ℝ, w = fun _ => c :=
  gyires_equality_of_chamber_margins all_chambers_raw_margin w hw


theorem gyires_doubly_stochastic (w : Fin 6 → ℝ)
    (hA : matrix w ∈ doublyStochastic ℝ (Fin 6)) :
    (Nat.factorial 6 : ℝ) / 6 ^ 6 *
      ((matrix w * (matrix w).transpose).permanent +
        ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) ≤
      4 * (matrix w).permanent ^ 2 ∧
    ((Nat.factorial 6 : ℝ) / 6 ^ 6 *
      ((matrix w * (matrix w).transpose).permanent +
        ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) =
      4 * (matrix w).permanent ^ 2 ↔
        matrix w = (fun _ _ => 1 / 6 : Matrix (Fin 6) (Fin 6) ℝ)) :=
  gyires_doubly_stochastic_of_chamber_margins all_chambers_raw_margin w hA

#print axioms strong_margin
#print axioms sorted_margin
#print axioms sorted_gyires_margin
#print axioms strong_inequality
#print axioms strong_equality
#print axioms gyires
#print axioms gyires_equality
#print axioms gyires_doubly_stochastic
#print axioms margin_coefficient_le
#print axioms normalized_margin_coefficient_le
end MathAndTheory.Gyires.CirculantSix
