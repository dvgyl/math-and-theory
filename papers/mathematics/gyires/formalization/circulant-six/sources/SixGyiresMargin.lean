import SixPrincipalConsequences
namespace MathAndTheory.Gyires.CirculantSix
open MathAndTheory.Gyires.CirculantCertificate
open SixCertificates

theorem gyires_deficit_ge_four_strong (w : Fin 6 → ℝ) :
    4 * (324 * (matrix w).permanent ^ 2 -
      5 * (matrix w * (matrix w).transpose).permanent) ≤
      1296 * (matrix w).permanent ^ 2 -
        5 * ((matrix w * (matrix w).transpose).permanent +
          ((matrix w).transpose * matrix w).permanent +
          2 * (matrix w * matrix w).permanent) := by
  have hn : matrix w * (matrix w).transpose = (matrix w).transpose * matrix w :=
    circulant_normal w
  have hp := MathAndTheory.GyiresCirculant5.PermanentGram.permanent_gram_add_ge
    (matrix w) (matrix w).transpose
  rw [Matrix.transpose_transpose, ← hn] at hp
  rw [← hn]
  linarith

theorem sorted_gyires_margin_of_chamber_margins (hch : ChamberMargins)
    (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) :
    1184 * (∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12) ≤
      1296 * (matrix w).permanent ^ 2 -
        5 * ((matrix w * (matrix w).transpose).permanent +
          ((matrix w).transpose * matrix w).permanent +
          2 * (matrix w * matrix w).permanent) := by
  have hs := sorted_margin_of_chamber_margins hch σ w hw hm
  have hg := gyires_deficit_ge_four_strong w
  linarith

#print axioms gyires_deficit_ge_four_strong
#print axioms sorted_gyires_margin_of_chamber_margins
end MathAndTheory.Gyires.CirculantSix
