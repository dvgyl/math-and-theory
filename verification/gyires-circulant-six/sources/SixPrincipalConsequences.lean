import SixPrincipalBridge
import SixEqualityLemmas
import SixSharpness
import SixSortedGaps
namespace MathAndTheory.Gyires.CirculantSix
open MathAndTheory.Gyires.CirculantCertificate
open SixCertificates

theorem sorted_margin_of_chamber_margins (hch : ChamberMargins) (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) :
    296 * (∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12) ≤
      324 * (matrix w).permanent ^ 2 -
        5 * (matrix w * (matrix w).transpose).permanent := by
  have h := strong_margin_of_chamber_margins hch σ (orderedGaps σ w)
    (orderedGaps_nonneg σ w hw hm)
  rwa [gapWeights_orderedGaps, gapPowerSum_orderedGaps] at h

theorem strong_equality_of_chamber_margins (hch : ChamberMargins) (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * (matrix w * (matrix w).transpose).permanent = 324 * (matrix w).permanent ^ 2 ↔
      ∃ c : ℝ, w = fun _ => c := by
  constructor
  · intro he
    obtain ⟨σ, g, hg, hgw⟩ := exists_gapWeights w hw
    have h := strong_margin_of_chamber_margins hch σ g hg
    rw [hgw] at h
    have hz : gapPowerSum g = 0 := by nlinarith [gapPowerSum_nonneg g]
    refine ⟨g 0, ?_⟩
    rw [← hgw]
    exact gapWeights_constant_of_zero σ g (gaps_zero_of_power_sum_zero g hg hz)
  · rintro ⟨c, rfl⟩
    exact (strong_equality_constant c).symm

theorem gyires_of_chamber_margins (hch : ChamberMargins) (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * ((matrix w * (matrix w).transpose).permanent +
      ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) ≤
      1296 * (matrix w).permanent ^ 2 := by
  have hs := strong_inequality_of_chamber_margins hch w hw
  have hn : matrix w * (matrix w).transpose = (matrix w).transpose * matrix w :=
    circulant_normal w
  have h := MathAndTheory.GyiresCirculant5.gyires_of_strong (matrix w) (5 / 324)
    (by norm_num) (by linarith) (by rw [← hn]; linarith)
  linarith

theorem gyires_equality_of_chamber_margins (hch : ChamberMargins) (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * ((matrix w * (matrix w).transpose).permanent +
      ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) =
      1296 * (matrix w).permanent ^ 2 ↔ ∃ c : ℝ, w = fun _ => c := by
  have hn : matrix w * (matrix w).transpose = (matrix w).transpose * matrix w :=
    circulant_normal w
  constructor
  · intro he
    have hs := strong_inequality_of_chamber_margins hch w hw
    have hp := MathAndTheory.GyiresCirculant5.PermanentGram.permanent_gram_add_ge
      (matrix w) (matrix w).transpose
    rw [Matrix.transpose_transpose, ← hn] at hp
    rw [← hn] at he
    apply (strong_equality_of_chamber_margins hch w hw).mp
    linarith
  · rintro ⟨c, rfl⟩
    have ht : (matrix (fun _ : Fin 6 => c)).transpose = matrix (fun _ : Fin 6 => c) := rfl
    rw [ht]
    have hs := strong_equality_constant c
    change 324 * (matrix (fun _ : Fin 6 => c)).permanent ^ 2 =
      5 * (matrix (fun _ : Fin 6 => c) * (matrix (fun _ : Fin 6 => c)).transpose).permanent at hs
    rw [ht] at hs
    linarith

#print axioms sorted_margin_of_chamber_margins
#print axioms strong_equality_of_chamber_margins
#print axioms gyires_equality_of_chamber_margins
end MathAndTheory.Gyires.CirculantSix
