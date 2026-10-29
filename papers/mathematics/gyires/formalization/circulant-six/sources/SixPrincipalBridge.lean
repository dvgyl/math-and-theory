import SixRawDeficitBridge
import SixGapMarginGeometry
import AffineCoverSixComplete
namespace MathAndTheory.Gyires.CirculantSix
open MathAndTheory.Gyires.CirculantCertificate
open SixCertificates
set_option maxHeartbeats 2000000
open MathAndTheory.Gyires.SparsePolynomial

def ChamberMargins : Prop :=
  ∀ (r : Fin 60) (z : Fin 6 → ℝ), (∀ i, 0 ≤ z i) →
    42624 * gapPowerSum z ≤
      eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative r) z)) rawDense


private theorem representative_margin (hch : ChamberMargins) (r : Fin 60) (g : Fin 6 → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    296 * gapPowerSum g ≤
      324 * (circulant (gapWeights (AffineCoverSix.permutation r) g)).permanent ^ 2 -
        5 * (circulant (gapWeights (AffineCoverSix.permutation r) g) *
          (circulant (gapWeights (AffineCoverSix.permutation r) g)).transpose).permanent := by
  let ρ := AffineCoverSix.permutation r
  have h := hch r (g ∘ ρ.symm) (fun i => hg (ρ.symm i))
  change 42624 * gapPowerSum (g ∘ ρ.symm) ≤
    MathAndTheory.Gyires.SparsePolynomial.eval
      (MathAndTheory.Gyires.SparsePolynomial.primeEvaluation primes
        (prefixVector ρ (g ∘ ρ.symm))) rawDense at h
  rw [raw_deficit_eval, prefix_gap, gapPowerSum_permutation ρ (representative_zero r)] at h
  linarith

private def negateIndex : Fin 6 ≃+ Fin 6 where
  toFun := fun i => -i
  invFun := fun i => -i
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := by intro i j; exact neg_add i j

theorem strong_margin_of_chamber_margins (hch : ChamberMargins) (σ : Equiv.Perm (Fin 6)) (g : Fin 6 → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    296 * gapPowerSum g ≤
      324 * (matrix (gapWeights σ g)).permanent ^ 2 -
        5 * (matrix (gapWeights σ g) * (matrix (gapWeights σ g)).transpose).permanent := by
  obtain ⟨r, h | h⟩ := AffineCoverSix.affine_cover σ
  · have hr := representative_margin hch r g hg
    have hw := gap_affine σ (AffineCoverSix.permutation r) (AddEquiv.refl (Fin 6)) (σ 0)
      (fun i => h i) g
    have hi := strong_deficit_affine (AddEquiv.refl (Fin 6)) (σ 0) (gapWeights σ g)
    rw [hw] at hi
    norm_num at hi
    change 296 * gapPowerSum g ≤
      324 * (circulant (gapWeights σ g)).permanent ^ 2 -
        5 * (circulant (gapWeights σ g) * (circulant (gapWeights σ g)).transpose).permanent
    linarith
  · have hr := representative_margin hch r g hg
    have hw := gap_affine σ (AffineCoverSix.permutation r) negateIndex (σ 0)
      (fun i => h i) g
    have hi := strong_deficit_affine negateIndex (σ 0) (gapWeights σ g)
    rw [hw] at hi
    norm_num at hi
    change 296 * gapPowerSum g ≤
      324 * (circulant (gapWeights σ g)).permanent ^ 2 -
        5 * (circulant (gapWeights σ g) * (circulant (gapWeights σ g)).transpose).permanent
    linarith

theorem strong_inequality_of_chamber_margins (hch : ChamberMargins) (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * (matrix w * (matrix w).transpose).permanent ≤ 324 * (matrix w).permanent ^ 2 := by
  obtain ⟨σ, g, hg, heq⟩ := exists_gapWeights w hw
  have h := strong_margin_of_chamber_margins hch σ g hg
  rw [heq] at h
  have hs := gapPowerSum_nonneg g
  linarith

#print axioms strong_margin_of_chamber_margins
#print axioms strong_inequality_of_chamber_margins
end MathAndTheory.Gyires.CirculantSix
