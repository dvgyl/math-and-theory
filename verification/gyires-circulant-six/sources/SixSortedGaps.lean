import SixGapMarginGeometry
namespace SixCertificates
open MathAndTheory.Gyires.CirculantCertificate

def orderedGaps (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![w (σ 0), w (σ 1) - w (σ 0), w (σ 2) - w (σ 1),
    w (σ 3) - w (σ 2), w (σ 4) - w (σ 3), w (σ 5) - w (σ 4)]

theorem orderedGaps_nonneg (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) : ∀ i, 0 ≤ orderedGaps σ w i := by
  intro i
  fin_cases i
  · exact hw (σ 0)
  all_goals
    simp only [orderedGaps]
    exact sub_nonneg.mpr (hm (by decide))

theorem gapWeights_orderedGaps (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ) :
    gapWeights σ (orderedGaps σ w) = w := by
  have hp : prefixVector (fun i => i) (orderedGaps σ w) = w ∘ σ := by
    funext i
    fin_cases i <;> norm_num [prefixVector, orderedGaps, Function.comp_def]
  rw [prefix_identity] at hp
  funext i
  have hi := congrFun hp (σ.symm i)
  simpa [gapWeights, Function.comp_def] using hi

theorem gapPowerSum_orderedGaps (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ) :
    gapPowerSum (orderedGaps σ w) =
      ∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12 := by
  norm_num [gapPowerSum, orderedGaps, Fin.sum_univ_succ]
  simp only [add_assoc]

#print axioms gapWeights_orderedGaps
end SixCertificates
