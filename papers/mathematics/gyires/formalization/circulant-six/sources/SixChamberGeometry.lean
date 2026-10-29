import SixCertificateBase
import MathAndTheory.Mathematics.Gyires.CirculantCertificate
import Mathlib.Tactic.FinCases
namespace SixCertificates
open MathAndTheory.Gyires.CirculantCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem prefix_comp_permutation (σ : Equiv.Perm (Fin 6)) (z : Fin 6 → ℝ) :
    prefixVector σ z ∘ σ = prefixVector (fun i => i) (z ∘ σ) := by
  funext i
  simp [prefixVector, Function.comp_def, Function.update_apply, σ.injective.eq_iff]

theorem prefix_identity (g : Fin 6 → ℝ) :
    prefixVector (fun i => i) g = gapWeights (Equiv.refl _) g := by
  have h0 : Finset.Iic (0 : Fin 6) = {0} := by decide +kernel
  have h1 : Finset.Iic (1 : Fin 6) = {0, 1} := by decide +kernel
  have h2 : Finset.Iic (2 : Fin 6) = {0, 1, 2} := by decide +kernel
  have h3 : Finset.Iic (3 : Fin 6) = {0, 1, 2, 3} := by decide +kernel
  have h4 : Finset.Iic (4 : Fin 6) = {0, 1, 2, 3, 4} := by decide +kernel
  have h5 : Finset.Iic (5 : Fin 6) = {0, 1, 2, 3, 4, 5} := by decide +kernel
  ext i
  fin_cases i <;> norm_num [prefixVector, gapWeights, h0, h1, h2, h3, h4, h5] <;> ring

theorem prefix_gap (σ : Equiv.Perm (Fin 6)) (g : Fin 6 → ℝ) :
    prefixVector σ (g ∘ σ.symm) = gapWeights σ g := by
  have h := prefix_comp_permutation σ (g ∘ σ.symm)
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, prefix_identity] at h
  funext i
  have hi := congrFun h (σ.symm i)
  simpa [Function.comp_def, gapWeights] using hi

theorem gap_affine (σ ρ : Equiv.Perm (Fin 6)) (e : Fin 6 ≃+ Fin 6) (b : Fin 6)
    (h : ∀ i, σ i = e (ρ i) + b) (g : Fin 6 → ℝ) :
    (fun i => gapWeights σ g (e i + b)) = gapWeights ρ g := by
  funext i
  have hi : σ (ρ.symm i) = e i + b := by rw [h]; simp
  have hinv : σ.symm (e i + b) = ρ.symm i := by rw [← hi]; simp
  simp [gapWeights, hinv]
end SixCertificates
