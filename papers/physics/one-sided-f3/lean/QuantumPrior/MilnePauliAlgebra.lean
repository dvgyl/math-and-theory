/- Attributed extraction from the existing user Milne formalization.
   These three theorem statements and proof bodies are unchanged.
   Source files and exact declaration hashes are in PROVENANCE.json. -/
import QuantumPrior.MilneBlochIdentities

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000
noncomputable section
namespace Milne

theorem spin_hermitian (n : V3) : (spin n).IsHermitian := by
  change (spin n)ᴴ = spin n
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, Matrix.conjTranspose_apply, Complex.star_def]
  all_goals ring

theorem spin_squared (n : V3) : spin n * spin n = (vSq n : ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spin,vSq,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

theorem psd_real_smul {n : Type*} [Fintype n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) : ((t:ℂ) • A).PosSemidef := by
  constructor
  · change ((t:ℂ) • A)ᴴ = (t:ℂ) • A
    simp [Matrix.conjTranspose_smul, hA.1.eq]
  · intro v
    simp only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (RCLike.ofReal_nonneg.mpr ht) (hA.2 v)

end Milne
