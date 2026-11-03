import MilneTraceNorm

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
noncomputable section
namespace Milne

theorem hermitianTraceNorm_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    hermitianTraceNorm hA.1 = (Matrix.trace A).re := by
  rw [hermitian_trace_eq_sum_eigenvalues hA.1]
  unfold hermitianTraceNorm
  apply Finset.sum_congr rfl
  intro i hi
  exact abs_of_nonneg (hA.eigenvalues_nonneg i)

theorem matrix_diagonal_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ) (i : n) :
    (Uᴴ*A*U) i i = dotProduct (star (U.transpose i)) (A *ᵥ U.transpose i) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    dotProduct,Matrix.mulVec,Pi.star_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

theorem eigenbasis_sum_expectation {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (P : Matrix n n ℂ) :
    (∑ i, (dotProduct (star (fun j => hA.eigenvectorBasis i j))
      (P *ᵥ (fun j => hA.eigenvectorBasis i j))).re) = (Matrix.trace P).re := by
  let U : Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary
  have hdiag : ∀ i, (dotProduct (star (fun j => hA.eigenvectorBasis i j))
      (P *ᵥ (fun j => hA.eigenvectorBasis i j))).re =
      (((U : Matrix n n ℂ)ᴴ*P*(U : Matrix n n ℂ)) i i).re := by
    intro i
    rw [matrix_diagonal_congruence]
    change _ = (dotProduct (star ((hA.eigenvectorUnitary : Matrix n n ℂ).transpose i))
      (P *ᵥ (hA.eigenvectorUnitary : Matrix n n ℂ).transpose i)).re
    rw [hA.eigenvectorUnitary_transpose_apply]
    rfl
  simp_rw [hdiag]
  rw [← Complex.re_sum]
  change (Matrix.trace ((U : Matrix n n ℂ)ᴴ*P*(U : Matrix n n ℂ))).re = _
  have ht := trace_unitary_conj (star U) P
  simpa [← Matrix.star_eq_conjTranspose] using congrArg Complex.re ht

/-- A spectral order bound for the trace norm. No inverse, positive eigenvalue,
or rank assumption is used. -/
theorem hermitianTraceNorm_le_trace_of_order {n : Type*} [Fintype n] [DecidableEq n]
    {A P : Matrix n n ℂ} (hA : A.IsHermitian)
    (hplus : (P+A).PosSemidef) (hminus : (P-A).PosSemidef) :
    hermitianTraceNorm hA ≤ (Matrix.trace P).re := by
  rw [← eigenbasis_sum_expectation hA P]
  apply Finset.sum_le_sum
  intro i hi
  have hp := hplus.re_dotProduct_nonneg (fun j => hA.eigenvectorBasis i j)
  have hm := hminus.re_dotProduct_nonneg (fun j => hA.eigenvectorBasis i j)
  change 0 ≤ (dotProduct (star (fun j => hA.eigenvectorBasis i j))
    ((P+A) *ᵥ (fun j => hA.eigenvectorBasis i j))).re at hp
  change 0 ≤ (dotProduct (star (fun j => hA.eigenvectorBasis i j))
    ((P-A) *ᵥ (fun j => hA.eigenvectorBasis i j))).re at hm
  rw [Matrix.add_mulVec,dotProduct_add,Complex.add_re] at hp
  rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re] at hm
  have he := hA.eigenvalues_eq i
  change hA.eigenvalues i = (dotProduct (star (fun j => hA.eigenvectorBasis i j))
    (A *ᵥ (fun j => hA.eigenvectorBasis i j))).re at he
  rw [← he] at hp hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Trace distance between two density matrices is at most two, including
all singular states. The convention here is the full trace norm. -/
theorem density_trace_distance_le_two (A B : CMatrix)
    (hA : Density A) (hB : Density B) :
    hermitianTraceNorm (hA.1.1.sub hB.1.1) ≤ 2 := by
  have hp : ((A+B)+(A-B)).PosSemidef := by
    have he : (A+B)+(A-B)=A+A := by abel
    rw [he]
    exact hA.1.add hA.1
  have hm : ((A+B)-(A-B)).PosSemidef := by
    have he : (A+B)-(A-B)=B+B := by abel
    rw [he]
    exact hB.1.add hB.1
  have h := hermitianTraceNorm_le_trace_of_order (hA.1.1.sub hB.1.1) hp hm
  norm_num [Matrix.trace_add,hA.2,hB.2] at h
  exact h

theorem density_trace_distance_sq_le_four (A B : CMatrix)
    (hA : Density A) (hB : Density B) :
    (hermitianTraceNorm (hA.1.1.sub hB.1.1))^2 ≤ 4 := by
  have h := density_trace_distance_le_two A B hA hB
  have hn := hermitianTraceNorm_nonneg (hA.1.1.sub hB.1.1)
  nlinarith

end Milne
