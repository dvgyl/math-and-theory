import QuantumCHSH

/-! Support consequences of positivity for actual complex matrices. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

/-- A positive semidefinite matrix with zero real trace is zero. -/
theorem psd_eq_zero_of_trace_re_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (ht : (Matrix.trace A).re=0) : A=0 := by
  have hsum : ∑ i : ι, (A i i).re=0 := by
    simpa only [Matrix.trace,Matrix.diag,Complex.re_sum] using ht
  have hdiag (i : ι) : A i i=0 := by
    have hr := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j∈Finset.univ) => psd_diag_nonneg hA j)).mp hsum i (Finset.mem_univ i)
    have hi := congrArg Complex.im (hA.1.apply i i)
    apply Complex.ext
    · exact hr
    · simp only [Complex.star_def,Complex.conj_im] at hi
      change (A i i).im=0
      linarith
  ext i j
  have hs : star (Pi.single j (1:ℂ) : ι → ℂ) = (Pi.single j (1:ℂ) : ι → ℂ) := by
    ext k
    by_cases h : k=j <;> simp [Pi.star_apply,Pi.single_apply,h]
  have hq : star (Pi.single j (1:ℂ) : ι → ℂ) ⬝ᵥ A *ᵥ Pi.single j 1=0 := by
    simp [hs,hdiag]
  have hz := (hA.dotProduct_mulVec_zero_iff (Pi.single j 1)).mp hq
  simpa using congrFun hz i

/-- Positivity turns vanishing of a whole sandwich into vanishing of its
right factor against the matrix. -/
theorem psd_mul_zero_of_sandwich_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (B : Matrix ι ι ℂ)
    (hz : Bᴴ*A*B=0) : A*B=0 := by
  have hk (x : ι → ℂ) : A *ᵥ (B *ᵥ x)=0 := by
    apply (hA.dotProduct_mulVec_zero_iff (B *ᵥ x)).mp
    rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hz]
    simp
  apply Matrix.ext_of_mulVec_single
  intro i
  simpa only [←Matrix.mulVec_mulVec,Matrix.zero_mulVec] using hk (Pi.single i 1)

/-- Orthogonality of two positive matrices is equivalent to a zero trace
product.  This is the operator support theorem used at a pure marginal. -/
theorem psd_mul_zero_of_trace_product_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (ht : (Matrix.trace (A*B)).re=0) : A*B=0 := by
  have hs := hA.conjTranspose_mul_mul_same hB.sqrt
  have he : Matrix.trace (hB.sqrtᴴ*A*hB.sqrt)=Matrix.trace (A*B) := by
    rw [hB.posSemidef_sqrt.1.eq,Matrix.trace_mul_cycle,hB.sqrt_mul_self,
      Matrix.trace_mul_comm]
  have hz := psd_eq_zero_of_trace_re_zero hs (by rw [he]; exact ht)
  have hk := psd_mul_zero_of_sandwich_zero hA hB.sqrt hz
  calc
    A*B=A*(hB.sqrt*hB.sqrt) := by rw [hB.sqrt_mul_self]
    _=(A*hB.sqrt)*hB.sqrt := (Matrix.mul_assoc _ _ _).symm
    _=0 := by rw [hk,Matrix.zero_mul]

theorem psd_trace_product_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.trace (A*B)).re=0 ↔ A*B=0 := by
  constructor
  · exact psd_mul_zero_of_trace_product_zero hA hB
  · intro h
    simp [h]

end UnilateralCHSH.Quantum
