import MilneGeometryRange
import MilneSingular
import MilneStabilityScalar

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

noncomputable section
namespace Milne

def alignedA (c t : ℝ) : Matrix Q Q ℂ :=
  !![(((1+c+t)/4:ℝ):ℂ), 0; 0, (((1+c-t)/4:ℝ):ℂ)]

def alignedD (c t : ℝ) : Matrix Q Q ℂ :=
  !![(((1-c-t)/4:ℝ):ℂ), 0; 0, (((1-c+t)/4:ℝ):ℂ)]

def alignedC (z w v : ℂ) : Matrix Q Q ℂ := !![z,w;v,-z]

/-- An actual Hermitian four-by-four canonical state in a radial basis.
Positivity is not built into the definition and is imposed explicitly. -/
def alignedState (c t : ℝ) (z w v : ℂ) : CMatrix := fun p q =>
  if p.1 = 0 then
    if q.1 = 0 then alignedA c t p.2 q.2 else alignedC z w v p.2 q.2
  else
    if q.1 = 0 then star (alignedC z w v q.2 p.2) else alignedD c t p.2 q.2

def alignedT (t : ℝ) (z w v : ℂ) : T3 :=
  !![2*(w.re+v.re), 2*(v.im-w.im), 4*z.re;
     -2*(w.im+v.im), 2*(v.re-w.re), -4*z.im;
     0, 0, t]

def rigidityDeficit (c : ℝ) (M : CMatrix) : ℝ :=
  (1-c)*(3-c)-correlationSq M

theorem alignedState_hermitian (c t : ℝ) (z w v : ℂ) :
    (alignedState c t z w v).IsHermitian := by
  change (alignedState c t z w v)ᴴ = alignedState c t z w v
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [alignedState,alignedA,alignedD,alignedC,Matrix.conjTranspose_apply,
      Complex.star_def]

theorem alignedState_bloch (c t : ℝ) (z w v : ℂ) :
    alignedState c t z w v = blochState (c • geometryEz) 0 (alignedT t z w v) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    apply Complex.ext <;>
    simp [alignedState,alignedA,alignedD,alignedC,alignedT,blochState,
      geometryEz,onAlice,onBob,pauli,pauliZ,Pi.smul_apply,smul_eq_mul,
      Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,Complex.star_def,
      Prod.ext_iff]
  all_goals ring

theorem alignedState_density (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    Density (alignedState c t z w v) := by
  refine ⟨hM,?_⟩
  rw [alignedState_bloch,blochState_trace]

theorem alignedState_partialA (c t : ℝ) (z w v : ℂ) :
    partialA (alignedState c t z w v) = qubitState (c • geometryEz) := by
  rw [alignedState_bloch,blochState_partialA]

theorem alignedState_partialB (c t : ℝ) (z w v : ℂ) :
    partialB (alignedState c t z w v) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  rw [alignedState_bloch,blochState_canonical]

theorem alignedT_radial (t : ℝ) (z w v : ℂ) :
    vSq (ttVec (alignedT t z w v) geometryEz) = t^2 := by
  simp [vSq,ttVec,alignedT,geometryEz,Fin.sum_univ_three]

theorem alignedT_squared (t : ℝ) (z w v : ℂ) :
    tSq (alignedT t z w v) =
      t^2+16*Complex.normSq z+8*Complex.normSq w+8*Complex.normSq v := by
  simp [tSq,alignedT,Fin.sum_univ_three,Complex.normSq_apply]
  ring

theorem alignedState_correlationSq (c t : ℝ) (z w v : ℂ) :
    correlationSq (alignedState c t z w v) =
      t^2+16*Complex.normSq z+8*Complex.normSq w+8*Complex.normSq v := by
  rw [alignedState_bloch,blochState_correlationSq,alignedT_squared]

theorem alignedState_radial_range (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) : t ≤ 1-c := by
  have h := psd_diag_nonneg hM ((1,0):QQ)
  simp [alignedState,alignedA,alignedD,alignedC] at h
  linarith

theorem alignedState_geometric_bound (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    correlationSq (alignedState c t z w v) ≤ 1-c^2+2*t^2 := by
  have hP : (blochState (c • geometryEz) 0 (alignedT t z w v)).PosSemidef := by
    rwa [← alignedState_bloch]
  have h := geometry_radial c geometryEz (alignedT t z w v) geometryEz_unit hP
  rw [alignedT_radial] at h
  simpa only [alignedState_bloch,blochState_correlationSq] using h

theorem alignedState_deficit_radial (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    2*(1-c-t)*(1-c+t) ≤ rigidityDeficit c (alignedState c t z w v) := by
  have h := alignedState_geometric_bound c t z w v hM
  unfold rigidityDeficit
  nlinarith

/-- Three actual two-by-two principal minors. They remain valid when a
diagonal entry or the entire state is rank deficient. -/
theorem alignedState_minor_w (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    Complex.normSq w ≤ (1+c+t)*(1-c+t)/16 := by
  have h := psd_det_nonneg (hM.submatrix (![(0,0),(1,1)] : Q → QQ))
  simp [Matrix.det_fin_two,Matrix.submatrix_apply,alignedState,alignedA,
    alignedD,alignedC,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.normSq_apply] at h ⊢
  nlinarith

theorem alignedState_minor_z (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    Complex.normSq z ≤ (1+c+t)*(1-c-t)/16 := by
  have h := psd_det_nonneg (hM.submatrix (![(0,0),(1,0)] : Q → QQ))
  simp [Matrix.det_fin_two,Matrix.submatrix_apply,alignedState,alignedA,
    alignedD,alignedC,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.normSq_apply] at h ⊢
  nlinarith

theorem alignedState_minor_v (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    Complex.normSq v ≤ (1+c-t)*(1-c-t)/16 := by
  have h := psd_det_nonneg (hM.submatrix (![(0,1),(1,0)] : Q → QQ))
  simp [Matrix.det_fin_two,Matrix.submatrix_apply,alignedState,alignedA,
    alignedD,alignedC,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.normSq_apply] at h ⊢
  nlinarith

/-- Equality in positivity of a trace product means orthogonal supports.
This is proved with PSD square roots and includes all singular cases. -/
theorem psd_mul_eq_zero_of_trace_re_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hz : (Matrix.trace (A*B)).re = 0) : A*B = 0 := by
  have htr : Matrix.trace (A*B) = 0 := by
    apply Complex.ext
    · exact hz
    · simpa using trace_mul_hermitian_im hA.1 hB.1
  let R := hB.sqrt
  have hR : R.IsHermitian := hB.posSemidef_sqrt.1
  have hRR : R*R = B := hB.sqrt_mul_self
  have hP : (R*A*R).PosSemidef := by
    simpa only [hR.eq] using hA.mul_mul_conjTranspose_same R
  have hPtr : Matrix.trace (R*A*R) = 0 := by
    rw [Matrix.trace_mul_cycle R A R,hRR,Matrix.trace_mul_comm B A,htr]
  have hzero := psd_eq_zero_of_trace_zero hP hPtr
  have hAR : A*R = 0 := psd_mul_eq_zero_of_congruence hA R (by simpa only [hR.eq] using hzero)
  rw [← hRR,← mul_assoc,hAR,zero_mul]

theorem alignedState_spinflip_trace (c t : ℝ) (z w v : ℂ) :
    4*(Matrix.trace (alignedState c t z w v *
      geometryFlip geometryEz (alignedState c t z w v))).re =
      1-c^2+2*t^2-correlationSq (alignedState c t z w v) := by
  rw [alignedState_bloch,blochState_correlationSq]
  have h := geometry_spinflip_identity (c • geometryEz) 0 geometryEz (alignedT t z w v)
  rw [alignedT_radial] at h
  simp [geometryEz,vSq,vDot,Fin.sum_univ_three,Pi.smul_apply,smul_eq_mul] at h ⊢
  linarith

theorem alignedState_saturation_product (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef)
    (he : correlationSq (alignedState c t z w v) = 1-c^2+2*t^2) :
    alignedState c t z w v * geometryFlip geometryEz (alignedState c t z w v) = 0 := by
  apply psd_mul_eq_zero_of_trace_re_zero hM (geometryFlip_psd geometryEz hM)
  have h := alignedState_spinflip_trace c t z w v
  rw [he] at h
  linarith

end Milne

#print axioms Milne.alignedState_geometric_bound
#print axioms Milne.alignedState_minor_w
#print axioms Milne.alignedState_saturation_product
