module
public import MilneFiltering
public import MilneCorrelation
public import MilneScalarBounds
public import MilneCanonicalization

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def blochLength (A : Matrix Q Q ℂ) : ℝ := Real.sqrt (blochSq A)

theorem blochLength_nonneg (A : Matrix Q Q ℂ) : 0 ≤ blochLength A :=
  Real.sqrt_nonneg _

theorem blochLength_sq (A : Matrix Q Q ℂ) : blochLength A ^ 2 = blochSq A :=
  Real.sq_sqrt (blochSq_nonneg A)

theorem blochLength_add_le (A B : Matrix Q Q ℂ) :
    blochLength (A+B) ≤ blochLength A + blochLength B := by
  let u : Fin 3 → ℝ := ![(A 0 0).re-(A 1 1).re, 2*(A 0 1).re, 2*(A 0 1).im]
  let v : Fin 3 → ℝ := ![(B 0 0).re-(B 1 1).re, 2*(B 0 1).re, 2*(B 0 1).im]
  have hu : (∑ i, u i ^ 2) = blochSq A := by
    simp [u, Fin.sum_univ_three, blochSq, Complex.normSq_apply]
    ring
  have hv : (∑ i, v i ^ 2) = blochSq B := by
    simp [v, Fin.sum_univ_three, blochSq, Complex.normSq_apply]
    ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  rw [hu, hv] at hc
  have hid : blochSq (A+B) = blochSq A + blochSq B + 2*(∑ i, u i*v i) := by
    simp [u, v, Fin.sum_univ_three, blochSq, Complex.normSq_apply]
    ring
  have hp0 : 0 ≤ blochLength A * blochLength B :=
    mul_nonneg (blochLength_nonneg A) (blochLength_nonneg B)
  have hp2 : (blochLength A * blochLength B)^2 = blochSq A * blochSq B := by
    rw [mul_pow, blochLength_sq, blochLength_sq]
  have hcross : (∑ i, u i*v i) ≤ blochLength A * blochLength B := by
    nlinarith
  have ha := blochLength_sq A
  have hb := blochLength_sq B
  have hab := blochLength_sq (A+B)
  nlinarith [blochLength_nonneg A, blochLength_nonneg B, blochLength_nonneg (A+B)]

theorem blochLength_smul (t : ℝ) (ht : 0 ≤ t) (A : Matrix Q Q ℂ) :
    blochLength ((t:ℂ) • A) = t * blochLength A := by
  unfold blochLength
  rw [blochSq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

theorem blochLength_psd_le {A : Matrix Q Q ℂ} (hA : A.PosSemidef) :
    blochLength A ≤ (Matrix.trace A).re := by
  have h := blochSq_psd_le hA
  have ht := psd_trace_nonneg hA
  have hs := blochLength_sq A
  nlinarith [blochLength_nonneg A]

theorem onBob_smul (t : ℂ) (A : Matrix Q Q ℂ) :
    onBob (t • A) = t • onBob A := by
  ext i j
  by_cases h : i.1 = j.1 <;> simp [onBob, h]

theorem onBob_sub (A B : Matrix Q Q ℂ) :
    onBob (A-B) = onBob A - onBob B := by
  ext i j
  by_cases h : i.1 = j.1 <;> simp [onBob, h]

/-- Moving a Bob operator around a partial trace is a purely algebraic
identity; Alice's two indices are not traced out. -/
theorem partialA_bob_cycle (M : CMatrix) (F G : Matrix Q Q ℂ) :
    partialA (onBob F * M * onBob G) = partialA (M * onBob (G*F)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialA, onBob, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals ring

def bobWeighted (M : CMatrix) (K : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  partialA (M * onBob K)

theorem bobWeighted_psd {M : CMatrix} (hM : M.PosSemidef)
    {K : Matrix Q Q ℂ} (hK : K.PosSemidef) : (bobWeighted M K).PosSemidef := by
  let S : Matrix Q Q ℂ := CFC.sqrt K
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian
  have hSS : S*S = K := CFC.sqrt_mul_sqrt_self K hK.nonneg
  have hp := hM.mul_mul_conjTranspose_same (onBob S)
  rw [(onBob_hermitian hS).eq] at hp
  have h := partialA_psd hp
  rw [partialA_bob_cycle, hSS] at h
  exact h

theorem bobWeighted_trace (M : CMatrix) (K : Matrix Q Q ℂ) :
    Matrix.trace (bobWeighted M K) = Matrix.trace (partialB M * K) := by
  simp [bobWeighted, partialA, partialB, onBob, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem bobWeighted_sub (M : CMatrix) (K L : Matrix Q Q ℂ) :
    bobWeighted M (K-L) = bobWeighted M K - bobWeighted M L := by
  simp only [bobWeighted, onBob_sub, mul_sub, partialA_sub]

theorem bobWeighted_smul (M : CMatrix) (t : ℂ) (K : Matrix Q Q ℂ) :
    bobWeighted M (t • K) = t • bobWeighted M K := by
  simp only [bobWeighted, onBob_smul, Matrix.mul_smul, partialA_smul]

theorem bobWeighted_one (M : CMatrix) :
    bobWeighted M (1 : Matrix Q Q ℂ) = partialA M := by
  simp only [bobWeighted, onBob_one, mul_one]

theorem filtered_density (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    Density (onBob F * M * onBob F) := by
  constructor
  · have h := hM.1.mul_mul_conjTranspose_same (onBob F)
    simpa only [(onBob_hermitian hF).eq] using h
  · rw [← trace_partialB, partialB_filter, hB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, Matrix.trace_smul]
    rw [hTr]
    norm_num

theorem filtered_bob_marginal (M : CMatrix)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (F : Matrix Q Q ℂ) :
    partialB (onBob F * M * onBob F) = (1/2:ℂ) • (F*F) := by
  rw [partialB_filter, hB]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one]

/-- The sharp marginal contraction used in the steering envelope. Every
hypothesis refers to the actual state and filter, including positivity. -/
theorem filtered_alice_bloch_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    blochSq (partialA ρ) ≤ (center M + (1-center M)*r)^2 := by
  let ρ := onBob F * M * onBob F
  let r := blochLength (partialB ρ)
  let K : Matrix Q Q ℂ := F*F - ((1-r:ℝ):ℂ) • (1 : Matrix Q Q ℂ)
  let R := bobWeighted M K
  have hρ : Density ρ := filtered_density M hM hB F hF hTr
  have htB : Matrix.trace (partialB ρ) = 1 := by rw [trace_partialB, hρ.2]
  have hr0 : 0 ≤ r := blochLength_nonneg _
  have hr1 : r ≤ 1 := by
    have h := blochLength_psd_le (partialB_psd hρ.1)
    simpa only [htB, Complex.one_re] using h
  have hK : K.PosSemidef := by
    have h := qubit_lower_operator_bound (partialB_psd hρ.1).1 htB
    change ((2:ℂ) • partialB ρ - ((1-r:ℝ):ℂ) • (1 : Matrix Q Q ℂ)).PosSemidef at h
    rw [filtered_bob_marginal M hB F] at h
    simpa [K, smul_smul] using h
  have hR : R.PosSemidef := bobWeighted_psd hM.1 hK
  have htK : Matrix.trace K = (2*r:ℝ) := by
    change Matrix.trace (F*F - ((1-r:ℝ):ℂ) • (1 : Matrix Q Q ℂ)) = (2*r:ℝ)
    rw [Matrix.trace_sub, Matrix.trace_smul, hTr]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, smul_eq_mul]
    ring
  have htR : Matrix.trace R = (r:ℂ) := by
    rw [bobWeighted_trace, hB, Matrix.smul_mul, one_mul, Matrix.trace_smul, htK]
    simp only [smul_eq_mul]
    push_cast
    ring
  have hsplit : partialA ρ = ((1-r:ℝ):ℂ) • partialA M + R := by
    have hRdef : R = bobWeighted M (F*F) - ((1-r:ℝ):ℂ) • partialA M := by
      change bobWeighted M (F*F - ((1-r:ℝ):ℂ) • (1 : Matrix Q Q ℂ)) = _
      rw [bobWeighted_sub, bobWeighted_smul, bobWeighted_one]
    rw [hRdef]
    change partialA (onBob F * M * onBob F) = _
    rw [partialA_bob_cycle]
    simp only [bobWeighted]
    abel
  have hl : blochLength (partialA ρ) ≤ (1-r)*center M + r := by
    rw [hsplit]
    have h := blochLength_add_le (((1-r:ℝ):ℂ) • partialA M) R
    rw [blochLength_smul (1-r) (sub_nonneg.mpr hr1)] at h
    have hRl := blochLength_psd_le hR
    rw [htR, Complex.ofReal_re] at hRl
    have hc : blochLength (partialA M) = center M := rfl
    rw [hc] at h
    linarith
  have hs := blochLength_sq (partialA ρ)
  have htarget0 : 0 ≤ center M + (1-center M)*r := by
    have hc0 := center_nonneg M
    have hc1 := center_le_one M hM
    nlinarith
  change blochSq (partialA ρ) ≤ (center M + (1-center M)*r)^2
  nlinarith [blochLength_nonneg (partialA ρ)]

theorem purityDifference_filter_re (M : CMatrix) (F : Matrix Q Q ℂ)
    (hF : F.IsHermitian) :
    (purityDifference (onBob F * M * onBob F)).re =
      F.det.re ^ 2 * (purityDifference M).re := by
  have h := congrArg Complex.re (purityDifference_filter M F)
  simpa [pow_two, Complex.mul_re, Complex.mul_im, hermitian_det_im hF] using h

theorem filter_det_bloch (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    F.det.re ^ 2 = 1 - blochSq (partialB (onBob F * M * onBob F)) := by
  let ρ := onBob F * M * onBob F
  have hρ : Density ρ := filtered_density M hM hB F hF hTr
  have htB : Matrix.trace (partialB ρ) = 1 := by rw [trace_partialB, hρ.2]
  have hd := blochSq_det_identity (partialB_psd hρ.1).1
  rw [htB] at hd
  have hdet : (partialB ρ).det = (1/4:ℂ) * F.det ^ 2 := by
    rw [filtered_bob_marginal M hB F, Matrix.det_smul, Matrix.det_mul]
    norm_num [Q]
    ring
  rw [hdet] at hd
  have hi := hermitian_det_im hF
  simp [pow_two, Complex.mul_re, Complex.mul_im, hi] at hd
  change F.det.re ^ 2 = 1 - blochSq (partialB ρ)
  nlinarith

/-- The exact physical quadratic bound before optimizing the Bob filter.
No Bloch vector, purity inequality, or determinant identity is assumed. -/
theorem filtered_steering_quadratic_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    let ρ := onBob F * M * onBob F
    correlationSq ρ ≤ steeringQuadratic (center M) (blochLength (partialB ρ)) := by
  let ρ := onBob F * M * onBob F
  let r := blochLength (partialB ρ)
  have hρ : Density ρ := filtered_density M hM hB F hF hTr
  have htB : Matrix.trace (partialB ρ) = 1 := by rw [trace_partialB, hρ.2]
  have hr0 : 0 ≤ r := blochLength_nonneg _
  have hr1 : r ≤ 1 := by
    have h := blochLength_psd_le (partialB_psd hρ.1)
    simpa only [htB, Complex.one_re] using h
  have hrsq : r^2 = blochSq (partialB ρ) := blochLength_sq _
  have hcSq : center M ^ 2 = blochSq (partialA M) := Real.sq_sqrt (blochSq_nonneg _)
  have hAP := blochSq_trace_identity (partialA_psd hM.1).1
  rw [trace_partialA, hM.2] at hAP
  norm_num at hAP
  have hP := canonical_purity_bound M hM hB
  have hE : 4*(purityDifference M).re ≤ 2-4*center M := by
    simp only [purityDifference, Complex.sub_re]
    nlinarith
  have hdet := filter_det_bloch M hM hB F hF hTr
  have hCov := purityDifference_filter_re M F hF
  rw [hdet] at hCov
  change (purityDifference ρ).re =
    (1-blochSq (partialB ρ))*(purityDifference M).re at hCov
  rw [← hrsq] at hCov
  have hD : 0 ≤ 1-r^2 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hProd := mul_le_mul_of_nonneg_left hE hD
  have hC := correlationSq_purityDifference ρ hρ
  rw [← hrsq] at hC
  have hA := filtered_alice_bloch_bound M hM hB F hF hTr
  change blochSq (partialA ρ) ≤ (center M + (1-center M)*r)^2 at hA
  change correlationSq ρ ≤ steeringQuadratic (center M) r
  unfold steeringQuadratic
  nlinarith

/-- Sharp universal three-setting steering envelope for all canonical states
and all normalized Hermitian Bob filters, including singular filters. -/
theorem filtered_steering_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    correlationSq (onBob F * M * onBob F) ≤ steeringEnvelopeSq (center M) := by
  let ρ := onBob F * M * onBob F
  have hρ : Density ρ := filtered_density M hM hB F hF hTr
  have htB : Matrix.trace (partialB ρ) = 1 := by rw [trace_partialB, hρ.2]
  have hr0 : 0 ≤ blochLength (partialB ρ) := blochLength_nonneg _
  have hr1 : blochLength (partialB ρ) ≤ 1 := by
    have h := blochLength_psd_le (partialB_psd hρ.1)
    simpa only [htB, Complex.one_re] using h
  exact (filtered_steering_quadratic_bound M hM hB F hF hTr).trans
    (steeringQuadratic_le_envelope (center_nonneg M) (center_le_one M hM) hr0 hr1)

/-- The three-setting steering bound for an arbitrary physical density
matrix, with the center computed by actual canonicalization. -/
theorem arbitrary_steering_bound (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    correlationSq M ≤ steeringEnvelopeSq (center (canonicalize M hM)) := by
  have h := filtered_steering_bound (canonicalize M hM)
    (canonicalize_density M hM hdet) (canonicalize_partialB M hM hdet)
    (bobFilter M hM) (bobFilter_hermitian M hM) (bobFilter_trace M hM)
  rwa [canonicalize_reconstruction M hM hdet] at h

/-- The same exact envelope in the conventional nonnegative F3 units. -/
theorem arbitrary_steering_value_bound (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    Real.sqrt (correlationSq M) ≤
      Real.sqrt (steeringEnvelopeSq (center (canonicalize M hM))) :=
  Real.sqrt_le_sqrt (arbitrary_steering_bound M hM hdet)

/-- The exact center threshold 2/3 for the three-setting criterion. -/
theorem arbitrary_steering_threshold (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) (hc : 2/3 ≤ center (canonicalize M hM)) :
    correlationSq M ≤ 1 := by
  have h := arbitrary_steering_bound M hM hdet
  rwa [steeringEnvelopeSq_eq_one hc] at h

end Milne
