import MilneCanonicalization
import MilneCorrelation
import MilneScalarBounds

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

theorem pure_psd (v : QQ → ℂ) : (pure v).PosSemidef := by
  let W : Matrix Unit QQ ℂ := fun _ i => star (v i)
  have h : pure v = Wᴴ * W := by
    ext i j
    simp [W, pure, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self W

theorem psd_real_smul {n : Type*} [Fintype n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) : ((t:ℂ) • A).PosSemidef := by
  constructor
  · change ((t:ℂ) • A)ᴴ = (t:ℂ) • A
    simp [Matrix.conjTranspose_smul, hA.1.eq]
  · intro v
    simp only [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (RCLike.ofReal_nonneg.mpr ht) (hA.2 v)

def obeseVector (c : ℝ) : QQ → ℂ := fun i =>
  if i = (0,1) then 1 else if i = (1,0) then (Real.sqrt (1-c):ℂ) else 0

def obese (c : ℝ) : CMatrix :=
  (c/2:ℂ) • pure (Pi.single (0,0) 1) + (1/2:ℂ) • pure (obeseVector c)

def endpointFilter (r : ℝ) : Matrix Q Q ℂ :=
  Matrix.diagonal ![(Real.sqrt (1-r):ℂ), (Real.sqrt (1+r):ℂ)]

def obeseFiltered (c r : ℝ) : CMatrix :=
  onBob (endpointFilter r) * obese c * onBob (endpointFilter r)

/-- Positive square-root uniqueness recovers the actual physical filter from
the filtered state's Bob marginal. -/
theorem bobFilter_positive_filter (M : CMatrix) (F : Matrix Q Q ℂ)
    (hF : F.PosSemidef) (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hMF : Density (onBob F * M * onBob F)) :
    bobFilter (onBob F * M * onBob F) hMF = F := by
  unfold bobFilter
  symm
  apply hF.eq_sqrt_of_sq_eq
  rw [pow_two, partialB_filter, hB]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  ext i j
  simp
  ring

/-- Canonicalization is the inverse of every invertible positive Bob filter,
as an equality of actual complex matrices. -/
theorem canonicalize_positive_filter (M : CMatrix) (F : Matrix Q Q ℂ)
    (hF : F.PosSemidef) (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hMF : Density (onBob F * M * onBob F)) (hdet : F.det ≠ 0) :
    canonicalize (onBob F * M * onBob F) hMF = M := by
  have hFu := isUnit_iff_ne_zero.mpr hdet
  have hleft : onBob F⁻¹ * onBob F = (1:CMatrix) := by
    rw [← onBob_mul, Matrix.nonsing_inv_mul F hFu, onBob_one]
  have hright : onBob F * onBob F⁻¹ = (1:CMatrix) := by
    rw [← onBob_mul, Matrix.mul_nonsing_inv F hFu, onBob_one]
  rw [canonicalize, bobFilter_positive_filter M F hF hB hMF]
  calc
    _ = (onBob F⁻¹ * onBob F) * M * (onBob F * onBob F⁻¹) := by noncomm_ring
    _ = M := by rw [hleft, hright]; simp

theorem obese_psd {c : ℝ} (hc : 0 ≤ c) : (obese c).PosSemidef := by
  have h0 := psd_real_smul (pure_psd (Pi.single (0,0) 1)) (c/2) (by linarith)
  have h1 := psd_real_smul (pure_psd (obeseVector c)) (1/2) (by norm_num)
  simpa [obese] using h0.add h1

theorem obese_partialB {c : ℝ} (hc1 : c ≤ 1) :
    partialB (obese c) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [obese, obeseVector, pure, partialB, Fin.sum_univ_two,
      Matrix.one_apply, Complex.star_def, ← Complex.ofReal_mul,
      ← Complex.ofReal_pow, hs]
  all_goals ring_nf
  all_goals simp [← pow_two, hs]
  all_goals ring

theorem obese_density {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : Density (obese c) := by
  refine ⟨obese_psd hc0, ?_⟩
  rw [← trace_partialB, obese_partialB hc1, Matrix.trace_smul]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem obese_center {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : center (obese c) = c := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have hsC : (Real.sqrt (1-c):ℂ)^2 = (1-c:ℂ) := by exact_mod_cast hs
  have hb : blochSq (partialA (obese c)) = c^2 := by
    simp [blochSq, partialA, obese, obeseVector, pure, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.star_def, ← pow_two, hs, hsC]
    ring
  rw [center, hb, Real.sqrt_sq hc0]

theorem endpointFilter_psd {r : ℝ} : (endpointFilter r).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i
  · change 0 ≤ (Real.sqrt (1-r):ℂ)
    exact RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)
  · change 0 ≤ (Real.sqrt (1+r):ℂ)
    exact RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)

theorem endpointFilter_trace {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Matrix.trace (endpointFilter r * endpointFilter r) = 2 := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have h0C : (Real.sqrt (1-r):ℂ)^2 = (1-r:ℂ) := by exact_mod_cast h0
  have h1C : (Real.sqrt (1+r):ℂ)^2 = (1+r:ℂ) := by exact_mod_cast h1
  simp [endpointFilter, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.diagonal_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
    ← pow_two, h0, h1, h0C, h1C]
  ring

theorem endpointFilter_det_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (endpointFilter r).det ≠ 0 := by
  have h0 : (Real.sqrt (1-r) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (show 0 < 1-r by linarith))
  have h1 : (Real.sqrt (1+r) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (show 0 < 1+r by linarith))
  simpa [endpointFilter, Matrix.det_fin_two] using mul_ne_zero h0 h1

theorem obeseFiltered_density {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Density (obeseFiltered c r) := by
  have hM := obese_density hc0 hc1
  have hF := (endpointFilter_psd (r:=r)).1
  have hH := onBob_hermitian hF
  constructor
  · simpa only [obeseFiltered, hH.eq] using
      hM.1.mul_mul_conjTranspose_same (onBob (endpointFilter r))
  · rw [obeseFiltered, ← trace_partialB, partialB_filter, obese_partialB hc1]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul]
    rw [endpointFilter_trace hr0 hr1]
    norm_num

theorem obeseFiltered_bob_det_ne_zero {c r : ℝ} (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : (partialB (obeseFiltered c r)).det ≠ 0 := by
  have hd := endpointFilter_det_ne_zero hr0 hr1
  rw [obeseFiltered, partialB_filter, obese_partialB hc1]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [Matrix.det_smul, Matrix.det_mul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hd hd)

theorem obeseFiltered_canonicalize {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    canonicalize (obeseFiltered c r)
      (obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1)) = obese c := by
  exact canonicalize_positive_filter (obese c) (endpointFilter r) endpointFilter_psd
    (obese_partialB hc1) (obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1))
    (endpointFilter_det_ne_zero hr0 hr1)

theorem obeseFiltered_center {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    center (canonicalize (obeseFiltered c r)
      (obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1))) = c := by
  rw [obeseFiltered_canonicalize hc0 hc1 hr0 hr1]
  exact obese_center hc0 hc1

/-- The complete correlation matrix of the extremal filtered obese family. -/
theorem obeseFiltered_correlations {c r : ℝ} (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    correlation (obeseFiltered c r) = Matrix.diagonal
      ![Real.sqrt (1-c)*Real.sqrt (1-r)*Real.sqrt (1+r),
        Real.sqrt (1-c)*Real.sqrt (1-r)*Real.sqrt (1+r), -(1-c+c*r)] := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have hc := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  have h0C : (Real.sqrt (1-r):ℂ)^2 = (1-r:ℂ) := by exact_mod_cast h0
  have h1C : (Real.sqrt (1+r):ℂ)^2 = (1+r:ℂ) := by exact_mod_cast h1
  have hcC : (Real.sqrt (1-c):ℂ)^2 = (1-c:ℂ) := by exact_mod_cast hc
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlation, obeseFiltered, obese, obeseVector, endpointFilter,
      pure, onBob, pauliPair, pauli, pauliZ, Matrix.diagonal_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, Complex.star_def,
      ← pow_two, h0, h1, hc, h0C, h1C, hcC]
  all_goals ring_nf
  all_goals simp [h0, h1, hc, h0C, h1C, hcC]
  all_goals ring

/-- Saturation reduces to the exact scalar quadratic already checked in Lean. -/
theorem obeseFiltered_correlationSq {c r : ℝ} (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    correlationSq (obeseFiltered c r) = steeringQuadratic c r := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have hc := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  simp [correlationSq, obeseFiltered_correlations hc1 hr0 hr1,
    Fin.sum_univ_three, Matrix.diagonal_apply, mul_pow, h0, h1, hc,
    steeringQuadratic]
  ring

/-- On the nonconstant branch, the exact steering envelope is attained by a
density matrix whose actual canonical steering center is the prescribed c. -/
theorem steeringEnvelope_attained {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3) :
    ∃ (M : CMatrix) (hM : Density M), (partialB M).det ≠ 0 ∧
      center (canonicalize M hM) = c ∧ correlationSq M = steeringEnvelopeSq c := by
  let r := c*(1-c)/steeringDenominator c
  have hr0 : 0 ≤ r := (steering_vertex_in_unit_interval hc0 (le_of_lt hc)).1
  have hr1 : r < 1 := steering_vertex_lt_one hc0 hc
  have hc1 : c ≤ 1 := by linarith
  refine ⟨obeseFiltered c r, obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1),
    obeseFiltered_bob_det_ne_zero hc1 hr0 hr1, obeseFiltered_center hc0 hc1 hr0 hr1, ?_⟩
  rw [obeseFiltered_correlationSq hc1 hr0 (le_of_lt hr1)]
  exact steering_vertex_attains hc0 (le_of_lt hc)

/-- The numerical decimal 0.66 cannot be interpreted as an exact threshold:
the true transition is 2/3. This witness has c=0.6625 and F3²=1512/1511. -/
theorem decimal_threshold_counterexample :
    ∃ (M : CMatrix) (hM : Density M), (partialB M).det ≠ 0 ∧
      center (canonicalize M hM) = (53/80:ℝ) ∧ correlationSq M = (1512/1511:ℝ) := by
  obtain ⟨M, hM, hd, hc, hs⟩ := steeringEnvelope_attained
    (c := (53/80:ℝ)) (by norm_num) (by norm_num)
  refine ⟨M, hM, hd, hc, ?_⟩
  rw [hs]
  norm_num [steeringEnvelopeSq, steeringDenominator]

/-- An explicit epsilon version of the endpoint limit. It avoids any
assumption that a singular filter preserves the original steering center. -/
theorem steeringQuadratic_approaches_endpoint {c ε : ℝ}
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε : 0 < ε) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ 1-ε < steeringQuadratic c r := by
  let δ : ℝ := min (1/2) (ε/4)
  have hd0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd1 : δ ≤ 1/2 := min_le_left _ _
  have hde : δ ≤ ε/4 := min_le_right _ _
  have hA : 4*c-2-c^2 ≤ 1 := by nlinarith [sq_nonneg (c-1)]
  have hB : 6*c-4 ≤ 2 := by linarith
  have hpA := mul_le_mul_of_nonneg_left hA (sq_nonneg δ)
  have hpB := mul_le_mul_of_nonneg_left hB
    (mul_nonneg (show 0 ≤ 1-δ by linarith) (le_of_lt hd0))
  have hid : 1-steeringQuadratic c (1-δ) =
      δ^2*(4*c-2-c^2)+(1-δ)*δ*(6*c-4) := by
    unfold steeringQuadratic
    ring
  refine ⟨1-δ, by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg δ]

/-- On the constant branch the exact envelope is a supremum over invertible
filters. Every approximant has the prescribed, explicitly computed center. -/
theorem steeringEnvelope_supremum {c ε : ℝ} (hc : 2/3 ≤ c) (hc1 : c ≤ 1)
    (hε : 0 < ε) :
    ∃ (M : CMatrix) (hM : Density M), (partialB M).det ≠ 0 ∧
      center (canonicalize M hM) = c ∧ steeringEnvelopeSq c-ε < correlationSq M := by
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨r, hr0, hr1, hr⟩ := steeringQuadratic_approaches_endpoint hc0 hc1 hε
  refine ⟨obeseFiltered c r, obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1),
    obeseFiltered_bob_det_ne_zero hc1 hr0 hr1, obeseFiltered_center hc0 hc1 hr0 hr1, ?_⟩
  rw [obeseFiltered_correlationSq hc1 hr0 (le_of_lt hr1), steeringEnvelopeSq_eq_one hc]
  exact hr

end Milne
