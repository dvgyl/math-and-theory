import MilneOptimality
import MilneNonattainment

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- Loss from the maximal canonical correlation norm at the same center. -/
def canonicalCorrelationDeficit (M : CMatrix) : ℝ :=
  3 - 4 * center M + center M ^ 2 - correlationSq M

/-- Loss in the sharp bound on Alice's marginal after a normalized Bob filter. -/
def marginalDeficit (M : CMatrix) (F : Matrix Q Q ℂ) : ℝ :=
  (center M + (1-center M) * blochLength (partialB (onBob F * M * onBob F)))^2 -
    blochSq (partialA (onBob F * M * onBob F))

def optimalFilterLength (c : ℝ) : ℝ := c*(1-c)/steeringDenominator c

theorem canonical_bob_blochSq_zero (M : CMatrix)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    blochSq (partialB M) = 0 := by
  rw [hB]
  norm_num [blochSq, Matrix.one_apply, Complex.normSq_apply]

theorem canonicalCorrelationDeficit_nonneg (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    0 ≤ canonicalCorrelationDeficit M := by
  have hp := canonical_purity_bound M hM hB
  have hc := correlationSq_bloch M hM
  rw [canonical_bob_blochSq_zero M hB] at hc
  have hs : center M ^ 2 = blochSq (partialA M) :=
    Real.sq_sqrt (blochSq_nonneg _)
  unfold canonicalCorrelationDeficit
  nlinarith

theorem marginalDeficit_nonneg (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    0 ≤ marginalDeficit M F := by
  have h := filtered_alice_bloch_bound M hM hB F hF hTr
  exact sub_nonneg.mpr h

/-- Exact physical filter identity, with no positivity-rank restriction on F. -/
theorem filtered_correlation_identity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    correlationSq ρ = (1-r^2)*(correlationSq M-center M^2) + blochSq (partialA ρ) := by
  let ρ := onBob F * M * onBob F
  let r := blochLength (partialB ρ)
  have hρ : Density ρ := filtered_density M hM hB F hF hTr
  have hCov := purityDifference_filter_re M F hF
  rw [filter_det_bloch M hM hB F hF hTr] at hCov
  have hCM := correlationSq_purityDifference M hM
  rw [canonical_bob_blochSq_zero M hB] at hCM
  have hCρ := correlationSq_purityDifference ρ hρ
  have hcSq : center M ^ 2 = blochSq (partialA M) :=
    Real.sq_sqrt (blochSq_nonneg _)
  have hrSq : r ^ 2 = blochSq (partialB ρ) := blochLength_sq _
  change (purityDifference ρ).re =
    (1-blochSq (partialB ρ))*(purityDifference M).re at hCov
  change correlationSq ρ = (1-r^2)*(correlationSq M-center M^2) + blochSq (partialA ρ)
  rw [hCρ, hCM, ← hcSq, ← hrSq, hCov, ← hrSq]
  ring

/-- The two physical losses exactly account for the joint-envelope slack. -/
theorem filtered_quadratic_deficit_identity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    steeringQuadratic (center M) r-correlationSq ρ =
      (1-r^2)*canonicalCorrelationDeficit M + marginalDeficit M F := by
  dsimp only
  rw [filtered_correlation_identity M hM hB F hF hTr]
  unfold steeringQuadratic canonicalCorrelationDeficit marginalDeficit
  ring

theorem steering_completed_square {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/3)
    (r : ℝ) : steeringEnvelopeSq c-steeringQuadratic c r =
      steeringDenominator c*(r-optimalFilterLength c)^2 := by
  rw [steeringEnvelopeSq, if_pos hc]
  have hd := ne_of_gt (steeringDenominator_pos hc0 hc)
  unfold optimalFilterLength steeringQuadratic
  field_simp
  unfold steeringDenominator
  ring

/-- Exact global-envelope deficit decomposition on the curved branch. -/
theorem filtered_envelope_deficit_identity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2)
    (hc : center M ≤ 2/3) :
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    steeringEnvelopeSq (center M)-correlationSq ρ =
      steeringDenominator (center M)*(r-optimalFilterLength (center M))^2 +
      (1-r^2)*canonicalCorrelationDeficit M + marginalDeficit M F := by
  have h1 := filtered_quadratic_deficit_identity M hM hB F hF hTr
  have h2 := steering_completed_square (center_nonneg M) hc
    (blochLength (partialB (onBob F * M * onBob F)))
  dsimp only at h1 ⊢
  linarith

/-- Exact flat-branch deficit identity. For 2/3 ≤ center M ≤ 1 and a
physical marginal length every displayed summand is nonnegative. -/
theorem filtered_flat_deficit_identity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2) :
    let c := center M
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    1-correlationSq ρ =
      (1-r)^2*(4*c-2-c^2)+r*(1-r)*(6*c-4) +
      (1-r^2)*canonicalCorrelationDeficit M + marginalDeficit M F := by
  have h := filtered_quadratic_deficit_identity M hM hB F hF hTr
  dsimp only at h ⊢
  unfold steeringQuadratic at h
  nlinarith

/-- Every term of the exact deficit is separately bounded by the total deficit. -/
theorem filtered_envelope_quantitative_rigidity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2)
    (hc : center M ≤ 2/3) :
    let ρ := onBob F * M * onBob F
    let r := blochLength (partialB ρ)
    let ε := steeringEnvelopeSq (center M)-correlationSq ρ
    steeringDenominator (center M)*(r-optimalFilterLength (center M))^2 ≤ ε ∧
    (1-r^2)*canonicalCorrelationDeficit M ≤ ε ∧ marginalDeficit M F ≤ ε := by
  let ρ := onBob F * M * onBob F
  let r := blochLength (partialB ρ)
  have hρ : Density ρ := filtered_density M hM hB F hF hTr
  have hr0 : 0 ≤ r := blochLength_nonneg _
  have hr1 : r ≤ 1 := by
    have h := blochLength_psd_le (partialB_psd hρ.1)
    rw [trace_partialB,hρ.2] at h
    exact h
  have hrSq : 0 ≤ 1-r^2 := by nlinarith
  have hC := canonicalCorrelationDeficit_nonneg M hM hB
  have hA := marginalDeficit_nonneg M hM hB F hF hTr
  have hD := steeringDenominator_pos (center_nonneg M) hc
  have hP := mul_nonneg hrSq hC
  have hS := mul_nonneg (le_of_lt hD) (sq_nonneg (r-optimalFilterLength (center M)))
  have hid := filtered_envelope_deficit_identity M hM hB F hF hTr hc
  dsimp only at hid ⊢
  change steeringDenominator (center M)*(r-optimalFilterLength (center M))^2 ≤ _ ∧
    (1-r^2)*canonicalCorrelationDeficit M ≤ _ ∧ marginalDeficit M F ≤ _
  change steeringEnvelopeSq (center M)-correlationSq ρ =
    steeringDenominator (center M)*(r-optimalFilterLength (center M))^2 +
    (1-r^2)*canonicalCorrelationDeficit M + marginalDeficit M F at hid
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A necessary and sufficient, coordinate-free equality test for all physical
states on the curved branch. It uses two geometric saturation conditions and
the unique filter length; neither low density-matrix rank nor a special form
of the state is assumed. -/
theorem filtered_envelope_equality_iff (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F*F) = 2)
    (hc : center M ≤ 2/3)
    (hr : blochLength (partialB (onBob F * M * onBob F)) < 1) :
    correlationSq (onBob F * M * onBob F) = steeringEnvelopeSq (center M) ↔
      blochLength (partialB (onBob F * M * onBob F)) = optimalFilterLength (center M) ∧
      canonicalCorrelationDeficit M = 0 ∧ marginalDeficit M F = 0 := by
  let r := blochLength (partialB (onBob F * M * onBob F))
  have hr0 : 0 ≤ r := blochLength_nonneg _
  have hrP : 0 < 1-r^2 := by change r < 1 at hr; nlinarith
  have hD := steeringDenominator_pos (center_nonneg M) hc
  have hC := canonicalCorrelationDeficit_nonneg M hM hB
  have hA := marginalDeficit_nonneg M hM hB F hF hTr
  have hid := filtered_envelope_deficit_identity M hM hB F hF hTr hc
  dsimp only at hid
  change steeringEnvelopeSq (center M)-correlationSq (onBob F * M * onBob F) =
    steeringDenominator (center M)*(r-optimalFilterLength (center M))^2 +
    (1-r^2)*canonicalCorrelationDeficit M + marginalDeficit M F at hid
  have hP := mul_nonneg (le_of_lt hrP) hC
  have hS := mul_nonneg (le_of_lt hD) (sq_nonneg (r-optimalFilterLength (center M)))
  constructor
  · intro heq
    rw [heq] at hid
    have hsZero : steeringDenominator (center M)*(r-optimalFilterLength (center M))^2 = 0 := by
      linarith
    have hs : (r-optimalFilterLength (center M))^2 = 0 :=
      (mul_eq_zero.mp hsZero).resolve_left (ne_of_gt hD)
    have hpZero : (1-r^2)*canonicalCorrelationDeficit M = 0 := by linarith
    have hcZero : canonicalCorrelationDeficit M = 0 :=
      (mul_eq_zero.mp hpZero).resolve_left (ne_of_gt hrP)
    exact ⟨by change r = _; nlinarith, hcZero, by linarith⟩
  · rintro ⟨hrEq,hcZero,haZero⟩
    change r = optimalFilterLength (center M) at hrEq
    rw [hrEq,hcZero,haZero] at hid
    nlinarith

/-- Stronger physical envelope retaining the original Bob marginal length. -/
theorem arbitrary_joint_steering_bound (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det ≠ 0) :
    correlationSq M ≤ steeringQuadratic (steeringCenter M hM) (blochLength (partialB M)) := by
  have h := filtered_steering_quadratic_bound (canonicalize M hM)
    (canonicalize_density M hM hd) (canonicalize_partialB M hM hd)
    (bobFilter M hM) (bobFilter_hermitian M hM) (bobFilter_trace M hM)
  dsimp only at h
  rw [canonicalize_reconstruction M hM hd] at h
  rwa [steeringCenter_of_nonsingular M hM hd]

/-- The exact deficit formula directly on an arbitrary state, without an
external assumption that the state has a chosen canonical/filter form. -/
theorem arbitrary_envelope_deficit_identity (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det ≠ 0) (hc : steeringCenter M hM ≤ 2/3) :
    let c := steeringCenter M hM
    let r := blochLength (partialB M)
    steeringEnvelopeSq c-correlationSq M =
      steeringDenominator c*(r-optimalFilterLength c)^2 +
      (1-r^2)*canonicalCorrelationDeficit (canonicalize M hM) +
      ((c+(1-c)*r)^2-blochSq (partialA M)) := by
  rw [steeringCenter_of_nonsingular M hM hd] at hc
  have h := filtered_envelope_deficit_identity (canonicalize M hM)
    (canonicalize_density M hM hd) (canonicalize_partialB M hM hd)
    (bobFilter M hM) (bobFilter_hermitian M hM) (bobFilter_trace M hM) hc
  dsimp only at h ⊢
  unfold marginalDeficit at h
  rw [canonicalize_reconstruction M hM hd] at h
  rwa [steeringCenter_of_nonsingular M hM hd]

/-- An exact extremizer test stated directly for an arbitrary physical state.
The canonical correlation norm and the output marginal must both saturate
their independent sharp bounds, and the marginal length is uniquely fixed. -/
theorem arbitrary_envelope_equality_iff (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det ≠ 0) (hc : steeringCenter M hM ≤ 2/3) :
    let c := steeringCenter M hM
    let r := blochLength (partialB M)
    correlationSq M = steeringEnvelopeSq c ↔
      r = optimalFilterLength c ∧
      correlationSq (canonicalize M hM) = 3-4*c+c^2 ∧
      blochSq (partialA M) = (c+(1-c)*r)^2 := by
  rw [steeringCenter_of_nonsingular M hM hd] at hc
  have hr : blochLength
      (partialB (onBob (bobFilter M hM) * canonicalize M hM * onBob (bobFilter M hM))) < 1 := by
    rw [canonicalize_reconstruction M hM hd]
    exact fullrank_Bob_blochLength_lt_one M hM hd
  have h := filtered_envelope_equality_iff (canonicalize M hM)
    (canonicalize_density M hM hd) (canonicalize_partialB M hM hd)
    (bobFilter M hM) (bobFilter_hermitian M hM) (bobFilter_trace M hM) hc hr
  unfold marginalDeficit canonicalCorrelationDeficit at h
  rw [canonicalize_reconstruction M hM hd] at h
  dsimp only
  rw [steeringCenter_of_nonsingular M hM hd]
  constructor
  · intro heq
    obtain ⟨hrEq,hcEq,haEq⟩ := h.mp heq
    exact ⟨hrEq,by linarith,by linarith⟩
  · rintro ⟨hrEq,hcEq,haEq⟩
    exact h.mpr ⟨hrEq,by linarith,by linarith⟩

theorem bob_det_ne_zero_of_blochLength_lt_one (M : CMatrix) (hM : Density M)
    (hr : blochLength (partialB M) < 1) : (partialB M).det ≠ 0 := by
  intro hd
  have hs := singular_Bob_blochSq M hM hd
  have hlen : blochLength (partialB M) = 1 := by
    rw [blochLength, hs, Real.sqrt_one]
  linarith

theorem obeseFiltered_bob_length {c r : ℝ} (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    blochLength (partialB (obeseFiltered c r)) = r := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have h0C : (Real.sqrt (1-r):ℂ)^2 = (1-r:ℂ) := by exact_mod_cast h0
  have h1C : (Real.sqrt (1+r):ℂ)^2 = (1+r:ℂ) := by exact_mod_cast h1
  have hb : blochSq (partialB (obeseFiltered c r)) = r^2 := by
    rw [obeseFiltered, filtered_bob_marginal (obese c) (obese_partialB hc1)]
    simp only [endpointFilter, Matrix.diagonal_mul_diagonal]
    simp [blochSq, endpointFilter, Matrix.diagonal_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, ← pow_two, h0, h1, h0C, h1C]
    ring
  rw [blochLength,hb,Real.sqrt_sq hr0]

/-- Squared correlation values at prescribed actual center and marginal length. -/
def jointSteeringSpectrum (c r : ℝ) : Set ℝ :=
  {x | ∃ (M : CMatrix) (hM : Density M), steeringCenter M hM = c ∧
    blochLength (partialB M) = r ∧ correlationSq M = x}

/-- The complete two-parameter sharp envelope away from the pure-marginal boundary. -/
theorem jointSteeringQuadratic_isGreatest {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsGreatest (jointSteeringSpectrum c r) (steeringQuadratic c r) := by
  constructor
  · let hM := obeseFiltered_density hc0 hc1 hr0 (le_of_lt hr1)
    refine ⟨obeseFiltered c r, hM, ?_, obeseFiltered_bob_length hc1 hr0 (le_of_lt hr1),
      obeseFiltered_correlationSq hc1 hr0 (le_of_lt hr1)⟩
    rw [steeringCenter_of_nonsingular _ hM (obeseFiltered_bob_det_ne_zero hc1 hr0 hr1)]
    exact obeseFiltered_center hc0 hc1 hr0 hr1
  · rintro x ⟨M,hM,hc,hr,hx⟩
    have hlen : blochLength (partialB M) < 1 := by rwa [hr]
    have h := arbitrary_joint_steering_bound M hM
      (bob_det_ne_zero_of_blochLength_lt_one M hM hlen)
    rwa [hc,hr,hx] at h

/-- A product state with a prescribed point ellipsoid and pure Bob marginal. -/
def pointProduct (c : ℝ) : CMatrix :=
  (((1+c)/2:ℝ):ℂ) • pure (Pi.single (0,0) 1) +
  (((1-c)/2:ℝ):ℂ) • pure (Pi.single (1,0) 1)

theorem pointProduct_density {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Density (pointProduct c) := by
  constructor
  · exact (psd_real_smul (pure_psd (Pi.single (0,0) 1)) ((1+c)/2) (by linarith)).add
      (psd_real_smul (pure_psd (Pi.single (1,0) 1)) ((1-c)/2) (by linarith))
  · simp [pointProduct, Matrix.trace, Matrix.diag, pure, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    ring

theorem pointProduct_bob_det (c : ℝ) : (partialB (pointProduct c)).det = 0 := by
  simp [pointProduct, partialB, pure, Matrix.det_fin_two, Fin.sum_univ_two]

theorem pointProduct_blochSq (c : ℝ) : blochSq (partialA (pointProduct c)) = c^2 := by
  simp [pointProduct, partialA, pure, blochSq, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem singular_joint_spectrum_value (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det = 0) : correlationSq M = (steeringCenter M hM)^2 := by
  rw [singular_Bob_correlationSq_eq_blochSq M hM hd, steeringCenter, if_pos hd,
    center, Real.sq_sqrt (blochSq_nonneg _)]

/-- At a pure steering-party marginal the entire joint spectrum is a singleton.
This is different from substituting r=1 into the nonsingular formula. -/
theorem jointSteeringSpectrum_pure_marginal {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    jointSteeringSpectrum c 1 = {c^2} := by
  ext x
  constructor
  · rintro ⟨M,hM,hc,hr,hx⟩
    have hd : (partialB M).det = 0 := by
      by_contra hn
      have h := fullrank_Bob_blochLength_lt_one M hM hn
      rw [hr] at h
      linarith
    have h := singular_joint_spectrum_value M hM hd
    rw [hc,hx] at h
    exact h
  · intro hx
    have hxEq : x = c^2 := hx
    subst x
    let hM := pointProduct_density hc0 hc1
    have hd := pointProduct_bob_det c
    have hcenter : steeringCenter (pointProduct c) hM = c := by
      rw [steeringCenter,if_pos hd,center,pointProduct_blochSq,Real.sqrt_sq hc0]
    refine ⟨pointProduct c,hM,hcenter,?_,?_⟩
    · rw [blochLength,singular_Bob_blochSq _ hM hd,Real.sqrt_one]
    · rw [singular_joint_spectrum_value _ hM hd,hcenter]

/-- The sharp joint envelope includes the rank-deficient marginal separately. -/
def jointSteeringEnvelopeSq (c r : ℝ) : ℝ :=
  if r = 1 then c^2 else steeringQuadratic c r

theorem jointSteeringEnvelope_isGreatest {c r : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsGreatest (jointSteeringSpectrum c r) (jointSteeringEnvelopeSq c r) := by
  by_cases hr : r = 1
  · subst r
    rw [jointSteeringSpectrum_pure_marginal hc0 hc1]
    simp [jointSteeringEnvelopeSq, IsGreatest, upperBounds]
  · rw [jointSteeringEnvelopeSq,if_neg hr]
    exact jointSteeringQuadratic_isGreatest hc0 hc1 hr0 (lt_of_le_of_ne hr1 hr)

end Milne
