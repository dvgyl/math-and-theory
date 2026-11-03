import MilneGeometryRange
import MilnePhysicalOrbitFilter

/-!
# The actual Bloch-coordinate formula for the steering centre

For every density matrix with invertible Bob marginal, this module proves
that the Alice vector of its canonical representative is
`(a - T b) / (1 - |b|^2)`, using directly measured Pauli coordinates.
No full-rank assumption on the joint state is imposed.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

theorem center_actual_partialA (M : CMatrix) (hM : Density M) :
    partialA M = qubitState (geometryLocalA M) := by
  have h := congrArg partialA (geometry_density_reconstruction M hM)
  rw [blochState_partialA] at h
  exact h.symm

theorem center_actual_partialB (M : CMatrix) (hM : Density M) :
    partialB M = qubitState (geometryLocalB M) := by
  have h := congrArg partialB (geometry_density_reconstruction M hM)
  rw [blochState_partialB] at h
  exact h.symm

/-- Exact weighted marginal identity in actual Bloch coordinates. -/
theorem center_weighted_bloch (a b : V3) (T : T3) :
    bobWeighted (blochState a b T) (1-spin b) =
      (1/2:ℂ) • ((((1-vSq b):ℝ):ℂ) • (1 : Matrix Q Q ℂ) +
        spin (a-tVec T b)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [bobWeighted,partialA,blochState,onAlice,onBob,spin,pauli,pauliZ,
      vSq,tVec,Matrix.mul_apply,Matrix.one_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,
      Pi.sub_apply,pow_two]
  all_goals ring

theorem center_weighted_congruence (M : CMatrix) (F G K : Matrix Q Q ℂ) :
    bobWeighted (onBob F*M*onBob G) K = bobWeighted M (G*K*F) := by
  unfold bobWeighted
  calc
    partialA ((onBob F*M*onBob G)*onBob K) =
        partialA (onBob F*M*onBob (G*K)) := by
      rw [onBob_mul]
      noncomm_ring
    _ = partialA (M*onBob (G*K*F)) := partialA_bob_cycle M F (G*K)

/-- A polynomial identity for the positive reconstruction filter. It also
holds for singular filters; no inverse is used in this lemma. -/
theorem center_filter_sandwich (b : V3) (F : Matrix Q Q ℂ)
    (hF : F*F = 1+spin b) :
    F*(1-spin b)*F = (((1-vSq b):ℝ):ℂ) • (1 : Matrix Q Q ℂ) := by
  have hs : spin b = F*F-1 := by rw [hF]; abel
  calc
    F*(1-spin b)*F = F*F+F*F-(F*F)*(F*F) := by
      rw [hs]
      noncomm_ring
    _ = 1-spin b*spin b := by rw [hF]; noncomm_ring
    _ = (((1-vSq b):ℝ):ℂ) • (1 : Matrix Q Q ℂ) := by
      rw [spin_squared]
      ext i j
      simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Complex.ofReal_sub,Complex.ofReal_one]
      ring

theorem center_scaled_qubit_coordinates (d : ℝ) (a c : V3)
    (h : (1/2:ℂ) • ((d:ℂ) • (1 : Matrix Q Q ℂ)+spin a) =
      (d:ℂ) • qubitState c) : a = d • c := by
  have h00 := congrArg Complex.re (congrFun (congrFun h (0:Q)) (0:Q))
  have h01r := congrArg Complex.re (congrFun (congrFun h (0:Q)) (1:Q))
  have h01i := congrArg Complex.im (congrFun (congrFun h (0:Q)) (1:Q))
  simp [qubitState,spin,Matrix.one_apply,Complex.mul_re,Complex.mul_im]
    at h00 h01r h01i
  norm_num at h00 h01r h01i
  have h0 : a 0 = d*c 0 := by nlinarith
  have h1 : a 1 = d*c 1 := by nlinarith
  have h2 : a 2 = d*c 2 := by nlinarith
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The numerator identity for every physical state with full-rank Bob
marginal. The only rank hypothesis concerns the two-dimensional marginal. -/
theorem canonicalize_center_numerator (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    geometryLocalA M-tVec (correlation M) (geometryLocalB M) =
      (1-vSq (geometryLocalB M)) • geometryLocalA (canonicalize M hM) := by
  let b := geometryLocalB M
  let F := bobFilter M hM
  let N := canonicalize M hM
  have hF : F*F = 1+spin b := by
    rw [bobFilter_sq,center_actual_partialB M hM]
    simp [b,qubitState,smul_smul]
  have hrec : onBob F*N*onBob F = M := canonicalize_reconstruction M hM hdet
  have hw : bobWeighted M (1-spin b) =
      (((1-vSq b):ℝ):ℂ) • partialA N := by
    rw [← hrec,center_weighted_congruence,center_filter_sandwich b F hF,
      bobWeighted_smul,bobWeighted_one]
  have hp := center_weighted_bloch (geometryLocalA M) b (correlation M)
  have hbloch : blochState (geometryLocalA M) b (correlation M) = M :=
    geometry_density_reconstruction M hM
  rw [hbloch,hw,center_actual_partialA N (canonicalize_density M hM hdet)] at hp
  exact center_scaled_qubit_coordinates (1-vSq b)
    (geometryLocalA M-tVec (correlation M) b) (geometryLocalA N) hp.symm

theorem center_denominator_ne_zero (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) : 1-vSq (geometryLocalB M) ≠ 0 := by
  intro hz
  apply hdet
  rw [center_actual_partialB M hM]
  simp only [qubitState,Matrix.det_smul,qubitBall_det]
  rw [hz]
  simp

/-- Exact vector formula in the original state's actual local and joint
Pauli expectations. This identifies the whitening definition with the
usual steering-ellipsoid centre formula. -/
theorem canonicalize_center_coordinates (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    geometryLocalA (canonicalize M hM) =
      (1-vSq (geometryLocalB M))⁻¹ •
        (geometryLocalA M-tVec (correlation M) (geometryLocalB M)) := by
  rw [canonicalize_center_numerator M hM hdet,smul_smul,
    inv_mul_cancel₀ (center_denominator_ne_zero M hM hdet),one_smul]

/-- The exact centre length appearing in the global F3 envelope is the
Euclidean length of the usual rational Bloch-coordinate formula. -/
theorem canonicalize_center_length_coordinates (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    center (canonicalize M hM) =
      Real.sqrt (vSq ((1-vSq (geometryLocalB M))⁻¹ •
        (geometryLocalA M-tVec (correlation M) (geometryLocalB M)))) := by
  unfold center
  rw [center_actual_partialA _ (canonicalize_density M hM hdet),
    qubitState_blochSq,canonicalize_center_coordinates M hM hdet]

/-- Agreement of the all-states centre definition with the usual formula
on precisely the branch where its denominator is nonzero. -/
theorem steeringCenter_coordinates (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    steeringCenter M hM =
      Real.sqrt (vSq ((1-vSq (geometryLocalB M))⁻¹ •
        (geometryLocalA M-tVec (correlation M) (geometryLocalB M)))) := by
  rw [steeringCenter_of_nonsingular M hM hdet,
    canonicalize_center_length_coordinates M hM hdet]

/-- The exact global F3 envelope directly in the original state's measured
Bloch coordinates, with no unproved representation assumption. -/
theorem coordinate_steering_bound (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0) :
    correlationSq M ≤ steeringEnvelopeSq
      (Real.sqrt (vSq ((1-vSq (geometryLocalB M))⁻¹ •
        (geometryLocalA M-tVec (correlation M) (geometryLocalB M))))) := by
  have h := all_states_steering_bound M hM
  rwa [steeringCenter_coordinates M hM hdet] at h

/-- The exact two-thirds non-violation threshold in actual Bloch coordinates.
The separately formalized pure-Bob branch requires no quotient formula. -/
theorem coordinate_steering_threshold (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det ≠ 0)
    (hc : 2/3 ≤ Real.sqrt (vSq ((1-vSq (geometryLocalB M))⁻¹ •
      (geometryLocalA M-tVec (correlation M) (geometryLocalB M))))) :
    correlationSq M ≤ 1 := by
  have h := coordinate_steering_bound M hM hdet
  rwa [steeringEnvelopeSq_eq_one hc] at h

end Milne

#print axioms Milne.canonicalize_center_numerator
#print axioms Milne.canonicalize_center_coordinates
#print axioms Milne.canonicalize_center_length_coordinates
#print axioms Milne.steeringCenter_coordinates
#print axioms Milne.coordinate_steering_bound
#print axioms Milne.coordinate_steering_threshold
