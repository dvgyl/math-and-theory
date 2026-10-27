import HS.CertificateData
import HS.ExactPolynomial
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith

open scoped BigOperators ComplexConjugate
namespace HS
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Semantically stated exact certificate in an arbitrary commutative ring. -/
theorem certificate_identity {R : Type*} [CommRing R] (x y : Fin 16 → R) :
    400 * (∑ i : Fin 16, x i * y i) ^ 3 -
      2880 * (∑ cut : Fin 3, ∑ r : Fin 4, ∑ c : Fin 4,
        minor3 (flatten cut x) r c * minor3 (flatten cut y) r c) =
    weightedProduct sosData x y := by
  exact polynomial_identity x y

/-- Exact real sum-of-squares identity on all complex sixteen-dimensional vectors. -/
theorem certificate_identity_real (z : Fin 16 → ℂ) :
    400 * stateNormSq z ^ 3 - 2880 * minorSum z = weightedSOS sosData z := by
  have h := certificate_identity z (conjugateState z)
  have hn : (∑ i : Fin 16, z i * conjugateState z i) = (stateNormSq z : ℂ) := by
    simp [conjugateState, stateNormSq, Complex.mul_conj]
  have hm : (∑ cut : Fin 3, ∑ r : Fin 4, ∑ c : Fin 4,
        minor3 (flatten cut z) r c * minor3 (flatten cut (conjugateState z)) r c) =
      (minorSum z : ℂ) := by
    simp [minorSum, minor3_conjugate, Complex.mul_conj]
  rw [hn, hm, weightedProduct_eq_sos] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using h

/-- Homogeneous bound, without normalization or a restriction to a special state family. -/
theorem minorSum_le (z : Fin 16 → ℂ) :
    minorSum z ≤ (5 / 36 : ℝ) * stateNormSq z ^ 3 := by
  have hi := certificate_identity_real z
  have hp := weightedSOS_nonneg sosData z
  linarith

/-- Universal normalized third-minor bound. -/
theorem minorSum_le_of_normalized (z : Fin 16 → ℂ) (hz : stateNormSq z = 1) :
    minorSum z ≤ (5 / 36 : ℝ) := by
  simpa [hz] using minorSum_le z

end HS
