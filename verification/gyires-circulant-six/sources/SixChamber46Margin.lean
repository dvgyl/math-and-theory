import SixChamber46Certificate
import SixMargin
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem chamber46_margin_coefficients : coeffsNonneg (sub SixC46S4OutputPolynomial marginPolynomial) = true := by
  decide +kernel

theorem chamber46_raw_margin (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 46) z)) rawDense := by
  have h := eval_nonneg_of_check (primeEvaluation primes z)
    (primeEvaluation_nonneg primes z hz) _ chamber46_margin_coefficients
  rw [eval_sub, eval_margin, chamber46_eval] at h
  exact sub_nonneg.mp h
#print axioms chamber46_raw_margin
end SixCertificates
