import SixChamber10Certificate
import SixMargin
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem chamber10_margin_coefficients : coeffsNonneg (sub SixC10S4OutputPolynomial marginPolynomial) = true := by
  decide +kernel

theorem chamber10_raw_margin (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 10) z)) rawDense := by
  have h := eval_nonneg_of_check (primeEvaluation primes z)
    (primeEvaluation_nonneg primes z hz) _ chamber10_margin_coefficients
  rw [eval_sub, eval_margin, chamber10_eval] at h
  exact sub_nonneg.mp h
#print axioms chamber10_raw_margin
end SixCertificates
