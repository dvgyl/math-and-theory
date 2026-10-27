import SixChamber06Certificate
import SixMargin
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem chamber6_margin_coefficients : coeffsNonneg (sub SixC06S4OutputPolynomial marginPolynomial) = true := by
  decide +kernel

theorem chamber6_raw_margin (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 6) z)) rawDense := by
  have h := eval_nonneg_of_check (primeEvaluation primes z)
    (primeEvaluation_nonneg primes z hz) _ chamber6_margin_coefficients
  rw [eval_sub, eval_margin, chamber6_eval] at h
  exact sub_nonneg.mp h
#print axioms chamber6_raw_margin
end SixCertificates
