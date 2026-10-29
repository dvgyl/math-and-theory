import SixChamber02Certificate
import SixMargin
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem chamber2_margin_coefficients : coeffsNonneg (sub SixC02S4OutputPolynomial marginPolynomial) = true := by
  decide +kernel

theorem chamber2_raw_margin (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (AffineCoverSix.representative 2) z)) rawDense := by
  have h := eval_nonneg_of_check (primeEvaluation primes z)
    (primeEvaluation_nonneg primes z hz) _ chamber2_margin_coefficients
  rw [eval_sub, eval_margin, chamber2_eval] at h
  exact sub_nonneg.mp h
#print axioms chamber2_raw_margin
end SixCertificates
