import SixChamberZeroCertificate
import SixRawDense
import SixMargin
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem chamber0_margin_coefficients :
    coeffsNonneg (sub ChamberSix0.SixStep4OutputPolynomial marginPolynomial) = true := by
  decide +kernel

theorem chamber0_raw_margin (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    42624 * gapPowerSum z ≤ eval (primeEvaluation primes (prefixVector (fun i => i) z)) rawDense := by
  have h := eval_nonneg_of_check (primeEvaluation primes z)
    (primeEvaluation_nonneg primes z hz) _ chamber0_margin_coefficients
  rw [eval_sub, eval_margin] at h
  have hc := ChamberSix0.chamber_eval z
  change eval (primeEvaluation primes z) ChamberSix0.SixStep4OutputPolynomial =
    eval (primeEvaluation primes (prefixVector (fun i => i) z)) rawDense at hc
  rw [hc] at h
  exact sub_nonneg.mp h
#print axioms chamber0_raw_margin
end SixCertificates
