import SixStep4Semantics
import SixCertificateBase
namespace ChamberSix0
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem final_coefficients_nonneg : coeffsNonneg SixStep4OutputPolynomial = true := by
  decide +kernel

theorem chamber_eval (z : Fin 6 → ℝ) :
    eval (primeEvaluation primes z) SixStep4OutputPolynomial =
      eval (primeEvaluation primes (SixCertificates.prefixVector (fun i => i) z))
        SixStep0InputPolynomial := by
  dsimp only [SixCertificates.prefixVector]
  rw [step4_eval, step3_eval, step2_eval, step1_eval, step0_eval]

theorem chamber_raw_nonneg (z : Fin 6 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ eval (primeEvaluation primes (SixCertificates.prefixVector (fun i => i) z))
      SixStep0InputPolynomial := by
  rw [← chamber_eval]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ final_coefficients_nonneg

#print axioms chamber_eval
#print axioms chamber_raw_nonneg
end ChamberSix0
