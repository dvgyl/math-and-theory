import RawSixPart75
import SixEvaluationBridge
import SixRawDense
import CirculantSixPolynomial
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
open MathAndTheory.Gyires.CirculantCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem raw_dense_checked : prune rawDense = RawSix.g1502 := by
  apply same_sound
  decide +kernel

theorem permanent_formula (w : Fin 6 → ℝ) : (circulant w).permanent = RawSix.P6 w := by
  exact MathAndTheory.Gyires.CirculantSix.permanent_matrix w

theorem raw_deficit_eval (w : Fin 6 → ℝ) :
    eval (primeEvaluation primes w) rawDense =
      46656 * (circulant w).permanent ^ 2 -
        720 * (circulant w * (circulant w).transpose).permanent := by
  rw [← eval_prune, raw_dense_checked, RawSix.deficit_eval,
    RawSix.eval_p6, RawSix.eval_gram]
  change 46656 * RawSix.P6 ![primeEvaluation RawSix.primes w 2,
    primeEvaluation RawSix.primes w 3, primeEvaluation RawSix.primes w 5,
    primeEvaluation RawSix.primes w 7, primeEvaluation RawSix.primes w 11,
    primeEvaluation RawSix.primes w 13] ^ 2 -
    720 * RawSix.P6 (RawSix.gram6 ![primeEvaluation RawSix.primes w 2,
    primeEvaluation RawSix.primes w 3, primeEvaluation RawSix.primes w 5,
    primeEvaluation RawSix.primes w 7, primeEvaluation RawSix.primes w 11,
    primeEvaluation RawSix.primes w 13]) = _
  rw [RawSix.prime_values, permanent_formula, RawSix.matrix_gram, permanent_formula]

#print axioms raw_deficit_eval
end SixCertificates
