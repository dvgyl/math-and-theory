module

public import TransferTwoPower5

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem two_pow_6 (d e f : ℝ) :
    transferTwo d e f ^ 6 =
      !![d^6 + 5*d^4*e^2 + 4*d^4*f^2 + 8*d^3*e^2*f + 6*d^2*e^4 + 12*d^2*e^2*f^2 + 4*d^2*f^4 + 12*d*e^4*f + 8*d*e^2*f^3 + e^6 + 8*e^4*f^2 + 4*e^2*f^4, d^5*e + d^4*e*f + 4*d^3*e^3 + 4*d^3*e*f^2 + 9*d^2*e^3*f + 3*d^2*e*f^3 + 3*d*e^5 + 12*d*e^3*f^2 + 4*d*e*f^4 + 5*e^5*f + 7*e^3*f^3 + 2*e*f^5, d^5*f + d^4*e^2 + 4*d^3*e^2*f + 3*d^3*f^3 + 3*d^2*e^4 + 7*d^2*e^2*f^2 + 7*d*e^4*f + 6*d*e^2*f^3 + 2*d*f^5 + e^6 + 5*e^4*f^2 + 4*e^2*f^4, d^5*f + 4*d^3*e^2*f + 3*d^3*f^3 + 6*d^2*e^2*f^2 + 3*d*e^4*f + 6*d*e^2*f^3 + 2*d*f^5 + 4*e^4*f^2 + 2*e^2*f^4, d^4*e*f + d^3*e*f^2 + 3*d^2*e^3*f + 3*d^2*e*f^3 + 6*d*e^3*f^2 + 2*d*e*f^4 + e^5*f + 5*e^3*f^3 + 2*e*f^5, d^4*f^2 + 3*d^2*e^2*f^2 + 2*d^2*f^4 + 4*d*e^2*f^3 + e^4*f^2 + 2*e^2*f^4 + f^6;
      d^5*e + d^4*e*f + 4*d^3*e^3 + 4*d^3*e*f^2 + 9*d^2*e^3*f + 3*d^2*e*f^3 + 3*d*e^5 + 12*d*e^3*f^2 + 4*d*e*f^4 + 5*e^5*f + 7*e^3*f^3 + 2*e*f^5, d^4*e^2 + 2*d^3*e^2*f + 3*d^2*e^4 + 5*d^2*e^2*f^2 + 8*d*e^4*f + 6*d*e^2*f^3 + e^6 + 9*e^4*f^2 + 6*e^2*f^4 + f^6, d^4*e*f + d^3*e^3 + d^3*e*f^2 + 4*d^2*e^3*f + 3*d^2*e*f^3 + 2*d*e^5 + 7*d*e^3*f^2 + 2*d*e*f^4 + 4*e^5*f + 5*e^3*f^3 + e*f^5, d^4*e*f + d^3*e*f^2 + 3*d^2*e^3*f + 3*d^2*e*f^3 + 6*d*e^3*f^2 + 2*d*e*f^4 + e^5*f + 5*e^3*f^3 + 2*e*f^5, d^3*e^2*f + 2*d^2*e^2*f^2 + 2*d*e^4*f + 4*d*e^2*f^3 + 4*e^4*f^2 + 4*e^2*f^4, d^3*e*f^2 + d^2*e*f^3 + 2*d*e^3*f^2 + 2*d*e*f^4 + 3*e^3*f^3 + e*f^5;
      d^5*f + 4*d^3*e^2*f + 3*d^3*f^3 + 6*d^2*e^2*f^2 + 3*d*e^4*f + 6*d*e^2*f^3 + 2*d*f^5 + 4*e^4*f^2 + 2*e^2*f^4, d^4*e*f + d^3*e*f^2 + 3*d^2*e^3*f + 3*d^2*e*f^3 + 6*d*e^3*f^2 + 2*d*e*f^4 + e^5*f + 5*e^3*f^3 + 2*e*f^5, d^4*f^2 + d^3*e^2*f + 3*d^2*e^2*f^2 + 2*d^2*f^4 + 2*d*e^4*f + 4*d*e^2*f^3 + 3*e^4*f^2 + 2*e^2*f^4, d^4*f^2 + 3*d^2*e^2*f^2 + 2*d^2*f^4 + 4*d*e^2*f^3 + e^4*f^2 + 2*e^2*f^4 + f^6, d^3*e*f^2 + d^2*e*f^3 + 2*d*e^3*f^2 + 2*d*e*f^4 + 3*e^3*f^3 + e*f^5, d^3*f^3 + 2*d*e^2*f^3 + d*f^5 + 2*e^2*f^4;
      d^5*f + d^4*e^2 + 4*d^3*e^2*f + 3*d^3*f^3 + 3*d^2*e^4 + 7*d^2*e^2*f^2 + 7*d*e^4*f + 6*d*e^2*f^3 + 2*d*f^5 + e^6 + 5*e^4*f^2 + 4*e^2*f^4, d^4*e*f + d^3*e^3 + d^3*e*f^2 + 4*d^2*e^3*f + 3*d^2*e*f^3 + 2*d*e^5 + 7*d*e^3*f^2 + 2*d*e*f^4 + 4*e^5*f + 5*e^3*f^3 + e*f^5, d^4*f^2 + 2*d^3*e^2*f + d^2*e^4 + 3*d^2*e^2*f^2 + 2*d^2*f^4 + 4*d*e^4*f + 4*d*e^2*f^3 + e^6 + 3*e^4*f^2 + 3*e^2*f^4 + f^6, d^4*f^2 + d^3*e^2*f + 3*d^2*e^2*f^2 + 2*d^2*f^4 + 2*d*e^4*f + 4*d*e^2*f^3 + 3*e^4*f^2 + 2*e^2*f^4, d^3*e*f^2 + d^2*e^3*f + d^2*e*f^3 + 3*d*e^3*f^2 + 2*d*e*f^4 + e^5*f + 3*e^3*f^3 + 2*e*f^5, d^3*f^3 + d^2*e^2*f^2 + 2*d*e^2*f^3 + d*f^5 + e^4*f^2 + e^2*f^4;
      d^4*e*f + d^3*e*f^2 + 3*d^2*e^3*f + 3*d^2*e*f^3 + 6*d*e^3*f^2 + 2*d*e*f^4 + e^5*f + 5*e^3*f^3 + 2*e*f^5, d^3*e^2*f + 2*d^2*e^2*f^2 + 2*d*e^4*f + 4*d*e^2*f^3 + 4*e^4*f^2 + 4*e^2*f^4, d^3*e*f^2 + d^2*e^3*f + d^2*e*f^3 + 3*d*e^3*f^2 + 2*d*e*f^4 + e^5*f + 3*e^3*f^3 + 2*e*f^5, d^3*e*f^2 + d^2*e*f^3 + 2*d*e^3*f^2 + 2*d*e*f^4 + 3*e^3*f^3 + e*f^5, d^2*e^2*f^2 + 2*d*e^2*f^3 + e^4*f^2 + 3*e^2*f^4 + f^6, d^2*e*f^3 + d*e*f^4 + e^3*f^3 + e*f^5;
      d^4*f^2 + 3*d^2*e^2*f^2 + 2*d^2*f^4 + 4*d*e^2*f^3 + e^4*f^2 + 2*e^2*f^4 + f^6, d^3*e*f^2 + d^2*e*f^3 + 2*d*e^3*f^2 + 2*d*e*f^4 + 3*e^3*f^3 + e*f^5, d^3*f^3 + d^2*e^2*f^2 + 2*d*e^2*f^3 + d*f^5 + e^4*f^2 + e^2*f^4, d^3*f^3 + 2*d*e^2*f^3 + d*f^5 + 2*e^2*f^4, d^2*e*f^3 + d*e*f^4 + e^3*f^3 + e*f^5, d^2*f^4 + e^2*f^4] := by
  rw [pow_succ, two_pow_5]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferTwo, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end MathAndTheory.Gyires.PermutationFinite
