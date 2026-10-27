module

public import TransferTwoPower3

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem two_pow_4 (d e f : ℝ) :
    transferTwo d e f ^ 4 =
      !![d^4 + 3*d^2*e^2 + 2*d^2*f^2 + 4*d*e^2*f + e^4 + 2*e^2*f^2 + f^4, d^3*e + d^2*e*f + 2*d*e^3 + 2*d*e*f^2 + 3*e^3*f + e*f^3, d^3*f + d^2*e^2 + 2*d*e^2*f + d*f^3 + e^4 + e^2*f^2, d^3*f + 2*d*e^2*f + d*f^3 + 2*e^2*f^2, d^2*e*f + d*e*f^2 + e^3*f + e*f^3, d^2*f^2 + e^2*f^2;
      d^3*e + d^2*e*f + 2*d*e^3 + 2*d*e*f^2 + 3*e^3*f + e*f^3, d^2*e^2 + 2*d*e^2*f + e^4 + 3*e^2*f^2 + f^4, d^2*e*f + d*e^3 + d*e*f^2 + 2*e^3*f + e*f^3, d^2*e*f + d*e*f^2 + e^3*f + e*f^3, d*e^2*f + 2*e^2*f^2, d*e*f^2 + e*f^3;
      d^3*f + 2*d*e^2*f + d*f^3 + 2*e^2*f^2, d^2*e*f + d*e*f^2 + e^3*f + e*f^3, d^2*f^2 + d*e^2*f + e^2*f^2 + f^4, d^2*f^2 + e^2*f^2, d*e*f^2 + e*f^3, d*f^3;
      d^3*f + d^2*e^2 + 2*d*e^2*f + d*f^3 + e^4 + e^2*f^2, d^2*e*f + d*e^3 + d*e*f^2 + 2*e^3*f + e*f^3, d^2*f^2 + 2*d*e^2*f + e^4 + e^2*f^2, d^2*f^2 + d*e^2*f + e^2*f^2 + f^4, d*e*f^2 + e^3*f + e*f^3, d*f^3 + e^2*f^2;
      d^2*e*f + d*e*f^2 + e^3*f + e*f^3, d*e^2*f + 2*e^2*f^2, d*e*f^2 + e^3*f + e*f^3, d*e*f^2 + e*f^3, e^2*f^2 + f^4, e*f^3;
      d^2*f^2 + e^2*f^2, d*e*f^2 + e*f^3, d*f^3 + e^2*f^2, d*f^3, e*f^3, f^4] := by
  rw [pow_succ, two_pow_3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferTwo, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end MathAndTheory.Gyires.PermutationFinite
