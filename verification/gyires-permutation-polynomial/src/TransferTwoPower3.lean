module

public import TransferTwoPower2

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem two_pow_3 (d e f : ℝ) :
    transferTwo d e f ^ 3 =
      !![d^3 + 2*d*e^2 + d*f^2 + 2*e^2*f, d^2*e + d*e*f + e^3 + e*f^2, d^2*f + d*e^2 + e^2*f + f^3, d^2*f + e^2*f, d*e*f + e*f^2, d*f^2;
      d^2*e + d*e*f + e^3 + e*f^2, d*e^2 + 2*e^2*f, d*e*f + e^3 + e*f^2, d*e*f + e*f^2, e^2*f + f^3, e*f^2;
      d^2*f + e^2*f, d*e*f + e*f^2, d*f^2 + e^2*f, d*f^2, e*f^2, f^3;
      d^2*f + d*e^2 + e^2*f + f^3, d*e*f + e^3 + e*f^2, 0, d*f^2 + e^2*f, 0, 0;
      d*e*f + e*f^2, e^2*f + f^3, 0, e*f^2, 0, 0;
      d*f^2, e*f^2, 0, f^3, 0, 0] := by
  rw [pow_succ, two_pow_2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferTwo, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end MathAndTheory.Gyires.PermutationFinite
