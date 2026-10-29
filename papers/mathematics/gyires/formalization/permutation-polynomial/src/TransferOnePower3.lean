module

public import TransferOnePower2

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem one_pow_3 (d e f : ℝ) :
    transferOne d e f ^ 3 =
      !![2*d*e*f + e^3 + e*f^2, d^2*f + d*e^2 + e^2*f + f^3, d*e*f + e^3 + e*f^2, d*f^2 + e^2*f;
      d*f^2 + e^2*f, d*e*f + e*f^2, e^2*f + f^3, e*f^2;
      e*f^2, d*f^2, e*f^2, f^3;
      f^3, 0, 0, 0] := by
  rw [pow_succ, one_pow_2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferOne, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end MathAndTheory.Gyires.PermutationFinite
