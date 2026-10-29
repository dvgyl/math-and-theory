module

public import MathAndTheory.Mathematics.Gyires.PermutationTransfer

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem two_pow_2 (d e f : ℝ) :
    transferTwo d e f ^ 2 =
      !![d^2 + e^2, d*e + e*f, d*f + e^2, d*f, e*f, f^2;
      d*e + e*f, e^2 + f^2, 0, e*f, 0, 0;
      d*f, e*f, 0, f^2, 0, 0;
      d*f + e^2, 0, e^2 + f^2, 0, e*f, 0;
      e*f, 0, e*f, 0, f^2, 0;
      f^2, 0, 0, 0, 0, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferTwo, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end MathAndTheory.Gyires.PermutationFinite
