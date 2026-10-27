module

public import MathAndTheory.Mathematics.Gyires.PermutationTransfer

@[expose] public section

namespace MathAndTheory.Gyires.PermutationFinite

open Matrix PermutationTransfer
open scoped BigOperators Matrix

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem one_pow_2 (d e f : ℝ) :
    transferOne d e f ^ 2 =
      !![d*f + e^2, d*e + e*f, e^2 + f^2, e*f;
      e*f, d*f, e*f, f^2;
      f^2, 0, 0, 0;
      0, f^2, 0, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transferOne, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end MathAndTheory.Gyires.PermutationFinite
