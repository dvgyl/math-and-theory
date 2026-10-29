module
public import ADChannel
public import TraceNormBounds


@[expose] public section

open Matrix
open scoped Matrix ComplexOrder

namespace ADSeparation
noncomputable section

abbrev TrivialReference := Fin 1 × Q
abbrev SharpMat := CMat TrivialReference TrivialReference

/-- The ordinary qubit states |+><+| and |-><-|, with a one-dimensional reference. -/
def sharpPlus : SharpMat := fun _ _ => (1/2 : ℂ)
def sharpMinus : SharpMat := fun i j => if i.2 = j.2 then (1/2 : ℂ) else -(1/2 : ℂ)
def sharpDifference : SharpMat := sharpPlus - sharpMinus

theorem sharpPlus_hermitian : sharpPlus.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  norm_num [Prod.ext_iff, sharpPlus, Complex.star_def, map_ofNat]

theorem sharpMinus_hermitian : sharpMinus.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : i.2 = j.2
  · simp [sharpMinus, h, Complex.star_def, map_ofNat]
  · simp [sharpMinus, h, Ne.symm h, Complex.star_def, map_ofNat]

theorem sharpPlus_idempotent : sharpPlus * sharpPlus = sharpPlus := by
  ext i j
  norm_num [Prod.ext_iff, sharpPlus, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem sharpMinus_idempotent : sharpMinus * sharpMinus = sharpMinus := by
  ext ⟨i,q⟩ ⟨j,r⟩
  fin_cases q <;> fin_cases r <;>
    norm_num [Prod.ext_iff, sharpMinus, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem sharpPlus_positive : sharpPlus.PosSemidef := by
  apply CMICounterexample.flat_posSemidef sharpPlus sharpPlus_hermitian 1 (by norm_num)
  simpa using sharpPlus_idempotent

theorem sharpMinus_positive : sharpMinus.PosSemidef := by
  apply CMICounterexample.flat_posSemidef sharpMinus sharpMinus_hermitian 1 (by norm_num)
  simpa using sharpMinus_idempotent

theorem sharpPlus_trace : sharpPlus.trace = 1 := by
  norm_num [Prod.ext_iff, sharpPlus, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem sharpMinus_trace : sharpMinus.trace = 1 := by
  norm_num [Prod.ext_iff, sharpMinus, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem sharp_reference_equal : partialTraceQ sharpPlus = partialTraceQ sharpMinus := by
  ext i j
  norm_num [Prod.ext_iff, partialTraceQ, sharpPlus, sharpMinus, Fin.sum_univ_succ]

theorem sharpDifference_hermitian : sharpDifference.IsHermitian :=
  sharpPlus_hermitian.sub sharpMinus_hermitian

theorem sharpDifference_square : sharpDifference * sharpDifference = (1 : SharpMat) := by
  ext ⟨i,q⟩ ⟨j,r⟩
  fin_cases i
  all_goals fin_cases j
  all_goals fin_cases q
  all_goals fin_cases r
  all_goals norm_num [Prod.ext_iff, sharpDifference, sharpPlus, sharpMinus, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem sharp_input_norm : CMICounterexample.traceNorm sharpDifference sharpDifference_hermitian = 2 := by
  have hs : sharpDifference * sharpDifference = (1:ℝ)^2 • (1 : SharpMat) := by
    simpa using sharpDifference_square
  rw [CMICounterexample.traceNorm_of_square_scalar sharpDifference sharpDifference_hermitian
    1 (by norm_num) hs]
  norm_num [Prod.ext_iff, TrivialReference, Q]

theorem sharp_output_action : adAmplified sharpDifference = (1/2 : ℝ) • sharpDifference := by
  ext ⟨i,q⟩ ⟨j,r⟩
  fin_cases q <;> fin_cases r <;>
    norm_num [Prod.ext_iff, adAmplified, adChannel, sharpDifference, sharpPlus, sharpMinus,
      Matrix.smul_apply, Complex.real_smul]

theorem sharp_output_norm :
    CMICounterexample.traceNorm (adAmplified sharpDifference)
      (adAmplified_hermitian _ sharpDifference_hermitian) = 1 := by
  have h := CMICounterexample.traceNorm_real_smul sharpDifference sharpDifference_hermitian
    (1/2) (by norm_num)
  simpa only [← sharp_output_action, sharp_input_norm, show (1/2:ℝ)*2=1 by norm_num] using h

end
end ADSeparation
