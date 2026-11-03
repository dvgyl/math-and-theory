import QuantumSingular
import Lean.Elab.Tactic.NormCast

/-!
# Success-normalized physical filtering

The preceding theorems fix filter scale by requiring the raw output trace
to be one.  This module proves equality with the usual conditional-state
definition: divide an arbitrary successful filter output by its success
probability.  The algebraic formula therefore optimizes the operational
one-sided filtered quantity, rather than merely a convenient normalization.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace FilteredF3

def quantumSuccess (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) : ℝ :=
  (Matrix.trace (Milne.complexFiltered M F)).re

def quantumNormalizedBob (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) :
    Milne.CMatrix :=
  (((quantumSuccess M F)⁻¹ : ℝ) : ℂ) • Milne.complexFiltered M F

def quantumNormalizedBobValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ, 0 < quantumSuccess M F ∧
    Milne.correlationSq (quantumNormalizedBob M F) = v}

theorem onBob_smul (z : ℂ) (F : Matrix Milne.Q Milne.Q ℂ) :
    Milne.onBob (z • F) = z • Milne.onBob F := by
  ext i j
  by_cases h : i.1 = j.1 <;> simp [Milne.onBob, h]

theorem complex_filtered_real_smul (M : Milne.CMatrix)
    (F : Matrix Milne.Q Milne.Q ℂ) (r : ℝ) :
    Milne.complexFiltered M ((r : ℂ) • F) =
      ((r^2 : ℝ) : ℂ) • Milne.complexFiltered M F := by
  simp only [Milne.complexFiltered, Matrix.conjTranspose_smul, onBob_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_pow, Complex.ofReal_mul, pow_two]

theorem complex_filtered_trace_real (M : Milne.CMatrix) (hM : Milne.Density M)
    (F : Matrix Milne.Q Milne.Q ℂ) :
    Matrix.trace (Milne.complexFiltered M F) = (quantumSuccess M F : ℂ) := by
  have hi := Milne.trace_mul_hermitian_im
    (Milne.complexFiltered_psd hM.1 F).1
    (Matrix.isHermitian_one : (1 : Milne.CMatrix).IsHermitian)
  simp only [Matrix.mul_one] at hi
  apply Complex.ext
  · rfl
  · simpa using hi

theorem quantumNormalizedBob_trace (M : Milne.CMatrix) (hM : Milne.Density M)
    (F : Matrix Milne.Q Milne.Q ℂ) (hp : 0 < quantumSuccess M F) :
    Matrix.trace (quantumNormalizedBob M F) = 1 := by
  rw [quantumNormalizedBob, Matrix.trace_smul, complex_filtered_trace_real M hM F]
  have hn : (quantumSuccess M F : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  simp [hn]

/-- An explicit scalar multiple of every successful filter realizes exactly
its normalized conditional state with unit raw trace. -/
theorem quantumNormalizedBob_realized (M : Milne.CMatrix)
    (F : Matrix Milne.Q Milne.Q ℂ) (hp : 0 < quantumSuccess M F) :
    Milne.complexFiltered M ((((Real.sqrt (quantumSuccess M F))⁻¹ : ℝ) : ℂ) • F) =
      quantumNormalizedBob M F := by
  rw [complex_filtered_real_smul, quantumNormalizedBob]
  have hs : ((Real.sqrt (quantumSuccess M F))⁻¹)^2 = (quantumSuccess M F)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt hp)]
  rw [hs]

theorem quantumNormalizedBob_density (M : Milne.CMatrix) (hM : Milne.Density M)
    (F : Matrix Milne.Q Milne.Q ℂ) (hp : 0 < quantumSuccess M F) :
    Milne.Density (quantumNormalizedBob M F) := by
  refine ⟨?_, quantumNormalizedBob_trace M hM F hp⟩
  rw [← quantumNormalizedBob_realized M F hp]
  exact Milne.complexFiltered_psd hM.1 _

theorem quantum_normalization_value_sets (M : Milne.CMatrix) (hM : Milne.Density M) :
    quantumNormalizedBobValues M = quantumBobValues M := by
  ext v
  constructor
  · rintro ⟨F, hp, hv⟩
    refine ⟨(((Real.sqrt (quantumSuccess M F))⁻¹ : ℝ) : ℂ) • F, ?_, ?_⟩
    · rw [quantumNormalizedBob_realized M F hp]
      exact quantumNormalizedBob_trace M hM F hp
    · rw [quantumNormalizedBob_realized M F hp]
      exact hv
  · rintro ⟨F, hTr, hv⟩
    have hp : quantumSuccess M F = 1 := by
      simp [quantumSuccess, hTr]
    refine ⟨F, by rw [hp]; norm_num, ?_⟩
    simpa [quantumNormalizedBob, hp] using hv

/-- Exact one-sided squared F3 optimum with the usual success-probability
normalization, for every two-qubit density matrix and every complex filter. -/
theorem closed_form_success_normalized_Bob (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsGreatest (quantumNormalizedBobValues M) (quantumBobExactValue M hM) := by
  rw [quantum_normalization_value_sets M hM]
  exact closed_form_all_quantum_Bob M hM

end FilteredF3
