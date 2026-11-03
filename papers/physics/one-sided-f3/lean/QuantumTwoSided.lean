import QuantumNormalization

/-!
# Both one-sided filtered quantities

The Alice result is transported by the explicit swap of the two finite
qubit indices.  Positivity, trace, actual filtering, and the Frobenius
correlation norm are proved invariant under this swap; no symmetry premise
on the original state is imposed.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace FilteredF3

def quantumSwap (M : Milne.CMatrix) : Milne.CMatrix :=
  M.submatrix Prod.swap Prod.swap

theorem quantumSwap_involutive (M : Milne.CMatrix) :
    quantumSwap (quantumSwap M) = M := by
  ext i j
  rfl

theorem quantumSwap_trace (M : Milne.CMatrix) :
    Matrix.trace (quantumSwap M) = Matrix.trace M := by
  simp only [quantumSwap, Matrix.trace, Matrix.diag, Matrix.submatrix_apply,
    Fintype.sum_prod_type, Prod.swap_prod_mk]
  rw [Finset.sum_comm]

theorem quantumSwap_density (M : Milne.CMatrix) (hM : Milne.Density M) :
    Milne.Density (quantumSwap M) := by
  refine ⟨hM.1.submatrix Prod.swap, ?_⟩
  rw [quantumSwap_trace]
  exact hM.2

theorem quantumSwap_mul (M N : Milne.CMatrix) :
    quantumSwap (M*N) = quantumSwap M * quantumSwap N := by
  ext i j
  simp only [quantumSwap, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Prod.swap_prod_mk]
  rw [Finset.sum_comm]

theorem quantumSwap_onAlice (F : Matrix Milne.Q Milne.Q ℂ) :
    quantumSwap (Milne.onAlice F) = Milne.onBob F := by
  ext i j
  simp [quantumSwap, Milne.onAlice, Milne.onBob]

theorem quantumSwap_partialB (M : Milne.CMatrix) :
    Milne.partialB (quantumSwap M) = Milne.partialA M := by
  ext i j
  rfl

theorem quantumSwap_partialA (M : Milne.CMatrix) :
    Milne.partialA (quantumSwap M) = Milne.partialB M := by
  ext i j
  rfl

theorem quantumSwap_pauliPair (i j : Fin 3) :
    quantumSwap (Milne.pauliPair i j) = Milne.pauliPair j i := by
  ext a b
  simp [quantumSwap, Milne.pauliPair, mul_comm]

theorem quantumSwap_correlation (M : Milne.CMatrix) (i j : Fin 3) :
    Milne.correlation (quantumSwap M) i j = Milne.correlation M j i := by
  unfold Milne.correlation
  rw [← quantumSwap_pauliPair j i, ← quantumSwap_mul, quantumSwap_trace]

theorem quantumSwap_correlationSq (M : Milne.CMatrix) :
    Milne.correlationSq (quantumSwap M) = Milne.correlationSq M := by
  simp only [Milne.correlationSq, quantumSwap_correlation]
  rw [Finset.sum_comm]

def quantumAliceFiltered (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) :
    Milne.CMatrix := Milne.onAlice F * M * Milne.onAlice Fᴴ

theorem quantumSwap_aliceFiltered (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) :
    quantumSwap (quantumAliceFiltered M F) = Milne.complexFiltered (quantumSwap M) F := by
  simp only [quantumAliceFiltered, quantumSwap_mul, quantumSwap_onAlice,
    Milne.complexFiltered]

def quantumAliceValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ,
    Matrix.trace (quantumAliceFiltered M F) = 1 ∧
    Milne.correlationSq (quantumAliceFiltered M F) = v}

theorem quantumAlice_values_swap (M : Milne.CMatrix) :
    quantumAliceValues M = quantumBobValues (quantumSwap M) := by
  ext v
  simp only [quantumAliceValues, quantumBobValues, Set.mem_setOf_eq,
    ← quantumSwap_aliceFiltered, quantumSwap_trace, quantumSwap_correlationSq]

def quantumAliceExactValue (M : Milne.CMatrix) (hM : Milne.Density M) : ℝ :=
  quantumBobExactValue (quantumSwap M) (quantumSwap_density M hM)

theorem closed_form_all_quantum_Alice (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsGreatest (quantumAliceValues M) (quantumAliceExactValue M hM) := by
  rw [quantumAlice_values_swap]
  exact closed_form_all_quantum_Bob (quantumSwap M) (quantumSwap_density M hM)

def quantumAliceSuccess (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) : ℝ :=
  (Matrix.trace (quantumAliceFiltered M F)).re

def quantumNormalizedAlice (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) :
    Milne.CMatrix := (((quantumAliceSuccess M F)⁻¹ : ℝ) : ℂ) • quantumAliceFiltered M F

def quantumNormalizedAliceValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ, 0 < quantumAliceSuccess M F ∧
    Milne.correlationSq (quantumNormalizedAlice M F) = v}

theorem quantumSwap_smul (M : Milne.CMatrix) (z : ℂ) :
    quantumSwap (z • M) = z • quantumSwap M := by
  rfl

theorem quantumAlice_success_swap (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) :
    quantumAliceSuccess M F = quantumSuccess (quantumSwap M) F := by
  rw [quantumAliceSuccess, quantumSuccess, ← quantumSwap_aliceFiltered, quantumSwap_trace]

theorem quantumNormalizedAlice_swap (M : Milne.CMatrix) (F : Matrix Milne.Q Milne.Q ℂ) :
    quantumSwap (quantumNormalizedAlice M F) = quantumNormalizedBob (quantumSwap M) F := by
  rw [quantumNormalizedAlice, quantumSwap_smul, quantumSwap_aliceFiltered,
    quantumAlice_success_swap]
  rfl

theorem quantumNormalizedAlice_values_swap (M : Milne.CMatrix) :
    quantumNormalizedAliceValues M = quantumNormalizedBobValues (quantumSwap M) := by
  ext v
  simp only [quantumNormalizedAliceValues, quantumNormalizedBobValues, Set.mem_setOf_eq,
    ← quantumNormalizedAlice_swap, quantumSwap_correlationSq, quantumAlice_success_swap]

/-- Both one-sided formulas simultaneously, with the usual division by the
success probability.  There are no marginal-rank or state-rank restrictions. -/
theorem closed_form_both_success_normalized (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsGreatest (quantumNormalizedAliceValues M) (quantumAliceExactValue M hM) ∧
    IsGreatest (quantumNormalizedBobValues M) (quantumBobExactValue M hM) := by
  constructor
  · rw [quantumNormalizedAlice_values_swap]
    exact closed_form_success_normalized_Bob (quantumSwap M) (quantumSwap_density M hM)
  · exact closed_form_success_normalized_Bob M hM

end FilteredF3
