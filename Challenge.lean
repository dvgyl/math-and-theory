module
public import Mathlib

/-! The exact envelope uses actual two-qubit density matrices, their Pauli
correlations, and their computed canonical steering centre. The threshold
concerns only the specified three-setting correlation expression. -/
@[expose] public section
open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
noncomputable section
namespace Milne

abbrev Q := Fin 2

abbrev QQ := Q × Q

abbrev CMatrix := Matrix QQ QQ ℂ

def partialA (M : CMatrix) : Matrix Q Q ℂ := fun i j => ∑ b, M (i,b) (j,b)

def partialB (M : CMatrix) : Matrix Q Q ℂ := fun i j => ∑ a, M (a,i) (a,j)

def Density (M : CMatrix) : Prop := M.PosSemidef ∧ Matrix.trace M = 1

def blochSq (A : Matrix Q Q ℂ) : ℝ :=
  (A 0 0).re ^ 2 - 2 * (A 0 0).re * (A 1 1).re + (A 1 1).re ^ 2 +
    4 * Complex.normSq (A 0 1)

noncomputable def center (M : CMatrix) : ℝ := Real.sqrt (blochSq (partialA M))

def onBob (F : Matrix Q Q ℂ) : CMatrix := fun i j => if i.1 = j.1 then F i.2 j.2 else 0

theorem partialB_psd {M : CMatrix} (hM : M.PosSemidef) : (partialB M).PosSemidef := by
  have h0 := hM.submatrix (fun i : Q => (0,i))
  have h1 := hM.submatrix (fun i : Q => (1,i))
  convert h0.add h1 using 1
  ext i j
  simp [partialB, Fin.sum_univ_two]

noncomputable def bobFilter (M : CMatrix) (hM : Density M) : Matrix Q Q ℂ :=
  ((partialB_psd hM.1).add (partialB_psd hM.1)).sqrt

noncomputable def canonicalize (M : CMatrix) (hM : Density M) : CMatrix :=
  onBob (bobFilter M hM)⁻¹ * M * onBob (bobFilter M hM)⁻¹

def pauliZ : Matrix Q Q ℂ := !![1, 0; 0, -1]

def pauli : Fin 3 → Matrix Q Q ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], pauliZ]

def pauliPair (i j : Fin 3) : CMatrix :=
  fun p q => pauli i p.1 q.1 * pauli j p.2 q.2

def correlation (M : CMatrix) (i j : Fin 3) : ℝ :=
  (Matrix.trace (M * pauliPair i j)).re

def correlationSq (M : CMatrix) : ℝ := ∑ i, ∑ j, correlation M i j ^ 2

def steeringDenominator (c : ℝ) : ℝ := 2-2*c-c^2

def steeringEnvelopeSq (c : ℝ) : ℝ :=
  if c ≤ 2/3 then 1+(2-3*c)^2 / steeringDenominator c else 1

def steeringCenter (M : CMatrix) (hM : Density M) : ℝ :=
  if (partialB M).det = 0 then center M else center (canonicalize M hM)

def steeringValue (M : CMatrix) : ℝ := Real.sqrt (correlationSq M)

def steeringSpectrum (c : ℝ) : Set ℝ :=
  {x | ∃ (M : CMatrix) (hM : Density M),
    steeringCenter M hM = c ∧ correlationSq M = x}

theorem steeringEnvelope_isLUB {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsLUB (steeringSpectrum c) (steeringEnvelopeSq c) := by
  sorry

theorem all_states_envelope_attained {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3) :
    steeringEnvelopeSq c ∈ steeringSpectrum c := by
  sorry

theorem no_maximizer_on_flat_branch (M : CMatrix) (hM : Density M)
    (hc : 2/3 ≤ steeringCenter M hM) (hc1 : steeringCenter M hM < 1) :
    correlationSq M < 1 := by
  sorry

theorem steeringEndpoint_isGreatest : IsGreatest (steeringSpectrum 1) 1 := by
  sorry

theorem three_setting_violation_possible_iff {c : ℝ} (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) :
    (∃ (M : CMatrix) (hM : Density M), steeringCenter M hM = c ∧
      1 < steeringValue M) ↔ c < 2/3 := by
  sorry

end Milne
