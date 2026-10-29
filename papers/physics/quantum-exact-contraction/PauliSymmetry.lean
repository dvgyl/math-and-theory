import PauliChannel
import UnitaryCoefficient

/-! Every ordered pair of distinct Pauli labels can be moved to labels zero
and three by actual unitary preprocessing and postprocessing. The construction
preserves the complete conditional ratio set at every real parameter. -/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace PauliSymmetry
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000
abbrev Q := Fin 2

def shiftIndex (a i : Fin 4) : Fin 4 :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] a i

theorem shiftIndex_involutive (a i : Fin 4) : shiftIndex a (shiftIndex a i) = i := by
  fin_cases a <;> fin_cases i <;> rfl

def shift (a : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := shiftIndex a
  invFun := shiftIndex a
  left_inv := shiftIndex_involutive a
  right_inv := shiftIndex_involutive a

def axisIndex (c i : Fin 4) : Fin 4 :=
  ![![0,1,2,3], ![0,3,2,1], ![0,1,3,2], ![0,1,2,3]] c i

theorem axisIndex_involutive (c i : Fin 4) : axisIndex c (axisIndex c i) = i := by
  fin_cases c <;> fin_cases i <;> rfl

def axis (c : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := axisIndex c
  invFun := axisIndex c
  left_inv := axisIndex_involutive c
  right_inv := axisIndex_involutive c

/-- Global phases make both nontrivial Clifford matrices rational over Q(i). -/
def rotate (c : Fin 4) : Matrix Q Q ℂ :=
  ![1,
    !![(1+Complex.I)/2, (1+Complex.I)/2;
       (1+Complex.I)/2, -(1+Complex.I)/2],
    !![(1+Complex.I)/2, (1-Complex.I)/2;
       (1-Complex.I)/2, (1+Complex.I)/2],
    1] c

theorem rotate_unitary (c : Fin 4) : (rotate c)ᴴ * rotate c = 1 := by
  fin_cases c <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [rotate, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.star_def, Matrix.one_apply, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, map_ofNat]

theorem rotate_unitary_right (c : Fin 4) : rotate c * (rotate c)ᴴ = 1 := by
  fin_cases c <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [rotate, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.star_def, Matrix.one_apply, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, map_ofNat]

theorem linear_shift (w : Fin 4 → ℝ) (a : Fin 4) (X : Matrix Q Q ℂ) :
    PauliChannel.linear (fun i => w (shiftIndex a i)) X =
      (PauliChannel.pauli a)ᴴ * PauliChannel.linear w X * PauliChannel.pauli a := by
  rw [PauliChannel.map_entries, PauliChannel.map_entries]
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [shiftIndex, PauliChannel.pauli, ADSeparation.pauliX,
      ADSeparation.pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.star_def, Matrix.one_apply] <;> push_cast <;> ring

theorem linear_axis (w : Fin 4 → ℝ) (c : Fin 4) (X : Matrix Q Q ℂ) :
    PauliChannel.linear (fun i => w (axisIndex c i)) X =
      rotate c * PauliChannel.linear w ((rotate c)ᴴ * X * rotate c) * (rotate c)ᴴ := by
  rw [PauliChannel.map_entries, PauliChannel.map_entries]
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [axisIndex, rotate, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.star_def, Matrix.one_apply, map_ofNat] <;>
    push_cast <;> ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, map_ofNat] <;> ring

def normalizingEquiv (a b : Fin 4) : Equiv.Perm (Fin 4) :=
  (shift a).trans (axis (shiftIndex a b))

theorem normalizingEquiv_apply_left (a b : Fin 4) : normalizingEquiv a b a = 0 := by
  fin_cases a <;> fin_cases b <;> rfl

theorem normalizingEquiv_apply_right (a b : Fin 4) (hab : a ≠ b) :
    normalizingEquiv a b b = 3 := by
  fin_cases a <;> fin_cases b <;> first | contradiction | rfl

theorem normalizingEquiv_symm_zero (a b : Fin 4) :
    (normalizingEquiv a b).symm 0 = a := by
  apply (normalizingEquiv a b).injective
  simp only [Equiv.apply_symm_apply, normalizingEquiv_apply_left]

theorem normalizingEquiv_symm_three (a b : Fin 4) (hab : a ≠ b) :
    (normalizingEquiv a b).symm 3 = b := by
  apply (normalizingEquiv a b).injective
  simp only [Equiv.apply_symm_apply, normalizingEquiv_apply_right a b hab]

def inputUnitary (a b : Fin 4) : Matrix Q Q ℂ := (rotate (shiftIndex a b))ᴴ

def outputUnitary (a b : Fin 4) : Matrix Q Q ℂ :=
  rotate (shiftIndex a b) * (PauliChannel.pauli a)ᴴ

theorem inputUnitary_left (a b : Fin 4) :
    (inputUnitary a b)ᴴ * inputUnitary a b = 1 := by
  simpa [inputUnitary] using rotate_unitary_right (shiftIndex a b)

theorem inputUnitary_right (a b : Fin 4) :
    inputUnitary a b * (inputUnitary a b)ᴴ = 1 := by
  simpa [inputUnitary] using rotate_unitary (shiftIndex a b)

theorem outputUnitary_left (a b : Fin 4) :
    (outputUnitary a b)ᴴ * outputUnitary a b = 1 := by
  simp only [outputUnitary, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (PauliChannel.pauli a * (rotate (shiftIndex a b))ᴴ) *
        (rotate (shiftIndex a b) * (PauliChannel.pauli a)ᴴ) =
      PauliChannel.pauli a * ((rotate (shiftIndex a b))ᴴ * rotate (shiftIndex a b)) *
        (PauliChannel.pauli a)ᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [rotate_unitary, Matrix.mul_one, PauliChannel.pauli_unitary_right]

theorem outputUnitary_right (a b : Fin 4) :
    outputUnitary a b * (outputUnitary a b)ᴴ = 1 := by
  simp only [outputUnitary, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (rotate (shiftIndex a b) * (PauliChannel.pauli a)ᴴ) *
        (PauliChannel.pauli a * (rotate (shiftIndex a b))ᴴ) =
      rotate (shiftIndex a b) * ((PauliChannel.pauli a)ᴴ * PauliChannel.pauli a) *
        (rotate (shiftIndex a b))ᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [PauliChannel.pauli_unitary, Matrix.mul_one, rotate_unitary_right]

theorem normalizing_map (w : Fin 4 → ℝ) (a b : Fin 4) (X : Matrix Q Q ℂ) :
    PauliChannel.linear (fun i => w ((normalizingEquiv a b).symm i)) X =
      outputUnitary a b * PauliChannel.linear w
        (inputUnitary a b * X * (inputUnitary a b)ᴴ) * (outputUnitary a b)ᴴ := by
  change PauliChannel.linear (fun i => w (shiftIndex a (axisIndex (shiftIndex a b) i))) X = _
  rw [linear_axis (fun i => w (shiftIndex a i)) (shiftIndex a b) X, linear_shift]
  simp only [inputUnitary, outputUnitary, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem relabel_nonneg (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i) (e : Equiv.Perm (Fin 4)) :
    ∀ i, 0 ≤ w (e.symm i) := fun i => hw (e.symm i)

theorem relabel_sum (w : Fin 4 → ℝ) (hsum : ∑ i, w i = 1) (e : Equiv.Perm (Fin 4)) :
    ∑ i, w (e.symm i) = 1 := (e.symm.sum_comp w).trans hsum

theorem conditionalRatioSet_normalize (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (a b : Fin 4) (γ : ℝ) :
    conditionalRatioSet
      (PauliChannel.channel (fun i => w ((normalizingEquiv a b).symm i))
        (relabel_nonneg w hw _) (relabel_sum w hsum _)) γ =
      conditionalRatioSet (PauliChannel.channel w hw hsum) γ := by
  apply UnitaryCoefficient.conditionalRatioSet_unitary_equiv _ _
    (inputUnitary a b) (outputUnitary a b)
    (inputUnitary_left a b) (inputUnitary_right a b)
    (outputUnitary_left a b) (outputUnitary_right a b)
  intro X
  exact normalizing_map w a b X

theorem conditionalCoefficient_normalize (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (a b : Fin 4) (γ : ℝ) :
    conditionalCoefficient
      (PauliChannel.channel (fun i => w ((normalizingEquiv a b).symm i))
        (relabel_nonneg w hw _) (relabel_sum w hsum _)) γ =
      conditionalCoefficient (PauliChannel.channel w hw hsum) γ := by
  unfold conditionalCoefficient
  rw [conditionalRatioSet_normalize]

end
end PauliSymmetry
