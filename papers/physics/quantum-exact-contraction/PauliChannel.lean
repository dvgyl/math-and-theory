import NegativeDepolarizingChannel

/-! Actual stochastic Pauli channels, with complete positivity at every finite reference. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace PauliChannel
noncomputable section
set_option maxHeartbeats 2000000
abbrev Q := Fin 2
variable {R : Type} [Fintype R] [DecidableEq R]

/-- Labels are identity, X, a real phase of Y, and Z. Phases cancel in conjugation. -/
def pauli (i : Fin 4) : Matrix Q Q ℂ :=
  ![1, ADSeparation.pauliX, !![0, -1; 1, 0], ADSeparation.pauliZ] i

theorem pauli_unitary (i : Fin 4) : (pauli i)ᴴ * pauli i = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, ADSeparation.pauliX, ADSeparation.pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem pauli_unitary_right (i : Fin 4) : pauli i * (pauli i)ᴴ = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, ADSeparation.pauliX, ADSeparation.pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]

def linear (w : Fin 4 → ℝ) : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ where
  toFun X := ∑ i, w i • (pauli i * X * (pauli i)ᴴ)
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_comm (w _) z,
      Finset.smul_sum, RingHom.id_apply]

@[simp] theorem linear_apply (w : Fin 4 → ℝ) (X : Matrix Q Q ℂ) :
    linear w X = ∑ i, w i • (pauli i * X * (pauli i)ᴴ) := rfl

theorem amplify_linear (w : Fin 4 → ℝ) (X : Matrix (R × Q) (R × Q) ℂ) :
    amplify (linear w) X = ∑ i, w i •
      (GeneralKraus.lift (pauli i) * X * (GeneralKraus.lift (pauli i))ᴴ) := by
  ext r t
  simp only [amplify, linear_apply, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [GeneralKraus.lift_sandwich_entry]
  rfl

theorem linear_trace (w : Fin 4 → ℝ) (hsum : ∑ i, w i = 1)
    (X : Matrix Q Q ℂ) : (linear w X).trace = X.trace := by
  simp only [linear_apply, Matrix.trace_sum, Matrix.trace_smul,
    trace_unitary_conj X _ (pauli_unitary _)]
  rw [← Finset.sum_smul, hsum, one_smul]

def channel (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    QuantumChannel Q Q where
  map := linear w
  trace_preserving := linear_trace w hsum
  completely_positive S _ _ X hX := by
    rw [amplify_linear]
    exact Finset.sum_induction _ _ (fun P Q hP hQ => hP.add hQ)
      Matrix.PosSemidef.zero (fun i _ => posSemidef_real_smul _
        (hX.mul_mul_conjTranspose_same (GeneralKraus.lift (pauli i))) (w i) (hw i))

@[simp] theorem channel_map (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (X : Matrix Q Q ℂ) :
    (channel w hw hsum).map X = linear w X := rfl

/-- Entry formula without any normalization or positivity assumptions on weights. -/
theorem map_entries (w : Fin 4 → ℝ) (X : Matrix Q Q ℂ) :
    linear w X =
      !![ ((w 0 + w 3 : ℝ) : ℂ) * X 0 0 + ((w 1 + w 2 : ℝ) : ℂ) * X 1 1,
          ((w 0 - w 3 : ℝ) : ℂ) * X 0 1 + ((w 1 - w 2 : ℝ) : ℂ) * X 1 0;
          ((w 0 - w 3 : ℝ) : ℂ) * X 1 0 + ((w 1 - w 2 : ℝ) : ℂ) * X 0 1,
          ((w 1 + w 2 : ℝ) : ℂ) * X 0 0 + ((w 0 + w 3 : ℝ) : ℂ) * X 1 1] := by
  ext i j
  simp only [linear_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [pauli, ADSeparation.pauliX, ADSeparation.pauliZ,
      Matrix.one_apply, Fin.sum_univ_succ, Complex.real_smul] <;> push_cast <;> ring

def single (i : Fin 4) : QuantumChannel Q Q :=
  channel (fun j => if j = i then 1 else 0)
    (by intro j; dsimp; split_ifs <;> norm_num) (by simp)

@[simp] theorem single_map (i : Fin 4) (X : Matrix Q Q ℂ) :
    (single i).map X = pauli i * X * (pauli i)ᴴ := by
  simp [single, linear_apply]

theorem core_identity (a b : ℝ) (hm : a + 3*b ≠ 0) (X : Matrix Q Q ℂ) :
    (a+3*b) • NegativeDepolarizingChannel.linear ((b-a)/(a+3*b)) X =
      linear ![a,b,b,b] X := by
  have hc : (a+3*b) * ((1+(b-a)/(a+3*b))/2) = 2*b := by
    field_simp [hm]
    ring
  have hd : (a+3*b) * ((b-a)/(a+3*b)) = b-a := by
    field_simp [hm]
  rw [NegativeDepolarizingChannel.linear_formula, smul_sub, smul_smul, smul_smul,
    hc, hd, map_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.smul_apply,
      Complex.real_smul, Matrix.sub_apply, Matrix.one_apply] <;>
    push_cast <;> ring

theorem core_decomposition (w : Fin 4 → ℝ) (X : Matrix Q Q ℂ) :
    linear w X = linear ![w 0,w 3,w 3,w 3] X +
      (w 1-w 3) • (single 1).map X + (w 2-w 3) • (single 2).map X := by
  change linear w X = linear ![w 0,w 3,w 3,w 3] X +
    (w 1-w 3) • linear (fun j => if j = 1 then 1 else 0) X +
    (w 2-w 3) • linear (fun j => if j = 2 then 1 else 0) X
  simp only [map_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] <;>
    push_cast <;> ring

end
end PauliChannel
