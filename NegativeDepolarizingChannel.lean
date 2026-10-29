module
public import ADChannel
public import ADSharp
public import GeneralKraus
public import GeneralContraction
public import ReplacerBounds


@[expose] public section

/-! The actual negative qubit depolarizing channel and complete trace contraction. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace NegativeDepolarizingChannel
noncomputable section
set_option maxHeartbeats 2000000
abbrev Q := Fin 2
variable {R : Type} [Fintype R] [DecidableEq R]

def pauliK (i : Fin 3) : Matrix Q Q ℂ :=
  ![ADSeparation.pauliX, !![0, -1; 1, 0], ADSeparation.pauliZ] i

theorem pauli_reduction (X : Matrix Q Q ℂ) :
    GeneralKraus.krausMap pauliK X = (2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - X := by
  ext i j
  change (∑ k : Fin 3, pauliK k * X * (pauliK k)ᴴ) i j = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliK, ADSeparation.pauliX,
      ADSeparation.pauliY, ADSeparation.pauliZ, Matrix.trace, Fin.sum_univ_succ,
      Matrix.smul_apply, Complex.real_smul] <;> ring

omit [Fintype R] [DecidableEq R] in
theorem amplify_reduction [Fintype R] [DecidableEq R] (X : Matrix (R × Q) (R × Q) ℂ) :
    amplify (GeneralKraus.krausMap pauliK) X =
      (2 : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix Q Q ℂ)) - X := by
  ext r s
  change GeneralKraus.krausMap pauliK (GeneralKraus.block X r.1 s.1) r.2 s.2 = _
  rw [pauli_reduction]
  rfl

/-- The amplified qubit reduction map is completely positive with three explicit
Pauli Kraus operators. -/
theorem reduction_positive (X : Matrix (R × Q) (R × Q) ℂ) (hX : X.PosSemidef) :
    ((2 : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix Q Q ℂ)) - X).PosSemidef := by
  rw [← amplify_reduction]
  exact GeneralKraus.completely_positive pauliK X hX

def linear (s : ℝ) : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ where
  toFun X := ((1+s)/2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - s • X
  map_add' X Y := by
    rw [Matrix.trace_add, add_smul, smul_add, smul_add]
    abel
  map_smul' c X := by
    ext i j
    simp only [Matrix.trace_smul, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul, RingHom.id_apply]
    ring

theorem linear_formula (s : ℝ) (X : Matrix Q Q ℂ) :
    linear s X = ((1+s)/2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - s • X := rfl

omit [Fintype R] [DecidableEq R] in
theorem amplified_formula [Fintype R] [DecidableEq R] (s : ℝ) (X : Matrix (R × Q) (R × Q) ℂ) :
    amplify (linear s) X =
      ((1+s)/2 : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix Q Q ℂ)) - s • X := rfl

omit [Fintype R] [DecidableEq R] in
theorem amplified_formula_of_map [Fintype R] [DecidableEq R] (N : QuantumChannel Q Q) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - s • X)
    (X : Matrix (R × Q) (R × Q) ℂ) :
    amplify N.map X =
      ((1+s)/2 : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix Q Q ℂ)) - s • X := by
  ext r t
  exact congrArg (fun Y : Matrix Q Q ℂ => Y r.2 t.2)
    (hN (fun a b => X (r.1,a) (t.1,b)))

theorem linear_trace (s : ℝ) (X : Matrix Q Q ℂ) : (linear s X).trace = X.trace := by
  simp [linear_formula, Matrix.trace, Fin.sum_univ_succ, Matrix.smul_apply, Complex.real_smul]
  ring

theorem amplified_pauli_mixture (s : ℝ) (X : Matrix (R × Q) (R × Q) ℂ) :
    amplify (linear s) X = ((1-3*s)/4 : ℝ) • X +
      ((1+s)/4 : ℝ) • amplify (GeneralKraus.krausMap pauliK) X := by
  rw [amplified_formula, amplify_reduction]
  ext r t
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

def channel (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) : QuantumChannel Q Q where
  map := linear s
  trace_preserving := linear_trace s
  completely_positive R _ _ X hX := by
    rw [amplified_pauli_mixture]
    exact (posSemidef_real_smul X hX ((1-3*s)/4) (by linarith)).add
      (posSemidef_real_smul _ (GeneralKraus.completely_positive pauliK X hX)
        ((1+s)/4) (by linarith))

@[simp] theorem channel_map (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) (X : Matrix Q Q ℂ) :
    (channel s hs hs3).map X =
      ((1+s)/2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - s • X := rfl

theorem equal_reference_hockey (N : QuantumChannel Q Q) (s : ℝ) (hs : 0 ≤ s)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - s • X)
    (ρ σ : Density (R × Q))
    (href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat) :
    hockeyStick 1 (N.outputDensity ρ) (N.outputDensity σ) = s * hockeyStick 1 ρ σ := by
  have hx : (ρ.mat-σ.mat).IsHermitian := ρ.positive.1.sub σ.positive.1
  have ho : (N.outputDensity ρ).mat-(N.outputDensity σ).mat = -(s • (ρ.mat-σ.mat)) := by
    change amplify N.map ρ.mat-amplify N.map σ.mat = _
    rw [← amplify_sub, amplified_formula_of_map N s hN,
      partialTraceMatrix_sub, href, sub_self, Matrix.zero_kronecker, smul_zero, zero_sub]
  have ht := traceNorm_neg (s • (ρ.mat-σ.mat)) (hermitian_real_smul _ hx s)
  rw [traceNorm_real_smul _ hx s hs] at ht
  have ht' : traceNorm ((N.outputDensity ρ).mat-(N.outputDensity σ).mat)
      ((N.outputDensity ρ).positive.1.sub (N.outputDensity σ).positive.1) =
      s * traceNorm (ρ.mat-σ.mat) hx := by
    simpa only [← ho] using ht
  rw [hockeyStick_one_eq_traceDistance, hockeyStick_one_eq_traceDistance, ht']
  ring

def witnessPlus : Density (Fin 1 × Q) :=
  ⟨ADSeparation.sharpPlus, ADSeparation.sharpPlus_positive, ADSeparation.sharpPlus_trace⟩
def witnessMinus : Density (Fin 1 × Q) :=
  ⟨ADSeparation.sharpMinus, ADSeparation.sharpMinus_positive, ADSeparation.sharpMinus_trace⟩

theorem witness_reference : partialTraceMatrix witnessPlus.mat = partialTraceMatrix witnessMinus.mat :=
  ADSeparation.sharp_reference_equal

theorem witness_hockey : hockeyStick 1 witnessPlus witnessMinus = 1 := by
  rw [hockeyStick_one_eq_traceDistance]
  change traceNorm ADSeparation.sharpDifference ADSeparation.sharpDifference_hermitian / 2 = 1
  rw [ADSeparation.sharp_input_norm]
  norm_num

theorem complete_trace_eq (N : QuantumChannel Q Q) (s : ℝ) (hs : 0 ≤ s)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) • (X.trace • (1 : Matrix Q Q ℂ)) - s • X) :
    GeneralContraction.completeCoefficient N 1 = s := by
  have hm : s ∈ GeneralContraction.completeRatioSet N 1 := by
    refine ⟨⟨Fin 1,inferInstance,inferInstance⟩,witnessPlus,witnessMinus,
      witness_reference, ?_, ?_⟩
    · rw [witness_hockey]; norm_num
    · rw [equal_reference_hockey N s hs hN _ _ witness_reference, witness_hockey]
      ring
  apply le_antisymm
  · apply csSup_le ⟨s,hm⟩
    rintro r ⟨R,ρ,σ,href,hpos,rfl⟩
    rw [equal_reference_hockey N s hs hN ρ σ href]
    exact le_of_eq (mul_div_cancel_right₀ s (ne_of_gt hpos))
  · exact le_csSup (GeneralContraction.completeRatioSet_bddAbove N 1) hm

theorem channel_complete_trace_eq (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    GeneralContraction.completeCoefficient (channel s hs hs3) 1 = s :=
  complete_trace_eq _ s hs (channel_map s hs hs3)

end
end NegativeDepolarizingChannel
