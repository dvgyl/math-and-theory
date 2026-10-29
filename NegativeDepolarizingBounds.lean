module
public import NegativeDepolarizingEffects
public import NegativeDepolarizingDuality
public import NegativeDepolarizingChannel


@[expose] public section

/-! Sharp conditional contraction bounds for the actual negative-depolarizing qubit channel. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction ReplacerBounds

namespace NegativeDepolarizingBounds
noncomputable section
variable {R : Type} [Fintype R] [DecidableEq R]
set_option maxHeartbeats 1000000

omit [Fintype R] in
theorem partialTrace_qubit_one [Fintype R] :
    partialTraceMatrix (1:Matrix (R×Fin 2) (R×Fin 2) ℂ) =
      (2:ℝ) • (1:Matrix R R ℂ) := by
  ext r t
  by_cases h : r=t
  · subst t
    simp [partialTraceMatrix, Fin.sum_univ_succ, Matrix.one_apply, Complex.real_smul]
  · simp [partialTraceMatrix, Fin.sum_univ_succ, Matrix.one_apply, Prod.ext_iff, h,
      Complex.real_smul]

/-- The actual adjoint of negative qubit depolarization admits the sharp complete
binary-effect lift, with a reference-only reserve. -/
theorem qubit_effect_split (M : Matrix (R×Fin 2) (R×Fin 2) ℂ)
    (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3) :
    ∃ H : Matrix R R ℂ, H.PosSemidef ∧
      ((1-sharpBound s) • (1:Matrix R R ℂ)-H).PosSemidef ∧
      (((1+s)/2:ℝ) • referenceLift (partialTraceMatrix M)-s • M-referenceLift H).PosSemidef ∧
      (sharpBound s • (1:Matrix (R×Fin 2) (R×Fin 2) ℂ)-
        (((1+s)/2:ℝ) • referenceLift (partialTraceMatrix M)-s • M-referenceLift H)).PosSemidef := by
  let D := (2:ℝ) • partialTraceMatrix M
  have hD : D.PosSemidef :=
    posSemidef_real_smul _ (partialTraceMatrix_posSemidef M hM) 2 (by norm_num)
  have hD4 : ((4:ℝ) • (1:Matrix R R ℂ)-D).PosSemidef := by
    have hp := posSemidef_real_smul _ (partialTraceMatrix_posSemidef (1-M) hIM) 2 (by norm_num)
    rw [partialTraceMatrix_sub, partialTrace_qubit_one] at hp
    have heq : (2:ℝ) • ((2:ℝ) • (1:Matrix R R ℂ)-partialTraceMatrix M) =
        (4:ℝ) • (1:Matrix R R ℂ)-D := by
      dsimp [D]
      module
    rwa [heq] at hp
  have hDM : (referenceLift (A:=Fin 2) D-M).PosSemidef := by
    simpa only [referenceLift, D, Matrix.smul_kronecker] using
      NegativeDepolarizingChannel.reduction_positive M hM
  have hcomp : ((4:ℝ) • (1:Matrix (R×Fin 2) (R×Fin 2) ℂ)-referenceLift D-(1-M)).PosSemidef := by
    have hp := NegativeDepolarizingChannel.reduction_positive (1-M) hIM
    rw [partialTraceMatrix_sub, partialTrace_qubit_one, sub_kronecker,
      Matrix.smul_kronecker, Matrix.one_kronecker_one] at hp
    convert hp using 1
    dsimp [referenceLift,D]
    rw [Matrix.smul_kronecker]
    module
  obtain ⟨H,hH,hHc,hF,hFc⟩ := reference_effect_split D hD hD4 M hM hIM hDM hcomp s hs hs3
  have hJ : prefactor s • referenceLift (A:=Fin 2) D =
      ((1+s)/2:ℝ) • referenceLift (partialTraceMatrix M) := by
    dsimp [prefactor, referenceLift,D]
    rw [Matrix.smul_kronecker]
    module
  exact ⟨H,hH,hHc,by simpa only [hJ] using hF, by simpa only [hJ] using hFc⟩

/-- The sharp positive-trace inequality holds for every finite quantum reference
and every Hermitian input operator. -/
theorem positiveTrace_amplify_le (N : QuantumChannel (Fin 2) (Fin 2))
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3)
    (hN : ∀ X, N.map X = ((1+s)/2:ℝ) • (X.trace • (1:Matrix (Fin 2) (Fin 2) ℂ))-s • X)
    (X : Matrix (R×Fin 2) (R×Fin 2) ℂ) (hX : X.IsHermitian) :
    positiveTrace (amplify N.map X) (N.amplify_hermitian X hX) ≤
      sharpBound s * positiveTrace X hX + (1-sharpBound s) *
        positiveTrace (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) := by
  have hp := sharpBound_bounds s hs hs3
  apply NegativeDepolarizingDuality.positiveTrace_le_of_effect_split X (amplify N.map X)
    hX (N.amplify_hermitian X hX) (sharpBound s) hp.1 hp.2
  intro M hM hIM
  obtain ⟨H,hH,hHc,hF,hFc⟩ := qubit_effect_split M hM hIM s hs hs3
  let F := ((1+s)/2:ℝ) • referenceLift (partialTraceMatrix M)-s • M-referenceLift (A:=Fin 2) H
  refine ⟨H,F,hH,hHc,hF,hFc,?_⟩
  rw [NegativeDepolarizingChannel.amplified_formula_of_map N s hN,
    NegativeDepolarizingDuality.trace_depolarizing_adjoint]
  dsimp [F,referenceLift]
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
    NegativeDepolarizingDuality.trace_reference_pairing]
  ring

/-- Exact all-reference conditional gap upper bound, with no equal-marginal
restriction on the Hermitian input. -/
theorem positiveTraceGap_amplify_le (N : QuantumChannel (Fin 2) (Fin 2))
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3)
    (hN : ∀ X, N.map X = ((1+s)/2:ℝ) • (X.trace • (1:Matrix (Fin 2) (Fin 2) ℂ))-s • X)
    (X : Matrix (R×Fin 2) (R×Fin 2) ℂ) (hX : X.IsHermitian) :
    positiveTraceGap (amplify N.map X) (N.amplify_hermitian X hX) ≤
      sharpBound s * positiveTraceGap X hX := by
  have hh := positiveTrace_amplify_le N s hs hs3 hN X hX
  unfold positiveTraceGap
  simp only [N.partialTrace_amplify]
  linarith

/-- The upper bound is for the actual conditional coefficient over all finite
references and all state pairs, at every hockey parameter. -/
theorem conditionalCoefficient_le (N : QuantumChannel (Fin 2) (Fin 2))
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3)
    (hN : ∀ X, N.map X = ((1+s)/2:ℝ) • (X.trace • (1:Matrix (Fin 2) (Fin 2) ℂ))-s • X)
    (γ : ℝ) : conditionalCoefficient N γ ≤ sharpBound s := by
  by_cases hn : (conditionalRatioSet N γ).Nonempty
  · apply csSup_le hn
    rintro r ⟨R,ρ,σ,hpos,rfl⟩
    apply (div_le_iff₀ hpos).mpr
    exact positiveTraceGap_amplify_le N s hs hs3 hN
      (difference γ ρ σ) (difference_hermitian γ ρ σ)
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simpa [conditionalCoefficient,he] using (sharpBound_bounds s hs hs3).1.le

end
end NegativeDepolarizingBounds
