module
public import GeneralContraction


@[expose] public section

/-! Positive replacer components give strict conditional trace and hockey contraction. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction

namespace ReplacerBounds
noncomputable section
variable {A B R n m : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq n] in
theorem hermitian_trace_im [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    X.trace.im = 0 := by
  have h : star X.trace = X.trace := by rw [← Matrix.trace_conjTranspose, hX.eq]
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem positive_trace_re (X : Matrix n n ℂ) (hX : X.PosSemidef) :
    0 ≤ X.trace.re := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => posSemidef_diagonal_re X hX i)

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem sub_kronecker [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (X Y : Matrix n n ℂ) (P : Matrix m m ℂ) :
    (X-Y) ⊗ₖ P = X ⊗ₖ P - Y ⊗ₖ P := by
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply]
  exact sub_mul _ _ _

omit [DecidableEq n] in
theorem trace_kronecker_re [DecidableEq n] (X : Matrix n n ℂ) (P : Matrix m m ℂ)
    (hP : P.IsHermitian) : (X ⊗ₖ P).trace.re = P.trace.re * X.trace.re := by
  rw [Matrix.trace_kronecker]
  simp only [Complex.mul_re, hermitian_trace_im P hP, mul_zero, sub_zero]
  ring

theorem traceNorm_kronecker_le (X : Matrix n n ℂ) (P : Matrix m m ℂ)
    (hX : X.IsHermitian) (hP : P.PosSemidef) :
    traceNorm (X ⊗ₖ P) (kronecker_hermitian X P hX hP.1) ≤
      P.trace.re * traceNorm X hX := by
  exact traceNorm_map_le_scale (fun Y => Y ⊗ₖ P) P.trace.re
    (fun Y Z => sub_kronecker Y Z P)
    (fun Y hY => kronecker_positive Y P hY hP)
    (fun Y => trace_kronecker_re Y P hP.1) X hX _

def residual (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (X : Matrix (R × A) (R × A) ℂ) : Matrix (R × B) (R × B) ℂ :=
  amplify N.map X - partialTraceMatrix X ⊗ₖ P

theorem residual_sub (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (X Y : Matrix (R × A) (R × A) ℂ) :
    residual N P (X-Y) = residual N P X-residual N P Y := by
  unfold residual
  rw [amplify_sub, partialTraceMatrix_sub, sub_kronecker]
  abel

theorem residual_hermitian (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (hP : P.IsHermitian) (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    (residual N P X).IsHermitian :=
  (N.amplify_hermitian X hX).sub
    (kronecker_hermitian (partialTraceMatrix X) P (partialTraceMatrix_hermitian X hX) hP)

theorem residual_trace_re (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (hP : P.IsHermitian) (X : Matrix (R × A) (R × A) ℂ) :
    (residual N P X).trace.re = (1-P.trace.re)*X.trace.re := by
  unfold residual
  rw [Matrix.trace_sub, Complex.sub_re, N.amplify_trace,
    trace_kronecker_re _ P hP, partialTraceMatrix_trace]
  ring

theorem traceNorm_amplify_le (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (hP : P.PosSemidef)
    (hres : ∀ X : Matrix (R × A) (R × A) ℂ, X.PosSemidef → (residual N P X).PosSemidef)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    traceNorm (amplify N.map X) (N.amplify_hermitian X hX) ≤
      (1-P.trace.re)*traceNorm X hX +
        P.trace.re*traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) := by
  have hr := traceNorm_map_le_scale (residual N P) (1-P.trace.re)
    (residual_sub N P) hres (residual_trace_re N P hP.1) X hX
    (residual_hermitian N P hP.1 X hX)
  have ht := traceNorm_kronecker_le (partialTraceMatrix X) P
    (partialTraceMatrix_hermitian X hX) hP
  have hsum := traceNorm_triangle (residual N P X) (partialTraceMatrix X ⊗ₖ P)
    (residual_hermitian N P hP.1 X hX)
    (kronecker_hermitian _ P (partialTraceMatrix_hermitian X hX) hP.1)
  have heq : residual N P X + partialTraceMatrix X ⊗ₖ P = amplify N.map X := by
    unfold residual
    abel
  simpa only [heq] using hsum.trans (add_le_add hr ht)

theorem positiveTraceGap_amplify_le (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (hP : P.PosSemidef)
    (hres : ∀ X : Matrix (R × A) (R × A) ℂ, X.PosSemidef → (residual N P X).PosSemidef)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    positiveTraceGap (amplify N.map X) (N.amplify_hermitian X hX) ≤
      (1-P.trace.re)*positiveTraceGap X hX := by
  have h := traceNorm_amplify_le N P hP hres X hX
  rw [positiveTraceGap_eq, positiveTraceGap_eq]
  unfold normGap
  simp only [N.partialTrace_amplify]
  linarith

theorem replacer_trace_le_one [Nonempty A] (N : QuantumChannel A B) (P : Matrix B B ℂ)
    (hP : P.PosSemidef)
    (hres : ∀ (R : Type) [Fintype R] [DecidableEq R]
      (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef → (residual N P X).PosSemidef) :
    P.trace.re ≤ 1 := by
  let ρ := basisDensity ((), Classical.choice (inferInstance : Nonempty A))
  have h := positive_trace_re (residual N P ρ.mat) (hres Unit ρ.mat ρ.positive)
  rw [residual_trace_re N P hP.1, ρ.normalized, Complex.one_re, mul_one] at h
  linarith

theorem conditionalCoefficient_le_replacer [Nonempty A] (N : QuantumChannel A B)
    (P : Matrix B B ℂ) (hP : P.PosSemidef)
    (hres : ∀ (R : Type) [Fintype R] [DecidableEq R]
      (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef → (residual N P X).PosSemidef)
    (γ : ℝ) :
    conditionalCoefficient N γ ≤ 1-P.trace.re := by
  have hc : 0 ≤ 1-P.trace.re := sub_nonneg.mpr (replacer_trace_le_one N P hP hres)
  by_cases hn : (conditionalRatioSet N γ).Nonempty
  · apply csSup_le hn
    rintro r ⟨R,ρ,σ,hpos,rfl⟩
    apply (div_le_iff₀ hpos).mpr
    exact positiveTraceGap_amplify_le N P hP (hres R.Carrier)
      (difference γ ρ σ) (difference_hermitian γ ρ σ)
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simpa [conditionalCoefficient, he] using hc

theorem conditionalCoefficient_lt_one_of_positiveReplacer [Nonempty A]
    (N : QuantumChannel A B) (h : HasPositiveReplacer N) (γ : ℝ) :
    conditionalCoefficient N γ < 1 := by
  obtain ⟨P,hP,htr,hres⟩ := h
  have hb := conditionalCoefficient_le_replacer N P hP hres γ
  linarith

theorem completeCoefficient_le_replacer [Nonempty A] (N : QuantumChannel A B)
    (P : Matrix B B ℂ) (hP : P.PosSemidef)
    (hres : ∀ (R : Type) [Fintype R] [DecidableEq R]
      (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef → (residual N P X).PosSemidef)
    (γ : ℝ) (hγ : 1 ≤ γ) :
    GeneralContraction.completeCoefficient N γ ≤ 1-P.trace.re := by
  have hc : 0 ≤ 1-P.trace.re := sub_nonneg.mpr (replacer_trace_le_one N P hP hres)
  by_cases hn : (GeneralContraction.completeRatioSet N γ).Nonempty
  · have hb := conditionalCoefficient_le_replacer N P hP hres γ
    have hs := GeneralContraction.completeRatioSet_subset_conditional N γ hγ
    exact (csSup_le hn (fun r hr => le_csSup
      (ConditionalHockey.conditionalRatioSet_bddAbove N γ) (hs hr))).trans hb
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simpa [GeneralContraction.completeCoefficient, he] using hc

theorem completeCoefficient_lt_one_of_positiveReplacer [Nonempty A]
    (N : QuantumChannel A B) (h : HasPositiveReplacer N) (γ : ℝ) (hγ : 1 ≤ γ) :
    GeneralContraction.completeCoefficient N γ < 1 := by
  obtain ⟨P,hP,htr,hres⟩ := h
  have hb := completeCoefficient_le_replacer N P hP hres γ hγ
  linarith

end
end ReplacerBounds
