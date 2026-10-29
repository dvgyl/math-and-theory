import ReplacerBounds

/-! Exact finite-dimensional support duality for binary quantum effects. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction ReplacerBounds

namespace NegativeDepolarizingDuality
noncomputable section
variable {n R A : Type} [Fintype n] [DecidableEq n]
  [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]

/-- The positive spectral trace is attained by an actual binary measurement effect. -/
theorem exists_positiveTrace_dual (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ F : Matrix n n ℂ, F.PosSemidef ∧ (1-F).PosSemidef ∧
      (F*X).trace.re = positiveTrace X hX := by
  obtain ⟨T,hT,hm,hp,heq⟩ := exists_traceNorm_dual X hX
  let F := (1/2:ℝ) • (T+1)
  have hF : F.PosSemidef := by
    apply posSemidef_real_smul _ _ (1/2:ℝ) (by norm_num)
    simpa only [add_comm] using hp
  have hc : (1-F).PosSemidef := by
    have hh := posSemidef_real_smul _ hm (1/2:ℝ) (by norm_num)
    have he : (1:Matrix n n ℂ)-F = (1/2:ℝ) • (1-T) := by
      dsimp [F]
      module
    rwa [← he] at hh
  refine ⟨F,hF,hc,?_⟩
  dsimp [F]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul,
    Matrix.trace_add, Complex.smul_re, Complex.add_re, smul_eq_mul, heq, positiveTrace_eq]
  ring

/-- A subnormalized effect is a support bound scaled by its interval width. -/
theorem scaled_effect_pairing_le (X F : Matrix n n ℂ) (hX : X.IsHermitian)
    (c : ℝ) (hc : 0<c) (hF : F.PosSemidef)
    (hFc : (c • (1:Matrix n n ℂ)-F).PosSemidef) :
    (F*X).trace.re ≤ c*positiveTrace X hX := by
  have hG := posSemidef_real_smul _ hF c⁻¹ (inv_pos.mpr hc).le
  have hGc : ((1:Matrix n n ℂ)-c⁻¹ • F).PosSemidef := by
    have hh := posSemidef_real_smul _ hFc c⁻¹ (inv_pos.mpr hc).le
    simpa only [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hh
  have hh := KrausSaturation.effect_pairing_le_positiveTrace X (c⁻¹ • F) hX hG hGc
  simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hm

omit [DecidableEq R] in
/-- Hilbert--Schmidt adjoint identity for the actual partial trace and reference lift. -/
theorem trace_reference_pairing [DecidableEq R] (H : Matrix R R ℂ)
    (X : Matrix (R×A) (R×A) ℂ) :
    ((H ⊗ₖ (1:Matrix A A ℂ))*X).trace = (H*partialTraceMatrix X).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, partialTraceMatrix,
    Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq']
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  simp

/-- The depolarizing map is self-adjoint under the trace pairing at every reference. -/
theorem trace_depolarizing_adjoint (M X : Matrix (R×A) (R×A) ℂ) (c s : ℝ) :
    (M*(c • (partialTraceMatrix X ⊗ₖ (1:Matrix A A ℂ))-s • X)).trace.re =
      ((c • (partialTraceMatrix M ⊗ₖ (1:Matrix A A ℂ))-s • M)*X).trace.re := by
  have hh : (M*(partialTraceMatrix X ⊗ₖ (1:Matrix A A ℂ))).trace =
      ((partialTraceMatrix M ⊗ₖ (1:Matrix A A ℂ))*X).trace := by
    rw [Matrix.trace_mul_comm M, trace_reference_pairing, trace_reference_pairing,
      Matrix.trace_mul_comm]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul, hh]

/-- A decomposition of every dual output effect gives a uniform positive-trace bound. -/
theorem positiveTrace_le_of_effect_split
    (X Y : Matrix (R×A) (R×A) ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (p : ℝ) (hp : 0<p) (hp1 : p<1)
    (hsplit : ∀ M : Matrix (R×A) (R×A) ℂ, M.PosSemidef → (1-M).PosSemidef →
      ∃ (H : Matrix R R ℂ) (F : Matrix (R×A) (R×A) ℂ),
        H.PosSemidef ∧ ((1-p) • (1:Matrix R R ℂ)-H).PosSemidef ∧
        F.PosSemidef ∧ (p • (1:Matrix (R×A) (R×A) ℂ)-F).PosSemidef ∧
        (M*Y).trace.re = (F*X).trace.re + (H*partialTraceMatrix X).trace.re) :
    positiveTrace Y hY ≤ p*positiveTrace X hX +
      (1-p)*positiveTrace (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) := by
  obtain ⟨M,hM,hIM,hattain⟩ := exists_positiveTrace_dual Y hY
  obtain ⟨H,F,hH,hHc,hF,hFc,hpair⟩ := hsplit M hM hIM
  have hfb := scaled_effect_pairing_le X F hX p hp hF hFc
  have hhb := scaled_effect_pairing_le (partialTraceMatrix X) H
    (partialTraceMatrix_hermitian X hX) (1-p) (by linarith) hH hHc
  linarith

end
end NegativeDepolarizingDuality
