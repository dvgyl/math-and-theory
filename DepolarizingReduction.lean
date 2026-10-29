module
public import PositiveReplacerSDP


@[expose] public section

/-! The completely positive dimensional reduction map, with explicit Gram
factorization and every finite reference admitted. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace DepolarizingReduction
noncomputable section

variable {A R : Type} [Fintype A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

theorem omega_outer_trace :
    (BellSupport.outer (ChannelKraus.omega (A:=A))).trace.re = Fintype.card A := by
  simp [BellSupport.outer, ChannelKraus.omega, Matrix.trace,
    Fintype.sum_prod_type]

theorem choiApply_one (X : Matrix A A ℂ) :
    KrausSupport.choiApply (1 : Matrix (A×A) (A×A) ℂ) X =
      X.trace • (1 : Matrix A A ℂ) := by
  simpa only [Matrix.one_kronecker_one] using
    PositiveReplacerSDP.choiApply_replacer (1 : Matrix A A ℂ) X

theorem choiApply_omega_outer (X : Matrix A A ℂ) :
    KrausSupport.choiApply (BellSupport.outer (ChannelKraus.omega (A:=A))) X = X := by
  ext b d
  simp [KrausSupport.choiApply, BellSupport.outer, ChannelKraus.omega]

theorem reduction_gram_positive :
    ((Fintype.card A : ℝ) • (1 : Matrix (A×A) (A×A) ℂ) -
      BellSupport.outer (ChannelKraus.omega (A:=A))).PosSemidef := by
  have h := KrausSaturation.posSemidef_trace_domination
    (BellSupport.outer (ChannelKraus.omega (A:=A)))
    (BellSupport.outer_posSemidef _)
  rwa [omega_outer_trace] at h

/-- The map `X ↦ d Tr(X)I - X` has an actual finite Kraus representation. -/
theorem exists_reduction_kraus :
    ∃ K : (A×A) → Matrix A A ℂ, ∀ X,
      GeneralKraus.krausMap K X =
        (Fintype.card A : ℝ) • (X.trace • (1 : Matrix A A ℂ)) - X := by
  obtain ⟨K,hK⟩ := KrausSupport.exists_kraus_of_positive_gram _
    (reduction_gram_positive (A:=A))
  refine ⟨K,?_⟩
  intro X
  rw [hK, KrausSupport.choiApply_sub, KrausSupport.choiApply_real_smul,
    choiApply_one, choiApply_omega_outer]

/-- Complete dimensional domination, valid for arbitrary finite references. -/
theorem reduction_positive (X : Matrix (R×A) (R×A) ℂ) (hX : X.PosSemidef) :
    ((Fintype.card A : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix A A ℂ)) - X).PosSemidef := by
  obtain ⟨K,hK⟩ := exists_reduction_kraus (A:=A)
  have hcp := GeneralKraus.completely_positive K X hX
  have heq : amplify (GeneralKraus.krausMap K) X =
      (Fintype.card A : ℝ) • (partialTraceMatrix X ⊗ₖ (1 : Matrix A A ℂ)) - X := by
    ext r t
    change GeneralKraus.krausMap K (GeneralKraus.block X r.1 t.1) r.2 t.2 = _
    rw [hK]
    rfl
  rwa [heq] at hcp

omit [Fintype R] in
theorem partialTrace_one [Fintype R] :
    partialTraceMatrix (1 : Matrix (R×A) (R×A) ℂ) =
      (Fintype.card A : ℝ) • (1 : Matrix R R ℂ) := by
  ext r t
  by_cases h : r=t
  · subst t
    simp [partialTraceMatrix, Matrix.one_apply, Complex.real_smul]
  · simp [partialTraceMatrix, Matrix.one_apply, Prod.ext_iff, h,
      Complex.real_smul]

end
end DepolarizingReduction
