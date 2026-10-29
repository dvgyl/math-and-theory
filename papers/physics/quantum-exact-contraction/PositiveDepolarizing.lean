import DepolarizingComparison

/-! The positive depolarizing branch.  This is a standard supporting calculation,
not an independent novelty claim.  The coefficient is the actual supremum over
all finite quantum references and normalized density pairs. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction

namespace PositiveDepolarizing
noncomputable section

variable {A R : Type} [Fintype A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

set_option maxHeartbeats 2000000

omit [Fintype R] [DecidableEq R] in
theorem amplified_formula_of_map [Fintype R] [DecidableEq R] (N : QuantumChannel A A) (l : ℝ)
    (hN : ∀ X, N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)))
    (X : Matrix (R×A) (R×A) ℂ) :
    amplify N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (partialTraceMatrix X ⊗ₖ (1 : Matrix A A ℂ)) := by
  ext r t
  exact congrArg (fun Y : Matrix A A ℂ => Y r.2 t.2)
    (hN (fun a b => X (r.1,a) (t.1,b)))

theorem equal_reference_hockey (N : QuantumChannel A A) (l : ℝ) (hl : 0≤l)
    (hN : ∀ X, N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)))
    (ρ σ : Density (R×A))
    (href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat) :
    hockeyStick 1 (N.outputDensity ρ) (N.outputDensity σ) = l*hockeyStick 1 ρ σ := by
  have hx : (ρ.mat-σ.mat).IsHermitian := ρ.positive.1.sub σ.positive.1
  have ho : (N.outputDensity ρ).mat-(N.outputDensity σ).mat = l • (ρ.mat-σ.mat) := by
    change amplify N.map ρ.mat-amplify N.map σ.mat = _
    rw [← amplify_sub, amplified_formula_of_map N l hN,
      partialTraceMatrix_sub, href, sub_self]
    simp
  have ht := traceNorm_real_smul (ρ.mat-σ.mat) hx l hl
  have ht' : traceNorm ((N.outputDensity ρ).mat-(N.outputDensity σ).mat)
      ((N.outputDensity ρ).positive.1.sub (N.outputDensity σ).positive.1) =
      l * traceNorm (ρ.mat-σ.mat) hx := by
    simpa only [← ho] using ht
  rw [hockeyStick_one_eq_traceDistance, hockeyStick_one_eq_traceDistance, ht']
  ring

theorem completeRatioSet_member (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (l : ℝ) (hl : 0≤l)
    (hN : ∀ X, N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ))) :
    l ∈ completeRatioSet N 1 := by
  obtain ⟨ρ,σ,href,hpos⟩ :=
    DepolarizingComparison.exists_distinct_reference_pair (A:=A) hdim
  refine ⟨⟨Unit,inferInstance,inferInstance⟩,ρ,σ,href,hpos,?_⟩
  rw [equal_reference_hockey N l hl hN ρ σ href]
  exact (mul_div_cancel_right₀ l hpos.ne').symm

theorem complete_trace_eq (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (l : ℝ) (hl : 0≤l)
    (hN : ∀ X, N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ))) :
    completeCoefficient N 1 = l := by
  have hm := completeRatioSet_member N hdim l hl hN
  apply le_antisymm
  · apply csSup_le ⟨l,hm⟩
    rintro r ⟨R,ρ,σ,href,hpos,rfl⟩
    rw [equal_reference_hockey N l hl hN ρ σ href]
    exact le_of_eq (mul_div_cancel_right₀ l hpos.ne')
  · exact le_csSup (completeRatioSet_bddAbove N 1) hm

theorem conditionalCoefficient_le [Nonempty A] (N : QuantumChannel A A)
    (l : ℝ) (hl : 0≤l) (hl1 : l≤1)
    (hN : ∀ X, N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ))) (γ : ℝ) :
    conditionalCoefficient N γ ≤ l := by
  let P : Matrix A A ℂ := (1-l) • DepolarizingBounds.uniformReplacer
  have hP : P.PosSemidef := posSemidef_real_smul _
    DepolarizingBounds.uniformReplacer_positive _ (sub_nonneg.mpr hl1)
  have hres : ∀ (R : Type) [Fintype R] [DecidableEq R]
      (X : Matrix (R×A) (R×A) ℂ), X.PosSemidef →
      (ReplacerBounds.residual N P X).PosSemidef := by
    intro R _ _ X hX
    have heq : ReplacerBounds.residual N P X = l • X := by
      rw [ReplacerBounds.residual, amplified_formula_of_map N l hN]
      simp [P, DepolarizingBounds.uniformReplacer, Matrix.kronecker_smul,
        smul_smul, div_eq_mul_inv]
    rw [heq]
    exact posSemidef_real_smul X hX l hl
  have hp : P.trace.re = 1-l := by
    simp [P, Matrix.trace_smul, Complex.smul_re,
      DepolarizingBounds.uniformReplacer_trace]
  have h := ReplacerBounds.conditionalCoefficient_le_replacer N P hP hres γ
  simpa only [hp, sub_sub_cancel] using h

/-- The positive branch, including both endpoints, for every hockey-stick
parameter at least one and every finite reference dimension. -/
theorem conditionalCoefficient_eq (N : QuantumChannel A A)
    (hdim : 2 ≤ Fintype.card A) (l : ℝ) (hl : 0≤l) (hl1 : l≤1)
    (hN : ∀ X, N.map X = l • X + ((1-l)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ))) (γ : ℝ) (hγ : 1≤γ) :
    conditionalCoefficient N γ = l := by
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  rw [conditionalCoefficient_parameter_independent N γ hγ]
  apply le_antisymm (conditionalCoefficient_le N l hl hl1 hN 1)
  exact le_csSup (conditionalRatioSet_bddAbove N 1)
    (completeRatioSet_subset_conditional N 1 le_rfl
      (completeRatioSet_member N hdim l hl hN))

end
end PositiveDepolarizing
