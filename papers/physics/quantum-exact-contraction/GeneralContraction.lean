import KrausChannelSaturation
import Mathlib.Data.Matrix.Kronecker

/-! Complete contraction and positive replacer components in arbitrary finite dimensions. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace GeneralContraction
noncomputable section
variable {A B R n m : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def completeRatioSet (N : QuantumChannel A B) (γ : ℝ) : Set ℝ := {r |
  ∃ (R : FiniteReference) (ρ σ : Density (R.Carrier × A)),
    partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat ∧
    0 < hockeyStick γ ρ σ ∧
    r = hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) / hockeyStick γ ρ σ}

def completeCoefficient (N : QuantumChannel A B) (γ : ℝ) : ℝ :=
  sSup (completeRatioSet N γ)

/-- The channel contains a nonzero positive replacer map in the CP order. -/
def HasPositiveReplacer (N : QuantumChannel A B) : Prop :=
  ∃ P : Matrix B B ℂ, P.PosSemidef ∧ 0 < P.trace.re ∧
    ∀ (R : Type) [Fintype R] [DecidableEq R]
      (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef →
      (amplify N.map X - (partialTraceMatrix X) ⊗ₖ P).PosSemidef

theorem hockey_output_eq (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) :
    hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) =
      positiveTrace (amplify N.map (difference γ ρ σ))
        (N.amplify_hermitian _ (difference_hermitian γ ρ σ)) := by
  unfold hockeyStick
  congr 1
  simp only [difference, QuantumChannel.outputDensity, amplify_sub, amplify_real_smul]

theorem hockey_output_le (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) :
    hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) ≤ hockeyStick γ ρ σ := by
  rw [hockey_output_eq]
  unfold hockeyStick
  rw [positiveTrace_eq, positiveTrace_eq, N.amplify_trace]
  linarith [N.amplify_norm_le (difference γ ρ σ) (difference_hermitian γ ρ σ)]

theorem hockey_nonneg (γ : ℝ) (ρ σ : Density n) : 0 ≤ hockeyStick γ ρ σ := by
  exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem completeRatioSet_subset_unitInterval (N : QuantumChannel A B) (γ : ℝ) :
    completeRatioSet N γ ⊆ Set.Icc 0 1 := by
  rintro r ⟨R,ρ,σ,_,hpos,rfl⟩
  constructor
  · exact div_nonneg (hockey_nonneg γ _ _) hpos.le
  · apply (div_le_iff₀ hpos).mpr
    simpa using hockey_output_le N γ ρ σ

theorem completeRatioSet_bddAbove (N : QuantumChannel A B) (γ : ℝ) :
    BddAbove (completeRatioSet N γ) :=
  ⟨1, fun _ hr => (completeRatioSet_subset_unitInterval N γ hr).2⟩

theorem completeCoefficient_le_one (N : QuantumChannel A B) (γ : ℝ) :
    completeCoefficient N γ ≤ 1 := by
  by_cases hn : (completeRatioSet N γ).Nonempty
  · exact csSup_le hn (fun _ hr => (completeRatioSet_subset_unitInterval N γ hr).2)
  · have he : completeRatioSet N γ = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [completeCoefficient, he]

theorem completeCoefficient_nonneg (N : QuantumChannel A B) (γ : ℝ) :
    0 ≤ completeCoefficient N γ := by
  by_cases hn : (completeRatioSet N γ).Nonempty
  · obtain ⟨r,hr⟩ := hn
    exact (completeRatioSet_subset_unitInterval N γ hr).1.trans
      (le_csSup (completeRatioSet_bddAbove N γ) hr)
  · have he : completeRatioSet N γ = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [completeCoefficient, he]

theorem finalGap_eq_hockey_of_equalReference (N : QuantumChannel A B) (γ : ℝ)
    (hγ : 1 ≤ γ) (ρ σ : Density (R × A))
    (href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat) :
    finalGap N γ ρ σ = hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) := by
  rw [finalGap_eq_output]
  apply KrausChannelSaturation.initialGap_eq_hockey_of_equalReference γ hγ
  simpa only [QuantumChannel.outputDensity, N.partialTrace_amplify] using href

theorem completeRatioSet_subset_conditional (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ) :
    completeRatioSet N γ ⊆ ConditionalHockey.conditionalRatioSet N γ := by
  rintro r ⟨R,ρ,σ,href,hpos,hr⟩
  refine ⟨R,ρ,σ,?_,?_⟩
  · rw [KrausChannelSaturation.initialGap_eq_hockey_of_equalReference γ hγ ρ σ href]
    exact hpos
  · rw [KrausChannelSaturation.initialGap_eq_hockey_of_equalReference γ hγ ρ σ href,
      finalGap_eq_hockey_of_equalReference N γ hγ ρ σ href]
    exact hr

theorem conditionalCoefficient_le_one (N : QuantumChannel A B) (γ : ℝ) :
    ConditionalHockey.conditionalCoefficient N γ ≤ 1 := by
  by_cases hn : (ConditionalHockey.conditionalRatioSet N γ).Nonempty
  · exact csSup_le hn (fun _ hr => (ConditionalHockey.conditionalRatioSet_subset_unitInterval N γ hr).2)
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp [ConditionalHockey.conditionalCoefficient, he]

theorem conditionalCoefficient_eq_one_of_complete [Nonempty A]
    (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ)
    (h : completeCoefficient N γ = 1) :
    ConditionalHockey.conditionalCoefficient N 1 = 1 := by
  have hn : (completeRatioSet N γ).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp [completeCoefficient, he] at h
  have hi := completeRatioSet_subset_conditional N γ hγ
  have hb := ConditionalHockey.conditionalRatioSet_bddAbove N γ
  have hle : completeCoefficient N γ ≤ ConditionalHockey.conditionalCoefficient N γ :=
    csSup_le hn (fun _ hr => le_csSup hb (hi hr))
  have he : ConditionalHockey.conditionalCoefficient N γ = 1 := by
    apply le_antisymm (conditionalCoefficient_le_one N γ)
    simpa [h] using hle
  rwa [ConditionalHockey.conditionalCoefficient_parameter_independent N γ hγ] at he

/-- A positive subtraction-preserving map with scaled real trace contracts by that scale. -/
theorem traceNorm_map_le_scale (Φ : Matrix n n ℂ → Matrix m m ℂ) (c : ℝ)
    (hsub : ∀ X Y, Φ (X-Y) = Φ X-Φ Y)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (htrace : ∀ X, (Φ X).trace.re = c * X.trace.re)
    (X : Matrix n n ℂ) (hX : X.IsHermitian) (hΦX : (Φ X).IsHermitian) :
    traceNorm (Φ X) hΦX ≤ c * traceNorm X hX := by
  obtain ⟨P,Q,hP,hQ,heq,hcost⟩ := exists_posSemidef_decomposition X hX
  have hm : Φ X = Φ P-Φ Q := by rw [heq,hsub]
  have h := traceNorm_sub_le_of_posSemidef (Φ P) (Φ Q) (hpos P hP) (hpos Q hQ)
  simpa only [← hm,htrace,← mul_add,hcost] using h

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem kronecker_conjTranspose [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    (X ⊗ₖ Y)ᴴ = Xᴴ ⊗ₖ Yᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem kronecker_hermitian (X : Matrix n n ℂ) (Y : Matrix m m ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : (X ⊗ₖ Y).IsHermitian := by
  change (X ⊗ₖ Y)ᴴ = X ⊗ₖ Y
  rw [kronecker_conjTranspose,hX.eq,hY.eq]

theorem kronecker_positive (X : Matrix n n ℂ) (Y : Matrix m m ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (X ⊗ₖ Y).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (hX.sqrt ⊗ₖ hY.sqrt)
  rw [kronecker_conjTranspose,hX.posSemidef_sqrt.1.eq,hY.posSemidef_sqrt.1.eq,
    ← Matrix.mul_kronecker_mul,hX.sqrt_mul_self,hY.sqrt_mul_self] at h
  exact h

end
end GeneralContraction
