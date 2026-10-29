module
public import ChannelKraus
public import SimplexPreparation
public import PhaseTransport
public import ReplacerBounds


@[expose] public section

/-!
# Strict contraction is equivalent to a positive replacer component

All coefficients below are the actual suprema over normalized density matrices
and arbitrary finite quantum references. Complete coefficients additionally
require identical reference marginals. The input dimension is nonzero.
-/
open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey GeneralContraction
open KrausChannelSaturation

namespace UniversalContraction
noncomputable section
set_option maxHeartbeats 3000000
variable {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B]

/-- Failure of every positive replacer minorant forces unit complete hockey-stick
contraction at each fixed parameter strictly above one. -/
theorem complete_eq_one_of_no_positiveReplacer (N : QuantumChannel A B)
    (hN : ¬ HasPositiveReplacer N) (γ : ℝ) (hγ : 1 < γ) :
    GeneralContraction.completeCoefficient N γ = 1 := by
  let I := A × (A × Bool)
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let ρ : Option I → Density (A × A) := fun i => match i with
    | none => BellSupport.bellDensity a₀ a₀ false
    | some p => BellSupport.bellDensity p.1 p.2.1 p.2.2
  let σ : Option I → Density (A × B) := fun i => N.outputDensity (ρ i)
  have hz : ∀ w : A × B → ℂ,
      (∀ i, w ∈ LinearMap.range (σ i).mat.toLin') → w = 0 := by
    intro w hw
    apply ChannelKraus.bell_output_common_range_zero N hN w
    intro a b e
    simpa only [σ, ρ, QuantumChannel.outputDensity, Matrix.toLin'_apply'] using
      hw (some (a,(b,e)))
  let E₀ := SimplexPreparation.preparedDensityChannel ρ
  let M₀ := SimplexPreparation.preparedDensityChannel σ
  obtain ⟨D,hquad,hcross⟩ := SimplexPreparation.preparedDensity_intertwiner σ hz
  let E := PhaseTransport.reindexChannel E₀ (Equiv.prodAssoc (Option I) A A)
  let M := PhaseTransport.reindexChannel M₀ (Equiv.prodAssoc (Option I) A B)
  let D' := D.submatrix (Equiv.prodAssoc (Option I) A B) (Equiv.prodAssoc (Option I) A B)
  have hi := PhaseTransport.reindex_intertwiner M₀ D
    (Equiv.prodAssoc (Option I) A B) hquad hcross
  have hM : ∀ X, M.map X = amplify N.map (E.map X) := by
    intro X
    have hn := SimplexPreparation.preparedDensityChannel_natural
      (PhaseTransport.amplifyLinear (R := A) N.map) ρ σ (fun _ => rfl) X
    ext ⟨⟨r,a⟩,b⟩ ⟨⟨s,c⟩,d⟩
    change M₀.map X (r,(a,b)) (s,(c,d)) =
      N.map (fun u v => E₀.map X (r,(a,u)) (s,(c,v))) b d
    exact (congrArg (fun Y : Matrix (Option I × (A × B)) (Option I × (A × B)) ℂ =>
      Y (r,(a,b)) (s,(c,d))) hn).symm
  have href : partialTraceMatrix (E.map (matrixUnit 0 1)) = 0 := by
    have hcommon : ∀ i : Option I,
        partialTraceMatrix (ρ i).mat = partialTraceMatrix (ρ none).mat := by
      intro i
      cases i with
      | none => rfl
      | some p => exact BellSupport.bellDensity_common_marginal p.1 p.2.1 a₀ a₀ p.2.2 false
    ext ⟨r,a⟩ ⟨s,b⟩
    change (∑ z : A, E₀.map (matrixUnit 0 1) (r,(a,z)) (s,(b,z))) = 0
    exact SimplexPreparation.preparedDensity_cross_marginal ρ _ hcommon r s a b
  exact PhaseTransport.completeCoefficient_eq_one N E M D' hM href hi.1 hi.2 γ hγ

/-- Universal strictness criterion for complete hockey-stick contraction. -/
theorem complete_lt_one_iff_positiveReplacer (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 < γ) :
    GeneralContraction.completeCoefficient N γ < 1 ↔ HasPositiveReplacer N := by
  constructor
  · intro h
    by_contra hN
    rw [complete_eq_one_of_no_positiveReplacer N hN γ hγ] at h
    exact (lt_irrefl 1) h
  · intro hN
    exact ReplacerBounds.completeCoefficient_lt_one_of_positiveReplacer N hN γ hγ.le

theorem complete_eq_one_iff_no_positiveReplacer (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 < γ) :
    GeneralContraction.completeCoefficient N γ = 1 ↔ ¬ HasPositiveReplacer N := by
  constructor
  · intro h hN
    have hs := (complete_lt_one_iff_positiveReplacer N γ hγ).mpr hN
    rw [h] at hs
    exact (lt_irrefl 1) hs
  · exact fun hN => complete_eq_one_of_no_positiveReplacer N hN γ hγ

/-- The parameter-one conditional coefficient is the conditional trace-distance
coefficient, by the checked `hockeyStick_one_eq_traceDistance` identity. -/
theorem conditional_trace_eq_one_of_no_positiveReplacer (N : QuantumChannel A B)
    (hN : ¬ HasPositiveReplacer N) :
    ConditionalHockey.conditionalCoefficient N 1 = 1 := by
  apply GeneralContraction.conditionalCoefficient_eq_one_of_complete N 2 (by norm_num)
  exact complete_eq_one_of_no_positiveReplacer N hN 2 (by norm_num)

theorem conditional_eq_one_of_no_positiveReplacer (N : QuantumChannel A B)
    (hN : ¬ HasPositiveReplacer N) (γ : ℝ) (hγ : 1 ≤ γ) :
    ConditionalHockey.conditionalCoefficient N γ = 1 := by
  rw [ConditionalHockey.conditionalCoefficient_parameter_independent N γ hγ]
  exact conditional_trace_eq_one_of_no_positiveReplacer N hN

/-- Universal strictness criterion for the conditional trace-distance coefficient
and every conditional hockey-stick coefficient of parameter at least one. -/
theorem conditional_lt_one_iff_positiveReplacer (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 ≤ γ) :
    ConditionalHockey.conditionalCoefficient N γ < 1 ↔ HasPositiveReplacer N := by
  constructor
  · intro h
    by_contra hN
    rw [conditional_eq_one_of_no_positiveReplacer N hN γ hγ] at h
    exact (lt_irrefl 1) h
  · intro hN
    exact ReplacerBounds.conditionalCoefficient_lt_one_of_positiveReplacer N hN γ

theorem conditional_eq_one_iff_no_positiveReplacer (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 ≤ γ) :
    ConditionalHockey.conditionalCoefficient N γ = 1 ↔ ¬ HasPositiveReplacer N := by
  constructor
  · intro h hN
    have hs := (conditional_lt_one_iff_positiveReplacer N γ hγ).mpr hN
    rw [h] at hs
    exact (lt_irrefl 1) hs
  · exact fun hN => conditional_eq_one_of_no_positiveReplacer N hN γ hγ

end
end UniversalContraction
