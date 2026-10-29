module
public import ChannelKraus
public import ReplacerBounds


@[expose] public section

/-!
# The positive quantum Doeblin coefficient as a finite semidefinite program

The Choi constraint is proved equivalent to complete positivity of the residual
map using actual finite Kraus operators. The supremum is nonnegative, at most
one, and is positive exactly when a positive replacer component exists.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction

namespace PositiveReplacerSDP
noncomputable section

variable {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
theorem choiApply_replacer [Fintype B] [DecidableEq B] (P : Matrix B B ℂ) (X : Matrix A A ℂ) :
    KrausSupport.choiApply ((1 : Matrix A A ℂ) ⊗ₖ P) X = X.trace • P := by
  ext b c
  simp [KrausSupport.choiApply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.trace, Finset.sum_mul, Finset.mul_sum, mul_comm]

theorem partialTrace_omega_outer :
    partialTraceMatrix (BellSupport.outer (ChannelKraus.omega (A:=A))) =
      (1 : Matrix A A ℂ) := by
  have hω : ChannelKraus.omega (A:=A) =
      fun p : A × A => (1 : Matrix A A ℂ) p.1 p.2 := by
    ext p
    simp [ChannelKraus.omega, Matrix.one_apply]
  rw [hω, BellSupport.partialTrace_outer_matrix, Matrix.conjTranspose_one,
    Matrix.one_mul]

/-- The finite Choi constraint is equivalent to actual complete positivity of
the channel after subtracting the replacer `X ↦ Tr(X)P`. -/
theorem choi_residual_pos_iff (N : QuantumChannel A B) (P : Matrix B B ℂ) :
    (ChannelKraus.choiMatrix N - (1 : Matrix A A ℂ) ⊗ₖ P).PosSemidef ↔
      ∀ (R : Type) [Fintype R] [DecidableEq R]
        (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef →
        (amplify N.map X - partialTraceMatrix X ⊗ₖ P).PosSemidef := by
  constructor
  · intro hJ
    obtain ⟨L,hL⟩ := KrausSupport.exists_kraus_of_positive_gram _ hJ
    have hmap : ∀ X, GeneralKraus.krausMap L X = N.map X - X.trace • P := by
      intro X
      rw [hL, KrausSupport.choiApply_sub, ChannelKraus.choiApply_eq,
        choiApply_replacer]
    intro R _ _ X hX
    have hcp := GeneralKraus.completely_positive L X hX
    have heq : amplify (GeneralKraus.krausMap L) X =
        amplify N.map X - partialTraceMatrix X ⊗ₖ P := by
      ext r s
      change (GeneralKraus.krausMap L (fun a b => X (r.1,a) (s.1,b))) r.2 s.2 = _
      rw [hmap]
      rfl
    rwa [heq] at hcp
  · intro hcp
    have h := hcp A (BellSupport.outer (ChannelKraus.omega (A:=A)))
      (BellSupport.outer_posSemidef _)
    rwa [← ChannelKraus.choiMatrix_eq_amplify, partialTrace_omega_outer] at h

theorem hasPositiveReplacer_iff_choi (N : QuantumChannel A B) :
    HasPositiveReplacer N ↔
      ∃ P : Matrix B B ℂ, P.PosSemidef ∧ 0 < P.trace.re ∧
        (ChannelKraus.choiMatrix N - (1 : Matrix A A ℂ) ⊗ₖ P).PosSemidef := by
  constructor
  · rintro ⟨P,hP,htr,hres⟩
    exact ⟨P,hP,htr,(choi_residual_pos_iff N P).mpr hres⟩
  · rintro ⟨P,hP,htr,hJ⟩
    exact ⟨P,hP,htr,(choi_residual_pos_iff N P).mp hJ⟩

def Feasible (N : QuantumChannel A B) (P : Matrix B B ℂ) : Prop :=
  P.PosSemidef ∧ (ChannelKraus.choiMatrix N - (1 : Matrix A A ℂ) ⊗ₖ P).PosSemidef

def weightSet (N : QuantumChannel A B) : Set ℝ :=
  {x | ∃ P : Matrix B B ℂ, Feasible N P ∧ x = P.trace.re}

/-- Positive quantum Doeblin coefficient, with the unnormalized Choi convention. -/
def alphaPlus (N : QuantumChannel A B) : ℝ := sSup (weightSet N)

theorem zero_feasible (N : QuantumChannel A B) : Feasible N 0 := by
  refine ⟨Matrix.PosSemidef.zero, ?_⟩
  simpa only [Matrix.kronecker_zero, sub_zero] using ChannelKraus.choiMatrix_posSemidef N

theorem zero_mem_weightSet (N : QuantumChannel A B) : 0 ∈ weightSet N :=
  ⟨0, zero_feasible N, by simp⟩

theorem weightSet_nonempty (N : QuantumChannel A B) : (weightSet N).Nonempty :=
  ⟨0, zero_mem_weightSet N⟩

theorem weightSet_subset_unitInterval [Nonempty A] (N : QuantumChannel A B) :
    weightSet N ⊆ Set.Icc 0 1 := by
  rintro x ⟨P,⟨hP,hJ⟩,rfl⟩
  refine ⟨ReplacerBounds.positive_trace_re P hP, ?_⟩
  exact ReplacerBounds.replacer_trace_le_one N P hP ((choi_residual_pos_iff N P).mp hJ)

theorem weightSet_bddAbove [Nonempty A] (N : QuantumChannel A B) :
    BddAbove (weightSet N) :=
  ⟨1, fun _ hx => (weightSet_subset_unitInterval N hx).2⟩

theorem alphaPlus_nonneg [Nonempty A] (N : QuantumChannel A B) : 0 ≤ alphaPlus N :=
  le_csSup (weightSet_bddAbove N) (zero_mem_weightSet N)

theorem alphaPlus_le_one [Nonempty A] (N : QuantumChannel A B) : alphaPlus N ≤ 1 :=
  csSup_le (weightSet_nonempty N) (fun _ hx => (weightSet_subset_unitInterval N hx).2)

theorem alphaPlus_pos_iff [Nonempty A] (N : QuantumChannel A B) :
    0 < alphaPlus N ↔ HasPositiveReplacer N := by
  rw [alphaPlus, lt_csSup_iff (weightSet_bddAbove N) (weightSet_nonempty N),
    hasPositiveReplacer_iff_choi]
  constructor
  · rintro ⟨x,⟨P,⟨hP,hJ⟩,rfl⟩,hx⟩
    exact ⟨P,hP,hx,hJ⟩
  · rintro ⟨P,hP,htr,hJ⟩
    exact ⟨P.trace.re,⟨P,⟨hP,hJ⟩,rfl⟩,htr⟩

theorem alphaPlus_eq_zero_iff [Nonempty A] (N : QuantumChannel A B) :
    alphaPlus N = 0 ↔ ¬ HasPositiveReplacer N := by
  rw [← alphaPlus_pos_iff]
  constructor
  · intro h
    rw [h]
    exact lt_irrefl 0
  · intro h
    exact le_antisymm (le_of_not_gt h) (alphaPlus_nonneg N)

theorem conditionalCoefficient_le_one_sub_alphaPlus [Nonempty A]
    (N : QuantumChannel A B) (γ : ℝ) :
    ConditionalHockey.conditionalCoefficient N γ ≤ 1 - alphaPlus N := by
  have hsup : alphaPlus N ≤ 1 - ConditionalHockey.conditionalCoefficient N γ := by
    apply csSup_le (weightSet_nonempty N)
    rintro x ⟨P,⟨hP,hJ⟩,rfl⟩
    have h := ReplacerBounds.conditionalCoefficient_le_replacer N P hP
      ((choi_residual_pos_iff N P).mp hJ) γ
    linarith
  linarith

theorem completeCoefficient_le_one_sub_alphaPlus [Nonempty A]
    (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ) :
    GeneralContraction.completeCoefficient N γ ≤ 1 - alphaPlus N := by
  have hsup : alphaPlus N ≤ 1 - GeneralContraction.completeCoefficient N γ := by
    apply csSup_le (weightSet_nonempty N)
    rintro x ⟨P,⟨hP,hJ⟩,rfl⟩
    have h := ReplacerBounds.completeCoefficient_le_replacer N P hP
      ((choi_residual_pos_iff N P).mp hJ) γ hγ
    linarith
  linarith

end
end PositiveReplacerSDP
