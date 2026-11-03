import AllStates

/-!
The full operator interface: four arbitrary nondegenerate qubit spin
observables, defined as traceless Hermitian involutions.  Their equivalence
with unit Bloch vectors is proved, and the actual GL-filter supremum and
activation results are transported through that equivalence.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

def matrixBellExpectation (ρ : State) (A₀ A₁ B₀ B₁ : QubitMatrix) : ℝ :=
  (Matrix.trace (ρ*matrixBell A₀ A₁ B₀ B₁)).re/2

def operatorCHSHValues (ρ : State) : Set ℝ :=
  {z | ∃ A₀ A₁ B₀ B₁ : QubitMatrix,
    IsSpinObservable A₀ ∧ IsSpinObservable A₁ ∧
    IsSpinObservable B₀ ∧ IsSpinObservable B₁ ∧
    (matrixBellExpectation ρ A₀ A₁ B₀ B₁)^2=z}

def aliceOperatorGLValues (ρ : State) : Set ℝ :=
  {z | ∃ F : QubitMatrix, F.det≠0 ∧ z∈operatorCHSHValues (normalizedFiltered ρ F)}

def bobOperatorGLValues (ρ : State) : Set ℝ :=
  {z | ∃ F : QubitMatrix, F.det≠0 ∧ z∈operatorCHSHValues (normalizedFilteredBob ρ F)}

theorem matrixBellExpectation_spin (ρ : State) (a₀ a₁ b₀ b₁ : Vec) :
    matrixBellExpectation ρ (realSpin a₀) (realSpin a₁) (realSpin b₀) (realSpin b₁)=
      bellExpectation ρ a₀ a₁ b₀ b₁ := rfl

theorem operatorCHSHValues_eq_spinCHSHValues (ρ : State) :
    operatorCHSHValues ρ=spinCHSHValues ρ := by
  ext z
  constructor
  · rintro ⟨A₀,A₁,B₀,B₁,hA₀,hA₁,hB₀,hB₁,hz⟩
    obtain ⟨a₀,ha₀,rfl⟩ := (isSpinObservable_iff_unit_realSpin A₀).mp hA₀
    obtain ⟨a₁,ha₁,rfl⟩ := (isSpinObservable_iff_unit_realSpin A₁).mp hA₁
    obtain ⟨b₀,hb₀,rfl⟩ := (isSpinObservable_iff_unit_realSpin B₀).mp hB₀
    obtain ⟨b₁,hb₁,rfl⟩ := (isSpinObservable_iff_unit_realSpin B₁).mp hB₁
    exact ⟨a₀,a₁,b₀,b₁,⟨ha₀,ha₁,hb₀,hb₁⟩,hz⟩
  · rintro ⟨a₀,a₁,b₀,b₁,hm,hz⟩
    exact ⟨realSpin a₀,realSpin a₁,realSpin b₀,realSpin b₁,
      unit_realSpin_observable a₀ hm.1,unit_realSpin_observable a₁ hm.2.1,
      unit_realSpin_observable b₀ hm.2.2.1,unit_realSpin_observable b₁ hm.2.2.2,hz⟩

theorem aliceOperatorGLValues_eq (ρ : State) : aliceOperatorGLValues ρ=aliceGLValues ρ := by
  ext z
  constructor
  · rintro ⟨F,hF,hz⟩
    rw [operatorCHSHValues_eq_spinCHSHValues] at hz
    obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ := hz
    exact ⟨F,a₀,a₁,b₀,b₁,hF,hm,hv⟩
  · rintro ⟨F,a₀,a₁,b₀,b₁,hF,hm,hv⟩
    refine ⟨F,hF,?_⟩
    rw [operatorCHSHValues_eq_spinCHSHValues]
    exact ⟨a₀,a₁,b₀,b₁,hm,hv⟩

theorem bobOperatorGLValues_eq (ρ : State) : bobOperatorGLValues ρ=bobGLValues ρ := by
  ext z
  constructor
  · rintro ⟨F,hF,hz⟩
    rw [operatorCHSHValues_eq_spinCHSHValues] at hz
    obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ := hz
    exact ⟨F,a₀,a₁,b₀,b₁,hF,hm,hv⟩
  · rintro ⟨F,a₀,a₁,b₀,b₁,hF,hm,hv⟩
    refine ⟨F,hF,?_⟩
    rw [operatorCHSHValues_eq_spinCHSHValues]
    exact ⟨a₀,a₁,b₀,b₁,hm,hv⟩

theorem operatorCHSHValues_upper_iff (ρ : State) (bound : ℝ) :
    (∀ z∈operatorCHSHValues ρ, z≤bound) ↔
      ∀ n : Vec, normSq n=1 → Horodecki.planeValue (correlation ρ) n≤bound := by
  rw [operatorCHSHValues_eq_spinCHSHValues]
  constructor
  · intro h
    apply (Horodecki.exact_chsh_bound (correlation ρ) bound).mpr
    intro a₀ a₁ b₀ b₁ hm
    have hh := h ((bellExpectation ρ a₀ a₁ b₀ b₁)^2) ⟨a₀,a₁,b₀,b₁,hm,rfl⟩
    simpa only [bell_expectation_correlation,Horodecki.chshValue] using hh
  · intro h
    rintro z ⟨a₀,a₁,b₀,b₁,hm,hz⟩
    rw [←hz,bell_expectation_correlation]
    exact (Horodecki.exact_chsh_bound (correlation ρ) bound).mp h a₀ a₁ b₀ b₁ hm

theorem all_states_operator_both_isLUB (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    IsLUB (aliceOperatorGLValues ρ) (aliceMaximum ρ) ∧
      IsLUB (bobOperatorGLValues ρ) (bobMaximum ρ) := by
  rw [aliceOperatorGLValues_eq,bobOperatorGLValues_eq]
  exact all_states_both_isLUB ρ hρ ht

theorem all_states_alice_operator_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (∃ z∈aliceOperatorGLValues ρ, 1<z) ↔ aliceActivationCondition ρ := by
  rw [aliceOperatorGLValues_eq]
  exact all_states_alice_activation_iff ρ hρ ht

theorem all_states_bob_operator_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (∃ z∈bobOperatorGLValues ρ, 1<z) ↔ aliceActivationCondition (swapState ρ) := by
  rw [bobOperatorGLValues_eq]
  exact all_states_bob_activation_iff ρ hρ ht

theorem all_states_alice_operator_hidden_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    ((∀ z∈operatorCHSHValues ρ, z≤1) ∧ ∃ z∈aliceOperatorGLValues ρ, 1<z) ↔
      ((∀ n : Vec, normSq n=1 → Horodecki.planeValue (correlation ρ) n≤1) ∧
        aliceActivationCondition ρ) :=
  and_congr (operatorCHSHValues_upper_iff ρ 1)
    (all_states_alice_operator_activation_iff ρ hρ ht)

theorem all_states_bob_operator_hidden_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    ((∀ z∈operatorCHSHValues ρ, z≤1) ∧ ∃ z∈bobOperatorGLValues ρ, 1<z) ↔
      ((∀ n : Vec, normSq n=1 → Horodecki.planeValue (correlation ρ) n≤1) ∧
        aliceActivationCondition (swapState ρ)) :=
  and_congr (operatorCHSHValues_upper_iff ρ 1)
    (all_states_bob_operator_activation_iff ρ hρ ht)

theorem all_states_alice_operator_violation_attained (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (hv : ∃ z∈aliceOperatorGLValues ρ, 1<z) :
    IsGreatest (aliceOperatorGLValues ρ) (aliceMaximum ρ) := by
  rw [aliceOperatorGLValues_eq] at hv ⊢
  exact all_states_alice_violation_attained ρ hρ ht hv

theorem all_states_bob_operator_violation_attained (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (hv : ∃ z∈bobOperatorGLValues ρ, 1<z) :
    IsGreatest (bobOperatorGLValues ρ) (bobMaximum ρ) := by
  rw [bobOperatorGLValues_eq] at hv ⊢
  exact all_states_bob_violation_attained ρ hρ ht hv

end UnilateralCHSH.Quantum
