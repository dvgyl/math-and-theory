import CanonicalGLValues
import QuantumGLPhysical

/-! Actual interchange of the two qubits, including Bob filters and the
four-observable CHSH value set. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

def swapState (ρ : State) : State := ρ.submatrix Prod.swap Prod.swap

def filteredBob (ρ : State) (F : QubitMatrix) : State :=
  onBob F * ρ * (onBob F)ᴴ

def normalizedFilteredBob (ρ : State) (F : QubitMatrix) : State :=
  normalizeState (filteredBob ρ F)

def bobGLValues (ρ : State) : Set ℝ :=
  {z | ∃ (F : QubitMatrix) (a₀ a₁ b₀ b₁ : Vec), F.det≠0 ∧
    Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
    (bellExpectation (normalizedFilteredBob ρ F) a₀ a₁ b₀ b₁)^2=z}

theorem swapState_involution (ρ : State) : swapState (swapState ρ)=ρ := by
  ext p q
  rfl

theorem swapState_add (ρ σ : State) : swapState (ρ+σ)=swapState ρ+swapState σ := rfl

theorem swapState_sub (ρ σ : State) : swapState (ρ-σ)=swapState ρ-swapState σ := rfl

theorem swapState_smul (z : ℂ) (ρ : State) : swapState (z • ρ)=z • swapState ρ := rfl

theorem swapState_mul (ρ σ : State) : swapState (ρ*σ)=swapState ρ*swapState σ :=
  Matrix.submatrix_mul ρ σ Prod.swap Prod.swap Prod.swap (Equiv.prodComm Q Q).bijective

theorem swapState_conjTranspose (ρ : State) : swapState ρᴴ=(swapState ρ)ᴴ := rfl

theorem swapState_trace (ρ : State) : Matrix.trace (swapState ρ)=Matrix.trace ρ := by
  simp only [swapState,Matrix.trace,Matrix.diag,Matrix.submatrix_apply,Fintype.sum_prod_type,Prod.swap]
  rw [Finset.sum_comm]

theorem swapState_posSemidef (ρ : State) (hρ : ρ.PosSemidef) :
    (swapState ρ).PosSemidef := hρ.submatrix Prod.swap

theorem swapState_onAlice (F : QubitMatrix) : swapState (onAlice F)=onBob F := rfl

theorem swapState_onBob (F : QubitMatrix) : swapState (onBob F)=onAlice F := rfl

theorem swapState_filteredBob (ρ : State) (F : QubitMatrix) :
    swapState (filteredBob ρ F)=filtered (swapState ρ) F := by
  simp only [filteredBob,filtered,swapState_mul,swapState_conjTranspose,swapState_onBob]

theorem swapState_filtered (ρ : State) (F : QubitMatrix) :
    swapState (filtered ρ F)=filteredBob (swapState ρ) F := by
  simp only [filteredBob,filtered,swapState_mul,swapState_conjTranspose,swapState_onAlice]

theorem swapState_normalizeState (ρ : State) :
    swapState (normalizeState ρ)=normalizeState (swapState ρ) := by
  unfold normalizeState
  rw [swapState_smul,swapState_trace]

theorem swapState_normalizedFilteredBob (ρ : State) (F : QubitMatrix) :
    swapState (normalizedFilteredBob ρ F)=normalizedFiltered (swapState ρ) F := by
  unfold normalizedFilteredBob normalizedFiltered
  rw [swapState_normalizeState,swapState_filteredBob]

theorem swapState_normalizedFiltered (ρ : State) (F : QubitMatrix) :
    swapState (normalizedFiltered ρ F)=normalizedFilteredBob (swapState ρ) F := by
  unfold normalizedFilteredBob normalizedFiltered
  rw [swapState_normalizeState,swapState_filtered]


theorem filteredBob_trace_positive (ρ : State) (F : QubitMatrix)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) (hF : F.det≠0) :
    0<(Matrix.trace (filteredBob ρ F)).re := by
  have hp := filtered_trace_positive (swapState ρ) F (swapState_posSemidef ρ hρ)
    (by rw [swapState_trace]; exact ht) hF
  rwa [← swapState_filteredBob,swapState_trace] at hp

theorem normalizedFilteredBob_density (ρ : State) (F : QubitMatrix)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ=1) (hF : F.det≠0) :
    (normalizedFilteredBob ρ F).PosSemidef ∧
      Matrix.trace (normalizedFilteredBob ρ F)=1 := by
  have ha := normalizedFiltered_density (swapState ρ) F (swapState_posSemidef ρ hρ)
    (by rw [swapState_trace]; exact ht) hF
  have hp := swapState_posSemidef _ ha.1
  rw [← swapState_normalizedFilteredBob,swapState_involution] at hp
  refine ⟨hp,?_⟩
  rw [← swapState_trace (normalizedFilteredBob ρ F),swapState_normalizedFilteredBob,ha.2]

theorem swapState_bellOperator (a₀ a₁ b₀ b₁ : Vec) :
    swapState (bellOperator a₀ a₁ b₀ b₁)=bellOperator b₀ b₁ a₀ a₁ := by
  simp only [bellOperator,spinProduct,swapState_add,swapState_sub,swapState_mul,
    swapState_onAlice,swapState_onBob,← onAlice_onBob_commute]
  noncomm_ring

theorem bellExpectation_swap (ρ : State) (a₀ a₁ b₀ b₁ : Vec) :
    bellExpectation (swapState ρ) b₀ b₁ a₀ a₁=bellExpectation ρ a₀ a₁ b₀ b₁ := by
  unfold bellExpectation
  rw [← swapState_bellOperator a₀ a₁ b₀ b₁,← swapState_mul,swapState_trace]

theorem bobGLValues_eq_alice_swap (ρ : State) :
    bobGLValues ρ=aliceGLValues (swapState ρ) := by
  ext z
  constructor
  · rintro ⟨F,a₀,a₁,b₀,b₁,hF,hm,hz⟩
    refine ⟨F,b₀,b₁,a₀,a₁,hF,⟨hm.2.2.1,hm.2.2.2,hm.1,hm.2.1⟩,?_⟩
    rw [← swapState_normalizedFilteredBob,bellExpectation_swap]
    exact hz
  · rintro ⟨F,a₀,a₁,b₀,b₁,hF,hm,hz⟩
    refine ⟨F,b₀,b₁,a₀,a₁,hF,⟨hm.2.2.1,hm.2.2.2,hm.1,hm.2.1⟩,?_⟩
    rwa [← swapState_normalizedFilteredBob,bellExpectation_swap] at hz

theorem swapState_blochState (a b : Vec) (T : Mat3) :
    swapState (blochState a b T)=blochState b a T.transpose := by
  ext p q
  rcases p with ⟨p₀,p₁⟩
  rcases q with ⟨q₀,q₁⟩
  fin_cases p₀ <;> fin_cases p₁ <;> fin_cases q₀ <;> fin_cases q₁ <;> apply Complex.ext <;>
    simp [swapState,blochState,onAlice,onBob,pauli,Fin.sum_univ_three,
      Matrix.transpose_apply,Prod.ext_iff,Complex.mul_re,Complex.mul_im]
  all_goals ring

end UnilateralCHSH.Quantum
