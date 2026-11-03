import QuantumCHSH
import Horodecki
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Actual local-unitary transport of qubit observables and CHSH values. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

abbrev QubitMatrix := Matrix Q Q ℂ

def normalizeState (ρ : State) : State := (((Matrix.trace ρ).re)⁻¹ : ℂ) • ρ

def normalizedFiltered (ρ : State) (F : QubitMatrix) : State :=
  normalizeState (filtered ρ F)

def IsQubitUnitary (U : QubitMatrix) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

theorem onAlice_one : onAlice (1 : QubitMatrix) = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [onAlice, Matrix.one_apply, Prod.ext_iff]

theorem onAlice_mul (F G : QubitMatrix) : onAlice (F*G) = onAlice F * onAlice G := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [onAlice, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem onAlice_add (F G : QubitMatrix) : onAlice (F+G) = onAlice F + onAlice G := by
  ext p q
  by_cases h : p.2=q.2 <;> simp [onAlice,h]

theorem onAlice_sub (F G : QubitMatrix) : onAlice (F-G) = onAlice F - onAlice G := by
  ext p q
  by_cases h : p.2=q.2 <;> simp [onAlice,h]

theorem onAlice_smul (z : ℂ) (F : QubitMatrix) : onAlice (z • F) = z • onAlice F := by
  ext p q
  by_cases h : p.2=q.2 <;> simp [onAlice,h]

theorem onAlice_conjTranspose (F : QubitMatrix) : onAlice Fᴴ = (onAlice F)ᴴ := by
  ext p q
  by_cases h : p.2=q.2 <;> simp [onAlice, Matrix.conjTranspose_apply, h, eq_comm]

theorem onBob_mul_onAlice_apply (F G : QubitMatrix) (p q : QQ) :
    (onBob G * onAlice F) p q = G p.2 q.2 * F p.1 q.1 := by
  simp [Matrix.mul_apply, onAlice, onBob, Fintype.sum_prod_type, ite_mul, mul_ite]

theorem onAlice_onBob_commute (F G : QubitMatrix) :
    onAlice F * onBob G = onBob G * onAlice F := by
  ext p q
  rw [onAlice_mul_onBob_apply,onBob_mul_onAlice_apply]
  exact mul_comm _ _

theorem filtered_compose (ρ : State) (F G : QubitMatrix) :
    filtered (filtered ρ F) G = filtered ρ (G*F) := by
  unfold filtered
  rw [onAlice_mul,Matrix.conjTranspose_mul]
  noncomm_ring

theorem filtered_one (ρ : State) : filtered ρ 1 = ρ := by
  simp [filtered,onAlice_one]

theorem filtered_smul_state (ρ : State) (F : QubitMatrix) (z : ℂ) :
    filtered (z • ρ) F = z • filtered ρ F := by
  simp only [filtered,Matrix.mul_smul,Matrix.smul_mul]

theorem filtered_smul_filter (ρ : State) (F : QubitMatrix) (z : ℂ) :
    filtered ρ (z • F) = (z*star z) • filtered ρ F := by
  simp only [filtered,onAlice_smul,Matrix.conjTranspose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul]
  congr 1
  ring

theorem unitary_conjTranspose (U : QubitMatrix) (hU : IsQubitUnitary U) :
    IsQubitUnitary Uᴴ := by
  simpa only [IsQubitUnitary,Matrix.conjTranspose_conjTranspose] using And.symm hU

theorem unitary_onAlice_left (U : QubitMatrix) (hU : IsQubitUnitary U) :
    (onAlice U)ᴴ * onAlice U = 1 := by
  rw [← onAlice_conjTranspose,← onAlice_mul,hU.1,onAlice_one]

theorem unitary_onAlice_right (U : QubitMatrix) (hU : IsQubitUnitary U) :
    onAlice U * (onAlice U)ᴴ = 1 := by
  rw [← onAlice_conjTranspose,← onAlice_mul,hU.2,onAlice_one]

theorem conjugate_spin_observable (U O : QubitMatrix) (hU : IsQubitUnitary U)
    (hO : IsSpinObservable O) : IsSpinObservable (Uᴴ*O*U) := by
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul U hO.1,?_,?_⟩
  · calc
      (Uᴴ*O*U)*(Uᴴ*O*U) = Uᴴ*(O*(U*Uᴴ)*O)*U := by noncomm_ring
      _ = 1 := by rw [hU.2]; simp only [Matrix.mul_one,hO.2.1,Matrix.mul_one,hU.1]
  · rw [Matrix.trace_mul_cycle,hU.2,Matrix.one_mul,hO.2.2]

theorem unitary_transports_unit_spin (U : QubitMatrix) (hU : IsQubitUnitary U)
    (a : Vec) (ha : normSq a=1) :
    ∃ a' : Vec, normSq a'=1 ∧ Uᴴ*realSpin a*U = realSpin a' :=
  (isSpinObservable_iff_unit_realSpin _).mp
    (conjugate_spin_observable U (realSpin a) hU (unit_realSpin_observable a ha))

def matrixBell (A₀ A₁ B₀ B₁ : QubitMatrix) : State :=
  onAlice A₀*onBob B₀ + onAlice A₀*onBob B₁ +
    onAlice A₁*onBob B₀ - onAlice A₁*onBob B₁

theorem tensor_pullback (U A B : QubitMatrix) :
    (onAlice U)ᴴ * (onAlice A*onBob B) * onAlice U =
      onAlice (Uᴴ*A*U) * onBob B := by
  rw [← onAlice_conjTranspose,onAlice_mul,onAlice_mul]
  calc
    _ = onAlice Uᴴ * onAlice A * (onBob B*onAlice U) := by noncomm_ring
    _ = _ := by rw [← onAlice_onBob_commute]; noncomm_ring

theorem matrixBell_pullback (U A₀ A₁ B₀ B₁ : QubitMatrix) :
    (onAlice U)ᴴ * matrixBell A₀ A₁ B₀ B₁ * onAlice U =
      matrixBell (Uᴴ*A₀*U) (Uᴴ*A₁*U) B₀ B₁ := by
  unfold matrixBell
  simp only [Matrix.mul_sub,Matrix.mul_add,Matrix.sub_mul,Matrix.add_mul,tensor_pullback]

theorem trace_sandwich_move (V ρ O : State) :
    Matrix.trace ((V*ρ*Vᴴ)*O) = Matrix.trace (ρ*(Vᴴ*O*V)) := by
  calc
    _ = Matrix.trace (V*(ρ*(Vᴴ*O))) := by congr 1; noncomm_ring
    _ = Matrix.trace ((ρ*(Vᴴ*O))*V) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

theorem filtered_unitary_trace (ρ : State) (U : QubitMatrix) (hU : IsQubitUnitary U) :
    Matrix.trace (filtered ρ U) = Matrix.trace ρ := by
  calc
    _ = Matrix.trace ((onAlice U*ρ*(onAlice U)ᴴ)*1) := by simp [filtered]
    _ = Matrix.trace (ρ*((onAlice U)ᴴ*1*onAlice U)) := trace_sandwich_move _ _ _
    _ = _ := by rw [Matrix.mul_one,unitary_onAlice_left U hU,Matrix.mul_one]

theorem normalizedFiltered_unitary (ρ : State) (U : QubitMatrix) (hU : IsQubitUnitary U) :
    normalizedFiltered ρ U = filtered (normalizeState ρ) U := by
  unfold normalizedFiltered normalizeState
  rw [filtered_unitary_trace ρ U hU,filtered_smul_state]

theorem bellExpectation_smul_real (ρ : State) (r : ℝ) (a₀ a₁ b₀ b₁ : Vec) :
    bellExpectation ((r : ℂ) • ρ) a₀ a₁ b₀ b₁ =
      r*bellExpectation ρ a₀ a₁ b₀ b₁ := by
  simp only [bellExpectation,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem bell_expectation_unitary_transport (ρ : State) (U : QubitMatrix)
    (hU : IsQubitUnitary U) (a₀ a₁ b₀ b₁ : Vec)
    (hm : Horodecki.IsMeasurements a₀ a₁ b₀ b₁) :
    ∃ a₀' a₁' : Vec, Horodecki.IsMeasurements a₀' a₁' b₀ b₁ ∧
      bellExpectation (filtered ρ U) a₀ a₁ b₀ b₁ =
        bellExpectation ρ a₀' a₁' b₀ b₁ := by
  obtain ⟨a₀',h₀',he₀⟩ := unitary_transports_unit_spin U hU a₀ hm.1
  obtain ⟨a₁',h₁',he₁⟩ := unitary_transports_unit_spin U hU a₁ hm.2.1
  refine ⟨a₀',a₁',⟨h₀',h₁',hm.2.2.1,hm.2.2.2⟩,?_⟩
  unfold bellExpectation filtered
  change (Matrix.trace ((onAlice U*ρ*(onAlice U)ᴴ)*
    matrixBell (realSpin a₀) (realSpin a₁) (realSpin b₀) (realSpin b₁))).re/2 = _
  rw [trace_sandwich_move,matrixBell_pullback,he₀,he₁]
  rfl

def spinCHSHValues (ρ : State) : Set ℝ :=
  {z | ∃ a₀ a₁ b₀ b₁ : Vec, Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
    (bellExpectation ρ a₀ a₁ b₀ b₁)^2=z}

theorem unitary_spinCHSHValues_subset (ρ : State) (U : QubitMatrix)
    (hU : IsQubitUnitary U) : spinCHSHValues (filtered ρ U) ⊆ spinCHSHValues ρ := by
  rintro z ⟨a₀,a₁,b₀,b₁,hm,hz⟩
  obtain ⟨a₀',a₁',hm',he⟩ := bell_expectation_unitary_transport ρ U hU a₀ a₁ b₀ b₁ hm
  exact ⟨a₀',a₁',b₀,b₁,hm',by rwa [he] at hz⟩

theorem unitary_spinCHSHValues_eq (ρ : State) (U : QubitMatrix)
    (hU : IsQubitUnitary U) : spinCHSHValues (filtered ρ U) = spinCHSHValues ρ := by
  apply Set.Subset.antisymm (unitary_spinCHSHValues_subset ρ U hU)
  have h := unitary_spinCHSHValues_subset (filtered ρ U) Uᴴ (unitary_conjTranspose U hU)
  rwa [filtered_compose,hU.1,filtered_one] at h

end UnilateralCHSH.Quantum
