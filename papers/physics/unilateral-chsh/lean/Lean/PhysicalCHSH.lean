import PhysicalTheorems
import Horodecki
import QuantumCHSH

/-!
The actual four-spin CHSH operator for canonical states and every normalized
positive effect.  This closes the measurement/plane interface.  The remaining
arbitrary-original-state GL/polar/whitening interface is not assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

theorem bellExpectation_eq_chshValue (ρ : State) (a₀ a₁ b₀ b₁ : Vec) :
    bellExpectation ρ a₀ a₁ b₀ b₁ =
      Horodecki.chshValue (correlation ρ) a₀ a₁ b₀ b₁ :=
  bell_expectation_correlation ρ a₀ a₁ b₀ b₁

theorem planeValue_correlation (ρ : State) (n : Vec) :
    Horodecki.planeValue (correlation ρ) n = physicalPlane ρ n := rfl

def physicalCHSHValues (c : Vec) (D : Mat3) : Set ℝ :=
  {b | ∃ u a₀ a₁ b₀ b₁ : Vec, normSq u ≤ 1 ∧
    Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
    (bellExpectation (filtered (canonical c D) (positiveFilter u)) a₀ a₁ b₀ b₁)^2 = b}

/-- Exact attained optimization over every closed-ball effect and four actual
unit spin observables.  The displayed value is the checked reduced maximum. -/
theorem exact_physical_chsh_maximum (c : Vec) (D : Mat3) :
    IsGreatest (physicalCHSHValues c D) (Reduction.canonicalMaximum D c) := by
  constructor
  · obtain ⟨u,n,hu,hn,hv⟩ := (exact_physical_positive_filter_maximum c D).1
    obtain ⟨a₀,a₁,b₀,b₁,hm,hb⟩ := Horodecki.plane_attained
      (correlation (filtered (canonical c D) (positiveFilter u))) n hn
    refine ⟨u,a₀,a₁,b₀,b₁,hu,hm,?_⟩
    rw [bellExpectation_eq_chshValue]
    exact hb.trans hv
  · rintro z ⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩
    obtain ⟨n,hn,hb⟩ := Horodecki.measurements_bounded_by_plane
      (correlation (filtered (canonical c D) (positiveFilter u))) a₀ a₁ b₀ b₁ hm
    have hp := (exact_physical_positive_filter_maximum c D).2 ⟨u,n,hu,hn,rfl⟩
    rw [bellExpectation_eq_chshValue] at hv
    rw [hv] at hb
    exact le_trans hb hp

theorem actual_chsh_violation_iff_maximum (c : Vec) (D : Mat3) :
    (∃ u a₀ a₁ b₀ b₁ : Vec, normSq u ≤ 1 ∧
      Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
      1 < (bellExpectation (filtered (canonical c D) (positiveFilter u)) a₀ a₁ b₀ b₁)^2) ↔
      1 < Reduction.canonicalMaximum D c := by
  constructor
  · rintro ⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩
    exact lt_of_lt_of_le hv ((exact_physical_chsh_maximum c D).2
      ⟨u,a₀,a₁,b₀,b₁,hu,hm,rfl⟩)
  · intro h
    obtain ⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩ := (exact_physical_chsh_maximum c D).1
    exact ⟨u,a₀,a₁,b₀,b₁,hu,hm,by rwa [hv]⟩

theorem actual_plane_violation_iff_maximum (c : Vec) (D : Mat3) :
    (∃ u n : Vec, normSq u ≤ 1 ∧ normSq n = 1 ∧
      1 < physicalPlane (filtered (canonical c D) (positiveFilter u)) n) ↔
      1 < Reduction.canonicalMaximum D c := by
  constructor
  · rintro ⟨u,n,hu,hn,hv⟩
    exact lt_of_lt_of_le hv ((exact_physical_positive_filter_maximum c D).2
      ⟨u,n,hu,hn,rfl⟩)
  · intro h
    obtain ⟨u,n,hu,hn,hv⟩ := (exact_physical_positive_filter_maximum c D).1
    exact ⟨u,n,hu,hn,by rwa [hv]⟩

/-- Exact activation criterion for the actual four-observable CHSH expression
on the full canonical positive-filter family. -/
theorem canonical_actual_chsh_activation_iff (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) :
    (∃ u a₀ a₁ b₀ b₁ : Vec, normSq u ≤ 1 ∧
      Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
      1 < (bellExpectation (filtered (canonical c D) (positiveFilter u)) a₀ a₁ b₀ b₁)^2) ↔
    (1 < traceThree (covariance D)-normSq c ∧
      ∃ n : Vec, normSq n = 1 ∧
        quad (schurMatrix (shift (covariance D) (-normSq c))
          (crossMatrix (matVec D c)) (shift (covariance D) (-normSq c))⁻¹) n <
            traceThree (covariance D)-normSq c-1) := by
  rw [actual_chsh_violation_iff_maximum, ← actual_plane_violation_iff_maximum]
  exact canonical_activation_iff c D hρ

/-- In the strict physical guard region, an invertible filter and four
actual unit spin measurements attain the global CHSH maximum. -/
theorem canonical_actual_chsh_attained_invertibly (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hguard : 1 < traceThree (covariance D)-normSq c) :
    ∃ u a₀ a₁ b₀ b₁ : Vec, normSq u < 1 ∧
      (positiveFilter u).det ≠ 0 ∧ Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
      (filtered (canonical c D) (positiveFilter u)).PosSemidef ∧
      Matrix.trace (filtered (canonical c D) (positiveFilter u)) = 1 ∧
      (bellExpectation (filtered (canonical c D) (positiveFilter u)) a₀ a₁ b₀ b₁)^2 =
        Reduction.canonicalMaximum D c := by
  obtain ⟨r,u,n,_,hu,hn,hd,hpos,htrace,hv,hupper⟩ :=
    canonical_physical_shortcut c D hρ hguard
  have hmax : Reduction.canonicalMaximum D c =
      traceThree (covariance D)-normSq c-r := by
    apply le_antisymm
    · obtain ⟨w,z,hw,hz,heq⟩ := (exact_physical_positive_filter_maximum c D).1
      have hb := hupper w z hw hz
      rwa [heq] at hb
    · have hb := (exact_physical_positive_filter_maximum c D).2
        ⟨u,n,le_of_lt hu,hn,rfl⟩
      rwa [hv] at hb
  obtain ⟨a₀,a₁,b₀,b₁,hm,hb⟩ := Horodecki.plane_attained
    (correlation (filtered (canonical c D) (positiveFilter u))) n hn
  refine ⟨u,a₀,a₁,b₀,b₁,hu,hd,hm,hpos,htrace,?_⟩
  rw [bellExpectation_eq_chshValue,hb,planeValue_correlation,hv,hmax]

def operatorBellExpectation (ρ : State) (A₀ A₁ B₀ B₁ : Matrix Q Q ℂ) : ℝ :=
  (Matrix.trace (ρ * (onAlice A₀ * onBob B₀ + onAlice A₀ * onBob B₁ +
    onAlice A₁ * onBob B₀ - onAlice A₁ * onBob B₁))).re / 2

def physicalOperatorCHSHValues (c : Vec) (D : Mat3) : Set ℝ :=
  {b | ∃ u : Vec, ∃ A₀ A₁ B₀ B₁ : Matrix Q Q ℂ, normSq u ≤ 1 ∧
    IsSpinObservable A₀ ∧ IsSpinObservable A₁ ∧
    IsSpinObservable B₀ ∧ IsSpinObservable B₁ ∧
    (operatorBellExpectation (filtered (canonical c D) (positiveFilter u)) A₀ A₁ B₀ B₁)^2=b}

/-- Completeness of the Bloch parametrization closes the passage from actual
traceless Hermitian involutions to the four unit-vector statement. -/
theorem physicalOperatorCHSHValues_eq (c : Vec) (D : Mat3) :
    physicalOperatorCHSHValues c D = physicalCHSHValues c D := by
  ext z
  constructor
  · rintro ⟨u,A₀,A₁,B₀,B₁,hu,hA₀,hA₁,hB₀,hB₁,hv⟩
    obtain ⟨a₀,ha₀,rfl⟩ := (isSpinObservable_iff_unit_realSpin A₀).mp hA₀
    obtain ⟨a₁,ha₁,rfl⟩ := (isSpinObservable_iff_unit_realSpin A₁).mp hA₁
    obtain ⟨b₀,hb₀,rfl⟩ := (isSpinObservable_iff_unit_realSpin B₀).mp hB₀
    obtain ⟨b₁,hb₁,rfl⟩ := (isSpinObservable_iff_unit_realSpin B₁).mp hB₁
    exact ⟨u,a₀,a₁,b₀,b₁,hu,⟨ha₀,ha₁,hb₀,hb₁⟩,hv⟩
  · rintro ⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩
    exact ⟨u,realSpin a₀,realSpin a₁,realSpin b₀,realSpin b₁,hu,
      unit_realSpin_observable a₀ hm.1,unit_realSpin_observable a₁ hm.2.1,
      unit_realSpin_observable b₀ hm.2.2.1,unit_realSpin_observable b₁ hm.2.2.2,hv⟩

/-- Full actual-operator measurement optimization for every canonical positive
filter.  There are no unproved Horodecki or observable-parametrization premises. -/
theorem exact_physical_operator_chsh_maximum (c : Vec) (D : Mat3) :
    IsGreatest (physicalOperatorCHSHValues c D) (Reduction.canonicalMaximum D c) := by
  rw [physicalOperatorCHSHValues_eq]
  exact exact_physical_chsh_maximum c D

end UnilateralCHSH.Quantum
