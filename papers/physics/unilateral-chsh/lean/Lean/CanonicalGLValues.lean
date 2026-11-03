import CanonicalGL
import CanonicalSupremum

/-! Exact canonical CHSH optimization over all invertible complex filters. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

def aliceGLValues (ρ : State) : Set ℝ :=
  {z | ∃ (F : QubitMatrix) (a₀ a₁ b₀ b₁ : Vec), F.det≠0 ∧
    Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
    (bellExpectation (normalizedFiltered ρ F) a₀ a₁ b₀ b₁)^2=z}

def canonicalGLValues (c : Vec) (D : Mat3) : Set ℝ := aliceGLValues (canonical c D)

theorem normalizedFiltered_compose (ρ : State) (F G : QubitMatrix) :
    normalizedFiltered (filtered ρ F) G = normalizedFiltered ρ (G*F) := by
  unfold normalizedFiltered
  rw [filtered_compose]

theorem aliceGLValues_filter_subset (ρ : State) (W : QubitMatrix) (hW : W.det≠0) :
    aliceGLValues (filtered ρ W) ⊆ aliceGLValues ρ := by
  rintro z ⟨F,a₀,a₁,b₀,b₁,hF,hm,hz⟩
  refine ⟨F*W,a₀,a₁,b₀,b₁,?_,hm,?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero hF hW
  · rwa [normalizedFiltered_compose] at hz

theorem aliceGLValues_filter_invariant (ρ : State) (W : QubitMatrix) (hW : W.det≠0) :
    aliceGLValues (filtered ρ W)=aliceGLValues ρ := by
  apply Set.Subset.antisymm (aliceGLValues_filter_subset ρ W hW)
  have hi : W⁻¹.det≠0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hW
  have h := aliceGLValues_filter_subset (filtered ρ W) W⁻¹ hi
  have hc : W⁻¹*W=1 := Matrix.nonsing_inv_mul W (isUnit_iff_ne_zero.mpr hW)
  rwa [filtered_compose,hc,filtered_one] at h

theorem canonicalGLValues_eq_interior (c : Vec) (D : Mat3) :
    canonicalGLValues c D=interiorCHSHValues c D := by
  ext z
  constructor
  · rintro ⟨F,a₀,a₁,b₀,b₁,hF,hm,hz⟩
    obtain ⟨u,U,hu,hU,_,hstate⟩ := canonical_filter_polar c D F hF
    obtain ⟨a₀',a₁',hm',he⟩ := bell_expectation_unitary_transport
      (filtered (canonical c D) (positiveFilter u)) U hU a₀ a₁ b₀ b₁ hm
    refine ⟨u,a₀',a₁',b₀,b₁,hu,hm',?_⟩
    rwa [hstate,he] at hz
  · rintro ⟨u,a₀,a₁,b₀,b₁,hu,hm,hz⟩
    refine ⟨positiveFilter u,a₀,a₁,b₀,b₁,positive_filter_invertible u hu,hm,?_⟩
    rwa [normalizedFiltered_positiveFilter c u D hu.le]

theorem canonical_gl_isLUB (c : Vec) (D : Mat3) :
    IsLUB (canonicalGLValues c D) (Reduction.canonicalMaximum D c) := by
  rw [canonicalGLValues_eq_interior]
  exact canonical_interior_isLUB c D

theorem canonical_gl_attains_under_guard (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hguard : 1<traceThree (covariance D)-normSq c) :
    IsGreatest (canonicalGLValues c D) (Reduction.canonicalMaximum D c) := by
  rw [canonicalGLValues_eq_interior]
  exact canonical_interior_attains_under_guard c D hρ hguard

theorem canonical_gl_approximation (c : Vec) (D : Mat3) (ε : ℝ) (hε : 0<ε) :
    ∃ z∈canonicalGLValues c D, Reduction.canonicalMaximum D c-ε<z := by
  rw [canonicalGLValues_eq_interior]
  exact canonical_interior_approximation c D ε hε

theorem canonical_gl_violation_iff_maximum (c : Vec) (D : Mat3) :
    (∃ z∈canonicalGLValues c D, 1<z) ↔ 1<Reduction.canonicalMaximum D c := by
  constructor
  · rintro ⟨z,hz,hz1⟩
    exact lt_of_lt_of_le hz1 ((canonical_gl_isLUB c D).1 hz)
  · intro hm
    obtain ⟨z,hz,hv⟩ := canonical_gl_approximation c D
      ((Reduction.canonicalMaximum D c-1)/2) (by linarith)
    exact ⟨z,hz,by linarith⟩


theorem canonical_gl_activation_iff (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) :
    (∃ z∈canonicalGLValues c D, 1<z) ↔
      (1<traceThree (covariance D)-normSq c ∧
        ∃ n : Vec, normSq n=1 ∧
          quad (schurMatrix (shift (covariance D) (-normSq c))
            (crossMatrix (matVec D c)) (shift (covariance D) (-normSq c))⁻¹) n <
              traceThree (covariance D)-normSq c-1) := by
  rw [canonical_gl_violation_iff_maximum,← actual_chsh_violation_iff_maximum]
  exact canonical_actual_chsh_activation_iff c D hρ

end UnilateralCHSH.Quantum
