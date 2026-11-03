import PhysicalCHSH
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.FunProp

/-! The actual continuous filter map and the open-ball supremum. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Matrix
open scoped Topology ComplexOrder

namespace UnilateralCHSH.Quantum

theorem continuous_normSq : Continuous (normSq : Vec → ℝ) := by
  unfold normSq dot
  fun_prop

theorem continuous_filterRadius : Continuous filterRadius :=
  Real.continuous_sqrt.comp (continuous_const.sub continuous_normSq)

theorem continuous_filterScale : Continuous filterScale :=
  Real.continuous_sqrt.comp
    (continuous_const.mul (continuous_const.add continuous_filterRadius))

theorem continuous_realSpin : Continuous realSpin := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [realSpin,complexSpin]
  all_goals fun_prop

theorem continuous_positiveFilter : Continuous positiveFilter := by
  have ha : Continuous (fun u : Vec => (1+filterRadius u)/filterScale u) :=
    (continuous_const.add continuous_filterRadius).div continuous_filterScale
      (fun u => ne_of_gt (filterScale_pos u))
  have hb : Continuous (fun u : Vec => 1/filterScale u) :=
    continuous_const.div continuous_filterScale (fun u => ne_of_gt (filterScale_pos u))
  exact ((Complex.continuous_ofReal.comp ha).smul continuous_const).add
    ((Complex.continuous_ofReal.comp hb).smul continuous_realSpin)

theorem continuous_onAlice : Continuous onAlice := by
  apply continuous_matrix
  intro i j
  by_cases h : i.2=j.2
  · simp only [onAlice,h,if_true]
    fun_prop
  · simp only [onAlice,h,if_false]
    exact continuous_const

theorem continuous_positive_filtered (ρ : State) :
    Continuous (fun u : Vec => filtered ρ (positiveFilter u)) := by
  have h := continuous_onAlice.comp continuous_positiveFilter
  exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose

theorem continuous_positive_bell (ρ : State) (a₀ a₁ b₀ b₁ : Vec) :
    Continuous (fun u : Vec => bellExpectation (filtered ρ (positiveFilter u)) a₀ a₁ b₀ b₁) := by
  have h := ((continuous_positive_filtered ρ).matrix_mul
    (continuous_const (y:=bellOperator a₀ a₁ b₀ b₁))).matrix_trace
  exact (Complex.continuous_re.comp h).div_const 2

theorem continuous_positive_bell_squared (ρ : State) (a₀ a₁ b₀ b₁ : Vec) :
    Continuous (fun u : Vec =>
      (bellExpectation (filtered ρ (positiveFilter u)) a₀ a₁ b₀ b₁)^2) :=
  (continuous_positive_bell ρ a₀ a₁ b₀ b₁).pow 2

theorem radial_normSq (r : ℝ) (u : Vec) :
    normSq (fun i => r*u i) = r^2*normSq u := by
  simp only [normSq,dot]
  ring

theorem radial_strict (u : Vec) (hu : normSq u≤1) (r : ℝ)
    (hr : r∈Ioo (0:ℝ) 1) : normSq (fun i => r*u i)<1 := by
  rw [radial_normSq]
  have hs : r^2<1 := by nlinarith [hr.1,hr.2]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (sq_nonneg r) hu) hs

/-- An upper bound on every invertible effect extends to every boundary
effect by actual continuity, not by assuming equality of the suprema. -/
theorem closed_upper_of_interior_upper (f : Vec → ℝ) (hf : Continuous f)
    (bound : ℝ) (hbound : ∀ u : Vec, normSq u<1 → f u≤bound)
    (u : Vec) (hu : normSq u≤1) : f u≤bound := by
  let g : ℝ → ℝ := fun r => f (fun i => r*u i)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hsub : Ioo (0:ℝ) 1 ⊆ {r | g r≤bound} := by
    intro r hr
    exact hbound _ (radial_strict u hu r hr)
  have hc : (1:ℝ)∈closure (Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
    norm_num
  have h := closure_minimal hsub (isClosed_le hg continuous_const) hc
  change f (fun i => (1:ℝ)*u i) ≤ bound at h
  simpa only [one_mul] using h

def interiorCHSHValues (c : Vec) (D : Mat3) : Set ℝ :=
  {z | ∃ u a₀ a₁ b₀ b₁ : Vec, normSq u<1 ∧
    Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
    (bellExpectation (filtered (canonical c D) (positiveFilter u)) a₀ a₁ b₀ b₁)^2=z}

theorem interiorCHSHValues_subset (c : Vec) (D : Mat3) :
    interiorCHSHValues c D ⊆ physicalCHSHValues c D := by
  rintro z ⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩
  exact ⟨u,a₀,a₁,b₀,b₁,le_of_lt hu,hm,hv⟩

/-- Exact supremum over the OPEN effect ball, including cases whose only
closed-ball optimizers are rank-one filters. -/
theorem canonical_interior_isLUB (c : Vec) (D : Mat3) :
    IsLUB (interiorCHSHValues c D) (Reduction.canonicalMaximum D c) := by
  constructor
  · intro z hz
    exact (exact_physical_chsh_maximum c D).2 (interiorCHSHValues_subset c D hz)
  · intro bound hb
    obtain ⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩ := (exact_physical_chsh_maximum c D).1
    rw [← hv]
    apply closed_upper_of_interior_upper _
      (continuous_positive_bell_squared (canonical c D) a₀ a₁ b₀ b₁) bound _ u hu
    intro v hvi
    exact hb ⟨v,a₀,a₁,b₀,b₁,hvi,hm,rfl⟩

theorem canonical_interior_attains_under_guard (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hguard : 1<traceThree (covariance D)-normSq c) :
    IsGreatest (interiorCHSHValues c D) (Reduction.canonicalMaximum D c) := by
  obtain ⟨u,a₀,a₁,b₀,b₁,hu,_,hm,_,_,hv⟩ :=
    canonical_actual_chsh_attained_invertibly c D hρ hguard
  exact ⟨⟨u,a₀,a₁,b₀,b₁,hu,hm,hv⟩,(canonical_interior_isLUB c D).1⟩

theorem canonical_interior_approximation (c : Vec) (D : Mat3)
    (ε : ℝ) (hε : 0<ε) :
    ∃ z∈interiorCHSHValues c D, Reduction.canonicalMaximum D c-ε<z := by
  by_contra h
  push_neg at h
  have hb := (canonical_interior_isLUB c D).2 h
  linarith

end UnilateralCHSH.Quantum
