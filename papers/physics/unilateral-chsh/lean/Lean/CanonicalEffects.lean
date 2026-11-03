import QuantumCHSH
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact qubit effects, their square-root filters, and Bloch parametrization. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

abbrev EffectMatrix := Matrix Q Q ℂ

def spinEffect (u : Vec) : EffectMatrix := 1 + realSpin u

theorem affineFilter_square (u : Vec) (a b : ℝ) :
    affineFilter u a b * affineFilter u a b =
      ((a^2+b^2*normSq u : ℝ) : ℂ) • (1 : EffectMatrix) +
        ((2*a*b : ℝ) : ℂ) • realSpin u := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [affineFilter,realSpin,complexSpin,normSq,dot,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.one_apply,Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

theorem positive_filter_hermitian (u : Vec) : (positiveFilter u).IsHermitian :=
  affineFilter_hermitian u _ _

theorem positive_filter_effect_square (u : Vec) (hu : normSq u≤1) :
    positiveFilter u * positiveFilter u = spinEffect u := by
  unfold positiveFilter
  rw [affineFilter_square,(positive_filter_coefficients u hu).1,
    (positive_filter_coefficients u hu).2.2.1]
  simp [spinEffect]

theorem positive_filter_effect_gram (u : Vec) (hu : normSq u≤1) :
    (positiveFilter u)ᴴ * positiveFilter u = spinEffect u := by
  rw [(positive_filter_hermitian u).eq,positive_filter_effect_square u hu]

theorem spinEffect_posSemidef (u : Vec) (hu : normSq u≤1) :
    (spinEffect u).PosSemidef := by
  rw [← positive_filter_effect_gram u hu]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem spinEffect_det (u : Vec) : (spinEffect u).det = ((1-normSq u : ℝ) : ℂ) := by
  have h : spinEffect u = affineFilter u 1 1 := by simp [spinEffect,affineFilter]
  rw [h,affineFilter_det]
  norm_num

theorem trace_two_hermitian_effect (E : EffectMatrix) (hE : E.IsHermitian)
    (htrace : Matrix.trace E=2) : ∃ u : Vec, E=spinEffect u := by
  have hh : (E-1).IsHermitian := hE.sub Matrix.isHermitian_one
  have ht : Matrix.trace (E-1)=0 := by
    rw [Matrix.trace_sub,htrace]
    norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  obtain ⟨u,hu⟩ := traceless_hermitian_realSpin (E-1) hh ht
  refine ⟨u,?_⟩
  unfold spinEffect
  rw [← hu]
  noncomm_ring

theorem qubit_posSemidef_det_nonneg (E : EffectMatrix) (hE : E.PosSemidef) :
    0 ≤ E.det := by
  rw [hE.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_nonneg
  intro i _
  simpa using hE.eigenvalues_nonneg i

theorem trace_two_posSemidef_effect (E : EffectMatrix) (hE : E.PosSemidef)
    (htrace : Matrix.trace E=2) :
    ∃ u : Vec, normSq u≤1 ∧ E=spinEffect u := by
  obtain ⟨u,hu⟩ := trace_two_hermitian_effect E hE.1 htrace
  have hd := qubit_posSemidef_det_nonneg E hE
  rw [hu,spinEffect_det] at hd
  have hr : 0 ≤ 1-normSq u := by exact_mod_cast hd
  exact ⟨u,by linarith,hu⟩

theorem trace_two_invertible_posSemidef_effect (E : EffectMatrix) (hE : E.PosSemidef)
    (htrace : Matrix.trace E=2) (hdet : E.det≠0) :
    ∃ u : Vec, normSq u<1 ∧ E=spinEffect u := by
  obtain ⟨u,hu,he⟩ := trace_two_posSemidef_effect E hE htrace
  have hn : normSq u≠1 := by
    intro hz
    apply hdet
    rw [he,spinEffect_det,hz]
    norm_num
  exact ⟨u,lt_of_le_of_ne hu hn,he⟩

theorem trace_two_posDef_effect (E : EffectMatrix) (hE : E.PosDef)
    (htrace : Matrix.trace E=2) :
    ∃ u : Vec, normSq u<1 ∧ E=spinEffect u :=
  trace_two_invertible_posSemidef_effect E hE.posSemidef htrace hE.det_pos.ne'

theorem qubit_posSemidef_smul_real (E : EffectMatrix) (hE : E.PosSemidef)
    (r : ℝ) (hr : 0≤r) : ((r : ℂ) • E).PosSemidef := by
  constructor
  · change ((r : ℂ) • E)ᴴ = (r : ℂ) • E
    rw [Matrix.conjTranspose_smul,hE.1.eq]
    simp
  · intro x
    rw [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul]
    exact mul_nonneg (by exact_mod_cast hr) (hE.2 x)

theorem qubit_posDef_smul_real (E : EffectMatrix) (hE : E.PosDef)
    (r : ℝ) (hr : 0<r) : ((r : ℂ) • E).PosDef := by
  constructor
  · change ((r : ℂ) • E)ᴴ = (r : ℂ) • E
    rw [Matrix.conjTranspose_smul,hE.1.eq]
    simp
  · intro x hx
    rw [Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul]
    exact mul_pos (by exact_mod_cast hr) (hE.2 x hx)

theorem qubit_hermitian_trace_real (E : EffectMatrix) (hE : E.IsHermitian) :
    (Matrix.trace E).im=0 := by
  have hs : star (Matrix.trace E)=Matrix.trace E := by
    rw [← Matrix.trace_conjTranspose,hE.eq]
  have hi := congrArg Complex.im hs
  change -(Matrix.trace E).im=(Matrix.trace E).im at hi
  linarith

theorem qubit_gram_posDef (F : EffectMatrix) (hF : F.det≠0) :
    (Fᴴ*F).PosDef := by
  have hi : Function.Injective F.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det F).mpr (isUnit_iff_ne_zero.mpr hF))
  have h := (Matrix.PosDef.one : (1 : EffectMatrix).PosDef).conjTranspose_mul_mul_same hi
  simpa only [Matrix.mul_one] using h

theorem qubit_posDef_trace_positive (E : EffectMatrix) (hE : E.PosDef) :
    0 < (Matrix.trace E).re := by
  have hn (i : Q) : (Pi.single i (1:ℂ) : Q → ℂ) ≠ 0 := by
    intro hz
    have h := congrFun hz i
    simp at h
  have h₀ := hE.re_dotProduct_pos (hn 0)
  have h₁ := hE.re_dotProduct_pos (hn 1)
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.single_apply] at h₀ h₁
  simpa [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using add_pos h₀ h₁


theorem one_add_realSpin_posSemidef_norm (u : Vec)
    (h : ((1 : EffectMatrix)+realSpin u).PosSemidef) : normSq u≤1 := by
  have hd := qubit_posSemidef_det_nonneg (spinEffect u) h
  rw [spinEffect_det] at hd
  have hr : 0≤1-normSq u := by exact_mod_cast hd
  linarith

theorem one_add_realSpin_posDef_norm (u : Vec)
    (h : ((1 : EffectMatrix)+realSpin u).PosDef) : normSq u<1 := by
  have hd := h.det_pos
  change 0<(spinEffect u).det at hd
  rw [spinEffect_det] at hd
  have hr : 0<1-normSq u := by exact_mod_cast hd
  linarith

theorem one_add_realSpin_invertible_posSemidef_norm (u : Vec)
    (h : ((1 : EffectMatrix)+realSpin u).PosSemidef)
    (hdet : ((1 : EffectMatrix)+realSpin u).det≠0) : normSq u<1 := by
  have hb := one_add_realSpin_posSemidef_norm u h
  have hn : normSq u≠1 := by
    intro he
    apply hdet
    change (spinEffect u).det=0
    rw [spinEffect_det,he]
    norm_num
  exact lt_of_le_of_ne hb hn

end UnilateralCHSH.Quantum
