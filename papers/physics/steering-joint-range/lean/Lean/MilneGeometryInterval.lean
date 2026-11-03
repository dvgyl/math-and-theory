import MilneGeometryRange

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def geometryDiagonalValues (c t : ℝ) : QQ → ℝ := fun i =>
  if i.1 = 0 then (if i.2 = 0 then (1+c+t)/4 else (1+c-t)/4)
  else if i.2 = 0 then (1-c-t)/4 else (1-c+t)/4

def geometryDiagonalState (c t : ℝ) : CMatrix :=
  Matrix.diagonal (fun i => (geometryDiagonalValues c t i : ℂ))

def geometryDiagonalT (t : ℝ) : T3 := !![0,0,0;0,0,0;0,0,t]

theorem geometryDiagonalState_psd {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    (geometryDiagonalState c t).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro ⟨i,j⟩
  apply RCLike.ofReal_nonneg.mpr
  fin_cases i <;> fin_cases j
  · change 0 ≤ (1+c+t)/4
    linarith
  · change 0 ≤ (1+c-t)/4
    linarith
  · change 0 ≤ (1-c-t)/4
    linarith
  · change 0 ≤ (1-c+t)/4
    linarith

theorem geometryDiagonalState_bloch (c t : ℝ) :
    geometryDiagonalState c t = blochState (c • geometryEz) 0 (geometryDiagonalT t) := by
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    apply Complex.ext <;>
    simp [geometryDiagonalState,geometryDiagonalValues,geometryDiagonalT,
      geometryEz,blochState,onAlice,onBob,pauli,pauliZ,Matrix.diagonal_apply,
      Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,
      Prod.ext_iff]
  all_goals ring

def geometryInterpolatedState (c t α : ℝ) : CMatrix :=
  ((1-α:ℝ):ℂ) • geometryDiagonalState c t + (α:ℂ) • geometrySkewState c t

def geometryInterpolatedT (c t α : ℝ) : T3 :=
  !![α*(geometrySkewU c t+geometrySkewV c t)/2,0,0;
     0,α*(geometrySkewV c t-geometrySkewU c t)/2,0;
     0,0,t]

theorem geometryInterpolatedState_psd {c t α : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (geometryInterpolatedState c t α).PosSemidef := by
  exact (psd_real_smul (geometryDiagonalState_psd hc0 hc1 ht0 ht1)
    (1-α) (by linarith)).add (psd_real_smul (geometrySkewState_psd c t) α hα0)

theorem geometryInterpolatedState_bloch {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) (α : ℝ) :
    geometryInterpolatedState c t α =
      blochState (c • geometryEz) 0 (geometryInterpolatedT c t α) := by
  unfold geometryInterpolatedState
  rw [geometryDiagonalState_bloch,geometrySkewState_bloch hc0 hc1 ht0 ht1]
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    apply Complex.ext <;>
    simp [geometryDiagonalT,geometrySkewT,geometryInterpolatedT,geometryEz,
      blochState,onAlice,onBob,pauli,pauliZ,Pi.smul_apply,smul_eq_mul,
      Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,Prod.ext_iff]
  all_goals ring

theorem geometryInterpolatedT_radial (c t α : ℝ) :
    vSq (ttVec (geometryInterpolatedT c t α) geometryEz) = t^2 := by
  simp [geometryInterpolatedT,geometryEz,vSq,ttVec,Fin.sum_univ_three]

theorem geometryInterpolatedT_squared {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) (α : ℝ) :
    tSq (geometryInterpolatedT c t α) = t^2+α^2*(1-c^2+t^2) := by
  have hid : tSq (geometryInterpolatedT c t α) =
      t^2+α^2*(tSq (geometrySkewT c t)-t^2) := by
    simp [geometryInterpolatedT,geometrySkewT,tSq,Fin.sum_univ_three]
    ring
  rw [hid,geometrySkewT_squared hc0 hc1 ht0 ht1]
  ring

theorem geometry_radial_lower (T : T3) :
    vSq (ttVec T geometryEz) ≤ tSq T := by
  simp [vSq,ttVec,geometryEz,tSq,Fin.sum_univ_three]
  nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
    sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]

theorem geometry_radial_lower_equality_iff (T : T3) :
    tSq T = vSq (ttVec T geometryEz) ↔
      (∀ j, T 0 j = 0) ∧ (∀ j, T 1 j = 0) := by
  constructor
  · intro h
    simp [vSq,ttVec,geometryEz,tSq,Fin.sum_univ_three] at h
    have h00 : T 0 0 ^ 2 = 0 := by
      nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
        sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]
    have h01 : T 0 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
        sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]
    have h02 : T 0 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
        sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]
    have h10 : T 1 0 ^ 2 = 0 := by
      nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
        sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]
    have h11 : T 1 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
        sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]
    have h12 : T 1 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (T 0 0),sq_nonneg (T 0 1),sq_nonneg (T 0 2),
        sq_nonneg (T 1 0),sq_nonneg (T 1 1),sq_nonneg (T 1 2)]
    constructor
    · intro j
      fin_cases j
      · exact (sq_eq_zero_iff).mp h00
      · exact (sq_eq_zero_iff).mp h01
      · exact (sq_eq_zero_iff).mp h02
    · intro j
      fin_cases j
      · exact (sq_eq_zero_iff).mp h10
      · exact (sq_eq_zero_iff).mp h11
      · exact (sq_eq_zero_iff).mp h12
  · rintro ⟨h0,h1⟩
    simp [vSq,ttVec,geometryEz,tSq,Fin.sum_univ_three,h0,h1]

/-- Every value in the whole interval is realized by an actual PSD Fano
matrix.  Only its transverse coherences are attenuated. -/
theorem geometrySkewSpectrum_contains_interval {c t x : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hx0 : t^2 ≤ x) (hx1 : x ≤ 1-c^2+2*t^2) :
    x ∈ geometrySkewSpectrum c t := by
  let W := 1-c^2+t^2
  have hW0 : 0 ≤ W := by
    dsimp [W]
    nlinarith [sq_nonneg t,mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  by_cases hW : W = 0
  · have hx : x = t^2 := by dsimp [W] at hW; linarith
    subst x
    refine ⟨geometryInterpolatedT c t 0,?_,geometryInterpolatedT_radial c t 0,?_⟩
    · rw [← geometryInterpolatedState_bloch hc0 hc1 ht0 ht1]
      exact geometryInterpolatedState_psd hc0 hc1 ht0 ht1 (by norm_num) (by norm_num)
    · rw [geometryInterpolatedT_squared hc0 hc1 ht0 ht1]
      norm_num
  · have hWp : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
    let α := Real.sqrt ((x-t^2)/W)
    have hq0 : 0 ≤ (x-t^2)/W := div_nonneg (sub_nonneg.mpr hx0) hW0
    have hq1 : (x-t^2)/W ≤ 1 := by
      apply (div_le_iff₀ hWp).mpr
      dsimp [W]
      linarith
    have hα0 : 0 ≤ α := Real.sqrt_nonneg _
    have hαsq : α^2 = (x-t^2)/W := Real.sq_sqrt hq0
    have hα1 : α ≤ 1 := by nlinarith
    refine ⟨geometryInterpolatedT c t α,?_,geometryInterpolatedT_radial c t α,?_⟩
    · rw [← geometryInterpolatedState_bloch hc0 hc1 ht0 ht1]
      exact geometryInterpolatedState_psd hc0 hc1 ht0 ht1 hα0 hα1
    · rw [geometryInterpolatedT_squared hc0 hc1 ht0 ht1,hαsq]
      change t^2+(x-t^2)/W*W = x
      rw [div_mul_cancel₀ _ hW]
      ring

/-- Complete attainable correlation interval at fixed centre and radial
support, with density-matrix positivity and actual Pauli data in the set. -/
theorem geometryPhysicalSkewSpectrum_eq_interval {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    geometryPhysicalSkewSpectrum c t = Set.Icc (t^2) (1-c^2+2*t^2) := by
  rw [geometryPhysicalSkewSpectrum_eq]
  ext x
  constructor
  · rintro ⟨T,hM,hq,hx⟩
    constructor
    · have h := geometry_radial_lower T
      rwa [hq,hx] at h
    · have h := geometry_radial c geometryEz T geometryEz_unit hM
      rwa [hq,hx] at h
  · rintro ⟨hx0,hx1⟩
    exact geometrySkewSpectrum_contains_interval hc0 hc1 ht0 ht1 hx0 hx1

end Milne

#print axioms Milne.geometryPhysicalSkewSpectrum_eq_interval
#print axioms Milne.geometry_radial_lower_equality_iff
