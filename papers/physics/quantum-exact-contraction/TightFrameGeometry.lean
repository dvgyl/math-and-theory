import BellSupport
import Mathlib.Tactic.Module

/-! Elementary geometry of a balanced two-row tight frame. The final channel
theorem instantiates this interface with an explicit finite Fourier phase. -/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace TightFrameGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

variable (I : Type) [Fintype I] [DecidableEq I]

def size : ℝ := Fintype.card I
def radius : ℝ := 1-2/size I

structure Frame where
  Z : Matrix (Fin 2) I ℂ
  tight : Z * Zᴴ = (size I/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  balanced : ∀ (i : I) (j : Fin 2), star (Z j i) * Z j i = (1/2 : ℂ)

variable {I}

def flip : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]

theorem flip_adjoint : flipᴴ = flip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flip,Matrix.conjTranspose_apply,Matrix.diagonal]

theorem flip_sq : flip*flip=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flip,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.diagonal,Matrix.one_apply]

def Frame.minus (F : Frame I) : Matrix (Fin 2) I ℂ := flip * F.Z

def Frame.projection (F : Frame I) : Matrix I I ℂ :=
  1-(2/size I : ℝ) • (F.Zᴴ * F.Z)

omit [DecidableEq I] in
theorem size_pos [DecidableEq I] (hI : 2 ≤ Fintype.card I) : 0 < size I := by
  unfold size
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hI)

theorem radius_nonneg (hI : 2 ≤ Fintype.card I) : 0 ≤ radius I := by
  have hn := size_pos hI
  have hn2 : (2:ℝ) ≤ size I := by
    change (2:ℝ) ≤ (Fintype.card I:ℝ)
    exact_mod_cast hI
  unfold radius
  exact sub_nonneg.mpr ((div_le_one hn).mpr hn2)

omit [DecidableEq I] in
theorem Frame.gram_diagonal [DecidableEq I] (F : Frame I) (i : I) : (F.Zᴴ*F.Z) i i = 1 := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,F.balanced]
  norm_num

omit [DecidableEq I] in
theorem Frame.cross_diagonal [DecidableEq I] (F : Frame I) (i : I) : (F.Zᴴ*F.minus) i i = 0 := by
  change (F.Zᴴ*(flip*F.Z)) i i=0
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ]
  norm_num [flip,Matrix.diagonal]
  have h₀ : (starRingEnd ℂ) (F.Z 0 i) * F.Z 0 i = (1/2:ℂ) := by
    simpa only [Complex.star_def] using F.balanced i 0
  have h₁ : (starRingEnd ℂ) (F.Z 1 i) * F.Z 1 i = (1/2:ℂ) := by
    simpa only [Complex.star_def] using F.balanced i 1
  rw [h₀,h₁]
  norm_num

omit [DecidableEq I] in
theorem Frame.minus_gram [DecidableEq I] (F : Frame I) : F.minusᴴ*F.minus=F.Zᴴ*F.Z := by
  unfold Frame.minus
  rw [Matrix.conjTranspose_mul,flip_adjoint]
  calc
    (F.Zᴴ*flip)*(flip*F.Z) = F.Zᴴ*(flip*flip)*F.Z := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [flip_sq,Matrix.mul_one]

theorem Frame.projection_hermitian (F : Frame I) : F.projection.IsHermitian :=
  Matrix.isHermitian_one.sub (hermitian_real_smul _
    (Matrix.posSemidef_conjTranspose_mul_self F.Z).1 (2/size I))

theorem Frame.projection_annihilates (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    F.projection*F.Zᴴ=0 := by
  have hc : (2/size I)*(size I/2) = (1:ℝ) := by
    field_simp [(size_pos hI).ne']
  unfold Frame.projection
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_assoc,F.tight,
    Matrix.mul_smul,Matrix.mul_one,smul_smul,hc,one_smul,sub_self]

theorem Frame.projection_annihilates_minus (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    F.projection*F.minusᴴ=0 := by
  unfold Frame.minus
  rw [Matrix.conjTranspose_mul,←Matrix.mul_assoc,F.projection_annihilates hI,
    Matrix.zero_mul]

theorem Frame.projection_sq (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    F.projection*F.projection=F.projection := by
  calc
    _ = F.projection*(1-(2/size I:ℝ) • (F.Zᴴ*F.Z)) := rfl
    _ = F.projection-(2/size I:ℝ) • ((F.projection*F.Zᴴ)*F.Z) := by
      simp only [Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,Matrix.mul_assoc]
    _ = F.projection := by
      rw [F.projection_annihilates hI,Matrix.zero_mul,smul_zero,sub_zero]

theorem Frame.projection_gram (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    F.projectionᴴ*F.projection=F.projection := by
  rw [F.projection_hermitian.eq,F.projection_sq hI]

theorem Frame.projection_positive (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    F.projection.PosSemidef := by
  rw [← F.projection_gram hI]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem Frame.projection_le_one (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    (1-F.projection).PosSemidef := by
  have he : 1-F.projection = (2/size I:ℝ) • (F.Zᴴ*F.Z) := by
    unfold Frame.projection
    abel
  rw [he]
  exact posSemidef_real_smul _ (Matrix.posSemidef_conjTranspose_mul_self _)
    _ (div_nonneg (by norm_num) (size_pos hI).le)

theorem Frame.projection_diagonal (F : Frame I) (i : I) :
    F.projection i i = ((radius I : ℝ):ℂ) := by
  simp only [Frame.projection,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,ite_true,F.gram_diagonal,Complex.real_smul,mul_one]
  simp [radius]

theorem Frame.projection_trace (F : Frame I) (hI : 2 ≤ Fintype.card I) :
    F.projection.trace = ((size I-2:ℝ):ℂ) := by
  simp only [Matrix.trace,Matrix.diag,F.projection_diagonal,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul]
  have hn : size I*radius I=size I-2 := by
    unfold radius
    field_simp [(size_pos hI).ne']
  change ((size I:ℝ):ℂ)*((radius I:ℝ):ℂ)=_
  rw [←Complex.ofReal_mul,hn]

end
end TightFrameGeometry
