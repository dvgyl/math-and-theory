import WeylBell
import TightFrameGeometry

/-! Explicit balanced two-row tight frames from zero-sum unit phases. -/
open Matrix
open scoped BigOperators

namespace WeylFrame
noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I]

def c : ℂ := (1+Complex.I)/2

theorem c_norm : star c*c=(1/2:ℂ) := by
  norm_num [c, Complex.star_def]
  ring_nf
  norm_num [Complex.I_sq]

theorem c_norm' : c*star c=(1/2:ℂ) := by rw [mul_comm]; exact c_norm

def rows (ζ : I → ℂ) : Matrix (Fin 2) I ℂ :=
  fun j i => if j=0 then c else c*ζ i

omit [Fintype I] [DecidableEq I] in
theorem rows_balanced [Fintype I] [DecidableEq I] (ζ : I → ℂ) (hu : ∀ i,star (ζ i)*ζ i=1)
    (i : I) (j : Fin 2) : star (rows ζ j i)*rows ζ j i=(1/2:ℂ) := by
  fin_cases j
  · simpa only [rows, if_pos rfl] using c_norm
  · change star (c*ζ i)*(c*ζ i)=(1/2:ℂ)
    rw [StarMul.star_mul]
    calc
      (star (ζ i)*star c)*(c*ζ i) = (star c*c)*(star (ζ i)*ζ i) := by ring
      _ = (1/2:ℂ) := by rw [c_norm,hu i,mul_one]

omit [DecidableEq I] in
theorem rows_tight [DecidableEq I] (ζ : I → ℂ) (hu : ∀ i,star (ζ i)*ζ i=1)
    (hz : ∑ i, ζ i=0) :
    rows ζ*(rows ζ)ᴴ=(TightFrameGeometry.size I/2:ℝ) •
      (1:Matrix (Fin 2) (Fin 2) ℂ) := by
  have hz' : ∑ i,star (ζ i)=0 := by
    simpa only [map_sum,map_zero,Complex.star_def] using congrArg (starRingEnd ℂ) hz
  have hu' (i : I) : ζ i*star (ζ i)=1 := by rw [mul_comm]; exact hu i
  have hc : c*(starRingEnd ℂ) c=(1/2:ℂ) := c_norm'
  ext j k
  fin_cases j <;> fin_cases k
  · norm_num [Matrix.mul_apply,Matrix.conjTranspose_apply,rows,hc,
      Matrix.smul_apply,Matrix.one_apply,TightFrameGeometry.size,div_eq_mul_inv]
  · have he : (∑ i, c*star (c*ζ i)) =
        (c*star c)*(∑ i,star (ζ i)) := by
      simp only [Finset.mul_sum,StarMul.star_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hz',mul_zero] at he
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,rows,
      Matrix.smul_apply,Matrix.one_apply,Complex.real_smul,Complex.star_def] using he
  · have he : (∑ i, (c*ζ i)*star c) =
        (c*star c)*(∑ i,ζ i) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hz,mul_zero] at he
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,rows,
      Matrix.smul_apply,Matrix.one_apply,Complex.real_smul,Complex.star_def] using he
  · have he (i : I) : (c*ζ i)*star (c*ζ i) = (1/2:ℂ) := by
      rw [StarMul.star_mul]
      calc
        _ = (c*star c)*(ζ i*star (ζ i)) := by ring
        _ = _ := by rw [c_norm',hu',mul_one]
    have hh : (∑ i, (c*ζ i)*star (c*ζ i)) =
        ((TightFrameGeometry.size I/2:ℝ):ℂ) := by
      simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      simp [TightFrameGeometry.size,div_eq_mul_inv]
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,rows,
      Matrix.smul_apply,Matrix.one_apply,Complex.real_smul,Complex.star_def] using hh

/-- A concrete frame; its hypotheses are elementary identities on phases. -/
def ofPhase (ζ : I → ℂ) (hu : ∀ i,star (ζ i)*ζ i=1) (hz : ∑ i,ζ i=0) :
    TightFrameGeometry.Frame I where
  Z := rows ζ
  tight := rows_tight ζ hu hz
  balanced := rows_balanced ζ hu

/-- The phase identities are supplied by the explicit finite Fourier character. -/
def bellFrame (d : ℕ) [NeZero d] (hd : 2≤d) :
    TightFrameGeometry.Frame (WeylBell.A d × WeylBell.A d) :=
  ofPhase WeylBell.framePhase WeylBell.framePhase_unit (WeylBell.framePhase_sum hd)

@[simp] theorem bellFrame_card (d : ℕ) [NeZero d] :
    Fintype.card (WeylBell.A d × WeylBell.A d)=d^2 := by
  simp [WeylBell.A,ZMod.card,pow_two]

end
end WeylFrame
