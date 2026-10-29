import FlowerPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace SquareFlowerCompletion.Radius

def A (z : ℂ) : ℂ := z^2+3*z+3
def B (z : ℂ) : ℂ := z^2+3*z+1
def bracket (n : ℕ) (z : ℂ) : ℂ := z*A z^n+B z^n-1

theorem norm_A_lower (z : ℂ) : ‖z‖^2-3*‖z‖-3 ≤ ‖A z‖ := by
  have hsmall : ‖(3 : ℂ)*z+3‖ ≤ 3*‖z‖+3 := by
    calc
      _ ≤ ‖(3 : ℂ)*z‖+‖(3 : ℂ)‖ := norm_add_le _ _
      _ = _ := by norm_num [norm_mul]
  have htriangle := norm_sub_le (A z) ((3 : ℂ)*z+3)
  have he : A z-((3 : ℂ)*z+3) = z^2 := by unfold A; ring
  rw [he, norm_pow] at htriangle
  linarith

theorem norm_A_ge_shift_square (z : ℂ) (hr : 4 ≤ ‖z‖) :
    (‖z‖-3)^2 ≤ ‖A z‖ := by
  have h := norm_A_lower z
  nlinarith

theorem norm_A_ge_one (z : ℂ) (hr : 4 ≤ ‖z‖) : 1 ≤ ‖A z‖ := by
  have hx : 1 ≤ ‖z‖-3 := by linarith
  have hsquare : 1 ≤ (‖z‖-3)^2 := one_le_pow₀ hx
  exact hsquare.trans (norm_A_ge_shift_square z hr)

theorem norm_B_le (z : ℂ) : ‖B z‖ ≤ ‖A z‖+2 := by
  have he : B z = A z-2 := by unfold A B; ring
  rw [he]
  simpa using norm_sub_le (A z) (2 : ℂ)

theorem bracket_root_norm_bound (n : ℕ) (z : ℂ) (hroot : bracket n z = 0)
    (hr : 4 ≤ ‖z‖) :
    ‖z‖-1 ≤ (1+2/(‖z‖-3)^2)^n := by
  have hx : 0 < ‖z‖-3 := by linarith
  have hx2 : 0 < (‖z‖-3)^2 := sq_pos_of_pos hx
  have hA := norm_A_ge_shift_square z hr
  have hAone := norm_A_ge_one z hr
  have hApos : 0 < ‖A z‖ := by linarith
  have hdiv : 1 ≤ ‖A z‖/(‖z‖-3)^2 :=
    (le_div_iff₀ hx2).mpr (by simpa using hA)
  have hscaled : ‖B z‖ ≤ ‖A z‖*(1+2/(‖z‖-3)^2) := by
    have hB := norm_B_le z
    have hh := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ ≤ ‖A z‖+2 := hB
      _ ≤ ‖A z‖+2*(‖A z‖/(‖z‖-3)^2) := by linarith
      _ = _ := by ring
  have hpower := pow_le_pow_left₀ (norm_nonneg (B z)) hscaled n
  rw [mul_pow] at hpower
  have hAonepow : 1 ≤ ‖A z‖^n := one_le_pow₀ hAone
  have hApowpos : 0 < ‖A z‖^n := pow_pos hApos n
  have he : z*A z^n = 1-B z^n := by
    apply eq_sub_iff_add_eq.mpr
    exact sub_eq_zero.mp hroot
  have htriangle : ‖z‖*‖A z‖^n ≤ 1+‖B z‖^n := by
    calc
      _ = ‖z*A z^n‖ := by rw [norm_mul, norm_pow]
      _ = ‖1-B z^n‖ := congrArg norm he
      _ ≤ 1+‖B z‖^n := by simpa using norm_sub_le (1 : ℂ) (B z^n)
  have hfinal : (‖z‖-1)*‖A z‖^n ≤ (1+2/(‖z‖-3)^2)^n*‖A z‖^n := by
    nlinarith
  exact (mul_le_mul_right hApowpos).mp hfinal

#print axioms norm_A_lower
#print axioms norm_A_ge_shift_square
#print axioms norm_A_ge_one
#print axioms norm_B_le
#print axioms bracket_root_norm_bound
end SquareFlowerCompletion.Radius
