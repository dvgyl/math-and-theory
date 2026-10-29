import RadiusAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace SquareFlowerCompletion.Radius

private def alpha : ℂ := ⟨-3/2, Real.sqrt 3/2⟩
private def beta : ℂ := ⟨-3/2, -(Real.sqrt 3)/2⟩

private theorem factor_A (z : ℂ) : A z = (z-alpha)*(z-beta) := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [A, alpha, beta, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

private theorem norm_alpha_lt : ‖alpha‖ < 2 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : ‖alpha‖^2 = 3 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [alpha, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg alpha]

private theorem norm_beta_lt : ‖beta‖ < 2 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : ‖beta‖^2 = 3 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [beta, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg beta]

theorem norm_A_gt_exact_square (z : ℂ) (hr : 3 ≤ ‖z‖) :
    (‖z‖-2)^2 < ‖A z‖ := by
  have ha : ‖z‖-2 < ‖z-alpha‖ := by
    have ht := norm_sub_le z alpha
    have ht' := norm_add_le (z-alpha) alpha
    rw [sub_add_cancel] at ht'
    linarith [norm_alpha_lt]
  have hb : ‖z‖-2 < ‖z-beta‖ := by
    have ht := norm_add_le (z-beta) beta
    rw [sub_add_cancel] at ht
    linarith [norm_beta_lt]
  rw [factor_A, norm_mul]
  have hp : 0 < ‖z‖-2 := by linarith
  simpa [pow_two] using mul_lt_mul ha hb.le hp (norm_nonneg (z-alpha))

theorem bracket_root_exact_power (n : ℕ) (z : ℂ) (hroot : bracket n z = 0)
    (hr : 3 ≤ ‖z‖) :
    ‖z‖-1 ≤ (1+2/(‖z‖-2)^2)^n := by
  have hx : 0 < ‖z‖-2 := by linarith
  have hx2 : 0 < (‖z‖-2)^2 := sq_pos_of_pos hx
  have hA := (norm_A_gt_exact_square z hr).le
  have hAone : 1 ≤ ‖A z‖ := by nlinarith [norm_A_gt_exact_square z hr]
  have hApos : 0 < ‖A z‖ := by linarith
  have hdiv : 1 ≤ ‖A z‖/(‖z‖-2)^2 :=
    (le_div_iff₀ hx2).mpr (by simpa using hA)
  have hscaled : ‖B z‖ ≤ ‖A z‖*(1+2/(‖z‖-2)^2) := by
    have hB := norm_B_le z
    have hh := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ ≤ ‖A z‖+2 := hB
      _ ≤ ‖A z‖+2*(‖A z‖/(‖z‖-2)^2) := by linarith
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
  have hfinal : (‖z‖-1)*‖A z‖^n ≤ (1+2/(‖z‖-2)^2)^n*‖A z‖^n := by
    nlinarith
  exact (mul_le_mul_right hApowpos).mp hfinal

#print axioms norm_A_gt_exact_square
#print axioms bracket_root_exact_power
end SquareFlowerCompletion.Radius
