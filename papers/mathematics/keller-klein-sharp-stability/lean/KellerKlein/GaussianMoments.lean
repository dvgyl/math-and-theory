import KellerKlein.Imports

/-!
# Gaussian integrals used in the Keller--Klein analytic completion

These are conventional analytic ingredients.  All integrals below are actual
Lebesgue integrals; their values are proved from Mathlib's Gaussian and Gamma
integral theorems.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace KellerKlein

set_option maxHeartbeats 800000

def phi0 : ℝ := 1 / Real.sqrt (2 * Real.pi)

def gaussian (s : ℝ) : ℝ := Real.exp (-(s ^ 2) / 2)

def phi (x : ℝ) : ℝ := gaussian x * phi0

def c (a : ℝ) : ℝ := ∫ x in (0 : ℝ)..a, phi x

def H (a : ℝ) : ℝ := 2 * c a

def halfMoment (k : ℕ) : ℝ := ∫ s in Ioi (0 : ℝ), s ^ k * gaussian s

lemma phi0_pos : 0 < phi0 := by
  unfold phi0
  positivity

lemma two_pi_phi0_sq : 2 * Real.pi * phi0^2 = 1 := by
  unfold phi0
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp

lemma gaussian_pos (s : ℝ) : 0 < gaussian s := Real.exp_pos _

lemma gaussian_nonneg (s : ℝ) : 0 ≤ gaussian s := (gaussian_pos s).le

lemma phi_pos (x : ℝ) : 0 < phi x := mul_pos (gaussian_pos x) phi0_pos

lemma continuous_gaussian : Continuous gaussian := by
  unfold gaussian
  fun_prop

lemma continuous_phi : Continuous phi := continuous_gaussian.mul continuous_const

lemma gaussian_zero : gaussian 0 = 1 := by simp [gaussian]

lemma gaussian_neg (s : ℝ) : gaussian (-s) = gaussian s := by simp [gaussian]

lemma gaussian_le_one (s : ℝ) : gaussian s ≤ 1 := by
  rw [gaussian, Real.exp_le_one_iff]
  nlinarith [sq_nonneg s]

lemma integrable_pow_gaussian (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k * gaussian s) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (by norm_num) (s := (k : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have he : (fun s : ℝ => s ^ k * gaussian s) =
      (fun s : ℝ => s ^ (k : ℝ) * Real.exp (-(1 / 2) * s ^ 2)) := by
    funext s
    rw [Real.rpow_natCast]
    congr 1
    unfold gaussian
    congr 1
    ring
  rw [he]
  exact h

lemma integrableOn_pow_gaussian (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * gaussian s) (Ioi 0) :=
  (integrable_pow_gaussian k).integrableOn

lemma integrable_gaussian : Integrable gaussian := by
  simpa using integrable_pow_gaussian 0

lemma integrable_phi : Integrable phi := integrable_gaussian.mul_const phi0

lemma halfMoment_nonneg (k : ℕ) : 0 ≤ halfMoment k := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro s hs
  exact mul_nonneg (pow_nonneg hs.le k) (gaussian_nonneg s)

lemma halfMoment_gamma (k : ℕ) :
    halfMoment k = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) *
      Real.Gamma (((k : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  rw [halfMoment]
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [Real.rpow_natCast, Real.rpow_two]
  congr 1
  unfold gaussian
  congr 1
  ring

lemma halfMoment_zero : halfMoment 0 = Real.pi * phi0 := by
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  have hs : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hn : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  calc
    halfMoment 0 = Real.sqrt (2 * Real.pi) / 2 := by
      convert h using 1
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        simp only [pow_zero, one_mul]
        unfold gaussian
        congr 1
        ring
      · congr 2
        ring
    _ = Real.pi * phi0 := by
      unfold phi0
      rw [mul_one_div]
      apply (div_eq_div_iff (by norm_num : (2 : ℝ) ≠ 0) hn).2
      nlinarith

lemma halfMoment_one : halfMoment 1 = 1 := by
  rw [halfMoment_gamma]
  norm_num [Real.rpow_neg_one, Real.Gamma_one]

lemma halfMoment_add_two (k : ℕ) :
    halfMoment (k + 2) = ((k : ℝ) + 1) * halfMoment k := by
  rw [halfMoment_gamma, halfMoment_gamma]
  have hk : ((k : ℝ) + 1) / 2 ≠ 0 := by positivity
  have he : -(((k + 2 : ℕ) : ℝ) + 1) / 2 = -((k : ℝ) + 1) / 2 + (-1) := by
    push_cast
    ring
  have hg : (((k + 2 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 := by
    push_cast
    ring
  rw [he, hg, Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2),
    Real.rpow_neg_one, Real.Gamma_add_one hk]
  ring

lemma halfMoment_two : halfMoment 2 = Real.pi * phi0 := by
  simpa using (halfMoment_add_two 0).trans (by simp [halfMoment_zero])

lemma halfMoment_three : halfMoment 3 = 2 := by
  have h := halfMoment_add_two 1
  norm_num [halfMoment_one] at h
  exact h

lemma halfMoment_four : halfMoment 4 = 3 * Real.pi * phi0 := by
  have h := halfMoment_add_two 2
  norm_num [halfMoment_two, mul_assoc] at h
  simpa only [mul_assoc] using h

lemma halfMoment_five : halfMoment 5 = 8 := by
  rw [show 5 = 3 + 2 by rfl, halfMoment_add_two, halfMoment_three]
  norm_num

lemma halfMoment_six : halfMoment 6 = 15 * Real.pi * phi0 := by
  rw [show 6 = 4 + 2 by rfl, halfMoment_add_two, halfMoment_four]
  norm_num
  ring

lemma halfMoment_seven : halfMoment 7 = 48 := by
  rw [show 7 = 5 + 2 by rfl, halfMoment_add_two, halfMoment_five]
  norm_num

lemma halfMoment_eight : halfMoment 8 = 105 * Real.pi * phi0 := by
  rw [show 8 = 6 + 2 by rfl, halfMoment_add_two, halfMoment_six]
  norm_num
  ring

lemma halfMoment_ten : halfMoment 10 = 945 * Real.pi * phi0 := by
  rw [show 10 = 8 + 2 by rfl, halfMoment_add_two, halfMoment_eight]
  norm_num
  ring

end KellerKlein
